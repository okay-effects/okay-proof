package okay.policy

import okay.scala3.*
import okay.scala3.std.*

import scala.concurrent.{ExecutionContext, Future}

/** a fact or a state, applied: `owns(ann, acc1)`, `spent(ann)` */
final case class FactRef(name: String, args: List[Value]):
  override def toString: String = s"$name(${args.mkString(", ")})"

/** what is known of a fact: a relation true or false, a function's value */
enum Answer:
  case Holds(truth: Boolean)
  case Is(value: Value)

/** WHAT THE GUARD KNOWS, asked: all of a decision's facts at once — the call's own, a database's, an external
 * service's (asynchronous in its handler). A fact not in the answer is unknown */
enum Facts[X]:
  case Ask(refs: List[FactRef]) extends Facts[Map[FactRef, Answer]]

object Facts:
  def ask[R[_]](refs: List[FactRef])(using In[Facts, R]): Map[FactRef, Answer] ! R =
    if refs.isEmpty then pure(Map.empty) else perform[Facts](Ask(refs))

  /** the sources a policy's facts name (`fact balance(...): Dec from stripe`) that are not among `registered`: what a
   * guard checks when it loads a policy — a fact of a missing source is always unknown */
  def missing(checked: Checked, registered: Set[String]): Set[String] =
    checked.facts.values.flatMap(_.source).toSet -- registered

  /**
   * THE FACTS FROM THEIR SOURCES: a fact `from s` asked of the source `s`, a fact with no `from` of `local` (the
   * session, the call's context). A decision's facts asked of all their sources at once, IN PARALLEL, each within
   * `timeoutMs`. Fail closed: a source that is missing, fails, or is late answers nothing; an answer of a fact not of
   * that source, or of the wrong kind or sort, is dropped — unknown, so it can never allow.
   */
  def from[R[_], Rest[_], A](checked: Checked, sources: Map[String, Source], local: Source = Source.none,
                             timeoutMs: Long = 2000)(p: A ! R)(
    using Split[Facts, R, Rest], In[Async, Rest], ExecutionContext): A ! Rest =
    def asked(source: Option[String], refs: List[FactRef]): Map[FactRef, Answer] ! Async =
      val of = source.fold(Some(local))(sources.get)
      of.fold(pure(Map.empty)) { src =>
        Async.async[Map[FactRef, Answer], Async](cb =>
          Async.start(Async.timeout(timeoutMs)(defer(src.ask(refs)))).future.onComplete {
            case scala.util.Success(Some(m)) => cb(Right(m.filter((r, a) => refs.contains(r) && fits(checked, r, a))))
            case _ => cb(Right(Map.empty))
          }(using ExecutionContext.parasitic))
      }
    handle(p, Handler.general[Facts, Rest, A, A](pure)([X] => (op: Facts[X], k: X => A ! Rest) => op match
      case Ask(refs) =>
        val groups = refs.distinct.groupBy(r => checked.facts.get(r.name).flatMap(_.source)).toList
        val all = Async.parTraverse(groups)((source, rs) => asked(source, rs))
          .map(_.foldLeft(Map.empty[FactRef, Answer])(_ ++ _))
        Async.async[Map[FactRef, Answer], Rest](cb => Async.start(all).future.onComplete {
          case scala.util.Success(m) => cb(Right(m))
          case _ => cb(Right(Map.empty))
        }(using ExecutionContext.parasitic)).flatMap(k)))

  /** an answer of the fact's kind and sort: a relation true or false, a function's value of its result's sort */
  def fits(checked: Checked, ref: FactRef, a: Answer): Boolean = (checked.facts.get(ref.name), a) match
    case (Some(FactSig(_, _, None, _)), Answer.Holds(_)) => true
    case (Some(FactSig(_, _, Some(sort), _)), Answer.Is(v)) => (sort, v) match
      case (Sort.Int, Value.I(_)) | (Sort.Dec, Value.D(_)) | (Sort.Text, Value.T(_)) => true
      case (Sort.Entity(t), Value.E(s, _)) => t == s
      case _ => false
    case _ => false

  /** the facts of a map: a test's `given`, a request's known facts */
  def known[R[_], Rest[_], A](known: Map[FactRef, Answer])(p: A ! R)(using Split[Facts, R, Rest]): A ! Rest =
    handle(p, Handler.tail[Facts, Rest, A, A](pure)([X] => (op: Facts[X]) => op match
      case Ask(refs) => refs.flatMap(r => known.get(r).map(r -> _)).toMap))

/** A SOURCE OF FACTS: asked all of a decision's facts it is the source of, at once, asynchronously — Stripe's API, a
 * database, an MCP server's tool, the session. What it does not answer is unknown */
trait Source:
  def ask(refs: List[FactRef]): Map[FactRef, Answer] ! Async

object Source:
  /** a source answering by a future: an HTTP client's, a driver's */
  def future(f: List[FactRef] => Future[Map[FactRef, Answer]]): Source = refs => Async.fromFuture(f(refs))

  /** a source answering at once, each fact alone: the session's, a map, a function */
  def of(f: FactRef => Option[Answer]): Source = refs => pure(refs.flatMap(r => f(r).map(r -> _)).toMap)

  /** a source of no fact */
  val none: Source = _ => pure(Map.empty)

/** a change of a state: set, or added to, or taken from — applied by the store, atomically with the others of its
 * decision */
final case class StateChange(ref: FactRef, change: Change, value: Value)

/** THE GUARD'S STATE: read for a decision, changed after it */
enum States[X]:
  case Read(refs: List[FactRef]) extends States[Map[FactRef, Value]]
  case Update(changes: List[StateChange]) extends States[Unit]

object States:
  def read[R[_]](refs: List[FactRef])(using In[States, R]): Map[FactRef, Value] ! R =
    if refs.isEmpty then pure(Map.empty) else perform[States](Read(refs))

  def update[R[_]](changes: List[StateChange])(using In[States, R]): Unit ! R =
    if changes.isEmpty then unit else perform[States](Update(changes))

  /** a state in memory: each value with the start of its window; `now` the time in milliseconds */
  final class Memory(checked: Checked, now: () => Long = () => System.currentTimeMillis()):
    private val values = scala.collection.mutable.Map.empty[FactRef, (Value, Long)]

    /** a value, the state's initial one if never set or if its window has passed */
    def get(ref: FactRef): Value =
      val sig = checked.states(ref.name)
      values.get(ref) match
        case Some((v, since)) if sig.window.forall(w => window(w, now()) == since) => v
        case _ => sig.init

    def set(ref: FactRef, v: Value): Unit =
      values(ref) = (v, checked.states(ref.name).window.fold(0L)(window(_, now())))

    private def window(w: Window, t: Long): Long = t - Math.floorMod(t, w.millis)

    def change(c: StateChange): Unit = synchronized {
      val old = get(c.ref)
      set(c.ref, c.change match
        case Change.Set => c.value
        case Change.Add => Eval.plus(old, c.value)
        case Change.Sub => Eval.minus(old, c.value))
    }

    /** the handler of `States` on this memory */
    def handler[R[_], Rest[_], A](p: A ! R)(using Split[States, R, Rest]): A ! Rest =
      handle(p, Handler.tail[States, Rest, A, A](pure)([X] => (op: States[X]) => op match
        case Read(refs) => synchronized(refs.map(r => r -> get(r)).toMap)
        case Update(changes) => changes.foreach(change)))
