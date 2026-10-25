package okay.policy

import okay.scala3.*

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

  /** the facts of a map: a test's `given`, a request's known facts */
  def known[R[_], Rest[_], A](known: Map[FactRef, Answer])(p: A ! R)(using Split[Facts, R, Rest]): A ! Rest =
    handle(p, Handler.tail[Facts, Rest, A, A](pure)([X] => (op: Facts[X]) => op match
      case Ask(refs) => refs.flatMap(r => known.get(r).map(r -> _)).toMap))

/** a change of a state: set, or added to, or taken from — applied by the store, atomically with the others of its
 * decision */
final case class StateChange(ref: FactRef, change: Change, value: Value)

/** THE GUARD'S STATE: read for a decision, changed after it */
enum Store[X]:
  case Read(refs: List[FactRef]) extends Store[Map[FactRef, Value]]
  case Update(changes: List[StateChange]) extends Store[Unit]

object Store:
  def read[R[_]](refs: List[FactRef])(using In[Store, R]): Map[FactRef, Value] ! R =
    if refs.isEmpty then pure(Map.empty) else perform[Store](Read(refs))

  def update[R[_]](changes: List[StateChange])(using In[Store, R]): Unit ! R =
    if changes.isEmpty then unit else perform[Store](Update(changes))

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

    /** the handler of `Store` on this memory */
    def handler[R[_], Rest[_], A](p: A ! R)(using Split[Store, R, Rest]): A ! Rest =
      handle(p, Handler.tail[Store, Rest, A, A](pure)([X] => (op: Store[X]) => op match
        case Read(refs) => synchronized(refs.map(r => r -> get(r)).toMap)
        case Update(changes) => changes.foreach(change)))
