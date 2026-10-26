package okay.policy

import okay.proof.Json

/** a call's argument: a value, a record of fields, a list */
enum Data:
  case Leaf(v: Value)
  case Bit(b: Boolean)
  case Rec(fields: Map[String, Data])
  case Lst(items: List[Data])

/** A CALL to decide: its tool, who calls, its arguments by name — a missing optional one absent from the map */
final case class Call(tool: String, caller: Value, args: Map[String, Data]):
  /** the variables of a rule: `caller`, `tool`, and the call itself */
  def env: Map[String, Value] = Map("caller" -> caller, "tool" -> Value.T(tool), "call" -> Call.self)

object Call:
  /** the call, as an entity of the logic */
  val self: Value = Value.E(Types.callType, "call")

  /** a call of flat arguments */
  def flat(tool: String, caller: Value, args: Map[String, Value]): Call =
    Call(tool, caller, args.map((k, v) => k -> Data.Leaf(v)))

  /** what the call says, as facts: each value of a field an equation (`arg:amount(call) = 50`), each optional field
   * supplied or not (`has:arg:coupon(call)`), each list's count and members (`arg:items(call,
     #items0)`), each element's
   * fields as facts of the element (`Item.qty(#items0) = 3`) — and each list with all its elements. A field missing or
   * of the wrong kind is reported in `malformed`: such a call is denied */
  final case class Facts(facts: Map[FactRef, Answer], lists: Map[FactRef, List[Value]], malformed: List[String])

  def facts(checked: Checked, call: Call): Facts =
    val out = scala.collection.mutable.Map.empty[FactRef, Answer]
    val lists = scala.collection.mutable.Map.empty[FactRef, List[Value]]
    val bad = scala.collection.mutable.ListBuffer.empty[String]
    def fields(of: List[Field], supplied: Map[String, Data], prefix: String, base: Value, where: String): Unit =
      // a field the policy does not know is no concern of it: left out, as a client may send more than it needs
      for f <- of do
        val name = if prefix.endsWith(":") then prefix + f.name else s"$prefix.${f.name}"
        if f.optional then out(FactRef("has:" + name, List(base))) = Answer.Holds(supplied.contains(f.name))
        supplied.get(f.name) match
          case None => if !f.optional then bad += s"${where}'s ${f.name} is missing"
          case Some(d) => one(f.sort, d, name, base, s"$where.${f.name}")
    def one(s: Sort, d: Data, name: String, base: Value, where: String): Unit = (s, d) match
      case (Sort.Rec(r), Data.Rec(fs)) => fields(checked.records(r), fs, name, base, where)
      case (Sort.ListOf(el), Data.Lst(items)) =>
        val ref = FactRef(name, List(base))
        out(FactRef(name + "#count", List(base))) = Answer.Is(Value.I(items.size))
        val elems = items.zipWithIndex.flatMap { (item, i) =>
          val e: Option[Value] = el match
            case Sort.Rec(r) =>
              val v = Value.E(r, s"#$name#$i")
              item match
                case Data.Rec(fs) => fields(checked.records(r), fs, r, v, s"$where[$i]"); Some(v)
                case _ => bad += s"$where[$i] is not a $r"; None
            case scalar => item match
              case Data.Leaf(v) if fits(scalar, v) => Some(v)
              case _ => bad += s"$where[$i] is not a $scalar"; None
          e.foreach(v => out(FactRef(name, List(base, v))) = Answer.Holds(true))
          e
        }
        lists(ref) = elems.distinct
      case (Sort.Bool, Data.Bit(b)) => out(FactRef(name, List(base))) = Answer.Holds(b)
      case (scalar, Data.Leaf(v)) if fits(scalar, v) => out(FactRef(name, List(base))) = Answer.Is(v)
      case _ => bad += s"$where is not a $s"
    checked.calls.get(call.tool) match
      case Some(sig) => fields(sig.params, call.args, "arg:", Call.self, call.tool)
      case None => bad += s"an unknown tool ${call.tool}"
    Facts(out.toMap, lists.toMap, bad.toList)

  private def fits(s: Sort, v: Value): Boolean = (s, v) match
    case (Sort.Int, Value.I(_)) | (Sort.Dec, Value.D(_)) | (Sort.Text, Value.T(_)) => true
    case (Sort.Entity(t), Value.E(u, _)) => t == u
    case _ => false

  /** a call's arguments from JSON, by the tool's signature: numbers to `Int` or `Dec`, texts to `Text` or an entity's
   * name; what does not fit is left as it is, to be reported as malformed */
  def fromJson(checked: Checked, tool: String, caller: Value, args: Json): Call =
    def data(s: Sort, j: Json): Data = (s, j) match
      case (Sort.Int, Json.Num(t)) if t.forall(c => c.isDigit || c == '-') => Data.Leaf(Value.I(BigInt(t)))
      case (Sort.Dec, Json.Num(t)) => Data.Leaf(Value.D(BigDecimal(t)))
      case (Sort.Dec, Json.Str(t)) if t.nonEmpty && t.toDoubleOption.isDefined => Data.Leaf(Value.D(BigDecimal(t)))
      case (Sort.Text, Json.Str(t)) => Data.Leaf(Value.T(t))
      case (Sort.Bool, Json.Bool(b)) => Data.Bit(b)
      case (Sort.Entity(e), Json.Str(t)) => Data.Leaf(Value.E(e, t))
      case (Sort.Entity(e), Json.Num(t)) => Data.Leaf(Value.E(e, t))
      case (Sort.ListOf(el), Json.Arr(xs)) => Data.Lst(xs.map(data(el, _)))
      case (Sort.Rec(r), Json.Obj(fs)) =>
        val of = checked.records(r)
        Data.Rec(fs.collect { case (k, v) if v != Json.Null && of.exists(_.name == k) =>
          k -> data(of.find(_.name == k).get.sort, v) }.toMap)
      case _ => Data.Lst(List(Data.Leaf(Value.T(j.render)))) // of the wrong kind: reported as malformed
    val params = checked.calls.get(tool).fold(Nil)(_.params)
    val fields = args match
      case Json.Obj(fs) => fs.collect { case (k, v) if v != Json.Null && params.exists(_.name == k) =>
        k -> data(params.find(_.name == k).get.sort, v) }.toMap
      case _ => Map.empty
    Call(tool, caller, fields)
