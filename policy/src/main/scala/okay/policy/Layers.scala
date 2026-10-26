package okay.policy

/** a layer's word on a call: a rule's verdict, or none — no rule of it applied */
enum Said:
  case Rule(verdict: Verdict)
  case Nothing

/**
 * POLICIES IN LAYERS: an organization's, a team's, an agent's — each decides the same call. A layer that is not the
 * bottom one says nothing when no rule of it applied (its own default ignored); the words combine deny over ask over
 * allow; if no layer said anything, the BOTTOM layer's decision stands, its default with it. So a lower layer can make
 * a decision stricter, never looser; each layer's decision keeps its own proof.
 */
object Layers:
  /** what a layer's decision says, as a layer above the bottom */
  def said(d: Decision): Said = if d.byDefault then Said.Nothing else Said.Rule(d.verdict)

  /** the decisions of the layers, top first, the bottom last: the verdict, and the decisions it rests on */
  def combine(layers: List[Decision]): (Verdict, List[Decision]) =
    require(layers.nonEmpty, "no layer")
    val spoken = layers.filterNot(_.byDefault)
    def with_(v: Verdict) = spoken.filter(_.verdict == v)
    if with_(Verdict.Deny).nonEmpty then (Verdict.Deny, with_(Verdict.Deny))
    else if with_(Verdict.Ask).nonEmpty then (Verdict.Ask, with_(Verdict.Ask))
    else if with_(Verdict.Allow).nonEmpty then (Verdict.Allow, with_(Verdict.Allow))
    else (layers.last.verdict, List(layers.last))
