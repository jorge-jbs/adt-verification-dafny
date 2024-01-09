include "../../../../src/Collections/KeyValue.dfy"
include "../../../../src/Collections/Option.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/Iterator.dfy"

module {:options "-functionSyntax:4"} TRBTree.Find {
  import opened KeyValue
  import opened Option
  import opened Color
  import opened Base
  import opened Iterator

  function Find(t: trbtreeOrThread, k: K): iter
  {
    match t
    case Empty|Thread(_) => PastTheEnd
    case Node(l, k', v', r, c) =>
      if k == k' then
        Link(k)
      else if k < k' then
        Find(t.left, k)
      else
        Find(t.right, k)
  }

  lemma FindSpec(t: trbtreeOrThread, k: K)
    requires SearchTree(t)
    ensures Valid(Find(t, k), ForgetThread(t))
    ensures k in keys(t) <==> HasPeek(Find(t, k))
    ensures k !in keys(t) ==> Find(t, k).PastTheEnd?
  {}
}
