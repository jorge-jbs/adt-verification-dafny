include "../../../../src/Collections/KeyValue.dfy"
include "../../../../src/Collections/Option.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Iterator.dfy"

module {:options "-functionSyntax:4"} ThreadedLinkedTree.Model.Find {
  import opened KeyValue
  import opened Option
  import opened Color
  import opened Base
  import opened Iterator

  function Find(t: trbtreeOrThread, k: K): iter
  {
    match t
    case Empty|Thread(_) => Null
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
  {}
}
