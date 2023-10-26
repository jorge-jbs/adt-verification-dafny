include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/Remove.dfy"

module {:options "-functionSyntax:4"} TRBTree.RemoveRoot {
  import opened KeyValue
  import opened Utils
  import opened Utils.Option
  import opened Color
  import opened Base
  import opened R = Remove

  function RemoveRoot(t: trbtree, k: K): option<trbtree>
  {
    var t' :- Remove(ConditionalReddenRoot(t), false, k);
    Some(BlackenRoot(ForgetThread(t')))
  }

  lemma RemoveRootSpec(t: trbtree, k: K)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)

    ensures RemoveRoot(t, k).Some?
    ensures SearchTree(RemoveRoot(t, k).unwrap)
    ensures RedBlackTreeRoot(RemoveRoot(t, k).unwrap)
    ensures keys(RemoveRoot(t, k).unwrap) == keys(t) - {k}
  {
    RemoveSpec(ConditionalReddenRoot(t), false, k);
  }

  lemma RemoveRootModel(t: trbtree, k: K)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)

    ensures RemoveRoot(t, k).Some?
    ensures SearchTree(RemoveRoot(t, k).unwrap)
    ensures toMap(RemoveRoot(t, k).unwrap) == toMap(t) - {k}

  predicate IsRemovedRoot(t: trbtree, k: K)
    requires RemoveRoot(t, k).Some?
  {
    IsRemoved(ConditionalReddenRoot(t), false, k)
  }

  lemma IsRemovedRootSpec(t: trbtree, k: K)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    requires RemoveRoot(t, k).Some?
    ensures IsRemovedRoot(t, k) <==> k in keys(t)
  {
    IsRemovedSpec(ConditionalReddenRoot(t), false, k);
  }
}
