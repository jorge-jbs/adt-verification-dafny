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
    ensures k in keys(t) ==> size(RemoveRoot(t, k).unwrap) == size(t) - 1
  {
    RemoveSpec(ConditionalReddenRoot(t), false, k);
    if k in keys(t) {
      SizeLemmas(t);
      SizeLemmas(RemoveRoot(t, k).unwrap);
    } else {
      SizeLemmas(t);
      SizeLemmas(RemoveRoot(t, k).unwrap);
    }
  }

  lemma RemoveRootModel(t: trbtree, k: K)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)

    ensures RemoveRoot(t, k).Some?
    ensures SearchTree(RemoveRoot(t, k).unwrap)
    ensures toMapRec(RemoveRoot(t, k).unwrap) == toMapRec(t) - {k}
  {
    RemoveSpec(ConditionalReddenRoot(t), false, k);
    RemoveModel(ConditionalReddenRoot(t), false, k);
  }

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
