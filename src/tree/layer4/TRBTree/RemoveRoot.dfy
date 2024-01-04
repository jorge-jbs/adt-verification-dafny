include "../../../../src/Collections/Option.dfy"
include "../../../../src/Collections/Set.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/Remove.dfy"

module {:options "-functionSyntax:4"} TRBTree.RemoveRoot {
  import opened Option
  import opened Set
  import opened KeyValue
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
    if k in keys(t) {
      SizeLemmas(t);
      SizeLemmas(RemoveRoot(t, k).unwrap);
    } else {
      SizeLemmas(t);
      SizeLemmas(RemoveRoot(t, k).unwrap);
    }
  }

  lemma RemoveRootSize(t: trbtree, k: K)
    requires RemoveRoot(t, k).Some?
    ensures
      if IsRemovedRoot(t, k) then
        size(RemoveRoot(t, k).unwrap) == size(t) - 1
      else
        size(RemoveRoot(t, k).unwrap) == size(t)
  {
    RemoveSize(ConditionalReddenRoot(t), false, k);
  }

  lemma RemoveRootModel(t: trbtree, k: K)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)

    ensures RemoveRoot(t, k).Some?
    ensures SearchTree(RemoveRoot(t, k).unwrap)
    ensures toMapRec(RemoveRoot(t, k).unwrap) == toMapRec(t) - {k}
    ensures
      if k in toMapRec(t) then
        |toMapRec(RemoveRoot(t, k).unwrap)| == |toMapRec(t)| - 1
      else
        |toMapRec(RemoveRoot(t, k).unwrap)| == |toMapRec(t)|
  {
    RemoveSpec(ConditionalReddenRoot(t), false, k);
    RemoveModel(ConditionalReddenRoot(t), false, k);
    if k in toMapRec(t) {
      assert |toMapRec(RemoveRoot(t, k).unwrap)| == |toMapRec(t)| - 1 by {
        SizeLemmas(t);
        SizeLemmas(RemoveRoot(t, k).unwrap);
        ToMapRecKeys(t);
        ToMapRecKeys(RemoveRoot(t, k).unwrap);
        SubCard(keys(t), {k});
      }
    } else {
      assert |toMapRec(RemoveRoot(t, k).unwrap)| == |toMapRec(t)| by {
        SizeLemmas(t);
        SizeLemmas(RemoveRoot(t, k).unwrap);
        ToMapRecKeys(t);
        ToMapRecKeys(RemoveRoot(t, k).unwrap);
      }
    }
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
