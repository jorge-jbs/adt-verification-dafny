include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/RBTree/Base.dfy"
include "../../../../src/tree/layer1/OrderedSetUtils.dfy"

module RBTree.RemoveElemth {
  //import opened Utils
  import opened KeyValue
  import opened Base
  import opened OrderedSetUtils

  function method RemoveMin(t: rbtree): (rbtree, K, V)
    requires t.Node?
    requires SearchTree(t)
  {
    if t.left.Empty? then
      (t.right, t.key, t.value)
    else
      var (l', minK, minV) := RemoveMin(t.left);
      ( Node(
          l',
          t.key,
          t.value,
          t.right,
          t.color
        )
      , minK
      , minV
      )
  }
  
  lemma RemoveMinSpec(t: rbtree)
    requires t.Node?
    requires SearchTree(t)

    ensures keys(RemoveMin(t).0) == keys(t) - {RemoveMin(t).1}
    //ensures |toMap(RemoveMin(t).0)| == |toMap(t)| - 1;
    ensures inorder(t) == [(RemoveMin(t).1, RemoveMin(t).2)] + inorder(RemoveMin(t).0)
    ensures |inorder(RemoveMin(t).0)| == |inorder(t)| - 1;
    ensures RemoveMin(t).1 in keys(t)
    ensures RemoveMin(t).1 !in keys(RemoveMin(t).0)
    ensures forall k | k in keys(RemoveMin(t).0) :: RemoveMin(t).1 < k

    ensures SearchTree(RemoveMin(t).0)
  {
    if t.left.Empty? {
    } else {
      RemoveMinSpec(t.left);
    }
  }
  lemma RemoveMinCard(t: rbtree)
    requires t.Node?
    requires SearchTree(t)
    requires SearchTree(RemoveMin(t).0)

    ensures |keys(RemoveMin(t).0)| == |keys(t)| - 1;
    ensures |toMap(RemoveMin(t).0)| == |toMap(t)| - 1;
  {
    RemoveMinSpec(t);
    calc == {
      |toMap(RemoveMin(t).0)|;
      { assume false; toMapCard(RemoveMin(t).0);}
      |keys(RemoveMin(t).0)|;
      |keys(t)| - 1;
      { assume false; toMapCard(t); }
      |toMap(t)| - 1;
    }
  }

  lemma Drop1Index<A>(s: seq<A>, i: nat)
    requires i < |s|
    requires i > 0
    ensures |s| - 1 == |s[1..]|
    ensures s[i] == s[1..][i-1]
  {}

  lemma ElemthInorder(t: rbtree, i: nat)
    decreases i
    requires SearchTree(t)
    requires toMap(t) != map[] || t.Node?
    requires i < |toMap(t)|
    requires i < |inorder(t)|
    ensures elemth(toMap(t).Keys, i) == inorder(t)[i].0
  {
    if t.Empty? {
    } else if i == 0{
      ElemthInorder0(t);
    } else {
      var (t', minK, minV) := RemoveMin(t);
      RemoveMinSpec(t);
      assert |inorder(t')| == |inorder(t)| - 1;
      RemoveMinCard(t);
      assert |toMap(t')| == |toMap(t)| - 1;
      ElemthInorder(t', i-1);
      calc == {
        elemth(toMap(t).Keys, i);
        { assume false; }
        elemth(toMap(RemoveMin(t).0).Keys, i-1);
        inorder(RemoveMin(t).0)[i-1].0;
        { Drop1Index([inorder(t)[0]] + inorder(RemoveMin(t).0), i); }
        ([inorder(t)[0]] + inorder(RemoveMin(t).0))[i].0;
        ([inorder(t)[0]] + inorder(t)[1..])[i].0;
        inorder(t)[i].0;
      }
    }
  }

  lemma PeekElemth(t: rbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
    requires SearchTree(t)
    requires inorder(t) == traversed + st
    requires st != []
    requires |keys(t)| == |inorder(t)|
    ensures st[0].0 == elemth(keys(t), |traversed|)
  {
    assert SearchTree(t);
    assert toMap(t) != map[] || t.Node?;
    assert |traversed| < |inorder(t)|;
    toMapCard(t);
    assert |traversed| < |keys(t)| == |toMap(t)|;
    ElemthInorder(t, |traversed|);
    calc == {
      elemth(keys(t), |traversed|);
      { assert keys(t) == toMap(t).Keys; }
      elemth(toMap(t).Keys, |traversed|);
      inorder(t)[|traversed|].0;
      st[0].0;
    }
  }

  lemma TraversedSmaller(t: rbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
    requires SearchTree(t)
    requires inorder(t) == traversed + st
    requires st != []
    requires |keys(t)| == |inorder(t)|
    ensures orderKeysToSet(traversed) == smaller(keys(t), elemth(keys(t), |traversed|))
  {
    if t.Empty? {
    } else {
      calc == {
        |toMap(t)|;
        |toMap(t).Keys|;
        { assert toMap(t).Keys == keys(t); }
        |keys(t)|;
        { SizeKeys(t); }
        size(t);
        { SizeInorder(t); }
        |inorder(t)|;
      }
      forall k
        ensures k in orderKeysToSet(traversed)
          <==> k in smaller(keys(t), elemth(keys(t), |traversed|))
      {
        if k in orderKeysToSet(traversed) {
          var i :| 0 <= i < |traversed| && traversed[i].0 == k;
          assert inorder(t)[i] == traversed[i];

          ElemthInorder(t, i);
          var a := elemth(toMap(t).Keys, i);
          assert a == inorder(t)[i].0;

          ElemthInorder(t, |traversed|);
          var b := elemth(toMap(t).Keys, |traversed|);
          assert b == elemth(toMap(t).Keys, |traversed|);

          SearchImpliesOrdered(t);
          assert a < b;
        }
        if k in smaller(keys(t), elemth(keys(t), |traversed|)) {
          assert k in keys(t);
          KeyInOrder(t, k);
          var i :| 0 <= i < |inorder(t)| && inorder(t)[i].0 == k;
          
          ElemthInorder(t, i);
          var a := elemth(toMap(t).Keys, i);
          assert a == inorder(t)[i].0;

          ElemthInorder(t, |traversed|);
          var b := elemth(toMap(t).Keys, |traversed|);
          assert b == elemth(toMap(t).Keys, |traversed|);

          SearchImpliesOrdered(t);
          assert a < b;
        }
      }
    }
  }
}
