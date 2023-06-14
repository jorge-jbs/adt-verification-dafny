include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/RBTree/Base.dfy"
include "../../../../src/tree/layer1/OrderedSetUtils.dfy"

module RBTree.RemoveElemth {
  //import opened Utils
  import opened KeyValue
  import opened Base
  import opened OrderedSetUtils

  function method RemoveMax(t: rbtree): (rbtree, K, V)
    requires t.Node?
    requires SearchTree(t)
  {
    if t.right.Empty? then
      (t.left, t.key, t.value)
    else
      var (r', maxK, maxV) := RemoveMax(t.right);
      ( Node(
          t.left,
          t.key,
          t.value,
          r',
          t.color
        )
      , maxK
      , maxV
      )
  }
  
  lemma RemoveMaxSpec(t: rbtree)
    requires t.Node?
    requires SearchTree(t)

    ensures keys(RemoveMax(t).0) == keys(t) - {RemoveMax(t).1}
    //ensures |toMap(RemoveMax(t).0)| == |toMap(t)| - 1;
    ensures inorder(t) == inorder(RemoveMax(t).0) + [(RemoveMax(t).1, RemoveMax(t).2)]
    ensures |inorder(RemoveMax(t).0)| == |inorder(t)| - 1;
    ensures RemoveMax(t).1 in keys(t)
    ensures RemoveMax(t).1 !in keys(RemoveMax(t).0)
    ensures forall k | k in keys(RemoveMax(t).0) :: k < RemoveMax(t).1

    ensures SearchTree(RemoveMax(t).0)
  {
    if t.right.Empty? {
    } else {
      RemoveMaxSpec(t.right);
    }
  }
  lemma RemoveMaxCard(t: rbtree)
    requires t.Node?
    requires SearchTree(t)
    requires SearchTree(RemoveMax(t).0)

    ensures |keys(RemoveMax(t).0)| == |keys(t)| - 1;
    ensures |toMap(RemoveMax(t).0)| == |toMap(t)| - 1;
  {
    RemoveMaxSpec(t);
    calc == {
      |toMap(RemoveMax(t).0)|;
      { toMapCard(RemoveMax(t).0); }
      |keys(RemoveMax(t).0)|;
      |keys(t)| - 1;
      { toMapCard(t); }
      |toMap(t)| - 1;
    }
  }

  lemma Drop1Index<A>(s: seq<A>, i: nat)
    requires i < |s|
    requires i > 0
    ensures |s| - 1 == |s[1..]|
    ensures s[i] == s[1..][i-1]
  {}

  lemma NodeCard(t: rbtree)
    requires t.Node?
    ensures size(t) >= 1
  {}

  lemma ElemthInorderInd(t: rbtree)
    requires SearchTree(t)
    requires |inorder(t)| == |toMap(t).Keys|
    requires t.Node?
    ensures elemth(toMap(t).Keys, |inorder(t.left)|) == inorder(t)[|inorder(t.left)|].0
  {
    assume false;
  }

  lemma SizeLemmas(t: rbtree)
    requires SearchTree(t)
    ensures size(t)
      == |inorder(t)|
      == |keys(t)|
      == |toMap(t).Keys|
      == |toMap(t)|

  lemma DafnyYouAreStupid(a: nat, b: nat)
    requires a >= b
    requires a <= b
    ensures a == b
  {}

  lemma AllElemthInorder(t: rbtree)
    requires SearchTree(t)
    requires |inorder(t)| == |toMap(t).Keys|
    ensures forall i | 0 <= i < |inorder(t)| ::
      elemth(toMap(t).Keys, i) == inorder(t)[i].0
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) => {
        SizeLemmas(l);
        AllElemthInorder(l);
        SizeLemmas(r);
        AllElemthInorder(r);
        forall i | 0 <= i < |inorder(t)|
          ensures elemth(toMap(t).Keys, i) == inorder(t)[i].0
        {
          if i == |inorder(l)| {
            assume false;
          } else if i < |inorder(l)| {
            calc == {
              inorder(t)[i].0;
              inorder(l)[i].0;
              elemth(toMap(l).Keys, i);
              { assume false; }
              elemth(toMap(t).Keys, i);
            }
          } else if |inorder(l)| < i {
            calc == {
              inorder(t)[i].0;
              inorder(r)[i - |inorder(l)| - 1].0;
              elemth(toMap(r).Keys, i - |inorder(l)| - 1);
              { assume false; }
              elemth(toMap(t).Keys, i);
            }
          } else {
            assert false;
          }
        }
      }
    }
  }

/*
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
  */
}
