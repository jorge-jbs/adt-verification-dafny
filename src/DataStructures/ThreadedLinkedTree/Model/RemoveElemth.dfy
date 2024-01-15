include "../../../../src/Collections/KeyValue.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"

module {:options "-functionSyntax:4"} ThreadedLinkedTree.Model.RemoveElemth {
  import opened KeyValue
  import opened Base
  import opened OrderedSetUtils

  function SRemoveMin(t: trbtreeOrThread): (trbtreeOrThread, K, V)
    requires t.Node?
    requires SearchTree(t)
  {
    match t.left
    case Empty|Thread(_) =>
      ( t.right
      , t.key
      , t.value
      )
    case Node(_, _, _, _, _) =>
      var (l', minK, minV) := SRemoveMin(t.left);
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

  lemma SRemoveMinSpec(t: trbtree)
    requires t.Node?
    requires SearchTree(t)

    ensures keys(SRemoveMin(t).0) == keys(t) - {SRemoveMin(t).1}
    ensures inorder(t) == [(SRemoveMin(t).1, SRemoveMin(t).2)] + inorder(SRemoveMin(t).0)
    ensures |inorder(SRemoveMin(t).0)| == |inorder(t)| - 1
    ensures SRemoveMin(t).1 in keys(t)
    ensures SRemoveMin(t).1 !in keys(SRemoveMin(t).0)
    ensures forall k | k in keys(SRemoveMin(t).0) :: SRemoveMin(t).1 < k

    ensures SearchTree(SRemoveMin(t).0)
  {
    if IsThreadOrEmpty(t.left) {
    } else {
      SRemoveMinSpec(t.left);
    }
  }

  lemma SRemoveMinMinimum(t: trbtree)
    requires t.Node?
    requires SearchTree(t)
    ensures assert toMap(t).Keys == keys(t); true
    ensures minimum(toMap(t).Keys) == minimum(keys(t)) == SRemoveMin(t).1
  {
    assert toMap(t).Keys == keys(t);
    SRemoveMinSpec(t);
    lminimumrev(keys(t), SRemoveMin(t).1);
  }

  lemma SRemoveMinCard(t: trbtree)
    requires t.Node?
    requires SearchTree(t)
    requires SearchTree(SRemoveMin(t).0)

    ensures |keys(SRemoveMin(t).0)| == |keys(t)| - 1
    ensures |toMap(SRemoveMin(t).0)| == |toMap(t)| - 1
  {
    SRemoveMinSpec(t);
    calc == {
      |toMap(SRemoveMin(t).0)|;
      { SizeLemmas(SRemoveMin(t).0); }
      |keys(SRemoveMin(t).0)|;
      |keys(t)| - 1;
      { SizeLemmas(t); }
      |toMap(t)| - 1;
    }
  }

  lemma Drop1Index<A>(s: seq<A>, i: nat)
    requires i < |s|
    requires i > 0
    ensures |s| - 1 == |s[1..]|
    ensures s[i] == s[1..][i-1]
  {}

  lemma ElemthInorder0(t: trbtree)
    requires SearchTree(t)
    requires toMap(t) != map[] || t.Node?
    ensures assert toMap(t).Keys == keys(t); true
    ensures elemth(toMap(t).Keys, 0) == inorder(t)[0].0
  {
    assert elemth(toMap(t).Keys, 0) == minimum(toMap(t).Keys);
    SearchImpliesOrdered(t);
    var s := inorder(t);
    assert forall x | x in s :: s[0].0 <= x.0;
    assert forall x | x in orderKeysToSet(s) :: s[0].0 <= x;
    OrderKeysIsTreeKeys(t);
    assert orderKeysToSet(s) == toMap(t).Keys;
    if minimum(toMap(t).Keys) != s[0].0 {
      assert s[0].0 in toMap(t).Keys;
      lmin(toMap(t).Keys, s[0].0);
      assert minimum(toMap(t).Keys) <= s[0].0;

      assert minimum(toMap(t).Keys) in orderKeysToSet(s);
      assert s[0].0 <= minimum(toMap(t).Keys);

      assert minimum(toMap(t).Keys) < s[0].0;
      assert s[0].0 < minimum(toMap(t).Keys);

      assert false;
    }
  }

  lemma ElemthInorder(t: trbtree, i: nat)
    decreases i
    requires SearchTree(t)
    requires toMap(t) != map[] || t.Node?
    requires i < |toMap(t)|
    requires i < |inorder(t)|
    ensures elemth(toMap(t).Keys, i) == inorder(t)[i].0
  {
    if t.Empty? {
    } else if i == 0 {
      ElemthInorder0(t);
    } else {
      var (t', minK, minV) := SRemoveMin(t);
      SRemoveMinSpec(t);
      assert |inorder(t')| == |inorder(t)| - 1;
      SRemoveMinCard(t);
      assert |toMap(t')| == |toMap(t)| - 1;
      calc == {
        elemth(toMap(t).Keys, i);
        elemth(toMap(t).Keys - {minimum(toMap(t).Keys)}, i-1);
        {
          SRemoveMinMinimum(t);
          assert minK == minimum(toMap(t).Keys);
        }
        elemth(toMap(t).Keys - {minK}, i-1);
        {
          calc == {
            toMap(t').Keys;
            keys(t');
            keys(t) - {minK};
            toMap(t).Keys - {minK};
          }
        }
        elemth(toMap(t').Keys, i-1);
        { ElemthInorder(t', i-1); }
        inorder(SRemoveMin(t).0)[i-1].0;
        { Drop1Index([inorder(t)[0]] + inorder(SRemoveMin(t).0), i); }
        ([inorder(t)[0]] + inorder(SRemoveMin(t).0))[i].0;
        ([inorder(t)[0]] + inorder(t)[1..])[i].0;
        inorder(t)[i].0;
      }
    }
  }

  lemma PeekKeyElemth(t: trbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
    requires SearchTree(t)
    requires inorder(t) == traversed + st
    requires st != []
    requires |keys(t)| == |inorder(t)|
    ensures st[0].0 == elemth(keys(t), |traversed|)
  {
    assert SearchTree(t);
    assert toMap(t) != map[] || t.Node?;
    assert |traversed| < |inorder(t)|;
    SizeLemmas(t);
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

  lemma PeekElemth(t: trbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
    requires SearchTree(t)
    requires inorder(t) == traversed + st
    requires st != []
    requires |keys(t)| == |inorder(t)|
    ensures st[0].0 == elemth(keys(t), |traversed|)
    ensures st[0].1 == toMap(t)[st[0].0]
  {
    PeekKeyElemth(t, traversed, st);
    GetInorder(t, |traversed|);
  }

  lemma TraversedSmaller(t: trbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
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
        ensures (
          k in orderKeysToSet(traversed) <==>
            k in smaller(keys(t), elemth(keys(t), |traversed|))
        )
      {
        
        assert toMap(t).Keys == keys(t);
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
