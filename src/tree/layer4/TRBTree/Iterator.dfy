include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/RemoveElemth.dfy"
include "../../../../src/tree/layer1/OrderedSetUtils.dfy"

module {:options "-functionSyntax:4"} TRBTree.Iterator {
  import opened Utils.Set
  import opened KeyValue
  import opened Color
  import opened Base
  import opened RemoveElemth
  import opened OrderedSetUtils

  datatype iter
    = PastTheBeginning
    | PastTheEnd
    | Link(link: K)

  predicate Valid(it: iter, root: trbtree)
  {
    it.Link? ==> it.link in keys(root)
  }

  function Index(it: iter, root: trbtree): int
  {
    match it {
      case PastTheBeginning => -1
      case PastTheEnd => size(root)
      case Link(k) => sizeSmaller(root, k)
    }
  }

  lemma SizeIndex(it: iter, root: trbtree)
    requires SearchTree(root)
    ensures Index(it, root) <= |toMapRec(root)|
  {
    if it.Link? {
      SizeSmaller(root, it.link);
    }
    SizeLemmas(root);
  }

  predicate HasPeek(it: iter)
  {
    it.Link?
  }

  predicate HasPeek'(it: iter, root: trbtree)
    requires SearchTree(root)
  {
    0 <= Index(it, root) < |toMapRec(root)|
  }

  lemma HasPeekEq(it: iter, root: trbtree)
    requires Valid(it, root)
    requires SearchTree(root)
    ensures HasPeek(it) == HasPeek'(it, root)
  {
    if HasPeek(it) {
      assert it.Link?;
      assert Index(it, root) < size(root) by {
        if it.Link? {
          SizeSmaller(root, it.link);
        }
      }
      assert size(root) == |toMapRec(root)| by {
        SizeLemmas(root);
      }
      assert Index(it, root) < |toMapRec(root)|;
    }
    if HasPeek'(it, root) {
      assert 0 <= Index(it, root) < |toMapRec(root)|;
      assert size(root) == |toMapRec(root)| by {
        SizeLemmas(root);
      }
      assert it.Link?;
    }
  }

  function Peek(it: iter, root: trbtree): (K, V)
    requires HasPeek(it)
    requires Valid(it, root)
  {
    (it.link, Get'(root, it.link))
  }

  ghost function Peek'(it: iter, root: trbtree): (K, V)
    requires SearchTree(root)
    requires HasPeek'(it, root)
  {
    var k := elemth(toMapRec(root).Keys, Index(it, root));
    (k, toMapRec(root)[k])
  }

/*
  function Peek(it: iter, root: trbtree): (K, V)
    requires HasPeek(it, root)
  {
    var s := inorder(root);
    var i := Index(it, root);
    SizeInorder(root);
    s[i]
  }
*/

  lemma PeekEq(it: iter, root: trbtree)
    requires Valid(it, root)
    requires SearchTree(root)
    requires HasPeek(it)
    requires HasPeek'(it, root)
    ensures Peek(it, root) == Peek'(it, root)
  {
    ToMapRec(root);
    calc == {
      elemth(toMapRec(root).Keys, Index(it, root));
      elemth(toMapRec(root).Keys, sizeSmaller(root, it.link));
      {
        if root.Node? {
          SizeSmaller(root, it.link);
          SizeLemmas(root);
          ElemthInorder(root, sizeSmaller(root, it.link));
        }
      }
      inorder(root)[sizeSmaller(root, it.link)].0;
      { SmallerInorderSize(root, it.link); }
      inorder(root)[|smallerInorder(root, it.link)|].0;
      { InorderOfSmallerInorderSize(root, it.link); }
      it.link;
    }
    var k := elemth(toMapRec(root).Keys, Index(it, root));
    calc == {
      Get'(root, it.link);
      { GetEqGet'(root, it.link); }
      Get(root, it.link);
      toMapRec(root)[it.link];
      toMapRec(root)[k];
    }
  }

  function Traversed(it: iter, root: trbtree): set<K>
  {
    match it {
      case PastTheBeginning => keys(root)
      case PastTheEnd => keys(root)
      case Link(k) => smallerKeys(root, k)
    }
  }

  ghost function Traversed'(it: iter, root: trbtree): set<K>
    requires SearchTree(root)
  {
    if Index(it, root) == -1 || Index(it, root) == |toMapRec(root)| then
      toMapRec(root).Keys
    else
      SizeIndex(it, root);
      lelemth(toMapRec(root).Keys, Index(it, root));
      smaller(toMapRec(root).Keys, elemth(toMapRec(root).Keys, Index(it, root)))
  }

  lemma TraversedEq(it: iter, root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires Valid(it, root)
    ensures Traversed(it, root) == Traversed'(it, root)
  {
    ToMapRec(root);
    if Index(it, root) == -1 || Index(it, root) == |toMapRec(root)| {
      assert |toMapRec(root)| == size(root) by {
        SizeLemmas(root);
      }
      if it.Link? {
        SizeSmaller(root, it.link);
        assert false;
      }
      assert it.PastTheBeginning? || it.PastTheEnd?;
      assert toMapRec(root).Keys == keys(root);
    } else {
      SizeIndex(it, root);
      lelemth(toMapRec(root).Keys, Index(it, root));
      HasPeekEq(it, root);
      calc == {
        smaller(toMapRec(root).Keys, elemth(toMapRec(root).Keys, Index(it, root)));
        { PeekEq(it, root); }
        smaller(toMapRec(root).Keys, it.link);
        smaller(keys(root), it.link);
        { SmallerKeys(root, it.link); }
        smallerKeys(root, it.link);
      }
    }
  }

  lemma TraversedIndex(it: iter, root: trbtree)
    requires it.Link? || it.PastTheEnd?
    requires SearchTree(root)
    ensures |Traversed(it, root)| == Index(it, root)
  {
    SizeLemmas(root);
  }

  function First(root: trbtree): iter
  {
    if root.Node? then
      Link(minimumKey(root))
    else
      PastTheEnd
  }

  lemma FirstSpec(root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    ensures Valid(First(root), root)
  {}

  lemma FirstTraversed(root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    ensures Traversed(First(root), root) == {}
  {
    if root.Node? {
      SearchImpliesOrdered(root);
      SmallerKeys(root, First(root).link);
      forall k | k in keys(root)
        ensures !(k < minimumKey(root))
      {
        KeyInOrder(root, k);
      }
    }
  }

  lemma FirstIndex(root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    ensures Index(First(root), root) == 0
  {
    FirstTraversed(root);
    TraversedIndex(First(root), root);
  }

  function Find(k: K, root: trbtree): iter
  {
    if k in keys(root) then
      Link(k)
    else
      PastTheEnd
  }

  lemma FindPeek(k: K, root: trbtree)
    requires k in keys(root)
    ensures Peek(Find(k, root), root) == (k, Get'(root, k))
  {}

  lemma FindAfterInsert(k: K, v: V, root: trbtree)
    requires SearchTree(root)
    requires k in keys(root)
    requires assert keys(root) == toMapRec(root).Keys by {ToMapRecKeys(root);} true
    requires toMapRec(root)[k] == v
    ensures Peek(Find(k, root), root) == (k, v)
  {
    assert Peek(Find(k, root), root).0 == k;
    assert Peek(Find(k, root), root).1 == v by {
      Get'ToMapRec(root, k);
    }
  }

  function Next(it: iter, root: trbtree): iter
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
  {
    var t := GetSubtree(root, it.link);
    match t.right
    case Empty => PastTheEnd
    case Thread(k) =>
      assert k in keys(root) by {
        assert k in keysAndThreads(t);
        assert k in keysAndThreads(root);
        ThreadedKeys(root);
      }
      Link(k)
    case Node(_, _, _, _, _) =>
      Link(minimumKey(t.right))
  }

  lemma NextSpec(it: iter, root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures Valid(Next(it, root), root)
  {
    var t := GetSubtree(root, it.link);
    match t.right
    case Empty =>
    case Thread(k) =>
      assert k in keysAndThreads(t);
      assert k in keysAndThreads(root);
      ThreadedKeys(root);
    case Node(_, _, _, _, _) =>
  }

  lemma NextTraversed(it: iter, root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures Traversed(Next(it, root), root)
      == Traversed(it, root) + {Peek(it, root).0}
  {
    var t := GetSubtree(root, it.link);
    match t.right
    case Empty =>
      SmallerKeysRightEmpty(t, root);
    case Thread(k) =>
      SmallerKeysRightThread(t, root);
    case Node(_, _, _, _, _) =>
      SmallerKeysMin(t, root);
  }

  function Prev(it: iter, root: trbtree): iter
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
  {
    var t := GetSubtree(root, it.link);
    match t.left
    case Empty => PastTheBeginning
    case Thread(k) =>
      assert k in keys(root) by {
        assert k in keysAndThreads(t);
        assert k in keysAndThreads(root);
        ThreadedKeys(root);
      }
      Link(k)
    case Node(_, _, _, _, _) =>
      Link(maximumKey(t.left))
  }

  lemma ModelAfterInsert(it: iter, k: K, v: V, root: trbtree, root': trbtree)
    requires SearchTree(root)
    requires SearchTree(root')
    requires Valid(it, root)
    requires toMapRec(root') == toMapRec(root)[k := v]

    ensures Valid(it, root')
    ensures HasPeek(it) && (k !in keys(root) || k != it.link) ==>
      Peek(it, root') == Peek(it, root)
    ensures
      if k in keys(root) || it.PastTheBeginning? || (it.Link? && it.link < k) then
        Index(it, root') == Index(it, root)
      else
        Index(it, root') == Index(it, root) + 1
    ensures
      if k in keys(root) || (it.Link? && it.link < k) then
        && Traversed(it, root') == Traversed(it, root)
        && |Traversed(it, root')| == |Traversed(it, root)|
      else
        && Traversed(it, root') == Traversed(it, root) + {k}
        && |Traversed(it, root')| == |Traversed(it, root)| + 1
  {
    ToMapRecKeys(root);
    ToMapRecKeys(root');
    assert Valid(it, root');
    if HasPeek(it) && (k !in keys(root) || k != it.link) {
      calc == {
        Peek(it, root');
        (it.link, Get'(root', it.link));
        { Get'ToMapRec(root', it.link); }
        (it.link, toMapRec(root')[it.link]);
        (it.link, toMapRec(root)[it.link]);
        { Get'ToMapRec(root, it.link); }
        (it.link, Get'(root, it.link));
        Peek(it, root);
      }
    }
    if it.Link? {
      SmallerKeys(root, it.link);
      SmallerKeys(root', it.link);
    }
    if k in keys(root) {
      assert Traversed(it, root') == Traversed(it, root) by {
      }
    } else if !it.Link? || k < it.link {
      assert Traversed(it, root') == Traversed(it, root) + {k} by {
      }
    } else {
      assert Traversed(it, root') == Traversed(it, root) by {
      }
    }
    if it.Link? || it.PastTheEnd? {
      TraversedIndex(it, root);
      TraversedIndex(it, root');
    }
    if k in keys(root) || it.PastTheBeginning? || (it.Link? && it.link < k) {
      assert Index(it, root') == Index(it, root) by {
      }
    } else {
      assert Index(it, root') == Index(it, root) + 1 by {
      }
    }
  }

  lemma ModelAfterRemove(it: iter, k: K, root: trbtree, root': trbtree)
    requires SearchTree(root)
    requires SearchTree(root')
    requires Valid(it, root)
    requires toMapRec(root') == toMapRec(root) - {k}

    ensures HasPeek(it) ==>
      if it.link == k then
        !Valid(it, root')
      else
        && Valid(it, root')
        && Peek(it, root') == Peek(it, root)
        && (
          if k in keys(root) && k < it.link then
            && Traversed(it, root') == Traversed(it, root) - {k}
            && |Traversed(it, root')| == |Traversed(it, root)| - 1
            && Index(it, root') == Index(it, root) - 1
          else
            && Traversed(it, root') == Traversed(it, root)
            && |Traversed(it, root')| == |Traversed(it, root)|
            && Index(it, root') == Index(it, root)
        )
    ensures !HasPeek(it) && Index(it, root) == -1 ==>
      && Valid(it, root')
      && Index(it, root') == -1
      && (
        if k in keys(root) then
          && Traversed(it, root') == Traversed(it, root) - {k}
          && |Traversed(it, root')| == |Traversed(it, root)| - 1
        else
          && Traversed(it, root') == Traversed(it, root)
          && |Traversed(it, root')| == |Traversed(it, root)|
      )
    ensures !HasPeek(it) && Index(it, root) == |toMapRec(root)| ==>
      && Valid(it, root')
      //&& Index(it, root') == |toMapRec(root')|
      && (
        if k in keys(root) then
          && Index(it, root') == Index(it, root) - 1
          && Traversed(it, root') == Traversed(it, root) - {k}
          && |Traversed(it, root')| == |Traversed(it, root)| - 1
        else
          && Index(it, root') == Index(it, root)
          && Traversed(it, root') == Traversed(it, root)
          && |Traversed(it, root')| == |Traversed(it, root)|
      )

    ensures var i := |smaller(toMapRec(root).Keys, k)|;
      true
      //&& ((Index(it, root)) < i ==> Index(it, root') == (Index(it, root)))
      //&& (i < (Index(it, root')) ==> Index(it, root) == (Index(it, root)) - 1)
  {
    if HasPeek(it) {
      ToMapRecKeys(root);
      ToMapRecKeys(root');
      if it.link != k {
        assert Valid(it, root');
        calc == {
          Peek(it, root');
          (it.link, Get'(root', it.link));
          { Get'ToMapRec(root', it.link); }
          (it.link, toMapRec(root')[it.link]);
          (it.link, toMapRec(root)[it.link]);
          { Get'ToMapRec(root, it.link); }
          (it.link, Get'(root, it.link));
          Peek(it, root);
        }
        if k in keys(root) && k < it.link {
          assert Traversed(it, root') == Traversed(it, root) - {k} by {
            SmallerKeys(root, it.link);
            SmallerKeys(root', it.link);
          }
          assert Index(it, root') == Index(it, root) - 1 by {
            TraversedIndex(it, root);
            calc == {
              Index(it, root');
              { TraversedIndex(it, root'); }
              |Traversed(it, root')|;
              |Traversed(it, root) - {k}|;
              {
                assert k in Traversed(it, root) by {
                  SmallerKeys(root, it.link);
                }
                SubCard(Traversed(it, root), {k});
              }
              |Traversed(it, root)| - |{k}|;
              |Traversed(it, root)| - 1;
              { TraversedIndex(it, root); }
              Index(it, root) - 1;
            }
          }
          assert |Traversed(it, root')| == |Traversed(it, root)| - 1 by {
            TraversedIndex(it, root);
            TraversedIndex(it, root');
          }
        } else {
          assert Traversed(it, root') == Traversed(it, root) by {
            SmallerKeys(root, it.link);
            SmallerKeys(root', it.link);
          }
          assert Index(it, root') == Index(it, root) by {
            TraversedIndex(it, root);
            TraversedIndex(it, root');
          }
          assert |Traversed(it, root')| == |Traversed(it, root)| by {
            TraversedIndex(it, root);
            TraversedIndex(it, root');
          }
        }
      }
    }
    if !HasPeek(it) && Index(it, root) == -1 {
      SizeLemmas(root);
      SizeLemmas(root');
      ToMapRecKeys(root);
      ToMapRecKeys(root');
    }
    if !HasPeek(it) && Index(it, root) == |toMapRec(root)| {
      SizeLemmas(root);
      SizeLemmas(root');
      ToMapRecKeys(root);
      ToMapRecKeys(root');
    }
  }

  lemma ModelAfterRemoveV2(it: iter, k: K, root: trbtree, root': trbtree)
    requires SearchTree(root)
    requires SearchTree(root')
    requires Valid(it, root)
    requires toMapRec(root') == toMapRec(root) - {k}

    ensures
      var i := |smaller(toMapRec(root).Keys, k)|;
      if Index(it, root) == i then
        !Valid(it, root')
      else
        && Valid(it, root')
        && (HasPeek(it) ==> Peek(it, root') == Peek(it, root))
        && (
          if k !in toMapRec(root) then
            && Index(it, root') == Index(it, root)
            && |Traversed(it, root')| == |Traversed(it, root)|
            && Traversed(it, root') == Traversed(it, root)
          else
            && (Index(it, root) == -1 ==>
              && Index(it, root') == -1
              && |Traversed(it, root')| == |Traversed(it, root)| - 1
              && Traversed(it, root') == Traversed(it, root) - {k}
            )
            && (0 <= Index(it, root) < i ==>
              && Index(it, root') == Index(it, root)
              && |Traversed(it, root')| == |Traversed(it, root)|
              && Traversed(it, root') == Traversed(it, root)
            )
            && (i < Index(it, root') ==>
              && Index(it, root) == Index(it, root) - 1
              && |Traversed(it, root)| == |Traversed(it, root)| - 1
              && Traversed(it, root) == Traversed(it, root) - {k}
            )
        )
      /*
      if Index(it, root) < i || k !in toMapRec(root) then
        Index(it, root') == Index(it, root)
      else
        Index(it, root) == Index(it, root) - 1
        */
  /*
  {
    ModelAfterRemove(it, k, root, root');
    SizeLemmas(root);
    SizeLemmas(root');
    ToMapRecKeys(root);
    ToMapRecKeys(root');
  }
  */
}
