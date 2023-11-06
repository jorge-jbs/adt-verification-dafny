include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/RemoveElemth.dfy"
include "../../../../src/tree/layer1/OrderedSetUtils.dfy"

module {:options "-functionSyntax:4"} TRBTree.Iterator {
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

  function Peek'(it: iter, root: trbtree): (K, V)
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

  function Traversed'(it: iter, root: trbtree): set<K>
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

  lemma {:verify false} ModelAfterInsert(it: iter, k: K, root: trbtree, root': trbtree)
    requires HasPeek(it)
    requires Valid(it, root)
    requires Valid(it, root')
    requires keys(root') == keys(root) + {k}

    ensures k !in keys(root) || k != it.link ==> Peek(it, root') == Peek(it, root)
    ensures
      if k !in keys(root) && k < it.link then
        && Index(it, root') == Index(it, root) + 1
        && Traversed(it, root') == Traversed(it, root) + {k}
      else
        && Index(it, root') == Index(it, root)
        && Traversed(it, root') == Traversed(it, root)
  {}

  lemma {:verify false} ModelAfterRemove(it: iter, k: K, root: trbtree, root': trbtree)
    requires HasPeek(it)
    requires Valid(it, root)
    requires Valid(it, root')
    requires keys(root') == keys(root) - {k}

    ensures Peek(it, root') == Peek(it, root)
    ensures
      if k in keys(root) && k < it.link then
        && Index(it, root') == Index(it, root) - 1
        && Traversed(it, root') == Traversed(it, root) - {k}
      else
        && Index(it, root') == Index(it, root)
        && Traversed(it, root') == Traversed(it, root)
  {}
}
