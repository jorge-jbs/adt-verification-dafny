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
    | Link(link: netrbtree)

  predicate Valid(it: iter, root: trbtree)
  {
    && SearchTree(root)
    && ThreadedTreeRoot(root)
    && (it.Link? ==> Subtree(it.link, root))
  }

  function Index(it: iter, root: trbtree): int
  {
    match it {
      case PastTheBeginning => -1
      case PastTheEnd => size(root)
      case Link(t) => sizeSmaller(root, t.key)
    }
  }

  lemma SizeIndex(it: iter, root: trbtree)
    requires SearchTree(root)
    ensures Index(it, root) <= |toMap(root)|
  {
    if it.Link? {
      SizeSmaller(root, it.link.key);
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
    0 <= Index(it, root) < |toMap(root)|
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
          SizeSmaller(root, it.link.key);
        }
      }
      assert size(root) == |toMap(root)| by {
        SizeLemmas(root);
      }
      assert Index(it, root) < |toMap(root)|;
    }
    if HasPeek'(it, root) {
      assert 0 <= Index(it, root) < |toMap(root)|;
      assert size(root) == |toMap(root)| by {
        SizeLemmas(root);
      }
      assert it.Link?;
    }
  }

  function Peek(it: iter, root: trbtree): (K, V)
    requires HasPeek(it)
  {
    (it.link.key, it.link.value)
  }

  function Peek'(it: iter, root: trbtree): (K, V)
    requires SearchTree(root)
    requires HasPeek'(it, root)
  {
    var k := elemth(toMap(root).Keys, Index(it, root));
    (k, toMap(root)[k])
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
    calc == {
      elemth(toMap(root).Keys, Index(it, root));
      elemth(toMap(root).Keys, sizeSmaller(root, it.link.key));
      {
        if root.Node? {
          SizeSmaller(root, it.link.key);
          SizeLemmas(root);
          ElemthInorder(root, sizeSmaller(root, it.link.key));
        }
      }
      inorder(root)[sizeSmaller(root, it.link.key)].0;
      { SmallerInorderSize(root, it.link.key); }
      inorder(root)[|smallerInorder(root, it.link.key)|].0;
      { InorderOfSmallerInorderSize(root, it.link.key); }
      it.link.key;
    }
    var k := elemth(toMap(root).Keys, Index(it, root));
    calc == {
      it.link.value;
      { GetOfSubtree(root, it.link); }
      Get(root, it.link.key);
      toMap(root)[it.link.key];
      toMap(root)[k];
    }
  }

  function Traversed(it: iter, root: trbtree): set<K>
  {
    match it {
      case PastTheBeginning => keys(root)
      case PastTheEnd => keys(root)
      case Link(t) => smallerKeys(root, t.key)
    }
  }

  function Traversed'(it: iter, root: trbtree): set<K>
    requires SearchTree(root)
  {
    if Index(it, root) == -1 || Index(it, root) == |toMap(root)| then
      toMap(root).Keys
    else
      SizeIndex(it, root);
      lelemth(toMap(root).Keys, Index(it, root));
      smaller(toMap(root).Keys, elemth(toMap(root).Keys, Index(it, root)))
  }

  lemma TraversedEq(it: iter, root: trbtree)
    requires Valid(it, root)
    ensures Traversed(it, root) == Traversed'(it, root)
  {
    if Index(it, root) == -1 || Index(it, root) == |toMap(root)| {
      assert |toMap(root)| == size(root) by {
        SizeLemmas(root);
      }
      if it.Link? {
        SizeSmaller(root, it.link.key);
        assert false;
      }
      assert it.PastTheBeginning? || it.PastTheEnd?;
      assert toMap(root).Keys == keys(root);
    } else {
      SizeIndex(it, root);
      lelemth(toMap(root).Keys, Index(it, root));
      HasPeekEq(it, root);
      calc == {
        smaller(toMap(root).Keys, elemth(toMap(root).Keys, Index(it, root)));
        { PeekEq(it, root); }
        smaller(toMap(root).Keys, it.link.key);
        smaller(keys(root), it.link.key);
        { SmallerKeys(root, it.link.key); }
        smallerKeys(root, it.link.key);
      }
    }
  }

  function Next(it: iter, root: trbtree): iter
    requires HasPeek(it)
    requires Valid(it, root)
  {
    match it.link.right
    case Empty => PastTheEnd
    case Thread(k) =>
      assert k in keys(root) by {
        assert k in keysAndThreads(it.link);
        assert k in keysAndThreads(root);
        ThreadedKeys(root);
      }
      Link(GetSubtree(root, k))
    case Node(_, _, _, _, _) =>
      Link(minSubtree(it.link.right))
  }

  lemma NextSpec(it: iter, root: trbtree)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures Valid(Next(it, root), root)
  {
    match it.link.right
    case Empty =>
    case Thread(_) =>
    case Node(_, _, _, _, _) =>
      assert Subtree(minSubtree(it.link.right), it.link.right);
      assert Subtree(it.link.right, it.link);
      SubtreeTrans(minSubtree(it.link.right), it.link.right, it.link);
      SubtreeTrans(minSubtree(it.link.right), it.link, root);
  }

  lemma NextTraversed(it: iter, root: trbtree)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures Traversed(Next(it, root), root)
      == Traversed(it, root) + {Peek(it, root).0}
  {
    match it.link.right {
      case Empty() => {
        SmallerKeysRightEmpty(it.link, root);
      }
      case Thread(k) => {
        SmallerKeysRightThread(it.link, root);
      }
      case Node(_, _, _, _, _) => {
        SmallerKeysMin(it.link, root);
      }
    }
  }

  function Prev(it: iter, root: trbtree): iter
    requires HasPeek(it)
    requires Valid(it, root)
  {
    match it.link.left {
      case Empty() => PastTheBeginning
      case Thread(k) =>
        assert k in keys(root) by {
          assert k in keysAndThreads(it.link);
          assert k in keysAndThreads(root);
          ThreadedKeys(root);
        }
        Link(GetSubtree(root, k))
      case Node(_, _, _, _, _) =>
        Link(maxSubtree(it.link.left))
    }
  }
}
