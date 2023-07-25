include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer1/OrderedSetUtils.dfy"

module TRBTree.Iterator {
  import opened KeyValue
  import opened Color
  import opened Base
  import opened OrderedSetUtils

  type nerbtree
    = t: rbtree
    | t.Node?
    witness Node(Child(Empty), 0, 0, Child(Empty), Black)

  datatype iter
    = PastTheBeginning
    | PastTheEnd
    | Link(link: nerbtree)

  predicate Valid(it: iter, root: rbtree)
  {
    && SearchTree(root)
    && ThreadedTreeRoot(root)
    && (it.Link? ==> Subtree(it.link, root))
  }

  function Index(it: iter, root: rbtree): int
  {
    match it {
      case PastTheBeginning => -1
      case PastTheEnd => size(root)
      case Link(t) => sizeSmaller(root, t.key)
    }
  }

  lemma SizeIndex(it: iter, root: rbtree)
    requires SearchTree(root)
    ensures Index(it, root) <= |toMap(root)|;
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

  predicate HasPeek'(it: iter, root: rbtree)
    requires SearchTree(root)
  {
    0 <= Index(it, root) < |toMap(root)|
  }

  lemma HasPeekEq(it: iter, root: rbtree)
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

  function Peek(it: iter, root: rbtree): (K, V)
    requires HasPeek(it)
  {
    (it.link.key, it.link.value)
  }

  function Peek'(it: iter, root: rbtree): (K, V)
    requires SearchTree(root)
    requires HasPeek'(it, root)
  {
    var k := elemth(toMap(root).Keys, Index(it, root));
    (k, toMap(root)[k])
  }

/*
  function Peek(it: iter, root: rbtree): (K, V)
    requires HasPeek(it, root)
  {
    var s := inorder(root);
    var i := Index(it, root);
    SizeInorder(root);
    s[i]
  }
*/

  lemma PeekEq(it: iter, root: rbtree)
    requires Valid(it, root)
    requires SearchTree(root)
    requires HasPeek(it)
    requires HasPeek'(it, root)
    ensures Peek(it, root) == Peek'(it, root)

  function Traversed(it: iter, root: rbtree): set<K>
  {
    match it {
      case PastTheBeginning => keys(root)
      case PastTheEnd => keys(root)
      case Link(t) => smallerKeys(root, t.key)
    }
  }

  function Traversed'(it: iter, root: rbtree): set<K>
    requires SearchTree(root)
  {
    if Index(it, root) == -1 || Index(it, root) == |toMap(root)| then
      toMap(root).Keys
    else
      SizeIndex(it, root);
      lelemth(toMap(root).Keys, Index(it, root));
      smaller(toMap(root).Keys, elemth(toMap(root).Keys, Index(it, root)))
  }

  lemma TraversedEq(it: iter, root: rbtree)
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
      assume false;
    }
  }

  function Next(it: iter, root: rbtree): iter
    requires HasPeek(it)
    requires Valid(it, root)
  {
    match it.link.right {
      case Thread(k) =>
        assert k in keys(root) by {
          ThreadedKeys(root);
        }
        Link(GetSubtree(root, k))
      case Child(Empty()) =>
        PastTheEnd
      case Child(Node(_, _, _, _, _)) =>
        Link(minSubtreeP(it.link.right))
    }
  }

  lemma NextSpec(it: iter, root: rbtree)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures Valid(it, root)
  {}

  lemma NextTraversed(it: iter, root: rbtree)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures Traversed(Next(it, root), root)
      == Traversed(it, root) + {Peek(it, root).0}
  {
    match it.link.right {
      case Thread(k) => {
        SmallerKeysRightThread(it.link, root);
      }
      case Child(Empty()) => {
        SmallerKeysRightEmpty(it.link, root);
      }
      case Child(Node(_, _, _, _, _)) => {
        SmallerKeysMin(it.link, root);
      }
    }
  }

  function Prev(it: iter, root: rbtree): iter
    requires HasPeek(it)
    requires Valid(it, root)
  {
    match it.link.left {
      case Thread(k) =>
        assert k in keys(root) by {
          ThreadedKeys(root);
        }
        Link(GetSubtree(root, k))
      case Child(Empty()) =>
        PastTheBeginning
      case Child(Node(_, _, _, _, _)) =>
        Link(maxSubtreeP(it.link.left))
    }
  }
}
