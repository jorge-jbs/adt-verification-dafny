include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module TRBTree.TRBInsert {
  import opened KeyValue
  import opened Color
  import opened Base

  datatype iter
    = PastTheBeginning
    | PastTheEnd
    | Link(link: K)

  predicate Valid(it: iter, root: rbtree)
  {
    && SearchTree(root)
    && (it.Link? ==>
      && it.link in keys(root)
      && GetSubtree(root, it.link).Node?
    )
  }

  function Index(it: iter, root: rbtree): int
  {
    match it {
      case PastTheBeginning => 0
      case PastTheEnd => size(root)
      case Link(k) => sizeSmaller(root, k)
    }
  }

  function Traversed(it: iter, root: rbtree): set<K>
  {
    match it {
      case PastTheBeginning => {}
      case PastTheEnd => keys(root)
      case Link(k) => smallerKeys(root, k)
    }
  }

/*
  predicate HasPeek(it: iter, root: rbtree)
  {
    0 <= Index(it, root) < size(root)
  }

  function Peek(it: iter, root: rbtree): (K, V)
    requires HasPeek(it, root)
  {
    var s := inorder(root);
    var i := Index(it, root);
    SizeInorder(root);
    s[i]
  }

  function Next(it: iter, root: rbtree): iter
  */

  predicate HasPeek(it: iter)
  {
    it.Link?
  }

  function Peek(it: iter, root: rbtree): (K, V)
    requires Valid(it, root)
    requires HasPeek(it)
  {
    (it.link, Get(root, it.link))
  }

  function Next(it: iter, root: rbtree): iter
    requires Valid(it, root)
    requires HasPeek(it)
  {
    match GetSubtree(root, it.link).right {
      case Thread(k) => Link(k)
      case Child(Empty()) => PastTheEnd
      case Child(t) => Link(minimum(t))
    }
  }
}
