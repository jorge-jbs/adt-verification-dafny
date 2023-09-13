include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module TRBTree.UpdateNext {
  import opened Color
  import opened Base

  function method UpdateNextP(newNext: threadOrEmpty, p: pointer): pointer
    requires !IsThreadOrEmpty(p)
  {
    Child(UpdateNext(newNext, p.child))
  }

  function method UpdateNext(newNext: threadOrEmpty, t: rbtree): rbtree
  {
    match t {
      case Empty => Empty
      case Node(l, k, v, Thread(_), c) =>
        Node(l, k, v, newNext, c)
      case Node(l, k, v, Child(Empty), c) =>
        Node(l, k, v, newNext, c)
      case Node(l, k, v, r, c) =>
        Node(l, k, v, Child(UpdateNext(newNext, r.child)), c)
    }
  }

  lemma UpdateNextPSpec(newNext: threadOrEmpty, p: pointer)
    decreases sizeWithPointersP(p)

    requires !IsThreadOrEmpty(p)
    requires SearchTreeP(p)
    requires RedBlackTreeP(p)

    ensures SearchTreeP(UpdateNextP(newNext, p))
    ensures RedBlackTreeP(UpdateNextP(newNext, p))
    ensures BlackHeightP(UpdateNextP(newNext, p)) == BlackHeightP(p)
    ensures keysP(UpdateNextP(newNext, p)) == keysP(p)
  {
    UpdateNextSpec(newNext, p.child);
  }

  lemma UpdateNextSpec(newNext: threadOrEmpty, t: rbtree)
    requires SearchTree(t)
    requires RedBlackTree(t)

    ensures SearchTree(UpdateNext(newNext, t))
    ensures RedBlackTree(UpdateNext(newNext, t))
    ensures BlackHeight(UpdateNext(newNext, t)) == BlackHeight(t)
    ensures keys(UpdateNext(newNext, t)) == keys(t)
  {
    match t {
      case Empty => {}
      case Node(l, k, v, Thread(_), c) => {}
      case Node(l, k, v, Child(Empty), c) => {}
      case Node(l, k, v, r, c) => {
        UpdateNextSpec(newNext, r.child);
        assert forall m | m in keysP(r) :: k < m;
      }
    }
  }

  lemma UpdateNextPThreaded(
      newNext: threadOrEmpty,
      prev: threadOrEmpty, 
      p: pointer, 
      next: threadOrEmpty
    )
    decreases sizeWithPointersP(p)

    requires !IsThreadOrEmpty(p)
    requires ThreadedTreeRec(prev, p.child, next)
    ensures ThreadedTreeRec(prev, UpdateNextP(newNext, p).child, newNext)
  {
    match p {
      case Child(t) => {
        if t.Node? {
          UpdateNextThreaded(newNext, prev, t, next);
        }
      }
    }
  }

  lemma UpdateNextThreaded(
      newNext: threadOrEmpty,
      prev: threadOrEmpty, 
      t: rbtree, 
      next: threadOrEmpty
    )
    decreases sizeWithPointers(t)

    requires t.Node?
    requires ThreadedTreeRec(prev, t, next)
    ensures ThreadedTreeRec(prev, UpdateNext(newNext, t), newNext)
    {
    match t {
      case Node(_, _, _, Thread(_), _) | Node(_, _, _, Child(Empty), _) => {}
      case Node(l, k, v, r, c) => {
        UpdateNextPThreaded(newNext, Thread(k), r, next);
      }
    }
  }
}
