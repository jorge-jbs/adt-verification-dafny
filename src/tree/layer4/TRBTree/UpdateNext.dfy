include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module TRBTree.UpdateNext {
  import opened Color
  import opened Base

  function method UpdateNextP(newNext: threadOrEmpty, p: pointer): pointer
  {
    match p {
      case Thread(k) => Thread(k)
      case Child(t) => Child(UpdateNext(newNext, t))
    }
  }

  function method UpdateNext(newNext: threadOrEmpty, t: rbtree): rbtree
  {
    match t {
      case Empty => Empty
      case Node(l, k, v, Thread(_), c) =>
        Node(l, k, v, newNext, c)
      case Node(l, k, v, r, c) =>
        Node(l, k, v, UpdateNextP(newNext, r), c)
    }
  }

  lemma UpdateNextPSpec(newNext: threadOrEmpty, p: pointer)
    decreases sizeWithPointersP(p)

    requires SearchTreeP(p)
    requires RedBlackTreeP(p)

    ensures SearchTreeP(UpdateNextP(newNext, p))
    ensures RedBlackTreeP(UpdateNextP(newNext, p))
    ensures BlackHeightP(UpdateNextP(newNext, p)) == BlackHeightP(p)
    ensures keysP(UpdateNextP(newNext, p)) == keysP(p)
  {
    match p {
      case Thread(k) => {}
      case Child(t) => {
        UpdateNextSpec(newNext, t);
      }
    }
  }

  lemma UpdateNextSpec(newNext: threadOrEmpty, t: rbtree)
    decreases sizeWithPointers(t)

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
      case Node(l, k, v, r, c) => {
        UpdateNextPSpec(newNext, r);
      }
    }
  }
}
