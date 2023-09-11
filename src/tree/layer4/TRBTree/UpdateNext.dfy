include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module TRBTree.UpdateNext {
  import opened Color
  import opened Base

  function method UpdateNextP(
      newNext: threadOrEmpty,
      node: pointer
    ): pointer
  {
    match node {
      case Thread(k) => Thread(k)
      case Child(t) => Child(UpdateNext(newNext, t))
    }
  }

  function method UpdateNext(
      newNext: threadOrEmpty,
      node: rbtree
    ): rbtree
  {
    match node {
      case Empty => Empty
      case Node(l, k, v, Thread(_), c) =>
        Node(l, k, v, newNext, c)
      case Node(l, k, v, r, c) =>
        Node(l, k, v, UpdateNextP(newNext, r), c)
    }
  }
}
