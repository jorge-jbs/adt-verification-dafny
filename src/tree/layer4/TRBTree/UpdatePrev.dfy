include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module {:options "-functionSyntax:4"} TRBTree.UpdatePrev {
  import opened Color
  import opened Base

  function UpdatePrevP(
      newPrev: threadOrEmpty,
      node: pointer
    ): pointer
  {
    match node {
      case Thread(k) => Thread(k)
      case Child(t) => Child(UpdatePrev(newPrev, t))
    }
  }

  function UpdatePrev(
      newPrev: threadOrEmpty,
      node: rbtree
    ): rbtree
  {
    match node {
      case Empty => Empty
      case Node(Thread(_), k, v, r, c) =>
        Node(newPrev, k, v, r, c)
      case Node(l, k, v, r, c) =>
        Node(UpdatePrevP(newPrev, l), k, v, r, c)
    }
  }
}
