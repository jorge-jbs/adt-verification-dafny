include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module {:options "-functionSyntax:4"} TRBTree.UpdateNext {
  import opened Color
  import opened Base

  function UpdateNext(newNext: threadOrEmpty, t: trbtree): trbtree
  {
    match t
    case Empty => Empty
    case Node(l, k, v, Empty, c) => Node(l, k, v, newNext, c)
    case Node(l, k, v, Thread(_), c) => Node(l, k, v, newNext, c)
    case Node(l, k, v, r, c) => Node(l, k, v, UpdateNext(newNext, r), c)
  }

  lemma UpdateNextSpec(newNext: threadOrEmpty, t: trbtree)
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
      case Node(l, k, v, Empty, c) => {}
      case Node(l, k, v, r, c) => {
        UpdateNextSpec(newNext, r);
        assert forall m | m in keys(r) :: k < m;
      }
    }
  }

  lemma UpdateNextThreaded(
      newNext: threadOrEmpty,
      prev: threadOrEmpty, 
      t: trbtree, 
      next: threadOrEmpty
    )
    decreases size(t)

    requires t.Node?
    requires t.Node? ==> ThreadedTreeNe(prev, t, next)
    ensures UpdateNext(newNext, t).Node? ==> ThreadedTreeNe(prev, UpdateNext(newNext, t), newNext)
    {
    match t {
      case Node(_, _, _, Thread(_), _) | Node(_, _, _, Empty, _) => {}
      case Node(l, k, v, r, c) => {
        UpdateNextThreaded(newNext, Thread(k), r, next);
      }
    }
  }
}
