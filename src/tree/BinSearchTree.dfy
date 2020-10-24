include "../../src/tree/BinTree.dfy"
include "../../src/Order.dfy"

predicate isSearchTree<A>(t: BinTree<A>, le: (A, A) -> bool)
{
  match t
    case Empty =>
      true
    case Node(l, x, r) =>
      (forall y | y in elems(l) :: le(y, x)) && (forall z | z in elems(r) :: le(x, z))
      && isSearchTree(l, le) && isSearchTree(r, le)
}

function method search<A>(x: A, t: BinTree<A>, le: (A, A) -> bool): bool
  requires isSearchTree(t, le)
  requires isTotalPreorder(le)
  //ensures search(x, t, le) <==> x in elems(t)
  ensures search(x, t, le) <==> exists y | y in elems(t) :: le(x, y) && le(y, x)
{
  match t
    case Empty =>
      false
    case Node(l, y, r) =>
      if !le(y, x) then // y > x
        search(x, l, le)
      else if !le(x, y) then // x < y
        search(x, r, le)
      else
        true
}

function method insert<A>(x: A, t: BinTree<A>, le: (A, A) -> bool): BinTree<A>
  requires isTotalPreorder(le)
  requires isSearchTree(t, le)
  ensures isSearchTree(insert(x, t, le), le)
  ensures elems(insert(x, t, le)) == elems(t) + {x}
  ensures melems(insert(x, t, le)) == melems(t) + multiset{x}
{
  match t
    case Empty =>
      Node(Empty, x, Empty)
    case Node(l, y, r) =>
      if le(x, y) then
        Node(insert(x, l, le), y, r)
      else
        Node(l, y, insert(x, r, le))
}

function method deleteMin<A>(t: BinTree<A>, le: (A, A) -> bool):
    (res: (A, BinTree<A>))
  requires t != Empty
  requires isTotalPreorder(le)
  requires isSearchTree(t, le)
  ensures isSearchTree(res.1, le)
  ensures res.0 in elems(t)
  ensures elems(res.1) <= elems(t)
  ensures forall x | x in elems(res.1) :: le(res.0, x)
{
  match t
    case Node(l, x, r) =>
      if l == Empty then
        (x, r)
      else
        var (m, s) := deleteMin(l, le);
        (m, Node(s, x, r))
}

function method deleteOne<A(==)>(x: A, t: BinTree<A>, le: (A, A) -> bool):
    BinTree<A>
  requires isTotalPreorder(le)
  requires isSearchTree(t, le)
  ensures isSearchTree(deleteOne(x, t, le), le)
  ensures elems(deleteOne(x, t, le)) <= elems(t)
  //ensures melems(deleteOne(x, t, le)) == melems(t) - multiset{x}
{
  match t
    case Empty =>
      Empty
    case Node(l, y, r) =>
      if !le(y, x) then // y > x
        assert isSearchTree(Node(deleteOne(x, l, le), y, r), le);
        Node(deleteOne(x, l, le), y, r)
      else if !le(x, y) then // x < y
        assert isSearchTree(Node(l, y, deleteOne(x, r, le)), le);
        Node(l, y, deleteOne(x, r, le))
      else
        if r == Empty then
          l
        else
          var (m, s) := deleteMin(r, le);
          Node(l, m, s)
}

/*
function method deleteAll<A(==)>(x: A, t: BinTree<A>, le: (A, A) -> bool):
    BinTree<A>
  requires isTotalPreorder(le)
  requires isSearchTree(t, le)
  ensures isSearchTree(deleteAll(x, t, le), le)
  ensures elems(deleteAll(x, t, le)) + {x} == elems(t)
  //ensures melems(deleteOne(x, t, le)) == melems(t) - multiset{x}
{
  match t
    case Empty =>
      Empty
    case Node(l, y, r) =>
      if !le(y, x) then // y > x
        assert isSearchTree(Node(deleteAll(x, l, le), y, r), le);
        Node(deleteAll(x, l, le), y, r)
      else if !le(x, y) then // x < y
        assert isSearchTree(Node(l, y, deleteAll(x, r, le)), le);
        Node(l, y, deleteAll(x, r, le))
      else
        var rr := deleteAll(x, r, le);
        if rr == Empty then
          l
        else
          var (m, s) := deleteMin(rr, le);
          Node(deleteAll(x, l, le), m, s)
}
*/
