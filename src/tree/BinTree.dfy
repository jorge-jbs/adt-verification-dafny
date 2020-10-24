/*
class Node<A> {
  var data: A;
  var left: Node?<A>;
  var right: Node?<A>;

  constructor(l: Node?<A>, d: A, r: Node?<A>)
  {
    data := d;
    left := l;
    right := r;
  }

  constructor Leaf(d: A)
  {
    data := d;
    left := null;
    right := null;
  }
}

type BinTree<A> = Node?<A>
*/

datatype BinTree<A> = Empty | Node(left: BinTree<A>, data: A, right: BinTree<A>)

function method Leaf<A>(d: A): BinTree<A>
{
  Node(Empty, d, Empty)
}

function method elems<A>(t: BinTree<A>): set<A>
{
  match t {
    case Empty => {}
    case Node(l, x, r) => elems(l) + {x} + elems(r)
  }
}

function method melems<A>(t: BinTree<A>): multiset<A>
{
  match t {
    case Empty => multiset{}
    case Node(l, x, r) => melems(l) + multiset{x} + melems(r)
  }
}

function method preorder<A>(t: BinTree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => [x] + preorder(l) + preorder(r)
  }
}

function method inorder<A>(t: BinTree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => inorder(l) + [x] + inorder(r)
  }
}

function method revinorder<A>(t: BinTree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => revinorder(r) + [x] + revinorder(l)
  }
}

function method postorder<A>(t: BinTree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => postorder(l) + postorder(r) + [x]
  }
}

function method size<A>(t: BinTree<A>): nat
{
  |preorder(t)|
}

function method max(x: int, y: int): int
{
  if x < y then
    y
  else
    x
}

function method depth<A>(t: BinTree<A>): nat
{
  match t {
    case Empty => 0
    case Node(l, x, r) => max(depth(l), depth(r))
  }
}
