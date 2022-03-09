include "../../src/Order.dfy"

datatype tree<A> = Empty | Node(left: tree<A>, data: A, right: tree<A>)

function method elems<A>(t: tree<A>): set<A>
{
  match t {
    case Empty => {}
    case Node(l, x, r) => elems(l) + {x} + elems(r)
  }
}

class TNode<K, V> {
  var key: K;
  var value: V;
  var left: TNode?<K, V>;
  var right: TNode?<K, V>;

  constructor(l: TNode?<K, V>, k: K, v: V, r: TNode?<K, V>)
  {
    key := k;
    value := v;
    left := l;
    right := r;
  }

  constructor Leaf(k: K, v: V)
  {
    key := k;
    value := v;
    left := null;
    right := null;
  }
}

predicate SearchTreeRec<K, V>(sk: tree<TNode<K, V>>, le: (K, K) -> bool)
  // reads set x | x in elems(sk) :: x`key
  requires isTotalOrder(le)
{
  match sk {
    case Empty() => true
    case Node(l, n, r) =>
      && (forall m | m in elems(l) :: le(m.key, n.key))
      && (forall m | m in elems(r) :: le(n.key, m.key))
      && SearchTreeRec(l, le)
      && SearchTreeRec(r, le)
  }
}
