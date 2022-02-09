include "../../src/Order.dfy"

//type tree<A> = Node?<A>

datatype tree<A> = Empty | Node(left: tree<A>, data: A, right: tree<A>)

function method Leaf<A>(d: A): tree<A>
{
  Node(Empty, d, Empty)
}

function method elems<A>(t: tree<A>): set<A>
{
  match t {
    case Empty => {}
    case Node(l, x, r) => elems(l) + {x} + elems(r)
  }
}

function method melems<A>(t: tree<A>): multiset<A>
{
  match t {
    case Empty => multiset{}
    case Node(l, x, r) => melems(l) + multiset{x} + melems(r)
  }
}

function method fmap<A, B>(t: tree<A>, f: A -> B): tree<B>
{
  match t {
    case Empty() => Empty()
    case Node(l, x, r) => Node(fmap(l, f), f(x), fmap(r, f))
  }
}

function method preorder<A>(t: tree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => [x] + preorder(l) + preorder(r)
  }
}

function method inorder<A>(t: tree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => inorder(l) + [x] + inorder(r)
  }
}

function method revinorder<A>(t: tree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => revinorder(r) + [x] + revinorder(l)
  }
}

function method postorder<A>(t: tree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => postorder(l) + postorder(r) + [x]
  }
}

function method size<A>(t: tree<A>): nat
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

function method depth<A>(t: tree<A>): nat
{
  match t {
    case Empty => 0
    case Node(l, x, r) => max(depth(l), depth(r))
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

class Tree<K, V> {
  var root: TNode?<K, V>;
  ghost var skeleton: tree<TNode<K, V>>;

  function Repr(): set<object>
    reads this
  {
    set x | x in elems(skeleton)
  }

  static predicate ValidRec(tree: TNode?<K, V>, sk: tree<TNode<K, V>>)
    reads elems(sk)
  {
    match sk {
      case Empty => tree == null
      case Node(l, x, r) =>
        && x == tree
        && ValidRec(tree.left, l)
        && ValidRec(tree.right, r)
    }
  }

  predicate Valid()
    reads this, Repr()
  {
    ValidRec(root, skeleton)
  }

  lemma DistinctSkeleton()
    requires Valid()
    // ensures melems(skeleton) == elems(skeleton)
    ensures forall n | n in melems(skeleton) :: melems(skeleton)[n] == 1

  static function ModelRec(sk: tree<TNode<K, V>>): tree<K>
    reads set x | x in elems(sk) :: x`key
  {
    match sk {
      case Empty() => Empty()
      case Node(l, n, r) => Node(ModelRec(l), n.key, ModelRec(r))
    }
  }

  function Model(): tree<K>  // TODO: tree<(K, V)>
    reads this, elems(skeleton)
    requires Valid()
  {
    ModelRec(skeleton)
  }

  static function MapModelRec(sk: tree<TNode<K, V>>): map<K, V>
    reads set x | x in elems(sk) :: x`key
    reads set x | x in elems(sk) :: x`value
    ensures forall n | n in elems(sk) :: n.key in MapModelRec(sk)
  {
    match sk {
      case Empty() => map[]
      case Node(l, n, r) => MapModelRec(l) + MapModelRec(r) + map[n.key := n.value]
    }
  }

  function MapModel(): map<K, V>
    reads this, elems(skeleton)
    requires Valid()
  {
    MapModelRec(skeleton)
  }

  constructor()
    ensures Valid()
    ensures fresh(Repr())
    ensures Model() == Empty
  {
    root := null;
    skeleton := Empty;
  }

  predicate SearchTree(le: (K, K) -> bool)
    reads this, Repr()
    requires Valid()
    requires isTotalOrder(le)
  {
    Ordered(inorder(Model()), le)
  }

  static predicate SearchTreeRec(sk: tree<TNode<K, V>>, le: (K, K) -> bool)
    reads set x | x in elems(sk) :: x`key
    requires isTotalOrder(le)
  {
    match sk {
      case Empty() => true
      case Node(l, n, r) =>
        // && (forall m | m in elems(l) :: le(m.key, n.key))
        // && (forall m | m in elems(r) :: le(n.key, m.key))
        && (forall k | k in MapModelRec(l) :: le(k, n.key))
        && (forall k | k in MapModelRec(r) :: le(n.key, k))
        && SearchTreeRec(l, le)
        && SearchTreeRec(r, le)
    }
  }

  static method GetRec(
      n: TNode<K, V>,
      ghost sk: tree<TNode<K, V>>,
      k: K,
      le: (K, K) -> bool)
      returns (v: V)
    requires ValidRec(n, sk)
    // requires n in elems(sk)
    requires isTotalOrder(le)
    requires SearchTreeRec(sk, le)
    requires k in MapModelRec(sk)
    // requires sk.data == n
    requires ValidRec(n, sk)
    ensures k in MapModelRec(sk)
    ensures MapModelRec(sk)[k] == v
  {
    /*
    match sk {
      case Empty() => assert false;
      case Node(l, nn, r) =>
        assert nn == n;
        assert forall m | m in elems(sk.left) :: le(m.key, n.key);
        assert forall m | m in elems(sk.right) :: le(n.key, m.key);
        assert SearchTreeRec(sk.left, le);
        assert SearchTreeRec(sk.right, le);
    }
    */
    /*
    assert sk != Empty;
    assert sk.data == n;
    assert forall m | m in elems(sk.left) :: le(m.key, n.key);
    assert forall m | m in elems(sk.right) :: le(n.key, m.key);
    assert SearchTreeRec(sk, le);
    assert sk == Node(sk.left, n, sk.right);
    assert SearchTreeRec(sk.left, le);
    assert SearchTreeRec(sk.right, le);
    */
    if le(n.key, k) && le(k, n.key) {
      assert n.key == k;
      v := n.value;
      assert MapModelRec(sk)[k] == v;
    } else if le(n.key, k) {
      /*
      forall p | p in MapModelRec(sk.left)
        ensures le(p, k)
      {
        var nn :| nn in elems(sk) && nn.key == p;
        assert le(nn.key, k);
        assert le(p, n.key);
        assert le(n.key, k);
      }
      if k in MapModelRec(sk.left) {
        assert false;
      }
      */
      assert k !in MapModelRec(sk.left);
      assert k in MapModelRec(sk.right);
      assert sk.right != Empty;
      assert ValidRec(n.right, sk.right);
      assert n.right != null;
      v := GetRec(n.right, sk.right, k, le);
    } else if le(k, n.key) {
      assert k in MapModelRec(sk.left);
      assert sk.left != Empty;
      assert ValidRec(n.left, sk.left);
      assert n.left != null;
      v := GetRec(n.left, sk.left, k, le);
    } else {
      assert false;
    }
  }

  /*
  method Test()
  {
    assert false;
  }

  method Test1()
    requires Valid()
  {
    assert false;
  }

  method Test4(k: K)
    requires Valid()
  {
    assert false;
  }

  method Test5(k: K) returns (v: V)
    requires Valid()
  {
    assert false;
  }

  method Test6(k: K, le: (K, K) -> bool) returns (v: V)
    requires Valid()
  {
    assert false;
  }

  method Test2(k: K, le: (K, K) -> bool) returns (v: V)
    requires Valid()
    requires isTotalOrder(le)
  {
    assert false;
  }

  method Test3(k: K, le: (K, K) -> bool) returns (v: V)
    requires Valid()
    requires isTotalOrder(le)
    requires SearchTree(le)
  {
    assert false;
  }

  method Get(k: K, le: (K, K) -> bool) returns (v: V)
    requires Valid()
    requires isTotalOrder(le)
    requires SearchTree(le)
    requires k in MapModel()
    ensures Valid()
    ensures k in MapModel()
    ensures MapModel()[k] == v
  {
    assert false;
    if root == null {
      assert false;
    }
    assert SearchTree(le) ==> SearchTreeRec(skeleton, le);
    v := GetRec(root, skeleton, k, le);
  }
  */
}

/*
class STree<K(!new), V> {
  var tree: Tree<K, V>;
  var le: (K, K) -> bool;

  constructor(le: (K, K) -> bool)
    requires isTotalOrder(le)
  {
    this.tree := new Tree();
    this.le := le;
  }

  predicate Valid()
    reads this, tree, tree.Repr()
  {
    && tree.Valid()
    && isTotalOrder(le)
    && Ordered(inorder(tree.Model()), le)
  }

  method Get(k: K) returns (v: V)
    requires Valid()
    requires k in tree.MapModel()
    ensures Valid()
    ensures k in tree.MapModel()
    ensures tree.MapModel()[k] == v
  {
    v := tree.Get(k, le);
  }
}
*/
