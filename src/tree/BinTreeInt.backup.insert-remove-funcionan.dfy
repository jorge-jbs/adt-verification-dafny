include "../../src/Order.dfy"

//type tree<A> = Node?<A>

datatype tree<A> = Empty | Node(left: tree<A>, data: A, right: tree<A>)

function method {:verify false} Leaf<A>(d: A): tree<A>
{
  Node(Empty, d, Empty)
}

function method {:verify false} elems<A>(t: tree<A>): set<A>
  ensures t.Empty? ==> elems(t) == {}
  ensures !t.Empty? ==> elems(t) == elems(t.left) + {t.data} + elems(t.right)
{
  match t {
    case Empty => {}
    case Node(l, x, r) => elems(l) + {x} + elems(r)
  }
}

function method {:verify false} melems<A>(t: tree<A>): multiset<A>
{
  match t {
    case Empty => multiset{}
    case Node(l, x, r) => melems(l) + multiset{x} + melems(r)
  }
}

function method {:verify false} fmap<A, B>(t: tree<A>, f: A -> B): tree<B>
{
  match t {
    case Empty() => Empty()
    case Node(l, x, r) => Node(fmap(l, f), f(x), fmap(r, f))
  }
}

function method {:verify false} preorder<A>(t: tree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => [x] + preorder(l) + preorder(r)
  }
}

function method {:verify false} inorder<A>(t: tree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => inorder(l) + [x] + inorder(r)
  }
}

function method {:verify false} revinorder<A>(t: tree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => revinorder(r) + [x] + revinorder(l)
  }
}

function method {:verify false} postorder<A>(t: tree<A>): seq<A>
{
  match t {
    case Empty => []
    case Node(l, x, r) => postorder(l) + postorder(r) + [x]
  }
}

function method {:verify false} size<A>(t: tree<A>): nat
{
  |preorder(t)|
}

function method {:verify false} max(x: int, y: int): int
{
  if x < y then
    y
  else
    x
}

function method {:verify false} depth<A>(t: tree<A>): nat
{
  match t {
    case Empty => 0
    case Node(l, x, r) => max(depth(l), depth(r)) + 1
  }
}

datatype Color = Red | Black

type K = int
type V = int

class TNode {
  var key: K;
  var value: V;
  var left: TNode?;
  var right: TNode?;

  var color: Color;

  constructor(l: TNode?, k: K, v: V, r: TNode?)
    ensures left == l
    ensures key == k
    ensures value == v
    ensures right == r
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

class Tree {
  var root: TNode?;
  ghost var skeleton: tree<TNode>;

  function Repr(): set<object>
    reads this
  {
    elems(skeleton)
  }

  static predicate ValidRec(node: TNode?, sk: tree<TNode>)
    // reads elems(sk)
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`right
  {
    match sk {
      case Empty => node == null
      case Node(l, x, r) =>
        && x == node
        && x !in elems(l)
        && x !in elems(r)
        && elems(l) !! elems(r)
        && ValidRec(node.left, l)
        && ValidRec(node.right, r)
    }
  }

  predicate Valid()
    reads this, Repr()
  {
    ValidRec(root, skeleton)
  }

  // lemma DistinctSkeleton()
  //   requires Valid()
  //   // ensures melems(skeleton) == elems(skeleton)
  //   ensures forall n | n in melems(skeleton) :: melems(skeleton)[n] == 1

  static lemma DistinctSkeletonRec(node: TNode, sk: tree<TNode>)
    requires ValidRec(node, sk)
    ensures node !in elems(sk.left)
    ensures node !in elems(sk.right)

  static function ModelRec(sk: tree<TNode>): tree<K>
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

  static function MapModelRec(root: TNode?, sk: tree<TNode>): map<K, V>
    reads elems(sk)
    // reads set x | x in elems(sk) :: x`key
    // reads set x | x in elems(sk) :: x`value
    requires ValidRec(root, sk)
    requires SearchTreeRec(sk)
    // ensures forall n | n in elems(sk) :: n.key in MapModelRec(sk)
    // ensures forall .... k in MapModelRec(sk) && MapModelRec(sk)[k] == v <==> (exists n | n in elems(sk) :: n.key == k && n.value == v)
  {
    map k | k in TreeKeys(sk) :: FindNode(k, root, sk).value
    // match sk {
    //   case Empty() => map[]
    //   case Node(l, n, r) => (MapModelRec(l) + MapModelRec(r))[n.key := n.value]
    // }
  }

  static lemma MapModelLemmas(root: TNode?, sk: tree<TNode>)
    requires ValidRec(root, sk)
    requires SearchTreeRec(sk)
    requires sk.Node?
    ensures MapModelRec(root, sk) == (MapModelRec(root.left, sk.left) + MapModelRec(root.right, sk.right))[root.key := root.value]

  function MapModel(): map<K, V>
    reads this, elems(skeleton)
    requires Valid()
    requires SearchTree()
  {
    MapModelRec(root, skeleton)
  }

  constructor()
    ensures Valid()
    ensures fresh(Repr())
    ensures Model() == Empty
  {
    root := null;
    skeleton := Empty;
  }

  predicate SearchTree()
    reads this, Repr()
    requires Valid()
  {
    SearchTreeRec(skeleton)
  }

  static predicate SearchTreeRec(sk: tree<TNode>)
    reads set x | x in elems(sk) :: x`key
  {
    match sk {
      case Empty() => true
      case Node(l, n, r) =>
        && (forall m | m in elems(l) :: m.key < n.key)
        && (forall m | m in elems(r) :: n.key < m.key)
        && SearchTreeRec(l)
        && SearchTreeRec(r)
    }
  }

  // lemma SearchTreeDefEquiv()
  //   requires Valid()
  //   ensures SearchTree() <==> OrderedInt(inorder(Model()))

  lemma {:verify false} ModelRelationWithSkeleton(k: K, v: V)
    requires Valid()
    requires SearchTree()
    ensures k in MapModel() && MapModel()[k] == v <==> exists n | n in elems(skeleton) :: n.key == k && n.value == v
  {
    if k in MapModel() && MapModel()[k] == v {
      ModelRelationWithSkeletonRecR(root, skeleton, k, v);
    }
    if exists n | n in elems(skeleton) :: n.key == k && n.value == v {
      ModelRelationWithSkeletonRecL(root, skeleton, k, v);
    }
  }

  static lemma {:verify false} ModelRelationWithSkeletonRecR(node: TNode?, sk: tree<TNode>, k: K, v: V)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires k in MapModelRec(node, sk)
    requires MapModelRec(node, sk)[k] == v
    ensures (exists n | n in elems(sk) :: n.key == k && n.value == v)
  {}

  static lemma {:verify false} ModelRelationWithSkeletonRecL(node: TNode?, sk: tree<TNode>, k: K, v: V)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires (exists n | n in elems(sk) :: n.key == k && n.value == v)
    ensures k in MapModelRec(node, sk)
    ensures MapModelRec(node, sk)[k] == v
  {
    match sk {
      case Empty => {}
      case Node(l, n, r) => {
        if n.key == k {
        } else if k < n.key {
          assert k in MapModelRec(node, l);

          assert forall m | m in elems(r) :: n.key != m.key;
          if k in MapModelRec(node, r) {
            ModelRelationWithSkeletonKeyRecR(n.right, r, k);
            assert false;
          }
          assert k !in MapModelRec(node, r);

          assert MapModelRec(node, sk)[k] == v;
        } else if n.key < k {
        } else {
          assert false;
        }
      }
    }
  }

  lemma {:verify false} ModelRelationWithSkeletonKey(k: K)
    requires Valid()
    requires SearchTree()
    ensures k in MapModel() <==> exists n | n in elems(skeleton) :: n.key == k
  {
    if k in MapModel() {
      ModelRelationWithSkeletonKeyRecR(root, skeleton, k);
    }
    if exists n | n in elems(skeleton) :: n.key == k {
      ModelRelationWithSkeletonKeyRecL(root, skeleton, k);
    }
  }

  static lemma {:verify false} ModelRelationWithSkeletonKeyRecR(node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires k in MapModelRec(node, sk)
    ensures (exists n | n in elems(sk) :: n.key == k)
  {}

  static lemma {:verify false} ContraModelRelationWithSkeletonKeyRecR(node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires forall m | m in elems(sk) :: k != m.key;
    ensures k !in MapModelRec(node, sk)
  {
      if k in MapModelRec(node, sk) {
        ModelRelationWithSkeletonKeyRecR(node, sk, k);
        assert false;
      }
      assert k !in MapModelRec(node, sk);
  }

  static lemma {:verify false} ModelRelationWithSkeletonKeyRecL (node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires (exists n | n in elems(sk) :: n.key == k)
    ensures k in MapModelRec(node, sk)
  {
    match sk {
      case Empty => {}
      case Node(l, n, r) => {}
    }
  }

  static method {:verify false} GetRec(n: TNode, ghost sk: tree<TNode>, k: K) returns (v: V)
    requires ValidRec(n, sk)
    requires SearchTreeRec(sk)
    requires exists n | n in elems(sk) :: n.key == k
    ensures ValidRec(n, sk)
    ensures SearchTreeRec(sk)
    ensures exists n | n in elems(sk) :: n.key == k && n.value == v

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    if k == n.key {
      v := n.value;
    } else if n.key < k {
      v := GetRec(n.right, sk.right, k);
    } else if k < n.key {
      v := GetRec(n.left, sk.left, k);
    } else {
      assert false;
    }
  }

  method {:verify false} Get(k: K) returns (v: V)
    requires Valid()
    requires SearchTree()
    requires k in MapModel()
    ensures Valid()
    ensures SearchTree()
    ensures k in MapModel()
    ensures MapModel()[k] == v

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x | x in Repr() :: allocated(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    /*GHOST*/ ModelRelationWithSkeletonKey(k);
    assert Repr() == elems(skeleton);
    v := GetRec(root, skeleton, k);
    /*GHOST*/ ModelRelationWithSkeleton(k, v);
  }

  static lemma CommuteMapModelRec(node: TNode?, sk: tree<TNode>)
    requires sk.Node?
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    ensures MapModelRec(node, sk)
      == (MapModelRec(node.left, sk.left) + MapModelRec(node.right, sk.right))[sk.data.key := sk.data.value]
      == (MapModelRec(node.right, sk.right) + MapModelRec(node.left, sk.left))[sk.data.key := sk.data.value]

  static lemma MapSubst(a: map<K, V>, b: map<K, V>, c: map<K, V>, k: K, v: V)
    requires k !in a
    requires k !in c
    ensures (a + b + c)[k := v] == a + b[k := v] + c
  {}

  static method {:verify true} InsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V) returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode: TNode)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    // ensures MapModelRec(newNode, newSk) == old(MapModelRec(node, sk)[k := v])

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures forall n | n in elems(sk) && n.key != k :: n.key == old(n.key) && n.value == old(n.value)

    // ensures newNode == node <==> node != null
    // ensures node == null ==> newNode.left == null && newNode.key == k && newNode.value == v && newNode.right == null
    // ensures forall n | n in elems(sk) :: n.key == old(n.key) && (if n.key == k then n.value == v else n.value == old(n.value))
    // ensures forall n | n in elems(newSk) :: n.key == old(n.key) && (if n.key == k then n.value == v else n.value == old(n.value))
    // ensures forall n | n in elems(newSk) && n.key != k :: exists m | m in elems(sk) :: n.key == old(m.key) && n.value == old(m.value)
    // ensures forall m | m in MapModel() && k != m :: m in old(MapModel())
    // ensures elems(sk) <= elems(newSk)
    // ensures forall n | n in elems(sk) :: n in elems(newSk)
    // ensures newNode in elems(newSk)
    // ensures forall m | m in old(MapModelRec(sk)) && k != m :: m in MapModelRec(newSk) && MapModelRec(newSk)[m] == old(MapModelRec(sk)[m])
    // ensures MapModelRec(newNode, newSk) == map k' | k' in old(MapModelRec(node, sk))  old(MapModelRec(node, sk)[k := v])

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(newSk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      newNode := new TNode(null, k, v, null);
      newSk := Node(Empty, newNode, Empty);
      insertedNode := newNode;
      assert MapModelRec(newNode, newSk) == old(MapModelRec(node, sk)[k := v]);
    } else {
      MapModelLemmas(node, sk);
      assert MapModelRec(node, sk)[k := v] == ((MapModelRec(node.left, sk.left) + MapModelRec(node.right, sk.right) + map[node.key := node.value])[k := v]);
      // CommuteMapModelRec(node, sk);
      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        insertedNode := node;
        assert MapModelRec(newNode, newSk) == old(MapModelRec(node, sk)[k := v]);
      } else if node.key < k {
        calc == {
          MapModelRec(node.left, sk.left) + MapModelRec(node.right, sk.right)[k := v] + map[node.key := node.value];
          {
            assert k !in MapModelRec(node.left, sk.left) && k !in map[node.key := node.value];
            MapSubst(MapModelRec(node.left, sk.left), MapModelRec(node.right, sk.right), map[node.key := node.value], k, v);
          }
          (MapModelRec(node.left, sk.left) + MapModelRec(node.right, sk.right) + map[node.key := node.value])[k := v];
          MapModelRec(node, sk)[k := v];
        }
        ghost var newSkRight;
        node.right, newSkRight, insertedNode := InsertRec(node.right, sk.right, k, v);
        assume MapModelRec(node.right, newSkRight) == old(MapModelRec(node.right, sk.right)[k := v]);
        newSk := Node(sk.left, node, newSkRight);
        assert SearchTreeRec(newSk);
        MapModelLemmas(newNode, newSk);
        calc == {
          MapModelRec(newNode, newSk);
          MapModelRec(newNode.left, sk.left) + MapModelRec(node.right, newSkRight) + map[node.key := node.value];
          old(MapModelRec(node.left, sk.left)) + old(MapModelRec(node.right, sk.right)[k := v]) + old(map[node.key := node.value]);
          old((MapModelRec(node.left, sk.left) + MapModelRec(node.right, sk.right)[k := v] + map[node.key := node.value]));
          old((MapModelRec(node.left, sk.left) + MapModelRec(node.right, sk.right) + map[node.key := node.value])[k := v]);
          old(MapModelRec(node, sk)[k := v]);
        }
        assert MapModelRec(newNode, newSk) == old(MapModelRec(node, sk)[k := v]);
      } else if k < node.key {
        assume false;
        ghost var newSkLeft;
        node.left, newSkLeft, insertedNode := InsertRec(node.left, sk.left, k, v);
        newSk := Node(newSkLeft, node, sk.right);
        assume MapModelRec(newNode, newSk) == old(MapModelRec(node, sk)[k := v]);
      } else {
        assert false;
      }
    }
  }

  lemma InsertMap(omm: map<K, V>, mm: map<K, V>, k: K, v: V)
    requires k in mm
    requires mm[k] == v
    requires forall m | m in omm && k != m :: m in mm && mm[m] == omm[m]
    requires forall m | m in mm && k != m :: m in omm
    ensures mm == omm[k := v]
  {}

  method {:verify false} Insert(k: K, v: V)
    modifies this, Repr()
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    ensures k in MapModel()
    ensures MapModel()[k] == v
    // TODO: la siguiente línea no es equivalente a las siguientes
    ensures forall m | m in old(MapModel()) && k != m :: m in MapModel() && MapModel()[m] == old(MapModel()[m])
    // ensures forall m | m in MapModel() && k != m :: m in old(MapModel())
    // ensures MapModel() == old(MapModel()) + map[k := v]
    // ensures MapModel() == old(MapModel())[k := v]

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    forall m | m in MapModel() && k != m
      ensures exists n | n in elems(skeleton) :: n.key == m && n.value == MapModel()[m]
    {
      ModelRelationWithSkeleton(m, MapModel()[m]);
    }
    ghost var insertedNode;
    root, skeleton, insertedNode := InsertRec(root, skeleton, k, v);
    ModelRelationWithSkeleton(k, v);
    forall m | m in old(MapModel()) && k != m
      ensures m in MapModel() && MapModel()[m] == old(MapModel()[m])
    {
      ModelRelationWithSkeleton(m, old(MapModel()[m]));
    }
    forall m | m in MapModel() && k != m
      ensures m in old(MapModel())
    {
      ModelRelationWithSkeletonKeyRecL(old(root), old(skeleton), m);
    }
  }

  static method {:verify false} RemoveMinRec(node: TNode, ghost sk: tree<TNode>) returns (newNode: TNode?, ghost newSk: tree<TNode>, removedNode: TNode)
    modifies set x | x in elems(sk) :: x`left

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures elems(sk) >= elems(newSk)
    ensures elems(newSk) == set n | n in elems(sk) && n.key != removedNode.key :: n
    ensures elems(newSk) + {removedNode} == elems(sk)
    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures exists n | n in elems(sk) :: n.key == removedNode.key
    ensures forall n | n in elems(sk) && n.key != removedNode.key :: removedNode.key < n.key
    ensures forall n | n in elems(sk) && n.key == removedNode.key :: removedNode.value == n.value && n !in elems(newSk)
    ensures forall n | n in elems(newSk) :: n.key == old(n.key)
    ensures MapModelRec(newNode, newSk) == map k | k in old(MapModelRec(node, sk)) && k != removedNode.key :: old(MapModelRec(node, sk)[k])

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    if node.left == null {
      newNode := node.right;
      newSk := sk.right;
      removedNode := node;
    } else {
      ghost var newSkLeft;
      node.left, newSkLeft, removedNode := RemoveMinRec(node.left, sk.left);
      newNode := node;
      newSk := Node(newSkLeft, newNode, sk.right);
    }
  }

  static function FindNode(k: K, node: TNode?, sk: tree<TNode>): TNode
    reads elems(sk)
    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires exists n | n in elems(sk) :: n.key == k
    ensures FindNode(k, node, sk).key == k
    ensures forall n | n in elems(sk) && n.key == k :: n == FindNode(k, node, sk)
    ensures FindNode(k, node, sk) in elems(sk)
  {
    match sk {
      case Empty() => assert false; assert sk.Node?; sk.data
      case Node(l, n, r) =>
        if k < n.key then
          FindNode(k, node.left, sk.left)
        else if n.key < k then
          FindNode(k, node.right, sk.right)
        else
          assert n.key == k;
          n
    }
  }

  static function TreeKeys(sk: tree<TNode>): set<K>
    reads elems(sk)
  {
    set n | n in elems(sk) :: n.key
  }

  // static lemma MapModelLemmas(node: TNode?, sk: tree<TNode>)
  //   requires ValidRec(node, sk)
  //   requires SearchTreeRec(sk)
  //   ensures MapModelRec(node, sk).Keys == TreeKeys(sk)
  //   ensures MapModelRec(node, sk) == map k | k in TreeKeys(sk) :: FindNode(k, node, sk).value
  //   ensures forall n | n in elems(sk) :: n.key in MapModelRec(node, sk)
  //   ensures sk.Node? ==> forall k | k in MapModelRec(node, sk.left) :: k !in MapModelRec(node, sk.right)
  //   ensures sk.Node? ==> forall k | k in MapModelRec(node, sk.right) :: k !in MapModelRec(node, sk.left)

  //   // ensures sk.Node? ==> sk.data.key !in MapModelRec(root.right, sk.right)
  //   // ensures sk.Node? ==> forall k | sk.data.key < k :: k !in MapModelRec(root.left, sk.left)
  // {
  //   match sk {
  //     case Empty() => {}
  //     case Node(l, n, r) => {
  //       MapModelLemmas(node.left, sk.left);
  //       MapModelLemmas(node.right, sk.right);
  //     }
  //   }
  // }

  method RotateRight(node: TNode, ghost sk: tree<TNode>) returns (newNode: TNode, ghost newSk: tree<TNode>)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color
    requires Tree.ValidRec(node, sk)
    // requires node.left != null ==> node.left.color.Black?
    requires node.left != null
    requires node.left.color.Red?
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk.left)
    requires Tree.RedBlackTreeRec(sk.right)
    requires Tree.BlackHeight(sk.left) == Tree.BlackHeight(sk.right)

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))
    // ensures
    //   old((node.left != null ==> node.left.color.Black?)
    //     && (node.right.left != null ==> node.right.left.color.Black?)
    //     && (node.right.right != null ==> node.right.right.color.Black?))
    //   ==> RedBlackTreeRec(newSk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    newNode := node.left;
    node.left := newNode.right;
    newNode.right := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := Node(sk.left.left, newNode, Node(sk.left.right, node, sk.right));
  }

  static method {:verify false} RemoveRec(node: TNode?, ghost sk: tree<TNode>, k: K) returns (newNode: TNode?, ghost newSk: tree<TNode>, ghost removedNode: TNode?)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    // modifies set x | x in elems(sk) :: x`key
    // modifies set x | x in elems(sk) :: x`value
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures forall n | n in elems(sk) :: n.key == old(n.key) && n.value == old(n.value)
    ensures elems(sk) >= elems(newSk)
    ensures forall n | n in elems(newSk) :: n.key == old(n.key) && n.value == old(n.value)
    ensures elems(newSk) == set n | n in elems(sk) && n.key != k :: n
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures removedNode != null ==> removedNode in elems(sk) && removedNode.key == k
    ensures removedNode != null ==> elems(newSk) + {removedNode} == elems(sk)
    // ensures MapModelRec(newSk).Keys == old(MapModelRec(sk).Keys) - {k}
    ensures TreeKeys(newSk) == old(TreeKeys(sk)) - {k}
    // ensures removedNode != null ==> MapModelRec(newNode, newSk) == map k' | k' in old(MapModelRec(node, sk)) && removedNode.key != k' :: old(MapModelRec(node, sk)[k'])
    // ensures MapModelRec(newNode, newSk) == map k' | k' in old(MapModelRec(node, sk)) && k != k' :: old(MapModelRec(node, sk)[k'])

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    if node == null {
      newNode := node;
      newSk := sk;
      removedNode := null;
    } else {
      if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, removedNode := RemoveRec(node.right, sk.right, k);
        newNode := node;
        newSk := Node(sk.left, node, newSkRight);
      } else if k < node.key {
        newNode := node;
        ghost var newSkLeft;
        node.left, newSkLeft, removedNode := RemoveRec(node.left, sk.left, k);
        newSk := Node(newSkLeft, node, sk.right);
      } else {
        assert k == node.key;
        if node.right == null {
          newNode := node.left;
          newSk := sk.left;
          removedNode := node;
        } else if node.left == null {
          newNode := node.right;
          newSk := sk.right;
          removedNode := node;
        } else {
          removedNode := node;
          ghost var newSkRight;
          var newRight;
          newRight, newSkRight, newNode := RemoveMinRec(node.right, sk.right);
          newNode.left := node.left;
          newNode.right := newRight;
          newSk := Node(sk.left, newNode, newSkRight);
        }
      }
    }
  }

  method {:verify false} Remove(k: K)
    modifies this, Repr()
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    // ensures forall m | m in MapModel() && k != m :: m in old(MapModel()) && MapModel()[m] == old(MapModel()[m])
    ensures k !in MapModel()
    // ensures MapModel() + map[k := old(MapModel()[k])] == old(MapModel())
    ensures MapModel() == map k' | k' in old(MapModel()) && k' != k :: old(MapModel()[k'])

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    // forall m | m in MapModel() && k != m
    //   ensures exists n | n in elems(skeleton) :: n.key == m && n.value == MapModel()[m]
    // {
    //   ModelRelationWithSkeleton(m, MapModel()[m]);
    // }
    // MapModelLemmas(root, skeleton);
    ghost var removedNode;
    root, skeleton, removedNode := RemoveRec(root, skeleton, k);
    ContraModelRelationWithSkeletonKeyRecR(root, skeleton, k);
    // assume MapModelRec(skeleton).Keys == TreeKeys(skeleton);
    // MapModelLemmas(root, skeleton);
    // forall m | m in old(MapModel()) && k != m
    //   ensures m in MapModel() && MapModel()[m] == old(MapModel()[m])
    // {
    //   // ModelRelationWithSkeleton(m, old(MapModel()[m]));
    //   assert exists n | n in elems(skeleton) :: n.key == m && n.value == old(MapModel()[m]);
    //   ModelRelationWithSkeletonRecL(root, skeleton, m, old(MapModel()[m]));
    //   assert m in MapModel() && MapModel()[m] == old(MapModel()[m]);
    // }
  }

  static function BlackHeight(sk: tree<TNode>): nat
    reads set x | x in elems(sk) :: x`color
  {
    match sk {
      case Empty() => 0
      case Node(l, n, r) =>
        if n.color.Black? then
          1 + max(BlackHeight(l), BlackHeight(r))
        else
          max(BlackHeight(l), BlackHeight(r))
    }
  }

  static predicate RedBlackTreeRec(sk: tree<TNode>)
    reads set x | x in elems(sk) :: x`key
    reads set x | x in elems(sk) :: x`color
  {
    match sk {
      case Empty() => true
      case Node(l, n, r) =>
        // Red links lean left:
        && (!r.Empty? ==> r.data.color.Black?)
        // No node has two red links connected to it:
        && (!l.Empty? && l.data.color.Red? && !l.left.Empty? ==> l.left.data.color.Black?)
        // && (n.color.Red? && !l.Empty? ==> l.data.color.Black?)
        // Perfect black balance:
        && BlackHeight(l) == BlackHeight(r)

        && RedBlackTreeRec(l)
        && RedBlackTreeRec(r)
    }
  }

  predicate RedBlackTree()
    reads this, Repr()
    requires Valid()
  {
    && SearchTree()
    && (root != null ==> root.color.Black?)
    && RedBlackTreeRec(skeleton)
  }

  static method {:verify false} RotateLeft(node: TNode, ghost sk: tree<TNode>) returns (newNode: TNode, ghost newSk: tree<TNode>)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color
    requires ValidRec(node, sk)
    // requires node.left != null ==> node.left.color.Black?
    requires node.right != null
    requires node.right.color.Red?
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk.left)
    requires RedBlackTreeRec(sk.right)
    requires BlackHeight(sk.left) == BlackHeight(sk.right)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))
    // ensures RedBlackTreeRec(newSk)
    // ensures old(node.left != null && node.left.color.Black?) ==> RedBlackTreeRec(newSk)
    ensures
      old((node.left != null ==> node.left.color.Black?)
        && (node.right.left != null ==> node.right.left.color.Black?)
        && (node.right.right != null ==> node.right.right.color.Black?))
      ==> RedBlackTreeRec(newSk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    newNode := node.right;
    node.right := newNode.left;
    newNode.left := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := Node(Node(sk.left, node, sk.right.left), newNode, sk.right.right);
  }
}

class STree {
  var tree: Tree;

  constructor()
  {
    this.tree := new Tree();
  }

  function Repr(): set<object>
    reads this, tree
  {
    tree.Repr()
  }

  predicate Valid()
    reads this, tree, tree.Repr()
  {
    && tree.Valid()
    && tree.SearchTree()
  }

  method {:verify false} Get(k: K) returns (v: V)
    requires Valid()
    requires k in tree.MapModel()
    ensures Valid()
    ensures k in tree.MapModel()
    ensures tree.MapModel()[k] == v

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    assert Repr() == tree.Repr();
    v := tree.Get(k);
  }
}
