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
    case Node(l, x, r) => max(depth(l), depth(r)) + 1
  }
}

type K = int
type V = int

class TNode {
  var key: K;
  var value: V;
  var left: TNode?;
  var right: TNode?;

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

  static predicate ValidRec(tree: TNode?, sk: tree<TNode>)
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

  static function MapModelRec(sk: tree<TNode>): map<K, V>
    reads set x | x in elems(sk) :: x`key
    reads set x | x in elems(sk) :: x`value
    // requires SearchTreeRec(sk)
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
    // requires SearchTree()
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

  lemma ModelRelationWithSkeleton(k: K, v: V)
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

  static lemma ModelRelationWithSkeletonRecR(node: TNode?, sk: tree<TNode>, k: K, v: V)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires k in MapModelRec(sk)
    requires MapModelRec(sk)[k] == v
    ensures (exists n | n in elems(sk) :: n.key == k && n.value == v)
  {}

  static lemma ModelRelationWithSkeletonRecL(node: TNode?, sk: tree<TNode>, k: K, v: V)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires (exists n | n in elems(sk) :: n.key == k && n.value == v)
    ensures k in MapModelRec(sk)
    ensures MapModelRec(sk)[k] == v
  {
    match sk {
      case Empty => {}
      case Node(l, n, r) => {
        if n.key == k {
        } else if k < n.key {
          assert k in MapModelRec(l);

          assert forall m | m in elems(r) :: n.key != m.key;
          if k in MapModelRec(r) {
            ModelRelationWithSkeletonKeyRecR(n.right, r, k);
            assert false;
          }
          assert k !in MapModelRec(r);

          assert MapModelRec(sk)[k] == v;
        } else if n.key < k {
        } else {
          assert false;
        }
      }
    }
  }

  lemma ModelRelationWithSkeletonKey(k: K)
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

  static lemma ModelRelationWithSkeletonKeyRecR(node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires k in MapModelRec(sk)
    ensures (exists n | n in elems(sk) :: n.key == k)
  {}

  static lemma ContraModelRelationWithSkeletonKeyRecR(node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires forall m | m in elems(sk) :: k != m.key;
    ensures k !in MapModelRec(sk)
  {
      if k in MapModelRec(sk) {
        ModelRelationWithSkeletonKeyRecR(node, sk, k);
        assert false;
      }
      assert k !in MapModelRec(sk);
  }

  static lemma ModelRelationWithSkeletonKeyRecL(node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires (exists n | n in elems(sk) :: n.key == k)
    ensures k in MapModelRec(sk)
  {
    match sk {
      case Empty => {}
      case Node(l, n, r) => {}
    }
  }

  static method {:verify true} GetRec(n: TNode, ghost sk: tree<TNode>, k: K) returns (v: V, ghost z:TNode)
    requires ValidRec(n, sk)
    requires SearchTreeRec(sk)
    requires k in MapModelRec(sk)
    requires forall x | x in elems(sk) :: allocated(x)

    ensures ValidRec(n, sk)
    ensures SearchTreeRec(sk)
    ensures MapModelRec(sk)[k]==v
    ensures z in elems(sk) && z.key==k && z.value==v

    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {    
    /*GHOST*/ModelRelationWithSkeletonKeyRecR(n,sk,k);

    if k == n.key {
      v := n.value; z:=n; 
    } else if n.key < k {
      v,z := GetRec(n.right, sk.right, k);
    } else if k < n.key {
      v,z := GetRec(n.left, sk.left, k);
    } 
    
    /*GHOST*/ ModelRelationWithSkeletonRecL(n,sk,k, v);

  }

  method {:verify true} Get(k: K) returns (v: V)
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
    assert Repr() == elems(skeleton);
    ghost var z;
    
    v,z := GetRec(root, skeleton, k);
  }

  static method {:verify false} InsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V) returns (newNode: TNode, ghost newSk: tree<TNode>, ghost z:TNode)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires forall x | x in elems(sk) :: allocated(x)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures MapModelRec(newSk)==MapModelRec(sk)[k:=v]
//    ensures elems(newSk)==elems(sk)-{node}+{z,newNode}
    ensures forall x {:trigger x in elems(newSk), x in old(elems(newSk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      newNode := new TNode(null, k, v, null);
      newSk := Node(Empty, newNode, Empty);
      z:=newNode;
    } else {
      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        z:=node;
      } else if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, z := InsertRec(node.right, sk.right, k, v);
        newSk := Node(sk.left, node, newSkRight);
      } else if k < node.key {
        ghost var newSkLeft;
        node.left, newSkLeft,z := InsertRec(node.left, sk.left, k, v);
        newSk := Node(newSkLeft, node, sk.right);
      } else {
        assert false;
      }
    }
  }

  method {:verify true} Insert(k: K, v: V)
    modifies this, Repr()
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    ensures MapModel() == old(MapModel())[k := v]

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  { ghost var z;
    root, skeleton, z := InsertRec(root, skeleton, k, v);
    ModelRelationWithSkeleton(k, v);
    
  }

  static method {:verify false} RemoveMinRec(node: TNode, ghost sk: tree<TNode>) returns (newNode: TNode?, ghost newSk: tree<TNode>, minK: K, minV: V)
    modifies set x | x in elems(sk) :: x`left

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures elems(sk) >= elems(newSk)
    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures exists n | n in elems(sk) :: n.key == minK
    ensures forall n | n in elems(sk) && n.key != minK :: minK < n.key
    ensures forall n | n in elems(sk) && n.key == minK :: minV == n.value && n !in elems(newSk)
    ensures forall n | n in elems(newSk) :: n.key == old(n.key)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    if node.left == null {
      newNode := node.right;
      newSk := sk.right;
      minK := node.key;
      minV := node.value;
    } else {
      ghost var newSkLeft;
      node.left, newSkLeft, minK, minV := RemoveMinRec(node.left, sk.left);
      newNode := node;
      newSk := Node(newSkLeft, newNode, sk.right);
    }
  }

  static method {:verify false} RemoveRec(node: TNode?, ghost sk: tree<TNode>, k: K) returns (newNode: TNode?, ghost newSk: tree<TNode>)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`key
    modifies set x | x in elems(sk) :: x`value
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures forall n | n in elems(newSk) :: n.key != k
    ensures elems(sk) >= elems(newSk)
    ensures forall m | m in elems(newSk) :: exists n | n in elems(sk) :: m.key == old(n.key)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    if node == null {
      newNode := node;
      newSk := sk;
    } else {
      if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight := RemoveRec(node.right, sk.right, k);
        newNode := node;
        newSk := Node(sk.left, node, newSkRight);
      } else if k < node.key {
        newNode := node;
        ghost var newSkLeft;
        node.left, newSkLeft := RemoveRec(node.left, sk.left, k);
        newSk := Node(newSkLeft, node, sk.right);
      } else {
        assert k == node.key;
        if node.right == null {
          newNode := node.left;
          newSk := sk.left;
        } else if node.left == null {
          newNode := node.right;
          newSk := sk.right;
        } else {
          ghost var newSkRight;
          var minK, minV;
          node.right, newSkRight, minK, minV := RemoveMinRec(node.right, sk.right);
          newNode := node;
          newNode.key := minK;
          newNode.value := minV;
          newSk := Node(sk.left, newNode, newSkRight);
        }
      }
    }
  }

  method {:verify false}  Remove(k: K)
    modifies this, Repr()
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    // ensures forall m | m in MapModel() && k != m :: m in old(MapModel()) && MapModel()[m] == old(MapModel()[m])
    ensures k !in MapModel()

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    root, skeleton := RemoveRec(root, skeleton, k);
    ContraModelRelationWithSkeletonKeyRecR(root, skeleton, k);
  }
}

/*class STree {
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

  method Get(k: K) returns (v: V)
    requires Valid()
    requires k in tree.MapModel()
    ensures Valid()
    ensures k in tree.MapModel()
    ensures tree.MapModel()[k] == v

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x | x in Repr() :: allocated(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    assert Repr() == tree.Repr();
    v := tree.Get(k);
  }
}*/