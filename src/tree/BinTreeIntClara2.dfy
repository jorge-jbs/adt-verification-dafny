include "../../src/Order.dfy"

//type tree<A> = Node?<A>

datatype tree<A> = Empty | Node(left: tree<A>, data: A, right: tree<A>)

function method Leaf<A>(d: A): tree<A>
{
  Node(Empty, d, Empty)
}

function method elems<A>(t: tree<A>): set<A>
  ensures t.Empty? ==> elems(t) == {}
  ensures !t.Empty? ==> elems(t) == elems(t.left) + {t.data} + elems(t.right)
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

  static function MapModelRec(sk: tree<TNode>): map<K, V>
    reads set x | x in elems(sk) :: x`key
    reads set x | x in elems(sk) :: x`value
    // requires SearchTreeRec(sk)
    ensures forall n | n in elems(sk) :: n.key in MapModelRec(sk)
  {
    match sk {
      case Empty() => map[]
      case Node(l, n, r) => (MapModelRec(l) + MapModelRec(r))[n.key := n.value]
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

  // TODO: devolver el nuevo nodo insertado como fantasma
  /*static method InsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V) returns (newNode: TNode, ghost newSk: tree<TNode>)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures newNode == node <==> node != null
    ensures node == null ==> newNode.left == null && newNode.key == k && newNode.value == v && newNode.right == null
    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures exists n | n in elems(newSk) :: n.key == k && n.value == v
    ensures forall n | n in elems(sk) :: n.key == old(n.key) && (if n.key == k then n.value == v else n.value == old(n.value))
    ensures forall n | n in elems(newSk) && n.key != k :: exists m | m in elems(sk) :: n.key == old(m.key) && n.value == old(m.value)
    ensures exists n | n in elems(newSk) :: n.key == k && n.value == v && elems(sk) + {n} == elems(newSk)
    // ensures elems(sk) <= elems(newSk)
    ensures forall n | n in elems(sk) :: n in elems(newSk)
    ensures newNode in elems(newSk)
    // ensures forall m | m in old(MapModelRec(sk)) && k != m :: m in MapModelRec(newSk) && MapModelRec(newSk)[m] == old(MapModelRec(sk)[m])

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(newSk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      assert elems(sk)=={};
      newNode := new TNode(null, k, v, null);
      newSk := Node(Empty, newNode, Empty);      
    } else {
      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        assert elems(sk)==elems(newSk);
      } else if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight := InsertRec(node.right, sk.right, k, v);
        assert forall n | n in elems(sk.right) :: n in elems(newSkRight);

        newSk := Node(sk.left, node, newSkRight);
        
        assert elems(newSk)==elems(sk.left)+{node}+elems(newSkRight);
        
        assert forall n | n in elems(sk) :: n in elems(newSk);

      } else if k < node.key {
        ghost var newSkLeft;
        node.left, newSkLeft := InsertRec(node.left, sk.left, k, v);
                assert forall n | n in elems(sk.left) :: n in elems(newSkLeft);

        newSk := Node(newSkLeft, node, sk.right);
        assert elems(newSk)==elems(newSkLeft)+{node}+elems(sk.right);
        
        assert forall n | n in elems(sk) :: n in elems(newSk);

      } else {
        assert false;
      }
    }
  }*/
static lemma commuteMapModelRec(sk: tree<TNode>,k:K, v:V)
  requires sk!=Empty() && SearchTreeRec(sk) && k < sk.data.key
  ensures MapModelRec(sk)[k:=v]==(MapModelRec(sk.left)[k:=v]+MapModelRec(sk.right))[sk.data.key:=sk.data.value]

static lemma pushUpMapModelRec(skLeft: tree<TNode>,node:TNode, skRight:tree<TNode>, k:K, v:V)
  requires  SearchTreeRec(Node(skLeft,node,skRight)) && k < node.key
  ensures (MapModelRec(skLeft)[k:=v]+MapModelRec(skRight))[node.key:=node.value]==
          MapModelRec(Node(skLeft,node,skRight))[k:=v]

static lemma pushUpMap(ml:map<K,V>, mr:map<K,V>, k:K, v:V)
requires k !in mr 
ensures ml[k:=v]+mr == (ml+mr)[k:=v]

static lemma keysSearchTree(sk:tree<TNode>,k:K)
requires SearchTreeRec(sk)  && sk !=Empty()
ensures  k < sk.data.key ==> k !in MapModelRec(sk.right)
ensures  k > sk.data.key ==> k !in MapModelRec(sk.left)

  static method {:verify true} InsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V) returns (newNode: TNode, ghost newSk: tree<TNode>, ghost z:TNode)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires forall x | x in elems(sk) :: allocated(x)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures MapModelRec(newSk)==old(MapModelRec(sk))[k:=v]

    ensures elems(newSk)==elems(sk)+{z}
    ensures z.key==k && z.value==v
    ensures forall n | n in elems(sk) && n.key!=k :: n.key==old(n.key) && n.value==old(n.value)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(newSk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {


    if node == null {
      newNode := new TNode(null, k, v, null);
      newSk := Node(Empty, newNode, Empty);
      z:=newNode;
      //assert  MapModelRec(newSk)==old(MapModelRec(sk))[k:=v];
    } else {
       assert sk.data==node;

      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        z:=node;

      //assert  MapModelRec(newSk)==old(MapModelRec(sk))[k:=v];

      } else if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, z := InsertRec(node.right, sk.right, k, v);


        newSk := Node(sk.left, node, newSkRight);
      
        //assert MapModelRec(newSk.left)==old(MapModelRec(sk.left));
        //assert MapModelRec(newSk.right)==old(MapModelRec(sk.right))[k:=v];
        //assert MapModelRec(newSk)==(MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];

      } else if k < node.key {

        keysSearchTree(sk,k);
        assert k !in MapModelRec(sk.right);
        assert k !in MapModelRec(sk.right)[node.key:=node.value];

        ghost var newSkLeft;
        node.left, newSkLeft,z := InsertRec(node.left, sk.left, k, v);

        newSk := Node(newSkLeft, node, sk.right);

        assert node.key==old(node.key) && node.value==old(node.value);
        


        calc =={
           MapModelRec(newSk);
           (MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];
           (old(MapModelRec(sk.left))[k:=v]+old(MapModelRec(sk.right)))[node.key:=node.value];
           old(MapModelRec(sk.left))[k:=v]+old(MapModelRec(sk.right))[node.key:=node.value];
           {
             assert k !in old(MapModelRec(sk.right))[node.key:=node.value];
           pushUpMap(old(MapModelRec(sk.left)),old(MapModelRec(sk.right))[old(node.key):=old(node.value)],k,v);}
           (old(MapModelRec(sk.left))+old(MapModelRec(sk.right))[old(node.key):=old(node.value)])[k:=v];
           old(MapModelRec(sk))[k:=v];
        
        }

      } else {
        assert false;
      }
    }
  }

  lemma InsertMap(omm: map<K, V>, mm: map<K, V>, k: K, v: V)
    requires k in mm
    requires mm[k] == v
    requires forall m | m in omm && k != m :: m in mm && mm[m] == omm[m]


static lemma sameModelRec(sk: tree<TNode>,newSk:tree<TNode>)
requires elems(newSk)==elems(sk)
ensures MapModelRec(sk)==MapModelRec(newSk)

static lemma newModelRec(sk: tree<TNode>,newSk:tree<TNode>,z:TNode)
requires z !in elems(sk)
requires elems(newSk)==elems(sk)+{z}
ensures MapModelRec(sk)[z.key:=z.value]==MapModelRec(newSk)

  method {:verify false} Insert(k: K, v: V)
    modifies this, Repr()
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    ensures k in MapModel()
    ensures MapModel()[k] == v
    // TODO: la siguiente línea no es equivalente a las siguientes
    //ensures forall m | m in old(MapModel()) && k != m :: m in MapModel() && MapModel()[m] == old(MapModel()[m])
    //ensures forall m | m in MapModel() && k != m :: m in old(MapModel()) && old(MapModel())[m]==MapModel()[m]
    // ensures MapModel() == old(MapModel()) + map[k := v]
     ensures MapModel() == old(MapModel())[k := v]

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    /*forall m | m in MapModel() && k != m
      ensures exists n | n in elems(skeleton) :: n.key == m && n.value == MapModel()[m]
    {
      ModelRelationWithSkeleton(m, MapModel()[m]);
    }*/
    ghost var z;
    ghost var oskeleton:=skeleton;
    ghost var oldMapModel:=MapModelRec(oskeleton);
    assert oldMapModel==MapModelRec(oskeleton);
    root, skeleton, z := InsertRec(root, skeleton, k, v);
    
    /*assert elems(skeleton)==elems(old(skeleton))+{z};

    if (z !in elems(old(skeleton)))
    {
      newModelRec(old(skeleton),skeleton,z);
      assert MapModelRec(old(skeleton))[z.key:=z.value]==MapModelRec(skeleton);
    }
    else{
     assert elems(skeleton)==elems(old(skeleton));
     sameModelRec(old(skeleton),skeleton);
     assert  MapModelRec(old(skeleton))==MapModelRec(skeleton);
     assert MapModel()==MapModelRec(skeleton)==MapModelRec(old(skeleton))[k:=v];
    }
     assert old(MapModel())==old(MapModelRec(skeleton));
     

    assert MapModelRec(skeleton)==MapModelRec(old(skeleton))[k:=v];
    
    assert old(MapModel())==oldMapModel;
    assert old(skeleton)==oskeleton;*/
    //assert oldMapModel==MapModelRec(oskeleton);
    //assert MapModel()==MapModelRec(skeleton)==MapModelRec(old(skeleton))[k:=v];
    
    //assert old(MapModel())==MapModelRec(old(skeleton));
    /*ModelRelationWithSkeleton(k, v);
    forall m | m in old(MapModel()) && k != m
      ensures m in MapModel() && MapModel()[m] == old(MapModel()[m])
    {
      ModelRelationWithSkeleton(m, old(MapModel()[m]));
    }*/
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

  static method {:verify false}  RemoveRec(node: TNode?, ghost sk: tree<TNode>, k: K) returns (newNode: TNode?, ghost newSk: tree<TNode>)
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

  method {:verify false} Remove(k: K)
    modifies this, Repr()
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    // ensures forall m | m in MapModel() && k != m :: m in old(MapModel()) && MapModel()[m] == old(MapModel()[m])
    ensures k !in MapModel()
    // ensures MapModel() + map[k := old(MapModel()[k])] == old(MapModel())
    // ensures MapModel() == map k' | k' in old(MapModel()) && k' != k :: old(MapModel()[k'])

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    root, skeleton := RemoveRec(root, skeleton, k);
    ContraModelRelationWithSkeletonKeyRecR(root, skeleton, k);
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