include "../../src/Order.dfy"
include "../../src/tree/TreeData.dfy"

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

  constructor RedBlack(l: TNode?, k: K, v: V, r: TNode?, c: Color)
    ensures left == l
    ensures key == k
    ensures value == v
    ensures right == r
    ensures color == c
  {
    key := k;
    value := v;
    left := l;
    right := r;
    color := c;
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
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`right
    //ensures ValidRec(node, sk) ==> (node == null <==> sk.Empty?)
    //ensures ValidRec(node, sk) ==> (node != null <==> sk.Node?)
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

  static function {:opaque} MapModelRec(sk: tree<TNode>): map<K, V>
    reads set x | x in elems(sk) :: x`key
    reads set x | x in elems(sk) :: x`value
    //ensures forall n | n in elems(sk) :: n.key in MapModelRec(sk)
    //ensures sk.Empty? ==> MapModelRec(sk) == map[]
    //ensures !sk.Empty? ==> MapModelRec(sk) == (MapModelRec(sk.left)+MapModelRec(sk.right))[sk.data.key:=sk.data.value]
  {
    match sk {
      case Empty() => map[]
      case Node(l, n, r) => (MapModelRec(l) + MapModelRec(r))[n.key := n.value]
    }
  }

  static function FindNode(k: K, node: TNode?, sk: tree<TNode>): TNode
    reads elems(sk)
    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires exists n | n in elems(sk) :: n.key == k
    ensures FindNode(k, node, sk).key == k
    ensures forall n | n in elems(sk) && n.key == k :: n == FindNode(k, node, sk)
  {
    match sk {
      case Empty() => assert false; node
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

  static lemma MapModelLemmas(node: TNode?, sk: tree<TNode>)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    ensures MapModelRec(sk).Keys == TreeKeys(sk)
    // ensures MapModelRec(root, sk) == map n | n in elems(sk) :: n.value
    ensures MapModelRec(sk) == map k | k in TreeKeys(sk) :: FindNode(k, node, sk).value
    ensures forall n | n in elems(sk) :: n.key in MapModelRec(sk)
    ensures sk.Node? ==> sk.data.key !in MapModelRec(sk.left)
    ensures sk.Node? ==> sk.data.key !in MapModelRec(sk.right)
    ensures sk.Node? ==> forall k | k in MapModelRec(sk.left) :: k !in MapModelRec(sk.right)
    ensures sk.Node? ==> forall k | k in MapModelRec(sk.right) :: k !in MapModelRec(sk.left)
    // ensures sk.Node? ==> forall k | sk.data.key < k :: k !in MapModelRec(root.left, sk.left)
  {
    reveal MapModelRec();
    match sk {
      case Empty() => {}
      case Node(l, n, r) => {
        reveal MapModelRec();
        MapModelLemmas(node.left, sk.left);
        MapModelLemmas(node.right, sk.right);
      }
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
    ensures MapModel() == map[]
  {
    root := null;
    skeleton := Empty;
    reveal MapModelRec();
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
    requires k in MapModelRec(sk)
    requires MapModelRec(sk)[k] == v
    ensures (exists n | n in elems(sk) :: n.key == k && n.value == v)
  {}

  static lemma {:verify false} ModelRelationWithSkeletonRecL(node: TNode?, sk: tree<TNode>, k: K, v: V)
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

  lemma {:verify false} ModelRelationWithSkeletonKey(k: K)
    requires Valid()
    requires SearchTree()
    ensures k in MapModel() <==> exists n | n in elems(skeleton) :: n.key == k
  {
    ModelRelationWithSkeletonKeyRec(root, skeleton, k);
  }

 static lemma {:verify false} ModelRelationWithSkeletonKeyRec(node: TNode?, sk: tree<TNode>,k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    ensures k in MapModelRec(sk) <==> (exists n | n in elems(sk) :: n.key == k)
  {
    if k in MapModelRec(sk) {
      ModelRelationWithSkeletonKeyRecR(node, sk, k);
    }
    if exists n | n in elems(sk) :: n.key == k {
      ModelRelationWithSkeletonKeyRecL(node, sk, k);
    }
  }

  static lemma {:verify false} ModelRelationWithSkeletonKeyRecR(node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires k in MapModelRec(sk)
    ensures (exists n | n in elems(sk) :: n.key == k)
  {}

  static lemma {:verify false} ContraModelRelationWithSkeletonKeyRecR(node: TNode?, sk: tree<TNode>, k: K)
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

  static lemma {:verify false} ModelRelationWithSkeletonKeyRecL(node: TNode?, sk: tree<TNode>, k: K)
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

  function method {:verify false} isEmpty(): bool
    reads this, Repr()
    requires Valid()
    ensures isEmpty() <==> MapModel() == map[]
  { root==null }

  function method {:verify false} Size():nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |MapModel()|
  //TO  DO:añadir tamaño

  static method {:verify false} GetRec(n: TNode, ghost sk: tree<TNode>, k: K) returns (v: V)
    requires ValidRec(n, sk)
    requires SearchTreeRec(sk)
    //requires exists n | n in elems(sk) :: n.key == k
    requires k in MapModelRec(sk)

    ensures ValidRec(n, sk)
    ensures SearchTreeRec(sk)
    ensures exists n | n in elems(sk) :: n.key == k && n.value == v
    ensures MapModelRec(sk)==old(MapModelRec(sk))
    ensures MapModelRec(sk)[k]==v

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)

  static method {:verify false} SearchRec(n: TNode, ghost sk: tree<TNode>, k: K) returns (b:bool, ghost z:TNode)
    requires ValidRec(n, sk)
    requires SearchTreeRec(sk)
    ensures ValidRec(n, sk)
    ensures SearchTreeRec(sk)
    ensures b == exists n | n in elems(sk) :: n.key == k
    ensures b ==> z in elems(sk) && z.key==k

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)

  static method {:verify false} FindRec(node: TNode?, ghost sk: tree<TNode>, k: K) returns (found: TNode?)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures ValidRec(node, sk)
    ensures SearchTreeRec(sk)
    ensures found == null <==> k !in old(MapModelRec(sk))
    ensures found != null ==> found.key == k && found.value == MapModelRec(sk)[k] && found in elems(sk)

    //ensures forall n | n in elems(sk) :: n.key == old(n.key) && n.value == old(n.value)
    //ensures MapModelRec(sk) == old(MapModelRec(sk))

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    ModelRelationWithSkeletonKeyRec(node, sk, k);
    if node == null {
      found := null;
    } else {
      if k == node.key {
        found := node;
      } else if node.key < k {
        found := FindRec(node.right, sk.right, k);
      } else if k < node.key {
        found := FindRec(node.left, sk.left, k);
      } else {
        assert false;
      }
    }
    if found != null {
      ModelRelationWithSkeletonRecL(node, sk, k, found.value);
    }
  }

  method {:verify true} Find(k: K) returns (found: TNode?)
    requires Valid()
    requires SearchTree()

    //ensures Valid()
    //ensures SearchTree()
    //ensures MapModel() == old(MapModel())
    //ensures found != null ==> found.key == k

    requires forall x | x in Repr() :: allocated(x)
    //ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    //ensures fresh(Repr()-old(Repr()))
    //ensures forall x | x in Repr() :: allocated(x)
  {
    //found := FindRec(root, skeleton, k);
  }

  method {:verify false} Search(k: K) returns (b:bool)
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    ensures b == (k in MapModel())

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() :: allocated(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

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
    assert Repr() == elems(skeleton);
    v := GetRec(root, skeleton, k);
  }

static lemma {:verify false}  pushUpMapL(ml:map<K,V>, mr:map<K,V>, k:K, v:V)
  requires k !in mr
  ensures ml[k:=v]+mr == (ml+mr)[k:=v]
{}

static lemma {:verify false}  pushUpMapR(ml:map<K,V>, mr:map<K,V>, k:K, v:V)
  ensures (ml+mr)[k:=v]==ml+mr[k:=v]
{}

static lemma {:verify false}  pushUpMapD(ml:map<K,V>, mr:map<K,V>, k:K)
  requires k !in mr
  ensures ml-{k}+mr == (ml+mr)-{k}
{}

static lemma {:verify false}  pushUpMapDR(ml:map<K,V>, mr:map<K,V>, k:K)
  requires k !in ml
  ensures ml+(mr-{k}) == (ml+mr)-{k}
{}

static lemma {:verify false}  deletion(m:map<K,V>, m':map<K,V>, k:K,v:V)
  requires m==m'[k:=v] && k !in m'
  ensures m-{k}==m'
{}

static lemma {:verify false} idem(m:map<K,V>,k:K,v:V)
  requires k in m && m[k]==v
  ensures (m-{k})[k:=v]==m
{}

static lemma {:verify false} idem2(m:map<K,V>,k:K,v:V)
  requires k !in m
  ensures (m[k:=v])-{k}==m
{}

static lemma {:verify false} keysSearchTree(sk:tree<TNode>,k:K)
  requires SearchTreeRec(sk)  && sk !=Empty()
  ensures (set n | n in elems(sk)::n.key) == MapModelRec(sk).Keys
  ensures sk.data.key !in MapModelRec(sk.left) && sk.data.key !in MapModelRec(sk.right)
  ensures MapModelRec(sk.left).Keys !! MapModelRec(sk.right).Keys
  ensures MapModelRec(sk).Keys==MapModelRec(sk.left).Keys+MapModelRec(sk.right).Keys+{sk.data.key}
  ensures  k < sk.data.key ==> k !in MapModelRec(sk.right)
  ensures  k > sk.data.key ==> k !in MapModelRec(sk.left)
{}

static lemma {:verify false} keysSearchTreeP(sk:tree<TNode>)
  requires SearchTreeRec(sk)  && sk !=Empty()
  ensures (set n | n in elems(sk)::n.key) == MapModelRec(sk).Keys
  ensures sk.data.key !in MapModelRec(sk.left) && sk.data.key !in MapModelRec(sk.right)
  ensures MapModelRec(sk.left).Keys !! MapModelRec(sk.right).Keys
  ensures MapModelRec(sk).Keys==MapModelRec(sk.left).Keys+MapModelRec(sk.right).Keys+{sk.data.key}
{}

static lemma {:verify false} oldNewMapModelRecL(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,k:K,v:V)
  requires ValidRec(node,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires MapModelRec(newSk.left)==mskL[k:=v]
  requires MapModelRec(newSk.right)==mskR
  requires node.key !in mskL && node.key !in mskR && node.key !=k && k !in mskR
  requires moSk==(mskL+mskR)[node.key:=node.value]
  ensures MapModelRec(newSk)==moSk[k:=v]
{
  calc == {
    MapModelRec(newSk);
    (MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];
    (mskL[k:=v]+mskR)[node.key:=node.value];
    { pushUpMapR(mskL[k:=v],mskR,node.key,node.value);}
    mskL[k:=v]+mskR[node.key:=node.value];
    {
      assert k !in mskR[node.key:=node.value];
      pushUpMapL(mskL,mskR[node.key:=node.value],k,v);
    }
    ((mskL+mskR)[node.key:=node.value])[k:=v];
    moSk[k:=v];
  }
}

static lemma {:verify false} oldNewMapModelRecR(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,k:K,v:V)
  requires ValidRec(node,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires MapModelRec(newSk.left)==mskL
  requires MapModelRec(newSk.right)==mskR[k:=v]
  requires node.key !in mskL && node.key !in mskR && node.key !=k
  requires moSk==(mskL+mskR)[node.key:=node.value]
  ensures MapModelRec(newSk)==moSk[k:=v]
{
  calc == {
    MapModelRec(newSk);
    (MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];
    (mskL+mskR[k:=v])[node.key:=node.value];
    { pushUpMapR(mskL[k:=v],mskR,node.key,node.value); }
    mskL+mskR[k:=v][node.key:=node.value];
    { assert k != node.key; }
    mskL+mskR[node.key:=node.value][k:=v];
    { pushUpMapR(mskL,mskR[node.key:=node.value],k,v); }
    ((mskL+mskR)[node.key:=node.value])[k:=v];
    moSk[k:=v];
  }
}

  static method {:verify false} InsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V) returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode:TNode)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures MapModelRec(newSk)==old(MapModelRec(sk))[k:=v]

    ensures elems(newSk) == elems(sk)+{insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures forall n | n in elems(sk) && old(n.key) != k ::
      n.key == old(n.key) && n.value == old(n.value)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      newNode := new TNode(null, k, v, null);
      newSk := Node(Empty, newNode, Empty);
      insertedNode := newNode;
      assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v] by {
        reveal MapModelRec();
      }
    } else {
      assert sk.data == node;
      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        insertedNode := node;
        assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v] by {
          reveal MapModelRec();
        }
      } else if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, insertedNode := InsertRec(node.right, sk.right, k, v);
        newSk := Node(sk.left, node, newSkRight);
        assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v] by {
          reveal MapModelRec();
        }
      } else if k < node.key {
        ghost var oMMRight := MapModelRec(sk.right);
        ghost var oMMLeft := MapModelRec(sk.left);
        ghost var oMM := MapModelRec(sk);
        keysSearchTree(sk, k);
        ghost var newSkLeft;
        node.left, newSkLeft, insertedNode := InsertRec(node.left, sk.left, k, v);
        newSk := Node(newSkLeft, node, sk.right);

        assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v] by {
          reveal MapModelRec();
          assert node.key!=k;
          assert node.key==old(node.key) && node.value==old(node.value);
          assert node.key !in oMMLeft && node.key !in oMMRight && node.key !=k;

          assert newSk.left==newSkLeft && newSk.right==sk.right && newSk.data==node;
          assert MapModelRec(newSk.left)==oMMLeft[k:=v];
          assert MapModelRec(newSk.right)==oMMRight;
          assert oMM==(oMMLeft+oMMRight)[node.key:=node.value];
          oldNewMapModelRecL(newSk, old(MapModelRec(sk)), oMMLeft, oMMRight, node, k, v);
        }
      } else {
        assert false;
      }
    }
  }

  method {:verify false} Insert(k: K, v: V)
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
  {
    ghost var z;
    root, skeleton, z := InsertRec(root, skeleton, k, v);
  }

static lemma {:verify false} oldNewMapModelRecRemoveL(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,k:K)
  requires ValidRec(node,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires MapModelRec(newSk.left)==mskL-{k}
  requires MapModelRec(newSk.right)==mskR
  requires node.key !in mskL && node.key !in mskR && node.key !=k && k !in mskR
  requires moSk==(mskL+mskR)[node.key:=node.value]
ensures MapModelRec(newSk)==moSk-{k}
{
  calc == {
    MapModelRec(newSk);
    (MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];
    (mskL-{k}+mskR)[node.key:=node.value];
    { assert node.key !in mskR;
    pushUpMapR(mskL-{k},mskR,node.key,node.value);}
    mskL-{k}+mskR[node.key:=node.value];
    { assert k !in mskR[node.key:=node.value];
    pushUpMapD(mskL,mskR[node.key:=node.value],k);}
    ((mskL+mskR)[node.key:=node.value])-{k};
    moSk-{k};
  }
}

static lemma {:verify false} oldNewMapModelRecRemoveR(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,k:K)
  requires ValidRec(node,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires MapModelRec(newSk.left)==mskL
  requires MapModelRec(newSk.right)==mskR-{k}
  requires node.key !in mskL && node.key !in mskR && node.key !=k && k !in mskL
  requires moSk==(mskL+mskR)[node.key:=node.value]
  ensures MapModelRec(newSk)==moSk-{k}
{
  calc == {
    MapModelRec(newSk);
    (MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];
    (mskL+(mskR-{k}))[node.key:=node.value];
    { assert k !in mskL;
    pushUpMapDR(mskL,mskR,k);}
    ((mskL+mskR)-{k})[node.key:=node.value];
    { assert node.key!=k; }
    ((mskL+mskR)[node.key:=node.value])-{k};
    moSk-{k};
  }
}

static lemma {:verify false} oldNewMapModelRecRemoveRMin(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,newNode:TNode)
  requires ValidRec(newNode,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires MapModelRec(newSk.left)==mskL
  requires MapModelRec(newSk.right)==mskR-{newNode.key}
  requires node.key !in mskL && node.key !in mskR
  requires newNode.key in mskR && mskR[newNode.key]==newNode.value
  requires moSk==(mskL+mskR)[node.key:=node.value]
  ensures MapModelRec(newSk)==moSk-{node.key}
{
  calc == {
    MapModelRec(newSk);
    (MapModelRec(newSk.left)+MapModelRec(newSk.right))[newNode.key:=newNode.value];
    (mskL+(mskR-{newNode.key}))[newNode.key:=newNode.value];
    { pushUpMapR(mskL,mskR-{newNode.key},newNode.key,newNode.value); }
    mskL+(mskR-{newNode.key})[newNode.key:=newNode.value];
    {idem(mskR,newNode.key,newNode.value);}
    mskL+mskR;
    { idem2(mskL+mskR,node.key,node.value); }
    ((mskL+mskR)[node.key:=node.value])-{node.key};
    moSk-{node.key};
  }
}

  static method {:verify false} RemoveMinRec(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode?, ghost newSk: tree<TNode>, removedNode: TNode)
    modifies set x | x in elems(sk) :: x`left

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)

    ensures removedNode in elems(sk)
    ensures removedNode !in elems(newSk)
    ensures removedNode.key == old(removedNode.key)
    ensures removedNode.value == old(removedNode.value)
    ensures elems(newSk) == elems(sk) - {removedNode}

    //ensures removedNode.key in old(MapModelRec(sk))
    //ensures old(MapModelRec(sk))[removedNode.key] == removedNode.value
    //ensures MapModelRec(newSk) == old(MapModelRec(sk)) - {removedNode.key}

    //ensures forall n | n in elems(sk) ::
      //n.key==old(n.key) && n.value==old(n.value)
    //ensures forall n | n in elems(sk) && n.key != removedNode.key ::
      //removedNode.key < n.key
    ensures forall n | n in elems(newSk) ::
      removedNode.key < n.key

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    keysSearchTreeP(sk);

    if node.left == null {
      ghost var oMMRight:=MapModelRec(sk.right);
      ghost var oMM:=MapModelRec(sk);
      deletion(oMM, oMMRight, node.key, node.value);

      newNode := node.right;
      newSk := sk.right;
      removedNode := node;
    } else {
      ghost var oMMRight := MapModelRec(sk.right);
      ghost var oMMLeft := MapModelRec(sk.left);
      ghost var oMM := MapModelRec(sk);

      ghost var newSkLeft;
      node.left, newSkLeft, removedNode := RemoveMinRec(node.left, sk.left);

      newNode:=node;
      newSk := Node(newSkLeft, newNode, sk.right);

      oldNewMapModelRecRemoveL(newSk,oMM,oMMLeft,oMMRight,node,removedNode.key);
    }
  }

  static method {:verify false} RemoveRec(node: TNode?, ghost sk: tree<TNode>, k: K) returns (newNode: TNode?, ghost newSk: tree<TNode>, ghost removedNode: TNode?)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)

    //ensures forall n | n in elems(sk) ::
      //n.key == old(n.key) && n.value == old(n.value)
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures removedNode != null ==>
      && removedNode in elems(sk)
      && removedNode !in elems(newSk)
      && removedNode.key == k
    //ensures k !in old(MapModelRec(sk)) <==> removedNode==null
    //ensures MapModelRec(newSk)==old(MapModelRec(sk))-{k}

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    //ModelRelationWithSkeletonKeyRec(node,sk,k);

    if node == null {
      newNode := node;
      newSk := sk;
      removedNode := null;
      //assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};
    } else {
      //ghost var oMMRight:=MapModelRec(sk.right);
      //ghost var oMMLeft:=MapModelRec(sk.left);
      //ghost var oMM:=MapModelRec(sk);
      //keysSearchTreeP(sk);
      //assert node.key !in oMMLeft && node.key !in oMMRight;

      if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, removedNode := RemoveRec(node.right, sk.right, k);
        newNode := node;
        newSk := Node(sk.left, node, newSkRight);

        //assert MapModelRec(newSkRight)==oMMRight-{k};
        //oldNewMapModelRecRemoveR(newSk,oMM,oMMLeft,oMMRight,node,k);
        //assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};
      } else if k < node.key {
        newNode := node;
        ghost var newSkLeft;
        node.left, newSkLeft, removedNode := RemoveRec(node.left, sk.left, k);
        newSk := Node(newSkLeft, node, sk.right);

        //assert MapModelRec(newSkLeft)==oMMLeft-{k};
        //oldNewMapModelRecRemoveL(newSk,oMM,oMMLeft,oMMRight,node,k);
        //assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};
      } else {
        assert k == node.key;
        if node.right == null {
          newNode := node.left;
          newSk := sk.left;
          removedNode := node;

          //assert oMM==oMMLeft[node.key:=node.value] && node.key !in oMMLeft;
          //deletion(oMM,oMMLeft,node.key,node.value);
          //assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};
        } else {
          removedNode := node;
          ghost var newSkRight;
          var newRight;
          newRight, newSkRight, newNode := RemoveMinRec(node.right, sk.right);

          //assert MapModelRec(newSkRight)==oMMRight-{newNode.key};
          //assert newNode.key in oMMRight && oMMRight[newNode.key]==newNode.value;

          newNode.left := node.left;
          newNode.right := newRight;
          newSk := Node(sk.left, newNode, newSkRight);

          //oldNewMapModelRecRemoveRMin(newSk,oMM,oMMLeft,oMMRight,node,newNode);
          //assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};
        }
      }
    }
  }

  static function method NegColor(color: Color): Color
  {
    match color {
      case Black => Red
      case Red => Black
    }
  }

  static method {:verify false} GFlipColors(node: TNode, ghost sk: tree<TNode>)
    modifies node`color, node.left`color, node.right`color

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires node.left != null
    requires node.left.color == NegColor(node.color)
    requires node.right != null
    requires node.right.color == NegColor(node.color)

    ensures ValidRec(node, sk)
    ensures SearchTreeRec(sk)
    ensures BlackHeight(sk) == old(BlackHeight(sk))
    ensures node.color == NegColor(old(node.color))
    ensures node.left != null
    ensures node.left.color == NegColor(old(node.left.color))
    ensures node.right != null
    ensures node.right.color == NegColor(old(node.right.color))

    /*
    ensures
      (
        && old(RedBlackTreeRec(sk))
        && old(node.color.Red?)
        && old(node.left.left == null || node.left.left.color.Black?)
        && old(node.right.left == null || node.right.left.color.Black?)
      ) ==> (
        TempRedBlack234TreeRec(sk)
      )
    */

    //ensures MapModelRec(sk) == old(MapModelRec(sk))
    //ensures elems(sk) == old(elems(sk))

    requires forall x | x in elems(sk) :: allocated(x)
    //ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    //ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
    /*
    if old(RedBlackTreeRec(sk))
        && old(node.color.Red?)
        && old(node.left.left == null || node.left.left.color.Black?)
        && old(node.right.left == null || node.right.left.color.Black?)
    {
      assert ValidRec(node.left, sk.left);
      assert ValidRec(node.right, sk.right);
      assert old(RedBlackTreeRec(sk.left));
      assert RedBlackTreeRec(sk.left);
      assert old(RedBlackTreeRec(sk.right));
      assert RedBlackTreeRec(sk.right);
      assert ValidRec(node.left.left, sk.left.left);
    }
    */
  }

  static method {:verify false} GRotateLeft(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`right
    modifies node.right`left
    modifies node.right`color

    requires ValidRec(node, sk)
    requires isRed(node.right)
    requires SearchTreeRec(sk)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))

    ensures newNode.left == old(node)
    ensures newNode.left.left == old(node.left)
    ensures newNode.left.right == old(node.right.left)
    ensures newNode == old(node.right)
    ensures newNode.right == old(node.right.right)

    ensures newNode.color == old(node.color)
    ensures newNode.left.color == Red

    //ensures MapModelRec(newSk) == old(MapModelRec(sk))
    ensures elems(newSk) == elems(sk)
    ensures size(newSk) == size(sk)
    ensures size(newSk.left) < size(sk)

    ensures newSk.right == sk.right.right
    ensures newSk.left.left == sk.left
    ensures newSk.left.right == sk.right.left

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    newNode := node.right;
    node.right := newNode.left;
    newNode.left := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := Node(Node(sk.left, node, sk.right.left), newNode, sk.right.right);
    calc {
      size(newSk.left);
      == 1 + size(sk.left) + size(sk.right.left);
      < 1 + size(sk.left) + size(sk.right);
      == size(sk);
    }
    /*
    if newNode.right != null {
      assert ValidRec(newNode.right, newSk.right);
    }
    if newNode.left.left != null {
      assert ValidRec(newNode.left.left, newSk.left.left);
    }
    if newNode.left.right != null {
      assert ValidRec(newNode.left.right, newSk.left.right);
    }
    assert MapModelRec(newSk) == old(MapModelRec(sk)) by {
      reveal MapModelRec();
      calc == {
        MapModelRec(newSk);
        MapModelRec(newSk.left) + MapModelRec(newSk.right)[newNode.key := newNode.value];
        MapModelRec(Node(sk.left, node, sk.right.left)) + MapModelRec(sk.right.right)[newNode.key := newNode.value];
        (MapModelRec(sk.left) + MapModelRec(sk.right.left))[node.key := node.value] + MapModelRec(sk.right.right)[newNode.key := newNode.value];
        (MapModelRec(sk.left) + MapModelRec(sk.right.left)) + map[node.key := node.value] + MapModelRec(sk.right.right) + map[newNode.key := newNode.value];
        {
          assert node.key !in MapModelRec(sk.right.right) by {
            MapModelLemmas(newNode, newSk);
          }
        }
        (MapModelRec(sk.left) + MapModelRec(sk.right.left)) + MapModelRec(sk.right.right) + map[node.key := node.value] + map[newNode.key := newNode.value];
        MapModelRec(sk.left) + (MapModelRec(sk.right.left) + MapModelRec(sk.right.right)) + map[node.key := node.value] + map[newNode.key := newNode.value];
        (MapModelRec(sk.left) + (MapModelRec(sk.right.left) + MapModelRec(sk.right.right))[newNode.key := newNode.value])[node.key := node.value];
        (MapModelRec(sk.left) + (MapModelRec(sk.right.left) + MapModelRec(sk.right.right))[old(node.right.key) := old(node.right.value)])[node.key := node.value];
        old((MapModelRec(sk.left) + (MapModelRec(sk.right.left) + MapModelRec(sk.right.right))[node.right.key := node.right.value])[node.key := node.value]);
        old((MapModelRec(sk.left) + MapModelRec(sk.right))[node.key := node.value]);
        old(MapModelRec(sk));
      }
    }
    */
  }

  static method {:verify false} GRotateRight(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`left
    modifies node.left`right
    modifies node.left`color

    requires ValidRec(node, sk)
    requires isRed(node.left)
    requires SearchTreeRec(sk)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))

    ensures newNode == old(node.left)
    ensures newNode.left == old(node.left.left)
    ensures newNode.right == old(node)
    ensures newNode.right.left == old(node.left.right)
    ensures newNode.right.right == old(node.right)

    ensures newNode.color == old(node.color)
    ensures newNode.right.color == Red

    //ensures MapModelRec(newSk) == old(MapModelRec(sk))
    ensures elems(newSk) == elems(sk)
    ensures size(newSk) == size(sk)
    ensures size(newSk.right) < size(sk)

    ensures newSk.left == sk.left.left
    ensures newSk.right.left == sk.left.right
    ensures newSk.right.right == sk.right

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    newNode := node.left;
    node.left := newNode.right;
    newNode.right := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := Node(sk.left.left, newNode, Node(sk.left.right, node, sk.right));
    calc {
      size(newSk.right);
      == 1 + size(sk.left.right) + size(sk.right);
      < 1 + size(sk.left) + size(sk.right);
      == size(sk);
    }
    /*
    assert ValidRec(newNode.left, newSk.left);
    if newNode.left.left != null {
      assert ValidRec(newNode.left.left, newSk.left.left);
    }
    if newNode.left.right != null {
      assert ValidRec(newNode.left.right, newSk.left.right);
    }
    if newNode.right.left != null {
      assert ValidRec(newNode.right.left, newSk.right.left);
    }
    if newNode.right.right != null {
      assert ValidRec(newNode.right.right, newSk.right.right);
    }
    assert MapModelRec(newSk) == old(MapModelRec(sk)) by {
      reveal MapModelRec();
      calc == {
        MapModelRec(newSk);
        MapModelRec(newSk.left) + MapModelRec(newSk.right)[newNode.key := newNode.value];
        MapModelRec(sk.left.left) + MapModelRec(Node(sk.left.right, node, sk.right)) + map[newNode.key := newNode.value];
        MapModelRec(sk.left.left) + MapModelRec(sk.left.right) + MapModelRec(sk.right) + map[node.key := node.value] + map[newNode.key := newNode.value];
        MapModelRec(sk.left.left) + MapModelRec(sk.left.right) + MapModelRec(sk.right) + map[newNode.key := newNode.value] + map[node.key := node.value];
        {
          assert newNode.key !in MapModelRec(sk.right) by {
            MapModelLemmas(newNode, newSk);
          }
        }
        MapModelRec(sk.left.left) + MapModelRec(sk.left.right) + map[newNode.key := newNode.value] + MapModelRec(sk.right) + map[node.key := node.value];
        old(MapModelRec(sk.left.left) + MapModelRec(sk.left.right) + map[node.left.key := node.left.value] + MapModelRec(sk.right) + map[node.key := node.value]);
        old(MapModelRec(sk.left) + MapModelRec(sk.right) + map[node.key := node.value]);
        old(MapModelRec(sk));
      }
    }
    */
  }

  static lemma {:verify false} ParentNotChild1(node: TNode, sk: tree<TNode>)
    requires ValidRec(node, sk)
    ensures node != node.left
    ensures node != node.right
  {}

  static lemma {:verify false} ParentNotChild2(node: TNode, sk: tree<TNode>)
    requires ValidRec(node, sk)
    ensures node != node.left
    ensures node.left != null ==> node != node.left.left
    ensures node.left != null ==> node != node.left.right
    ensures node != node.right
    ensures node.right != null ==> node != node.right.left
    ensures node.right != null ==> node != node.right.right
  {}

  static lemma {:verify false} UncleNotNephew(node: TNode, sk: tree<TNode>)
    requires ValidRec(node, sk)
    requires node.left != null
    requires node.right != null
    ensures node.right != node.left.left
    ensures node.right != node.left.right
    ensures node.left != node.right.left
    ensures node.left != node.right.right
  {
    assert ValidRec(node, sk);
    assert ValidRec(node.left, sk.left);
    assert ValidRec(node.left.left, sk.left.left);
    assert ValidRec(node.left.right, sk.left.right);
    assert ValidRec(node.right, sk.right);
    assert ValidRec(node.right.left, sk.right.left);
    assert ValidRec(node.right.right, sk.right.right);
  }

  static method {:verify false} MoveRedLeft(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode, ghost newSk: tree<TNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`right
    //modifies elems(sk)

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)
    requires isRed(node)
    requires isBlack(node.left)
    requires isBlack(node.right)
    requires !isRed(node.left.left)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures RedBlackTreeRec(newSk.left)
    ensures RedBlackTreeRec(newSk.right)
    ensures BlackHeight(newSk.right) == BlackHeight(newSk.left)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))
    ensures newNode.left != null && newNode.right != null
    ensures
      || isRed(newNode.left)
      || isRed(newNode.left.left)
    ensures
      || (!isRed(newNode) && isRed(newNode.left) && isRed(newNode.right) && !isRed(newNode.right.left) && !isRed(newNode.left.left))
      || (isRed(newNode) && !isRed(newNode.left) && !isRed(newNode.right) && isRed(newNode.left.left))

    //ensures MapModelRec(newSk) == old(MapModelRec(sk))
    ensures elems(newSk) == elems(sk)
    ensures size(newSk) == size(sk)
    ensures size(newSk.left) < size(sk)

    ensures forall n | n in elems(sk) ::
      n.key == old(n.key) && n.value == old(n.value)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    GFlipColors(node, sk);
    newNode := node;
    newSk := sk;
    assert RedBlackTreeRec(newSk.left);
    assert RedBlackTreeRec(newSk.right);
    if (newNode.right.left != null && newNode.right.left.color.Red?) {
      assert size(newSk.left) < size(sk);
      ghost var newSkRight;
      assert ValidRec(newNode.right.left, newSk.right.left);
      assert RedBlackTreeRec(newSk.right.right);
      assert RedBlackTreeRec(newSk.right.left);
      assert RedBlackTreeRec(newSk.right.left.left);
      assert RedBlackTreeRec(newSk.right.left.right);
      label PreRR:
      newNode.right, newSkRight := GRotateRight(newNode.right, newSk.right);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assert unchanged(elems(newSk.right.right));
      assert unchanged(elems(newSk.right.left.left));
      assert unchanged(elems(newSk.right.left.right));
      newSk := Node(newSk.left, newNode, newSkRight);
      assert size(newSk.left) < size(sk);
      assert unchanged@PreRR(elems(newSk.left));
      assert RedBlackTreeRec(newSk.left);
      assert RedBlackTreeRec(newSk.right.left);
      assert RedBlackTreeRec(newSk.right.right.left);
      assert RedBlackTreeRec(newSk.right.right.right);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      label PreRL:
      newNode, newSk := GRotateLeft(newNode, newSk);
      assert size(newSk.left) < size(sk);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assert unchanged@PreRL(elems(newSk.left.left));
      assert unchanged@PreRL(elems(newSk.left.right));
      assert unchanged@PreRL(elems(newSk.right.left));
      assert unchanged@PreRL(elems(newSk.right.right));
      assert RedBlackTreeRec(newSk.left.left);
      assert RedBlackTreeRec(newSk.left.right);
      assert RedBlackTreeRec(newSk.right.left);
      assert RedBlackTreeRec(newSk.right.right);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      label PreFlip:
      GFlipColors(newNode, newSk);
      assert size(newSk.left) < size(sk);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assert RedBlackTreeRec(newSk.left) by {
        assert unchanged@PreRL(elems(newSk.left.left));
        assert unchanged@PreRL(elems(newSk.left.right));
        assert !isRed(newNode.left.right);
        assert !isRed(newNode.left.left.left);
        assert BlackHeight(newSk.left.left) == BlackHeight(newSk.left.right);
        assert RedBlackTreeRec(newSk.left.left);
        assert RedBlackTreeRec(newSk.left.right);
      }
      assert RedBlackTreeRec(newSk.right) by {
        assert unchanged@PreRL(elems(newSk.right.left));
        assert unchanged@PreRL(elems(newSk.right.right));
        assert RedBlackTreeRec(newSk.right.left);
        assert RedBlackTreeRec(newSk.right.right);
        assert !isRed(newNode.right.right) by {
          assert newNode.right.right == old(node.right.right);
          assert ValidRec(newNode.right.right, newSk.right.right);
        }
        assert !isRed(newNode.right.left) by {
          assert newNode.right.left == old(node.right.left.right);
          assert ValidRec(newNode.right.left, newSk.right.left);
        }
        assert BlackHeight(newSk.right.left) == BlackHeight(newSk.right.right);
      }
      assert BlackHeight(newSk.left.left) == BlackHeight(newSk.left.right);
      assert BlackHeight(newSk.right.left) == BlackHeight(newSk.right.right);
      assert RedBlackTreeRec(newSk) by {
        assert RedBlackTreeRec(newSk.left);
        assert RedBlackTreeRec(newSk.right);
        assert isBlack(newNode.right);
        assert isBlack(newNode.left);
        assert BlackHeight(newSk.left) == BlackHeight(newSk.right);
      }
      assert isRed(newNode);
      assert isBlack(newNode.left);
      assert isBlack(newNode.right);
      assert isRed(newNode.left.left);
      assert ValidRec(newNode, newSk);
      assert SearchTreeRec(newSk);
      assert elems(newSk) == elems(sk);
      assert size(newSk) == size(sk);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assert size(newSk.left) < size(sk);
    } else {
      assert ValidRec(newNode.left.left, newSk.left.left);
      assert !isRed(newNode) && isRed(newNode.left) && isRed(newNode.right) && !isRed(newNode.right.left) && !isRed(newNode.left.left);
    }
  }

  static method {:verify false} MoveRedRight(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`right

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)
    requires isRed(node)
    requires isBlack(node.left)
    requires isBlack(node.right)
    requires !isRed(node.right.left)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures
      || newNode.right == null
      || newNode.right.color.Red?
      || (newNode.right.left != null && newNode.right.left.color.Red?)
    ensures RedBlackTreeRec(newSk.left)  // TODO
    ensures RedBlackTreeRec(newSk.right)  // TODO
    ensures BlackHeight(newSk.right) == BlackHeight(newSk.left)  // TODO
    ensures BlackHeight(newSk) == old(BlackHeight(sk))  // TODO
    ensures newNode.left != null && newNode.right != null  // TODO
    ensures
      || isRed(newNode.left)
      || isRed(newNode.left.left)
    ensures  // TODO
      || (!isRed(newNode) && isRed(newNode.left) && isRed(newNode.right) && !isRed(newNode.left.left) && !isRed(newNode.right.left) && !isRed(newNode.right.right))
      || (isRed(newNode) && !isRed(newNode.left) && !isRed(newNode.right) && isRed(newNode.right.right))

    //ensures MapModelRec(newSk) == old(MapModelRec(sk))
    ensures elems(newSk) == elems(sk)
    ensures size(newSk) == size(sk)
    ensures size(newSk.right) < size(sk)
    ensures forall n | n in elems(newSk) ::
      n.key == old(n.key) && n.value == old(n.value)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    GFlipColors(node, sk);
    newNode := node;
    newSk := sk;
    if (newNode.left.left != null && newNode.left.left.color.Red?) {
      newNode, newSk := GRotateRight(newNode, newSk);
      GFlipColors(newNode, newSk);
      ghost var newSkRight;
      newNode.right, newSkRight := GRotateLeft(newNode.right, newSk.right);
      newSk := Node(newSk.left, newNode, newSkRight);
      /*
      assert RestorePre(newNode, newSk) by {
        assume false;
      }
      */
    } else {
      assert ValidRec(newNode.left.left, newSk.left.left);
    }
  }

  static function method isRed(node: TNode?): bool
    reads node
  {
    node != null && node.color.Red?
  }

  static function method isBlack(node: TNode?): bool
    reads node
  {
    node != null && node.color.Black?
  }

  static method {:verify false} RBRestore(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires
    || (
        && isBlack(node)
        && isRed(node.left)
        && isRed(node.right)
        && isRed(node.right.left)
      )
      || !(
        && isRed(node.right)
        && isRed(node.right.left)
      )
    requires !(
      && isRed(node)
      && isRed(node.left)
      && isRed(node.right)
    )
    requires !(
      && isRed(node)
      && isRed(node.left)
      && isRed(node.left.left)
    )
    requires BlackHeight(sk.left) == BlackHeight(sk.right)
    requires RedBlackTreeRec(sk.left)
    requires RedBlackTreeRec(sk.right)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures RedBlackTreeRec(newSk)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))
    ensures old(isBlack(node)) && isRed(newNode) ==>
      !isRed(newNode.left)
    //ensures MapModelRec(newSk) == old(MapModelRec(sk))
    ensures elems(newSk) == elems(sk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    newNode := node;
    newSk := sk;

    assert !(
      && isRed(newNode)
      && isRed(newNode.left)
      && isRed(newNode.right));

    if newNode.right != null && newNode.right.right != null {
      assert ValidRec(newNode.right.right, newSk.right.right);
      assert RedBlackTreeRec(newSk.right);
      assert RedBlackTreeRec(newSk.right.right);
      assert newNode.right.right.color.Black?;
    }

    if newNode.left!= null && newNode.left.right != null {
      assert ValidRec(newNode.left.right, newSk.left.right);
      assert RedBlackTreeRec(newSk.left);
      assert RedBlackTreeRec(newSk.left.right);
      assert newNode.left.right.color.Black?;
    }

    assert RedBlackTreeRec(newSk.left);

    label A:
    if isRed(newNode.right) {
      assert newNode.right.left != newNode by {
        ParentNotChild2(newNode, newSk);
      }
      assert newNode.right.left != newNode.right by {
        ParentNotChild1(newNode.right, newSk.right);
      }
      newNode, newSk := GRotateLeft(newNode, newSk);
      assert !(
        && isRed(newNode)
        && isRed(newNode.left)
        && isRed(newNode.left.left));
      assert RedBlackTreeRec(newSk.right);
      assert newNode.left.right == old(node.right.left);
      assert newNode.left.right != null ==>
        newNode.left.right.color == old(node.right.left.color);
      assert !isRed(newNode.left.right) || old(
        && isBlack(node)
        && isRed(node.left)
        && isRed(node.right)
        && isRed(node.right.left)
      );
    } else {
      assert RedBlackTreeRec(newSk.left);
      assert RedBlackTreeRec(newSk.right);
    }

    if newNode.left != null {
      assert !isRed(newNode.left.right) || old(
        && isBlack(node)
        && isRed(node.left)
        && isRed(node.right)
        && isRed(node.right.left)
      );
    }

    assert !(
      && isRed(newNode)
      && isRed(newNode.left)
      && isRed(newNode.right));

    assert !isRed(newNode.right);
    assert RedBlackTreeRec(newSk.right);
    if newNode.left != null {
      assert RedBlackTreeRec(newSk.left.left);
      assert RedBlackTreeRec(newSk.left.right);
    }


    label B:
    if isRed(newNode.left) && isRed(newNode.left.left) {
      newNode, newSk := GRotateRight(newNode, newSk);
      assert isRed(newNode.left);
      assert isRed(newNode.right);
      assert !isRed(newNode);
      assert RedBlackTreeRec(newSk.right);
      assert RedBlackTreeRec(newSk.left);
    } else {
      assert RedBlackTreeRec(newSk.right);
      if newNode.left != null {
        assert RedBlackTreeRec(newSk.left.left);
        assert RedBlackTreeRec(newSk.left.right);
        assert BlackHeight(newSk.left.left) == BlackHeight(newSk.left.right);
        assert (newSk.left.left.Node? && newSk.left.left.data.color.Red? && newSk.left.left.left.Node? ==> newSk.left.left.left.data.color.Black?);
        assert (newSk.left.right.Node? ==> newSk.left.right.data.color.Black?) by {
          assert ValidRec(newNode.left, newSk.left);
          assert ValidRec(newNode.left.right, newSk.left.right);
          if newSk.left.right.Node? {
            assert newSk.left.right.data == newNode.left.right;
            assert !isRed(newNode.left.right);
          }
        }
      }
    }

    assert RedBlackTreeRec(newSk.right);
    assert RedBlackTreeRec(newSk.left);

    label C:
    if isRed(newNode.left) && isRed(newNode.right) {
      GFlipColors(newNode, newSk);
    }

    assert ValidRec(newNode, newSk);
    assert SearchTreeRec(newSk);
    assert BlackHeight(newSk) == old(BlackHeight(sk));
    assert RedBlackTreeRec(newSk) by {
      assert newSk.right.Node? ==> newSk.right.data.color.Black? by {
        assert !isRed(newNode.right);
      }
      assert newSk.left.Node? && newSk.left.data.color.Red? && newSk.left.left.Node?
          ==> newSk.left.left.data.color.Black? by {
        if newNode.left != null {
          assert ValidRec(newNode.left, newSk.left);
          assert ValidRec(newNode.left.left, newSk.left.left);
          assert !(isRed(newNode.left) && isRed(newNode.left.left));
        }
      }
      assert BlackHeight(newSk.left) == BlackHeight(newSk.right);
      assert RedBlackTreeRec(newSk.left);
      assert RedBlackTreeRec(newSk.right);
    }
  }

  static method {:verify false} RBRemoveMinRec(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode?, ghost newSk: tree<TNode>, removedNode: TNode)
    decreases size(sk)
    modifies elems(sk)
    //modifies set n | n in elems(sk) :: n`color
    //modifies set n | n in elems(sk) :: n`left
    //modifies set n | n in elems(sk) :: n`right

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)
    requires !(isRed(node) && isRed(node.left))
    requires isRed(node) || isRed(node.left)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures RedBlackTreeRec(newSk)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))
    //ensures old(node.color).Black? && newNode.color.Red? ==>
      //newNode.left == null || newNode.left.color.Black?
    ensures old(isBlack(node)) && isRed(newNode) ==> !isRed(newNode.left)

    ensures removedNode in elems(sk)
    ensures removedNode !in elems(newSk)
    ensures removedNode.key == old(removedNode.key)
    ensures removedNode.value == old(removedNode.value)
    ensures elems(newSk) == elems(sk) - {removedNode}

    //ensures removedNode.key in old(MapModelRec(sk))
    //ensures old(MapModelRec(sk))[removedNode.key] == removedNode.value
    //ensures MapModelRec(newSk) == old(MapModelRec(sk)) - {removedNode.key}

    ensures forall n | n in elems(sk) ::
      n.key == old(n.key) && n.value == old(n.value)
    ensures forall n | n in elems(newSk) ::
      removedNode.key < n.key

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node.left == null {
      newNode := node.right;
      newSk := sk.right;
      removedNode := node;
    } else {
      newNode := node;
      newSk := sk;
      if newNode.left != null && newNode.left.color.Black?
          && (newNode.left.left == null || newNode.left.left.color.Black?) {
        newNode, newSk := MoveRedLeft(newNode, newSk);
      } else {
        assert !(isRed(newNode.left) && isRed(newNode.left.left)) by {
          assert ValidRec(newNode.left.left, newSk.left.left);
        }
      }
      var newNodeLeft;
      ghost var newSkLeft;
      label PreRec:
      newNodeLeft, newSkLeft, removedNode := RBRemoveMinRec(newNode.left, newSk.left);
      assert unchanged@PreRec(elems(newSk.right));
      assert ValidRec(newNode.right, newSk.right);
      assert SearchTreeRec(newSk.right);
      assert RedBlackTreeRec(newSk.right);
      newNode.left := newNodeLeft;
      newSk := Node(newSkLeft, newNode, newSk.right);
      assert !(
        && isRed(newNode.right)
        && isRed(newNode.right.left)
      ) by {
        if newNode.right != null && newNode.right.left != null {
          assert ValidRec(newNode.right.left, newSk.right.left);
        }
      }
      assert !(
        && isRed(newNode)
        && isRed(newNode.left)
        && isRed(newNode.left.left)
      ) by {
        if newNode.left != null && newNode.left.left != null {
          assert ValidRec(newNode.left.left, newSk.left.left);
        }
      }
      newNode, newSk := RBRestore(newNode, newSk);
    }
  }

  static method {:verify false} RBRemoveRec(node: TNode?, ghost sk: tree<TNode>, k: K)
      returns (newNode: TNode?, ghost newSk: tree<TNode>, ghost removedNode: TNode?)
    decreases size(sk)
    //modifies set x | x in elems(sk) :: x`color
    //modifies set x | x in elems(sk) :: x`left
    //modifies set x | x in elems(sk) :: x`right
    modifies elems(sk)

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)
    requires
      || node == null
      || isRed(node)
      || isRed(node.left)
    requires !(isRed(node) && isRed(node.left))

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures RedBlackTreeRec(newSk)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))
    ensures old(isBlack(node)) && isRed(newNode) ==>
      !isRed(newNode.left)

    ensures forall n | n in elems(sk) ::
      n.key == old(n.key) && n.value == old(n.value)
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures removedNode != null ==>
      && removedNode in elems(sk)
      && removedNode !in elems(newSk)
      && removedNode.key == k
    //ensures k !in old(MapModelRec(sk)) <==> removedNode==null
    //ensures MapModelRec(newSk)==old(MapModelRec(sk))-{k}

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      newNode := node;
      newSk := sk;
      removedNode := null;
    } else {
      if node.key > k {
        //assume false;
        newNode := node;
        newSk := sk;
        if isBlack(newNode.left) && !isRed(newNode.left.left) {
          newNode, newSk := MoveRedLeft(newNode, newSk);
        } else {
          assert !(isRed(newNode.left) && isRed(newNode.left.left)) by {
            assert RedBlackTreeRec(newSk);
            if newNode.left != null {
              assert ValidRec(newNode.left.left, newSk.left.left);
            }
          }
        }
        ghost var newSkLeft;
        label PreRec:
        newNode.left, newSkLeft, removedNode := RBRemoveRec(newNode.left, newSk.left, k);
        newSk := Node(newSkLeft, newNode, newSk.right);
        //assume false;
        assert ValidRec(newNode, newSk);
        assert !(
          && isRed(newNode.right)
          && isRed(newNode.right.left)
        ) by {
          assert ValidRec(newNode.right, newSk.right);
          if newNode.right != null {
            assert ValidRec(newNode.right.left, newSk.right.left);
          }
        }
        assert !(
          && isRed(newNode)
          && isRed(newNode.left)
          && isRed(newNode.right)
        );
        assert !(
          && isRed(newNode)
          && isRed(newNode.left)
          && isRed(newNode.left.left)
        ) by {
          assert ValidRec(newNode.left, newSk.left);
          if newNode.left != null {
            assert ValidRec(newNode.left.left, newSk.left.left);
          }
        }
        assert BlackHeight(newSk.left) == BlackHeight(newSk.right);
        assert RedBlackTreeRec(newSk.left);
        assert RedBlackTreeRec(newSk.right);
      } else {
        newNode := node;
        newSk := sk;

        if isRed(newNode.left) {
          assert ValidRec(newNode.left.right, newSk.left.right);
          newNode, newSk := GRotateRight(newNode, newSk);
          assert isRed(newNode.right) || isRed(newNode.right.left);
          assert !(isRed(newNode.right) && isRed(newNode.right.left));
        }

        if k == newNode.key && newNode.right == null {
          label A:
          assert elems(sk) == elems(newSk) == elems(newSk.left) + {newNode};
          assert elems(sk) - {newNode} == elems(newSk) - {newNode} == elems(newSk.left);
          newNode := newNode.left;
          newSk := newSk.left;
          removedNode := newNode;
          assume elems(newSk) == elems(sk) - {removedNode};
          assert elems(newSk) == old@A(elems(newSk) - {newNode}) == old@A(elems(sk)) - {removedNode};
          return;
        }

        if isBlack(newNode.right) && !isRed(newNode.right.left) {
          newNode, newSk := MoveRedRight(newNode, newSk);
          assert !(isRed(newNode.right) && isRed(newNode.right.left));
        } else {
          assert
            || newNode.right == null
            || isRed(newNode.right)
            || isRed(newNode.right.left);
          assert !(isRed(newNode.right) && isRed(newNode.right.left));
        }
        assert !(isRed(newNode.right) && isRed(newNode.right.left));
        if k == newNode.key {
          //assume false;
          label PreRec:
          ghost var newSkRight;
          newNode.right, newSkRight, removedNode := RBRemoveRec(newNode.right, newSk.right, k);
          newSk := Node(newSk.left, newNode, newSkRight);
          assert BlackHeight(newSk.left) == BlackHeight(newSk.right);
          assert RedBlackTreeRec(newSk.right);
          assert unchanged@PreRec(elems(newSk.left));
          assert RedBlackTreeRec(newSk.left);
          assert ValidRec(newNode, newSk);
          assert || (
              && isBlack(newNode)
              && isRed(newNode.left)
              && isRed(newNode.right)
              && isRed(newNode.right.left)
          ) || !(
              && isRed(newNode.right)
              && isRed(newNode.right.left)
          ) by {
            if isRed(newNode.right) {
              if old@PreRec(isBlack(newNode.right)) {
                assert !isRed(newNode.right.left);
                assert !(
                  && isRed(newNode.right)
                  && isRed(newNode.right.left)
                );
              } else if isRed(newNode.right.left) && old@PreRec(newNode.right != null) {
                assert isBlack(newNode);
                assert isRed(newNode.left);
                assert isRed(newNode.right);
                assert isRed(newNode.right.left);
              }
            }
            /*
            if old@PreRec(isBlack(newNode.right)) && isRed(newNode.right) {
              assert !isRed(newNode.right.left);
              assert !(
                && isRed(newNode.right)
                && isRed(newNode.right.left)
              );
            } else if !isRed(newNode.right) {
              assert !(
                && isRed(newNode.right)
                && isRed(newNode.right.left)
              );
            } else if old@PreRec(newNode.right == null) {
              assert !(
                && isRed(newNode.right)
                && isRed(newNode.right.left)
              );
            } else if isRed(newNode.right.left) {
              assert old@PreRec(isRed(newNode.right)) && isRed(newNode.right);
              //assert isRed(newNode.left);
              assert isBlack(newNode);
              assert isRed(newNode.left);
              assert isRed(newNode.right);
              assert isRed(newNode.right.left);
            } else {
            }
            */
          }
          assert !(
            && isRed(newNode)
            && isRed(newNode.left)
            && isRed(newNode.right)
          );
          assert !(
            && isRed(newNode)
            && isRed(newNode.left)
            && isRed(newNode.left.left)
          ) by {
            assert ValidRec(newNode.left, newSk.left);
            if newNode.left != null {
              assert ValidRec(newNode.left.left, newSk.left.left);
            }
          }
        } else {
          //assume false;
          if newNode.right == null {
            assume false;
            return;
          }
          removedNode := newNode;
          ghost var oldNewSkLeft := newSk.left;
          var oldNewNodeLeft := newNode.left;
          var oldNewNodeColor := newNode.color;
          assert RedBlackTreeRec(newSk.left);
          assert !(
            && isRed(newNode)
            && isRed(newNode.left)
          );
          label PreRec:
          ghost var newSkRight;
          var newNodeRight;
          var minNode;
          newNodeRight, newSkRight, minNode := RBRemoveMinRec(newNode.right, newSk.right);
          /*
          label PostRec:
          assert old@PreRec(isBlack(newNode.right)) && isRed(newNodeRight)
            ==> !isRed(newNodeRight.left);
          assert newNode !in elems(newSkRight);
          assert newNode != newNodeRight;
          assert newNodeRight != null ==> newNode != newNodeRight.left;
          assert minNode !in elems(newSkRight);
          assert minNode != newNodeRight;
          assert newNodeRight != null ==> minNode != newNodeRight.left;
          */
          newNode := minNode;
          /*
          // Somehow Dafny cannot prove the following:
          assume old@PreRec(isBlack(newNode.right)) && old@PostRec(isRed(newNodeRight))
            ==> old@PostRec(!isRed(newNodeRight.left));
          assert old@PreRec(isBlack(newNode.right)) && isRed(newNodeRight)
            ==> !isRed(newNodeRight.left);
          */
          /*
          assert isRed(newNodeRight) <==> old@PostRec(isRed(newNodeRight));
          if newNodeRight != null {
            assert unchanged@PostRec(newNodeRight);
            assert old@PostRec(newNodeRight.color) == newNodeRight.color;
            assert isRed(newNodeRight.left) <==> old@PostRec(isRed(newNodeRight.left));
            if newNodeRight.left != null {
              assert unchanged@PostRec(newNodeRight.left);
            }
          }
          */
          newNode.left := oldNewNodeLeft;
          newNode.right := newNodeRight;
          newNode.color := oldNewNodeColor;
          ghost var goodSk := Node(oldNewSkLeft, newNode, newSkRight);
          newSk := goodSk;
          //newSk := Node(oldNewSkLeft, newNode, newSkRight);
          assert || (
              && isBlack(newNode)
              && isRed(newNode.left)
              && isRed(newNode.right)
              && isRed(newNode.right.left)
          ) || !(
              && isRed(newNode.right)
              && isRed(newNode.right.left)
          ) by {
            assume false;
            /*
            assert old@PreRec(isBlack(newNode.right)) && isRed(newNode.right)
              ==> !isRed(newNode.right.left);
            if old@PreRec(isBlack(newNode.right)) && isRed(newNode.right) {
              assert !isRed(newNode.right.left);
              assert !(
                && isRed(newNode.right)
                && isRed(newNode.right.left)
              );
            } else if !isRed(newNode.right) {
              assert !(
                && isRed(newNode.right)
                && isRed(newNode.right.left)
              );
            } else if old@PreRec(newNode.right == null) {
              // The proof would be something like this but Dafny cannot even
              // prove that newNode.right was valid before the call.
              /*
              assert isRed(newNode.right);
              assert newNode.right != null;
              assert old@PreRec(ValidRec(newNode.right, newSk.right));
              assert old@PreRec(newSk.right.Empty?);
              assert old@PreRec(elems(newSk.right)) == {};
              assert elems(newSk.right) <= old@PreRec(elems(newSk.right));
              assert elems(newSk.right) == {};
              assert newNode.right in elems(newSk.right);
              assert newNode.right in {};
              assert false;
              */
              assume false;
            } else if isRed(newNode.right.left) {
              assert old@PreRec(isRed(newNode.right)) && isRed(newNode.right);
              //assert isRed(newNode.left);
              assert isBlack(newNode);
              assert isRed(newNode.right);
              assume false;
              assert isRed(newNode.left);
              assert isRed(newNode.right.left);
            } else {
              assume false;
            }
            */
          }
          assert unchanged@PreRec(elems(newSk.left));
          assert newNode.left != null ==> unchanged@PreRec(newNode.left);
          assert !(
            && isRed(newNode)
            && isRed(newNode.left)
            && isRed(newNode.left.left)
          ) by {
            assert ValidRec(newNode.left, newSk.left);
            if newNode.left != null {
              assert ValidRec(newNode.left.left, newSk.left.left);
            }
          }
          assert !(
            && isRed(newNode)
            && isRed(newNode.left)
            && isRed(newNode.right)
          );
          assert RedBlackTreeRec(newSk.right);
          assert RedBlackTreeRec(newSk.left);
          assert BlackHeight(newSk.left) == BlackHeight(newSk.right);
          assert ValidRec(newNode, newSk);
          assert SearchTreeRec(newSk);
          assert forall n | n in elems(sk) ::
            n.key == old(n.key) && n.value == old(n.value);
          assert elems(newSk) == elems(sk) - {removedNode};
          assert removedNode != null ==>
            && removedNode in elems(sk)
            && removedNode !in elems(newSk)
            && removedNode.key == k by {
            assume false;
          }
        }
        /*
        assume false;
        assert ValidRec(newNode, newSk);
        assert !(
          && isRed(newNode)
          && isRed(newNode.left)
          && isRed(newNode.right)
        );
        */
      }

      assert || (
          && isBlack(newNode)
          && isRed(newNode.left)
          && isRed(newNode.right)
          && isRed(newNode.right.left)
      ) || !(
          && isRed(newNode.right)
          && isRed(newNode.right.left)
      );
      assert !(
        && isRed(newNode)
        && isRed(newNode.left)
        && isRed(newNode.right)
      );
      assert !(
        && isRed(newNode)
        && isRed(newNode.left)
        && isRed(newNode.left.left)
      );
      assert BlackHeight(newSk.left) == BlackHeight(newSk.right);
      assert RedBlackTreeRec(newSk.left);
      assert RedBlackTreeRec(newSk.right);
      assert ValidRec(newNode, newSk);
      assert SearchTreeRec(newSk);
      newNode, newSk := RBRestore(newNode, newSk);
/*
      assert ValidRec(node, newSk);
      assert SearchTreeRec(newSk);
      assume forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assume elems(newSk) == elems(sk) - {removedNode};
      assume removedNode != null ==>
        && removedNode in elems(sk)
        && removedNode !in elems(newSk)
        && removedNode.key == k;
*/
    }
    assert BlackHeight(newSk) == old(BlackHeight(sk));
    assert RedBlackTreeRec(newSk);
    assert old(isBlack(node)) && isRed(newNode) ==>
      !isRed(newNode.left);
  }

  method {:verify false} Remove(k: K)
    modifies this, Repr()
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    ensures MapModel()==old(MapModel())-{k}

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    ghost var removedNode;
    root, skeleton, removedNode := RemoveRec(root, skeleton, k);
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
        && (r.Node? ==> r.data.color.Black?)
        // No node has two red links connected to it:
        && (l.Node? && l.data.color.Red? && l.left.Node? ==> l.left.data.color.Black?)
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

  static predicate IsMaybeRed(node: TNode?)
    reads node
  {
    node != null ==> node.color.Red?
  }
  static predicate IsMaybeBlack(node: TNode?)
    reads node
  {
    node != null ==> node.color.Black?
  }

  static method {:verify false} RotateLeft(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`right
    modifies node.right`left
    modifies node.right`color

    requires ValidRec(node, sk)
    requires node.right != null
    requires node.right.color.Red?
    requires node.left != null ==> node.left.color.Black?
    requires node.right.left != null ==> node.right.left.color.Black?
    requires node.right.right != null ==> node.right.right.color.Black?
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk.left)
    requires RedBlackTreeRec(sk.right)
    requires BlackHeight(sk.left) == BlackHeight(sk.right)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))
    ensures newNode.color == old(node.color)
    ensures newNode.left != null
    ensures newNode.left.color.Red?
    ensures newNode.right != null ==> newNode.right.color.Black?
    ensures newNode.left.left != null ==> newNode.left.left.color.Black?
    ensures newNode.left.right != null ==> newNode.left.right.color.Black?
    ensures RedBlackTreeRec(newSk.left)
    ensures RedBlackTreeRec(newSk.right)
    ensures RedBlackTreeRec(newSk)

    ensures MapModelRec(newSk) == old(MapModelRec(sk))
    ensures elems(newSk) == elems(sk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    newNode := node.right;
    node.right := newNode.left;
    newNode.left := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := Node(Node(sk.left, node, sk.right.left), newNode, sk.right.right);
    if newNode.right != null {
      assert ValidRec(newNode.right, newSk.right);
    }
    if newNode.left.left != null {
      assert ValidRec(newNode.left.left, newSk.left.left);
    }
    if newNode.left.right != null {
      assert ValidRec(newNode.left.right, newSk.left.right);
    }
    assert MapModelRec(newSk) == old(MapModelRec(sk)) by {
      reveal MapModelRec();
      calc == {
        MapModelRec(newSk);
        MapModelRec(newSk.left) + MapModelRec(newSk.right)[newNode.key := newNode.value];
        MapModelRec(Node(sk.left, node, sk.right.left)) + MapModelRec(sk.right.right)[newNode.key := newNode.value];
        (MapModelRec(sk.left) + MapModelRec(sk.right.left))[node.key := node.value] + MapModelRec(sk.right.right)[newNode.key := newNode.value];
        (MapModelRec(sk.left) + MapModelRec(sk.right.left)) + map[node.key := node.value] + MapModelRec(sk.right.right) + map[newNode.key := newNode.value];
        {
          assert node.key !in MapModelRec(sk.right.right) by {
            MapModelLemmas(newNode, newSk);
          }
        }
        (MapModelRec(sk.left) + MapModelRec(sk.right.left)) + MapModelRec(sk.right.right) + map[node.key := node.value] + map[newNode.key := newNode.value];
        MapModelRec(sk.left) + (MapModelRec(sk.right.left) + MapModelRec(sk.right.right)) + map[node.key := node.value] + map[newNode.key := newNode.value];
        (MapModelRec(sk.left) + (MapModelRec(sk.right.left) + MapModelRec(sk.right.right))[newNode.key := newNode.value])[node.key := node.value];
        (MapModelRec(sk.left) + (MapModelRec(sk.right.left) + MapModelRec(sk.right.right))[old(node.right.key) := old(node.right.value)])[node.key := node.value];
        old((MapModelRec(sk.left) + (MapModelRec(sk.right.left) + MapModelRec(sk.right.right))[node.right.key := node.right.value])[node.key := node.value]);
        old((MapModelRec(sk.left) + MapModelRec(sk.right))[node.key := node.value]);
        old(MapModelRec(sk));
      }
    }
  }

  static method {:verify false} RotateRight(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`left
    modifies node.left`right
    modifies node.left`color

    requires ValidRec(node, sk)
    requires node.color.Black?
    requires node.left != null
    requires node.left.color.Red?
    requires node.left.left != null
    requires node.left.left.color.Red?
    requires node.left.left.left != null ==> node.left.left.left.color.Black?
    requires node.left.left.right != null ==> node.left.left.right.color.Black?
    requires node.left.right != null ==> node.left.right.color.Black?
    requires node.right != null ==> node.right.color.Black?
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk.left)
    requires RedBlackTreeRec(sk.right)
    requires BlackHeight(sk.left) == BlackHeight(sk.right)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures BlackHeight(newSk.left) == BlackHeight(newSk.right)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))
    ensures RedBlackTreeRec(newSk.left)
    ensures RedBlackTreeRec(newSk.right)
    ensures newNode.color.Black?
    ensures newNode.left != null
    ensures newNode.left.color.Red?
    ensures newNode.left.left != null ==> newNode.left.left.color.Black?
    ensures newNode.left.right != null ==> newNode.left.right.color.Black?
    ensures newNode.right != null
    ensures newNode.right.color.Red?
    ensures newNode.right.left != null ==> newNode.right.left.color.Black?
    ensures newNode.right.right != null ==> newNode.right.right.color.Black?

    ensures MapModelRec(newSk) == old(MapModelRec(sk))
    ensures elems(newSk) == elems(sk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    newNode := node.left;
    node.left := newNode.right;
    newNode.right := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := Node(sk.left.left, newNode, Node(sk.left.right, node, sk.right));
    assert ValidRec(newNode.left, newSk.left);
    if newNode.left.left != null {
      assert ValidRec(newNode.left.left, newSk.left.left);
    }
    if newNode.left.right != null {
      assert ValidRec(newNode.left.right, newSk.left.right);
    }
    if newNode.right.left != null {
      assert ValidRec(newNode.right.left, newSk.right.left);
    }
    if newNode.right.right != null {
      assert ValidRec(newNode.right.right, newSk.right.right);
    }
    assert MapModelRec(newSk) == old(MapModelRec(sk)) by {
      reveal MapModelRec();
      calc == {
        MapModelRec(newSk);
        MapModelRec(newSk.left) + MapModelRec(newSk.right)[newNode.key := newNode.value];
        MapModelRec(sk.left.left) + MapModelRec(Node(sk.left.right, node, sk.right)) + map[newNode.key := newNode.value];
        MapModelRec(sk.left.left) + MapModelRec(sk.left.right) + MapModelRec(sk.right) + map[node.key := node.value] + map[newNode.key := newNode.value];
        MapModelRec(sk.left.left) + MapModelRec(sk.left.right) + MapModelRec(sk.right) + map[newNode.key := newNode.value] + map[node.key := node.value];
        {
          assert newNode.key !in MapModelRec(sk.right) by {
            MapModelLemmas(newNode, newSk);
          }
        }
        MapModelRec(sk.left.left) + MapModelRec(sk.left.right) + map[newNode.key := newNode.value] + MapModelRec(sk.right) + map[node.key := node.value];
        old(MapModelRec(sk.left.left) + MapModelRec(sk.left.right) + map[node.left.key := node.left.value] + MapModelRec(sk.right) + map[node.key := node.value]);
        old(MapModelRec(sk.left) + MapModelRec(sk.right) + map[node.key := node.value]);
        old(MapModelRec(sk));
      }
    }
  }

  static method {:verify false} FlipColors(node: TNode, ghost sk: tree<TNode>)
    modifies node`color, node.left`color, node.right`color
    requires ValidRec(node, sk)
    requires node.color.Black?
    requires node.left != null
    requires node.left.color.Red?
    requires node.left.left != null ==> node.left.left.color.Black?
    requires node.left.right != null ==> node.left.right.color.Black?
    requires node.right != null
    requires node.right.color.Red?
    requires node.right.left != null ==> node.right.left.color.Black?
    requires node.right.right != null ==> node.right.right.color.Black?
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk.left)
    requires RedBlackTreeRec(sk.right)
    requires BlackHeight(sk.left) == BlackHeight(sk.right)

    ensures node.color.Red?
    ensures node.left != null
    ensures node.left.color.Black?
    ensures node.left.left != null ==> node.left.left.color.Black?
    ensures node.left.right != null ==> node.left.right.color.Black?
    ensures node.right != null
    ensures node.right.color.Black?
    ensures node.right.left != null ==> node.right.left.color.Black?
    ensures node.right.right != null ==> node.right.right.color.Black?
    ensures ValidRec(node, sk)
    ensures SearchTreeRec(sk)
    ensures BlackHeight(sk) == old(BlackHeight(sk))
    ensures RedBlackTreeRec(sk)

    ensures MapModelRec(sk) == old(MapModelRec(sk))

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    assert node.left.left != null ==> node.left.left.color.Black?;
    node.color := Red;
    node.left.color := Black;
    node.right.color := Black;
    if node.left.left != null {
      assert ValidRec(node.left.left, sk.left.left);
    }
    if node.left.right != null {
      assert ValidRec(node.left.right, sk.left.right);
    }
    if node.right.left != null {
      assert ValidRec(node.right.left, sk.right.left);
    }
    if node.right.right != null {
      assert ValidRec(node.right.right, sk.right.right);
    }
  }

  static method {:verify false} RestoreInsert(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk.left)
    requires RedBlackTreeRec(sk.right)
    requires BlackHeight(sk.left) == BlackHeight(sk.right)
    requires !(node.right != null && node.right.color.Red? && node.right.left != null && node.right.left.color.Red?)
    requires node.left != null && node.left.color.Red? && node.right != null && node.right.color.Red? ==>
      node.color.Black? && (node.left.left == null || node.left.left.color.Black?)
    requires node.left != null && node.left.color.Red? && node.left.left != null && node.left.left.color.Red? ==>
      node.color.Black?

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures RedBlackTreeRec(newSk)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))
    ensures old(node.color).Black? && newNode.color.Red? ==> newNode.left == null || newNode.left.color.Black?
    ensures MapModelRec(newSk) == old(MapModelRec(sk))
    ensures elems(newSk) == elems(sk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node.left == null || node.left.color.Black? {
      if node.right != null && node.right.color.Red? {
        assert node.right.left != null ==> node.right.left.color.Black?;

        if sk.right.right.Node? {
          assert sk.right.right.data.color.Black?;
          assert ValidRec(node.right.right, sk.right.right);
          assert sk.right.right.data == node.right.right;
        }
        if node.right.right != null {
          assert ValidRec(node.right.right, sk.right.right);
        }
        assert node.right.right != null ==> node.right.right.color.Black?;

        newNode, newSk := RotateLeft(node, sk);
      } else {
        assert RedBlackTreeRec(sk);
        newNode := node;
        newSk := sk;
      }
    } else {
      assert node.left != null;
      assert node.left.color.Red?;
      if node.right != null && node.right.color.Red? {
        assert node.left.color.Red?;
        assert node.right.color.Red?;
        assert node.color.Black?;

        if node.left.left != null {
          assert ValidRec(node.left.left, sk.left.left);
        }
        if node.left.right != null {
          assert ValidRec(node.left.right, sk.left.right);
        }
        if node.right.left != null {
          assert ValidRec(node.right.left, sk.right.left);
        }
        if node.right.right != null {
          assert ValidRec(node.right.right, sk.right.right);
        }

        FlipColors(node, sk);
        newNode := node;
        newSk := sk;
      } else {
        assert node.right == null || node.right.color.Black?;
        if node.left.left != null && node.left.left.color.Red? {
          assert node.color.Black?;
          if node.left.left != null {
            assert ValidRec(node.left.left, sk.left.left);
          }
          if node.left.right != null {
            assert ValidRec(node.left.right, sk.left.right);
          }
          if node.left.left.left != null {
            assert ValidRec(node.left.left.left, sk.left.left.left);
          }
          if node.left.left.right != null {
            assert ValidRec(node.left.left.right, sk.left.left.right);
          }
          newNode, newSk := RotateRight(node, sk);
          FlipColors(newNode, newSk);
        } else {
          if sk.left.left.Node? {
            assert ValidRec(node.left.left, sk.left.left);
            assert sk.left.left.data == node.left.left;
          }

          assert RedBlackTreeRec(sk);
          newNode := node;
          newSk := sk;
        }
      }
    }
  }

  static method {:verify false} RBInsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V)
    returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode:TNode)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)

    /*
      La siguiente precondición es para el FlipColor.

      Si el nodo era rojo, con esta precondición garantizamos
      que el nodo izquierdo y el derecho eran negros. De esta forma, si insertamos a la derecha o a la izquierda
      solo uno de los hijos podrá ser rojo, pero no los dos, y por tanto FlipColor no se ejecutará.

      En cambio, si el hijo izquierdo era rojo, entonces sabemos que el padre era negro, y en el caso de que el
      hijo derecho se vuelva rojo podremos ejecutar FlipColor sin problema (ya que la raíz será negra).
    */
    requires alt_rb: node != null && node.color.Red? ==> node.left == null || node.left.color.Black?

    /*
      La siguiente poscondición es para descartar el caso de tener el hijo derecho rojo y su hijo
      izquierdo (node.right.left) también rojo.
    */
    ensures old(node) != null && old(node.color).Black? && newNode.color.Red? ==>
      newNode.left == null || newNode.left.color.Black?

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures RedBlackTreeRec(newSk)
    ensures BlackHeight(newSk) == old(BlackHeight(sk))
    ensures MapModelRec(newSk) == old(MapModelRec(sk))[k := v]

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures forall n | n in elems(sk) && old(n.key) != k ::
      n.key == old(n.key) && n.value == old(n.value)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      newNode := new TNode.RedBlack(null, k, v, null, Red);
      newSk := Node(Empty, newNode, Empty);
      insertedNode := newNode;
      assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v] by {
        reveal MapModelRec();
      }
    } else {
      assert sk.data == node;
      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        insertedNode := node;
        assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v] by {
          reveal MapModelRec();
        }
      } else if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, insertedNode := RBInsertRec(node.right, sk.right, k, v);
        assert MapModelRec(newSkRight) == old(MapModelRec(sk.right))[k := v];
        newSk := Node(sk.left, node, newSkRight);
        assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v] by {
          reveal MapModelRec();
        }
      } else if k < node.key {
        ghost var oMMRight := MapModelRec(sk.right);
        ghost var oMMLeft := MapModelRec(sk.left);
        ghost var oMM := MapModelRec(sk);
        keysSearchTree(sk, k);
        ghost var newSkLeft;
        assert node.left != null && node.left.color.Red? ==> node.left.left == null || node.left.left.color.Black? by {
          if node.left != null && node.left.left != null {
            assert ValidRec(node.left.left, sk.left.left);
          }
          reveal alt_rb;
        }
        node.left, newSkLeft, insertedNode := RBInsertRec(node.left, sk.left, k, v);
        assert MapModelRec(newSkLeft) == old(MapModelRec(sk.left))[k := v];
        newSk := Node(newSkLeft, node, sk.right);

        assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v] by {
          reveal MapModelRec();
          assert node.key!=k;
          assert node.key==old(node.key) && node.value==old(node.value);
          assert node.key !in oMMLeft && node.key !in oMMRight && node.key !=k;

          assert newSk.left==newSkLeft && newSk.right==sk.right && newSk.data==node;
          assert MapModelRec(newSk.left)==oMMLeft[k:=v];
          assert MapModelRec(newSk.right)==oMMRight;
          assert oMM==(oMMLeft+oMMRight)[node.key:=node.value];
          oldNewMapModelRecL(newSk,old(MapModelRec(sk)),oMMLeft,oMMRight,node,k,v);
        }
      } else {
        assert false;
      }
    }
    assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v];

    label A:
    assert !(newNode.right != null && newNode.right.color.Red? && newNode.right.left != null && newNode.right.left.color.Red?) by {
      if newNode.right != null && newNode.right.left != null {
        assert ValidRec(newNode.right.left, newSk.right.left);
      }
    }
    assert newNode.left != null && newNode.left.color.Red? && newNode.right != null && newNode.right.color.Red? ==>
        newNode.color.Black? && (newNode.left.left == null || newNode.left.left.color.Black?) by {
      if newNode.left != null && newNode.left.left != null {
        assert ValidRec(newNode.left.left, newSk.left.left);
      }
      reveal alt_rb;
    }
    assert newNode.left != null && newNode.left.color.Red? && newNode.left.left != null && newNode.left.left.color.Red? ==> newNode.color.Black? by{
      reveal alt_rb;
    }
    var newNewNode, newNewSk := RestoreInsert(newNode, newSk);
    assert old(node) != null && old(node.color).Black? && newNewNode.color.Red? ==> newNewNode.left == null || newNewNode.left.color.Black? by{
      assert old@A(newNode.color).Black? && newNewNode.color.Red? ==> newNewNode.left == null || newNewNode.left.color.Black?;
      if old(node) != null && old(node.color).Black? {
        assert old@A(newNode.color) == old(node.color);
        assert old@A(newNode.color).Black?;
      }
    }

    newNode, newSk := newNewNode, newNewSk;
    assert MapModelRec(newSk) == old(MapModelRec(sk))[k := v];
  }
}