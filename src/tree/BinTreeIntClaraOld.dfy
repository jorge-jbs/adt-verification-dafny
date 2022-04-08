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
    ensures sk==Empty() ==> MapModelRec(sk)==map[]
    ensures sk!=Empty ==>MapModelRec(sk) == (MapModelRec(sk.left)+MapModelRec(sk.right))[sk.data.key:=sk.data.value]
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

 static lemma ModelRelationWithSkeletonKeyRec(node: TNode?, sk: tree<TNode>,k: K)
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


  function method isEmpty(): bool
    reads this, Repr()
    requires Valid()
    ensures isEmpty() <==> MapModel() == map[]
  { root==null }  

  function method Size():nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |MapModel()|
  //TO  DO:añadir tamaño

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
 
  method {:verify false} Search(k: K) returns (b:bool)
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    ensures b == (k in MapModel())

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x | x in Repr() :: allocated(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

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

  
static lemma pushUpMapModelRec(skLeft: tree<TNode>,node:TNode, skRight:tree<TNode>, k:K, v:V)
  requires  SearchTreeRec(Node(skLeft,node,skRight)) && k < node.key
  ensures (MapModelRec(skLeft)[k:=v]+MapModelRec(skRight))[node.key:=node.value]==
          MapModelRec(Node(skLeft,node,skRight))[k:=v]

static lemma  pushUpMapL(ml:map<K,V>, mr:map<K,V>, k:K, v:V)  
requires k !in mr
ensures ml[k:=v]+mr == (ml+mr)[k:=v]
{}




static lemma  pushUpMapR(ml:map<K,V>, mr:map<K,V>, k:K, v:V)  
ensures (ml+mr)[k:=v]==ml+mr[k:=v]
{}


static lemma  pushUpMapD(ml:map<K,V>, mr:map<K,V>, k:K)  
requires k !in mr
ensures ml-{k}+mr == (ml+mr)-{k}
{}

static lemma  pushUpMapDR(ml:map<K,V>, mr:map<K,V>, k:K)  
requires k !in ml
ensures ml+(mr-{k}) == (ml+mr)-{k}
{}

static lemma  deletion(m:map<K,V>, m':map<K,V>, k:K,v:V)  
requires m==m'[k:=v] && k !in m'
ensures m-{k}==m'
{}

static lemma idem(m:map<K,V>,k:K,v:V)
requires k in m && m[k]==v
ensures (m-{k})[k:=v]==m
{}

static lemma idem2(m:map<K,V>,k:K,v:V)
requires k !in m 
ensures (m[k:=v])-{k}==m
{}
static lemma keysSearchTree(sk:tree<TNode>,k:K)
requires SearchTreeRec(sk)  && sk !=Empty()
ensures (set n | n in elems(sk)::n.key) == MapModelRec(sk).Keys
ensures sk.data.key !in MapModelRec(sk.left) && sk.data.key !in MapModelRec(sk.right)
ensures MapModelRec(sk.left).Keys !! MapModelRec(sk.right).Keys 
ensures MapModelRec(sk).Keys==MapModelRec(sk.left).Keys+MapModelRec(sk.right).Keys+{sk.data.key}
ensures  k < sk.data.key ==> k !in MapModelRec(sk.right)
ensures  k > sk.data.key ==> k !in MapModelRec(sk.left)
{
}

static lemma keysSearchTreeP(sk:tree<TNode>)
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
calc =={
           MapModelRec(newSk);
           (MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];
           (mskL[k:=v]+mskR)[node.key:=node.value];
           { pushUpMapR(mskL[k:=v],mskR,node.key,node.value);}
           mskL[k:=v]+mskR[node.key:=node.value];
           {  
             assert k !in mskR[node.key:=node.value];
             pushUpMapL(mskL,mskR[node.key:=node.value],k,v);}
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
calc =={
           MapModelRec(newSk);
           (MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];
           (mskL+mskR[k:=v])[node.key:=node.value];
           {pushUpMapR(mskL[k:=v],mskR,node.key,node.value);}
           mskL+mskR[k:=v][node.key:=node.value];
           {assert k != node.key;}
           mskL+mskR[node.key:=node.value][k:=v];
           {pushUpMapR(mskL,mskR[node.key:=node.value],k,v);}
           ((mskL+mskR)[node.key:=node.value])[k:=v];
           moSk[k:=v];

}
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
    ensures MapModelRec(newSk)==old(MapModelRec(sk))[k:=v]

    ensures elems(newSk)==elems(sk)+{z}
    ensures z.key==k && z.value==v
    ensures forall n | n in elems(sk) && old(n.key)!=k :: n.key==old(n.key) && n.value==old(n.value)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(newSk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
      
    if node == null {
      newNode := new TNode(null, k, v, null);
      newSk := Node(Empty, newNode, Empty);
      z:=newNode;
    } else {
       assert sk.data==node;

      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        z:=node;
      } else if node.key < k {

       /* ghost var oMMRight:=MapModelRec(sk.right);
        ghost var oMMLeft:=MapModelRec(sk.left);
        keysSearchTree(sk,k);*/

        ghost var newSkRight;
        node.right, newSkRight, z := InsertRec(node.right, sk.right, k, v);

        newSk := Node(sk.left, node, newSkRight);

       /* assert node.key==old(node.key) && node.value==old(node.value);
        assert node.key !in oMMLeft && node.key !in oMMRight && node.key !=k;

        assert newSk.left==sk.left && newSk.right==newSkRight && newSk.data==node;
        assert MapModelRec(newSk.left)==oMMLeft;
        assert MapModelRec(newSk.right)==oMMRight[k:=v];
        oldNewMapModelRecR(newSk,old(MapModelRec(sk)),oMMLeft,oMMRight,node,k,v);*/

      } else if k < node.key {

        ghost var oMMRight:=MapModelRec(sk.right);
        ghost var oMMLeft:=MapModelRec(sk.left);
        ghost var oMM:=MapModelRec(sk);

        //assert oMMRight==old(MapModelRec(sk.right));
        //assert oMMLeft==old(MapModelRec(sk.left));
        
        keysSearchTree(sk,k);
        //assert k !in oMMRight;

        ghost var newSkLeft;
        node.left, newSkLeft,z := InsertRec(node.left, sk.left, k, v);


        newSk := Node(newSkLeft, node, sk.right);
        
        assert node.key!=k;
        assert node.key==old(node.key) && node.value==old(node.value);
        assert node.key !in oMMLeft && node.key !in oMMRight && node.key !=k;

        assert newSk.left==newSkLeft && newSk.right==sk.right && newSk.data==node;
        assert MapModelRec(newSk.left)==oMMLeft[k:=v];
        assert MapModelRec(newSk.right)==oMMRight;
        assert oMM==(oMMLeft+oMMRight)[node.key:=node.value];
        oldNewMapModelRecL(newSk,old(MapModelRec(sk)),oMMLeft,oMMRight,node,k,v);
       /*calc =={
           MapModelRec(newSk);
           (MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];
           (oMMLeft[k:=v]+oMMRight)[node.key:=node.value];
           { assert node.key !in oMMRight;
             pushUpMapR(oMMLeft[k:=v],oMMRight,node.key,node.value);}
           oMMLeft[k:=v]+oMMRight[node.key:=node.value];
           { assert k !in oMMRight[node.key:=node.value];
             pushUpMapL(oMMLeft,oMMRight[node.key:=node.value],k,v);}
           ((oMMLeft+oMMRight)[old(node.key):=old(node.value)])[k:=v];
           old(MapModelRec(sk))[k:=v];
        
        }*/

      } else {
        assert false;
      }
    }
  }
  /*static method {:verify true} InsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V) returns (newNode: TNode, ghost newSk: tree<TNode>, ghost z:TNode)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires forall x | x in elems(sk) :: allocated(x)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    //ensures MapModelRec(newSk)==old(MapModelRec(sk))[k:=v]
    //ensures MapModelRec(sk)==old(MapModelRec(sk))


    ensures elems(newSk)==elems(sk)+{z} 
    ensures z.key==k && z.value==v
    ensures forall n | n in elems(sk) && n.key!=k :: n.key==old(n.key) && n.value==old(n.value)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {


    if node == null {
      newNode := new TNode(null, k, v, null);
      newSk := Node(Empty, newNode, Empty);
      z:=newNode;
    } else {
       assert sk.data==node;

      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        z:=node;
      } else if node.key < k {

        ghost var oMMRight:=MapModelRec(sk.right);
        ghost var oMMLeft:=MapModelRec(sk.left);

        ghost var newSkRight;
        node.right, newSkRight, z := InsertRec(node.right, sk.right, k, v);
        assume MapModelRec(newSkRight)==old(MapModelRec(sk.right))[k:=v];

        newSk := Node(sk.left, node, newSkRight);

        //assume MapModelRec(newSk.left)== oMMLeft==old(MapModelRec(sk.left));   

      //  oldNewMapModelRecR(newSk,old(MapModelRec(sk)),old(MapModelRec(sk.left)),old(MapModelRec(sk.right)),node,k,v);
       // assume  MapModelRec(newSk)==old(MapModelRec(sk))[k:=v];

      } else if k < node.key {

        ghost var oMMRight:=MapModelRec(sk.right);
        ghost var oMMLeft:=MapModelRec(sk.left);

        assert k < sk.data.key;
        keysSearchTree(sk,k);
        assert k !in oMMRight;

        ghost var newSkLeft;
        node.left, newSkLeft,z := InsertRec(node.left, sk.left, k, v);
        assume MapModelRec(newSkLeft)==old(MapModelRec(sk.left))[k:=v];

        newSk := Node(newSkLeft, node, sk.right);
      
        assert old(node.key)==node.key && old(node.value)==node.value;
        assert ValidRec(node,newSk) && SearchTreeRec(newSk);
        assert newSk!=Empty;
         assert node.key !in  old(MapModelRec(sk.left)) && node.key !in old(MapModelRec(sk.right)) && node.key !=k && k !in old(MapModelRec(sk.right));
       assert old(MapModelRec(sk))==(old(MapModelRec(sk.left))+old(MapModelRec(sk.right)))[old(node.key):=old(node.value)];
       
        assert MapModelRec(newSk.left)==MapModelRec(newSkLeft)==old(MapModelRec(sk.left))[k:=v];
        assert MapModelRec(newSk.right)== MapModelRec(sk.right)==old(MapModelRec(sk.right));   
       
       oldNewMapModelRecL(newSk,old(MapModelRec(sk)),old(MapModelRec(sk.left)),old(MapModelRec(sk.right)),node,k,v);
      assert  MapModelRec(newSk)==old(MapModelRec(sk))[k:=v];

      } 
    }
  }*/





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
  calc =={
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
  calc =={
           MapModelRec(newSk);
           (MapModelRec(newSk.left)+MapModelRec(newSk.right))[node.key:=node.value];
           (mskL+(mskR-{k}))[node.key:=node.value];
           { assert k !in mskL;
             pushUpMapDR(mskL,mskR,k);}
            ((mskL+mskR)-{k})[node.key:=node.value];
           {assert node.key!=k;}
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
  calc =={
           MapModelRec(newSk);
           (MapModelRec(newSk.left)+MapModelRec(newSk.right))[newNode.key:=newNode.value];
           (mskL+(mskR-{newNode.key}))[newNode.key:=newNode.value];
           {pushUpMapR(mskL,mskR-{newNode.key},newNode.key,newNode.value);}
           mskL+(mskR-{newNode.key})[newNode.key:=newNode.value];
           {idem(mskR,newNode.key,newNode.value);}
           mskL+mskR;
           { 
             idem2(mskL+mskR,node.key,node.value);}
           ((mskL+mskR)[node.key:=node.value])-{node.key};
           moSk-{node.key};
  }
}

  static method {:verify false} RemoveMinRec(node: TNode, ghost sk: tree<TNode>) returns (newNode: TNode?, ghost newSk: tree<TNode>, removedNode: TNode)
    modifies set x | x in elems(sk) :: x`left

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    //ensures elems(sk) >= elems(newSk)
    //ensures elems(newSk) == set n | n in elems(sk) && n.key != removedNode.key :: n
    ensures removedNode in elems(sk) && removedNode !in elems(newSk) 
    ensures removedNode.key==old(removedNode.key) && removedNode.value==old(removedNode.value)
    ensures elems(newSk) + {removedNode} == elems(sk)
    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    //ensures exists n | n in elems(sk) :: n.key == removedNode.key
    ensures forall n | n in elems(sk) :: n.key==old(n.key) && n.value==old(n.value)
    ensures forall n | n in elems(sk) && n.key != removedNode.key :: removedNode.key < n.key
    
    //ensures forall n | n in elems(sk) && n.key == removedNode.key :: removedNode.value == n.value && n !in elems(newSk)
    //ensures forall n | n in elems(newSk) :: n.key == old(n.key)
    //ensures MapModelRec(newNode, newSk) == map k | k in old(MapModelRec(node, sk)) && k != removedNode.key :: old(MapModelRec(node, sk)[k])
   
    ensures removedNode.key in old(MapModelRec(sk)) &&  old(MapModelRec(sk))[removedNode.key]==removedNode.value
    ensures MapModelRec(newSk)==old(MapModelRec(sk))-{removedNode.key}

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {      
    keysSearchTreeP(sk);

    if node.left == null {
      ghost var oMMRight:=MapModelRec(sk.right);
      ghost var oMM:=MapModelRec(sk);
      
      deletion(oMM,oMMRight,node.key,node.value);
      //assert oMM-{node.key}==oMMRight;

      newNode := node.right;
      newSk := sk.right;
      removedNode := node;
      
    } else {
      ghost var oMMRight:=MapModelRec(sk.right);
      ghost var oMMLeft:=MapModelRec(sk.left);
      ghost var oMM:=MapModelRec(sk);


      ghost var newSkLeft;
      node.left, newSkLeft, removedNode := RemoveMinRec(node.left, sk.left);
      
      newNode:=node;      
      newSk := Node(newSkLeft, newNode, sk.right);

      /*assert node.key==old(node.key) && node.value==old(node.value);
      assert newSk.left==newSkLeft && newSk.right==sk.right && newSk.data==node;
      assert MapModelRec(newSk.left)==oMMLeft-{removedNode.key};
      assert MapModelRec(newSk.right)==oMMRight;
      assert node.key !in oMMLeft && node.key !in oMMRight && node.key !=removedNode.key && removedNode.key !in oMMRight;
      assert oMM==(oMMLeft+oMMRight)[node.key:=node.value];
      */
      oldNewMapModelRecRemoveL(newSk,oMM,oMMLeft,oMMRight,node,removedNode.key);

      //assume MapModelRec(newSk)==old(MapModelRec(sk))-{removedNode.key};
    }
  }

  static method {:verify true} RemoveRec(node: TNode?, ghost sk: tree<TNode>, k: K) returns (newNode: TNode?, ghost newSk: tree<TNode>, ghost removedNode: TNode?)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    // modifies set x | x in elems(sk) :: x`key
    // modifies set x | x in elems(sk) :: x`value
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures forall n | n in elems(sk) :: n.key == old(n.key) && n.value == old(n.value)
    //ensures elems(sk) >= elems(newSk)
    //ensures forall n | n in elems(newSk) :: n.key == old(n.key) && n.value == old(n.value)
   // ensures elems(newSk) == set n | n in elems(sk) && n.key != k :: n
    
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures k !in old(MapModelRec(sk)) <==> removedNode==null 
    ensures removedNode != null ==> removedNode in elems(sk) && removedNode !in elems(newSk) && removedNode.key == k
    //ensures removedNode != null ==> elems(newSk) + {removedNode} == elems(sk)

    //ensures MapModelRec(newSk).Keys == old(MapModelRec(sk).Keys) - {k}
    //ensures TreeKeys(newSk) == old(TreeKeys(sk)) - {k}
    // ensures removedNode != null ==> MapModelRec(newNode, newSk) == map k' | k' in old(MapModelRec(node, sk)) && removedNode.key != k' :: old(MapModelRec(node, sk)[k'])
    // ensures MapModelRec(newNode, newSk) == map k' | k' in old(MapModelRec(node, sk)) && k != k' :: old(MapModelRec(node, sk)[k'])
    ensures MapModelRec(newSk)==old(MapModelRec(sk))-{k}

    
    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
       ModelRelationWithSkeletonKeyRec(node,sk,k);

    if node == null {
      newNode := node;
      newSk := sk;
      removedNode := null;
      assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};
    } else {
       ghost var oMMRight:=MapModelRec(sk.right);
       ghost var oMMLeft:=MapModelRec(sk.left);
       ghost var oMM:=MapModelRec(sk);
       keysSearchTreeP(sk);
       assert node.key !in oMMLeft && node.key !in oMMRight;

      if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, removedNode := RemoveRec(node.right, sk.right, k);
        newNode := node;
        newSk := Node(sk.left, node, newSkRight);
        
        assert MapModelRec(newSkRight)==oMMRight-{k};
        oldNewMapModelRecRemoveR(newSk,oMM,oMMLeft,oMMRight,node,k);
        assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};

             // assume MapModelRec(newSk)==old(MapModelRec(sk))-{k};
      } else if k < node.key {
        newNode := node;
        ghost var newSkLeft;
        node.left, newSkLeft, removedNode := RemoveRec(node.left, sk.left, k);
        newSk := Node(newSkLeft, node, sk.right);
        
        assert MapModelRec(newSkLeft)==oMMLeft-{k};
        oldNewMapModelRecRemoveL(newSk,oMM,oMMLeft,oMMRight,node,k);
        assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};

      } else {
        assert k == node.key;
        if node.right == null {
          newNode := node.left;
          newSk := sk.left;
          removedNode := node;
          
          assert oMM==oMMLeft[node.key:=node.value] && node.key !in oMMLeft;
          deletion(oMM,oMMLeft,node.key,node.value);
          assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};

        } else if node.left == null {
          newNode := node.right;
          newSk := sk.right;
          removedNode := node;
          
          assert oMM==oMMRight[node.key:=node.value] && node.key !in oMMRight;
          deletion(oMM,oMMRight,node.key,node.value);
          assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};

                

        } else {
          removedNode := node;
          ghost var newSkRight;
          var newRight;
          newRight, newSkRight, newNode := RemoveMinRec(node.right, sk.right);
          
          assert MapModelRec(newSkRight)==oMMRight-{newNode.key};
          assert newNode.key in oMMRight && oMMRight[newNode.key]==newNode.value;

          
          newNode.left := node.left;
          newNode.right := newRight;
          newSk := Node(sk.left, newNode, newSkRight);


          oldNewMapModelRecRemoveRMin(newSk,oMM,oMMLeft,oMMRight,node,newNode);
          assert MapModelRec(newSk)==old(MapModelRec(sk))-{k};

         

              //  assume MapModelRec(newSk)==old(MapModelRec(sk))-{k};

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
    //ensures k !in MapModel()
    // ensures MapModel() + map[k := old(MapModel()[k])] == old(MapModel())
    //ensures MapModel() == map k' | k' in old(MapModel()) && k' != k :: old(MapModel()[k'])
    ensures MapModel()==old(MapModel())-{k}

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
   // ContraModelRelationWithSkeletonKeyRecR(root, skeleton, k);
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