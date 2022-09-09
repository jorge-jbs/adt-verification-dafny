include "../../src/Order.dfy"
include "../../src/tree/TreeData.dfy"
include "../../src/tree/layer1/KeyValue.dfy"

datatype Color = Red | Black

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

  static function {:opaque} ModelRec(sk: tree<TNode>): map<K, V>
    reads set x | x in elems(sk) :: x`key
    reads set x | x in elems(sk) :: x`value
  {
    match sk {
      case Empty() => map[]
      case Node(l, n, r) => (ModelRec(l) + ModelRec(r))[n.key := n.value]
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

  static lemma ModelLemmas(node: TNode?, sk: tree<TNode>)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    ensures ModelRec(sk).Keys == TreeKeys(sk)
    ensures ModelRec(sk) == map k | k in TreeKeys(sk) :: FindNode(k, node, sk).value
    ensures forall n | n in elems(sk) :: n.key in ModelRec(sk) && n.value == ModelRec(sk)[n.key]
    ensures sk.Node? ==>
      && sk.data.key !in ModelRec(sk.left)
      && sk.data.key !in ModelRec(sk.right)
      && (forall k | k in ModelRec(sk.left) :: k !in ModelRec(sk.right))
      && (forall k | k in ModelRec(sk.right) :: k !in ModelRec(sk.left))
      && (forall k | sk.data.key <= k :: k !in ModelRec(sk.left))
      && (forall k | k <= sk.data.key :: k !in ModelRec(sk.right))
  {
    reveal ModelRec();
    match sk {
      case Empty() => {}
      case Node(l, n, r) => {
        ModelLemmas(node.left, sk.left);
        ModelLemmas(node.right, sk.right);
      }
    }
  }

  lemma ModelRecContained(node: TNode, sk: tree<TNode>, node': TNode, sk': tree<TNode>)
    requires ValidRec(node,sk) && ValidRec(node',sk')
    requires SearchTreeRec(sk) && SearchTreeRec(sk')
    requires elems(sk) <= elems(sk')
    ensures ModelRec(sk).Items <= ModelRec(sk').Items
  {
    if ModelRec(sk).Items != {} {
      forall p | p in ModelRec(sk).Items
        ensures p in ModelRec(sk').Items
      {
        ModelRelationWithSkeletonRecR(node,sk,p.0,p.1);
        var n :| n in elems(sk) && n.key == p.0 && n.value == p.1;
        assert n in elems(sk');
        ModelRelationWithSkeletonRecL(node',sk',p.0,p.1);
        assert p.0 in ModelRec(sk') && ModelRec(sk')[p.0]==p.1;
        assert p in ModelRec(sk').Items;
      }
    } else {
    }
  }

  static function LeftPathAux(n: TNode, sk: tree<TNode>): seq<TNode>
    reads elems(sk)
    requires SearchTreeRec(sk)
    requires n in elems(sk)
    ensures n==sk.data ==> LeftPathAux(n,sk)==[n]
    ensures |LeftPathAux(n,sk)|>=1 && LeftPathAux(n,sk)[0]==n
    ensures forall i | 0 < i <|LeftPathAux(n,sk)| :: LeftPathAux(n,sk)[i].key > n.key
    ensures n.key < sk.data.key ==> LeftPathAux(n, sk)==LeftPathAux(n, sk.left)+ [sk.data]
    ensures n.key > sk.data.key ==> LeftPathAux(n, sk)==LeftPathAux(n, sk.right)
  {
    match sk {
      case Node(l, x, r) =>
        if n == x then
          [n]
        else if n.key < x.key then
          LeftPathAux(n, l) + [x]
        else
          LeftPathAux(n, r)
    }
  }

  static lemma subTree(n:TNode,sk:tree<TNode>,root:TNode,p:tree<TNode>)
    requires SearchTreeRec(sk) && ValidRec(n,sk)
    requires SearchTreeRec(p) && ValidRec(root,p)
    requires n in elems(p)
    ensures elems(sk)  <= elems(p)
  {}

  static lemma {:verify true} propLeftPath(n:TNode,sk:tree<TNode>,root:TNode,p:tree<TNode>)
    requires SearchTreeRec(sk) && ValidRec(n,sk)
    requires SearchTreeRec(p) && ValidRec(root,p)
    requires n in elems(p)
    ensures  SearchTreeRec(sk.left) && ValidRec(n.left,sk.left)
    ensures n.left!=null ==> n.left in elems(p)
    ensures SearchTreeRec(sk.right) && ValidRec(n.right,sk.right)
    ensures n.right!=null ==> n.right in elems(p)
    ensures n.left!=null ==> LeftPathAux(n.left,p)==[n.left]+LeftPathAux(n,p)
    ensures n.right!=null ==> |LeftPathAux(n,p)|>=1 && LeftPathAux(n.right,p)==[n.right]+(LeftPathAux(n,p)[1..])
    ensures forall i | 0 < i < |LeftPathAux(n,p)| ::  LeftPathAux(n,p)[0].key < LeftPathAux(n,p)[i].key

    ensures forall i,j | 0 <= i < j < |LeftPathAux(n,p)| :: LeftPathAux(n,p)[i].key < LeftPathAux(n,p)[j].key
  {
    assert SearchTreeRec(sk.left);
    assert ValidRec(n.left,sk.left);
    assert SearchTreeRec(sk.right);
    assert ValidRec(n.right,sk.right);
    subTree(n,sk,root,p);
    assert elems(sk)<=elems(p);

    if (n.left!=null)
    {
     assert n.left in elems(p);
    assert n.left==sk.left.data;

    if (n==p.data) {
      assert LeftPathAux(n,p)==[n];
      assert LeftPathAux(n.left,p)==[n.left,n]; }
    else if (n.key < p.data.key)
    {

      calc =={
      LeftPathAux(n.left,p);
      {assert n.left.key < n.key < p.data.key;}
      LeftPathAux(n.left,p.left)+[p.data];
      {propLeftPath(n.left,sk.left,p.left.data,p.left);}
      [n.left]+LeftPathAux(n,p.left)+[p.data];
      [n.left]+LeftPathAux(n,p);
      }
     }
     else //n.key>p.data.key
     {
      calc =={
      LeftPathAux(n.left,p);
      { assert n in elems(p.right);
      subTree(n,sk,root.right,p.right);
        assert elems(sk)<=elems(p.right);
        assert n.left.key > p.data.key;}
      LeftPathAux(n.left,p.right);
      {propLeftPath(n.left,sk.left,p.right.data,p.right);}
      [n.left]+LeftPathAux(n,p.right);
      [n.left]+LeftPathAux(n,p);
      }


     }
    }

    if (n.right!=null)
    {
       assert n.right in elems(p);
       assert n.right==sk.right.data;

      if (n==p.data) {
      assert LeftPathAux(n,p)==[n];
      assert LeftPathAux(n,p)[1..]==[];
      assert LeftPathAux(n.right,p)==[n.right]; }
    else if (n.key > p.data.key)
    {
      calc =={
      LeftPathAux(n.right,p);
      {assert n.right.key > n.key > p.data.key;}
      LeftPathAux(n.right,p.right);
      {propLeftPath(n.right,sk.right,p.right.data,p.right);}
      [n.right]+LeftPathAux(n,p.right)[1..];
      [n.right]+LeftPathAux(n,p)[1..];
      }
     }
     else //n.key<p.data.key
     {
      calc =={
      LeftPathAux(n.right,p);
      { assert n in elems(p.left);
      subTree(n,sk,root.left,p.left);
        assert elems(sk)<=elems(p.left);
        assert n.right.key < p.data.key;
       }
      LeftPathAux(n.right,p.left)+[p.data];
      {propLeftPath(n.right,sk.right,p.left.data,p.left);}
      [n.right]+LeftPathAux(n,p.left)[1..]+[p.data];
      [n.right]+LeftPathAux(n,p)[1..];
      }


     }
    }

     assert LeftPathAux(n,p)[0]==n;
      forall i | 0 < i < |LeftPathAux(n,p)|
      ensures  LeftPathAux(n,p)[0].key < LeftPathAux(n,p)[i].key
      {assert n.key == LeftPathAux(n,p)[0].key < LeftPathAux(n,p)[i].key; }

    assume forall i,j | 0 <= i < j < |LeftPathAux(n,p)| :: LeftPathAux(n,p)[i].key < LeftPathAux(n,p)[j].key;

  }


  static lemma elemsProps(n:TNode,sk:tree<TNode>)
    requires ValidRec(n,sk)
    requires SearchTreeRec(sk)
    ensures forall m | m in elems(sk.left) :: m.key < n.key
    ensures  forall m | m in elems(sk.right) :: m.key > n.key
  {}

  function Model(): map<K, V>
    reads this, elems(skeleton)
    requires Valid()
  {
    ModelRec(skeleton)
  }

  constructor()
    ensures Valid()
    ensures Model() == map[]
    ensures SearchTree()
    ensures RedBlackTree()

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() :: fresh(x)
    ensures fresh(Repr())
    ensures forall x | x in Repr() :: allocated(x)
  {
    root := null;
    skeleton := Empty;
    reveal ModelRec();
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

  predicate SearchTree()
    reads this, Repr()
    requires Valid()
  {
    SearchTreeRec(skeleton)
  }

  lemma {:verify false} ModelRelationWithSkeleton(k: K, v: V)
    requires Valid()
    requires SearchTree()
    ensures k in Model() && Model()[k] == v <==> exists n | n in elems(skeleton) :: n.key == k && n.value == v
  {
    if k in Model() && Model()[k] == v {
      ModelRelationWithSkeletonRecR(root, skeleton, k, v);
    }
    if exists n | n in elems(skeleton) :: n.key == k && n.value == v {
      ModelRelationWithSkeletonRecL(root, skeleton, k, v);
    }
  }

  static lemma {:verify false} ModelRelationWithSkeletonRecR(node: TNode?, sk: tree<TNode>, k: K, v: V)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires k in ModelRec(sk)
    requires ModelRec(sk)[k] == v
    ensures (exists n | n in elems(sk) :: n.key == k && n.value == v)
  {}

  static lemma {:verify false} ModelRelationWithSkeletonRecL(node: TNode?, sk: tree<TNode>, k: K, v: V)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires (exists n | n in elems(sk) :: n.key == k && n.value == v)
    ensures k in ModelRec(sk)
    ensures ModelRec(sk)[k] == v
  {
    match sk {
      case Empty => {}
      case Node(l, n, r) => {
        if n.key == k {
        } else if k < n.key {
          assert k in ModelRec(l);

          assert forall m | m in elems(r) :: n.key != m.key;
          if k in ModelRec(r) {
            ModelRelationWithSkeletonKeyRecR(n.right, r, k);
            assert false;
          }
          assert k !in ModelRec(r);

          assert ModelRec(sk)[k] == v;
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
    ensures k in Model() <==> exists n | n in elems(skeleton) :: n.key == k
  {
    ModelRelationWithSkeletonKeyRec(root, skeleton, k);
  }

 static lemma {:verify false} ModelRelationWithSkeletonKeyRec(node: TNode?, sk: tree<TNode>,k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    ensures k in ModelRec(sk) <==> (exists n | n in elems(sk) :: n.key == k)
  {
    if k in ModelRec(sk) {
      ModelRelationWithSkeletonKeyRecR(node, sk, k);
    }
    if exists n | n in elems(sk) :: n.key == k {
      ModelRelationWithSkeletonKeyRecL(node, sk, k);
    }
  }

  static lemma {:verify false} ModelRelationWithSkeletonKeyRecR(node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires k in ModelRec(sk)
    ensures (exists n | n in elems(sk) :: n.key == k)
  {}

  static lemma {:verify false} ContraModelRelationWithSkeletonKeyRecR(node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires forall m | m in elems(sk) :: k != m.key;
    ensures k !in ModelRec(sk)
  {
      if k in ModelRec(sk) {
        ModelRelationWithSkeletonKeyRecR(node, sk, k);
        assert false;
      }
      assert k !in ModelRec(sk);
  }

  static lemma {:verify false} ModelRelationWithSkeletonKeyRecL(node: TNode?, sk: tree<TNode>, k: K)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires (exists n | n in elems(sk) :: n.key == k)
    ensures k in ModelRec(sk)
  {
    match sk {
      case Empty => {}
      case Node(l, n, r) => {}
    }
  }

  function method {:verify false} isEmpty(): bool
    reads this, Repr()
    requires Valid()
    ensures isEmpty() <==> Model() == map[]
  {
    root == null
  }

  // TODO: añadir tamaño
  function method {:verify false} Size():nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|

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
  ensures (set n | n in elems(sk)::n.key) == ModelRec(sk).Keys
  ensures sk.data.key !in ModelRec(sk.left) && sk.data.key !in ModelRec(sk.right)
  ensures ModelRec(sk.left).Keys !! ModelRec(sk.right).Keys
  ensures ModelRec(sk).Keys==ModelRec(sk.left).Keys+ModelRec(sk.right).Keys+{sk.data.key}
  ensures  k < sk.data.key ==> k !in ModelRec(sk.right)
  ensures  k > sk.data.key ==> k !in ModelRec(sk.left)
{}

static lemma {:verify false} keysSearchTreeP(sk:tree<TNode>)
  requires SearchTreeRec(sk)  && sk !=Empty()
  ensures (set n | n in elems(sk)::n.key) == ModelRec(sk).Keys
  ensures sk.data.key !in ModelRec(sk.left) && sk.data.key !in ModelRec(sk.right)
  ensures ModelRec(sk.left).Keys !! ModelRec(sk.right).Keys
  ensures ModelRec(sk).Keys==ModelRec(sk.left).Keys+ModelRec(sk.right).Keys+{sk.data.key}
{}

static lemma {:verify false} oldNewModelRecL(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,k:K,v:V)
  requires ValidRec(node,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires ModelRec(newSk.left)==mskL[k:=v]
  requires ModelRec(newSk.right)==mskR
  requires node.key !in mskL && node.key !in mskR && node.key !=k && k !in mskR
  requires moSk==(mskL+mskR)[node.key:=node.value]
  ensures ModelRec(newSk)==moSk[k:=v]
{
  calc == {
    ModelRec(newSk);
    (ModelRec(newSk.left)+ModelRec(newSk.right))[node.key:=node.value];
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

static lemma {:verify false} oldNewModelRecR(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,k:K,v:V)
  requires ValidRec(node,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires ModelRec(newSk.left)==mskL
  requires ModelRec(newSk.right)==mskR[k:=v]
  requires node.key !in mskL && node.key !in mskR && node.key !=k
  requires moSk==(mskL+mskR)[node.key:=node.value]
  ensures ModelRec(newSk)==moSk[k:=v]
{
  calc == {
    ModelRec(newSk);
    (ModelRec(newSk.left)+ModelRec(newSk.right))[node.key:=node.value];
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

static lemma {:verify false} oldNewModelRecRemoveL(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,k:K)
  requires ValidRec(node,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires ModelRec(newSk.left)==mskL-{k}
  requires ModelRec(newSk.right)==mskR
  requires node.key !in mskL && node.key !in mskR && node.key !=k && k !in mskR
  requires moSk==(mskL+mskR)[node.key:=node.value]
ensures ModelRec(newSk)==moSk-{k}
{
  calc == {
    ModelRec(newSk);
    (ModelRec(newSk.left)+ModelRec(newSk.right))[node.key:=node.value];
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

static lemma {:verify false} oldNewModelRecRemoveR(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,k:K)
  requires ValidRec(node,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires ModelRec(newSk.left)==mskL
  requires ModelRec(newSk.right)==mskR-{k}
  requires node.key !in mskL && node.key !in mskR && node.key !=k && k !in mskL
  requires moSk==(mskL+mskR)[node.key:=node.value]
  ensures ModelRec(newSk)==moSk-{k}
{
  calc == {
    ModelRec(newSk);
    (ModelRec(newSk.left)+ModelRec(newSk.right))[node.key:=node.value];
    (mskL+(mskR-{k}))[node.key:=node.value];
    { assert k !in mskL;
    pushUpMapDR(mskL,mskR,k);}
    ((mskL+mskR)-{k})[node.key:=node.value];
    { assert node.key!=k; }
    ((mskL+mskR)[node.key:=node.value])-{k};
    moSk-{k};
  }
}

static lemma {:verify false} oldNewModelRecRemoveRMin(newSk:tree<TNode>, moSk:map<K,V>,mskL:map<K,V>,mskR:map<K,V>,node:TNode,newNode:TNode)
  requires ValidRec(newNode,newSk) && SearchTreeRec(newSk)
  requires newSk!=Empty
  requires ModelRec(newSk.left)==mskL
  requires ModelRec(newSk.right)==mskR-{newNode.key}
  requires node.key !in mskL && node.key !in mskR
  requires newNode.key in mskR && mskR[newNode.key]==newNode.value
  requires moSk==(mskL+mskR)[node.key:=node.value]
  ensures ModelRec(newSk)==moSk-{node.key}
{
  calc == {
    ModelRec(newSk);
    (ModelRec(newSk.left)+ModelRec(newSk.right))[newNode.key:=newNode.value];
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

  static function method NegColor(color: Color): Color
  {
    match color {
      case Black => Red
      case Red => Black
    }
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

  static predicate {:verify true} RedBlackTreeRec(sk: tree<TNode>)
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
}