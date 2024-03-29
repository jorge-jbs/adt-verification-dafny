include "../../../src/tree/layer1/UnorderedMap.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"






trait OrderedMapIterator extends UnorderedMapIterator{

function Traversed():set<K>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed() <= (Parent().Model().Keys)
    ensures forall x,y | x in Traversed() && y in Parent().Model().Keys-Traversed() :: x < y

function method Peek():pairKV 
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model().Items &&
            key(Peek()) !in Traversed() 
    ensures key(Peek())==elemth(Parent().Model().Keys,|Traversed()|)  &&
            value(Peek()) == Parent().Model()[key(Peek())]      
    ensures forall k | k in Traversed() :: k < key(Peek())
    ensures forall k | k in Parent().Model().Keys-Traversed()-{key(Peek())} :: key(Peek()) < k
    ensures forall k | k in Parent().Model().Keys-Traversed() :: key(Peek()) <= k

  

 function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext()  <==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasNext() ==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|
  
  function method Index(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() ==> Index()==|Traversed()|==|smaller(Parent().Model().Keys,key(Peek()))|
    ensures !HasNext() ==> Index()==|Parent().Model()|
  

  method Next() returns (p: pairKV)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())

    ensures p==old(Peek()) && Traversed() == {old(key(Peek()))}+old(Traversed())
    ensures |Traversed()|==1+|old(Traversed())|
    ensures HasNext() ==> key(Peek())==elemth(Parent().Model().Keys,|Traversed()|)//already known

    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek())))

function method HasPrev(): bool//igual que HasNext
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasPrev()  <==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasPrev() ==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|
  

  method Prev() returns (p: pairKV)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasNext() 
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures p==old(Peek())  
    ensures old(Traversed())=={} ==> Traversed()==Parent().Model().Keys
    ensures old(Traversed())!={} ==> (Traversed()==old(Traversed())-{maximum(old(Traversed()))} &&
                                      (HasNext() ==> key(Peek())==maximum(old(Traversed()))))
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek())))

  method Copy() returns (it: UnorderedMapIterator)
    modifies Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures fresh(it)
    ensures Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Valid()
    ensures Parent().Model() == old(Parent().Model())

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)
    
    ensures it is OrderedMapIterator
    ensures it.Valid()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()

    ensures Traversed() == it.Traversed() 
    ensures HasNext() ==> Peek()==it.Peek()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))


}

trait OrderedMap extends UnorderedMap {
  
 
 function Iterators(): set<UnorderedMapIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is OrderedMapIterator

method First() returns (it: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures it is OrderedMapIterator
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed()=={} 
    ensures Model()!=map[] ==> it.HasNext() && key(it.Peek())==elemth(Model().Keys,0)
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

  method Last() returns (it: OrderedMapIterator)//iterator to the last element
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures Model()!=map[] ==> it.HasNext() && it.Traversed()==Model().Keys-{elemth(Model().Keys,|Model().Keys|-1)} && key(it.Peek())==elemth(Model().Keys,|Model().Keys|-1)
    ensures Model()==map[] ==> it.Traversed()=={}
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))




method find(k:K) returns (newt:UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model()==old(Model())
    
    ensures newt is OrderedMapIterator
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent()==this
    ensures k in old(Model()) ==> newt.HasNext() && key(newt.Peek())==k
    ensures k !in old(Model()) ==> newt.Traversed()==Model().Keys

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt}+old(Iterators())

  method insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt:UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())[k:=v]

    ensures newt is OrderedMapIterator
    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this  
    ensures newt.HasNext() && newt.Peek()==(k,v) && newt.Traversed()==smaller(Model().Keys,k)

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    //points either to the inserted elemento or to the already existing one
 



  method erase(mid:UnorderedMapIterator) returns (next: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== map k | k in old(Model()) && k!=old(key(mid.Peek()))::old(Model())[k]
    
    ensures next is OrderedMapIterator
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Traversed()==old(mid.Traversed()) &&
                (next.HasNext() ==> key(next.Peek())==elemth(Model().Keys,|next.Traversed()|) && value(next.Peek())==Model()[key(next.Peek())])


    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
 
}

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

 
  /*static function ModelRec(sk: tree<TNode>): tree<K>
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
  }*/

  static function MapModelRec(sk: tree<TNode>): map<K, V>
    reads set x | x in elems(sk) :: x`key
    reads set x | x in elems(sk) :: x`value
    ensures forall n | n in elems(sk) :: n.key in MapModelRec(sk)
   // ensures sk==Empty() ==> MapModelRec(sk)==map[]
   // ensures sk!=Empty ==>MapModelRec(sk) == (MapModelRec(sk.left)+MapModelRec(sk.right))[sk.data.key:=sk.data.value]
  {
    match sk {
      case Empty() => map[]
      case Node(l, n, r) => (MapModelRec(l) + MapModelRec(r))[n.key := n.value]
    }  
  
  }
  
  static function TreeKeys(sk: tree<TNode>): set<K>
    reads elems(sk)
  {
    set n | n in elems(sk) :: n.key
  }

 static lemma MapModelRecComAsoc(l:tree<TNode>,r:tree<TNode>)
 requires MapModelRec(r).Keys !! MapModelRec(l).Keys
 ensures MapModelRec(l)+MapModelRec(r) == MapModelRec(r) + MapModelRec(l)
{}

  function MapModel(): map<K, V>
    reads this, elems(skeleton)
    requires Valid()
  {
    MapModelRec(skeleton)
  }

  constructor()
    ensures Valid()
    ensures fresh(Repr())
    //ensures Model() == Empty
    ensures MapModel()==map[]
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

 static method {:verify true} FindRec(node: TNode?, ghost sk: tree<TNode>, k: K) returns (found: TNode?)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures ValidRec(node, sk)
    ensures SearchTreeRec(sk)
    ensures found == null <==> k !in old(MapModelRec(sk))
    ensures found != null ==>  found in elems(sk) && found.key == k && found.value==old(MapModelRec(sk))[k]
//    ensures MapModelRec(sk) == old(MapModelRec(sk))

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
        ModelRelationWithSkeletonKeyRec(node,sk,k);

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
    if (found!=null)
      { ModelRelationWithSkeletonRecL(node,sk,k,found.value); } 
 
    }
  }

method {:verify true} Find(k: K) returns (found: TNode?)
    requires Valid()
    requires SearchTree()
    requires forall x | x in Repr() :: allocated(x)

    ensures found == null <==> k !in old(MapModel())
    ensures found != null ==>  found in elems(skeleton) && found.key == k && found.value == old(MapModel())[k]

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    assert Repr() == elems(skeleton);
    found := FindRec(root, skeleton, k);
  }


  method {:verify true} Search(k: K) returns (b:bool)
    requires Valid()
    requires SearchTree()
    ensures Valid()
    ensures SearchTree()
    ensures b == (k in MapModel())

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x | x in Repr() :: allocated(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    { var found:=Find(k);
      b:= (found!=null); 
    }

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
  {
    ModelRelationWithSkeletonKeyRec(n,sk,k);
    assert exists n | n in elems(sk) :: n.key == k;
    
    if k == n.key {
      v := n.value;
    } else if n.key < k {
      v := GetRec(n.right, sk.right, k);
    } else if k < n.key {
      v := GetRec(n.left, sk.left, k);
    } else {
      assert false;
    }
    ModelRelationWithSkeletonRecL(n,sk,k,v);
    
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
    assert Repr() == elems(skeleton);
    v := GetRec(root, skeleton, k);
  }

  

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

        ghost var newSkRight;
        node.right, newSkRight, z := InsertRec(node.right, sk.right, k, v);

        newSk := Node(sk.left, node, newSkRight);

      } else if k < node.key {

        ghost var oMMRight:=MapModelRec(sk.right);
        ghost var oMMLeft:=MapModelRec(sk.left);
        ghost var oMM:=MapModelRec(sk);
        keysSearchTree(sk,k);

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
    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)

    ensures removedNode in elems(sk) && removedNode !in elems(newSk) 
    ensures removedNode.key==old(removedNode.key) && removedNode.value==old(removedNode.value)
    ensures elems(newSk) + {removedNode} == elems(sk)

    ensures removedNode.key in old(MapModelRec(sk)) &&  old(MapModelRec(sk))[removedNode.key]==removedNode.value
    ensures MapModelRec(newSk)==old(MapModelRec(sk))-{removedNode.key}

    ensures forall n | n in elems(sk) :: n.key==old(n.key) && n.value==old(n.value)
    ensures forall n | n in elems(sk) && n.key != removedNode.key :: removedNode.key < n.key
    

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
   
    ensures forall n | n in elems(sk) :: n.key == old(n.key) && n.value == old(n.value)
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures k !in old(MapModelRec(sk)) <==> removedNode==null 
    ensures removedNode != null ==> removedNode in elems(sk) && removedNode !in elems(newSk) && removedNode.key == k
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
    ensures MapModel()==old(MapModel())-{k}

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    ghost var removedNode;
    root, skeleton, removedNode := RemoveRec(root, skeleton, k);
  }


  
}