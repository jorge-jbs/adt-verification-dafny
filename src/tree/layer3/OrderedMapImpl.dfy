include "../../../src/tree/BinTreeIntClara.dfy"
include "../../../src/tree/layer1/OrderedMap.dfy"


class OrderedMapIteratorImpl extends OrderedMapIterator{

ghost var parent:OrderedMapImpl;
  ghost var stackSK: seq<tree<TNode>>;//esto debería ser una Stack
  var stack:seq<TNode>  

  constructor(p:OrderedMapImpl)
  requires p.Valid()
  ensures Valid()
  { parent:=p;
    assume false;//De momento para que see trague el valid
    stackSK:=[];
    stack := [];

  }




function Parent(): UnorderedMap
    reads this
    ensures Parent() is OrderedMapImpl
{ parent }


  
function reachableFromStack(i:int):set<TNode>
 reads this,Parent(), Parent().Repr()
 requires 0 <= i < |stack|==|stackSK|
 requires parent.Valid() 
 requires stack[i] in Parent().Repr()
 requires elems(stackSK[i]) <= Parent().Repr()
 requires Tree.ValidRec(stack[i],stackSK[i])
{ {stack[i]} + elems(stackSK[i].right)}

function reachableFromStacks():set<TNode>
 reads this,Parent(), Parent().Repr()
  requires parent.Valid() && |stack|==|stackSK|
  requires  (forall i | 0 <= i < |stack| :: stack[i] in Parent().Repr()) 
  requires  (forall i | 0 <= i < |stackSK| :: elems(stackSK[i]) <= Parent().Repr())  
  requires  (forall i | 0 <= i < |stack| :: Tree.ValidRec(stack[i],stackSK[i])) 
  ensures stack==[] ==> reachableFromStacks()=={}
{ unions(set i | 0 <= i < |stack| :: reachableFromStack(i))}

 


function unions<A> (ss:set<set<A>>):set<A>
  {
    if (ss=={}) then {}
    else 
     var s:| s in ss;
     s+unions(ss-{s})
  }


predicate Valid()
    reads this, Parent(), Parent().Repr()

{   parent.Valid() && 
    |stack|==|stackSK| &&  
    (forall i | 0 <= i < |stack| :: stack[i] in Parent().Repr()) &&
    (forall i | 0 <= i < |stackSK| :: elems(stackSK[i]) <= Parent().Repr()) && 
    (forall i,j | 0 <= i < j < |stackSK| :: elems(stackSK[i]) < elems(stackSK[j])) && //puede que se deduzca de leftPathAux
    (forall i | 0 <= i < |stack| :: Tree.ValidRec(stack[i],stackSK[i])) &&
    (forall i | 0 <= i < |stackSK| :: Tree.SearchTreeRec(stackSK[i])) && 
    (forall i,j | 0 <= i < j < |stack| :: reachableFromStack(i)!!reachableFromStack(j)) && 
    (forall i | 0 <= i < |stack| :: reachableFromStack(i)!!traversed()) && 
    elems(parent.tree.skeleton)==traversed()+ reachableFromStacks() &&
    (forall i, n, m | 0 <= i < |stack| && n in traversed() && m in reachableFromStack(i):: n.key < m.key) && 
    (forall i,j,n,m | 0 <= i < j < |stack| && n in reachableFromStack(i) && m in reachableFromStack(j):: n.key < m.key)&&
    (stack !=[] ==> |stack| == |Tree.LeftPathAux(stack[0],parent.tree.skeleton)|) && 
    (forall i | 0 <= i < |stack|  :: stack[i]==Tree.LeftPathAux(stack[0],parent.tree.skeleton)[i])  
}


function traversed():set<TNode>
      reads this,Parent(), Parent().Repr()
      requires parent.Valid()
      requires stack!=[] ==> stack[0] in Parent().Repr()
  { if (stack==[]) then {} 
    else 
      (set n | n in elems(parent.tree.skeleton) && n.key < stack[0].key :: n)
  }




function Traversed():set<K>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed() <= (Parent().Model().Keys)
    ensures forall x,y | x in Traversed() && y in Parent().Model().Keys-Traversed() :: x < y
{   
 if (stack==[]) then {}
  else 
   (set m | m in Parent().Model().Keys && m < stack[0].key)
}

lemma setProperty(s1:set<K>,s2:set<K>)
requires s1==s2
ensures  |s1|==|s2|
{}


lemma {:verify true} traversedRelation()
requires Valid()
ensures Traversed()==(set n | n in traversed():: n.key)
ensures |Traversed()|==|traversed()|
{ 
  if (stack==[]) {}
  else {parent.tree.ModelRelationWithSkeletonKeys(stack[0].key);}

  assert Traversed()==(set n | n in traversed():: n.key);
  sizes(Traversed(),(set n | n in traversed():: n.key));
  assert |Traversed()|==|(set n | n in traversed():: n.key)|;
  //assume false;

  //setProperty(Traversed(),(set n | n in traversed():: n.key));
  //assert |Traversed()|==|(set n | n in traversed():: n.key)|;
  assume |(set n | n in traversed():: n.key)| == |traversed()|;
  //assume false;
  //==|traversed()|;

}




function method {:verify true} Peek():pairKV 
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model().Items &&
            key(Peek()) !in Traversed() 
    ensures key(Peek())==elemth(Parent().Model().Keys,|Traversed()|)  
    ensures value(Peek()) == Parent().Model()[key(Peek())]      
    ensures forall k | k in Traversed() :: k < key(Peek())
    ensures forall k | k in Parent().Model().Keys-Traversed()-{key(Peek())} :: key(Peek()) < k
    ensures forall k | k in Parent().Model().Keys-Traversed() :: key(Peek()) <= k
  { peekProperties();
    elemthProperty();
    (stack[0].key,stack[0].value) }
  
  lemma {:verify true} peekProperties()
  requires Valid() 
  requires stack!=[]
  ensures (stack[0].key,stack[0].value) in  Parent().Model().Items
  ensures stack[0].key !in Traversed()
  ensures stack[0].value == Parent().Model()[stack[0].key]
  ensures forall k | k in Traversed() :: k < stack[0].key
  ensures forall k | k in Parent().Model().Keys-Traversed() :: stack[0].key <= k
  ensures forall k | k in Parent().Model().Keys-Traversed()-{stack[0].key} :: stack[0].key < k
  { assert Tree.ValidRec(stack[0],stackSK[0]);
    assert Tree.SearchTreeRec(stackSK[0]);
    assert stack[0] in elems(stackSK[0]);
    Tree.ModelRelationWithSkeletonRecL(stack[0],stackSK[0],stack[0].key,stack[0].value);
    assert (stack[0].key,stack[0].value) in Tree.MapModelRec(stackSK[0]).Items;
    parent.tree.mapModelRecContained(stack[0],stackSK[0],parent.tree.root,parent.tree.skeleton);
    assert Tree.MapModelRec(stackSK[0]).Items <= Parent().Model().Items;
    assert forall k | k in Parent().Model().Keys-Traversed() && k!=stack[0].key :: stack[0].key < k;
  }


lemma elemthProperty()
requires Valid()
requires stack!=[]
requires 0<=|Traversed()|< |Parent().Model().Keys|;
ensures stack[0].key==elemth(Parent().Model().Keys,|Traversed()|)  
{
  // && x in s && |smaller(s,x)|==k
  //assume false;

  lelemthrev(Parent().Model().Keys, stack[0].key, |Traversed()|);
  //assume false;
}


 function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext()  <==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasNext() ==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|
 // {stack != []}


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

class OrderedMapImpl extends OrderedMap {
  
 var  tree:Tree;
  ghost var iters:set<OrderedMapIteratorImpl>;


  constructor()
  {
   tree:=new Tree();
   iters:={};

  }

  function Repr0(): set<object>
    reads this
  {
    {tree} + iters 
  }

  function ReprDepth(): nat
    reads this
    ensures ReprDepth() > 0
  { 1 }

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= ReprDepth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)
  {
    if (n==0) then Repr0()
    else Repr0()+tree.Repr()
  }
  

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());

  predicate Valid()
    reads this, Repr()
  {
   tree.Valid() && tree.SearchTree()
  }  

  function Model(): map<K,V>
    reads this, Repr()
    requires Valid()
  {
    tree.MapModel()
  }

function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == map[]
  { 
    tree.isEmpty() 
  }



 function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|
  { 
    tree.Size() 
  }

 function Iterators(): set<UnorderedMapIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is OrderedMapIterator
  { {} }

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

method contains(k:K) returns (b:bool)
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    
    ensures Valid() 
    ensures b==(k in Model()) 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())
  {
   assert tree.Repr() <= Repr();

   b:=tree.Search(k);

  }

method at(k:K) returns (v:V)
    //modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    requires k in Model()
    ensures Valid()
    //ensures Model()==old(Model())
    ensures v == Model()[k] 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())
  {
    assert tree.Repr() <= Repr();

    v:=tree.Get(k);
  }


 method add(k:K,v:V)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())[k:=v] 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())
  {
    tree.Insert(k,v);
  }

method remove(k:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== map k' | k' in old(Model()) && k'!=k::old(Model())[k']

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
  {
   tree.Remove(k);
  }




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