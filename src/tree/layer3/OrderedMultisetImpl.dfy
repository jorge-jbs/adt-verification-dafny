include "../../../src/tree/layer1/OrderedMultiset.dfy"
include "../../../src/tree/layer1/OrderedMultisetUtils.dfy"
include "../../../src/tree/old/BinTreeIntClara.dfy"

function mapToMultiset(s:set<(K,V)>):multiset<K>  
  ensures forall k | k in mapToMultiset(s):: (exists p | p in s ::p.0==k && p.1>0)
  {
    if (s=={}) then multiset{}
    else 
       var p:| p in s;
       //assert p.1>0 && p.0 !in mapToMultiset(s-{p});
       if (p.1>0) then
        mapToMultiset(s-{p})[p.0:=p.1]
      else 
        mapToMultiset(s-{p})
  }

  /*function mapModelToMultiset(m:map<K,V>):multiset<K>
  {mapToMultiset(m.)}
  */
  lemma MapMultisetMonotone(s:set<(K,V)>,z:(K,V))
  ensures mapToMultiset(s-{z}) <= mapToMultiset(s)
  

  lemma MapMultisetMonotone2(s:set<(K,V)>,z:(K,V),p:(K,V))
  requires p in s && p!=z
  ensures mapToMultiset(s)[p.0]==mapToMultiset(s-{z})[p.0]
  
  
  lemma  {:verify false} MapMultisetRelationAuxA(s:set<(K,V)>,p:(K,V))
  requires s != {} && p in s && p.1>0
  ensures p.0 in mapToMultiset(s) && mapToMultiset(s)[p.0]==p.1
  {
     //
     if (s-{p}=={}) {assert s=={p}; //assert p==z;
      assert mapToMultiset(s)==multiset{}[p.0:=p.1];
     }
     else{
      var z:|z in s && p!=z;
       {assert p in s-{z};
        MapMultisetRelationAuxA(s-{z},p);
        assert p.0 in mapToMultiset(s-{z}) && mapToMultiset(s-{z})[p.0]==p.1;
        MapMultisetMonotone(s,z);
        MapMultisetMonotone2(s,z,p);       
        assert p.0 in mapToMultiset(s) && mapToMultiset(s)[p.0]==p.1;
        }
     }
}

lemma {:verify false} MapMultisetRelationAux(s:set<(K,V)>)
  ensures forall p | p in s && p.1>0 :: p.0 in mapToMultiset(s) && mapToMultiset(s)[p.0]==p.1
  {forall p | p in s && p.1>0 
  ensures p.0 in mapToMultiset(s) && mapToMultiset(s)[p.0]==p.1
  {MapMultisetRelationAuxA(s,p);}}

lemma {:verify false} mapItems(m:map<K,V>,k:K)
requires m!=map[] && k in m
ensures exists p :: p in m.Items && p.0==k
{ assert (k,m[k]) in m.Items;}


    lemma {:verify false} MapMultisetRelation(m:map<K,V>)
    requires forall k | k in m :: m[k]>0
    ensures m==map[] <==> mapToMultiset(m.Items)==multiset{}
    ensures forall k | k in m :: k in mapToMultiset(m.Items) && mapToMultiset(m.Items)[k]==m[k]
    ensures forall k | k in mapToMultiset(m.Items) :: k in m && mapToMultiset(m.Items)[k]==m[k]
    ensures forall k | mapToMultiset(m.Items)[k]>0 :: k in m
    ensures forall k | mapToMultiset(m.Items)[k]==0 :: k !in m
    ensures forall k | k !in m :: mapToMultiset(m.Items)[k]==0
    ensures forall k | k !in mapToMultiset(m.Items)::k !in m
  {
    forall k | k in m 
    ensures k in mapToMultiset(m.Items) && mapToMultiset(m.Items)[k]==m[k]
    { mapItems(m,k);
      MapMultisetRelationAux(m.Items);}
  }

    lemma {:verify false} EquivalenceMapMultisetRelation(m:map<K,V>,ms:multiset<K>)
    requires forall k | k in m :: m[k]>0
    ensures (map k | k in ms :: ms[k]) == m <==> (mapToMultiset(m.Items)==ms)
     {
      MapMultisetRelation(m);
      }

   lemma {:verify false} equalMapMultiset(m:map<K,V>,m':map<K,V>)
    requires forall k | k in m :: m[k]>0
    requires forall k | k in m' :: m'[k]>0
    requires mapToMultiset(m.Items)==mapToMultiset(m'.Items)
    ensures m.Items==m'.Items && m==m'
    {EquivalenceMapMultisetRelation(m,mapToMultiset(m'.Items));
    EquivalenceMapMultisetRelation(m',mapToMultiset(m.Items));
    } 


  

class OrderedMultisetIteratorImplMap extends OrderedMultisetIterator{
  
  ghost var parent:OrderedMultisetImplMap;
  ghost var stackSK: seq<tree<TNode>>;//esto debería ser una Stack
  ghost var index:nat;

  var stack:seq<TNode>
  var numTraversed:nat; //from 0 to numTraversed have already been traversed of the current element
  

  constructor(p:OrderedMultisetImplMap)
  requires p.Valid()
  ensures Valid()
  { parent:=p;
    stack := [];
    stackSK:=[];
    numTraversed:=0;
    index:=0;
  }

  function Parent(): UnorderedMultiset
    reads this
    ensures Parent() is OrderedMultisetImplMap
  { parent } 

 function straversed():set<TNode>
      reads this,Parent(), Parent().Repr()
      requires Valid()
      requires stack !=[]
  {set n | n in elems(parent.tree.skeleton) && n.key < stack[0].key :: n}
  
  /*function notYetTraversed():set<TNode>
      reads this,Parent(), Parent().Repr()
  { set n | n in elems(parent.tree.skeleton) && n.key > stack[0].key}*/

  function current():TNode
   reads this,Parent(), Parent().Repr()
   requires stack != [] 
  { stack[0]}

  function nodesStack():set<TNode>
      reads this
      requires stack!=[]
  { set p | p in stack[1..] :: p}

/*  function reachableFromStack():set<TNode>
  { nodesStack()+
    unions(set p | p in stackSK :: elems(p.right))}
  */
 /*function leftPathAux(n:TNode,sk:tree<TNode>,ac:seq<TNode>):seq<TNode>
  reads set x | x in elems(sk)+{n} :: x`key
  reads  set x | x in ac 
   requires n in elems(sk)
   {
     match sk {
       case Node(l,x,r) => 
          if (n==x) then [n]+ac
          else if (n.key<x.key) then leftPathAux(n,l,[x]+ac)
          else leftPathAux(n,r,ac)
     }
   }*/




  function unions<A> (ss:set<set<A>>):set<A>
  {
    if (ss=={}) then {}
    else 
     var s:| s in ss;
     s+unions(ss-{s})
  }

  
  function method inorderKeysR(t: tree<TNode>): seq<int>
  reads set x | x in elems(t) :: x`key
  {
   match t {
    case Empty => []
    case Node(l, x, r) => [x.key] + inorderKeys(r)
   }
  }
  function method inorderKeys(t: tree<TNode>): seq<int>
  reads set x | x in elems(t) :: x`key
  {
   match t {
    case Empty => []
    case Node(l, x, r) => inorderKeys(l) + [x.key] + inorderKeys(r)
   }
  }
  function inorders(st:seq<tree<TNode>>):seq<int>
  reads set t,x | t in st && x in elems(t) :: x`key 
  {
   if (st==[]) then []
   else inorderKeysR(st[0])+inorders(st[1..])

  }

function fset2Seq(s:set<int>):seq<int> 
  decreases s
{
  if s == {} then []
  else 
    var y := Pick(s);
    [y] + fset2Seq(s - {y}) //mejor insertar ordenadamente 
}

function Pick(s: set<int>): int
  requires s != {}
{
  var x :| x in s; x
}
  
 /* function seqTraversed():seq<int>
      reads this,Parent(), Parent().Repr()
  { fset2Seq(set n | n in  elems(parent.tree.skeleton) && n.key < stack[0].key :: n.key)}
  */
  
  predicate Valid()
    reads this, Parent(), Parent().Repr()
  { parent.Valid() && 
    |stack|==|stackSK| &&  
    (forall i | 0 <= i < |stack| :: stack[i] in Parent().Repr()) &&
    (forall i | 0 <= i < |stackSK| :: elems(stackSK[i]) <= Parent().Repr()) && 
    (forall i | 0 <= i < |stack| :: Tree.ValidRec(stack[i],stackSK[i])) 
    /*&&
    //all disjoint 
    (set n | n in nodesStack())!! straversed() &&
    straversed()!!notYetTraversed() && 
    stack!=[] ==> current() !in straversed() && current() !in notYetTraversed() &&

    elems(parent.tree.skeleton)==straversed()+{current()}+notYetTraversed() &&
    notYetTraversed()==reachableFromStack() &&
    0 <= numTraversed < stack[0].value &&

    // secuencia ordenada de los ya recorridos+inorders(stackSK)==inorderKeys(parent.tree.skeleton)
    stack[..]==leftPathAux(stack[0],parent.tree.skeleton,[]) &&
    index==|straversed()|+numTraversed &&
    stack[0].key==elemth(parent.Model(),index)*/
  }


  function {:verify false} Traversed():multiset<int>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed()<=Parent().Model()
    ensures forall x,y | x in Traversed() && y in Parent().Model()-Traversed() :: x<=y
   /* {
      mapToMultiset((set n | n in straversed()::(n.key,n.value))+{(stack[0].key,numTraversed)})

    }*/

   //Several elements equal to the Peek may be in Traversed and some others not
  // Example: Model=={1,1,2,3,3,3,4,5} Traversed=={1,1,2,3,3} Peek=3 

  function method {:verify false} Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model() && (Parent().Model()-Traversed())[Peek()]>0
    ensures Peek()==elemth(Parent().Model(),|Traversed()|)
    ensures forall x | x in Traversed() :: x<=Peek()
    ensures forall x | x in Parent().Model()-Traversed() :: Peek()<=x 
  //{ stack[0].key}

  function method Index(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() ==> Index()==|Traversed()|
    ensures !HasNext() ==> Index()==|Parent().Model()|
   
  function method {:verify false} HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext()  <==> Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasNext() ==> Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
 // { stack!=[] }

  method Next() returns (x: int)
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
    ensures x==old(Peek()) && Traversed() == multiset{old(Peek())}+old(Traversed()) 
    ensures |Traversed()|==1+|old(Traversed())|
    ensures HasNext() ==> Peek()==elemth(Parent().Model(),|Traversed()|)//already known


    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek())))

  function method HasPrev(): bool//igual que HasNext
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasPrev()  <==> Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasPrev() ==> Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
  

  method Prev() returns (x: int)
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
    ensures x==old(Peek())  
    ensures old(Traversed())==multiset{} ==> Traversed()==Parent().Model()
    ensures old(Traversed())!=multiset{} ==> Traversed()==old(Traversed())-multiset{maximum(old(Traversed()))}
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek())))

  method Copy() returns (it: UnorderedMultisetIterator)
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
    
    ensures it is OrderedMultisetIterator
    ensures it.Valid()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()

    ensures Traversed() == it.Traversed() 
    ensures HasNext() ==> Peek()==it.Peek()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

  
}

class OrderedMultisetImplMap extends OrderedMultiset{
  
  var  tree:Tree;
  ghost var iters:set<OrderedMultisetIteratorImplMap>;


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
   && forall k | k in tree.MapModel():: tree.MapModel()[k]>0
  }  



  

  function Model(): multiset<int>
    reads this, Repr()
    requires Valid()
  {
    mapToMultiset(tree.MapModel().Items)
  }


  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == multiset{}
  {MapMultisetRelation(tree.MapModel());
   tree.isEmpty()
  }

  function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|
  //La suma de las multiplicidades

  function Iterators(): set<UnorderedMultisetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is OrderedMultisetIterator
    { {} }

  method First() returns (it: UnorderedMultisetIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures it is OrderedMultisetIterator
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed()==multiset{} 
    ensures Model()!=multiset{} ==> it.HasNext() && it.Peek()==elemth(Model(),0)
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))


  method Last() returns (it: OrderedMultisetIterator)//iterator to the last element
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
    ensures Model()!=multiset{} ==> it.HasNext() && it.Traversed()==Model()-multiset{elemth(Model(),|Model()|-1)} && it.Peek()==elemth(Model(),|Model()|-1)
    ensures Model()==multiset{} ==> it.Traversed()==multiset{}
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))
  
  function contains(x:int):bool
    reads this, Repr()
    requires Valid()
    ensures  contains(x) == (x in Model())

  method {:verify false} count(x:int) returns (c:int)
    modifies this,Repr()
    requires forall x | x in Repr() :: allocated(x)
    requires Valid()
    ensures Valid() 
    ensures c==Model()[x] 
    ensures Model()==old(Model())
    
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())

  {
    /*var b:=tree.Search(x);
    if (b) 
     { c:=tree.Get(x); }
   else 
     { c:=0; }*/
    //using Find
    var found:=tree.Find(x);
    if (found==null) 
       { c := 0; }
    else
       { c := found.value; }

    MapMultisetRelation(tree.MapModel());
  }
  
  method {:verify false} add(x:int)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + multiset{x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())
  {
   var c:=count(x);
   MapMultisetRelation(tree.MapModel());

   tree.Insert(x,c+1);

   MapMultisetRelation(tree.MapModel());
  }


  method find(x:int) returns (newt:UnorderedMultisetIterator )
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model()==old(Model())

    ensures newt is OrderedMultisetIterator
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent()==this
    ensures x in Model() ==> newt.HasNext() && newt.Traversed()==msmaller(Model(),x) && newt.Peek()==x //points to the first occurrence
    ensures x !in Model() ==> newt.Traversed()==Model()

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt}+old(Iterators())

  method insert(mid: UnorderedMultisetIterator, x: int) returns (newt:UnorderedMultisetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    //mid just a hint, it is inserted where corresponds
    //efficiently or not if it respects order
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + multiset{x}

    
    ensures newt is OrderedMultisetIterator
    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this
    ensures newt.HasNext() && 
            msmaller(Model(),x)<=newt.Traversed()<=msmaller(Model(),x)[x:=old(Model())[x]] &&
            newt.Peek()==x 
            //Example: 1,2,2,2,2,3 insert another 2 , Traversed may be 
            //{1} (newt points to the first 2), {1,2}, ..., {1,2,2,2,2} (newt points to the last 2)
    
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    //points either to the inserted elemento or to the already existing one



  method {:verify false} remove(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model()) - multiset{x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
  {
   /*var c:=count(x);
   MapMultisetRelation(tree.MapModel());
   if (c!=0) {
     var c:=tree.Get(x);
     if (c-1 != 0) 
        { tree.Insert(x,c-1); }
     else 
        {tree.Remove(x); }
    }*/

    var found:=tree.Find(x);
    
    MapMultisetRelation(tree.MapModel());
    
    if (found!=null)
    {
     if (found.value - 1 > 0) 
      {
        tree.Insert(x,found.value-1);
      }
     else 
      {
        tree.Remove(x);
      }

     }
   MapMultisetRelation(tree.MapModel());

  }

  method {:verify false} removeAll(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model())[x:=0] 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
   {   
     MapMultisetRelation(tree.MapModel());

     tree.Remove(x);
   
     MapMultisetRelation(tree.MapModel());

   }
  
  
  method erase(mid:UnorderedMultisetIterator) returns (next: UnorderedMultisetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model())-multiset{old(mid.Peek())}
    
    ensures next is OrderedMultisetIterator
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Traversed()==old(mid.Traversed())  &&
           (next.HasNext() ==> next.Peek()==elemth(Model(),|next.Traversed()|))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

}


