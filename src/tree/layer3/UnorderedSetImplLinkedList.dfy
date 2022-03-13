include "../../../src/tree/layer2/UnorderedSetLinkedList.dfy"
include "../../../src/linear/layer3/LinkedListImpl.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"




class UnorderedSetIteratorImplLinkedList extends UnorderedSetIterator {
  var iter:LinkedListIteratorImpl;
  ghost var parent:UnorderedSetImpl;

  constructor (it:LinkedListIteratorImpl,ghost p:UnorderedSetImpl)
    requires p.Valid()
    requires it.Valid()  && it in p.Repr()
    requires it in p.elems.Iterators() && it.Parent()==p.elems
    requires forall itp | itp in p.iters :: (itp as UnorderedSetIteratorImpl).iter!=it
    ensures Valid()
    ensures iter==it && parent==p
  { 
    iter:=it;
    //ghost
    parent:=p;
  }

  
  
  function Parent(): UnorderedSet
    reads this
    ensures Parent() is UnorderedSetImpl
  {
      parent
  }

  predicate Valid()
    reads this, Parent(), Parent().Repr()
  { iter in Parent().Repr() && 
    iter.Parent() == parent.elems &&
    parent.Valid() && iter.Valid() &&
    iter in parent.elems.Iterators() &&
    forall it | it in parent.iters && it != this :: (it as UnorderedSetIteratorImpl).iter!=iter 
    //Duda this in parent.iters
  }

  function Traversed():set<int>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed() <= Parent().Model()
   // ensures Traversed() == set x | x in parent.elems.Model()[..iter.Index()]
  { 
    seq2Set(parent.elems.Model()[..iter.Index()])
  }  
  
  function method Peek():int 
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model() && Peek() !in Traversed()
   // ensures Peek()==parent.elems.Model()[iter.Index()]
  { 
    iter.Peek()
  }


  lemma {:verify false} HasNextTraversed()
  requires Valid()
  requires Parent().Valid()
  requires iter.HasNext() 
  ensures Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
  {
   assert 0 <= iter.Index() < |parent.elems.Model()|;
   assert seq2SetContained(parent.elems.Model(),0,iter.Index());
   assert Traversed() == seq2Set(parent.elems.Model()[..iter.Index()]) < seq2Set(parent.elems.Model());
   sizesStrictContained(seq2Set(parent.elems.Model()[..iter.Index()]),seq2Set(parent.elems.Model()));
   assert |Traversed()| < |Parent().Model()|;
   }

  lemma {:verify false} NotHasNextTraversed()
  requires Valid()
  requires Parent().Valid()
  requires !iter.HasNext() 
  ensures Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
  {
   assert iter.Index()<=|parent.elems.Model()|;
   assume iter.HasNext() <==> iter.Index()<|parent.elems.Model()|;
   assert iter.Index() == |parent.elems.Model()|;
  }

 lemma {:verify false} HasNext?Traversed()
 requires Valid()
  requires Parent().Valid()
  ensures iter.HasNext() ==> Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
  ensures !iter.HasNext() ==> Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
  {if (iter.HasNext()) {HasNextTraversed();}
   else {NotHasNextTraversed();}
  }


  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext()  <==> Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasNext() ==> Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
  { 
    HasNext?Traversed();
    iter.HasNext()
  }
  
  method Next() returns (x: int)
    modifies this, Parent(), Parent().Repr()
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

    ensures x==old(Peek()) && Traversed() == {old(Peek())}+old(Traversed()) 
    
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek())))
  {
       // assert Parent().Valid();
       // assert forall it1, it2 | it1 in parent.iters && it2 in parent.iters && it1!=it2 :: it1.iter!=it2.iter;
       // assert forall it1 | it1 in parent.iters && it1!=this :: it1.iter!=iter;
        //assert forall it | it in old(Parent().Iterators()) && it != this ::  (it as UnorderedSetIteratorImpl).iter!=iter;

    x:=iter.Next();
    
  }

  

  method Copy() returns (it: UnorderedSetIterator)
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
    
    ensures it is UnorderedSetIteratorImpl
    ensures it.Valid() 
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Traversed() == it.Traversed() && (it.HasNext() ==> Peek()==it.Peek())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

  { 
    var listIter:LinkedListIteratorImpl:=iter.Copy();
    it:=new UnorderedSetIteratorImpl(listIter,parent);

    parent.iters:={it}+parent.iters;
    
    
  }
}

class UnorderedSetImpl extends UnorderedSetLinkedList {

  var elems:LinkedListImpl;
  ghost var iters:set<UnorderedSetIteratorImplLinkedList>
  
  function Repr0(): set<object>
    reads this
  {
    {elems} + iters 
  }

 function Repr1(): set<object>
    reads this, Repr0()
  {
    Repr0()+ (set it | it in iters::it.iter) 
  }

  function ReprDepth(): nat
    reads this
    ensures ReprDepth() > 0
  {  
    elems.ReprDepth() + 2
  }

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= ReprDepth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)
    {
    if n == 0 then
      Repr0()
    else if (n==1) then
      Repr1()
    else 
      Repr1() + elems.ReprFamily(n-2)
    
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth())
    {}


  constructor()
    ensures Valid()
    ensures Model() == {}
    ensures forall x | x in Repr() :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    elems:=new LinkedListImpl();
    iters:={};
    new;
      //assert forall x {:trigger x in elems.Repr()}| x in elems.Repr() :: fresh(x);
      forall n {:induction n} | 0<=n<=ReprDepth() 
      ensures (forall x | x in ReprFamily(n) :: fresh(x)){
        if (n==0){assert forall x | x in Repr0() :: fresh(x);}
        else if (n==1) {assert forall x | x in Repr1() :: fresh(x);}
        else {assert forall x | x in elems.Repr() :: fresh(x);}
      }

  }
  

  predicate Valid()
    reads this, Repr()
  {
    elems.Valid() &&
    isSet(elems.Model()) &&
    (forall it | it in iters ::  it.iter in elems.Iterators() && it.Parent()==this) &&
    (forall it1, it2 | it1 in iters && it2 in iters && it1 != it2:: it1.iter != it2.iter) 
  }

  function Model(): set<int>
    reads this, Repr()
    requires Valid()
  {
    seq2Set(elems.Model())
  }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == {}
  {
       emptyset(elems.Model());

     elems.Empty()

  }

  function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|
  {
      sizesSeq2Set(elems.Model());
   
   elems.Size()

  }

  function Iterators(): set<UnorderedSetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is UnorderedSetIteratorImpl
  { iters }

  method {:verify true} First() returns (it: UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures it is UnorderedSetIteratorImpl
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed()=={} 
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))
  { 
    var listIter:LinkedListIteratorImpl:=elems.Begin();

    it := new UnorderedSetIteratorImpl(listIter,this);

    assert forall it1 | it1 in iters :: it!=it1 && it1.iter != (it as UnorderedSetIteratorImpl).iter;

    iters:={it}+iters;
    
  }
 

  method {:verify false} contains(x:int) returns (b:bool)
   modifies Repr()
   requires Valid()
   ensures Valid() && Model()==old(Model())
   ensures b==(x in Model())
   
   ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
   ensures fresh(Repr()-old(Repr()))
   ensures forall x | x in Repr() :: allocated(x)
   
   ensures Iterators() == old(Iterators())
   ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && 
      it.Traversed() == old(it.Traversed()) && 
      (it.HasNext() ==> it.Peek()==old(it.Peek()))

 
  {

    var aux:LinkedListIteratorImpl := elems.Begin(); var y:int;
    while (aux.HasNext() && aux.Peek()!=x)
      decreases |elems.Model()|-aux.Index()
      invariant Valid() &&  Model()==old(Model())
      invariant aux.Valid() && aux in elems.Iterators() && aux.Parent()==elems
      invariant 0<=aux.Index()<=|elems.Model()| 
      invariant aux.HasNext() ==> aux.Index()<|elems.Model()| && aux.Peek()==elems.Model()[aux.Index()]
      
      invariant forall z | z in elems.Model()[..aux.Index()]:: z!=x
      invariant forall z {:trigger z in elems.Repr(), z in old(elems.Repr())} | z in elems.Repr() - old(elems.Repr()) :: fresh(z)
      invariant forall z | z in elems.Repr() :: allocated(x)
      
      invariant forall it | it in old(Iterators()) && old(it.Valid()) :: (it as UnorderedSetIteratorImpl).iter!=aux
      invariant forall it | it in old(Iterators()) && old(it.Valid()) ::
         it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

    {
    
    assert elems.Model()[..aux.Index()+1]==elems.Model()[..aux.Index()]+[elems.Model()[aux.Index()]];
     y:=aux.Next();     
    }
    assert  !aux.HasNext() ==> aux.Index()==|elems.Model()| && elems.Model()[..aux.Index()]==elems.Model();
    b:=aux.HasNext();
  }

  

  method {:verify false} add(x:int)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + {x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())
   ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() &&
      (if !old(it.HasNext()) then
          it.Traversed() == Model()
      else
          it.Traversed() == old(it.Traversed()) &&
          it.HasNext() && 
          it.Peek()==old(it.Peek()))
     
  {
    var b := contains(x);
    if (!b) {elems.PushBack(x);}
  }


  method {:verify false} remove(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model()) - {x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) 
             && (!old(it.HasNext()) || (old(it.HasNext()) && old(it.Peek())!=x) )::
      it.Valid() && 
      it.Traversed() == old(it.Traversed())-{x} &&
      (it.HasNext() && old(it.Peek())!=x ==> it.Peek()==old(it.Peek()))
  
    {
      var aux:LinkedListIteratorImpl := elems.Begin(); var y:int;
    while (aux.HasNext() && aux.Peek()!=x)
      decreases |elems.Model()|-aux.Index()
      invariant Valid() &&  Model()==old(Model())
      invariant aux.Valid() && aux in elems.Iterators() && aux.Parent()==elems
      invariant 0<=aux.Index()<=|elems.Model()| 
      invariant aux.HasNext() ==> aux.Index()<|elems.Model()| && aux.Peek()==elems.Model()[aux.Index()]
      invariant forall z | z in elems.Model()[..aux.Index()]:: z!=x
      invariant forall z {:trigger z in elems.Repr(), z in old(elems.Repr())} | z in elems.Repr() - old(elems.Repr()) :: fresh(z)
      invariant forall z | z in elems.Repr() :: allocated(x)
      invariant Iterators() == old(Iterators())
      invariant forall it | it in old(Iterators()) && old(it.Valid()) :: it.Valid() && 
           it.Traversed() == old(it.Traversed()) &&
           (it.HasNext() ==> it.Peek()==old(it.Peek()))
    {
    
    assert elems.Model()[..aux.Index()+1]==elems.Model()[..aux.Index()]+[elems.Model()[aux.Index()]];
     y:=aux.Next();     
    }
    assert  !aux.HasNext() ==> aux.Index()==|elems.Model()| && elems.Model()[..aux.Index()]==elems.Model();
   // assert aux.HasNext() ==> aux.Peek()==x;
    if (aux.HasNext()) {aux:=elems.Erase(aux);}


    }
  

  method {:verify false} find(x:int) returns (newt:UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model()==old(Model())
    
    ensures fresh(newt) && newt is UnorderedSetIteratorImpl
    ensures newt.Valid() && newt.Parent()==this
    ensures x in old(Model()) ==> newt.HasNext() && newt.Peek()==x
    ensures x !in old(Model()) ==> newt.Traversed()==Model()

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt}+old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && 
      it.Traversed() == old(it.Traversed()) &&
      (it.HasNext() ==> it.Peek()==old(it.Peek()))

  {

    var aux:LinkedListIteratorImpl := elems.Begin(); var y:int;

    while (aux.HasNext() && aux.Peek()!=x)
      decreases |elems.Model()|-aux.Index()
      invariant Valid() &&  Model()==old(Model())
      invariant aux.Valid() && aux in elems.Iterators() && aux.Parent()==elems
      invariant 0<=aux.Index()<=|elems.Model()| 
      invariant aux.HasNext() ==> aux.Index()<|elems.Model()| && aux.Peek()==elems.Model()[aux.Index()]
      invariant forall z | z in elems.Model()[..aux.Index()]:: z!=x
     
      invariant forall z {:trigger z in elems.Repr(), z in old(elems.Repr())} | z in elems.Repr() - old(elems.Repr()) :: fresh(z)
      invariant forall z | z in elems.Repr() :: allocated(x)
      invariant Iterators() == old(Iterators())
     
      invariant forall itp | itp in iters :: (itp as UnorderedSetIteratorImpl).iter!=aux
      invariant forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

    {
    
    assert elems.Model()[..aux.Index()+1]==elems.Model()[..aux.Index()]+[elems.Model()[aux.Index()]];
     y:=aux.Next();     
    }

    newt := new UnorderedSetIteratorImpl(aux,this);
    
    iters:={newt}+iters;

  }

  method {:verify false} insert(mid: UnorderedSetIterator, x: int) returns (newt:UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + {x}

    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this  
    ensures newt.HasNext() && newt.Peek()==x 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() &&
      (if !old(it.HasNext()) then
          it.Traversed() == Model()
      else
          it.Traversed() == old(it.Traversed()) &&
          it.HasNext() && it.Peek()==old(it.Peek()))
     
  {
    newt := find(x);
    if (!newt.HasNext()) {
       (newt as UnorderedSetIteratorImpl).iter:=elems.Insert((newt as UnorderedSetIteratorImpl).iter,x);} 


  }
 



  method {:verify true} erase(mid:UnorderedSetIterator) returns (next: UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model())-{old(mid.Peek())}
    
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Traversed()==old(mid.Traversed()) 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
    ensures forall it | it in old(Iterators()) && old(it.Valid()) 
             && (!old(it.HasNext()) || (old(it.HasNext()) && old(it.Peek())!=old(mid.Peek())) )::
      it.Valid() && 
      it.Traversed() == old(it.Traversed())-{old(mid.Peek())} &&
      (it.HasNext() && old(it.Peek())!=old(mid.Peek()) ==> it.Peek()==old(it.Peek()))
 
{
    var newt:LinkedListIteratorImpl:=elems.Erase((mid as UnorderedSetIteratorImpl).iter);
    assert forall itp | itp in iters :: (itp as UnorderedSetIteratorImpl).iter!=newt;
    next := new UnorderedSetIteratorImpl(newt,this);
    
    forall it | it in old(Iterators()) && old(it.Valid()) 
             && (!old(it.HasNext()) || (old(it.HasNext()) && old(it.Peek())!=old(mid.Peek())) )
    ensures it.Valid() && 
      it.Traversed() == old(it.Traversed())-{old(mid.Peek())} &&
      (it.HasNext() && old(it.Peek())!=old(mid.Peek()) ==> it.Peek()==old(it.Peek()))
    {

     assert it.Valid();

    var index:= (it as UnorderedSetIteratorImpl).iter.Index(); 
    var oindex:= old((it as UnorderedSetIteratorImpl).iter.Index()); 
    var midindex:=old((mid as UnorderedSetIteratorImpl).iter.Index());
    if (oindex <  midindex) 
       { 
         assert index==oindex;
         assert elems.Model()[..index]==old(elems.Model())[..oindex];
         assert old(mid.Peek()) !in elems.Model()[..index];
         assert seq2Set(elems.Model()[..index])==seq2Set(old(elems.Model()[..oindex]));
         assert old(it.Traversed())-{old(mid.Peek())}==old(it.Traversed());
         assert it.Traversed() == old(it.Traversed())-{old(mid.Peek())};

       }
    else 
       {
         assert index==oindex-1;
         assert old(mid.Peek()) in old(it.Traversed());
         assert seq2Set(elems.Model()[..index])==seq2Set(old(elems.Model()[..oindex]))-{old(mid.Peek())};
       
       }



     assert it.Traversed() == old(it.Traversed())-{old(mid.Peek())};
     assume (it.HasNext() && old(it.Peek())!=old(mid.Peek()) ==> it.Peek()==old(it.Peek()));
   

    }
    




    iters:={next}+iters;
}
}


