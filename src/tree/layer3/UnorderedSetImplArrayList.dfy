include "../../../src/tree/layer1/OrderedSetUtils.dfy"
include "../../../src/tree/layer2/UnorderedSetArrayList.dfy"
include "../../../src/linear/layer3/ArrayListImpl.dfy"


class UnorderedSetIteratorImplArrayList extends UnorderedSetIterator {
  var iter:ArrayListIteratorImpl//ListIterator1;
  ghost var parent:UnorderedSetImplArrayList;

  constructor (it:ArrayListIteratorImpl/*ListIterator1*/,ghost p:UnorderedSetImplArrayList)
    requires p.Valid()
    requires it.Valid()  && it in p.Repr()
    requires it in p.elems.Iterators() && it.Parent()==p.elems
    requires forall itp | itp in p.iters :: (itp as UnorderedSetIteratorImplArrayList).iter!=it
    ensures Valid()
    ensures iter==it && parent==p
  { 
    iter:=it;
    //ghost
    parent:=p;
  }

  
  function Parent(): UnorderedSet
    reads this
    ensures Parent() is UnorderedSetImplArrayList
  {
      parent
  }

  predicate Valid()
    reads this, Parent(), Parent().Repr()
  { iter in Parent().Repr() && 
    iter.Parent() == parent.elems &&
    parent.Valid() && iter.Valid() &&
    iter in parent.elems.Iterators() &&
    forall it | it in parent.iters && it != this :: (it as UnorderedSetIteratorImplArrayList).iter!=iter 
    //this in parent.iters
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


  lemma {:verify true} HasNextTraversed()
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

  lemma {:verify true} NotHasNextTraversed()
  requires Valid()
  requires Parent().Valid()
  requires !iter.HasNext() 
  ensures Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
  {
   assert iter.Index()<=|parent.elems.Model()|;
   assert iter.HasNext() <==> iter.Index()<|parent.elems.Model()|;
   assert iter.Index() == |parent.elems.Model()|;
  }

 lemma {:verify true} HasNext?Traversed()
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
    
    ensures it is UnorderedSetIteratorImplArrayList
    ensures it.Valid() 
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Traversed() == it.Traversed() && (it.HasNext() ==> Peek()==it.Peek())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

  { 
    var listIter:ArrayListIteratorImpl:=iter.Copy();
    it:=new UnorderedSetIteratorImplArrayList(listIter,parent);

    parent.iters:={it}+parent.iters;
    
    
  }
}

class UnorderedSetImplArrayList extends UnorderedSetArrayList {

  var elems:ArrayListImpl//List1;
  ghost var iters:set<UnorderedSetIteratorImplArrayList>
  
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
    elems:=new ArrayListImpl();//new List1();
    iters:={};
    new;
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
  { iters }

  method First() returns (it: UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures it is UnorderedSetIteratorImplArrayList
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed()=={} 
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))
  { 
    var listIter:ArrayListIteratorImpl/*ListIterator1*/:=elems.Begin();

    it := new UnorderedSetIteratorImplArrayList(listIter,this);

    assert forall it1 | it1 in iters :: it!=it1 && it1.iter != (it as UnorderedSetIteratorImplArrayList).iter;

    iters:={it}+iters;
    
  }
 

  method contains(x:int) returns (b:bool)
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

    var aux:ArrayListIteratorImpl := elems.Begin(); var y:int;
    while (aux.HasNext() && aux.Peek()!=x)
      decreases |elems.Model()|-aux.Index()
      invariant Valid() &&  Model()==old(Model())
      invariant aux.Valid() && aux in elems.Iterators() && aux.Parent()==elems 
      invariant 0<=aux.Index()<=|elems.Model()| 
      invariant aux.HasNext() ==> aux.Index()<|elems.Model()| && aux.Peek()==elems.Model()[aux.Index()]
      invariant forall z | z in elems.Model()[..aux.Index()]:: z!=x
      
      invariant forall z {:trigger z in elems.Repr(), z in old(elems.Repr())} | z in elems.Repr() - old(elems.Repr()) :: fresh(z)
      invariant forall z | z in elems.Repr() :: allocated(x)
      
      invariant Iterators()==old(Iterators())
      invariant forall it | it in old(Iterators()) && old(it.Valid()) :: (it as UnorderedSetIteratorImplArrayList).iter!=aux
      invariant  forall it | it in old(Iterators()) && old(it.Valid()) ::
        it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

    {
    
    assert elems.Model()[..aux.Index()+1]==elems.Model()[..aux.Index()]+[elems.Model()[aux.Index()]];
     y:=aux.Next();     
    }
    assert  !aux.HasNext() ==> aux.Index()==|elems.Model()| && elems.Model()[..aux.Index()]==elems.Model();
    b:=aux.HasNext();
  }

  

  method {:verify true} add(x:int)
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
      it.Valid() && it.Traversed() == old(it.Traversed()) &&
      (it.HasNext() ==> (if (it.Traversed()!=old(Model())) 
                          then it.Peek()==old(it.Peek())
                          else it.Peek()==x))

  {
    var b := contains(x);
    if (!b) {elems.PushBack(x);}
  }


  method {:verify true} remove(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model()) - {x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext())  ::
      it.Valid() && 
      if (x !in old(it.Traversed())) then  
           it.Traversed()==old(it.Traversed()) && (it.HasNext() && old(it.Peek())!=x ==> it.Peek()==old(it.Peek()))
      else      
           it.Traversed() == old(it.Traversed())+{old(it.Peek())}-{x}

    {
      var aux:ArrayListIteratorImpl := elems.Begin(); var y:int;
    while (aux.HasNext() && aux.Peek()!=x)
      decreases |elems.Model()|-aux.Index()
      invariant Valid() &&  Model()==old(Model()) && elems.Model()==old(elems.Model())
      invariant aux.Valid() && aux in elems.Iterators() && aux.Parent()==elems
      invariant 0<=aux.Index()<=|elems.Model()|==|old(elems.Model())| 
      invariant aux.HasNext() ==> aux.Index()<|elems.Model()| && aux.Peek()==elems.Model()[aux.Index()]
     
      invariant forall z | z in elems.Model()[..aux.Index()]:: z!=x
      invariant forall z {:trigger z in elems.Repr(), z in old(elems.Repr())} | z in elems.Repr() - old(elems.Repr()) :: fresh(z)
      invariant forall z | z in elems.Repr() :: allocated(x)
     
      invariant Iterators() == old(Iterators())
      invariant forall it | it in old(Iterators()) && old(it.Valid()) :: (it as UnorderedSetIteratorImplArrayList).iter!=aux
      invariant forall it | it in old(Iterators()) && old(it.Valid()) :: it.Valid() && it.Traversed() == old(it.Traversed()) &&
                  (it.HasNext() ==> it.Peek()==old(it.Peek()))
      invariant forall it | it in old(Iterators()) && old(it.Valid()) :: (it as UnorderedSetIteratorImplArrayList).iter.Index()==old((it as UnorderedSetIteratorImplArrayList).iter.Index());
             
    {
    
    assert elems.Model()[..aux.Index()+1]==elems.Model()[..aux.Index()]+[elems.Model()[aux.Index()]];
     y:=aux.Next();     
    }
    assert  !aux.HasNext() ==> aux.Index()==|elems.Model()| && elems.Model()[..aux.Index()]==elems.Model();
   // assert aux.HasNext() ==> aux.Peek()==x;
   assert forall it | it in old(Iterators()) && old(it.Valid()) :: (it as UnorderedSetIteratorImplArrayList).iter.Index()==old((it as UnorderedSetIteratorImplArrayList).iter.Index());
   
    if (aux.HasNext()) {
       
      var auxindex:=aux.Index();
      var model:=elems.Model();

       aux:=elems.Erase(aux);
      forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext())  
      ensures it.Valid() &&
        if (x !in old(it.Traversed())) then  
           it.Traversed()==old(it.Traversed()) && (it.HasNext() && old(it.Peek())!=x==> it.Peek()==old(it.Peek()))
        else      
           it.Traversed() == old(it.Traversed())+{old(it.Peek())}-{x}
      { assert it.Valid();
      
        var index:= (it as UnorderedSetIteratorImplArrayList).iter.Index(); 
        var oindex:= old((it as UnorderedSetIteratorImplArrayList).iter.Index()); 
        assert index==oindex;
      
        assert it.Traversed()==seq2Set(elems.Model()[..index]);
        assert elems.Model()==Seq.Remove(model, auxindex);
        assert auxindex<|old(elems.Model())|;

      if (x !in old(it.Traversed()))
       { 
         assert auxindex>=index;
         assert elems.Model()[..index]==old(elems.Model())[..oindex];
         assert x !in elems.Model()[..index];
         assert seq2Set(elems.Model()[..index])==seq2Set(old(elems.Model()[..oindex]));
         assert it.Traversed()==old(it.Traversed());
         assert (it.HasNext() && old(it.Peek())!=x ==> it.Peek()==old(it.Peek()));
       
       }
      else 
       { 
         assert oindex > auxindex;
         subseq2SetRemoveL(old(elems.Model()),auxindex,oindex);
        assert it.Traversed() == old(it.Traversed())+{old(it.Peek())}-{x}; 

          } 
    }
  }
}
  

  method {:verify true} find(x:int) returns (newt:UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model()==old(Model())
    
    ensures fresh(newt) && newt is UnorderedSetIteratorImplArrayList
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

    var aux:ArrayListIteratorImpl := elems.Begin(); var y:int;

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
     
      invariant Iterators() == old(Iterators())
      invariant forall itp | itp in old(Iterators()) :: (itp as UnorderedSetIteratorImplArrayList).iter!=aux
      invariant forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

    {
    
    assert elems.Model()[..aux.Index()+1]==elems.Model()[..aux.Index()]+[elems.Model()[aux.Index()]];
     y:=aux.Next();     
    }

    newt := new UnorderedSetIteratorImplArrayList(aux,this);
    
    iters:={newt}+iters;

  }

  method {:verify true} insert(mid: UnorderedSetIterator, x: int) returns (newt:UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + {x}

    ensures fresh(newt) && newt is UnorderedSetIteratorImplArrayList
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this  
    ensures newt.HasNext() && newt.Peek()==x 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && 
      it.Traversed() == old(it.Traversed()) &&
      (it.HasNext() ==> (if (it.Traversed()!=old(Model())) 
                          then it.Peek()==old(it.Peek())
                          else it.Peek()==x))

  
  {
    newt := find(x);
    if (!newt.HasNext()) {
       (newt as UnorderedSetIteratorImplArrayList).iter:=elems.Insert((newt as UnorderedSetIteratorImplArrayList).iter,x);} 


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

    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext())  ::
      it.Valid() && 
      if (old(mid.Peek()) !in old(it.Traversed())) then  
           it.Traversed()==old(it.Traversed()) && (it.HasNext() && old(it.Peek())!=old(mid.Peek()) ==> it.Peek()==old(it.Peek()))
      else      
           it.Traversed() == old(it.Traversed())+{old(it.Peek())}-{old(mid.Peek())}
{
    var newt:ArrayListIteratorImpl:=elems.Erase((mid as UnorderedSetIteratorImplArrayList).iter);
    assert forall itp | itp in iters :: (itp as UnorderedSetIteratorImplArrayList).iter!=newt;
    next := new UnorderedSetIteratorImplArrayList(newt,this);
    
    forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext())  
     ensures it.Valid() &&
      if (old(mid.Peek()) !in old(it.Traversed())) then  
           it.Traversed()==old(it.Traversed()) && (it.HasNext() && old(it.Peek())!=old(mid.Peek()) ==> it.Peek()==old(it.Peek()))
      else      
           it.Traversed() == old(it.Traversed())+{old(it.Peek())}-{old(mid.Peek())}
    { assert it.Valid();
      
      var index:= (it as UnorderedSetIteratorImplArrayList).iter.Index(); 
      var oindex:= old((it as UnorderedSetIteratorImplArrayList).iter.Index()); 
      var midindex:=old((mid as UnorderedSetIteratorImplArrayList).iter.Index());
      assert index==oindex;
      
      assert it.Traversed()==seq2Set(elems.Model()[..index]);
      assert elems.Model()==Seq.Remove(old(elems.Model()), midindex);
      assert midindex<|old(elems.Model())|;

      if (old(mid.Peek()) !in old(it.Traversed()))
       { 
         assert midindex>=index;
         assert elems.Model()[..index]==old(elems.Model())[..oindex];
         assert old(mid.Peek()) !in elems.Model()[..index];
         assert seq2Set(elems.Model()[..index])==seq2Set(old(elems.Model()[..oindex]));
         assert it.Traversed()==old(it.Traversed());
         assert (it.HasNext() && old(it.Peek())!=old(mid.Peek()) ==> it.Peek()==old(it.Peek()));
       
       }
      else 
       { 
         assert oindex > midindex;
         subseq2SetRemoveL(old(elems.Model()),midindex,oindex);
        assert it.Traversed() == old(it.Traversed())+{old(it.Peek())}-{old(mid.Peek())}; 

          } 
    }

    iters:={next}+iters;
}
}


