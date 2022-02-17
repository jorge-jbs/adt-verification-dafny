include "../../../src/Utils.dfy"


trait UnorderedSetIterator {
  function Parent(): UnorderedSet
    reads this

  predicate Valid()
    reads this, Parent(), Parent().Repr()

  function Model(): (set<int>,int) //already traversed elements+ maybe elem
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures {} <=Model().0 <=Parent().Model()
    ensures Model().0 < Parent().Model() ==> 
             Model().1 in  Parent().Model() && Model().1 !in Model().0 

  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() ==> Model().0 < Parent().Model() && |Model().0| < |Parent().Model()|
    ensures !HasNext() ==> Model().0 == Parent().Model() && |Model().0| == |Parent().Model()|
  /*function method HasPrev(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasPrev() <==> Model().0 != {}*/

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

    ensures x==old(Model().1) && {old(Model().1)}+old(Model().0)==Model().0 //> old(Model().0)
    ensures HasNext() ==> Model().1 in Parent().Model() && Model().1 !in Model().0
    
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Model() == old(it.Model()))


  function method Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() == Model().1

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
    
    ensures it.Valid()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Model() == it.Model()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Model() == old(it.Model())

  
}

trait UnorderedSet {
  function ReprDepth(): nat
    ensures ReprDepth() > 0

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= ReprDepth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)

  function Repr(): set<object>
    reads this, ReprFamily(ReprDepth()-1)
  {
    ReprFamily(ReprDepth())
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());

  predicate Valid()
    reads this, Repr()

  function Model(): set<int>
    reads this, Repr()
    requires Valid()

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == {}

  function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|

  function Iterators(): set<UnorderedSetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

method First() returns (it: UnorderedSetIterator)
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
    ensures it.Model().0=={} && (Model()!={}==> it.Model().1 in Model())
    ensures it.Parent() == this
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Model() == old(it.Model())

 

  method contains(x:int) returns (b:bool)
    requires Valid()
    ensures Valid() && b == (x in Model())

  method add(x:int)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + {x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())



  method remove(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model()) - {x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())


  method find(x:int) returns (newt:UnorderedSetIterator)
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent()==this
    ensures x in Model() ==> newt.Model().0=={} && newt.Model().1==x
    ensures x !in Model() ==> newt.Model().0==Model()

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
    ensures Iterators() == {newt}+old(Iterators())

  method insert(mid: UnorderedSetIterator, x: int) returns (newt:UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + {x}

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this && newt.HasNext()
    ensures newt.Model().0==(old(mid.Model().0)-{x}) && newt.Model().1==x //??DUDA
    //points either to the inserted elemento or to the already existing one
 


  method erase(mid:UnorderedSetIterator) returns (next: UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model())-{old(mid.Model().1)}
    
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Model().0==old(mid.Model().0) && 
       (Model()!={} ==> next.Model().1 in Model() && next.Model().1 !in next.Model().0)
}



method {:verify true} try(s:UnorderedSet)
modifies s, s.Repr()
requires s.Valid() && s.Empty()
requires forall x | x in s.Repr() :: allocated(x)
ensures s.Valid()
ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)
{
 s.add(3);
 s.add(4);
 assert 3 in s.Model();
 assert 4 in s.Model();
 assert (set x | x in s.Model()) == {3,4};
 s.add(4);
 assert (set x | x in s.Model()) == {3,4};
 s.remove(2);
  assert (set x | x in s.Model()) == {3,4};
 s.remove(3);
  assert (set x | x in s.Model()) == {4};
 s.remove(4);
   assert (set x | x in s.Model()) == {};
 s.add(2); s.add(7); s.add(0); s.add(1);s.add(10);

 var b:=s.contains(10);
 assert b;

   var s1:set<int>;
   var s2:set<int>;
   s1:={1,2,4};
   s2:={0,1,2,3,4,8};
   assert s1<=s2;
   assert |s1|<=|s2|;


 var it:=s.First(); var cont:=0; /*ghost var omodel:=s.Model();
 assert |it.Model().0|<=|s.Model()|;
assert !it.HasNext() ==> |it.Model().0|==|s.Model()|;
assert |s.Model()|-|it.Model().0|>=0;*/
  while (it.HasNext())
     decreases |s.Model()|-|it.Model().0|
     invariant it.Valid() && it.Parent()==s  
     invariant s.Valid()
     invariant  forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
     invariant fresh(s.Repr()-old(s.Repr()))
     invariant forall x | x in s.Repr() :: allocated(x)
    {
     var aux:=it.Next();
     if (aux%2==0) {cont:=cont+1;} 
    } 
  var it2:=s.find(2);
  assert it2.Model().1==2;
  it2:=s.find(7); 
  assert it.Model().1==7;  
  var aux:=it.Next();
  assert aux==7;assert it.Model().0=={2,7,1,0,10};
  
  var it3:=s.find(7);
  it3:=s.insert(it3,5);
  assert it3.Model().1==5;
  it3:=s.insert(it3,12);
  assert it3.Model().1==12;
  assert it3.Model().0=={};
   aux:=it3.Next();
   assert 12 in it3.Model().0;
   aux:=it3.Next();
   assert 12 in it3.Model().0;
}