include "../../../src/Utils.dfy"


trait UnorderedMultisetIterator {
  function Parent(): UnorderedMultiset
    reads this

  predicate Valid()
    reads this, Parent(), Parent().Repr()

  function Traversed():multiset<int>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed()<=Parent().Model()
  
  function method Peek():int 
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model() && (Parent().Model()-Traversed())[Peek()]>0


  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext()  <==> Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasNext() ==> Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
  
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
    
    ensures it.Valid()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Traversed() == it.Traversed() && (it.HasNext() ==> Peek()==it.Peek())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

  
}

trait UnorderedMultiset {
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

  function Model(): multiset<int>
    reads this, Repr()
    requires Valid()

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == multiset{}

  function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|

  function Iterators(): set<UnorderedMultisetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

  method First() returns (it: UnorderedMultisetIterator)
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
    ensures it.Traversed()== multiset{} 
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

 

  function contains(x:int):bool
    reads this, Repr()
    requires Valid()
    ensures  contains(x) == (x in Model())

  method count(x:int) returns (c:int)
    modifies this,Repr()
    requires forall x | x in Repr() :: allocated(x)
    requires Valid()
    ensures Valid() && c==Model()[x] 

   ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
   ensures fresh(Repr()-old(Repr()))
   ensures forall x | x in Repr() :: allocated(x)
   
   ensures Iterators() == old(Iterators())

  method add(x:int)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + multiset{x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())



  method remove(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model()) - multiset{x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())

  method removeAll(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model())[x:=0] 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())


  method find(x:int) returns (newt:UnorderedMultisetIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model()==old(Model())
    
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent()==this
    ensures x in old(Model()) ==> newt.HasNext() && newt.Peek()==x
    ensures x !in old(Model()) ==> newt.Traversed()==Model()

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt}+old(Iterators())

  method insert(mid: UnorderedMultisetIterator, x: int) returns (newt:UnorderedMultisetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + multiset{x}

    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this  
    ensures newt.HasNext() && newt.Peek()==x 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    //points either to the inserted elemento or to the already existing one
 



  method erase(mid:UnorderedMultisetIterator) returns (next: UnorderedMultisetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model())- multiset{old(mid.Peek())}
    
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Traversed()==old(mid.Traversed()) 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

}

method {:verify false} main(s:UnorderedMultiset)
modifies s, s.Repr()
requires s.Valid() && s.Empty()
requires forall x | x in s.Repr() :: allocated(x)
ensures s.Valid()
ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)
{
 assert s.Model() == multiset{};
 s.add(2); s.add(4); s.add(6);
 assert s.Model() == multiset{2,4,6};
 var it := s.First();
 assert it.Traversed() == multiset{};
 //assert it.Peek()==4; //Falla, se sabe cual es traversed pero no Peek
 var cont:=0; 
  while (it.HasNext())
     decreases |s.Model()|-|it.Traversed()|
    //decreases |s.Model()-it.Model().0|
    //decreases s.Model()-it.Traversed()
     invariant it.Valid() && it.Parent()==s  
     invariant s.Valid()
     invariant  forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
     invariant fresh(s.Repr()-old(s.Repr()))
     invariant forall x | x in s.Repr() :: allocated(x)
    {
     var aux:=it.Next();
     if (aux%2==0) {cont:=cont+1;} 
    } 
  assert !it.HasNext();  
  assert it.Traversed()==s.Model();  
}

method {:verify false} otry(s:UnorderedMultiset)
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
 assert s.Model() == multiset{3,4};
 s.add(4);
 assert  s.Model() == multiset{3,4,4};
 s.remove(2);
  assert  s.Model() == multiset{3,4,4};
 s.remove(3);
  assert s.Model() == multiset{4,4};
 s.removeAll(4);
   assert s.Model() == multiset{};
 s.add(2); s.add(7); s.add(0); s.add(1);s.add(10);
 s.add(2); 
 var c:=s.count(2);
 var c':=s.count(25);
 assert c==2 && c'==0;
 
  var b:=s.contains(10);
 assert b;

  /* var s1:set<int>;
   var s2:set<int>;
   s1:={1,2,4};
   s2:={0,1,2,3,4,8};
   assert s1<=s2;
   assert |s1|<=|s2|;*/


  //var 
  var it2:=s.First();
  it2:=s.find(2);
  assert it2.Peek()==2 && it2.Peek()!=3;

  //var x:=it2.Next();
  it2:=s.erase(it2);
  
  it2:=s.insert(it2,3);
  assert it2.Peek()==3 && it2.Peek()!=2;

 
  var it3:=s.find(7);
  it3:=s.insert(it3,5);
  assert it3.Peek()==5;
  it3:=s.insert(it3,12);
  assert it3.Peek()==12;
  var aux:=it3.Next();
   assert 12 in it3.Traversed();
   
}