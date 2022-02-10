include "../../../src/Utils.dfy"

function isSortedSet(xs:seq<int>):bool
{forall i,j::0<=i<j<|xs| ==> xs[i]<xs[j]}


function isSubSet(xs:seq<int>,ys:seq<int>):bool
requires isSortedSet(xs) && isSortedSet(ys)
ensures isSubSet(xs,ys) == ((set x | x in xs) <= (set y | y in ys))

lemma lSubSet(xs:seq<int>,ys:seq<int>,i:int)
requires 0<=i<=|ys| && isSortedSet(xs) && isSortedSet(ys)
ensures isSubSet(xs,ys[..i]) ==> isSubSet(xs,ys)
ensures !isSubSet(xs,ys[..i])

function setSearch(xs:seq<int>,x:int):int
ensures 0<=setSearch(xs,x)<=|xs|
ensures x !in xs ==> forall k::setSearch(xs,x)<=k<|xs| ==> x<xs[k]
ensures x !in xs ==> forall k::0<=k<setSearch(xs,x) ==> x>xs[k]
ensures x in xs ==> 0<=setSearch(xs,x)<|xs| && xs[setSearch(xs,x)]==x

function  SetAdd(xs:seq<int>, x:int):seq<int>
requires isSortedSet(xs)
ensures isSortedSet(SetAdd(xs,x))
ensures (set y | y in xs) + {x} == (set y | y in SetAdd(xs,x)) 
{
 if (x in xs) then xs
 else xs[..setSearch(xs,x)]+[x]+xs[setSearch(xs,x)..]
}


function SetRemove(xs:seq<int>, x:int):seq<int>
requires isSortedSet(xs)
ensures isSortedSet(SetRemove(xs,x))
ensures (set y | y in xs) - {x} == (set y | y in SetRemove(xs,x)) 
{
  if (x !in xs) then xs
  else xs[..setSearch(xs,x)]+xs[setSearch(xs,x)+1..]

}

trait SetIterator {
  function Parent(): Set
    reads this

  predicate Valid()
    reads this, Parent(), Parent().Repr()

  function Index(): nat
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Index() <= |Parent().Model()|

  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() <==> Index() < |Parent().Model()|

  function method HasPrev(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasPrev() <==> Index() > 0

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
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Index() == old(it.Index()))

  method Prev() returns (x: int)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasPrev() && HasNext()
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
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == old(Index()) - 1
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Index() == old(it.Index()))

  function method Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() == Parent().Model()[Index()]

  method Copy() returns (it: SetIterator)
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
    ensures Index() == it.Index()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())

  
}

trait Set {
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

  function Model(): seq<int>
    reads this, Repr()
    requires Valid()
    ensures isSortedSet(Model())

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []

  function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|

  function Iterators(): set<SetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

method Begin() returns (it: SetIterator)
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
    ensures it.Index() == 0
    ensures it.Parent() == this
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())

  method End() returns (it: SetIterator)//iterator to the last element
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
    ensures if |Model()|==0 then it.Index() == 0 
            else it.Index() == |Model()|-1
    ensures it.Parent() == this
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())

  method contains(x:int) returns (b:bool)
    requires Valid()
    ensures Valid() && b == (x in Model())

  method add(x:int)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()==SetAdd(old(Model()),x)  

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)


  method remove(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()==SetRemove(old(Model()),x)  

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)


  method find(x:int) returns (newt:SetIterator)
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent()==this
    ensures x in Model() ==> 0<=newt.Index()<|Model()| && Model()[newt.Index()]==x
    ensures x !in Model() ==> newt.Index()==|Model()|

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
    ensures Iterators() == {newt}+old(Iterators())

  method insert(mid: SetIterator, x: int) returns (newt:SetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    //mid just a hint, it is inserted where corresponds
    //efficiently or not if it respects order
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == SetAdd(old(Model()), x)

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this
    ensures newt.HasNext() && Model()[newt.Index()]==x
    //points either to the inserted elemento or to the already existing one
 


  method erase(mid:SetIterator) returns (next: SetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()==SetRemove(old(Model()),old(Model())[old(mid.Index())])
    
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this && next.Index()==old(mid.Index())
}

method isContained(s1:Set,s2:Set) returns (b:bool)
modifies s1, s1.Repr(), s2, s2.Repr()
requires s1.Valid() && s2.Valid()
requires forall x | x in s1.Repr() :: allocated(x)
requires forall x | x in s2.Repr() :: allocated(x)

requires ({s1} + s1.Repr()) !! ({s2}+s2.Repr())
ensures s1.Valid() && s2.Valid()
ensures s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
ensures b == isSubSet(s1.Model(),s2.Model())

ensures forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
ensures fresh(s1.Repr()-old(s1.Repr()))
ensures forall x | x in s1.Repr() :: allocated(x)

ensures forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
ensures fresh(s2.Repr()-old(s2.Repr()))
ensures forall x | x in s2.Repr() :: allocated(x)

ensures s1.Iterators()>=old(s1.Iterators()) && s2.Iterators()>=old(s2.Iterators())
{
 var it1:=s1.Begin(); var x1:int; var x2:int;
 var it2:=s2.Begin(); b:=true;
 while (it1.HasNext() && it2.HasNext() && b)
   decreases |s1.Model()|+|s2.Model()|-(it1.Index()+it2.Index())+(if b then 1 else 0)
   invariant s1.Valid() && s2.Valid() 
   invariant ({s1} + s1.Repr()) !! ({s2}+s2.Repr()) 
   invariant s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
   invariant it1.Valid() && it2.Valid() 
   invariant it1 in s1.Iterators() && it2 in s2.Iterators()
   invariant it1.Parent()==s1 && it2.Parent()==s2
   invariant 0<=it1.Index()<=|s1.Model()| && 0<=it2.Index()<=|s2.Model()|
   invariant b == isSubSet(s1.Model()[..it1.Index()],s2.Model()[..it2.Index()])
   invariant forall u,v::0<=u<it1.Index() && it2.Index()<=v<|s2.Model()| ==> s1.Model()[u]<s2.Model()[v]
   invariant forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
   invariant forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
   invariant forall x | x in s1.Repr() :: allocated(x)
   invariant forall x | x in s2.Repr() :: allocated(x)
   invariant s1.Iterators() >= old(s1.Iterators()) && s2.Iterators() >= old(s2.Iterators())

 { 
  if (it1.Peek()==it2.Peek())
  {  x1 := it1.Next(); x2:=it2.Next(); }
  else if (it1.Peek()<it2.Peek())
   { b:=false; x1:=it1.Next();}
  else { x2 := it2.Next();}
  assert b ==> isSubSet(s1.Model()[..it1.Index()],s2.Model()[..it2.Index()]);
  assert isSubSet(s1.Model()[..it1.Index()],s2.Model()[..it2.Index()]) ==> b;
 }

 lSubSet(s1.Model(),s2.Model(),it2.Index());
 assert b && !it1.HasNext() ==> isSubSet(s1.Model(),s2.Model());
  b:=b && !it1.HasNext();





}

method {:verify false} try(s:Set)
modifies s, s.Repr()
requires s.Valid() && s.Empty()
requires forall x | x in s.Repr() :: allocated(x)
ensures s.Valid()
ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)
{
 /*s.add(3);
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
   assert (set x | x in s.Model()) == {};*/
 s.add(2); s.add(7); s.add(0); s.add(1);s.add(10);

 var b:=s.contains(10);
 assert b;

 var it:=s.Begin(); var cont:=0;
  while (it.HasNext())
  decreases |s.Model()|-it.Index()
  invariant it.Valid() && it.Parent()==s
  invariant s.Valid()
  invariant  forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  invariant fresh(s.Repr()-old(s.Repr()))
  invariant forall x | x in s.Repr() :: allocated(x)
    {var aux:=it.Next();
     if (aux%2==0) {cont:=cont+1;} 
    } 
  var it2:=s.find(2);
  assert it2.Index()==4;
  it2:=s.find(7); 
  assert it.Index()==3;  
  var aux:=it.Next();
  assert aux==7;assert it.Index()==4;
  
  var it3:=s.find(7);
  it3:=s.insert(it3,5);//efficient
  assert it3.Index()==3;
  it3:=s.insert(it3,12);
  assert it3.Index()==5;
  var z:=it3.Prev();
  assert it3.Index()==4;

  var it4:=s.End();
  z:=it4.Prev();
  z:=it4.Prev();

  assert z==10;
}