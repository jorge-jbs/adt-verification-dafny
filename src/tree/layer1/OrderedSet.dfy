include "../../../src/Utils.dfy"

function isSortedSet(xs:seq<int>):bool
{forall i,j::0<=i<j<|xs| ==> xs[i]<xs[j]}


function isSubSet(xs:seq<int>,ys:seq<int>):bool
requires isSortedSet(xs) && isSortedSet(ys)
ensures isSubSet(xs,ys) ==> ((set x | x in xs) <= (set y | y in ys))
ensures !isSubSet(xs,ys) <== (exists x:: x in xs && x!in ys)
{ forall x:: x in xs ==> x in ys}

lemma lSubSet(xs:seq<int>,ys:seq<int>,i:int)
requires 0<=i<=|ys| && isSortedSet(xs) && isSortedSet(ys)
ensures isSubSet(xs,ys[..i]) ==> isSubSet(xs,ys)
{}

lemma lmoreSubSet(xs:seq<int>,ys:seq<int>,i:int,j:int)
requires 0<=i<|xs| && 0<=j<|ys| && isSortedSet(xs) && isSortedSet(ys)
requires isSubSet(xs[..i],ys[..j]) && xs[i]==ys[j] 
ensures isSubSet(xs[..i+1],ys[..j+1])
{assert xs[..i+1]==xs[..i]+[xs[i]];}

lemma lmoreSubSet2(xs:seq<int>,ys:seq<int>,i:int,j:int)
requires 0<=i<|xs| && 0<=j<|ys| && isSortedSet(xs) && isSortedSet(ys)
requires isSubSet(xs[..i],ys[..j]) && xs[i]>ys[j] 
ensures isSubSet(xs[..i],ys[..j+1])
{}


lemma lnotSubSet(xs:seq<int>,ys:seq<int>,i:int,j:int)
requires 0<=i<|xs| && 0<=j<|ys| && isSortedSet(xs) && isSortedSet(ys)
requires (forall k::0<=k<j ==> ys[k]<xs[i]) && xs[i]<ys[j] 
ensures !isSubSet(xs[..i+1],ys)
{ assert forall k::j<k<|ys| ==> ys[j]<ys[k];
  assert forall k::j<=k<|ys| ==> xs[i]<ys[k];
  assert xs[i] in (set x | x in xs[..i+1]) && xs[i] !in (set y | y in ys);
  }

lemma lnotSubSet2(xs:seq<int>,ys:seq<int>,i:int)//no lo uso
requires 0<=i<|xs| && isSortedSet(xs) && isSortedSet(ys)
requires  (forall k::0<=k<|ys| ==> ys[k]<xs[i])
ensures !isSubSet(xs,ys)
{assert xs[i] in xs;
 assert xs[i] !in ys;}

function setSearchAux(xs:seq<int>,x:int,i:int):int
requires 0<=i<=|xs| &&  isSortedSet(xs) && forall k::i<=k<|xs| ==> x<xs[k]
ensures 0<=setSearchAux(xs,x,i)<=i 
ensures forall k::0<=k<setSearchAux(xs,x,i) ==> x>xs[k]
ensures forall k::setSearchAux(xs,x,i)<=k<|xs| ==> x<=xs[k]
ensures x in xs ==> 0<=setSearchAux(xs,x,i)<i && xs[setSearchAux(xs,x,i)]==x
{
  if (i==0) then 0
  else if (xs[i-1]==x) then i-1
  else if (xs[i-1]>x) then setSearchAux(xs,x,i-1)
  else i//xs[i-1]<x
   
}


function setSearch(xs:seq<int>,x:int):int
requires isSortedSet(xs)
ensures 0<=setSearch(xs,x)<=|xs| 
ensures forall k::0<=k<setSearch(xs,x) ==> x>xs[k]
ensures forall k::setSearch(xs,x)<=k<|xs| ==> x<=xs[k]
ensures x in xs ==> 0<=setSearch(xs,x)<|xs| && xs[setSearch(xs,x)]==x
{assert xs[..|xs|]==xs;
  setSearchAux(xs,x,|xs|)
  
}

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

trait OrderedSetIterator {
  function Parent(): OrderedSet
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

  method Copy() returns (it: OrderedSetIterator)
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

trait OrderedSet {
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

  function Iterators(): set<OrderedSetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

method First() returns (it: OrderedSetIterator)
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

  method Last() returns (it: OrderedSetIterator)//iterator to the last element
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
   
    ensures Iterators() == old(Iterators())



  method remove(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()==SetRemove(old(Model()),x)  

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())


  method find(x:int) returns (newt:OrderedSetIterator)
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

  method insert(mid: OrderedSetIterator, x: int) returns (newt:OrderedSetIterator)
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
 


  method erase(mid:OrderedSetIterator) returns (next: OrderedSetIterator)
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



method {:verify false} try(s:OrderedSet)
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

 var it:=s.First(); var cont:=0;
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

  var it4:=s.Last();
  z:=it4.Prev();
  z:=it4.Prev();

  assert z==10;
}