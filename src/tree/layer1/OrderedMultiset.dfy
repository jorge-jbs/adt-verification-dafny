include "../../../src/tree/layer1/UnorderedMultiset.dfy"


function isSortedSeq(xs:seq<int>):bool
{forall i,j::0<=i<j<|xs| ==> xs[i]<=xs[j]}

function Pick(s: multiset<int>): int
  requires s != multiset{}
{
  var x :| x in s; x
}

function seq2Multiset (xs:seq<int>):multiset<int>
{multiset(xs)}

function multiset2Seq(s:multiset<int>):seq<int>
decreases s
{
  if s == multiset{} then []
  else 
    var y := Pick(s);
    [y] + multiset2Seq(s - multiset{y})
    
}

lemma sizesSet2Seq(s:multiset<int>)
ensures |multiset2Seq(s)|==|s|
{}

lemma  sizesSeq2Multiset(xs:seq<int>)
ensures |seq2Multiset(xs)|==|xs|
{if (xs==[]) {}
 else {sizesSeq2Multiset(xs[1..]);
       assert xs==[xs[0]]+xs[1..];
       assert seq2Multiset(xs)==multiset{xs[0]}+seq2Multiset(xs[1..]);
       assert |seq2Multiset(xs)|==1+|seq2Multiset(xs[1..])|;}
}

lemma idem(s:multiset<int>)
ensures seq2Multiset(multiset2Seq(s)) == s 
{  if s != multiset{} {
    var y := Pick(s);
    assert seq2Multiset([y] + multiset2Seq(s - multiset{y})) == seq2Multiset([y]) + seq2Multiset(multiset2Seq(s - multiset{y}));
  }
}

function sort(xs:seq<int>):seq<int>
ensures seq2Multiset(xs)==seq2Multiset(sort(xs)) && isSortedSeq(sort(xs))
ensures |xs|==|sort(xs)|

function multiset2SortedSeq(s:multiset<int>):seq<int>
ensures multiset2SortedSeq(s)==sort(multiset2Seq(s))
{sort(multiset2Seq(s))
}

lemma sortedSeq(s:multiset<int>)
ensures isSortedSeq(multiset2SortedSeq(s)) && seq2Multiset(multiset2SortedSeq(s))==s
ensures |multiset2SortedSeq(s)|==|s|
{idem(s);sizesSet2Seq(s);}




function {:induction s} minimum(s:multiset<int>):int
requires s != multiset{}
//ensures forall x | x in s :: minimum(s)<=x
{ 
  var x :| x in s;
  if (s-multiset{x}==multiset{}) then x
  else if (x < minimum(s-multiset{x})) then x
  else minimum(s-multiset{x})

}

lemma lmin(s:multiset<int>,x:int)
requires s != multiset{} && x in s
ensures x >= minimum(s)
{
  var y:| y in s;
  if (s-multiset{y} == multiset{}){assert s==multiset{y};assert x==y;}
  else if (minimum(s-multiset{y})==minimum(s)){}
  else{}
}


lemma lminimum(s:multiset<int>)
requires s != multiset{}
ensures minimum(s) in s && forall x | x in s :: minimum(s) <= x
{forall x | x in s
 ensures minimum(s) <= x {lmin(s,x);}}


function {:induction s} maximum(s:multiset<int>):int
requires s != multiset{}
//ensures forall x | x in s :: maximum(s)>=x
{ 
  var x :| x in s;
  if (s-multiset{x}==multiset{}) then x
  else if (x > maximum(s-multiset{x})) then x
  else maximum(s-multiset{x})

}

lemma lmax(s:multiset<int>,x:int)
requires s != multiset{} && x in s
ensures x<=maximum(s)
{
  var y:| y in s;
  if (s-multiset{y} == multiset{}){assert s==multiset{y};assert x==y;}
  else if (maximum(s-multiset{y})==maximum(s)){}
  else{}
}


lemma lmaximum(s:multiset<int>)
requires s !=  multiset{}
ensures maximum(s) in s && forall x | x in s :: maximum(s) >= x
{forall x | x in s
 ensures maximum(s) >= x {lmax(s,x);}}


function msmaller(s:multiset<int>,x:int):multiset<int>
ensures forall z | z in msmaller(s,x) :: z < x && s[z]==msmaller(s,x)[z]
ensures forall z | z in s && z < x :: z in msmaller(s,x) 
{ if (s==multiset{}) then multiset{}
  else
    var y :| y in s;
    if (y<x) then 
       multiset{y} + msmaller(s-multiset{y},x)
    else 
       msmaller(s-multiset{y},x)
}

function elemth(s:multiset<int>,k:int):int
requires 0<=k<|s|
{
  var minim:=minimum(s);
  if (k==0) then minim
  else elemth(s-multiset{minim},k-1)
}

lemma {:induction s,k} lelemth(s:multiset<int>,k:int)
requires 0<=k<|s|
ensures elemth(s,k) in s && |msmaller(s,elemth(s,k))|<=k<=|msmaller(s,elemth(s,k))|+s[elemth(s,k)]-1
{ lminimum(s);
  if (k==0) { }
  else if (minimum(s)== elemth(s-multiset{minimum(s)},k-1)){}
  else {
    lelemth(s-multiset{minimum(s)},k-1);
    assert elemth(s,k) in s;
    assert minimum(s)<elemth(s-multiset{minimum(s)},k-1);
    assert msmaller(s-multiset{minimum(s)},elemth(s-multiset{minimum(s)},k-1))+multiset{minimum(s)}==msmaller(s,elemth(s,k));
    assert |msmaller(s-multiset{minimum(s)},elemth(s-multiset{minimum(s)},k-1))|+1==|msmaller(s,elemth(s,k))|;
  }
}


trait OrderedMultisetIterator extends UnorderedMultisetIterator{
  
  function Traversed():multiset<int>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed()<=Parent().Model()
    ensures forall x,y | x in Traversed() && y in Parent().Model()-Traversed() :: x<=y

   //Several elements equal to the Peek may be in Traversed and some others not
  // Example: Model=={1,1,2,3,3,3,4,5} Traversed=={1,1,2,3,3} Peek=3 

  function method Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model() && (Parent().Model()-Traversed())[Peek()]>0
    ensures Peek()==elemth(Parent().Model(),|Traversed()|)
    ensures forall x | x in Traversed() :: x<=Peek()
    ensures forall x | x in Parent().Model()-Traversed() :: Peek()<=x 


  function method Index(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() ==> Index()==|Traversed()|
    ensures !HasNext() ==> Index()==|Parent().Model()|

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
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

  
}

trait OrderedMultiset extends UnorderedMultiset{
  
   //Novelties respect UnorderedSet
   // Last iterator method 
   // Find knows the traversed elements
   // Insert knows the traversed elements
   // Those methods that return iterators do return OrderedSetIterator
   // Methods receiving iterators may be called with OrderedSetIterator
   // The rest remains the same 

  function Iterators(): set<UnorderedMultisetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is OrderedMultisetIterator

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
    ensures newt.HasNext() && msmaller(Model(),x)<=newt.Traversed()<=msmaller(Model(),x)[x:=Model()[x]]  && newt.Peek()==x 
    //DUDAS
    
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
    ensures Model()== old(Model())-multiset{old(mid.Peek())}
    
    ensures next is OrderedMultisetIterator
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Traversed()==old(mid.Traversed())  && (next.HasNext() ==> next.Peek()==elemth(Model(),|next.Traversed()|))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

}


/*
method {:verify true} try(s:OrderedSet)
modifies s, s.Repr()
requires s.Valid() && s.Empty()
requires forall x | x in s.Repr() :: allocated(x)
ensures s.Valid()
ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)
{

 
 s.add(2); s.add(7); s.add(0); s.add(1);s.add(10);
 assert s.Model()=={0,1,2,7,10};

 var b:=s.contains(10);
 assert b;
*/
 /*var it : OrderedSetIterator :=s.First(); var cont:=0;
  while (it.HasNext())
  //decreases |s.Model()|-|it.Traversed()|
  decreases |s.Model()|-it.Index()
  invariant it.Valid() && it.Parent()==s
  invariant s.Valid() && s.Model()=={0,1,2,7,10}
  invariant  forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  invariant fresh(s.Repr()-old(s.Repr()))
  invariant forall x | x in s.Repr() :: allocated(x)
    {var aux:=it.Next();
     if (aux%2==0) {cont:=cont+1;} 
    } 
*/
 /*  assert s.Model()=={0,1,2,7,10};
  var it2 :=s.find(2) ;
  assert it2 is OrderedSetIterator;
  assert s is OrderedSet;
  assert 2 in s.Model();
  assert it2.Peek()==2;
  assert it2.Peek()!=5;
  assert (it2 as OrderedSetIterator).Traversed()=={0,1};//OO(
  assert it2.Index()==2;
 it2:=s.find(7); 
  assert it2.Traversed()=={0,1,2};
  assert it2.Index()==3;  
  var aux:=it2.Next();
  assert aux==7;assert it2.Index()==4;
  
  var it3:OrderedSetIterator:=s.find(7);
  it3:=s.insert(it3,5);//efficient
  assert it3.Traversed()=={0,1,2};
  assert it3.Index()==3;
  it3:=s.insert(it3,12);
    assert it3.Traversed()=={0,1,2,5,7,10};
  assert it3.Index()==6;
  //assert maximum(it3.Traversed())==10;
  var z:=it3.Prev();

  var it4:=s.Last();
  z:=it4.Prev();
  z:=it4.Prev();

  assert z==10;
  z:=it4.Prev();
  z:=it4.Prev();
  z:=it4.Prev();
  z:=it4.Prev();
  z:=it4.Prev();
  z:=it4.Prev();
  assert !it4.HasPrev();

}*/