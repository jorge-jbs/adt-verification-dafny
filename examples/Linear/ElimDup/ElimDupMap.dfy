include "../../../src/List/ListSpec.dfy"
include "../../../src/LinkedList/LinkedListSpec.dfy"
include "../../../src/Order.dfy"


module ElimDupMap{
  import opened ListSpec
  import opened LinkedListSpec
  import opened Order 

  export provides LinkedListSpec, Order
         provides ElimDup
         reveals ValidIt, DelDup, Fit, DelMap


ghost function DelDup(xs:seq<int>,i:int):seq<int>//[0,i)
requires 0 <= i <= |xs|
ensures i == 0 ==> DelDup(xs,i) == []
ensures i == 1 ==> DelDup(xs,i) == [xs[0]]
ensures i > 1 && xs[i-1] != xs[i-2] ==> DelDup(xs,i) == DelDup(xs,i-1)+[xs[i-1]]
ensures i > 1 && xs[i-1] == xs[i-2] ==> DelDup(xs,i) == DelDup(xs,i-1)
ensures forall x | x in DelDup(xs,i) :: x in xs[..i]
ensures forall x | x in xs[..i] :: x in DelDup(xs,i)
ensures (set x | x in xs[..i]) == (set x | x in DelDup(xs,i))
{
 if (i == 0) then []
 else if (i == 1) then [xs[0]]
 else if (xs[i-1] != xs[i-2]) then DelDup(xs,i-1)+[xs[i-1]]
 else DelDup(xs,i-1)

}

lemma  DelDupSorted(xs:seq<int>,  p:int)
requires 0 <= p <= |xs|
requires Sorted(xs) 
ensures StrictSorted(DelDup(xs,p)) 
ensures forall i,j | 0 <= i < j < |DelDup(xs,p)| :: DelDup(xs,p)[i] != DelDup(xs,p)[j]
{
  forall i,j | 0 <= i < j < |DelDup(xs,p)| ensures DelDup(xs,p)[i] < DelDup(xs,p)[j]
  {
   if (p > 1)
   { if (xs[p-1]==xs[p-2]) {DelDupSorted(xs,p-1);}
     else {
      assert xs[p-1] > xs[p-2];
      assert DelDup(xs,p)[|DelDup(xs,p)|-1] == xs[p-1];
      if (j == |DelDup(xs,p)|-1) {
        assert i < j;
        assert DelDup(xs,p)[i] in xs[..p-1];
        assert DelDup(xs,p)[i] <  DelDup(xs,p)[j];
      }
      else {DelDupSorted(xs,p-1);}
      }}

  }
}

lemma PropDelDupAux(oxs:seq<int>,xs:seq<int>,i:int,j:int)
requires 0 <= i <= |oxs| && 0 <= j <= |xs| && xs[..j] == DelDup(oxs,i) && xs[j..] == oxs[i..] && Sorted(oxs)
 ensures (set x | x in oxs) == (set x | x in xs)
 ensures StrictSorted(xs[..|DelDup(oxs,i)|])
 {
  DelDupSorted(oxs,i);
  assert (set x | x in xs) == (set x | x in xs[..j]) + (set x | x in xs[j..]);
 }

lemma PropDelDup(oxs:seq<int>,xs:seq<int>)
requires  xs == DelDup(oxs,|oxs|) && Sorted(oxs)
 ensures (set x | x in oxs) == (set x | x in xs)
 ensures StrictSorted(xs[..|DelDup(oxs,|oxs|)|])
 {PropDelDupAux(oxs,xs,|oxs|,|xs|);}


lemma DelDupSize(xs:seq<int>,i:int)
requires 0 <= i <= |xs|
ensures 0 <= |DelDup(xs,i)| <= i
ensures |xs| > 0 && i > 0 ==>  |DelDup(xs,i)| > 0
{}

lemma DelDupSizeMonotone(xs:seq<int>,i:int, j:int)
requires 0 <= i <= j <= |xs| 
ensures |DelDup(xs,i)| <= |DelDup(xs,j)|
{}

ghost function ValidIt(xs:seq<int>,j:int,it:int):bool
requires  1 <= j <= |xs| && (-1 <= it <= |xs|)
ensures it <= 0 ==> ValidIt(xs,j,it) == true
ensures it == |xs| ==> ValidIt(xs,j,it) == true
ensures 1 <= it < j ==> ValidIt(xs,j,it) == (xs[it]!=xs[it-1])
ensures j <= it <|xs| ==>ValidIt(xs,j,it) == true
{ ((it <= 0) || (it == |xs|) || (1 <= it < j && (xs[it]!=xs[it-1])) || (j <= it < |xs|)) }


ghost function Fit(xs:seq<int>,j:int,it:int):int
requires 1 <= j <= |xs| && -1 <= it <= |xs|
ensures it <= 0 ==> Fit(xs,j,it) == it
ensures it > 0 && it >= j ==> Fit(xs,j,it) == it-(j-|DelDup(xs,j)|)
ensures it > 0 && it < j ==> Fit(xs,j,it) == |DelDup(xs,it)|
{ 
  if (it <= 0) then it
  else if (it >= j) then it-(j-|DelDup(xs,j)|)
      else |DelDup(xs,it)|
}

lemma FitPositive(xs:seq<int>,j:int,it:int)
requires 1 <= j <= |xs| && 0 <= it <= |xs|
ensures Fit(xs,j,it) >= 0
{ }


lemma Updatef(xs:seq<int>,j:int,it:int)
requires 1 <= j < |xs| && -1 <= it <= |xs|
ensures it == j ==> Fit(xs,j+1,it) == Fit(xs,j,it)
ensures it < j ==> Fit(xs,j+1,it) == Fit(xs,j,it)
{}


ghost function  DelMap(xs:seq<int>,its:set<int>,j:int):map<int,int>
requires 0 <= j <= |xs| 
ensures j == 0 ==> DelMap(xs,its,j) == map[]
ensures 0 < j <= |xs| ==> forall it | it in DelMap(xs,its,j) :: 
    it in its && -1 <= it <= |xs| && ValidIt(xs,j,it) && DelMap(xs,its,j)[it] == Fit(xs,j,it) 
{ if (j==0) then map[]
  else map it | it in its && -1 <= it <= |xs| && ValidIt(xs,j,it):: Fit(xs,j,it)}


lemma MonotoneSize(xs:seq<int>,i:int,j:int)
requires 0 <= i < j <= |xs| 
requires ValidIt(xs,j,i) 
ensures |DelDup(xs,i)| < j 
{
  DelDupSize(xs,i);
  assert  |DelDup(xs,i)| <= i <j;
}

lemma Equality(xs:seq<int>,i:int,j:int,z:int)
requires 0 < i < j < |xs| && Sorted(xs)
requires xs[i] != xs[i-1]
requires forall u | i < u <= j :: xs[i] == xs[u]
requires i < z <= j
ensures  DelDup(xs,z+1) == DelDup(xs,z) 
ensures DelDup(xs,z) == DelDup(xs,j)
{
}

lemma EqualToValidSize(xs:seq<int>,i:int,j:int)
requires 0 < i < j < |xs| && Sorted(xs)
requires xs[i] != xs[i-1]
requires forall z | i < z <= j :: xs[i] == xs[z]
ensures forall z | i < z <= j :: DelDup(xs,z) == DelDup(xs,j)
ensures forall z | i < z <= j :: |DelDup(xs,z)| == |DelDup(xs,j)|
ensures DelDup(xs,j) == DelDup(xs,i) + [xs[i]]
ensures |DelDup(xs,j)| == 1 + |DelDup(xs,i)| 
{
  forall z | i < z <= j ensures DelDup(xs,z) == DelDup(xs,j)
  {
   Equality(xs,i,j,z);
  }
  assert DelDup(xs,i+1) == DelDup(xs,i)+[xs[i]];
  assert |DelDup(xs,i+1)| == 1 + |DelDup(xs,i)|;
}

lemma SeqSize<A>(xs:seq<A>, ys:seq<A>,x:A)
requires x in xs && x !in ys
requires forall z | z in xs :: z in ys
ensures |xs| < |ys|
{}

lemma ValidSize(xs:seq<int>,i:int,j:int)
requires 0 < i < j < |xs| && Sorted(xs)
requires xs[i] != xs[i-1]
requires xs[i] != xs[j] //there is some index between i and j such that xs[i..k] == xs[i] but xs[k]!=xs[i]
ensures |DelDup(xs,j)| > |DelDup(xs,i)| 
{ 
    if (j==i+1){ assert |DelDup(xs,j)| == 1 + |DelDup(xs,i)|; }
    else if (xs[j-1] !=  xs[i])
           {ValidSize(xs,i,j-1);}
    else { EqualToValidSize(xs,i,j-1); }
}

lemma  DelMapRange(xs:seq<int>,its:set<int>,j:int)
requires 0 <= j < |xs| && Sorted(xs)
ensures forall it | it in DelMap(xs,its,j) && 0 <= it < j :: DelMap(xs,its,j)[it] < j
ensures forall it | it in DelMap(xs,its,j) && 0 <= it < j :: DelMap(xs,its,j)[it] < |DelDup(xs,j)|
ensures forall it | it in DelMap(xs,its,j) && it > j :: DelMap(xs,its,j)[it] > |DelDup(xs,j)|
ensures forall it | it in DelMap(xs,its,j) && it == j :: DelMap(xs,its,j)[it] == |DelDup(xs,j)|
{forall it | it in DelMap(xs,its,j) && 0 <= it < j
 ensures DelMap(xs,its,j)[it] < j
   {MonotoneSize(xs,it,j);}
  forall it | it in DelMap(xs,its,j) && 0 <= it < j 
  ensures  DelMap(xs,its,j)[it] < |DelDup(xs,j)|
  { if it==0 {
    DelDupSize(xs,j);
    assert DelMap(xs,its,j)[0] == 0 < |DelDup(xs,j)|;}
    else{
      assert DelMap(xs,its,j)[it] == |DelDup(xs,it)|;
      if (xs[it] == xs[j]) { 
        assert forall z | it < z <= j :: xs[z] == xs[it]; 
        EqualToValidSize(xs,it,j);
       }
      else {ValidSize(xs,it,j);}
    }
  }
}


lemma UpdateMapV(xs:seq<int>,its:set<int>,j:int)
requires 0 < j < |xs| 
requires ValidIt(xs,j+1,j)
ensures  DelMap(xs,its,j+1) == DelMap(xs,its,j)
{
    assert xs[j] != xs[j-1]; 
    assert DelDup(xs,j+1) == DelDup(xs,j) + [xs[j]]; 
    assert |DelDup(xs,j+1)| == |DelDup(xs,j)|+1;
   
    forall it | it in DelMap(xs,its,j+1) 
    ensures it in DelMap(xs,its,j) && DelMap(xs,its,j+1)[it] == DelMap(xs,its,j)[it]
    {
      assert ValidIt(xs,j,it);
      if (it < j) {}
      else if (it >= j + 1) {
        calc {
          DelMap(xs,its,j+1)[it] ;
           it - (j + 1 - |DelDup(xs,j+1)|);
           {assert DelDup(xs,j+1) == DelDup(xs,j) + [xs[j]]; 
            assert |DelDup(xs,j+1)| == |DelDup(xs,j)|+1;
            }
           it - (j + 1 - (|DelDup(xs,j)| + 1));
           it - (j - |DelDup(xs,j)|);
           DelMap(xs,its,j)[it] ;
        }
      }
      else { //it == j 
        calc {
          DelMap(xs,its,j+1)[it] ;
           |DelDup(xs,j)|;
           j - (j - |DelDup(xs,j)|);
           DelMap(xs,its,j)[it] ;
        }

        }
      }
      assert forall it | it in DelMap(xs,its,j) :: it in DelMap(xs,its,j+1) && DelMap(xs,its,j+1)[it] == DelMap(xs,its,j)[it];

    }


lemma UpdateMapNV(xs:seq<int>,its:set<int>,j:int)
requires 0 < j < |xs| && !ValidIt(xs,j+1,j)
ensures forall it | it in DelMap(xs,its,j) && it < j :: it in DelMap(xs,its,j+1) && DelMap(xs,its,j+1)[it] == DelMap(xs,its,j)[it]<j
ensures forall it | it in DelMap(xs,its,j) && it > j :: it in DelMap(xs,its,j+1) && DelMap(xs,its,j+1)[it] == DelMap(xs,its,j)[it]-1
ensures j !in DelMap(xs,its,j+1)
{
forall it | it in DelMap(xs,its,j) && 0 <= it < j 
ensures it in DelMap(xs,its,j+1) && DelMap(xs,its,j+1)[it] == DelMap(xs,its,j)[it]<j
{
  MonotoneSize(xs,it,j);
  assert DelMap(xs,its,j+1)[it] == DelMap(xs,its,j)[it] == |DelDup(xs,it)|;
  DelDupSize(xs,j);
}
forall it | it in DelMap(xs,its,j) && it>j 
ensures it in DelMap(xs,its,j+1) && DelMap(xs,its,j+1)[it] == DelMap(xs,its,j)[it]-1
{
  assert DelMap(xs,its,j+1)[it] == it-(j+1-|DelDup(xs,j+1)|) == it-(j+1-|DelDup(xs,j)|);
}
}


method {:timeLimitMultiplier 100} ElimDup(l:LinkedList<int>) returns (ghost mit:map<int,int>)
//method elimDupA(l:ArrayList) //NO CHANGES
 modifies l, l.Repr()
 requires allocated(l.Repr())
 ensures fresh(l.Repr()-old(l.Repr()))
 ensures allocated(l.Repr())

 requires l.Valid() && Sorted(l.Model())
 ensures l.Valid()

 ensures l.Model() == DelDup(old(l.Model()),|old(l.Model())|)
 ensures (set x | x in old(l.Model())) == (set x | x in l.Model())
 ensures StrictSorted(l.Model())

 ensures l.Iterators() >= old(l.Iterators())
 ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit ::
   && it.Valid() 
   && it.Parent() == old(it.Parent()) 
   && mit[old(it.Index())] == it.Index()
 
 ensures mit == DelMap(old(l.Model()),(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),|old(l.Model())|)
{
  ghost var validSet := (set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index()));
  ghost var omodel := l.Model();


  var it2 := l.First(); 
  var it1 := it2.Copy();
  var b := it1.HasPeek();

  if (b) 
   { 
     
    mit := DelMap(old(l.Model()),validSet,1);

    it2.Next();
    ghost var j := 1; //to traverse old(l.Model())
    ghost var p := 0;//first occurrence in old(l.Model()) of current element it1

     assert it2.HasPeek?() ==> it1.HasPeek?() && l.Model()[it1.Index()+1] == l.Model()[it2.Index()];
     assert it2.Index() == 1 && it1.Index() == 0;
  

    b := it2.HasPeek();
    while b
     decreases |l.Model()| - it2.Index()
     invariant allocated(l.Repr())
     invariant fresh(l.Repr()-old(l.Repr()))

     invariant l.Valid()
     invariant it2 in l.Iterators() && it1 in l.Iterators()
     invariant it1.Parent() == l && it2.Parent() == l
     invariant it1.Valid() && it2.Valid()
     invariant it1.Index() >= 0 && it2.Index() >= 0
     invariant it2.Index() == it1.Index()+1 
     invariant it2.HasPeek?() ==> it1.HasPeek?() && l.Model()[it1.Index()+1] == l.Model()[it2.Index()]
     invariant j+(|l.Model()| - it2.Index()) == |omodel| && 1 <= j <= |old(l.Model())| 

     invariant l.Model()[..it2.Index()] == DelDup(old(l.Model()),j)    
     invariant old(l.Model())[j-1] == l.Model()[it1.Index()]
     invariant l.Model()[it2.Index()..] == old(l.Model())[j..] 
     invariant forall k | p <= k < j :: old(l.Model())[k] == old(l.Model())[j-1] == l.Model()[it1.Index()]
     invariant b == it2.HasPeek?()

     invariant l.Iterators() >= old(l.Iterators())
     invariant it1 !in old(l.Iterators()) && it2 !in old(l.Iterators())
     invariant it2.Index() == |DelDup(old(l.Model()),j)| <= j

     invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
       && it.Valid() 
       && it.Parent() == old(it.Parent()) 
       && mit[old(it.Index())] == it.Index() <= old(it.Index())
     invariant mit == DelMap(old(l.Model()),(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),j)
   
   { ghost var pmodel := l.Model();
     
       assert  j in mit ==> mit[j] == |DelDup(old(l.Model()),j)|;
     
     var it1Peek := it1.Peek();
     var it2Peek := it2.Peek();
     if (it1Peek == it2Peek) 
     {  assert old(l.Model())[j..] == l.Model()[it2.Index()..];
        assert old(l.Model())[j..][0] == l.Model()[it2.Index()..][0];
        assert old(l.Model())[j] == l.Model()[it2.Index()];
        assert l.Model()[it1.Index()] == old(l.Model())[j-1];
        ghost var oit2 := it2.Index();
          
        assert it2 !in old(l.Iterators()); 
        assert j < j+1 && old(l.Model())[j] == old(l.Model())[j-1];
        assert !ValidIt(old(l.Model()),j+1,j);
        
        DelMapRange(old(l.Model()),validSet,j);    
        
        it2 := l.Erase(it2);  
          
        assert forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit && old(it.Index()) < j ::
          && it.Valid() 
          && mit[old(it.Index())] == it.Index() < j;

        assert forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit && old(it.Index()) > j ::
          && it.Valid() 
          && mit[old(it.Index())] == it.Index()+1;

        UpdateMapNV(old(l.Model()),validSet,j);
        assert forall it | it in DelMap(old(l.Model()),validSet,j) && it < j :: it in DelMap(old(l.Model()),validSet,j+1) && DelMap(old(l.Model()),validSet,j+1)[it] == DelMap(old(l.Model()),validSet,j)[it]<j;
        assert forall it | it in DelMap(old(l.Model()),validSet,j) && it > j :: it in DelMap(old(l.Model()),validSet,j+1) && DelMap(old(l.Model()),validSet,j+1)[it] == DelMap(old(l.Model()),validSet,j)[it]-1;

        j := j+1;

        assert l.Model() == pmodel[..oit2]+pmodel[oit2+1..];
        assert l.Model()[..it2.Index()] == DelDup(old(l.Model()),j);    
       
        mit := DelMap(old(l.Model()),validSet,j);
        assert mit == DelMap(old(l.Model()),validSet,j);
        assert l.Model()[it2.Index()..] == old(l.Model())[j..];
      }
    else {

        assert  old(l.Model())[j] == l.Model()[it2.Index()]!=l.Model()[it1.Index()] == old(l.Model())[j-1];
        assert DelDup(old(l.Model()),j+1) ==  DelDup(old(l.Model()),j)+[old(l.Model())[j]];
        assert l.Model()[it2.Index()..] == [l.Model()[it2.Index()]]+l.Model()[it2.Index()+1..];
        assert l.Model()[..it2.Index()+1] ==  DelDup(old(l.Model()),j+1);//DelDup(old(l.Model()),j) + [l.Model()[it2.Index()]] 

        assert ValidIt(old(l.Model()),j+1,j);
        UpdateMapV(old(l.Model()),validSet,j);
        assert DelMap(old(l.Model()),validSet,j+1) == DelMap(old(l.Model()),validSet,j);

        it2.Next(); 
        it1.Next();
           
        p := j;
        j := j+1;
      
        assert l.Model()[it2.Index()..] == old(l.Model())[j..];
        assert l.Model()[..it2.Index()] == DelDup(old(l.Model()),j); 

        mit := DelMap(old(l.Model()),validSet,j); 
        assert mit == DelMap(old(l.Model()),validSet,j);

      }
    b:=it2.HasPeek();  
  }
  assert mit == DelMap(old(l.Model()),validSet,j);

  assert !b;
  assert !it2.HasPeek?();
  assert j == |old(l.Model())| && it2.Index() == |l.Model()|;
  assert l.Model() == DelDup(old(l.Model()),|old(l.Model())|);
  }
  else {
         mit := map[];
       }
  PropDelDup(old(l.Model()),l.Model());

}
  
}