
include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "../../src/Iterators_Utils.dfy"

predicate subSec<A>(xs1:seq<A>,xs2:seq<A>,f:map<int,int>)
  {
   forall i :: (0<=i<|xs1| <==> i in f) &&
   forall i | i in f :: 0<=i<|xs1| && 0<=f[i]<|xs2| && xs2[f[i]]==xs1[i] &&
   forall i,j | i in f && j in f && i<j :: f[i]<f[j]   
  }

  predicate isSubSec<A>(xs1:seq<A>,xs2:seq<A>)
  {exists f:map<int,int> :: subSec(xs1,xs2,f)}

 lemma {:verify false} multiSeq<A>(xs:seq<A>)
  requires xs!=[]
  ensures  multiset(xs)[xs[|xs|-1]]==multiset(xs[..|xs|-1])[xs[|xs|-1]]+1
  ensures forall x | x in xs && x!=xs[|xs|-1] :: multiset(xs)[x] == multiset(xs[..|xs|-1])[x]
  {assert xs[..|xs|-1]+[xs[|xs|-1]]==xs;}


function FilterR<A>(xs: seq<A>,f: A -> bool):seq<A>
  ensures xs==[] ==> FilterR(xs,f) == xs
  ensures xs!=[] && f(xs[|xs|-1]) ==> FilterR(xs,f)== FilterR(xs[..|xs|-1],f)+[xs[|xs|-1]] 
  ensures xs!=[] && !f(xs[|xs|-1]) ==> FilterR(xs,f)== FilterR(xs[..|xs|-1],f) 
  ensures forall i::0<=i<|FilterR(xs,f)| ==> f(FilterR(xs,f)[i])
  {
   if xs==[] then []
   else if f(xs[|xs|-1]) then
       FilterR(xs[..|xs|-1],f)+[xs[|xs|-1]] 
   else FilterR(xs[..|xs|-1],f) 
  }

//This is the map that proves the subsequence property
function FilterRMap<A>(xs: seq<A>,f: A -> bool):map<int,int>
ensures xs==[] ==> FilterRMap(xs,f)==map[]
ensures xs!=[] && f(xs[|xs|-1]) ==> FilterRMap(xs,f)==FilterRMap(xs[..|xs|-1],f)[|FilterR(xs,f)|-1:=|xs|-1]
ensures xs!=[] && !f(xs[|xs|-1]) ==> FilterRMap(xs,f)==FilterRMap(xs[..|xs|-1],f)
{
 if (xs==[]) then map[]
 else if f(xs[|xs|-1]) then 
    FilterRMap(xs[..|xs|-1],f)[|FilterR(xs,f)|-1:=|xs|-1]
 else FilterRMap(xs[..|xs|-1],f)

}
  
  lemma {:verify false} subSecFilter<A>(xs: seq<A>,f: A -> bool)
  ensures subSec(FilterR(xs,f),xs,FilterRMap(xs,f))
  {
    if xs==[] {}
    else {
      var m:=FilterRMap(xs[..|xs|-1],f);
      var filter:=FilterR(xs[..|xs|-1],f);
      assert subSec(filter,xs[..|xs|-1],m);
      assert |xs[..|xs|-1]|==|xs|-1;
      assert forall i::0<=i<|filter| <==> i in m; 
      assert forall i :: i in m ==>  0<=m[i]<|xs|-1 && filter[i]==xs[..|xs|-1][m[i]];
      assert forall i,j::i in m && j in m && i!=j ==> m[i]!=m[j];
      if f(xs[|xs|-1]) { 
        assert |FilterR(xs,f)|==1+|filter|;
        assert forall i :: 0<=i<|FilterR(xs,f)| <==> i in m[|FilterR(xs,f)|-1:=|xs|-1];
        assert forall i:: i in m[|FilterR(xs,f)|-1:=|xs|-1] ==> 
             0<=m[|FilterR(xs,f)|-1:=|xs|-1][i]<|xs| &&
             xs[m[|FilterR(xs,f)|-1:=|xs|-1][i]]==FilterR(xs,f)[i];
        forall  i,j | i in m[|FilterR(xs,f)|-1:=|xs|-1] && j in m[|FilterR(xs,f)|-1:=|xs|-1] && i!=j  
          ensures m[|FilterR(xs,f)|-1:=|xs|-1][i]!=m[|FilterR(xs,f)|-1:=|xs|-1][j]
          {}
        assert subSec(FilterR(xs,f),xs,m[|FilterR(xs,f)|-1:=|xs|-1]);}
      else {}

    }
  }

lemma {:verify false} PropinMultiFilter<A>(xs: seq<A>, x: A, f: A -> bool)
ensures x in multiset(FilterR(xs,f)) ==> x in multiset(xs)
{}


lemma {:verify false}  multiFilter<A>(xs: seq<A>,x:A,f: A -> bool)
requires xs!=[] && x in xs && x in FilterR(xs,f)
ensures multiset(FilterR(xs,f))[x]==multiset(xs)[x]
{
  if  (xs[..|xs|-1]==[]) {assert multiset(FilterR(xs,f))[x]==multiset(xs)[x];}
  else{
  var filter:=FilterR(xs[..|xs|-1],f);
  
  assert f(x);
   if (x==xs[|xs|-1]){
    if (xs[|xs|-1] in xs[..|xs|-1]){
    
     PropInFilter(xs[..|xs|-1],f);
     assert xs[|xs|-1] in FilterR(xs,f) && FilterR(xs,f)[|FilterR(xs,f)|-1]==xs[|xs|-1];
     assert xs[..|xs|-1]!=[] && x in xs[..|xs|-1] && x in FilterR(xs[..|xs|-1],f);
     multiFilter(xs[..|xs|-1],x,f);
     assert multiset(filter)[x]== multiset(xs[..|xs|-1])[x];
    calc =={
      multiset(FilterR(xs,f))[xs[|xs|-1]];
        {assert FilterR(xs,f)[|FilterR(xs,f)|-1]==xs[|xs|-1];}
      multiset(FilterR(xs,f))[FilterR(xs,f)[|FilterR(xs,f)|-1]];
       {multiSeq(FilterR(xs,f));
        assert multiset(FilterR(xs,f))[xs[|xs|-1]] == multiset(FilterR(xs,f)[..|FilterR(xs,f)|-1])[xs[|xs|-1]]+1;
        assert FilterR(xs,f)[..|FilterR(xs,f)|-1]== filter;
        assert x==xs[|xs|-1];
        }
      multiset(filter)[x]+1;//{multiFilter(xs[..|xs|-1],x,f);}
      multiset(xs[..|xs|-1])[x]+1;{ multiSeq(xs);}
      multiset(xs)[xs[|xs|-1]];}
      assert multiset(FilterR(xs,f))[x]==multiset(xs)[x];
     
    }
    else {
      assert xs[|xs|-1] !in xs[..|xs|-1];
      PropinMultiFilter(xs[..|xs|-1],xs[|xs|-1],f);
      assert xs[|xs|-1] !in FilterR(xs[..|xs|-1],f);
      assert multiset(xs[..|xs|-1])[xs[|xs|-1]]==0;
      multiSeq(xs);
      assert multiset(xs)[xs[|xs|-1]]==1;
      assert multiset(FilterR(xs,f))[xs[|xs|-1]]==multiset(xs)[xs[|xs|-1]]==1;}
   }
  else {

    assert x in xs[..|xs|-1] && x in multiset(filter);  
    calc =={
      multiset(FilterR(xs,f))[x];{multiSeq(FilterR(xs,f));}
      multiset(filter)[x];//{multiFilter(xs[..|xs|-1],x,f);}
      multiset(xs[..|xs|-1])[x];{multiSeq(xs);}
      multiset(xs)[x];}
     assert multiset(FilterR(xs,f))[x]==multiset(xs)[x];
  }
  }
  
}

lemma {:verify false} PropInFilter<A>(xs: seq<A>,f: A -> bool)
  ensures forall i::0<=i< |xs| && f(xs[i]) ==> xs[i] in  FilterR(xs,f)
  {}
lemma {:verify false} PropSubSecFilter<A>(xs: seq<A>,f: A -> bool)
ensures isSubSec(FilterR(xs,f),xs)
{subSecFilter(xs,f);}

lemma {:verify false} PropmultiFilter<A>(xs: seq<A>,f: A -> bool)
ensures forall x:: x in multiset(FilterR(xs,f)) ==> multiset(FilterR(xs,f))[x]==multiset(xs)[x]
{
  forall x | x in multiset(FilterR(xs,f))
  ensures multiset(FilterR(xs,f))[x]==multiset(xs)[x]
  { multiFilter(xs,x,f);}
}

lemma {:verify false} PropAtiFilter<A>(xs: seq<A>,f: A -> bool,i:int)
requires 0<=i<|xs|
ensures !f(xs[i]) ==> FilterR(xs[..i+1],f)==FilterR(xs[..i],f)
ensures f(xs[i]) ==> FilterR(xs[..i+1],f)==FilterR(xs[..i],f)+[xs[i]]
{
  if (!f(xs[i]))
  {
    calc =={
          FilterR(xs[..i+1],f);
          {assert |xs[..i+1]|==i+1; assert !f(xs[i]); assert xs[..i+1][..i]==xs[..i];}
          FilterR(xs[..i],f);}
  }
  else{
    calc =={
        FilterR(xs[..i+1],f);
        {assert |xs[..i+1]|==i+1; assert f(xs[i]); assert xs[..i+1][..i]==xs[..i];}
        FilterR(xs[..i],f)+[xs[i]];
      }

  }


}

lemma {:verify false} FilterLength<A>(xs: seq<A>,f: A -> bool,i:int)
requires 0<=i<|xs|
ensures !f(xs[i]) ==> |FilterR(xs[..i+1],f)|==|FilterR(xs[..i],f)|
ensures f(xs[i]) ==> |FilterR(xs[..i+1],f)|==|FilterR(xs[..i],f)|+1
{PropAtiFilter(xs,f,i);}

lemma {:verify false} {:induction i} FilterLength2<A>(xs: seq<A>,f: A -> bool,i:int)
requires 0<=i<=|xs|
ensures |FilterR(xs[..i],f)|<=i
{if (i==0) {assert xs[..i]==[];}
 else {FilterLength(xs,f,i-1);}}

function validIt(xs:seq<int>,i:int,f:int->bool):bool
requires 0<=i<=|xs|
ensures i==|xs|  ==> validIt(xs,i,f)
ensures i<|xs| && f(xs[i]) ==> validIt(xs,i,f)
{
  (i==|xs|) || (i<|xs| && f(xs[i]))
}

lemma allProps<A>(oxs:seq<A>,xs:seq<A>,f:A -> bool)
requires xs==FilterR(oxs,f)
ensures forall i::0<=i<|xs| ==> f(xs[i])
ensures forall i::0<=i< |oxs| && f(oxs[i]) ==> oxs[i] in xs 
ensures isSubSec(xs,oxs)//relative order is respected  
ensures forall i::0<=i<|xs|==> multiset(xs)[xs[i]]==multiset(oxs)[xs[i]]
 {PropSubSecFilter(oxs,f);
  PropInFilter(oxs,f);
  PropmultiFilter(oxs,f);}

method {:verify true} {:timeLimitMultiplier 100} filterEven(l:LinkedList) 
  modifies l, l.Repr()
  requires l.Valid()
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  
  ensures l.Model() == FilterR(old(l.Model()), x => x%2==0 )
  //All in filter meet the property
  //All that met the property are in the filter
  //The relative order is the same: it is a subsequence
  //The multiplicity is the same: a consequence that FilterRMap is surjective
  
  ensures l.Iterators()>=old(l.Iterators())
  ensures forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && validIt(old(l.Model()),old(iter.Index()),x => x%2==0) 
         ::iter.Valid() && iter.Index()==|FilterR(old(l.Model())[..old(iter.Index())],x => x%2==0)| 

  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)

{
   var it := l.Begin();
      ghost var i:=0; //index on old(Model())

  
  while it.HasNext()
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant it in l.Iterators()
    invariant it.Parent() == l
    invariant it.Valid()
    invariant 0<=i<=|old(l.Model())| && |l.Model()|-it.Index() == |old(l.Model())| -i
    invariant l.Model()[it.Index()..]==old(l.Model())[i..]
    invariant l.Model()[..it.Index()]==FilterR(old(l.Model())[..i],x => x%2==0)

    invariant l.Iterators()>=old(l.Iterators())
    invariant it !in old(l.Iterators())
    invariant it.Index()==|FilterR(old(l.Model())[..i],x => x%2==0)|<=i
    invariant forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && validIt(old(l.Model()),old(iter.Index()),x => x%2==0) && old(iter.Index())<i
         ::iter.Valid() && iter.Index()==|FilterR(old(l.Model())[..old(iter.Index())],x => x%2==0)|<it.Index()
    invariant forall iter  | iter in old(l.Iterators()) && old(iter.Valid()) && old(iter.Index())>=i
        ::iter.Valid() && iter.Index()==old(iter.Index())-(i-|FilterR(old(l.Model())[..i],x => x%2==0)|)


    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
    //forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant forall x | x in l.Repr() :: allocated(x)
 
  { 
    ghost var model:=old(l.Model());
    PropAtiFilter(old(l.Model()),x => x%2==0,i);
    FilterLength(old(l.Model()),x=>x%2==0,i);
    FilterLength2(old(l.Model()),x=>x%2==0,i);
   
    ghost var pmodel:=l.Model();
    if (it.Peek() % 2!=0) 
    {  
        ghost var oit:=it.Index();
        assert forall iter  | iter in old(l.Iterators()) && old(iter.Valid()) && validIt(old(l.Model()),old(iter.Index()),x => x%2==0) && old(iter.Index())<i
        :: iter.Valid() && iter.Index()==|FilterR(old(l.Model())[..old(iter.Index())],x => x%2==0)|<oit;
       
        assert old(l.Model())[i]%2!=0; assert !validIt(old(l.Model()),i,x => x%2==0);
        FilterLength2(old(l.Model()),x=>x%2==0,i);
        assert |FilterR(old(l.Model())[..i+1],x => x%2==0)|==|FilterR(old(l.Model())[..i],x => x%2==0)|;

      it := l.Erase(it); i:=i+1;

        assert it.Index()==oit;
        assert l.Model()==pmodel[..oit]+pmodel[oit+1..];
        assert l.Model()[..it.Index()]==FilterR(old(l.Model())[..i],x => x%2==0);   
        assert it !in old(l.Iterators());
          
        assert forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && validIt(old(l.Model()),old(iter.Index()),x => x%2==0) && old(iter.Index())<i
          :: iter.Valid() && iter.Index()==|FilterR(old(l.Model())[..old(iter.Index())],x => x%2==0)|<it.Index();

        assert forall iter  | iter in old(l.Iterators()) && old(iter.Valid()) && old(iter.Index())>=i
          ::iter.Valid() && iter.Index()==old(iter.Index())-(i-|FilterR(old(l.Model())[..i],x => x%2==0)|);

    }
    else 
    {   
        assert validIt(old(l.Model()),i,x => x%2==0);
        ghost var oit:=it.Index();
       
        assert forall iter  | iter in old(l.Iterators()) && old(iter.Valid()) && validIt(old(l.Model()),old(iter.Index()),x => x%2==0) && old(iter.Index())<i
          :: iter.Valid() && iter.Index()==|FilterR(old(l.Model())[..old(iter.Index())],x => x%2==0)|<oit;
        assert forall iter | iter  in old(l.Iterators()) && old(iter.Valid()) && old(iter.Index())==i
          ::iter.Index()==|FilterR(old(l.Model())[..i],x => x%2==0)|<=i;
        assert forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && validIt(old(l.Model()),old(iter.Index()),x => x%2==0) && old(iter.Index())<i+1
          :: iter.Valid() && iter.Index()==|FilterR(old(l.Model())[..old(iter.Index())],x => x%2==0)|<oit+1;
      
     
      var x := it.Next(); i:=i+1;
      
        assert it.Index()==oit+1;

        assert forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && validIt(old(l.Model()),old(iter.Index()),x => x%2==0) && old(iter.Index())<i
          ::iter.Valid() && iter.Index()==|FilterR(old(l.Model())[..old(iter.Index())],x => x%2==0)|<it.Index();
        assert forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && old(iter.Index())>=i
          ::iter.Valid() && iter.Index()==old(iter.Index())-(i-|FilterR(old(l.Model())[..i],x => x%2==0)|);
      
    }   

  
  }
    assert forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && validIt(old(l.Model()),old(iter.Index()),x => x%2==0) && old(iter.Index())<i
      ::iter.Valid() && iter.Index()==|FilterR(old(l.Model())[..old(iter.Index())],x => x%2==0)|<it.Index();
 
  
    assert it.Index()==|l.Model()| && i==|old(l.Model())|;
    assert l.Model()==l.Model()[..|l.Model()|];
    assert old(l.Model())==old(l.Model())[..|old(l.Model())|];
    assert l.Model()==FilterR(old(l.Model()),x=>x%2==0);

    assert it.Index()==|FilterR(old(l.Model())[..|old(l.Model())|],x => x%2==0)|==|FilterR(old(l.Model()),x => x%2==0)|;

    //allProps(old(l.Model()),l.Model(),x=>x%2==0);

    assert validIt(old(l.Model()),|old(l.Model())|,x=>x%2==0);
    assert forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && validIt(old(l.Model()),old(iter.Index()),x => x%2==0) 
         ::iter.Valid() && iter.Index()==|FilterR(old(l.Model())[..old(iter.Index())],x => x%2==0)|;

}