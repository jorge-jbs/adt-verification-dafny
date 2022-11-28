include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
 
 predicate Sorted(xs:seq<int>)
  { forall i,j | 0<=i<=j<|xs| :: xs[i]<=xs[j]}


  predicate StrictSorted(xs:seq<int>)
  { forall i,j | 0<=i<j<|xs| :: xs[i]<xs[j]}
 
function delDup(xs:seq<int>,i:int):seq<int>//[0,i)
requires 0<=i<=|xs|
ensures i==0 ==>delDup(xs,i)==[]
ensures i==1 ==>delDup(xs,i)==[xs[0]]
ensures i>1 && xs[i-1]!=xs[i-2] ==> delDup(xs,i)==delDup(xs,i-1)+[xs[i-1]]
ensures i>1 && xs[i-1]==xs[i-2] ==> delDup(xs,i)==delDup(xs,i-1)
{
 if (i==0) then []
 else if (i==1) then [xs[0]]
 else if (xs[i-1]!=xs[i-2]) then delDup(xs,i-1)+[xs[i-1]]
 else delDup(xs,i-1)

}

function elimDupMapAux(xs:seq<int>,its:set<int>,i:int):map<int,int>
requires 0<=i<=|xs| 
{
 if (i==0) then map[]
 else if (i>1 && xs[i-1]==xs[i-2]) then elimDupMapAux(xs,its,i-1)
 else if i-1 in its then  elimDupMapAux(xs,its,i-1)[i-1:=|delDup(xs,i)|-1]//i==1 or i>1
 else elimDupMapAux(xs,its,i-1)
       
}    


function elimDupMap(xs:seq<int>,its:set<int>):map<int,int>
{
  if (|xs| in its) then elimDupMapAux(xs,its,|xs|)[|xs|:=|delDup(xs,|xs|)|]
  else elimDupMapAux(xs,its,|xs|)

}
lemma elimMapAux(xs:seq<int>,its:set<int>,i:int)
requires 0<=i<=|xs| 
ensures forall it | it in elimDupMapAux(xs,its,i) :: it in its && 0 <= it < i && 0<=elimDupMapAux(xs,its,i)[it]<|delDup(xs,i)|
ensures forall it | it in elimDupMapAux(xs,its,i) :: (it==0) || (1 <= it < i && xs[it]!=xs[it-1])
{}

lemma elimMap(xs:seq<int>,its:set<int>)
ensures forall it | it in elimDupMap(xs,its) :: it in its 
ensures  forall it | it in elimDupMap(xs,its) :: 0<=it<=|xs| && 0<=elimDupMap(xs,its)[it]<=|delDup(xs,|xs|)|
ensures forall it | it in elimDupMap(xs,its) :: (it==0) || (it==|xs|) || (1<=it<|xs| && xs[it]!=xs[it-1])

{elimMapAux(xs,its,|xs|);}

method elimDup(l:LinkedList<int>) returns (ghost mit:map<int,int>)
//method {:verify true} elimDupA(l:ArrayList) //NO CHANGES
 modifies l, l.Repr()
  requires allocated(l.Repr())
 ensures fresh(l.Repr()-old(l.Repr()))
 ensures allocated(l.Repr())

 requires l.Valid() && Sorted(l.Model())
 ensures l.Valid()

 ensures l.Model()==delDup(old(l.Model()),|old(l.Model())|)
 ensures (set x | x in old(l.Model())) == (set x | x in l.Model())
 ensures StrictSorted(l.Model())

 ensures l.Iterators() >= old(l.Iterators())
 ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index()
 ensures mit==elimDupMap(old(l.Model()),(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())))
 ensures forall it | it in mit :: (it==0) || (it==|old(l.Model())|) || (1<=it<|old(l.Model())| && old(l.Model())[it]!=old(l.Model())[it-1])
{
  ghost var validSet:=(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index()));
  ghost var omodel:=l.Model();

  var aux;
  var it2:=l.Begin(); 
  var it1:=it2.Copy();
  var b := it1.HasNext();

  if (b) 
  {    
    aux:=it2.Next();
    ghost var j:=1; //to traverse old(l.Model())
    ghost var p:=0;//first occurrence in old(l.Model()) of current element it1

    assert it2.HasNext?() ==> it1.HasNext?() && l.Model()[it1.Index()+1]==l.Model()[it2.Index()];
    assert it2.Index()==1 && it1.Index()==0;
  
    if (0 in validSet) {mit:=map[0:=0];}
    else {mit:=map[];}
  

    b := it2.HasNext();

    while b
     decreases |l.Model()| - it2.Index()
     invariant allocated(l.Repr())
     invariant fresh(l.Repr()-old(l.Repr()))

     invariant l.Valid()
     invariant it2 in l.Iterators() && it1 in l.Iterators()
     invariant it1.Parent() == l && it2.Parent()==l
     invariant it1.Valid() && it2.Valid()
     invariant it2.Index()==it1.Index()+1 
     invariant it2.HasNext?() ==> it1.HasNext?() && l.Model()[it1.Index()+1]==l.Model()[it2.Index()]
     invariant j+(|l.Model()| - it2.Index())==|omodel| && 1<=j<=|old(l.Model())| 

     invariant l.Model()[..it2.Index()]==delDup(old(l.Model()),j)    
     invariant old(l.Model())[j-1]==l.Model()[it1.Index()]
     invariant l.Model()[it2.Index()..]==old(l.Model())[j..]
        
     invariant forall k | p<=k<j ::old(l.Model())[k]==old(l.Model())[j-1]==l.Model()[it1.Index()]

     invariant (set x | x in old(l.Model())) == (set x | x in l.Model())
     invariant Sorted(l.Model()) && StrictSorted(l.Model()[..it2.Index()])
     invariant b == it2.HasNext?()

     invariant l.Iterators() >= old(l.Iterators())
     invariant it1 !in old(l.Iterators()) && it2 !in old(l.Iterators())
     invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index()
     invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index())>=j::it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==old(it.Index())-(j-|delDup(old(l.Model()),j)|)
    { ghost var pmodel:=l.Model();

     var it1Peek := it1.Peek();
     var it2Peek := it2.Peek();
     if (it1Peek == it2Peek) 
      { assert old(l.Model())[j..]==l.Model()[it2.Index()..];
        assert old(l.Model())[j..][0]==l.Model()[it2.Index()..][0];
        assert old(l.Model())[j]==l.Model()[it2.Index()];
        assert l.Model()[it1.Index()]==old(l.Model())[j-1];
        ghost var oit2:=it2.Index();

        it2 := l.Erase(it2); j:=j+1; 
          
        assert l.Model()==pmodel[..oit2]+pmodel[oit2+1..];
        assert l.Model()[..it2.Index()]==delDup(old(l.Model()),j);    

        assert mit==elimDupMapAux(old(l.Model()),validSet,j);
        elimMapAux(old(l.Model()),validSet,j);
        forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit
        ensures it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==mit[old(it.Index())]{}
      }
     else 
      {   
        assert  old(l.Model())[j]==l.Model()[it2.Index()]!=l.Model()[it1.Index()]==old(l.Model())[j-1];
        assert l.Model()[it2.Index()..]==[l.Model()[it2.Index()]]+l.Model()[it2.Index()+1..];
         
        if (j in validSet)
          {mit:=mit[j:=it2.Index()];}

        forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index())==j
        ensures it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==it2.Index()==mit[j]{}
        forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit
        ensures it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==mit[old(it.Index())]{}
         
        var _ := it2.Next(); 
        var _ := it1.Next();
           
        p:=j;
        j:=j+1;
        assert l.Model()[it2.Index()..]==old(l.Model())[j..];
        assert l.Model()[..it2.Index()]==delDup(old(l.Model()),j);    

        assert mit==elimDupMapAux(old(l.Model()),validSet,j);
        elimMapAux(old(l.Model()),validSet,j);
      }
      b:=it2.HasNext();  

     }

     assert j==|old(l.Model())| && it2.Index()==|l.Model()|;
     assert l.Model()==delDup(old(l.Model()),|old(l.Model())|);

     if (|omodel| in validSet) {mit:=mit[|omodel|:=|l.Model()|];}
     elimMap(old(l.Model()),validSet);

     //assert forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index();
    }
  else 
    {
     mit:=map[];
     if (|omodel| in validSet) {mit:=mit[|omodel|:=|l.Model()|];
    }

}

}
