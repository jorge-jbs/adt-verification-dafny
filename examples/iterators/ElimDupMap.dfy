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


lemma monotone(xs:seq<int>,i:int,j:int)
requires 0<=i<j<=|xs|
ensures |delDup(xs,i)|<|delDup(xs,j)|



lemma delDupSize(xs:seq<int>,i:int)
requires 0<=i<=|xs|
ensures 0<=|delDup(xs,i)|<=i
{}

function validIt(xs:seq<int>,j:int,it:int):bool
requires  1<=j<=|xs| && (0<=it<=|xs|)
ensures it==0 ==> validIt(xs,j,it)==true
ensures it==|xs| ==> validIt(xs,j,it)==true
ensures 1<=it<j ==> validIt(xs,j,it)==(xs[it]!=xs[it-1])
ensures j<=it<|xs| ==>validIt(xs,j,it)==true
{ ((it==0) || (it==|xs|) || (1<=it<j && (xs[it]!=xs[it-1])) || (j<=it<|xs|)) }

function f(xs:seq<int>,j:int,it:int):int
requires 1<=j<=|xs| && 0<=it<=|xs|
ensures it==0 ==> f(xs,j,it)==0
ensures it>0 && it>=j ==> f(xs,j,it)==it-(j-|delDup(xs,j)|)
ensures it>0 && it<j ==> f(xs,j,it)==|delDup(xs,it)|
{
  if (it==0) then 0
  else if (it>=j) then it-(j-|delDup(xs,j)|)
      else |delDup(xs,it)|
    
}

lemma updatef(xs:seq<int>,j:int,it:int)
requires 1<=j<|xs| && 0<=it<=|xs|
ensures it==j ==> f(xs,j+1,it)==f(xs,j,it)
ensures it<j ==> f(xs,j+1,it)==f(xs,j,it)
{}


function  delMap(xs:seq<int>,its:set<int>,j:int):map<int,int>
requires 0<=j<=|xs| 
ensures j==0 ==> delMap(xs,its,j)==map[]
ensures 1<j<=|xs| ==> forall it | it in delMap(xs,its,j) :: 
    it in its && 0<=it<=|xs| && validIt(xs,j,it) && delMap(xs,its,j)[it]==f(xs,j,it) 
{ if (j==0) then map[]
  else map it | it in its && 0<=it<=|xs| && validIt(xs,j,it):: f(xs,j,it)}



lemma delMapRange(xs:seq<int>,its:set<int>,j:int)
requires 0<=j<=|xs| 
 ensures forall it | it in delMap(xs,its,j) && it<j
       ::delMap(xs,its,j)[it]<|delDup(xs,j)|
 ensures forall it | it in delMap(xs,its,j) && it>j
       ::delMap(xs,its,j)[it]>|delDup(xs,j)|
ensures forall it | it in delMap(xs,its,j) && it==j
       ::delMap(xs,its,j)[it]==|delDup(xs,j)|
{
forall it | it in delMap(xs,its,j) && it<j
ensures delMap(xs,its,j)[it]<|delDup(xs,j)|{
 monotone(xs,it,j);
}
}
  

lemma updateMapV(xs:seq<int>,its:set<int>,j:int)
requires 0<j<|xs| 
ensures   validIt(xs,j+1,j) ==> delMap(xs,its,j+1)==delMap(xs,its,j)
{
  if (validIt(xs,j+1,j)){
    assert |delDup(xs,j+1)|==|delDup(xs,j)|+1;}
}

lemma updateMapNV(xs:seq<int>,its:set<int>,j:int)
requires 0<j<|xs| && !validIt(xs,j+1,j)
ensures forall it | it in delMap(xs,its,j) && it<j :: it in delMap(xs,its,j+1) && delMap(xs,its,j+1)[it]==delMap(xs,its,j)[it]<j
ensures forall it | it in delMap(xs,its,j) && it>j :: it in delMap(xs,its,j+1) && delMap(xs,its,j+1)[it]==delMap(xs,its,j)[it]-1
ensures j !in delMap(xs,its,j+1)
{
forall it | it in delMap(xs,its,j) && it<j 
ensures it in delMap(xs,its,j+1) && delMap(xs,its,j+1)[it]==delMap(xs,its,j)[it]<j
{
  monotone(xs,it,j);delDupSize(xs,j);
}
forall it | it in delMap(xs,its,j) && it>j 
ensures it in delMap(xs,its,j+1) && delMap(xs,its,j+1)[it]==delMap(xs,its,j)[it]-1
{
  monotone(xs,j,it);delDupSize(xs,j);
  assert delMap(xs,its,j+1)[it]==it-(j+1-|delDup(xs,j+1)|)==it-(j+1-|delDup(xs,j)|);
}
}
method {:timeLimitMultiplier 100} elimDup(l:LinkedList<int>) returns (ghost mit:map<int,int>)
//method elimDupA(l:ArrayList) //NO CHANGES
 modifies l, l.Repr()
 requires allocated(l.Repr())
 ensures fresh(l.Repr()-old(l.Repr()))
 ensures allocated(l.Repr())

 requires l.Valid() && Sorted(l.Model())
 ensures l.Valid()

 ensures l.Model()==delDup(old(l.Model()),|old(l.Model())|)
 //ensures (set x | x in old(l.Model())) == (set x | x in l.Model())
 //ensures StrictSorted(l.Model())

 ensures l.Iterators() >= old(l.Iterators())
 ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index()
 ensures mit==delMap(old(l.Model()),(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),|old(l.Model())|)
{
  ghost var validSet:=(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index()));
  ghost var omodel:=l.Model();


  var it2:=l.Begin(); 
  var it1:=it2.Copy();
  var b := it1.HasNext();

  if (b) 
   { 
     
     mit:=delMap(old(l.Model()),validSet,1);

     var _ := it2.Next();
     ghost var j:=1; //to traverse old(l.Model())
     ghost var p:=0;//first occurrence in old(l.Model()) of current element it1

     assert it2.HasNext?() ==> it1.HasNext?() && l.Model()[it1.Index()+1]==l.Model()[it2.Index()];
     assert it2.Index()==1 && it1.Index()==0;
  

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
     invariant forall k | p <= k < j ::old(l.Model())[k]==old(l.Model())[j-1]==l.Model()[it1.Index()]
     invariant b == it2.HasNext?()

     //invariant (set x | x in old(l.Model())) == (set x | x in l.Model())
     //invariant Sorted(l.Model()) && StrictSorted(l.Model()[..it2.Index()])

     invariant l.Iterators() >= old(l.Iterators())
     invariant it1 !in old(l.Iterators()) && it2 !in old(l.Iterators())
     invariant it2.Index()==|delDup(old(l.Model()),j)|<=j
     //invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index())>=j :: it.Index()>=it2.Index();
     //invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && it.Valid() && it.Index()>it2.Index() :: old(it.Index())>j;

     invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
       it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index()<=old(it.Index())
     //invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit && old(it.Index())<j
     //   ::mit[old(it.Index())]<it2.Index()
     //invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit && old(it.Index())>=j
     //   ::mit[old(it.Index())]>=it2.Index()
     invariant mit==delMap(old(l.Model()),(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),j)
   { ghost var pmodel:=l.Model();
     
       assert  j in mit ==> mit[j]==|delDup(old(l.Model()),j)|;
     
     var it1Peek := it1.Peek();
     var it2Peek := it2.Peek();
     if (it1Peek == it2Peek) 
     {  assert old(l.Model())[j..]==l.Model()[it2.Index()..];
        assert old(l.Model())[j..][0]==l.Model()[it2.Index()..][0];
        assert old(l.Model())[j]==l.Model()[it2.Index()];
        assert l.Model()[it1.Index()]==old(l.Model())[j-1];
        ghost var oit2:=it2.Index();
          
        assert it2 !in old(l.Iterators()); 
        assert j<j+1 && old(l.Model())[j]==old(l.Model())[j-1];
        assert !validIt(old(l.Model()),j+1,j);
        
        delMapRange(old(l.Model()),validSet,j);     
        
      it2 := l.Erase(it2);  
          
        assert forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit && old(it.Index()) <j
          ::it.Valid() && mit[old(it.Index())]==it.Index()<j;
        assert forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit && old(it.Index()) >j
          ::it.Valid() && mit[old(it.Index())]==it.Index()+1;
        updateMapNV(old(l.Model()),validSet,j);
     

      j:=j+1;

        assert l.Model()==pmodel[..oit2]+pmodel[oit2+1..];
        assert l.Model()[..it2.Index()]==delDup(old(l.Model()),j);    
       
        mit:=delMap(old(l.Model()),validSet,j);

         
        assert forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index();
        assert mit==delMap(old(l.Model()),validSet,j);
        assert l.Model()[it2.Index()..]==old(l.Model())[j..];


    }
  else 
  {   
      assert  old(l.Model())[j]==l.Model()[it2.Index()]!=l.Model()[it1.Index()]==old(l.Model())[j-1];
      assert l.Model()[it2.Index()..]==[l.Model()[it2.Index()]]+l.Model()[it2.Index()+1..];


      assert validIt(old(l.Model()),j+1,j);
      updateMapV(old(l.Model()),validSet,j);
      assert delMap(old(l.Model()),validSet,j+1)==delMap(old(l.Model()),validSet,j);
      
      var _ := it2.Next(); 
      var _ := it1.Next();
           
      p:=j;
      j:=j+1;
      assert l.Model()[it2.Index()..]==old(l.Model())[j..];
      assert l.Model()[..it2.Index()]==delDup(old(l.Model()),j); 

      mit:=delMap(old(l.Model()),validSet,j);
      assert forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index();
      assert mit==delMap(old(l.Model()),validSet,j);
  }
  b:=it2.HasNext();  

}
    assert mit==delMap(old(l.Model()),validSet,j);
    assert j==|old(l.Model())| && it2.Index()==|l.Model()|;
    assert l.Model()==delDup(old(l.Model()),|old(l.Model())|);


    //assert forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index();
   }
   else {
         mit:=map[];
       }

   }
