include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"

predicate Sorted(xs:seq<int>)
{ forall i,j | 0<=i<=j<|xs| :: xs[i]<=xs[j]}


predicate StrictSorted(xs:seq<int>)
{ forall i,j | 0<=i<j<|xs| :: xs[i]<xs[j]}
 
function ValidIt(xs:seq<int>,i:int):bool
requires -1<=i<=|xs|
ensures i<=0==> ValidIt(xs,i)
ensures i==|xs| ==> ValidIt(xs,i)
ensures 0<i<|xs| ==> ValidIt(xs,i)==(xs[i]!=xs[i-1])
{
 if (i<=0) then true
 else if (i==|xs|) then true
 else xs[i]!=xs[i-1]

}

function DelDup(xs:seq<int>,i:int):seq<int>//[0,i)
requires 0<=i<=|xs|
ensures i==0 ==>DelDup(xs,i)==[]
ensures i==1 ==>DelDup(xs,i)==[xs[0]]
ensures i>1 && xs[i-1]!=xs[i-2] ==> DelDup(xs,i)==DelDup(xs,i-1)+[xs[i-1]]
ensures i>1 && xs[i-1]==xs[i-2] ==> DelDup(xs,i)==DelDup(xs,i-1)
{
 if (i==0) then []
 else if (i==1) then [xs[0]]
 else if (xs[i-1]!=xs[i-2]) then DelDup(xs,i-1)+[xs[i-1]]
 else DelDup(xs,i-1)

}


lemma PropDelDupAux(oxs:seq<int>,xs:seq<int>,i:int,j:int)
requires 0<=i<=|oxs| && 0<=j<= |xs| && xs[..j]==DelDup(oxs,i) && xs[j..]==oxs[i..] && Sorted(oxs)
 ensures (set x | x in oxs) == (set x | x in xs)
 ensures StrictSorted(xs[..|DelDup(oxs,i)|])


lemma PropDelDup(oxs:seq<int>,xs:seq<int>)
requires  xs==DelDup(oxs,|oxs|) && Sorted(oxs)
 ensures (set x | x in oxs) == (set x | x in xs)
 ensures StrictSorted(xs[..|DelDup(oxs,|oxs|)|])

method ElimDup(l:LinkedList<int>)  
 modifies l, l.Repr()
 requires allocated(l.Repr())
 ensures fresh(l.Repr()-old(l.Repr()))
 ensures allocated(l.Repr())

 requires l.Valid() && Sorted(l.Model())
 ensures l.Valid()

 ensures l.Model()==DelDup(old(l.Model()),|old(l.Model())|)
 ensures (set x | x in old(l.Model())) == (set x | x in l.Model())
 ensures StrictSorted(l.Model())

 ensures l.Iterators() >= old(l.Iterators())
 ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && ValidIt(old(l.Model()),old(it.Index()))
      ::it.Valid() && it.Parent()==old(it.Parent()) && 
      if (old(it.Index()==-1)) then it.Index()==-1
      else it.Index()==|DelDup(old(l.Model()),old(it.Index()))|
{
    ghost var validSet:=(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index()));
    ghost var omodel:=l.Model();


   var it2:=l.First(); 
   var it1:=it2.Copy();
   var b := it1.HasPeek();

   if (b) 
   { 
     
     
    it2.Next();
    ghost var j:=1; //to traverse old(l.Model())
    ghost var p:=0;//first occurrence in old(l.Model()) of current element it1

    assert it2.HasPeek?() ==> it1.HasPeek?() && l.Model()[it1.Index()+1]==l.Model()[it2.Index()];
    assert it2.Index()==1 && it1.Index()==0;
  
    

    b := it2.HasPeek();
    while b
     decreases |l.Model()| - it2.Index()
     invariant allocated(l.Repr())
     invariant fresh(l.Repr()-old(l.Repr()))

     invariant l.Valid()
     invariant it2 in l.Iterators() && it1 in l.Iterators()
     invariant it1.Parent() == l && it2.Parent()==l
     invariant it1.Valid() && it2.Valid()
     invariant it1.Index() >=0 && it2.Index()>=0
     invariant it2.Index()==it1.Index()+1 
     invariant it2.HasPeek?() ==> it1.HasPeek?() && l.Model()[it1.Index()+1]==l.Model()[it2.Index()]
     invariant j+(|l.Model()| - it2.Index())==|omodel| && 1<=j<=|old(l.Model())| 

    invariant l.Model()[..it2.Index()]==DelDup(old(l.Model()),j)    
    invariant old(l.Model())[j-1]==l.Model()[it1.Index()]
    invariant l.Model()[it2.Index()..]==old(l.Model())[j..]
    
    invariant forall k | p <= k < j ::old(l.Model())[k]==old(l.Model())[j-1]==l.Model()[it1.Index()]
    invariant b == it2.HasPeek?()
    // invariant (set x | x in old(l.Model())) == (set x | x in l.Model())
    // invariant Sorted(l.Model()) && StrictSorted(l.Model()[..it2.Index()])

    invariant l.Iterators() >= old(l.Iterators())
    invariant it1 !in old(l.Iterators()) && it2 !in old(l.Iterators())
    invariant it2.Index()==|DelDup(old(l.Model()),j)|<=j
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && ValidIt(old(l.Model()),old(it.Index())) && old(it.Index())<j
         ::it.Valid() && it.Parent()==old(it.Parent()) &&
          if (old(it.Index()==-1)) then it.Index()==-1
          else it.Index()==|DelDup(old(l.Model()),old(it.Index()))|<it2.Index()

         //it.Index()==|DelDup(old(l.Model()),old(it.Index()))|<it2.Index()
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index())>=j
         ::it.Valid() && it.Parent()==old(it.Parent()) && 
           it.Index()==old(it.Index())-(j-|DelDup(old(l.Model()),j)|)
   { ghost var pmodel:=l.Model();

     var it1Peek := it1.Peek();
     var it2Peek := it2.Peek();
     if (it1Peek == it2Peek) 
      {   assert old(l.Model())[j..]==l.Model()[it2.Index()..];
          assert old(l.Model())[j..][0]==l.Model()[it2.Index()..][0];
          assert old(l.Model())[j]==old(l.Model())[j..][0]==l.Model()[it2.Index()..][0]==l.Model()[it2.Index()];
          assert l.Model()[it1.Index()]==old(l.Model())[j-1];
          
          ghost var oit2:=it2.Index();
          //assert !validIt(old(l.Model()),j);
          
        it2 := l.Erase(it2); 


        j:=j+1; 
          
          assert l.Model()==pmodel[..oit2]+pmodel[oit2+1..];
          assert l.Model()[..it2.Index()]==DelDup(old(l.Model()),j);    
        
      }
     else 
       {   
        assert  old(l.Model())[j]==l.Model()[it2.Index()]!=l.Model()[it1.Index()]==old(l.Model())[j-1];
        assert l.Model()[it2.Index()..]==[l.Model()[it2.Index()]]+l.Model()[it2.Index()+1..];
        assert ValidIt(old(l.Model()),j);

        it2.Next(); 
        it1.Next();
           
        p:=j;
        j:=j+1;
        
        assert l.Model()[it2.Index()..]==old(l.Model())[j..];
        assert l.Model()[..it2.Index()]==DelDup(old(l.Model()),j);    
          }
     b:=it2.HasPeek();  
         
    }
   
    assert j==|old(l.Model())| && it2.Index()==|l.Model()|;
    assert l.Model()==DelDup(old(l.Model()),|old(l.Model())|);
       //propDelDupAux(old(l.Model()),l.Model(),|old(l.Model())|,|l.Model()|);
PropDelDup(old(l.Model()),l.Model());

   }
   else {
       }


  }
