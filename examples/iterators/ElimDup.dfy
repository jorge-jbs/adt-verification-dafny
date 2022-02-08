include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"

  predicate Sorted(xs:seq<int>)
  { forall i,j | 0<=i<=j<|xs| :: xs[i]<=xs[j]}


  predicate StrictSorted(xs:seq<int>)
  { forall i,j | 0<=i<j<|xs| :: xs[i]<xs[j]}
 
function validIt(xs:seq<int>,i:int):bool
requires 0<=i<=|xs|
ensures i==0==> validIt(xs,i)
ensures i==|xs| ==> validIt(xs,i)
ensures 0<i<|xs| ==> validIt(xs,i)==(xs[i]!=xs[i-1])
{
 if (i==0) then true
 else if (i==|xs|) then true
 else xs[i]!=xs[i-1]

}

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


lemma propDelDupAux(oxs:seq<int>,xs:seq<int>,i:int,j:int)
requires 0<=i<=|oxs| && 0<=j<= |xs| && xs[..j]==delDup(oxs,i) && xs[j..]==oxs[i..] && Sorted(oxs)
 ensures (set x | x in oxs) == (set x | x in xs)
 ensures StrictSorted(xs[..|delDup(oxs,i)|])


lemma propDelDup(oxs:seq<int>,xs:seq<int>)
requires  xs==delDup(oxs,|oxs|) && Sorted(oxs)
 ensures (set x | x in oxs) == (set x | x in xs)
 ensures StrictSorted(xs[..|delDup(oxs,|oxs|)|])

method {:verify true} elimDup(l:LinkedList)  

 modifies l, l.Repr()
 requires l.Valid() && Sorted(l.Model())
 requires forall x | x in l.Repr() :: allocated(x)
 ensures l.Valid()

 ensures l.Model()==delDup(old(l.Model()),|old(l.Model())|)
 ensures (set x | x in old(l.Model())) == (set x | x in l.Model())
 ensures StrictSorted(l.Model())

 ensures l.Iterators() >= old(l.Iterators())
 ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && validIt(old(l.Model()),old(it.Index()))
      ::it.Valid() && it.Index()==|delDup(old(l.Model()),old(it.Index()))|


 ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
 ensures fresh(l.Repr()-old(l.Repr()))
 ensures forall x | x in l.Repr() :: allocated(x)
{
    ghost var validSet:=(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index()));
    ghost var omodel:=l.Model();


   var aux;
   var it2:=l.Begin(); 
   var it1:=it2.Copy();
   if (it1.HasNext()) 
   { 
     
     
     aux:=it2.Next();
     ghost var j:=1; //to traverse old(l.Model())
     ghost var p:=0;//first occurrence in old(l.Model()) of current element it1

     assert it2.HasNext() ==> it1.HasNext() && l.Model()[it1.Index()+1]==l.Model()[it2.Index()];
     assert it2.Index()==1 && it1.Index()==0;
  
    


   while (it2.HasNext())
    decreases |l.Model()| - it2.Index()
    invariant l.Valid()
    invariant it2 in l.Iterators() && it1 in l.Iterators()
    invariant it1.Parent() == l && it2.Parent()==l
    invariant it1.Valid() && it2.Valid()
    invariant it2.Index()==it1.Index()+1 
    invariant it2.HasNext() ==> it1.HasNext() && l.Model()[it1.Index()+1]==l.Model()[it2.Index()]
    invariant j+(|l.Model()| - it2.Index())==|omodel| && 1<=j<=|old(l.Model())| 

    invariant l.Model()[..it2.Index()]==delDup(old(l.Model()),j)    
    invariant old(l.Model())[j-1]==l.Model()[it1.Index()]
    invariant l.Model()[it2.Index()..]==old(l.Model())[j..]
        
    invariant forall k | p<=k<j ::old(l.Model())[k]==old(l.Model())[j-1]==l.Model()[it1.Index()]

   // invariant (set x | x in old(l.Model())) == (set x | x in l.Model())
   // invariant Sorted(l.Model()) && StrictSorted(l.Model()[..it2.Index()])

    invariant l.Iterators() >= old(l.Iterators())
    invariant it1 !in old(l.Iterators()) && it2 !in old(l.Iterators())
    invariant it2.Index()==|delDup(old(l.Model()),j)|<=j
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && validIt(old(l.Model()),old(it.Index())) && old(it.Index())<j
         ::it.Valid() && it.Index()==|delDup(old(l.Model()),old(it.Index()))|<it2.Index()
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index())>=j
         ::it.Valid() && it.Index()==old(it.Index())-(j-|delDup(old(l.Model()),j)|)


    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
    //forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant forall x | x in l.Repr() :: allocated(x)

   { ghost var pmodel:=l.Model();

     if (it1.Peek()==it2.Peek()) 
      {   assert old(l.Model())[j..]==l.Model()[it2.Index()..];
          assert old(l.Model())[j..][0]==l.Model()[it2.Index()..][0];
          assert old(l.Model())[j]==old(l.Model())[j..][0]==l.Model()[it2.Index()..][0]==l.Model()[it2.Index()];
          assert l.Model()[it1.Index()]==old(l.Model())[j-1];
          
          ghost var oit2:=it2.Index();
          //assert !validIt(old(l.Model()),j);
          
        it2 := l.Erase(it2); 


        j:=j+1; 
          
          assert l.Model()==pmodel[..oit2]+pmodel[oit2+1..];
          assert l.Model()[..it2.Index()]==delDup(old(l.Model()),j);    
        
      }
     else 
       {   
         assert  old(l.Model())[j]==l.Model()[it2.Index()]!=l.Model()[it1.Index()]==old(l.Model())[j-1];
         assert l.Model()[it2.Index()..]==[l.Model()[it2.Index()]]+l.Model()[it2.Index()+1..];
          assert validIt(old(l.Model()),j);

         aux:=it2.Next(); 
         aux:=it1.Next();
           
           p:=j;
           j:=j+1;
           assert l.Model()[it2.Index()..]==old(l.Model())[j..];
           assert l.Model()[..it2.Index()]==delDup(old(l.Model()),j);    
          }
         
      }
   
    assert j==|old(l.Model())| && it2.Index()==|l.Model()|;
    assert l.Model()==delDup(old(l.Model()),|old(l.Model())|);
       //propDelDupAux(old(l.Model()),l.Model(),|old(l.Model())|,|l.Model()|);
propDelDup(old(l.Model()),l.Model());

   }
   else {
       }


  }