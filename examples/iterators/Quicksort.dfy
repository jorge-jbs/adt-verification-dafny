include "../../src/linear/adt/List.dfy"
include "../../src/linear/impl/LinkedList.dfy"

predicate GSorted(xs:seq<int>,c:int,f:int)
  { forall i,j | 0<=c<=i<=j<f<=|xs| :: xs[i]<=xs[j]}

lemma  swapMultisetAux(xs:seq<int>,ys:seq<int>, i:int, j:int)
requires 0<=i<|xs| && 0<=j<|ys| && i<=j && |xs|==|ys|
requires forall z | 0<=z<|xs| && z!=i && z!=j :: xs[z]==ys[z]
requires xs[i]==ys[j] && xs[j]==ys[i]
ensures multiset(xs)==multiset(ys)
{ 
 if (i==j) {assert xs==ys;} 
 else{  
 calc=={
   multiset(xs);{assert xs==xs[..i]+xs[i..j]+xs[j..];}
   multiset(xs[..i]+xs[i..j]+xs[j..]);
   {assert xs[i..j]==[xs[i]]+xs[i+1..j]; assert xs[j..] == [xs[j]]+xs[j+1..];}
   multiset(xs[..i]+[xs[i]]+xs[i+1..j]+[xs[j]]+xs[j+1..]);
   multiset(xs[..i])+multiset{xs[i]}+multiset(xs[i+1..j])+multiset{xs[j]}+multiset(xs[j+1..]);
   multiset(xs[..i])+multiset{xs[i]}+multiset{xs[j]}+multiset(xs[i+1..j])+multiset(xs[j+1..]);
   multiset(xs[..i])+multiset{xs[j]}+multiset{xs[i]}+multiset(xs[i+1..j])+multiset(xs[j+1..]);
   multiset(xs[..i])+multiset{xs[j]}+multiset(xs[i+1..j])+multiset{xs[i]}+multiset(xs[j+1..]);
   {assert xs[i]==ys[j] && xs[j]==ys[i]; 
   assert xs[..i]==ys[..i];
    assert xs[i+1..j]==ys[i+1..j];
    assert xs[j+1..]==ys[j+1..];}
   multiset(ys[..i])+multiset{ys[i]}+multiset(ys[i+1..j])+multiset{ys[j]}+multiset(ys[j+1..]);
   {assert ys[i..j]==[ys[i]]+ys[i+1..j]; assert ys[j..] == [ys[j]]+ys[j+1..];}
   multiset(ys[..i]+[ys[i]]+ys[i+1..j]+[ys[j]]+ys[j+1..]);
      {assert [ys[i]]+ys[i+1..j]==ys[i..j]; assert [ys[j]]+ys[j+1..]==ys[j..];}
   multiset(ys[..i]+ys[i..j]+ys[j..]);
       {assert ys==ys[..i]+ys[i..j]+ys[j..];}
   multiset(ys);
}
 }
}

lemma swapMultiset(xs:seq<int>,ys:seq<int>, i:int, j:int)
requires 0<=i<|xs| && 0<=j<|ys| && |xs|==|ys|
requires forall z | 0<=z<|xs| && z!=i && z!=j :: xs[z]==ys[z]
requires xs[i]==ys[j] && xs[j]==ys[i]
ensures multiset(xs)==multiset(ys)
{
  if (i<=j) {swapMultisetAux(xs,ys,i,j);}
  else {swapMultisetAux(xs,ys,j,i);}


}


lemma multisetPreservesStrictSmaller (a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires |a|==|b| && 0 <= c <= f + 1 <= |b| 
requires (forall j :: c <= j <= f ==> a[j] < x)
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures (forall j :: c <= j <= f ==> b[j] < x)
{if (c<=f){ 
 forall j | c<=j<=f 
   ensures b[j]<x
  {   assert b[j] in b[c..f+1];
      assert b[j] in multiset(a[c..f+1]);
   }
}
}


lemma multisetPreservesStrictGreater (a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires |a|==|b| && 0 <= c <= f + 1 <= |b| 
requires (forall j :: c <= j <= f ==> a[j] > x)
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures (forall j :: c <= j <= f ==> b[j] > x)
{if (c<=f){ 
 forall j | c<=j<=f 
   ensures b[j]>x
  {   assert b[j] in b[c..f+1];
      assert b[j] in multiset(a[c..f+1]);
   }
}
}

lemma seqSplit(s:seq<int>, c:int, p:int, f:int)
requires 0<=c<=p<=f+1<=|s|
ensures multiset(s[c..f+1])==multiset(s[c..p])+multiset(s[p..f+1])
{
    calc=={
  multiset(s[c..f+1]);
  {assert s[c..f+1]==s[c..p]+s[p..f+1];}
  multiset(s[c..p]+s[p..f+1]);
  multiset(s[c..p])+multiset(s[p..f+1]);
}
}

lemma subsecEq(xs:seq<int>,ys:seq<int>,c:int,f:int)
requires 0<=c<=f<=|xs|==|ys|
requires xs==ys
ensures xs[c..f]==ys[c..f] && xs[c..]==ys[c..]&&xs[..f]==ys[..f]
{}

//Additional ghost results to know additional information 
method swapG(l:LinkedList,p:ListIterator,q:ListIterator, ghost c:ListIterator, ghost n:int)
modifies l, l.Repr(),p,q
requires forall x | x in l.Repr() :: allocated(x)
requires l.Valid() && p.Valid() && q.Valid()
requires p in l.Iterators() && q in l.Iterators() 
requires p.Parent()==l && q.Parent()==l
requires p.HasNext() && q.HasNext()

requires c in l.Iterators() && c.Valid() && c.Parent()==l
requires 0<=c.Index()<|l.Model()| && 0<=n<=|l.Model()| && c.Index()+n<=|l.Model()|
requires c.Index()<=p.Index()<c.Index()+n && c.Index()<=q.Index()<c.Index()+n



ensures l.Valid() && p.Valid() && q.Valid()
ensures p.Parent()==l && q.Parent()==l

ensures |l.Model()|==|old(l.Model())|
ensures l.Model()[old(q.Index())] == old(l.Model())[old(p.Index())]
ensures l.Model()[old(p.Index())] == old(l.Model())[old(q.Index())]
ensures forall i | 0<=i<|l.Model()| && i!=old(p.Index()) && i != old(q.Index()) :: l.Model()[i]==old(l.Model())[i]
ensures multiset(l.Model())==multiset(old(l.Model()))

ensures l.Iterators()>=old(l.Iterators())
ensures p in l.Iterators() && q in l.Iterators() && p.Index()==old(p.Index()) && q.Index()==old(q.Index())
ensures forall it | it in old(l.Iterators()) && old(it.Valid())::it.Valid() && it.Index()==old(it.Index())

ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)

//ADDITIONAL GHOST INFO
ensures c in l.Iterators() && c.Valid() && c.Parent()==l && c.Index()==old(c.Index())
ensures |l.Model()|==|old(l.Model())| && 0<=c.Index()<=c.Index()+n<=|l.Model()|
ensures multiset(l.Model()[c.Index()..c.Index()+n])== multiset(old(l.Model()[c.Index()..c.Index()+n]))
//ensures l.Model()[..c.Index()] == old(l.Model()[..c.Index()]) && l.Model()[c.Index()+n..] == old(l.Model()[c.Index()+n..]) 

{
     var auxq :=q.Peek();
     var auxp:= p.Peek();
     p.Set(auxq);
     q.Set(auxp);
     
      swapMultiset(l.Model(),old(l.Model()),p.Index(),q.Index());
      assert 0<=c.Index()<=c.Index()+n<=|l.Model()|;
      swapMultiset(l.Model()[c.Index()..c.Index()+n],old(l.Model()[c.Index()..c.Index()+n]),p.Index()-c.Index(),q.Index()-c.Index());
     
}



method  {:verify false} partitionG(l:LinkedList,c:ListIterator,n:int, x:int) returns (p:ListIterator,nL:int,q:ListIterator,nG:int)
modifies l, l.Repr()
requires l.Valid() && c.Valid() 
requires c.Parent()==l && c in l.Iterators() 
requires 0<=n<= |l.Model()| && 0<=c.Index()<=c.Index()+n<=|l.Model()|
requires forall x | x in l.Repr() :: allocated(x)

ensures l.Valid()
ensures p.Valid() && q.Valid()
ensures p.Parent()==l && q.Parent()==l && c.Parent()==l 
ensures c.Valid() && c.Index()==old(c.Index()) 
ensures 0<=c.Index()<=p.Index()<=q.Index()<=c.Index()+n<=|l.Model()|
ensures |l.Model()|==|old(l.Model())|

ensures l.Iterators() >= {p,q}+old(l.Iterators())
ensures forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Index()==old(it.Index())


ensures multiset(l.Model()[c.Index()..c.Index()+n])== multiset(old(l.Model()[c.Index()..c.Index()+n]))
ensures l.Model()[..c.Index()] == old(l.Model()[..c.Index()]) && l.Model()[c.Index()+n..] == old(l.Model()[c.Index()+n..]) 
ensures forall z | c.Index()<=z<p.Index() :: l.Model()[z]<x
ensures forall z | p.Index()<=z<q.Index() :: l.Model()[z]==x
ensures forall z | q.Index()<=z<c.Index()+n:: l.Model()[z]>x
ensures nL==p.Index()-c.Index() && nG == c.Index()+n-q.Index()
ensures x in multiset(old(l.Model()[c.Index()..c.Index()+n])) ==> p.Index()<q.Index()

ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)
{
  var aux;
  p:=c.Copy();
  q:=c.Copy();
  var r:=c.Copy();

   var i:=0;nL:=0;nG:=0;

   while (i<n)
    decreases n-i
    invariant 0<=i<=n
    invariant l.Valid() && c.Valid() && c.Parent()==l 
    invariant p.Valid() && q.Valid() && r.Valid()
    invariant p.Parent()==l && q.Parent()==l && r.Parent()==l
    invariant r.Index()==c.Index()+i && c.Index()<=p.Index()<=q.Index()<=r.Index()<=c.Index()+n<=|l.Model()|
    invariant |l.Model()|==|old(l.Model())|
    invariant  multiset(l.Model())==multiset(old(l.Model()))
    invariant nL==p.Index()-c.Index() && nG == r.Index()-q.Index()
    invariant x in multiset(l.Model()[c.Index()..r.Index()]) ==> p.Index()<q.Index()
    
    invariant forall z | c.Index()<=z<p.Index() :: l.Model()[z]<x
    invariant forall z | p.Index()<=z<q.Index() :: l.Model()[z]==x
    invariant forall z | q.Index()<=z<r.Index() :: l.Model()[z]>x

    invariant multiset(l.Model()[c.Index()..c.Index()+n])== multiset(old(l.Model()[c.Index()..c.Index()+n]))
    invariant l.Model()[..c.Index()] == old(l.Model()[..c.Index()]) && l.Model()[c.Index()+n..] == old(l.Model()[c.Index()+n..]) 

    invariant l.Iterators() >= {p,q,r}+old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Index()==old(it.Index())


    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant forall x | x in l.Repr() :: allocated(x)
  {
   if (r.Peek()>x)
    {  nG:=nG+1; }
   else if (r.Peek()==x)
    { 
     swapG(l,q,r,c,n);
     aux:=q.Next();
    }  
   else {
   
     swapG(l,q,r,c,n);
     swapG(l,p,q,c,n);
     aux:=p.Next();
     aux:=q.Next();
     nL:=nL+1;
     
  }
  aux:= r.Next();
  i:=i+1;
    
}
assert r.Index()==c.Index()+n;

}

method {:verify true} {:timeLimitMultiplier 6} quicksort(l:LinkedList,c:ListIterator,n:int)
decreases n
modifies l, l.Repr()
requires l.Valid() && c in l.Iterators() && c.Valid() && c.Parent()==l 
requires forall x | x in l.Repr() :: allocated(x)
requires 0<=c.Index()<=|l.Model()| && 0<=n<=|l.Model()| && c.Index()+n<=|l.Model()|

ensures l.Valid() && c in l.Iterators() && c.Valid() && c.Parent()==l 
ensures c.Valid() &&  c.Index()==old(c.Index()) && 0<=c.Index()<=c.Index()+n<=|l.Model()|

ensures multiset(l.Model()[c.Index()..c.Index()+n])== multiset(old(l.Model())[c.Index()..c.Index()+n])
ensures GSorted(l.Model(),c.Index(),c.Index()+n)
ensures l.Model()[..c.Index()] == old(l.Model()[..c.Index()]) && l.Model()[c.Index()+n..] == old(l.Model()[c.Index()+n..]) 


ensures l.Iterators() >= old(l.Iterators())
ensures forall it | it in old(l.Iterators()) && old(it.Valid()) ::it.Valid() && it.Index()==old(it.Index())

ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
ensures fresh(l.Repr()-old(l.Repr()))
ensures forall x | x in l.Repr() :: allocated(x)
{
  var p,q:ListIterator;var nL,nG:int;
  if (n>1)
  {
      var omodel:=l.Model();
   
   p,nL,q,nG:=partitionG(l,c,n,c.Peek());
     
      assert q.Index()+nG==c.Index()+n;
   
      var omodel1:=l.Model();
      assert multiset(omodel1[c.Index()..c.Index()+n])== multiset(omodel[c.Index()..c.Index()+n]);
      assert forall z | c.Index()+nL <= z <q.Index() ::omodel1[z]==omodel1[c.Index()+nL];

   
   quicksort(l,c,nL);
    

      var omodel2:=l.Model();

      assert multiset(omodel2[c.Index()..c.Index()+nL])== multiset(omodel1[c.Index()..c.Index()+nL]);
      assert omodel2[..c.Index()] == omodel1[..c.Index()] && omodel2[c.Index()+nL..] == omodel1[c.Index()+nL..]; 
      
      seqSplit(omodel2,c.Index(),c.Index()+nL,c.Index()+n-1);
      
      assert 0<=c.Index()<=c.Index()+nL<=c.Index()+n<=|omodel1|;
      seqSplit(omodel1,c.Index(),c.Index()+nL,c.Index()+n-1);
    
      calc =={
        multiset(omodel2[c.Index()..c.Index()+n]);
        multiset(omodel2[c.Index()..c.Index()+nL])+multiset(omodel2[c.Index()+nL..c.Index()+n]);
        {assert omodel2[c.Index()+nL..] == omodel1[c.Index()+nL..];
        subsecEq(omodel2[c.Index()+nL..],omodel1[c.Index()+nL..],0,n-nL); 
         assert omodel2[c.Index()+nL..c.Index()+n] == omodel1[c.Index()+nL..c.Index()+n]; }
        multiset(omodel1[c.Index()..c.Index()+nL])+multiset(omodel1[c.Index()+nL..c.Index()+n]);
        multiset(omodel1[c.Index()..c.Index()+n]);
      }
   

       multisetPreservesStrictSmaller(omodel1,omodel2,c.Index(),c.Index()+nL-1,omodel2[c.Index()+nL]);
       assert GSorted(omodel2,c.Index(),c.Index()+nL);
       assert forall z | c.Index()+nL <= z <q.Index() ::omodel2[z]==omodel2[c.Index()+nL];

    quicksort(l,q,nG);
    
      assert multiset(l.Model()[q.Index()..q.Index()+nG])== multiset(omodel2[q.Index()..q.Index()+nG]);
      assert l.Model()[..q.Index()] == omodel2[..q.Index()] && l.Model()[q.Index()+nG..] == omodel2[q.Index()+nG..]; 
      assert c.Index()+nL<=q.Index();
      seqSplit(l.Model(),c.Index(),q.Index(),c.Index()+n-1);
      seqSplit(omodel2,c.Index(),q.Index(),c.Index()+n-1);
      calc =={
        multiset(l.Model()[c.Index()..c.Index()+n]);
        multiset(l.Model()[c.Index()..q.Index()])+multiset(l.Model()[q.Index()..c.Index()+n]);
        {assert l.Model()[c.Index()..q.Index()] == omodel2[c.Index()..q.Index()]; }
        multiset(omodel2[c.Index()..q.Index()])+multiset(omodel2[q.Index()..c.Index()+n]);
        multiset(omodel2[c.Index()..c.Index()+n]);
      }

      assert multiset(l.Model()[c.Index()..c.Index()+n])== multiset(old(l.Model())[c.Index()..c.Index()+n]);

      multisetPreservesStrictGreater(omodel2,l.Model(),q.Index(),c.Index()+n-1,omodel2[c.Index()+nL]);
      assert GSorted(l.Model(),q.Index(),c.Index()+n);
      assert GSorted(l.Model(),c.Index(),c.Index()+nL);

      assert l.Model()[c.Index()+nL..q.Index()]==omodel1[c.Index()+nL..q.Index()];
      assert forall z | c.Index()<=z<c.Index()+nL :: l.Model()[z]<l.Model()[c.Index()+nL];
      assert forall z | c.Index()+nL <= z <q.Index() :: l.Model()[z]==l.Model()[c.Index()+nL];
      assert forall z | q.Index()<=z<c.Index()+n:: l.Model()[z]>l.Model()[c.Index()+nL];
      assert GSorted(l.Model(),c.Index(),c.Index()+n);
  }
}




