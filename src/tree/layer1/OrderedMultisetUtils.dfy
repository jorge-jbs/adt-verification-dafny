

function Pick(s: multiset<int>): int
  requires s != multiset{}
{
  var x :| x in s; x
}


lemma {:verify true} sizeOfSet(s:multiset<int>,x:int)
requires x in s
ensures (s-multiset{x})+multiset{x}==s
{}

lemma {:verify true} sizes(s1:multiset<int>,s2:multiset<int>)
requires s1==s2
ensures |s1|==|s2|
{}

function {:induction s} minimum(s:multiset<int>):int
requires s != multiset{}
//ensures forall x | x in s :: minimum(s)<=x
{ 
  var x:=Pick(s);
  if (s-multiset{x}==multiset{}) then x
  else if (x < minimum(s-multiset{x})) then x
  else minimum(s-multiset{x})

}

lemma lmin(s:multiset<int>,x:int)
requires s != multiset{} && x in s
ensures x >= minimum(s)
{
  var y:=Pick(s);
  if (s-multiset{y} == multiset{}){assert s==multiset{y};assert x==y;}
  else if (minimum(s-multiset{y})==minimum(s)){}
  else{}
}


lemma lminimum(s:multiset<int>)
requires s != multiset{}
ensures minimum(s) in s && forall x | x in s :: minimum(s) <= x
{forall x | x in s
 ensures minimum(s) <= x {lmin(s,x);}}


//An element smaller than the rest of elements is the minimum
lemma {:verify true} lminimumrev(s:multiset<int>,x:int)
requires x in s && forall z | z in s :: x <= z
ensures x == minimum(s)
{
  lminimum(s);
  assert minimum(s) in s;
  if (x==minimum(s)){}
  else {assert x < minimum(s);
         assert false;}//contradiction
}

function {:induction s} maximum(s:multiset<int>):int
requires s != multiset{}
//ensures forall x | x in s :: maximum(s)>=x
{ 
  var x:=Pick(s);
  if (s-multiset{x}==multiset{}) then x
  else if (x > maximum(s-multiset{x})) then x
  else maximum(s-multiset{x})

}

lemma {:verify true} lmax(s:multiset<int>,x:int)
requires s != multiset{} && x in s
ensures x<=maximum(s)
{
  var y:=Pick(s);
  if (s-multiset{y} == multiset{}){assert s==multiset{y};assert x==y;}
  else if (maximum(s-multiset{y})==maximum(s)){}
  else{}
}


lemma lmaximum(s:multiset<int>)
requires s !=  multiset{}
ensures maximum(s) in s && forall x | x in s :: maximum(s) >= x
ensures forall x | x in s && s-multiset{x}!=multiset{} && x > maximum(s-multiset{x}) :: x==maximum(s) 
ensures forall x | x in s && s-multiset{x}!=multiset{} && x <= maximum(s-multiset{x}) :: maximum(s)==maximum(s-multiset{x}) 
{forall x | x in s
 ensures maximum(s) >= x {lmax(s,x);}}

lemma {:verify true} lmaximumOne(s:multiset<int>,x:int)
requires s!=multiset{} && x in s && s-multiset{x}!=multiset{} 
ensures if (x <= maximum(s-multiset{x})) then maximum(s) == maximum(s-multiset{x}) else maximum(s)==x
{
  lmaximum(s);
}


//Any element of the set bigger tahn the rest is the maximum
lemma {:verify true} lmaximumrev(s:multiset<int>,x:int)
requires x in s && forall z | z in s :: x >= z
ensures x == maximum(s)
{
  lmaximum(s);
   assert maximum(s) in s;
   if (x==maximum(s)){}
   else {assert x > maximum(s);
         assert false;}//contradiction
}

//If the multiset has two elements, if I remove the minimun, the maximum is the same: needed to prove First and Last
lemma {:verify true} max2Elems(s:multiset<int>)
requires |s|>=2
ensures s-multiset{minimum(s)} != multiset{} && maximum(s)==maximum(s-multiset{minimum(s)})
{
  lminimum(s);
  assert |s-multiset{minimum(s)}|==|s|-1>=1;
  //assert s-{minimum(s)} != {};
  lmax(s,minimum(s));
  assert minimum(s) in s && minimum(s) <= maximum(s-multiset{minimum(s)});
  lmaximumOne(s,minimum(s)); 

}

lemma {:verify true} lMaxMinOne(s:multiset<int>)
requires s != multiset{} && |s|==1
ensures maximum(s)==minimum(s)
{}


function msmaller(s:multiset<int>,x:int):multiset<int>
ensures forall z | z in msmaller(s,x) :: z < x && s[z]==msmaller(s,x)[z]
ensures forall z | z in s && z < x :: z in msmaller(s,x) 
{ if (s == multiset{}) then multiset{}
  else
    var y:=Pick(s);
    if (y < x) then 
       multiset{y} + msmaller(s-multiset{y},x)
    else 
       msmaller(s-multiset{y},x)
}

lemma {:verify true} smallerMin(s:multiset<int>)
requires s != multiset{}
ensures msmaller(s,minimum(s))==multiset{} && |msmaller(s,minimum(s))|==0
{}

lemma {:verify true} smallerMax(s:multiset<int>)
requires s != multiset{}
ensures msmaller(s,maximum(s))==s[maximum(s):=0] && |msmaller(s,maximum(s))|== |s|-s[maximum(s)]
{}
  
lemma smallerElem(s:multiset<int>,x:int)
requires s!=multiset{} && x in s && x != minimum(s)
ensures msmaller(s-multiset{minimum(s)},x)==msmaller(s,x)-multiset{minimum(s)}
ensures |msmaller(s-multiset{minimum(s)},x)|==|msmaller(s,x)|-1
{ lminimum(s);
  sizeOfSet(s,minimum(s));}

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

lemma {:induction s} lelemthrev(s:multiset<int>,x:int,k:int)
requires 0<=k<|s| && x in s && |msmaller(s,x)|==k
ensures x==elemth(s,k)
{
 if (k==0){  
   assert msmaller(s,x)==multiset{};
   assert forall z | z in s && z!=x :: z>x;
   lminimumrev(s,x);
   assert x==minimum(s);
   }
 else{ 
   var minim:=minimum(s);
   if (minim==x){smallerMin(s);}
   else{
     smallerElem(s,x);
     assert |msmaller(s-multiset{minim},x)|==k-1;
     lelemthrev(s-multiset{minim},x,k-1);
   }
   }
}

lemma {:verify true} firstAndLast(s:multiset<int>)
requires s!=multiset{}
ensures minimum(s)==elemth(s,0)
ensures maximum(s)==elemth(s,|s|-1)
{ 
  if (|s|==1) {
    lMaxMinOne(s);
    assert |s|-1==0;
    assert maximum(s)==minimum(s)==elemth(s,0);}
  else{
     
      var minim:=minimum(s);
      lminimum(s);
      assert minim in s;

      calc ==
      { elemth(s,|s|-1);{assert |s|-1 != 0;}
        elemth(s-multiset{minim},|s|-2);
         { assert s-multiset{minim}<s;
           sizeOfSet(s,minim);
           assert |s-multiset{minim}|==|s|-1;
           firstAndLast(s-multiset{minim});}
         maximum(s-multiset{minim});
          {  assert |s|>=2; assert minim==minimum(s);
             max2Elems(s);
             assert maximum(s-multiset{minim})==maximum(s);
          }
         maximum(s);
      }
      assume maximum(s)==elemth(s,|s|-1);
  }}






function isSortedSeq(xs:seq<int>):bool
{forall i,j::0<=i<j<|xs| ==> xs[i]<=xs[j]}


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


