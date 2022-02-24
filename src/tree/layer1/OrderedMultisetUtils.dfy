

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
{ if (s == multiset{}) then multiset{}
  else
    var y :| y in s;
    if (y < x) then 
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

