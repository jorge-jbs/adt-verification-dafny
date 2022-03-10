function Pick(s: set<int>): int
  requires s != {}
{
  var x :| x in s; x
}

lemma sizeOfSet(s:set<int>,x:int)
requires x in s
ensures (s-{x})+{x}==s
{}

lemma sizes(s1:set<int>,s2:set<int>)
requires s1==s2
ensures |s1|==|s2|
{}

lemma sizesContained(s1:set<int>,s2:set<int>)
requires s1 <= s2
ensures |s1| <= |s2|
{if (s1=={}) {}
 else{
  assert forall x | x in s1 :: x in s1;
 var z:=Pick(s1);
 calc  {
   |s1|; ==
   1+|s1-{z}|; <=
   {sizesContained(s1-{z},s2-{z});assert z in s2;}
   1 + |s2-{z}|; ==
   |s2|; 
  }
 }
}


lemma sizesStrictContained(s1:set<int>,s2:set<int>)
requires s1 < s2
ensures |s1| < |s2|
{
  sizesContained(s1,s2);
  assert |s1|<=|s2|;
  assume s1 == s2;
  sizes(s1,s2);
  assert false;
  }
//MINIMUM DEFINITION:  

function {:induction s} minimum(s:set<int>):int
requires s != {}
//ensures forall x | x in s :: minimum(s)<=x
{ 
  //var x :| x in s;
  var x:=Pick(s);
  if (s-{x}=={}) then x
  else if (x < minimum(s-{x})) then x
  else minimum(s-{x})

}

// Minimum is smaller or equal than all the set elements
lemma lmin(s:set<int>,x:int)
requires s!={} && x in s
ensures x>=minimum(s)
{
  var y:=Pick(s);
  if (s-{y} == {}){assert s=={y};assert x==y;}
  else if (minimum(s-{y})==minimum(s)){}
  else{}
}


lemma lminimum(s:set<int>)
requires s != {}
ensures minimum(s) in s && forall x | x in s :: minimum(s) <= x
{forall x | x in s
 ensures minimum(s) <= x {lmin(s,x);}}

//An element smaller than the rest of elements is the minimum
lemma lminimumrev(s:set<int>,x:int)
requires x in s && forall z | z in s && z!=x :: x < z
ensures x == minimum(s)
{
  lminimum(s);
  assert minimum(s) in s;
  if (x==minimum(s)){}
  else {assert x < minimum(s);
         assert false;}//contradiction
}

//MAXIMUM DEFINITION: 
function {:induction s} maximum(s:set<int>):int
requires s != {}
{ 
  var x:=Pick(s);
  if (s-{x}=={}) then x
  else if (x > maximum(s-{x})) then x
  else maximum(s-{x})
  
}

//Maximum is bigger or equal than all the set elements 
lemma lmax(s:set<int>,x:int)
requires s!={} && x in s
ensures x<=maximum(s)
{
  var y:=Pick(s);
  if (s-{y} == {}){assert s=={y};assert x==y;}
  else if (maximum(s-{y})==maximum(s)){}
  else{}
}


//maximum belongs to the set
lemma lmaximum(s:set<int>)
requires s != {}
ensures maximum(s) in s && forall x | x in s :: maximum(s) >= x
ensures forall x | x in s && s-{x}!={} && x > maximum(s-{x}) :: x==maximum(s) 
ensures forall x | x in s && s-{x}!={} && x <= maximum(s-{x}) :: maximum(s)==maximum(s-{x}) 
{forall x | x in s
 ensures maximum(s) >= x {lmax(s,x);}}

lemma lmaximumOne(s:set<int>,x:int)
requires s!={} && x in s && s-{x}!={} 
ensures if (x <= maximum(s-{x})) then maximum(s) == maximum(s-{x}) else maximum(s)==x
{
  lmaximum(s);
}

//Any element of the set bigger tahn the rest is the maximum
lemma lmaximumrev(s:set<int>,x:int)
requires x in s && forall z | z in s && z!=x :: x > z
ensures x == maximum(s)
{
  lmaximum(s);
   assert maximum(s) in s;
   if (x==maximum(s)){}
   else {assert x > maximum(s);
         assert false;}//contradiction
}

lemma lmaximum2(s:set<int>,x:int)
requires s!={} && x in s && s-{x}!={} && x < maximum(s-{x})
ensures maximum(s)!=x 
{lmaximum(s-{x});
assert maximum(s-{x}) in s;
lmax(s,maximum(s-{x}));
assert maximum(s-{x})<= maximum(s);
assert exists z | z in s :: z < maximum(s);
}


//If the set has two elements, if I remove the minimun, the maximum is the same: needed to prove First and Last
lemma max2Elems(s:set<int>)
requires |s|>=2
ensures s-{minimum(s)} != {} && maximum(s)==maximum(s-{minimum(s)})
{
  lminimum(s);
  assert |s-{minimum(s)}|==|s|-1>=1;
  //assert s-{minimum(s)} != {};
  lmax(s,minimum(s));
  assert minimum(s) in s && minimum(s) < maximum(s-{minimum(s)});
  lmaximumOne(s,minimum(s)); 

}

lemma {:verify true} lMaxMinOne(s:set<int>)
requires s != {} && |s|==1
ensures maximum(s)==minimum(s)
{}

function smaller(s:set<int>,x:int):set<int>
ensures forall z | z in smaller(s,x) :: z in s && z < x
ensures forall z | z in s && z < x :: z in smaller(s,x)
{set z | z in s && z < x}



lemma {:verify true} smallerMin(s:set<int>)
requires s != {}
ensures smaller(s,minimum(s))=={} && |smaller(s,minimum(s))|==0
{}


lemma {:verify true} smallerMax(s:set<int>)
requires s != {}
ensures smaller(s,maximum(s))==s-{maximum(s)} && |smaller(s,maximum(s))|== |s|-1
{ sizes(smaller(s,maximum(s)),s-{maximum(s)});
  assert |smaller(s,maximum(s))|==|s-{maximum(s)}|;
  lmaximum(s);
  sizeOfSet(s,maximum(s));
  }
  

lemma smallerElem(s:set<int>,x:int)
requires s!={} && x in s && x != minimum(s)
ensures smaller(s-{minimum(s)},x)==smaller(s,x)-{minimum(s)}
ensures |smaller(s-{minimum(s)},x)|==|smaller(s,x)|-1
{ lminimum(s);
  sizeOfSet(s,minimum(s));}

function elemth(s:set<int>,k:int):int
requires 0<=k<|s|
//ensures elemth(s,k) in s && |smaller(s,elemth(s,k))|==k
{
  var minim:=minimum(s);
  if (k==0) then minim
  else elemth(s-{minim},k-1)
}

lemma {:induction s,k} {:verify true} lelemth(s:set<int>,k:int)
requires 0<=k<|s|
ensures elemth(s,k) in s && |smaller(s,elemth(s,k))|==k
{ lminimum(s);
  if (k==0) { }
  else {
    lelemth(s-{minimum(s)},k-1);
    assert elemth(s,k) in s;
    calc =={
      |smaller(s,elemth(s,k))|;
      |set z | z in s && z < elemth(s,k)|;{assert k>0;}
      |set z | z in s && z < elemth(s-{minimum(s)},k-1)|;
      {assert s==(s-{minimum(s)})+{minimum(s)};
      assert minimum(s)<elemth(s-{minimum(s)},k-1);
      assert (set z | z in s && z < elemth(s-{minimum(s)},k-1))==(set z | z in s-{minimum(s)} && z < elemth(s-{minimum(s)},k-1)) + {minimum(s)};
      }
      |(set z | z in s-{minimum(s)} && z < elemth(s-{minimum(s)},k-1)) + {minimum(s)}|;
      |(set z | z in s-{minimum(s)} && z < elemth(s-{minimum(s)},k-1)) + {minimum(s)}|;

    }
  }
}



lemma {:induction s} lelemthrev(s:set<int>,x:int,k:int)
requires 0<=k<|s| && x in s && |smaller(s,x)|==k
ensures x==elemth(s,k)
{
 if (k==0){  
   assert smaller(s,x)=={};
   assert forall z | z in s && z!=x :: z>x;
   lminimumrev(s,x);
   assert x==minimum(s);
   }
 else{ 
   var minim:=minimum(s);
   if (minim==x){smallerMin(s);}
   else{
     smallerElem(s,x);
     assert |smaller(s-{minim},x)|==k-1;
     lelemthrev(s-{minim},x,k-1);
   }
   }

}


lemma {:verify true} firstAndLast(s:set<int>)
requires s!={}
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

      calc ==
      { elemth(s,|s|-1);{assert |s|-1 != 0;}
        elemth(s-{minim},|s|-2);
         { assert s-{minim}<s;
         assert |s-{minim}|==|s|-1;
           firstAndLast(s-{minim});}
        maximum(s-{minim});{max2Elems(s);}
        maximum(s);
      }
  }}



//Sorted seqs

function isSortedSeq(xs:seq<int>):bool
{forall i,j::0<=i<j<|xs| ==> xs[i]<xs[j]}

function seq2Set (xs:seq<int>):set<int>
{set x | x in xs::x}

function isSet(xs:seq<int>):bool
{forall i,j | 0 <= i < j < |xs| :: xs[i] != xs[j]}


lemma emptyset(xs:seq<int>)
ensures xs == [] <==> seq2Set(xs)=={}
{ assume xs != [];
  assert xs[0] in xs;
  assert xs[0] in seq2Set(xs);
}

lemma existsOne(xs:seq<int>,i:int,j:int)
requires isSet(xs) && |xs| > 0
requires 0<=i<=j<=|xs| && j-i < |xs| 
ensures exists k | 0 <= k < |xs| :: xs[k] !in xs[i..j];
{
 assert i>0 || j<|xs|;
 assert (i>0) ==> xs[0] !in xs[i..j];
 assert j<|xs| ==> xs[|xs|-1] !in xs[i..j];
}

//function lemma
function seq2SetContained(xs:seq<int>, i:int,j:int):bool
requires isSet(xs) 
requires |xs| > 0 && 0<=i<=j<=|xs| && j-i < |xs| 
ensures seq2Set(xs[i..j]) < seq2Set(xs)
ensures seq2SetContained(xs,i,j)
{

 if (i==j) then 
    sizesSeq2Set(xs); true
  
  else
    existsOne(xs,i,j);
    assert exists k | 0 <= k < |xs| :: xs[k] in  seq2Set(xs) && xs[k] !in  seq2Set(xs[i..j]);
    true
  
}


function set2Seq(s:set<int>):seq<int>
decreases s
{
  if s == {} then []
  else 
    var y := Pick(s);
    [y] + set2Seq(s - {y})
    
}

lemma sizesSet2Seq(s:set<int>)
ensures |set2Seq(s)|==|s|
{}

lemma  sizesSeq2Set(xs:seq<int>)
requires isSet(xs)//forall i,j|0 <= i < j < |xs| :: xs[i] != xs[j]
ensures |seq2Set(xs)| == |xs|
{if (xs==[]) {}
 else {sizesSeq2Set(xs[1..]);
       assert xs==[xs[0]]+xs[1..];
       assert seq2Set(xs)=={xs[0]}+seq2Set(xs[1..]);
       assert |seq2Set(xs)|==1+|seq2Set(xs[1..])|;}
}

lemma idem(s:set<int>)
ensures seq2Set(set2Seq(s)) == s 
{  if s != {} {
    var y := Pick(s);
    assert seq2Set([y] + set2Seq(s - {y})) == seq2Set([y]) + seq2Set(set2Seq(s - {y}));
  }
}

function sort(xs:seq<int>):seq<int>
ensures seq2Set(xs)==seq2Set(sort(xs)) && isSortedSeq(sort(xs))
ensures |xs|==|sort(xs)|

function set2SortedSeq(s:set<int>):seq<int>
ensures set2SortedSeq(s)==sort(set2Seq(s))
{sort(set2Seq(s))
}

lemma sortedSeq(s:set<int>)
ensures isSortedSeq(set2SortedSeq(s)) && seq2Set(set2SortedSeq(s))==s
ensures |set2SortedSeq(s)|==|s|
{idem(s);sizesSet2Seq(s);}
