include "../Collections/KeyValue.dfy"

module OrderedMultisetUtils {
  import opened KeyValue
  
  ghost function Pick<A>(s: multiset<A>): A
    requires s != multiset{}
  {
    var x :| x in s; x
  }

  lemma sizeOfSet<A>(s:multiset<A>,x:A)
    requires x in s
    ensures (s-multiset{x})+multiset{x}==s
  {}

  lemma sizes<A>(s1:multiset<A>,s2:multiset<A>)
    requires s1==s2
    ensures |s1|==|s2|
  {}

  lemma lessSize<A>(s:multiset<A>,x:A)
    requires x in s
    ensures |s-multiset{x}| == |s| - 1
    {}

  lemma moreSize<A>(s:multiset<A>,x:A)
    ensures |s+multiset{x}| == |s| + 1
    {}
  ghost function {:induction s} minimum(s:multiset<K>):K
    requires s != multiset{}
    //ensures forall x | x in s :: minimum(s)<=x
  {
    var x:=Pick(s);
    if (s-multiset{x}==multiset{}) then x
    else if (x < minimum(s-multiset{x})) then x
    else minimum(s-multiset{x})
  }

  lemma lmin(s:multiset<K>,x:K)
    requires s != multiset{} && x in s
    ensures x >= minimum(s)
  {
    var y:=Pick(s);
    if (s-multiset{y} == multiset{}){assert s==multiset{y};assert x==y;}
    else if (minimum(s-multiset{y})==minimum(s)){}
    else{}
  }

  lemma lminimum(s:multiset<K>)
    requires s != multiset{}
    ensures minimum(s) in s && forall x | x in s :: minimum(s) <= x
  {forall x | x in s
     ensures minimum(s) <= x {lmin(s,x);}}


  //An element smaller than the rest of elements is the minimum
  lemma  lminimumrev(s:multiset<K>,x:K)
    requires x in s && forall z | z in s :: x <= z
    ensures x == minimum(s)
  {
    lminimum(s);
    assert minimum(s) in s;
    if (x==minimum(s)){}
    else {assert x < minimum(s);
          assert false;}//contradiction
  }

  ghost function {:induction s} maximum(s:multiset<K>):K
    requires s != multiset{}
    //ensures forall x | x in s :: maximum(s)>=x
  {
    var x:=Pick(s);
    if (s-multiset{x}==multiset{}) then x
    else if (x > maximum(s-multiset{x})) then x
    else maximum(s-multiset{x})

  }

  lemma lmax(s:multiset<K>,x:K)
    requires s != multiset{} && x in s
    ensures x<=maximum(s)
  {
    var y:=Pick(s);
    if (s-multiset{y} == multiset{}){assert s==multiset{y};assert x==y;}
    else if (maximum(s-multiset{y})==maximum(s)){}
    else{}
  }

  lemma lmaximum(s:multiset<K>)
    requires s !=  multiset{}
    ensures maximum(s) in s && forall x | x in s :: maximum(s) >= x
    ensures forall x | x in s && s-multiset{x}!=multiset{} && x > maximum(s-multiset{x}) :: x==maximum(s)
    ensures forall x | x in s && s-multiset{x}!=multiset{} && x <= maximum(s-multiset{x}) :: maximum(s)==maximum(s-multiset{x})
  {forall x | x in s
     ensures maximum(s) >= x {lmax(s,x);}}

  lemma lmaximumOne(s:multiset<K>,x:K)
    requires s!=multiset{} && x in s && s-multiset{x}!=multiset{}
    ensures if (x <= maximum(s-multiset{x})) then maximum(s) == maximum(s-multiset{x}) else maximum(s)==x
  {
    lmaximum(s);
  }

  //Any element of the set bigger tahn the rest is the maximum
  lemma lmaximumrev(s:multiset<K>,x:K)
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
  lemma max2Elems(s:multiset<K>)
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

  lemma lMaxMinOne(s:multiset<K>)
    requires s != multiset{} && |s|==1
    ensures maximum(s)==minimum(s)
  { var x:=Pick(s);
    assert s == multiset{x};
  }

  ghost function msmaller(s:multiset<K>,x:K):multiset<K>
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

  lemma smallerMin(s:multiset<K>)
    requires s != multiset{}
    ensures msmaller(s,minimum(s))==multiset{} && |msmaller(s,minimum(s))|==0
  {}

  lemma smallerMax(s:multiset<K>)
    requires s != multiset{}
    ensures msmaller(s,maximum(s))==s[maximum(s):=0] && |msmaller(s,maximum(s))|== |s|-s[maximum(s)]
  {}

  lemma smallerElem(s:multiset<K>,x:K)
    requires s!=multiset{} && x in s && x != minimum(s)
    ensures msmaller(s-multiset{minimum(s)},x) == msmaller(s,x)-multiset{minimum(s)}
  { lminimum(s);
    assert minimum(s) in msmaller(s,x);

    assert msmaller(s-multiset{minimum(s)},x) <= msmaller(s,x)-multiset{minimum(s)};

    forall y | y in msmaller(s,x)-multiset{minimum(s)}
    ensures y in msmaller(s-multiset{minimum(s)},x){
           assert y in msmaller(s,x);
           assert y < x;
           assert y in s-multiset{minimum(s)};
           assert y in msmaller(s-multiset{minimum(s)},x);
    }
    assert msmaller(s-multiset{minimum(s)},x) == msmaller(s,x) - multiset{minimum(s)};
    }


  lemma smallerElemSize(s:multiset<K>,x:K)
    requires s != multiset{} && x in s && x != minimum(s)
    ensures |msmaller(s-multiset{minimum(s)},x)| == |msmaller(s,x)| - 1
    {
    calc
    { |msmaller(s-multiset{minimum(s)},x)|;
         {smallerElem(s,x);
          assert msmaller(s-multiset{minimum(s)},x) == msmaller(s,x) - multiset{minimum(s)};
          sizes(msmaller(s-multiset{minimum(s)},x),msmaller(s,x)-multiset{minimum(s)});}
      |msmaller(s,x) - multiset{minimum(s)}|;
         {
           lminimum(s);
           assert minimum(s) in msmaller(s,x);          
           lessSize(msmaller(s,x),minimum(s));
          }
      |msmaller(s,x)| - 1;
    }
    }

  ghost function elemth(s:multiset<K>,k:int):K
    requires 0<=k<|s|
    ensures elemth(s,k) in s
  {
    var minim:=minimum(s);lminimum(s);
    if (k==0) then minim
    else elemth(s-multiset{minim},k-1)
  }


  lemma smallerElemth(s:multiset<K>,k:int)
  requires 1 <= k < |s|
  requires minimum(s) != elemth(s-multiset{minimum(s)},k-1)
  ensures msmaller(s,elemth(s,k)) -  multiset{minimum(s)}== msmaller(s-multiset{minimum(s)},elemth(s-multiset{minimum(s)},k-1)) 
  {
   assert elemth(s,k) == elemth(s-multiset{minimum(s)},k-1);
   assert elemth(s,k) in s;
  calc{
     msmaller(s,elemth(s,k)) - multiset{minimum(s)};
     msmaller(s,elemth(s-multiset{minimum(s)},k-1)) - multiset{minimum(s)};
      { smallerElem(s,elemth(s-multiset{minimum(s)},k-1)); }
     msmaller(s-multiset{minimum(s)},elemth(s-multiset{minimum(s)},k-1));
  }
  }
  
  
  lemma {:induction s,k} lelemth(s:multiset<K>,k:int)
    requires 0<=k<|s|
    ensures elemth(s,k) in s && |msmaller(s,elemth(s,k))| <= k <= |msmaller(s,elemth(s,k))|+s[elemth(s,k)]-1
  {
    lminimum(s);
    if (k==0) { }
    else if (minimum(s)== elemth(s-multiset{minimum(s)},k-1)){}
    else {
      lelemth(s-multiset{minimum(s)},k-1);
  
      smallerElemth(s,k);
      sizes(msmaller(s-multiset{minimum(s)},elemth(s-multiset{minimum(s)},k-1))+multiset{minimum(s)},msmaller(s,elemth(s,k)));
      assert |msmaller(s,elemth(s,k))| == |msmaller(s-multiset{minimum(s)},elemth(s-multiset{minimum(s)},k-1))+multiset{minimum(s)}|;
      assert  |msmaller(s,elemth(s,k))|== |msmaller(s-multiset{minimum(s)},elemth(s-multiset{minimum(s)},k-1))| + 1  <= k;
      calc{  
        |msmaller(s,elemth(s,k))| + s[elemth(s,k)] - 1 ;
        |msmaller(s-multiset{minimum(s)},elemth(s-multiset{minimum(s)},k-1))| + 1 + s[elemth(s,k)] - 1;
        { assert elemth(s-multiset{minimum(s)},k-1) == elemth(s,k); }
        |msmaller(s-multiset{minimum(s)},elemth(s-multiset{minimum(s)},k-1))| + s[elemth(s-multiset{minimum(s)},k-1)];
        >= k;
      }
    }
  }

  lemma  {:induction s} lelemthrev(s:multiset<K>,x:K,k:int)
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
      var minim := minimum(s);
      if (minim==x){smallerMin(s);}
      else{
        smallerElemSize(s,x);
        assert |msmaller(s-multiset{minim},x)|==k-1;
        lelemthrev(s-multiset{minim},x,k-1);
      }
    }
  }

  lemma firstAndLast(s:multiset<K>)
    requires s != multiset{}
    ensures minimum(s) == elemth(s,0)
    ensures maximum(s) == elemth(s,|s|-1)
  {
    if |s| == 1 {
      lMaxMinOne(s);
      assert |s|-1==0;
      assert maximum(s)==minimum(s)==elemth(s,0);
    } else {
      var minim:=minimum(s);
      lminimum(s);
      assert minim in s;

      calc == {
        elemth(s,|s|-1);
        { assert |s|-1 != 0; }
        elemth(s-multiset{minim},|s|-2);
        {
          assert s-multiset{minim}<s;
          sizeOfSet(s,minim);
          assert |s-multiset{minim}|==|s|-1;
          firstAndLast(s-multiset{minim});
        }
        maximum(s-multiset{minim});
        {
          assert |s|>=2; assert minim==minimum(s);
          max2Elems(s);
          assert maximum(s-multiset{minim})==maximum(s);
        }
        maximum(s);
      }
    }
  }

  ghost function isSortedSeq(xs:seq<K>):bool
  {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
  }

  ghost function seq2Multiset(xs:seq<K>):multiset<K>
  {multiset(xs)}

  ghost function multiset2Seq(s:multiset<K>):seq<K>
    decreases s
  {
    if s == multiset{} then []
    else
      var y := Pick(s);
      [y] + multiset2Seq(s - multiset{y})

  }

  lemma sizesSet2Seq(s:multiset<K>)
    ensures |multiset2Seq(s)|==|s|
  {}

  lemma  sizesSeq2Multiset(xs:seq<K>)
    ensures |seq2Multiset(xs)|==|xs|
  {if (xs==[]) {}
   else {sizesSeq2Multiset(xs[1..]);
         assert xs==[xs[0]]+xs[1..];
         assert seq2Multiset(xs)==multiset{xs[0]}+seq2Multiset(xs[1..]);
         assert |seq2Multiset(xs)|==1+|seq2Multiset(xs[1..])|;}
  }

  lemma idem(s:multiset<K>)
    ensures seq2Multiset(multiset2Seq(s)) == s
  {  if s != multiset{} {
       var y := Pick(s);
       assert seq2Multiset([y] + multiset2Seq(s - multiset{y})) == seq2Multiset([y]) + seq2Multiset(multiset2Seq(s - multiset{y}));
     }
  }

  ghost function insert(x: K, xs: seq<K>): seq<K>
    requires isSortedSeq(xs)
    ensures multiset(insert(x, xs)) == multiset{x} + multiset(xs)
    ensures isSortedSeq(insert(x, xs))
    ensures |insert(x, xs)| == 1 + |xs|
  {
    if xs == [] then
      [x]
    else if x <= xs[0] then
      [x] + xs
    else
      calc == {
        multiset([xs[0]] + insert(x, xs[1..]));
        multiset([xs[0]]) + multiset(insert(x, xs[1..]));
        multiset([xs[0]]) + multiset{x} + multiset(xs[1..]);
        multiset{x} + multiset([xs[0]]) + multiset(xs[1..]);
        multiset{x} + multiset([xs[0]] + xs[1..]);
        { assert [xs[0]] + xs[1..] == xs; }
        multiset{x} + multiset(xs);
      }
      assert isSortedSeq(xs);
      assert isSortedSeq(xs[1..]);
      assert isSortedSeq(insert(x, xs[1..]));
      assert xs[0] <= x;
      assert forall j | 0 <= j < |xs|-1 :: xs[0] <= xs[1..][j];
      assert forall j | 0 <= j < |xs| ::
          insert(x, xs[1..])[j] in multiset{x} + multiset(xs[1..]);
      [xs[0]] + insert(x, xs[1..])
  }

  ghost function {:opaque} sort(xs: seq<K>):seq<K>
    ensures multiset(xs) == multiset(sort(xs))
    ensures isSortedSeq(sort(xs))
    ensures |xs| == |sort(xs)|
  {
    if xs == [] then
      []
    else
      calc == {
        multiset(insert(xs[0], sort(xs[1..])));
        multiset{xs[0]} + multiset(sort(xs[1..]));
        multiset{xs[0]} + multiset(xs[1..]);
        multiset([xs[0]] + xs[1..]);
        { assert [xs[0]] + xs[1..] == xs; }
        multiset(xs);
      }
      insert(xs[0], sort(xs[1..]))
  }

  ghost function multiset2SortedSeq(s:multiset<K>):seq<K>
    ensures multiset2SortedSeq(s)==sort(multiset2Seq(s))
  {
    sort(multiset2Seq(s))
  }

  lemma sortedSeq(s:multiset<K>)
    ensures isSortedSeq(multiset2SortedSeq(s)) && seq2Multiset(multiset2SortedSeq(s))==s
    ensures |multiset2SortedSeq(s)|==|s|
  {
    idem(s);sizesSet2Seq(s);
  }
}
