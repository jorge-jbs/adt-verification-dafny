include "../src/Utils.dfy"
include "../src/linear/layer1/Stack.dfy"
include "../src/linear/layer1/Queue.dfy"

lemma Allocated(s: set<object>)
  ensures forall x | x in s :: allocated(x)
{}

lemma TransitiveLemma(v: array<int>, i: int)
  requires forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])
  requires 0 <= i <= v.Length
  ensures forall j, k | 0 <= j < k < i :: abs(v[j]) <= abs(v[k])
{
  if i == 0 {
  } else if i == 1 {
  } else if i == 2 {
  } else {
    TransitiveLemma(v, i-1);
    assert abs(v[i-2]) <= abs(v[i-1]);
  }
}

method Split(v: array<int>, neg: Stack<int>, pos: Queue<int>)
  modifies pos, pos.Repr(), neg, neg.Repr()
  requires allocated(neg.Repr())
  requires allocated(pos.Repr())
  ensures fresh(neg.Repr()-old(neg.Repr()))
  ensures allocated(neg.Repr())
  ensures fresh(pos.Repr()-old(pos.Repr()))
  ensures allocated(pos.Repr())

  requires v !in {neg} + neg.Repr() && v !in {pos} + pos.Repr()
  ensures v !in {neg} + neg.Repr() && v !in {pos} + pos.Repr()
  // ensures v[..] == old(v[..])

  requires {pos} + pos.Repr() !! {neg} + neg.Repr()
  requires neg.Valid()
  requires pos.Valid()
  requires neg.Empty?()
  requires pos.Empty?()

  requires forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])

  ensures {pos} + pos.Repr() !! {neg} + neg.Repr()
  ensures pos.Valid()
  ensures neg.Valid()

  ensures forall x | x in neg.Model() :: x < 0
  ensures forall i | 0 <= i < |neg.Model()| - 1 :: abs(neg.Model()[i]) >= abs(neg.Model()[i+1])
  ensures forall x | x in pos.Model() :: x >= 0
  ensures forall i | 0 <= i < |pos.Model()| - 1 :: abs(pos.Model()[i]) <= abs(pos.Model()[i+1])

  ensures Seq.MElems(neg.Model()) + Seq.MElems(pos.Model()) == Seq.MElems(v[..])
{
  var i := 0;
  while i < v.Length
    invariant fresh(neg.Repr()-old(neg.Repr()))
    invariant allocated(neg.Repr())
    invariant fresh(pos.Repr()-old(pos.Repr()))
    invariant allocated(pos.Repr())

    invariant i <= v.Length

    invariant forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])

    invariant {pos} + pos.Repr() !! {neg} + neg.Repr()
    invariant neg.Valid()
    invariant pos.Valid()
    invariant v !in {pos} + pos.Repr()
    invariant v !in {neg} + neg.Repr()

    invariant forall x | x in neg.Model() :: x < 0
    invariant forall i | 0 <= i < |neg.Model()| - 1 :: abs(neg.Model()[i]) >= abs(neg.Model()[i+1])
    invariant forall x | x in pos.Model() :: x >= 0
    invariant forall i | 0 <= i < |pos.Model()| - 1 :: abs(pos.Model()[i]) <= abs(pos.Model()[i+1])

    invariant Seq.MElems(neg.Model()) + Seq.MElems(pos.Model())
      == Seq.MElems(v[..i])
  {
    TransitiveLemma(v, i+1);
    assert forall j | 0 <= j < i :: abs(v[j]) <= abs(v[i]);
    if v[i] < 0 {
      if |neg.Model()| > 0 {
        assert neg.Model()[0] in Seq.MElems(neg.Model());
        assert neg.Model()[0] in Seq.MElems(neg.Model()) + Seq.MElems(pos.Model());
        assert neg.Model()[0] in Seq.MElems(v[..i]);
        assert neg.Model()[0] in v[..i];
        assert abs(v[i]) >= abs(neg.Model()[0]);
      }
      neg.Push(v[i]);
    } else {
      if |pos.Model()| > 0 {
        assert pos.Model()[|pos.Model()|-1] in Seq.MElems(pos.Model());
        assert pos.Model()[|pos.Model()|-1] in Seq.MElems(neg.Model()) + Seq.MElems(pos.Model());
        assert pos.Model()[|pos.Model()|-1] in Seq.MElems(v[..i]);
        assert pos.Model()[|pos.Model()|-1] in v[..i];
        assert abs(pos.Model()[|pos.Model()|-1]) <= abs(v[i]);
      }
      pos.Enqueue(v[i]);
    }
    i := i + 1;
  }
  assert v[..i] == v[..];
}

method FillFromStack(r: array<int>, i: nat, st: Stack<int>) returns (l: nat)
  modifies r, st, st.Repr()
  requires allocated(st.Repr())
  ensures fresh(st.Repr()-old(st.Repr()))
  ensures allocated(st.Repr())

  requires st.Valid()
  // we have to say that r is not equal to st even though they are not of the same type:
  requires {r} !! {st} + st.Repr()
  requires i + |st.Model()| <= r.Length
  ensures st.Valid()
  ensures st.Empty?()
  ensures forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)
  ensures forall x | x in st.Repr() :: allocated(x)
  ensures r[..i] == old(r[..i])
  ensures r[i..i+old(|st.Model()|)] == old(st.Model())
  ensures r[i+old(|st.Model()|)..] == old(r[i+|st.Model()|..])
  // ensures Seq.MElems(r[i..i+old(|st.Model()|)]) == Seq.MElems(old(st.Model()))
  ensures l == i + old(|st.Model()|)
{
  l := 0;
  var b := st.Empty();

  while !b
    decreases |st.Model()|
    invariant fresh(st.Repr()-old(st.Repr()))
    invariant allocated(st.Repr())

    invariant st.Valid()
    invariant {r} !! {st} + st.Repr()

    invariant 0 <= l <= old(|st.Model()|)
    invariant l == old(|st.Model()|) - |st.Model()|

    invariant st.Model() == old(st.Model()[l..])
    invariant r[..i] == old(r[..i])
    invariant r[i..i+l] == old(st.Model()[..l])
    invariant r[i+old(|st.Model()|)..] == old(r[i+|st.Model()|..])
    invariant b == st.Empty?()
  {
    r[i+l] := st.Pop();
    b := st.Empty();
    l := l + 1;
  }
  l := l + i;
}

method FillFromQueue(r: array<int>, i: nat, q: Queue<int>) returns (l: nat)
  modifies r, q, q.Repr()
  requires allocated(q.Repr())
  ensures fresh(q.Repr()-old(q.Repr()))
  ensures allocated(q.Repr())

  requires q.Valid()
  // we have to say that r is not equal to q even though they are not of the same type:
  requires {r} !! {q} + q.Repr()
  requires i + |q.Model()| <= r.Length
  ensures q.Valid()
  ensures q.Empty?()
  ensures forall x | x in q.Repr() - old(q.Repr()) :: fresh(x)
  ensures forall x | x in q.Repr() :: allocated(x)
  ensures r[..i] == old(r[..i])
  ensures r[i..i+old(|q.Model()|)] == old(q.Model())
  ensures r[i+old(|q.Model()|)..] == old(r[i+|q.Model()|..])
  // ensures Seq.MElems(r[i..i+old(|q.Model()|)]) == Seq.MElems(old(q.Model()))
  ensures l == i + old(|q.Model()|)
{
  l := 0;
  var b := q.Empty();

  while !b
    decreases |q.Model()|
    invariant fresh(q.Repr()-old(q.Repr()))
    invariant allocated(q.Repr())

    invariant q.Valid()
    invariant {r} !! {q} + q.Repr()

    invariant 0 <= l <= old(|q.Model()|)
    invariant l == old(|q.Model()|) - |q.Model()|

    invariant q.Model() == old(q.Model()[l..])
    invariant r[..i] == old(r[..i])
    invariant r[i..i+l] == old(q.Model()[..l])
    invariant r[i+old(|q.Model()|)..] == old(r[i+|q.Model()|..])
    invariant b == q.Empty?()
  {
    r[i+l] := q.Dequeue();
    b := q.Empty();
    l := l + 1;
  }
  l := l + i;
}

lemma LastLemma(neg: seq<int>, pos: seq<int>, s: seq<int>)
  requires forall x | x in neg :: x < 0
  requires forall i | 0 <= i < |neg|-1 :: abs(neg[i]) >= abs(neg[i+1])

  requires forall x | x in pos :: x >= 0
  requires forall i | 0 <= i < |pos|-1 :: abs(pos[i]) <= abs(pos[i+1])

  requires s == neg + pos

  ensures forall i | 0 <= i < |s|-1 :: s[i] <= s[i+1]
{
  assert forall x | x in neg :: x < 0 && abs(x) == -x;
  assert forall i | 0 <= i < |neg|-1 :: neg[i] <= neg[i+1];
  assert forall x | x in pos :: x >= 0 && abs(x) == x;
  assert forall i | 0 <= i < |pos|-1 :: pos[i] <= pos[i+1];
  ghost var i := |neg|-1;
  if 0 <= i < |s|-1 {
    assert s[i] in neg && s[i] < 0;
    assert s[i+1] in pos && s[i+1] >= 0;
    assert s[i] <= s[i+1];
  } else {
    assert s == neg || s == pos;
  }
}

method Reorder(neg: Stack<int>, pos: Queue<int>, v: array<int>)
  modifies v
  modifies neg, neg.Repr()
  modifies pos, pos.Repr()
  requires allocated(neg.Repr())
  requires allocated(pos.Repr())
  ensures fresh(neg.Repr()-old(neg.Repr()))
  ensures allocated(neg.Repr())
  ensures fresh(pos.Repr()-old(pos.Repr()))
  ensures allocated(pos.Repr())

  requires {v} !! {neg} + neg.Repr()
  requires {v} !! {pos} + pos.Repr()
  requires {pos} + pos.Repr() !! {neg} + neg.Repr()
  requires forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])
  requires neg.Valid() && neg.Empty?()
  requires pos.Valid() && pos.Empty?()

  ensures neg.Valid()
  ensures pos.Valid()
  
  ensures {v} !! {neg} + neg.Repr()
  ensures {v} !! {pos} + pos.Repr()
  ensures {pos} + pos.Repr() !! {neg} + neg.Repr()

  ensures Array.melems(v) == old(Array.melems(v))
  ensures forall i | 0 <= i < v.Length - 1 :: v[i] <= v[i+1]
{
  Split(v, neg, pos);
  ghost var negmodel := neg.Model();
  ghost var posmodel := pos.Model();
  calc == {
    |negmodel| + |posmodel|;
    |Seq.MElems(negmodel)| + |Seq.MElems(posmodel)|;
    |Seq.MElems(negmodel) + Seq.MElems(posmodel)|;
    |Seq.MElems(v[..])|;
    |v[..]|;
    v.Length;
  }
  var i := 0;
  i := FillFromStack(v, i, neg);
  i := FillFromQueue(v, i, pos);
  LastLemma(negmodel, posmodel, v[..]);
}
