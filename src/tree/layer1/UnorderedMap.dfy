include "../../../src/tree/KeyValue.dfy"
include "../../../src/ADT.dfy"

module {:options "-functionSyntax:4"} UnorderedMapSpec {
  import opened KeyValue
  import opened ADT

  trait {:termination false} UnorderedMapIterator {
    function Parent(): UnorderedMap
      reads this

    ghost predicate Valid()
      reads this, Parent(), Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

    ghost function Traversed(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures Traversed() <= (Parent().Model().Keys)
      ensures 0 <= |Traversed()| <= |Parent().Model().Keys|

    ghost function Peek?():(K,V)
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()

      ensures Peek?() in Parent().Model().Items
      ensures key(Peek?()) in Parent().Model() - Traversed()

    ghost predicate HasPeek?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures HasPeek?()  ==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
      //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
      ensures !HasPeek?() ==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|

    method HasPeek() returns (b:bool)
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)
      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)

      ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())
      ensures b == HasPeek?()

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    method Peek() returns (p:(K,V))
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)
      ensures Traversed() == old(Traversed()) && Peek?()==old(Peek?())
      ensures |Traversed()| == old(|Traversed()|)

      ensures p == Peek?()
      ensures HasPeek?() && Peek?()==old(Peek?()) // no debería ser necesario pero lo es

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    method Next()
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Traversed() == {key(old(Peek?()))} + old(Traversed())
      ensures |Traversed()| == 1 + old(|Traversed()|)

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))


    method Copy() returns (it: UnorderedMapIterator)
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)
      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == |old(Traversed())|
      ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())

      ensures fresh(it)
      ensures it.Valid()
      ensures Parent() == it.Parent()
      ensures Traversed() == it.Traversed()
      ensures |Traversed()| == |it.Traversed()|
      ensures HasPeek?() ==> it.HasPeek?() && Peek?()==it.Peek?()

      ensures Parent().Iterators() >= {it} + old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))
  }

  trait {:termination false} UnorderedMap extends ADT<map<K,V>> { //<K (==),V> extends ADT<map<K,V>> {
    ghost predicate Empty?()
      reads this, Repr()
      requires Valid()
    {
      Model() == map[]
    }

    method Empty() returns (b: bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures b == Empty?()

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    method Size() returns (s: nat)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures s == |Model()|

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    ghost function Iterators(): set<UnorderedMapIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

    method First() returns (it: UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Traversed() == {}

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    method Contains(k:K) returns (b:bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures b == (k in Model())

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    method At(k:K) returns (v:V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires k in Model()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures v == Model()[k]

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    method Add(k: K,v: V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k:=v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|)
              else |Model()| == 1 + old(|Model()|)

      ensures Iterators() >= old(Iterators())

    method Remove(k: K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) - {k}
      ensures if (k in old(Model())) then |Model()| == old(|Model()|) - 1
              else |Model()| == old(|Model()|)

      ensures Iterators() >= old(Iterators())

    method Find(k:K) returns (newt:UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model()==old(Model())
      ensures |Model()| == old(|Model()|)

      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent()==this
      ensures k in old(Model()) ==> newt.HasPeek?() && key(newt.Peek?()) == k
      ensures k !in old(Model()) ==> newt.Traversed() == Model().Keys && |newt.Traversed()| == |Model().Keys|

      ensures Iterators() >= {newt}+old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    method Insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt:UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k:=v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|) else |Model()| == 1 + old(|Model()|)

      requires mid.Valid()
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent() == this
      ensures newt.HasPeek?() && newt.Peek?() == (k,v)

      ensures Iterators() >= {newt}+old(Iterators())

    //points either to the inserted element or to the already existing one

    method Erase(mid:UnorderedMapIterator) returns (next: UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires mid.Valid()
      requires mid.Parent() == this
      requires mid.HasPeek?()
      requires mid in Iterators()
      ensures Valid()
      ensures Model()== old(Model())- {key(old(mid.Peek?()))} //map k | k in old(Model()) && k != key(old(mid.Peek?()))::old(Model())[k]
      ensures |Model()|==|old(Model())|-1

      ensures fresh(next)
      ensures next.Valid() && next.Parent() == this
      ensures next.Traversed() == old(mid.Traversed())
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures Iterators() >= {next}+old(Iterators())
  }


  method {:verify true} main(s:UnorderedMap)
    modifies s, s.Repr()
    requires allocated(s.Repr())
    ensures fresh(s.Repr()-old(s.Repr()))
    ensures allocated(s.Repr())

    requires s.Valid() && s.Empty?()
  {
    assert s.Model()==map[];
    s.Add(1,2);
    var x:= s.At(1);
    assert s.Model()==map[1:=2];
    s.Add(1,3);
    x:=s.At(1);
    assert x==3;

    var z:=s.Contains(1);
    assert z;
    z:=s.Contains(7);
    assert !z;
    s.Add(2,3); s.Add(3,4); s.Add(4,5);

    var it:=s.First();
    var cont:=0;
    var b := it.HasPeek();
    while (b)
      decreases |s.Model()|
      //decreases |s.Model() - it.Model().0|
      //decreases s.Model() - it.Traversed()
      invariant s.Valid()
      invariant it.Valid() && it in s.Iterators() && it.Parent() == s
      invariant allocated(s.Repr())
      invariant fresh(s.Repr()-old(s.Repr()))
      invariant allocated(s.Repr())
      invariant b == it.HasPeek?()    {
      it := s.Erase(it);
      b := it.HasPeek();
    }
    assert it.Traversed()==s.Model().Keys;

    s.Remove(1);
    z:=s.Contains(1);
    assert !z;
  }
}
