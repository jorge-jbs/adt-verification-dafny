include "../../src/Collections/KeyValue.dfy"
include "../../src/Collections/Set.dfy"
include "../../src/UnorderedSet/UnorderedSetSpec2.dfy"
include "../../src/OrderedSet/OrderedSetSpec2.dfy"
include "../../src/OrderedMap/OrderedMapSpec2.dfy"
include "../../src/TreeMap/TreeMapSpec2.dfy"
include "../../src/TreeMap/TreeMapImpl2.dfy"
include "../../src/TreeSet/TreeSetSpec2.dfy"
include "../../src/Collections/SetInt.dfy"
include "../../src/DataStructures/ThreadedLinkedTree2.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Model/Insert.dfy"

module TreeSetImpl {
  import opened KeyValue
  import opened UnorderedSetSpec2
  import opened OrderedSetSpec2
  import opened OrderedMapSpec2
  import opened TreeSetSpec
  import opened TreeMapSpec
  import opened TreeMapImpl
  import opened SetInt
  import opened Set
  import opened ThreadedLinkedTree
  import opened ModelB = ThreadedLinkedTree.Model.Base
  import opened ModelI = ThreadedLinkedTree.Model.Insert
  import opened ModelR = ThreadedLinkedTree.Model.RemoveRoot
  import opened ModelIt = ThreadedLinkedTree.Model.Iterator
  import opened ThreadedLinkedTree.Impl.TTNode
  import opened ThreadedLinkedTree.Impl.TTree

  class TreeSetIteratorImpl extends OrderedSetIterator {
    const iter: OrderedMapIterator
    ghost const parent: TreeSetImpl

    ghost function Parent(): UnorderedSet
      ensures Parent() is OrderedSet
    {
      parent
    }

    ghost predicate Valid()
      reads Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()
    {
      && parent.Valid()
      && this in parent.iterators
      && assert parent == Parent();
      && assert Parent().Valid();
      && assert parent.iterators == parent.Iterators();
      && assert parent.Iterators() == Parent().Iterators();
      && iter.Parent() == parent.treemap
      && iter.Valid()
    }

    ghost predicate HasPeek?()
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
    {
      iter.HasPeek?()
    }

    ghost function Peek?(): K
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures PeekSpec(Peek?())
      ensures PeekOrderSpec(Peek?())
    {
      assert
        && PeekSpec(iter.Peek?().0)
        && PeekOrderSpec(iter.Peek?().0)
      by {
        reveal PeekSpec(), PeekOrderSpec();
        reveal iter.PeekSpec(), iter.PeekOrderSpec();
        assert iter.Peek?().0 in iter.Parent().Model();
        assert iter.Peek?().0 in iter.Parent().Model().Keys;
        assert iter.Peek?().0 in parent.Model();
        assert iter.Peek?().0 in Parent().Model();
        assert iter.Peek?().0 !in Before();
      }
      iter.Peek?().0
    }

    ghost function Before(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures BeforeSpec(Before())
    {
      assert
        && BeforeSpec(iter.Before())
      by {
        reveal BeforeSpec();
        reveal iter.BeforeSpec();
        assert iter.Before() < iter.Parent().Model().Keys;
        assert iter.Before() < parent.Model();
        assert iter.Before() < Parent().Model();
        assert |iter.Before()| < |Parent().Model()|;
      }
      iter.Before()
    }

    opaque static twostate predicate TreeSetIteratorImplCtrModel(
      new self: TreeSetIteratorImpl,
      parent: TreeSetImpl,
      iter: OrderedMapIterator
    )
      reads parent.Repr()
      requires iter.Parent() == parent.treemap
      requires old(parent.Valid())
      requires old(iter.Valid())
      requires self.Valid()
      requires iter.Valid()
      requires parent.Valid()
      requires self.parent == parent
    {
      && parent.Model() == old(parent.Model())
      && |parent.Model()| == |old(parent.Model())|
      && self.HasPeek?() == iter.HasPeek?() == old(iter.HasPeek?())
      && (iter.HasPeek?() ==>
        && iter.Peek?() == old(iter.Peek?())
        && iter.Before() == old(iter.Before())
        && |iter.Before()| == |old(iter.Before())|
      )
      && (self.HasPeek?() ==>
        && self.Peek?() == old(iter.Peek?().0)
        && self.Before() == old(iter.Before())
        && |self.Before()| == |old(iter.Before())|
      )
    }

    constructor (ghost parent: TreeSetImpl, iter: OrderedMapIterator)
      modifies parent`iterators

      requires allocated(parent.Repr())
      ensures allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))

      requires parent.Valid()
      requires iter.Valid()
      requires iter.Parent() == parent.treemap
      requires forall it <- parent.iterators :: it.iter != iter
      ensures parent.Valid()
      ensures Valid()
      ensures this.parent == parent
      ensures TreeSetIteratorImplCtrModel(this, parent, iter)
      ensures parent.iterators == {this} + old(parent.iterators)
      ensures parent.SameIterators()
    {
      this.iter := iter;
      this.parent := parent;
      new;
      parent.iterators := parent.iterators + {this};
      assert Valid();
      assert parent.Valid();
      assert TreeSetIteratorImplCtrModel(this, parent, iter) by{
        reveal TreeSetIteratorImpl.TreeSetIteratorImplCtrModel();
      }
      assert parent.SameIterators() by {
        reveal parent.SameIterators(), parent.SameIteratorModel();
      }
    }

    method HasPeek() returns (b: bool)
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      //ensures Parent() == old(Parent())
      ensures b == HasPeek?()
      ensures Parent().Iterators() >= old(Parent().Iterators())

      ensures HasPeekModel()
      ensures Parent().SameIterators()
    {
      b := iter.HasPeek();
      assert Valid();
      assert Parent().Valid();
      assert b == HasPeek?();
      assert Parent().Iterators() >= old(Parent().Iterators());
      assert HasPeekModel() by {
        reveal HasPeekModel();
        reveal iter.HasPeekModel();
        assert parent.Model() == old(parent.Model());
        assert Parent().Model() == old(Parent().Model());
        assert |Parent().Model()| == old(|Parent().Model()|);
        assert HasPeek?() == old(HasPeek?());
        if old(HasPeek?()) {
          assert Peek?() == old(Peek?());
          assert Before() == old(Before());
          assert |Before()| == old(|Before()|);
        }
      }
      assert Parent().SameIterators() by {
        reveal parent.SameIterators(), parent.SameIteratorModel();
        reveal iter.Parent().SameIterators(), iter.Parent().SameIteratorModel();
      }
    }

    method Peek() returns (k: K)
      modifies parent.Repr()
      requires allocated(parent)
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())

      requires Valid()
      requires parent.Valid()
      requires HasPeek?()
      ensures Valid()
      ensures parent.Valid()
      //ensures parent == old(parent)
      ensures HasPeek?()
      ensures parent.Iterators() >= old(parent.Iterators())
      ensures PeekModel(k)
      ensures parent.SameIterators()
    {
      var p := iter.Peek();
      k := p.0;
      assert Valid();
      assert Parent().Valid();
      assert Parent().Iterators() >= old(Parent().Iterators());
      assert PeekModel(k) by {
        reveal PeekModel();
        reveal iter.PeekModel();
        assert parent.Model() == old(parent.Model());
        assert Parent().Model() == old(Parent().Model());
        assert |Parent().Model()| == old(|Parent().Model()|);
        assert Before() == old(Before());
        assert |Before()| == old(|Before()|);
        assert k == Peek?() == old(Peek?());
      }
      assert parent.SameIterators() by {
        reveal parent.SameIterators(), parent.SameIteratorModel();
        reveal iter.Parent().SameIterators(), iter.Parent().SameIteratorModel();
      }
    }

    method Next()
      modifies parent.Repr()
      requires allocated(parent)
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())

      requires Valid()
      requires parent.Valid()
      requires HasPeek?()
      ensures Valid()
      ensures parent.Valid()
      ensures parent.Iterators() >= old(parent.Iterators())
      ensures NextModel()
      ensures NextIterators()
    {
      iter.Next();
      assert Valid();
      assert Parent().Valid();
      assert Parent().Iterators() >= old(Parent().Iterators());
      assert NextModel() by {
        reveal NextModel();
        reveal iter.NextModel();
        assert parent.Model() == old(parent.Model());
        assert |parent.Model()| == old(|parent.Model()|);
        assert Traversed() == {old(Peek?())} + old(Before());
        assert |Traversed()| == 1 + old(|Before()|);
      }
      assert NextIterators() by {
        reveal NextIterators(), parent.SameIteratorModel();
        reveal iter.NextIterators(), iter.Parent().SameIteratorModel();
      }
    }

    method Prev()
      modifies parent.Repr()
      requires allocated(parent)
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())

      requires Valid()
      requires parent.Valid()
      requires HasPeek?()
      ensures Valid()
      ensures parent.Valid()
      ensures parent.Iterators() >= old(parent.Iterators())
      ensures PrevModel()
    {
      iter.Prev();
      assert Valid();
      assert Parent().Valid();
      assert Parent().Iterators() >= old(Parent().Iterators());
      assert PrevModel() by {
        reveal PrevModel();
        reveal iter.PrevModel();
        assert parent.Model() == old(parent.Model());
        assert |parent.Model()| == old(|parent.Model()|);
        reveal After(), iter.After();
        assert RTraversed() == iter.RTraversed();
        assert RTraversed() == {old(Peek?())} + old(After());
        assert |RTraversed()| == 1 + old(|After()|);
      }
    }

    method Copy() returns (it: UnorderedSetIterator)
      modifies parent.Repr()
      requires allocated(parent)
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())

      requires Valid()
      requires parent.Valid()
      ensures Valid()
      ensures parent.Valid()
      ensures parent.Iterators() >= old(parent.Iterators())
      ensures fresh(it)
      ensures it != this
      ensures it.Valid()
      ensures it.Parent() == parent
      ensures it.HasPeek?() == HasPeek?()
      ensures CopyModel(it)
      ensures parent.SameIterators()
    {
      var iter': OrderedMapIterator := iter.Copy();
      it := new TreeSetIteratorImpl(parent, iter');
      assert Valid();
      assert Parent().Valid();
      assert Parent().Iterators() >= old(Parent().Iterators());
      assert fresh(it);
      assert it != this;
      assert it.Valid();
      assert it.Parent() == parent;
      calc == {
        HasPeek?();
        iter.HasPeek?();
        iter'.HasPeek?();
        { reveal TreeSetIteratorImplCtrModel(); }
        it.HasPeek?();
      }
      assert CopyModel(it) by {
        reveal CopyModel();
        reveal iter.CopyModel();
        reveal TreeSetIteratorImplCtrModel();
        assert parent.Model() == old(parent.Model());
        assert |parent.Model()| == old(|parent.Model()|);
        assert HasPeek?() == old(HasPeek?());
        if HasPeek?() {
          assert Peek?() == old(Peek?());
          assert Before() == old(Before());
          assert |Before()| == old(|Before()|);
          assert it.Before() == Before();
        }
      }
      assert parent.SameIterators() by {
        reveal parent.SameIterators(), parent.SameIteratorModel();
        reveal iter.Parent().SameIterators(), iter.Parent().SameIteratorModel();
      }
    }
  }

  class TreeSetImpl extends TreeSet {
    const treemap: TreeMap
    ghost var iterators: set<TreeSetIteratorImpl>

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads if n == 0 then {} else ReprFamily(n-1)
    {
      if n == 0 then
        {this}
      else if n == 1 then
        {this as object} + {treemap} + iterators
      else if n == 2 then
        {this as object} + {treemap} + iterators
        + (set it <- iterators :: it.iter)
      else
        {this as object} + {treemap} + iterators
        + (set it <- iterators :: it.iter)
        + treemap.ReprFamily(n-3)
    }

    ghost predicate Valid()
      reads Repr()
    {
      && ReprDepth == treemap.ReprDepth + 3
      && assert treemap.Repr() <= Repr(); true
      && treemap.Valid()
      && this !in treemap.Repr()
      && iterators !! treemap.Repr()
      && (forall it <- iterators :: it.parent == this)
      && (forall it <- iterators :: it.iter in treemap.Iterators())
      && (
        forall it1 <- iterators, it2 <- iterators | && it1 != it2 ::
          it1.iter != it2.iter
      )
    }

    ghost function Model(): set<K>
      reads Repr()
      requires Valid()
    {
      treemap.Model().Keys
    }

    ghost function Iterators(): set<UnorderedSetIterator>
      reads Repr()
      requires Valid()
      ensures forall it <- Iterators() ::
        && it in Repr()
        && it.Parent() == this
        && it is OrderedSetIterator
    {
      iterators
    }

    constructor()
      ensures Valid()
      ensures Model() == {}
      ensures fresh(Repr())
    {
      var treemap := new TreeMapImpl();
      ReprDepth := treemap.ReprDepth + 3;
      this.treemap := treemap;
      iterators := {};
    }

    method Empty() returns (b: bool)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures EmptyModel(b)
      ensures SameIterators()
    {
      b := treemap.Empty();
      assert Valid();
      assert Iterators() >= old(Iterators());
      assert EmptyModel(b) by {
        reveal EmptyModel();
        reveal treemap.EmptyModel();
        assert Model() == old(Model());
        assert |Model()| == old(|Model()|);
        assert b == (Model() == {});
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
        reveal treemap.SameIterators(), treemap.SameIteratorModel();
        forall it <- old(Iterators()) | old(it.Valid())
          ensures it.Valid()
          ensures SameIteratorModel(it)
        {
          assert it.HasPeek?() == old(it.HasPeek?());
          if it.HasPeek?() {
            assert it.Peek?() == old(it.Peek?());
            assert it.Before() == old(it.Before());
            assert |it.Before()| == old(|it.Before()|);
          }
        }
      }
    }

    method Size() returns (s: nat)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures SizeModel(s)
      ensures SameIterators()
    {
      s := treemap.Size();
      assert Valid();
      assert Iterators() >= old(Iterators());
      assert SizeModel(s) by {
        reveal SizeModel();
        reveal treemap.SizeModel();
        assert Model() == old(Model());
        assert |Model()| == old(|Model()|);
        assert s == |Model()|;
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
        reveal treemap.SameIterators(), treemap.SameIteratorModel();
        forall it <- old(Iterators()) | old(it.Valid())
          ensures it.Valid()
          ensures SameIteratorModel(it)
        {
          assert it.HasPeek?() == old(it.HasPeek?());
          if it.HasPeek?() {
            assert it.Peek?() == old(it.Peek?());
            assert it.Before() == old(it.Before());
            assert |it.Before()| == old(|it.Before()|);
          }
        }
      }
    }

    method First() returns (it: UnorderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it} + old(Iterators())

      ensures FirstModel(it)
      ensures SameIterators()
    {
      var iter: OrderedMapIterator := treemap.First();
      it := new TreeSetIteratorImpl(this, iter);
      assert Valid();
      assert Iterators() >= old(Iterators());
      assert FirstModel(it) by {
        reveal FirstModel();
        reveal treemap.FirstModel();
        reveal TreeSetIteratorImpl.TreeSetIteratorImplCtrModel();
        assert Model() == old(Model());
        assert |Model()| == old(|Model()|);
        assert it.Traversed() == {};
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
        reveal treemap.SameIterators(), treemap.SameIteratorModel();
        forall it <- old(Iterators()) | old(it.Valid())
          ensures it.Valid()
          ensures SameIteratorModel(it)
        {
          assert it.HasPeek?() == old(it.HasPeek?());
          if it.HasPeek?() {
            assert it.Peek?() == old(it.Peek?());
            assert it.Before() == old(it.Before());
            assert |it.Before()| == old(|it.Before()|);
          }
        }
      }
    }

    method Last() returns (it: OrderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it} + old(Iterators())

      ensures LastModel(it)
      ensures SameIterators()
    {
      var iter: OrderedMapIterator := treemap.Last();
      it := new TreeSetIteratorImpl(this, iter);
      assert Valid();
      assert Iterators() >= old(Iterators());
      assert LastModel(it) by {
        reveal LastModel();
        reveal treemap.LastModel();
        reveal TreeSetIteratorImpl.TreeSetIteratorImplCtrModel();
        assert Model() == old(Model());
        assert |Model()| == old(|Model()|);
        reveal it.After(), iter.After();
        assert it.RTraversed() == iter.RTraversed();
        assert it.RTraversed() == {};
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
        reveal treemap.SameIterators(), treemap.SameIteratorModel();
        forall it <- old(Iterators()) | old(it.Valid())
          ensures it.Valid()
          ensures SameIteratorModel(it)
        {
          assert it.HasPeek?() == old(it.HasPeek?());
          if it.HasPeek?() {
            assert it.Peek?() == old(it.Peek?());
            assert it.Before() == old(it.Before());
            assert |it.Before()| == old(|it.Before()|);
          }
        }
      }
    }

    method Contains(k: K) returns (b: bool)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures ContainsModel(k, b)
      ensures SameIterators()
    {
      var it: TreeSetIteratorImpl := Find(k);
      b := it.HasPeek();
      assert ContainsModel(k, b) by {
        reveal ContainsModel(), FindModel(), it.HasPeekModel();
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
      }
    }

    method Find(k: K) returns (it: UnorderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it}+old(Iterators())

      ensures FindModel(k, it)
      ensures SameIterators()
    {
      var it': OrderedMapIterator := treemap.Find(k);
      it := new TreeSetIteratorImpl(this, it');
      assert FindModel(k, it) by {
        reveal FindModel();
        reveal treemap.FindModel();
        reveal TreeSetIteratorImpl.TreeSetIteratorImplCtrModel();
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
        reveal treemap.SameIterators(), treemap.SameIteratorModel();
      }
    }

    method Add(k: K)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures AddModel(k)
      ensures AddIterators(k)
    {
      treemap.Add(k, 0);
      assert Valid();
      assert Iterators() >= old(Iterators());
      assert AddModel(k) by {
        reveal AddModel();
        reveal treemap.AddModel();
        assert Model() == old(Model()) + {k};
        if k in old(Model()) {
          assert |Model()| == old(|Model()|);
        } else {
          assert |Model()| == old(|Model()|) + 1;
        }
      }
      assert AddIterators(k) by {
        reveal AddIterators(), AddIteratorModel();
        reveal treemap.AddIterators(), treemap.AddIteratorModel();
        forall it <- old(iterators) | old(it.Valid())
          ensures it.Valid()
          ensures AddIteratorModel(it, k)
        {
          assert it.HasPeek?() == old(it.HasPeek?());
          if it.HasPeek?() {
            assert it.Peek?() == it.iter.Peek?().0;
            assert it.Peek?() == old(it.Peek?());
          }
          assert (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()));
          assert it.Traversed() == it.iter.Traversed() by {
            if it.HasPeek?() {
              assert it.Before() == it.iter.Before();
            } else {
              assert Model() == treemap.Model().Keys;
            }
          } 
          if k in old(Model()) || (it.HasPeek?() && it.Peek?() < k) {
            assert it.Traversed() == old(it.Traversed());
            assert |it.Traversed()| == old(|it.Traversed()|);
          } else {
            assert it.Traversed() == old(it.Traversed()) + {k};
            assert |it.Traversed()| == old(|it.Traversed()|) + 1;
          }
        }
      }
    }

    method Remove(k: K)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures RemoveModel(k)
      ensures RemoveIterators(k)
    {
      treemap.Remove(k);
      assert Valid();
      assert Iterators() >= old(Iterators());
      assert RemoveModel(k) by {
        reveal RemoveModel();
        reveal treemap.RemoveModel();
        assert Model() == old(Model()) - {k};
        if k in old(Model()) {
          assert |Model()| == old(|Model()|) - 1;
        } else {
          assert |Model()| == old(|Model()|);
        }
      }
      assert RemoveIterators(k) by {
        reveal RemoveIterators(), RemoveIteratorModel();
        reveal treemap.RemoveIterators(), treemap.RemoveIteratorModel();
        forall it <- old(iterators) | old(it.Valid()) && (old(it.HasPeek?()) ==> old(it.Peek?()) != k)
          ensures it.Valid()
          ensures RemoveIteratorModel(it, k)
        {
          assert it.HasPeek?() == old(it.HasPeek?());
          assert it.HasPeek?() ==> it.Peek?() == old(it.Peek?());
          if it.HasPeek?() {
            assert it.Before() == it.iter.Before();
            assert it.Traversed() == it.iter.Traversed();
          } else {
            assert Model() == treemap.Model().Keys;
            assert it.Traversed() == it.iter.Traversed();
          }
          assert it.Traversed() == it.iter.Traversed();
          if k in old(Model()) && (it.HasPeek?() ==> k < it.Peek?()) {
            assert it.Traversed() == old(it.Traversed()) - {k};
            assert |it.Traversed()| == old(|it.Traversed()|) - 1;
          } else {
            assert it.Traversed() == old(it.Traversed());
            assert |it.Traversed()| == old(|it.Traversed()|);
          }
        }
      }
    }

    method Insert(hint: UnorderedSetIterator, k: K) returns (it: UnorderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires hint.Valid()
      requires hint.Parent() == this
      requires hint in Iterators()

      ensures Valid()
      ensures fresh(it)
      ensures it.Valid() && it.Parent() == this
      ensures it.HasPeek?()
      ensures Iterators() >= {it} + old(Iterators())
      ensures InsertModel(k, it)
      ensures AddIterators(k)
    {
      var hint': TreeSetIteratorImpl := hint;
      var iter: OrderedMapIterator := treemap.Insert(hint'.iter, k, 0);
      it := new TreeSetIteratorImpl(this, iter);
      assert Valid();
      assert Iterators() >= old(Iterators());
      assert
        && it.HasPeek?()
        && InsertModel(k, it)
      by {
        reveal InsertModel();
        reveal treemap.InsertModel();
        reveal TreeSetIteratorImpl.TreeSetIteratorImplCtrModel();
        assert Model() == old(Model()) + {k};
        assert it.Peek?() == k;
        if k in old(Model()) {
          assert |Model()| == old(|Model()|);
        } else {
          assert |Model()| == old(|Model()|) + 1;
        }
      }
      assert AddIterators(k) by {
        reveal AddIterators(), AddIteratorModel();
        reveal treemap.AddIterators(), treemap.AddIteratorModel();
        forall it <- old(iterators) | old(it.Valid())
          ensures it.Valid()
          ensures AddIteratorModel(it, k)
        {
          assert it.HasPeek?() == old(it.HasPeek?());
          if it.HasPeek?() {
            assert it.Peek?() == it.iter.Peek?().0;
            assert it.Peek?() == old(it.Peek?());
          }
          assert (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()));
          assert it.Traversed() == it.iter.Traversed() by {
            if it.HasPeek?() {
              assert it.Before() == it.iter.Before();
            } else {
              assert Model() == treemap.Model().Keys;
            }
          } 
          if k in old(Model()) || (it.HasPeek?() && it.Peek?() < k) {
            assert it.Traversed() == old(it.Traversed());
            assert |it.Traversed()| == old(|it.Traversed()|);
          } else {
            assert it.Traversed() == old(it.Traversed()) + {k};
            assert |it.Traversed()| == old(|it.Traversed()|) + 1;
          }
        }
      }
    }

    method Erase(pos: UnorderedSetIterator) returns (it: UnorderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires pos.Valid()
      requires pos.Parent() == this
      requires pos.HasPeek?()
      requires pos in Iterators()

      ensures Valid()
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it} + old(Iterators())
      ensures EraseModel(pos, it)
      ensures RemoveIterators(old(pos.Peek?()))
    {
      var k := pos.Peek?();
      var pos': TreeSetIteratorImpl := pos;
      var iter: OrderedMapIterator := treemap.Erase(pos'.iter);
      it := new TreeSetIteratorImpl(this, iter);
      assert Valid();
      assert Iterators() >= old(Iterators());
      assert EraseModel(pos, it) by {
        reveal EraseModel();
        reveal treemap.EraseModel();
        reveal TreeSetIteratorImpl.TreeSetIteratorImplCtrModel();
        assert Model() == old(Model()) - {old(pos.Peek?())};
        assert |Model()| == old(|Model()|) - 1;
        assert it.Traversed() == old(pos.Before());
        assert |it.Traversed()| == old(|pos.Before()|);
      }
      assert RemoveIterators(k) by {
        reveal RemoveIterators(), RemoveIteratorModel();
        reveal treemap.RemoveIterators(), treemap.RemoveIteratorModel();
        forall it <- old(iterators) | old(it.Valid()) && (old(it.HasPeek?()) ==> old(it.Peek?()) != k)
          ensures it.Valid()
          ensures RemoveIteratorModel(it, k)
        {
          assert it.HasPeek?() == old(it.HasPeek?());
          assert it.HasPeek?() ==> it.Peek?() == old(it.Peek?());
          if it.HasPeek?() {
            assert it.Before() == it.iter.Before();
            assert it.Traversed() == it.iter.Traversed();
          } else {
            assert Model() == treemap.Model().Keys;
            assert it.Traversed() == it.iter.Traversed();
          }
          assert it.Traversed() == it.iter.Traversed();
          if k in old(Model()) && (it.HasPeek?() ==> k < it.Peek?()) {
            assert it.Traversed() == old(it.Traversed()) - {k};
            assert |it.Traversed()| == old(|it.Traversed()|) - 1;
          } else {
            assert it.Traversed() == old(it.Traversed());
            assert |it.Traversed()| == old(|it.Traversed()|);
          }
        }
      }
    }
  }
}