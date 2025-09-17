include "../../src/Collections/KeyValue.dfy"
include "../../src/Collections/Map.dfy"
include "../../src/UnorderedMap/UnorderedMapSpec.dfy"
include "../../src/OrderedMap/OrderedMapSpec.dfy"
include "../../src/TreeMap/TreeMapSpec.dfy"
include "../../src/Collections/SetInt.dfy"
include "../../src/DataStructures/ThreadedLinkedTree.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Model/Insert.dfy"

module TreeMapImpl {
  import opened KeyValue
  import opened UnorderedMapSpec
  import opened OrderedMapSpec
  import opened TreeMapSpec
  import opened SetInt
  import opened Map
  import opened ThreadedLinkedTree
  import opened ModelB = ThreadedLinkedTree.Model.Base
  import opened ModelI = ThreadedLinkedTree.Model.Insert
  import opened ModelR = ThreadedLinkedTree.Model.RemoveRoot
  import opened ModelIt = ThreadedLinkedTree.Model.Iterator
  import opened ThreadedLinkedTree.Impl.TTNode
  import opened ThreadedLinkedTree.Impl.TTree

  class TreeMapIteratorImpl extends OrderedMapIterator {
    const iter: ThreadedLinkedTreeIterator
    ghost const parent: TreeMapImpl

    ghost function Parent(): UnorderedMap
      ensures Parent() is OrderedMap
    {
      parent
    }

    ghost predicate Valid()
      reads Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()
    {
      && parent.Valid()
      && this in parent.iterators
      && iter.parent == parent.tree
      && iter.Valid()
    }

    ghost predicate HasPeek?()
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
    {
      ModelIt.HasPeek(iter.Model())
    }

    ghost function Peek?(): (K, V)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures PeekSpec(Peek?())
      ensures PeekOrderSpec(Peek?())
    {
      reveal PeekSpec(), PeekOrderSpec();
      iter.ValidImp();
      ModelIt.PeekSpec(iter.Model(), iter.parent.Model());
      var p := ModelIt.Peek(iter.Model(), iter.parent.Model());
      assert (forall x <- Parent().Model() | x !in Before() :: p.0 <= x);
      p
    }

    ghost function Before(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures BeforeSpec(Before())
    {
      reveal BeforeSpec();
      iter.ValidImp();
      SmallerKeys(iter.parent.Model(), iter.node.key);
      ModelIt.BeforeSpec(iter.Model(), iter.parent.Model());
      ModelIt.Before(iter.Model(), iter.parent.Model())
    }

    constructor (ghost parent: TreeMapImpl, iter: ThreadedLinkedTreeIterator)
      modifies parent`iterators
      requires parent.Valid()
      requires iter.Valid()
      requires iter.Parent() == parent.tree
      requires forall it <- parent.iterators :: it.iter != iter
      ensures parent.Valid()
      ensures parent.Model() == old(parent.Model())
      ensures |parent.Model()| == |old(parent.Model())|
      ensures parent.Valid()
      ensures Valid()
      ensures this.parent == parent
      ensures HasPeek?() == iter.HasPeek()
      ensures HasPeek?() ==> Peek?() == iter.Peek()
      ensures parent.iterators == {this} + old(parent.iterators)
      ensures Parent().SameIterators()
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())
    {
      this.iter := iter;
      this.parent := parent;
      new;
      parent.iterators := parent.iterators + {this};
      if HasPeek?() {
        iter.PeekEq();
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
      iter.ValidImp();
      iter.HasPeekEq();
      assert HasPeekModel() by {
        reveal HasPeekModel();
      }
      assert Parent().SameIterators() by {
        reveal parent.SameIterators(), parent.SameIteratorModel();
      }
      return iter.HasPeek();
    }

    method Peek() returns (p: (K, V))
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      //ensures Parent() == old(Parent())
      ensures HasPeek?()
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures PeekModel(p)
      ensures Parent().SameIterators()
    {
      iter.ValidImp();
      assert PeekModel(iter.Peek()) by {
        reveal PeekModel(), PeekSpec();
        assert iter.Peek() == Peek?() by {
          iter.PeekEq();
        }
      }
      assert Parent().SameIterators() by {
        reveal parent.SameIterators(), parent.SameIteratorModel();
      }
      return iter.Peek();
    }

    method Next()
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      //ensures Parent() == old(Parent())
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures NextModel()
      ensures NextIterators()
    {
      iter.Next();
      assert NextModel() by {
        reveal NextModel();
        calc == {
          Traversed();
          { ToMapRecKeys(iter.parent.Model()); }
          ModelIt.Traversed(iter.Model(), iter.parent.Model());
          {
            iter.ValidImp();
            iter.parent.ThreadedImp();
            ModelIt.NextTraversed(old(iter.Model()), old(iter.parent.Model()));
          }
          old(ModelIt.Before(iter.Model(), iter.parent.Model()) + {ModelIt.Peek(iter.Model(), iter.parent.Model()).0});
          old(Before() + {Peek?().0});
        }
        assert Traversed() == {old(Peek?().0)} + old(Before());
        assert |Traversed()| == 1 + old(|Before()|) by {
          reveal PeekSpec();
        }
      }
      assert NextIterators() by {
        reveal NextIterators(), parent.SameIteratorModel();
      }
    }

    lemma RTraversedEq()
      requires Valid()
      requires parent.Valid()
      ensures RTraversed()
        == ModelIt.RTraversed(iter.Model(), iter.parent.Model())
    {
      ModelIt.RTraversedSpec(iter.Model(), iter.parent.Model());
      if HasPeek?() {
        iter.ValidImp();
        calc == {
          After();
          { reveal After(); }
          (toMapRec(iter.parent.Model()).Keys - {Peek?().0}) - ModelIt.Before(iter.Model(), iter.parent.Model());
          { ModelIt.AfterSpec(iter.Model(), iter.parent.Model()); }
          ModelIt.After(iter.Model(), iter.parent.Model());
        }
      } else {
        assert keys(iter.parent.Model()) == parent.Model().Keys;
      }
    }

    method Prev()
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      //ensures Parent() == old(Parent())
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures PrevModel()
      ensures NextIterators()
    {
      iter.Prev();
      assert PrevModel() by {
        reveal PrevModel();
        calc == {
          RTraversed();
          { RTraversedEq(); }
          ModelIt.RTraversed(iter.Model(), iter.parent.Model());
          {
            iter.ValidImp();
            iter.parent.ThreadedImp();
            ModelIt.PrevRTraversed(old(iter.Model()), old(iter.parent.Model()));
          }
          old(ModelIt.After(iter.Model(), iter.parent.Model()) + {ModelIt.Peek(iter.Model(), iter.parent.Model()).0});
          {
            assert old(ModelIt.After(iter.Model(), iter.parent.Model())) == old(After()) by {
              ModelIt.AfterSpec(old(iter.Model()), old(iter.parent.Model()));
              reveal After();
            }
          }
          old(After() + {Peek?().0});
        }
        assert RTraversed() == {old(Peek?().0)} + old(After());
        assert |RTraversed()| == 1 + old(|After()|) by {
          reveal PeekSpec(), After();
        }
      }
      assert NextIterators() by {
        reveal NextIterators(), parent.SameIteratorModel();
      }
    }

    method Copy() returns (it: UnorderedMapIterator)
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
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures fresh(it)
      ensures it != this
      ensures it.Valid()
      ensures it.Parent() == Parent()
      ensures it.HasPeek?() == HasPeek?()
      ensures CopyModel(it)
      ensures Parent().SameIterators()
    {
      iter.parent.ThreadedImp();
      var iter' := new ThreadedLinkedTreeIterator(iter.node, iter.parent);
      it := new TreeMapIteratorImpl(parent, iter');
      assert CopyModel(it) by {
        reveal CopyModel();
      }
      assert Parent().SameIterators() by {
        reveal parent.SameIterators(), parent.SameIteratorModel();
      }
    }
  }

  class TreeMapImpl extends TreeMap {
    const tree: ThreadedLinkedTree
    var size: nat
    ghost var iterators: set<TreeMapIteratorImpl>

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads if n == 0 then {} else ReprFamily(n-1)
    {
      if n == 0 then
        {this}
      else if n == 1 then
        ReprFamily(0) + {tree} + iterators
      else if n == 2 then
        ReprFamily(1) + tree.Repr() + (set it <- iterators :: it.iter)
      else
        ReprFamily(n-1)
    }

    ghost predicate Valid()
      reads Repr()
    {
      && ReprDepth == 2
      && assert tree in ReprFamily(1) && tree.Repr() <= ReprFamily(2); true
      && tree.Valid()
      && tree.Threaded()
      && tree.SearchTree()
      && tree.RedBlackTree()
      && ModelB.size(tree.Model()) == size
      && (forall it | it in iterators :: it.parent == this)
      && (forall it | it in iterators :: it.iter in tree.iterators)
      && (
        forall it1 <- iterators, it2 <- iterators | && it1 != it2 ::
          it1.iter != it2.iter
      )
    }

    ghost function Model(): map<K, V>
      reads Repr()
      requires Valid()
    {
      toMapRec(tree.Model())
    }

    ghost function Iterators(): set<UnorderedMapIterator>
      reads Repr()
      requires Valid()
      ensures forall it <- Iterators() ::
         && it in Repr()
         && it.Parent() == this
         && it is OrderedMapIterator
    {
      iterators
    }

    constructor()
      ensures Valid()
      ensures Model() == map[]
      ensures fresh(Repr())
    {
      ReprDepth := 2;
      size := 0;
      tree := new ThreadedLinkedTree();
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
      b := tree.root == null;
      assert EmptyModel(b) by {
        reveal EmptyModel();
        assert Model() == old(Model());
        assert |Model()| == old(|Model()|);
        assert b == (Model() == map[]);
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
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
      assert SizeModel(size) by {
        reveal SizeModel();
        SizeLemmas(tree.Model());
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
      }
      return size;
    }

    method First() returns (it: UnorderedMapIterator)
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
      ThreadedRootImp(tree.skeleton);
      var iter := tree.First();
      var it' := new TreeMapIteratorImpl(this, iter);
      assert it'.Valid();
      it := it' as UnorderedMapIterator;
      assert fresh(it);
      assert it.Valid();
      assert it.Parent() == this;
      assert Iterators() >= {it} + old(Iterators());
      assert FirstModel(it) by {
        reveal FirstModel();
        ModelIt.FirstTraversed(tree.Model());
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
      }
    }

    method Last() returns (it: OrderedMapIterator)
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
      ThreadedRootImp(tree.skeleton);
      var iter := tree.Last();
      var it' := new TreeMapIteratorImpl(this, iter);
      assert it'.Valid();
      it := it' as UnorderedMapIterator;
      assert fresh(it);
      assert it.Valid();
      assert it.Parent() == this;
      assert Iterators() >= {it} + old(Iterators());
      assert LastModel(it) by {
        reveal LastModel();
        assert it.RTraversed() == {} by {
          ModelIt.LastRTraversed(tree.Model());
          it'.RTraversedEq();
        }
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
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
      var it: TreeMapIteratorImpl := Find(k);
      b := it.HasPeek();
      assert ContainsModel(k, b) by {
        reveal ContainsModel(), FindModel(), it.HasPeekModel();
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
      }
    }

    method At(k: K) returns (v: V)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires AtModelPre(k)
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures AtModel(k, v)
      ensures SameIterators()
    {
      var it: TreeMapIteratorImpl := Find(k);
      assert it.HasPeek?() by {
        reveal FindModel(), AtModelPre();
        assert it.Peek?().0 == k;
      }
      var p := it.Peek();
      v := p.1;
      assert AtModel(k, v) by {
        reveal AtModel(), AtModelPre(), FindModel(), it.PeekModel();
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
      }
    }

    method Find(k: K) returns (it: UnorderedMapIterator)
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
      var it' := tree.Find(k);
      it := new TreeMapIteratorImpl(this, it');
      assert FindModel(k, it) by {
        reveal FindModel();
        ToMapRecKeys(tree.Model());
      }
      assert SameIterators() by {
        reveal SameIterators(), SameIteratorModel();
      }
    }

    method Add(k: K, v: V)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures AddModel(k, v)
      ensures AddIterators(k, v)
    {
      var hint := First();
      label PreInsert:
      var _ := Insert(hint, k, v);
      assert AddModel(k, v) by {
        reveal AddModel(), FirstModel(), InsertModel();
      }
      assert AddIterators(k, v) by {
        reveal AddIterators();
        assert AddIterators@PreInsert(k, v);
        forall it <- old(Iterators()) | old(it.Valid())
          ensures it.Valid()
          ensures AddIteratorModel(it, k, v)
        {
          reveal AddIteratorModel();
          reveal AddModel(), FirstModel(), InsertModel(), SameIterators(), SameIteratorModel();
          assert AddIteratorModel@PreInsert(it, k, v);
          assert AddIteratorModel(it, k, v) by {
            assert it.HasPeek?() == old(it.HasPeek?());
            if it.HasPeek?() {
              assert it.Peek?().0 == old(it.Peek?().0);
              if k in old(Model()) && k == it.Peek?().0 {
                assert it.Peek?().1 == v;
              } else {
                assert it.Peek?().1 == old(it.Peek?().1);
              }
            }
            if k in old(Model()) || (it.HasPeek?() && it.Peek?().0 < k) {
              assert it.Traversed() == old(it.Traversed());
              assert |it.Traversed()| == old(|it.Traversed()|);
            } else {
              assert it.Traversed() == old(it.Traversed()) + {k};
              assert |it.Traversed()| == old(|it.Traversed()|) + 1;
            }
          }
        }
      }
    }

    twostate lemma RemoveIteratorsProof(it: TreeMapIteratorImpl, k: K)
      requires old(Valid())
      requires Valid()
      requires it in old(Iterators())
      requires old(it.Valid()) 
      requires old(it.HasPeek?()) ==> old(it.Peek?().0) != k
      requires Model() == old(Model()) - {k}
      requires it.iter.Model() == old(it.iter.Model())
      requires Iterators() >= old(Iterators())
      requires forall it
          | it in old(tree.Iterators())
          && old(it.Valid())
          && (old(it.HasPeek()) ==> old(it.Peek().0) != k) ::
        && it.Valid()
        //&& it.Parent() == old(it.Parent())  // obvious since it.parent is const
        && it.Model() == old(it.Model())
        && it.HasPeek() == old(it.HasPeek())
      ensures it.Valid()
      ensures RemoveIteratorModel(it, k)
    {
      if old(it.iter.HasPeek()) {
        calc == {
          old(it.iter.Peek());
          { assert old(it.iter.PeekEq(); true); }
          old(it.iter.Peek'());
          old(it.Peek?());
          old(it.Peek?());
        }
      }
      assert it.Valid() by {
        assert it.parent.Valid();
        assert it in it.parent.iterators;
        assert it.iter.parent == it.parent.tree;
        assert it.iter.Valid();
      }
      assert RemoveIteratorModel(it, k) by {
        reveal RemoveIteratorModel();
        assert it.HasPeek?() == old(it.HasPeek?());
        it.iter.ValidImp();
        it.iter.HasPeekEq();
        assert old(it.iter.ValidImp(); true);
        ModelIt.ModelAfterRemove(
          it.iter.Model(), 
          k, 
          old(tree.Model()), 
          tree.Model()
        );
        if it.HasPeek?() {
          it.iter.PeekEq();
          calc == {
            it.iter.Peek();
            { it.iter.PeekEq(); }
            it.iter.Peek'();
            it.Peek?();
            it.Peek?();
          }
          assert it.Peek?() == old(it.Peek?());
        }
        assert
          (
            && k in old(Model())
            && (it.HasPeek?() ==> k < it.Peek?().0)
          ) <==> (
            && k in old(keys(tree.Model()))
            && (it.iter.Model().Link? ==> k < it.iter.Model().link)
          )
        by {
          ToMapRecKeys(old(tree.Model()));
        }
        if k in old(Model()) && (it.HasPeek?() ==> k < it.Peek?().0) {
          assert it.Traversed() == old(it.Traversed()) - {k};
          assert |it.Traversed()| == old(|it.Traversed()|) - 1;
        } else {
          assert it.Traversed() == old(it.Traversed());
          assert |it.Traversed()| == old(|it.Traversed()|);
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
      ModelR.RemoveRootSpec(tree.Model(), k);
      ModelR.RemoveRootSize(tree.Model(), k);
      ModelR.IsRemovedRootSpec(tree.Model(), k);
      ModelR.RemoveRootModel(tree.Model(), k);
      var isRemoved := tree.Remove(k);
      if isRemoved {
        size := size - 1;
      }
      assert RemoveModel(k) by {
        reveal RemoveModel();
      }
      assert RemoveIterators(k) by {
        reveal RemoveIterators();
        forall it <- old(Iterators()) | old(it.Valid()) && (old(it.HasPeek?()) ==> old(it.Peek?().0) != k)
          ensures it.Valid()
          ensures RemoveIteratorModel(it, k)
        {
          var it': TreeMapIteratorImpl := it;
          reveal RemoveModel();
          RemoveIteratorsProof(it', k);
        }
      }
    }

    twostate lemma InsertIteratorsProof(it: TreeMapIteratorImpl, k: K, v: V)
      requires old(Valid())
      requires Valid()
      requires it in old(Iterators())
      requires old(it.Valid()) 
      requires Model() == old(Model()) + map[k := v]
      requires it.iter.Model() == old(it.iter.Model())
      requires Iterators() >= old(Iterators())
      requires forall it
          | it in old(tree.Iterators())
          && old(it.Valid()) ::
        && it.Valid()
        && it.Model() == old(it.Model())
        && it.HasPeek() == old(it.HasPeek())
      ensures it.Valid()
      ensures AddIteratorModel(it, k, v)
    {
      assert it.Valid() by {
      }
      assert AddIteratorModel(it, k, v) by {
        reveal AddIteratorModel();
        ToMapRecKeys(old(tree.Model()));
        ToMapRecKeys(tree.Model());
        assert old(it.iter.ValidImp(); true);
        assert Model() == old(Model())[k := v] by {
          UpdateEqAdd(old(Model()), k, v);
        }
        ModelIt.ModelAfterInsert(it.iter.Model(), k, v, old(tree.Model()), tree.Model());
        assert it.HasPeek?() == old(it.HasPeek?()) by {
        }
        if it.HasPeek?() {
          it.iter.PeekEq();
          assert it.Peek?().0 == old(it.Peek?().0);
          if k in old(Model()) && k == it.Peek?().0 {
            assert it.Peek?().1 == v;
          } else {
            assert it.Peek?().1 == old(it.Peek?().1);
          }
        }
        assert
          (
            k in old(Model()) || (it.HasPeek?() && it.Peek?().0 < k)
          ) <==> (
            k in keys(old(tree.Model())) || (it.iter.Model().Link? && it.iter.Model().link < k)
          )
        by {
          ToMapRecKeys(old(tree.Model()));
        }
        if k in old(Model()) || (it.HasPeek?() && it.Peek?().0 < k) {
          assert it.Traversed() == old(it.Traversed());
          assert |it.Traversed()| == old(|it.Traversed()|);
        } else {
          assert it.Traversed() == old(it.Traversed()) + {k};
          assert |it.Traversed()| == old(|it.Traversed()|) + 1;
        }
      }
    }

    method Insert(hint: UnorderedMapIterator, k: K, v: V) returns (it: UnorderedMapIterator)
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
      ensures InsertModel(k, v, it)
      ensures AddIterators(k, v)
    {
      ModelI.InsertRootSpec(tree.Model(), k, v);
      ModelI.InsertRootSize(tree.Model(), k, v);
      ModelI.IsInsertedSpec(tree.Model(), k);
      ModelI.InsertRootModel(tree.Model(), k, v);
      var isInserted, iter := tree.Insert(k, v);
      ModelIt.FindAfterInsert(k, v, iter.parent.Model());
      if isInserted {
        size := size + 1;
      }
      it := new TreeMapIteratorImpl(this, iter);
      assert InsertModel(k, v, it) by {
        reveal InsertModel();
        calc == {
          Model();
          old(Model())[k := v];
          { UpdateEqAdd(old(Model()), k, v); }
          old(Model()) + map[k := v];
        }
      }
      assert AddIterators(k, v) by {
        reveal AddIterators();
        forall it <- old(Iterators()) | old(it.Valid())
          ensures it.Valid()
          ensures AddIteratorModel(it, k, v)
        {
          var it': TreeMapIteratorImpl := it;
          reveal InsertModel();
          InsertIteratorsProof(it', k, v);
        }
      }
    }

    method Erase(pos: UnorderedMapIterator) returns (it: UnorderedMapIterator)
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
      ensures RemoveIterators(old(pos.Peek?().0))
    {
      it := pos.Copy();
      assert it.HasPeek?() by {
        reveal pos.CopyModel();
      }
      label PreNext:
      it.Next();
      it.NextIterator@PreNext(pos);
      assert pos.HasPeek?() by { reveal SameIteratorModel(); }
      label PrePeek:
      var p := pos.Peek();
      SameIterator@PrePeek(it);
      label PreRemove:
      Remove(p.0);
      assert old@PreRemove(RemoveIteratorTraversedShrinksModelPre(it, p.0)) by {
        reveal RemoveIteratorTraversedShrinksModelPre();
        reveal SameIteratorModel();
        reveal OrderedMapIterator.CopyModel();
        reveal OrderedMapIterator.NextModel();
        reveal OrderedMapIterator.PeekModel();
        reveal OrderedMapIterator.PeekSpec();
        reveal OrderedMapIterator.PeekOrderSpec();
      }
      RemoveIteratorTraversedShrinks@PreRemove(it, p.0);
      assert it.Valid();
      assert it.Parent() == this;
      assert EraseModel(pos, it) by {
        reveal EraseModel();
        reveal SameIteratorModel();
        reveal OrderedMapIterator.CopyModel();
        reveal OrderedMapIterator.NextModel();
        reveal OrderedMapIterator.PeekModel();
        reveal OrderedMapIterator.PeekSpec();
        reveal OrderedMapIterator.PeekOrderSpec();
        reveal RemoveModel();
        reveal RemoveIteratorTraversedShrinksModel();
      }
      assert RemoveIterators(old(pos.Peek?().0)) by {
        reveal EraseModel();
        reveal SameIterators();
        reveal SameIteratorModel();
        reveal OrderedMapIterator.CopyModel();
        reveal OrderedMapIterator.NextModel();
        reveal OrderedMapIterator.NextIterators();
        reveal OrderedMapIterator.PeekModel();
        reveal OrderedMapIterator.PeekSpec();
        reveal OrderedMapIterator.PeekOrderSpec();
        reveal RemoveModel();
        reveal RemoveIterators();
        reveal RemoveIteratorModel();
        var k := old(pos.Peek?().0);
        assert p.0 == k;
        forall it <- old(Iterators()) | old(it.Valid()) && (old(it.HasPeek?()) ==> old(it.Peek?().0) != k)
          ensures it.Valid()
          ensures RemoveIteratorModel(it, k)
        {
          assert it.HasPeek?() == old(it.HasPeek?());
          assert (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()));
          if k in old(Model()) && (it.HasPeek?() ==> k < it.Peek?().0) {
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