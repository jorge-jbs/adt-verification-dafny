include "../../src/Collections/KeyValue.dfy"
include "../../src/Collections/OrderedSetUtils.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Model/Iterator2.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Model/Find2.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Model/Insert.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Impl/Find2.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Impl/Insert.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Impl/RemoveRoot.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Impl/Min.dfy"
include "../../src/DataStructures/ThreadedLinkedTree/Impl/Max.dfy"

module ThreadedLinkedTree {
  import opened KeyValue
  import opened OrderedSetUtils
  import ModelB = Model.Base
  import ModelF = Model.Find
  import ModelI = Model.Insert
  import ModelR = Model.RemoveRoot
  import ModelIt = Model.Iterator
  import opened Impl.TTNode
  import opened T = Impl.TTree
  import opened Impl.Insert
  import opened Impl.Find
  import opened R = Impl.RemoveRoot
  import opened Impl.Min
  import opened Impl.Max

  class ThreadedLinkedTreeIterator {
    var node: TTNode?
    ghost const parent: ThreadedLinkedTree

    ghost function Parent(): ThreadedLinkedTree
    {
      parent
    }

    ghost predicate Valid()
      reads this, parent
    {
      && (node != null ==> node in elems(parent.skeleton))
      && this in parent.iterators
    }

    ghost function Skeleton(): ttree<TTNode>
      reads this, parent, parent.Repr()
      requires Valid()
      requires parent.Valid()
      requires parent.SearchTree()
    {
      if node == null then
        Empty
      else
        GetSk(node, parent.root, parent.skeleton)
    }

    ghost function Model(): ModelIt.iter
      reads this
    {
      if node == null then
        ModelIt.Null
      else
        // we do not need `reads node` because `key` is a constant
        ModelIt.Link(node.key)
    }

    ghost predicate Valid'()
      reads this, node, parent, parent.Repr()
    {
      ModelIt.Valid(Model(), parent.Model())
    }

    lemma ValidImp()
      ensures Valid() ==> Valid'()
    {
      KeysAndElems(parent.skeleton);
    }

    constructor Root(parent: ThreadedLinkedTree)
    {
      this.node := parent.root;
      this.parent := parent;
    }

    constructor(node: TTNode?, ghost parent: ThreadedLinkedTree)
      modifies parent`iterators
      requires parent.Valid()
      requires parent.Threaded()
      requires parent.SearchTree()
      requires ModelB.ThreadedTreeRoot(parent.Model())
      requires node != null ==> node in elems(parent.skeleton)
      ensures Valid()
      ensures
        if node == null then
          Model() == ModelIt.Null
        else
          Model() == ModelIt.Link(node.key)
      ensures Parent() == parent
      ensures parent.Valid()
      ensures parent.Threaded()
      ensures parent.SearchTree()
      ensures ModelB.ThreadedTreeRoot(parent.Model())
      ensures old(parent.RedBlackTree()) ==> parent.RedBlackTree()
      ensures parent.Model() == old(parent.Model())
      ensures parent.iterators == {this} + old(parent.iterators)
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())
    {
      this.node := node;
      this.parent := parent;
      new;
      parent.iterators := parent.iterators + {this};
      KeysAndElems(parent.skeleton);
    }

    constructor First(parent: ThreadedLinkedTree)
      modifies parent`iterators
      requires parent.Valid()
      requires parent.Threaded()
      requires parent.SearchTree()
      requires ModelB.ThreadedTreeRoot(parent.Model())
      ensures Valid()
      ensures Model() == ModelIt.First(parent.Model())
      ensures Parent() == parent
      ensures parent.Valid()
      ensures parent.Threaded()
      ensures parent.SearchTree()
      ensures ModelB.ThreadedTreeRoot(parent.Model())
      ensures old(parent.RedBlackTree()) ==> parent.RedBlackTree()
      ensures parent.Model() == old(parent.Model())
      ensures parent.iterators == {this} + old(parent.iterators)
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())
    {
      this.node := parent.root;
      this.parent := parent;
      new;
      parent.iterators := parent.iterators + {this};
      ValidImp();
      if parent.root == null {
        this.node := null;
      } else {
        ghost var sk;
        this.node, sk := Min.Min(parent.root, parent.skeleton);
      }
    }

    constructor Last(parent: ThreadedLinkedTree)
      modifies parent`iterators
      requires parent.Valid()
      requires parent.Threaded()
      requires parent.SearchTree()
      requires ModelB.ThreadedTreeRoot(parent.Model())
      ensures Valid()
      ensures Model() == ModelIt.Last(parent.Model())
      ensures Parent() == parent
      ensures parent.Valid()
      ensures parent.Threaded()
      ensures parent.SearchTree()
      ensures ModelB.ThreadedTreeRoot(parent.Model())
      ensures old(parent.RedBlackTree()) ==> parent.RedBlackTree()
      ensures parent.Model() == old(parent.Model())
      ensures parent.iterators == {this} + old(parent.iterators)
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())
    {
      this.node := parent.root;
      this.parent := parent;
      new;
      parent.iterators := parent.iterators + {this};
      ValidImp();
      if parent.root == null {
        this.node := null;
      } else {
        ghost var sk;
        this.node, sk := Max.Max(parent.root, parent.skeleton);
      }
    }

    constructor At(node: TTNode, parent: ThreadedLinkedTree)
      modifies parent`iterators
      requires parent.Valid()
      requires parent.Threaded()
      requires parent.SearchTree()
      requires ModelB.ThreadedTreeRoot(parent.Model())
      requires node in elems(parent.skeleton)
      ensures Valid()
      ensures Model() == ModelIt.Find(node.key, parent.Model())
      ensures Parent() == parent
      ensures parent.Valid()
      ensures parent.Threaded()
      ensures parent.SearchTree()
      ensures ModelB.ThreadedTreeRoot(parent.Model())
      ensures old(parent.RedBlackTree()) ==> parent.RedBlackTree()
      ensures parent.Model() == old(parent.Model())
      ensures parent.iterators == {this} + old(parent.iterators)
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())
    {
      this.node := node;
      this.parent := parent;
      new;
      parent.iterators := parent.iterators + {this};
      KeysAndElems(parent.skeleton);
    }

    predicate HasPeek()
      reads this
    {
      node != null
    }

    ghost predicate HasPeek'()
      reads this
    {
      ModelIt.HasPeek(Model())
    }

    lemma HasPeekEq()
      ensures HasPeek() <==> HasPeek'()
    {}

    function Peek(): (K, V)
      reads this, parent, parent.Repr()
      requires Valid()
      requires HasPeek()
    {
      (node.key, node.value)
    }

    ghost function Peek'(): (K, V)
      reads this, parent, parent.Repr()
      requires Valid()
      requires HasPeek()
    {
      ValidImp();
      ModelIt.Peek(Model(), parent.Model())
    }

    lemma PeekEq()
      requires Valid()
      requires HasPeek()
      requires parent.Valid()
      requires parent.SearchTree()
      ensures Peek() == Peek'()
    {
      GetValue(node, parent.root, parent.skeleton);
      ModelB.ToMapRecKeys(parent.Model());
      KeysAndElems(parent.skeleton);
      ModelB.Get'ToMapRec(parent.Model(), node.key);
      ModelB.GetEqGet'(parent.Model(), node.key);
    }

    method Next()  // 8"
      modifies this
      requires parent.Valid()
      requires parent.Threaded()
      requires parent.SearchTree()
      requires Valid()
      requires assert Valid'() by {ValidImp();} true
      requires assert ModelB.ThreadedTreeRoot(parent.Model()) by {parent.ThreadedImp();} true
      requires HasPeek()

      ensures parent.Valid()
      ensures parent.Threaded()
      ensures parent.SearchTree()
      ensures Valid()
      ensures Model() == ModelIt.Next(old(Model()), old(parent.Model()))

      requires allocated(parent.Repr())
      ensures allocated(parent.Repr())
    {
      assert ModelB.ThreadedTreeRoot(parent.Model()) by {
        parent.ThreadedImp();
      }
      if node.right == null {
        assert ValidRec(node.right, Skeleton().right);
        assert Skeleton().right.Empty?;
        assert TreeModelRec(Skeleton()).right.Empty?;
        node := null;
      } else if node.isThreadRight {
        assert ValidChild(node.right, Skeleton().right, true);
        assert Skeleton().right.Thread?;
        assert TreeModelRec(Skeleton()).right.Thread?;
        assert TreeModelRec(Skeleton()) == ModelB.GetSubtree(parent.Model(), Model().link);
        assert TreeModelRec(Skeleton()).right.thread == node.right.key;
        assert node.right in elems(parent.skeleton) by {
          assert node.right in elemsAndThreads(Skeleton());
          calc {
            elemsAndThreads(Skeleton());
            <= {parent.SubtreeOfInElems(node, Skeleton());} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
        }
        node := node.right;
        assert Model() == ModelIt.Next(old(Model()), old(parent.Model())) by {
          calc == {
            ModelIt.Next(old(Model()), old(parent.Model()));
            ModelIt.Link(old(TreeModelRec(Skeleton()).right.thread));
            ModelIt.Link(old(node.right.key));
            Model();
          }
        }
      } else {
        assert ValidRec(node.right, Skeleton().right);
        assert Skeleton().right.Node?;
        assert TreeModelRec(Skeleton()).right.Node?;
        assert node.right in elems(Skeleton());
        assert elems(Skeleton()) <= elems(parent.skeleton) by {
          calc {
            elems(Skeleton());
            <= {ElemsInElemsAndThreads(Skeleton());} elemsAndThreads(Skeleton());
            <= {parent.SubtreeOfInElems(node, Skeleton());} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
        }
        parent.ElemsOfThread();
        ghost var sk;
        node, sk := Min.Min(node.right, Skeleton().right);
      }
    }

    method Prev()  // 8"
      modifies this
      requires parent.Valid()
      requires parent.Threaded()
      requires parent.SearchTree()
      requires Valid()
      requires assert Valid'() by {ValidImp();} true
      requires assert ModelB.ThreadedTreeRoot(parent.Model()) by {parent.ThreadedImp();} true
      requires HasPeek()

      ensures parent.Valid()
      ensures parent.Threaded()
      ensures parent.SearchTree()
      ensures Valid()
      ensures Model() == ModelIt.Prev(old(Model()), old(parent.Model()))

      requires allocated(parent.Repr())
      ensures allocated(parent.Repr())
    {
      assert ModelB.ThreadedTreeRoot(parent.Model()) by {
        parent.ThreadedImp();
      }
      if node.left == null {
        assert ValidRec(node.left, Skeleton().left);
        assert Skeleton().left.Empty?;
        assert TreeModelRec(Skeleton()).left.Empty?;
        node := null;
      } else if node.isThreadLeft {
        assert ValidChild(node.left, Skeleton().left, true);
        assert Skeleton().left.Thread?;
        assert TreeModelRec(Skeleton()).left.Thread?;
        assert TreeModelRec(Skeleton()) == ModelB.GetSubtree(parent.Model(), Model().link);
        assert TreeModelRec(Skeleton()).left.thread == node.left.key;
        assert node.left in elems(parent.skeleton) by {
          assert node.left in elemsAndThreads(Skeleton());
          calc {
            elemsAndThreads(Skeleton());
            <= {parent.SubtreeOfInElems(node, Skeleton());} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
        }
        node := node.left;
        assert Model() == ModelIt.Prev(old(Model()), old(parent.Model())) by {
          calc == {
            ModelIt.Prev(old(Model()), old(parent.Model()));
            ModelIt.Link(old(TreeModelRec(Skeleton()).left.thread));
            ModelIt.Link(old(node.left.key));
            Model();
          }
        }
      } else {
        assert ValidRec(node.left, Skeleton().left);
        assert Skeleton().left.Node?;
        assert TreeModelRec(Skeleton()).left.Node?;
        assert node.left in elems(Skeleton());
        assert elems(Skeleton()) <= elems(parent.skeleton) by {
          calc {
            elems(Skeleton());
            <= {ElemsInElemsAndThreads(Skeleton());} elemsAndThreads(Skeleton());
            <= {parent.SubtreeOfInElems(node, Skeleton());} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
        }
        parent.ElemsOfThread();
        ghost var sk;
        node, sk := Max.Max(node.left, Skeleton().left);
      }
    }
  }

  class ThreadedLinkedTree {
    var root: TTNode?
    ghost var skeleton: ttree<TTNode>
    ghost var iterators: set<ThreadedLinkedTreeIterator>

    ghost function Repr(): set<object>
      reads this
    {
      elems(skeleton) + iterators
    }

    ghost predicate Valid()
      reads this, Repr()
    {
      && ValidRec(root, skeleton)
      && forall it | it in iterators :: it.Parent() == this
    }

    lemma ThreadedImp()
      requires Valid()
      requires Threaded()
      ensures ModelB.ThreadedTreeRoot(Model())
    {
      ThreadedRootImp(skeleton);
    }

    constructor()
      ensures Valid()
      ensures Threaded()
      ensures Model().Empty?
      ensures SearchTree()
      ensures RedBlackTree()
      ensures Iterators() == {}
      ensures fresh(Repr())
      ensures allocated(Repr())
    {
      root := null;
      skeleton := Empty;
      iterators := {};
    }

    ghost predicate SearchTree()
      reads this, Repr()
      requires Valid()
    {
      SearchTreeRec(skeleton)
    }

    ghost predicate Threaded()
      reads this, Repr()
      requires Valid()
    {
      ThreadedRoot(skeleton)
    }

    ghost function Model(): ModelB.trbtree
      reads this, elems(skeleton)
    {
      TreeModelRec(skeleton)
    }

    ghost function Iterators(): set<ThreadedLinkedTreeIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    {
      iterators
    }

    method First() returns (it: ThreadedLinkedTreeIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires SearchTree()
      requires Threaded()
      ensures Valid()
      ensures Threaded()
      ensures Model() == old(Model())

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Model() == ModelIt.First(Model())

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Model() == old(it.Model())
    {
      ThreadedImp();
      it := new ThreadedLinkedTreeIterator.First(this);
    }

    method Last() returns (it: ThreadedLinkedTreeIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires SearchTree()
      requires Threaded()
      ensures Valid()
      ensures Threaded()
      ensures Model() == old(Model())

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Model() == ModelIt.Last(Model())

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Model() == old(it.Model())
    {
      ThreadedImp();
      it := new ThreadedLinkedTreeIterator.Last(this);
    }

    method Find(k: K) returns (it: ThreadedLinkedTreeIterator)
      modifies this, Repr()

      requires Valid()
      requires SearchTree()
      requires Threaded()
      
      ensures Valid()
      ensures Threaded()
      ensures SearchTree()
      ensures Model() == old(Model())

      ensures fresh(it)
      ensures it.Parent() == this
      ensures it.Valid()
      ensures it.Model() == ModelIt.Find(k, Model())

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Model() == old(it.Model())
    {
      ThreadedImp();
      ModelF.FindSpec(Model(), k);
      var foundNode, foundSk := FindRec(root, false, skeleton, k);
      it := new ThreadedLinkedTreeIterator(foundNode, this);
    }

    lemma ElemsOfThread()
      requires Valid()
      requires Threaded()
      ensures elems(skeleton) == elemsAndThreads(skeleton)
    {
      T.ElemsAndThreads(skeleton);
    }

    lemma SubtreeOfInElems(node: TTNode?, sk: ttree<TTNode>)
      requires ValidRec(node, sk)
      requires Valid()
      requires node in elems(skeleton)
      ensures T.Subtree(sk, skeleton)
      ensures elemsAndThreads(sk) <= elemsAndThreads(skeleton)
    {
      SubtreeOfInElemsRoot(node, sk, root, skeleton);
    }

    ghost predicate RedBlackTree()
      reads this, elems(skeleton)
    {
      ModelB.RedBlackTreeRoot(TreeModelRec(skeleton))
    }

    method Insert(k: K, v: V) returns (isInserted: bool, it: ThreadedLinkedTreeIterator)
      modifies this, Repr()

      requires Valid()
      requires Threaded()
      requires SearchTree()
      requires RedBlackTree()

      ensures Valid()
      ensures Threaded()
      ensures SearchTree()
      ensures RedBlackTree()
      ensures Model() == ModelI.InsertRoot(old(Model()), k, v)
      ensures isInserted <==> ModelI.IsInserted(old(Model()), k)
      ensures fresh(it)
      ensures it.Parent() == this
      ensures it.Valid()
      ensures it.Model() == ModelIt.Link(k)

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Model() == old(it.Model())
        && it.HasPeek() == old(it.HasPeek())
    {
      ModelI.InsertRootSpec(TreeModelRec(skeleton), k, v);
      var insertedNode;
      root, skeleton, insertedNode, isInserted := InsertRoot(root, skeleton, k, v);

      ThreadedImp();
      it := new ThreadedLinkedTreeIterator.At(insertedNode, this);
    }

    method Remove(k: K) returns (isRemoved: bool)
      modifies this, Repr()

      requires Valid()
      requires Threaded()
      requires SearchTree()
      requires RedBlackTree()

      ensures Valid()
      ensures Threaded()
      ensures SearchTree()
      ensures RedBlackTree()
      ensures ModelR.RemoveRoot(old(Model()), k).Some?
      ensures Model() == ModelR.RemoveRoot(old(Model()), k).unwrap
      ensures isRemoved <==> ModelR.IsRemovedRoot(old(Model()), k)

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())

      ensures Iterators() >= old(Iterators())
      ensures forall it
          | it in old(Iterators())
          && old(it.Valid())
          && (old(it.HasPeek()) ==> old(it.Peek().0) != k) ::
        && it.Valid()
        //&& it.Parent() == old(it.Parent())  // obvious since it.parent is const
        && it.Model() == old(it.Model())
        && it.HasPeek() == old(it.HasPeek())
    {
      ModelR.RemoveRootSpec(TreeModelRec(skeleton), k);
      ghost var removedNode;
      root, skeleton, removedNode, isRemoved := R.RemoveRoot(root, skeleton, k);
      forall it <- old(Iterators()) | old(it.Valid()) && old(it.HasPeek())
        ensures old(it.Peek().0) == k <==> it.node == removedNode
      {
        KeysAndElems(skeleton);
      }
    }
  }

  method {:verify false} TestThreadedLinkedTree()
  {
    var t := new ThreadedLinkedTree();
    assert ModelB.toMap(t.Model()) == map[];

    ModelI.InsertRootModel(t.Model(), 1, 0);
    var _, _ := t.Insert(1, 0);
    assert ModelB.toMap(t.Model()) == map[1 := 0];

    ModelI.InsertRootModel(t.Model(), 3, 2);
    var _, _ := t.Insert(3, 2);
    assert ModelB.toMap(t.Model()) == map[1 := 0, 3 := 2];

    ModelI.InsertRootModel(t.Model(), 2, 1);
    var _, _ := t.Insert(2, 1);
    assert ModelB.toMap(t.Model()) == map[1 := 0, 3 := 2, 2 := 1];
  }

  method {:verify false} TestThreadedLinkedTreeIterator()
  {
    var t := new ThreadedLinkedTree();
    var _, _ := t.Insert(1, 0);
    var _, _ := t.Insert(3, 2);
    var _, _ := t.Insert(2, 1);
    print "\n";

    var it := t.First();
    assert it.Peek() == (1, 0);
    print it.node.key;
    print "\n";

    it.ValidImp();
    t.ThreadedImp();
    assume {:axiom} false;  // Dafny cannot verify anything below
    it.Next();
    assert it.Peek() == (2, 1);
    print it.node.key;
    print "\n";

    it.ValidImp();
    t.ThreadedImp();
    it.Next();
    assert it.Peek() == (3, 2);
    print it.node.key;
    print "\n";

    it.ValidImp();
    t.ThreadedImp();
    it.Next();
    assert !it.HasPeek();
  }
}