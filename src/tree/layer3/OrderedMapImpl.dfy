include "../../../src/MUtils.dfy"
include "../../../src/tree/layer4/Tree.dfy"
include "../../../src/tree/layer4/TNode.dfy"
include "../../../src/tree/layer4/LinkedTree.dfy"
include "../../../src/tree/layer4/LinkedTree/RBInsert.dfy"
include "../../../src/tree/layer4/LinkedTree/RBRemove.dfy"
include "../../../src/tree/layer1/OrderedMap.dfy"
include "../../../src/tree/layer4/RBTree/Base.dfy"

module OrderedMapImpl {
  import opened Utils
  import opened TNode
  import opened KeyValue
  import opened T = Tree
  import opened LinkedTree
  import opened LinkedTree.SInsert
  import opened LinkedTree.RBInsert
  import opened LinkedTree.RBRemove
  import RB = RBTree.Base

  trait UnorderedMapIterator {}
  trait OrderedMapIterator extends UnorderedMapIterator {}
  trait UnorderedMap {}
  trait OrderedMap extends UnorderedMap {}

  type pos = n: int | n > 0 witness 1

  class OrderedMapIteratorImpl extends OrderedMapIterator {
    var parent: OrderedMapImpl;
    var iter: LinkedTreeIterator;

    constructor First(parent: OrderedMapImpl)
      requires parent.Valid()
      ensures Valid()
      ensures Traversed() == {}

      requires allocated(parent.Repr())
      ensures allocated(parent.Repr())
    {
      this.parent := parent;
      this.iter := new LinkedTreeIterator.First(parent.tree);
      assume false;
    }

    function Parent(): OrderedMapImpl //UnorderedMap
      reads this
    {
      parent
    }

    predicate Valid()
      reads this, Parent(), Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()
    {
      && this in parent.iters
      && this in Parent().iters
      && iter.parent == parent.tree
      && parent.Valid()

      //&& BigUnion(set sk: tree<TNode> | sk in iter.stackSk :: elems(sk)) <= Parent().Repr()
      && (forall sk: tree<TNode> | sk in iter.stackSk :: elems(sk) <= elems(parent.tree.skeleton))
      && iter.Valid()
    }

    function Traversed(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures Traversed() <= (Parent().Model().Keys)
    {
      iter.TraversedInModel();
      set p | p in iter.traversed :: p.0
    }

    function Peek?():(K,V)
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()

      ensures Peek?() in Parent().Model().Items
              && key(Peek?()) !in Traversed()
              //key(Peek?()) in Parent().Model() &&
              //value(Peek?()) == Parent().Model()[key(Peek?())]

    predicate HasPeek?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures HasPeek?()  <==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
      //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
      ensures !HasPeek?() <==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|

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
      ensures Traversed() == old(Traversed())
      ensures HasPeek?() ==> Peek?()==old(Peek?())
      ensures b == HasPeek?()

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?()))

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

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures Traversed() == {key(old(Peek?()))}+old(Traversed())

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && (it != this ==> it.Traversed() == old(it.Traversed())
                           && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?())))

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

      ensures Traversed() == old(Traversed()) && Peek?()==old(Peek?())
      ensures p == Peek?()
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?()))

    method Copy() returns (it: OrderedMapIteratorImpl /*UnorderedMapIterator*/)
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures fresh(it)
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures Traversed() == old(Traversed())
      ensures HasPeek?() ==> Peek?()==old(Peek?())

      ensures it.Valid()
      ensures Parent().Iterators() >= {it} + old(Parent().Iterators())
      ensures Parent() == it.Parent()
      ensures Traversed() == it.Traversed() && (it.HasPeek?() ==> Peek?()==it.Peek?())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?()))
  }

  class OrderedMapImpl /*extends OrderedMap*/ {
    var tree: LinkedTree;
    ghost var iters: set<OrderedMapIteratorImpl>;
    var size: nat;

    ghost const ReprDepth: pos

    function Repr(): set<object>
      reads this, ReprFamily(ReprDepth-1)
    {
      ReprFamily(ReprDepth)
    }

    function Repr0(): set<object>
      reads this
    {
      {tree} + iters
    }

    function Repr1(): set<object>
      reads this, Repr0()
    {
      Repr0() + tree.Repr() + (set it | it in iters :: it.iter)
    }

    function ReprFamily(n: nat): set<object>
      decreases n
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads this, if n == 0 then {} else ReprFamily(n-1)
    {
      if n == 0 then Repr0()
      else Repr1()
    }

    lemma UselessLemma()
      ensures Repr() == ReprFamily(ReprDepth);

    predicate Valid()
      reads this, Repr()
    {
      && ReprDepth == 1
      && tree.Valid()
      && tree.SearchTree()
      && tree.RedBlackTree()
      && size == |tree.MapModel()|
      && (forall it | it in iters :: it.parent == this && {it} !! {this})
    }

    function Model(): map<K,V>
      reads this, Repr()
      requires Valid()
    {
      tree.MapModel()
    }

    constructor()
      ensures Valid()
      ensures Model() == map[]
      ensures fresh(Repr())
      ensures allocated(Repr())
    {
      tree := new LinkedTree();
      size := 0;
      iters := {};
      ReprDepth := 1;
    }

     predicate Empty?()
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

/*
      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
        (it is OrderedSetIterator &&
        (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index()))
        */
    {
      b := tree.root == null;
      if !b {
        assert !tree.TreeModel().Empty?;
        assert tree.MapModel().Keys == RB.keys(tree.TreeModel());
      }
    }

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

/*
      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
        (it is OrderedSetIterator &&
        (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index()))
        */
    {
      RB.SizeKeys(tree.TreeModel());
      calc == {
        RB.size(tree.TreeModel());
        |RB.keys(tree.TreeModel())|;
        { assert RB.keys(tree.TreeModel()) == tree.MapModel().Keys; }
        |tree.MapModel().Keys|;
        |tree.MapModel()|;
      }
      return size;
    }

   function Iterators(): set<OrderedMapIteratorImpl> // set<UnorderedMapIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
      ensures forall it | it in Iterators() :: it is OrderedMapIterator
    {
      iters
    }

    method First() returns (it: UnorderedMapIterator)
      modifies this, Repr()
      requires Valid()
      requires forall x | x in Repr() :: allocated(x)

      ensures Valid()
      ensures Model() == old(Model())

      ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
      ensures fresh(Repr()-old(Repr()))
      ensures forall x | x in Repr() :: allocated(x)

/*
      ensures it is OrderedMapIterator
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Traversed()=={}
      ensures Model()!=map[] ==> it.HasNext() && key(it.Peek())==elemth(Model().Keys,0)
      ensures Iterators() == {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))
        */
    /*
    {
      var  iter := new OrderedMapIteratorImpl(this);
      iters := iters+{iter};
      it := iter;
      assume false;
    }
    */

    method Last() returns (it: OrderedMapIterator)//iterator to the last element
      modifies this, Repr()
      requires Valid()
      requires forall x | x in Repr() :: allocated(x)
      ensures Valid()
      ensures Model() == old(Model())

      ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
      ensures fresh(Repr()-old(Repr()))
      ensures forall x | x in Repr() :: allocated(x)

/*
      ensures fresh(it)
      ensures Iterators() == {it} + old(Iterators())
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Model()!=map[] ==> it.HasNext() && it.Traversed()==Model().Keys-{elemth(Model().Keys,|Model().Keys|-1)} && key(it.Peek())==elemth(Model().Keys,|Model().Keys|-1)
      ensures Model()==map[] ==> it.Traversed()=={}
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))
        */

    method Contains(k: K) returns (b: bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures b == (k in Model())

  /*
      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && |it.Traversed()| == old(|it.Traversed()|)
        && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()):://NEW
        (it is OrderedSetIterator &&
        (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index()) )    {
        assert tree.tree.Repr() <= Repr();
        b := tree.Search(k);
      }
        */
    {
      var foundNode := tree.Find(k);
      return foundNode != null;
    }

    method Find(x: K) returns (newt: UnorderedMapIterator)
     modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

  /*
      ensures newt is OrderedSetIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent()==this
      ensures x in old(Model()) ==> newt.HasPeek?() && newt.Peek?() == x
      ensures x !in old(Model()) ==> newt.Traversed() == Model() && |newt.Traversed()| == |Model()|

      ensures x in old(Model()) ==> (newt as OrderedSetIterator).Index() == |smaller(Model(),x)| //NEW
      ensures x !in old(Model()) ==> (newt as OrderedSetIterator).Index() == |Model()|

      ensures Iterators() >= {newt}+old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && |it.Traversed()| == old(|it.Traversed()|)
        && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
        (it is OrderedSetIterator &&
        (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index()))
      */
      {
        //var foundNode := Find();
        assume false;
      }

    method At(k:K) returns (v:V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires k in Model()
      ensures Valid()
      ensures Model() == old(Model())
      ensures v == Model()[k]

/*
      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?()))
        */
    {
      var foundNode := tree.Find(k);
      return foundNode.value;
    }

    method {:verify false} Add(k: K, v: V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k:=v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|) else |Model()| == 1 + old(|Model()|)
  /*
      ensures Iterators() >= old(Iterators())
    */
    {
      var b := Contains(k);
      tree.RBInsert(k, v);
      if !b {
        size := size + 1;
      }
    }

    lemma MapDiffSize(m: map<K, V>, k: K)
      ensures k in m && m != map[] ==> |m - {k}| == |m| - 1
      ensures k !in m ==> |m - {k}| == |m|
    {
      assert forall p: map<K, V> :: |p| == |p.Keys|;
      /*
      if m == map[] {
        assert m - {k} == map[];
      } else if m.Keys == {k} {
        assert |m| == |m.Keys|;
        assert |m| == 1;
        assert m - {k} == map[];
      } else {
        var k' :| k' in m && k' != k;
        MapDiffSize(m - {k'}, k);
        assume false;
      }
      */
    }

    method {:verify false} Remove(k:K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      //ensures Model() == map k' | k' in old(Model()) && k' != k :: old(Model())[k']
      ensures Model() == old(Model()) - {k}

/*
      ensures Iterators() >= old(Iterators())
    */
    {
      MapDiffSize(tree.MapModel(), k);
      var b := Contains(k);
      tree.RBRemove(k);
      assert tree.MapModel() == old(tree.MapModel()) - {k};
      if b {
        size := size - 1;
      }
    }


/*
    method insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt:UnorderedMapIterator)
      modifies this, Repr()
      requires Valid()
      requires mid.Valid()
      requires mid.Parent() == this
      requires mid in Iterators()
      requires forall x | x in Repr() :: allocated(x)
      ensures Valid()
      ensures Model() == old(Model())[k := v]

      ensures newt is OrderedMapIterator
      ensures fresh(newt)
      ensures Iterators() == {newt}+old(Iterators())
      ensures newt.Valid() && newt.Parent()==this
      ensures newt.HasNext() && newt.Peek()==(k,v) && newt.Traversed()==smaller(Model().Keys,k)

      ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
      ensures fresh(Repr()-old(Repr()))
      ensures forall x | x in Repr() :: allocated(x)

      //points either to the inserted elemento or to the already existing one




    method erase(mid:UnorderedMapIterator) returns (next: UnorderedMapIterator)
      modifies this, Repr()
      requires Valid()
      requires mid.Valid()
      requires mid.Parent() == this
      requires mid.HasNext()
      requires mid in Iterators()
      requires forall x | x in Repr() :: allocated(x)
      ensures Valid()
      ensures Model()== map k | k in old(Model()) && k!=old(key(mid.Peek()))::old(Model())[k]

      ensures next is OrderedMapIterator
      ensures fresh(next)
      ensures Iterators() == {next}+old(Iterators())
      ensures next.Valid() && next.Parent()==this
      ensures next.Traversed()==old(mid.Traversed()) &&
                  (next.HasNext() ==> key(next.Peek())==elemth(Model().Keys,|next.Traversed()|) && value(next.Peek())==Model()[key(next.Peek())])


      ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
      ensures fresh(Repr()-old(Repr()))
      ensures forall x | x in Repr() :: allocated(x)
  */
  }
}