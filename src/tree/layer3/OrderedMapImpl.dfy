include "../../../src/tree/Tree.dfy"
include "../../../src/tree/SearchTree.dfy"
include "../../../src/tree/layer1/OrderedMap.dfy"

class OrderedMapImpl extends OrderedMap {
  var tree: SearchTree;
  //ghost var iters: set<OrderedMapIteratorImpl>;

  function Repr0(): set<object>
    reads this
  {
    {tree} // + iters
  }

  function Repr1(): set<object>
    reads this, Repr0()
  {
    Repr0() + {tree.tree}
  }

  function Repr2(): set<object>
    reads this, Repr1()
  {
    Repr1() + tree.tree.Repr()
  }

  function ReprDepth(): nat
    reads this
    ensures ReprDepth() > 0
  { 2 }

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= ReprDepth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)
  {
    if n == 0 then Repr0()
    else if n == 1 then Repr1()
    else Repr2()
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());

  predicate Valid()
    reads this, Repr()
  {
    tree.Valid()
    //&& (forall it | it in iters :: it.parent == this && {it} !! {this})
  }

  function Model(): map<K,V>
    reads this, Repr()
    requires Valid()
  {
    tree.tree.Model()
  }

  constructor()
    ensures Valid()
    ensures Model() == map[]
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() :: fresh(x)
    ensures fresh(Repr())
    ensures forall x | x in Repr() :: allocated(x)
  {
    tree := new SearchTree();
    new;
    assert Repr() == {tree} + {tree.tree} + tree.tree.Repr();
    assert fresh(tree.Repr());
    assert tree.Repr() == tree.tree.Repr();
    assert fresh(tree.tree.Repr());
    assert fresh(Repr());
  }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == map[]
  {
    tree.tree.isEmpty()
  }

 function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|
  {
    tree.tree.Size()
  }

 function Iterators(): set<UnorderedMapIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is OrderedMapIterator
  {
    {} //iters
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


    ensures it is OrderedMapIterator
    ensures fresh(it)
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed()=={}
    ensures Model()!=map[] ==> it.HasNext() && key(it.Peek())==elemth(Model().Keys,0)
    ensures Iterators() == {it} + old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))
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

    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures Model()!=map[] ==> it.HasNext() && it.Traversed()==Model().Keys-{elemth(Model().Keys,|Model().Keys|-1)} && key(it.Peek())==elemth(Model().Keys,|Model().Keys|-1)
    ensures Model()==map[] ==> it.Traversed()=={}
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

  method contains(k:K) returns (b:bool)
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)

    ensures Valid()
    ensures b==(k in Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
  {
    assert tree.tree.Repr() <= Repr();
    b := tree.Search(k);
  }

  method at(k:K) returns (v:V)
    //modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    requires k in Model()
    ensures Valid()
    //ensures Model()==old(Model())
    ensures v == Model()[k]

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
  {
    assert tree.tree.Repr() <= Repr();
    v := tree.Get(k);
  }


  method add(k: K, v: V)
    modifies this, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())[k := v]

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
  {
    tree.Insert(k, v);
  }

  method remove(k:int)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== map k' | k' in old(Model()) && k'!=k::old(Model())[k']

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
  {
    tree.Remove(k);
  }

  method find(k:K) returns (newt:UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()==old(Model())

    ensures newt is OrderedMapIterator
    ensures fresh(newt)
    ensures newt.Valid() && newt.Parent()==this
    ensures k in old(Model()) ==> newt.HasNext() && key(newt.Peek())==k
    ensures k !in old(Model()) ==> newt.Traversed()==Model().Keys

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt}+old(Iterators())

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
}