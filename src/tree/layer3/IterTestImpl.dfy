include "../layer1/KeyValue.dfy"


class UnorderedMapIterator {
  ghost var traversed: seq<pairKV>
  ghost var traversedKeys: seq<K>
  var parent: UnorderedMap
  var stack: seq<Tree>
  ghost var inorderParent: seq<pairKV>


  function Parent(): UnorderedMap
    reads this
  {
    parent
  }

  function InorderPArent(): seq<pairKV>
    reads this
  {
    inorderParent
  }

  function inorderStack(st: seq<Tree>): seq<pairKV> {
    if (|st| == 0) then 
      []
    else 
      var top: Tree := st[|st| - 1];
      match (top) {
        case Empty => inorderStack(st[0..|st| - 1])
        case Node(_, k, v, r) => [(k, v)] + inorder(r) + inorderStack(st[0..|st| - 1])
      }
  }

  predicate ValidStack()
    reads this`stack
  {
    forall i | 0 <= i < |stack| :: stack[i].Node?
  }

  predicate ValidInorderParent()
    requires parent.Valid()
    reads this`inorderParent, this`parent, this.parent.Repr()
  {
    (forall i, j | 0 <= i < j < |inorderParent| :: inorderParent[i].0 != inorderParent[j].0)
    && (forall p | p in inorderParent :: p in parent.Model().Items)
    && (forall p | p in parent.Model().Items :: p in inorderParent)
  }

  predicate ValidTraversedKeys()
    reads this`traversedKeys, this`traversed, this`inorderParent
  {
    |traversedKeys| == |traversed| <= |inorderParent|
    && (forall i | 0 <= i < |traversedKeys| :: traversed[i].0 == traversedKeys[i])
  }

  predicate Valid()
    reads this, Parent(), Parent().Repr()
  {
    parent.Valid()
    && inorderParent == inorder(parent.tree)
    && ValidStack()
    && ValidInorderParent()
    && ValidTraversedKeys()
    && traversed + inorderStack(stack) == inorderParent
  }

  lemma TraversedAreKeys()
    requires Valid()
    ensures forall i | 0 <= i < |traversedKeys| :: traversedKeys[i] in Parent().Model().Keys
  {
    assert traversed == inorderParent[..|traversed|];
    forall i | 0 <= i < |traversedKeys|
      ensures traversedKeys[i] in Parent().Model().Keys
    {
      InorderAndModel(parent.tree, i);
    }
  }

  function Traversed(): set<K>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed() <= (Parent().Model().Keys)
  {
    TraversedAreKeys();
    set x: K | x in traversedKeys
  }

  lemma SetsLower(xs: set<K>, ys: set<K>)
    requires xs < ys
    ensures |xs| < |ys|
  {
    if (|xs| == 0 ) {

    } else {
      var x :| x in xs;
      SetsLower(xs - {x}, ys - {x});
    }
  }

  
  lemma NonemptyStackImpliesPending()
    requires Valid()
    ensures |stack| > 0 ==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
  {
    if (|stack| > 0) {
      assert |inorderStack(stack)| > 0;
      assert traversed + inorderStack(stack) == inorderParent;
      var lastPair := inorderParent[|inorderParent| - 1];
      forall i | 0 <= i < |traversedKeys| 
        ensures traversedKeys[i] != lastPair.0;
      {
        assert traversedKeys[i] == inorderParent[i].0;      
      }
      assert lastPair.0 !in traversedKeys;
      InorderAndModel(parent.tree, |inorderParent| - 1);
      SetsLower(Traversed(), Parent().Model().Keys);
    }
  }

  lemma PendingImpliesNonemptyStack()
    requires Valid()
    ensures Traversed() < Parent().Model().Keys ==> |stack| > 0
  {
    if (Traversed() < Parent().Model().Keys) {
      var k :| k in Parent().Model().Keys && k !in Traversed();
      ghost var i := InorderAndModelInverse(parent.tree, k);
      assert inorderParent[i].0 == k;
    }
  }


  method descendAndPush(t: Tree)
    modifies this`stack
    requires ValidStack()
    requires traversed + inorder(t) + inorderStack(stack) == inorderParent
    ensures ValidStack()
    ensures traversed + inorderStack(stack) == inorderParent
  {
    var t' := t;
    while (t'.Node?)
      decreases t'
      invariant traversed + inorder(t') + inorderStack(stack) == inorderParent
      invariant ValidStack()
    {
      stack := stack + [t'];
      t' := t'.left;
    }
  }



  constructor (parent: UnorderedMap)
    requires parent.Valid()
    ensures Valid()
    ensures Traversed() == {}
    ensures Parent() == parent
  {
    assert isBST(parent.tree);
    this.parent := parent;
    this.traversed := [];
    this.traversedKeys := [];
    this.stack := [];
    this.inorderParent := inorder(parent.tree);
    new;
    descendAndPush(parent.tree);
    assert traversed + inorderStack(stack) == inorderParent;
    assert ValidInorderParent() by {
      assert isBST(parent.tree);
      assert forall i, j | 0 <= i < j < |inorder(parent.tree)| :: inorder(parent.tree)[i].0 != inorder(parent.tree)[j].0 by {
        forall i, j | 0 <= i < j < |inorder(parent.tree)| 
        ensures inorder(parent.tree)[i].0 != inorder(parent.tree)[j].0
        { 
          AllKeysDifferentInBST(parent.tree, i, j);
        }
      }
      
      assert (forall p | p in inorderParent :: p in parent.Model().Items) by {
        forall p | p in inorderParent
          ensures p in parent.Model().Items
        {
          ghost var i := SearchInList(inorderParent, p);
          InorderAndModel(parent.tree, i);
        }
      }
      assert (forall p | p in parent.Model().Items :: p in inorderParent) by {
        forall p | p in parent.Model().Items
          ensures p in inorderParent
        {
          assert p.0 in parent.Model();
          ghost var i := InorderAndModelInverse(parent.tree, p.0);
          assert inorderParent[i] == (p.0, p.1);
        }
      }
    }
    assert Valid();
  }



  function method Peek(): pairKV 
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model().Items &&
            key(Peek()) !in Traversed() &&
            // key(Peek()) in Parent().Model() && 
            value(Peek()) == Parent().Model()[key(Peek())]
  {
    var pair := (stack[|stack| - 1].k, stack[|stack| - 1].v);
    assert pair in inorderStack(stack);
    assert inorderParent[|traversed|..] == inorderStack(stack);
    pair
  }

  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext()  <==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasNext() ==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|
  { NonemptyStackImpliesPending(); PendingImpliesNonemptyStack(); |stack| > 0 }
  
  method Next() returns (p: pairKV)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())

    ensures p == old(Peek()) && Traversed() == old(Traversed()) + { old(key(Peek())) }

    // TODO: ¿Por qué esto es necesario?      
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
       it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek() == old(it.Peek())))
  {
    assert ValidInorderParent();
    modify this`stack, this`traversed, this`traversedKeys {
      assert |stack| > 0;
      var top := stack[|stack| - 1];
      assert top.Node?;
      p := (top.k, top.v);


      calc {
          traversed + inorderStack(stack) == inorderParent;
        ==>
          traversed + inorderStack(stack[..|stack| - 1] + [top]) == inorderParent;
        ==>
          traversed + ([p] + inorder(top.right) + inorderStack(stack[..|stack| - 1])) == inorderParent;
        ==>
          (traversed + [p]) + inorder(top.right) + inorderStack(stack[..|stack| - 1]) == inorderParent;
      }

      stack := stack[..|stack| - 1];
      traversed := traversed + [p];
      traversedKeys := traversedKeys + [top.k];

      assert traversed + inorder(top.right) + inorderStack(stack) == inorderParent;
      descendAndPush(top.right);

      assert traversed + inorderStack(stack) == inorderParent;
    }
    assert ValidInorderParent();
    assert Valid();
  }

  method Copy() returns (it: UnorderedMapIterator)
    modifies Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures fresh(it)
    ensures Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Valid()
    ensures Parent().Model() == old(Parent().Model())

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)
    
    ensures it.Valid()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Traversed() == it.Traversed() && (it.HasNext() ==> Peek() == it.Peek())

    // TODO: ¿Por qué esto es necesario?            
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
         it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek() == old(it.Peek()))

}

datatype Tree = Empty | Node(left: Tree, k: K, v: V, right: Tree)

function inorder(t: Tree): seq<pairKV>
{
    match (t) {
        case Empty => []
        case Node(l, k, v, r) => inorder(l) + [(k, v)] + inorder(r)
    }
}

function mapModel(t: Tree): map<K, V>
{
    match (t) {
        case Empty => map []
        case Node(l, k, v, r) => mapModel(l) + map [k := v] + mapModel(r)
    }
}

function keysOf(t: Tree): set<K>
{
  match t {
    case Empty => {} 
    case Node(l, k, v, r) => keysOf(l) + {k} + keysOf(r)
  }
}

predicate isBST(t: Tree)
{
  match t {
    case Empty => true
    case Node(l, k, _, r) => 
      isBST(l) 
      && isBST(r)
      && (forall k' | k' in keysOf(l) :: k' < k)
      && (forall k' | k' in keysOf(r) :: k < k')
  }
}


lemma InorderContainsKeys(t: Tree)
  ensures (set p | p in inorder(t) :: p.0) == keysOf(t)
{ }


lemma AllKeysDifferentInBST(t: Tree, i: nat, j: nat)
  requires isBST(t)
  requires 0 <= i < j < |inorder(t)|
  ensures inorder(t)[i].0 != inorder(t)[j].0
{
  match t {
    case Empty => { }
    case Node(l, k, v, r) => {
      assert inorder(t) == inorder(l) + [(k, v)] + inorder(r);
      if (j < |inorder(l)|) {
        assert inorder(t)[i].0 == inorder(l)[i].0 != inorder(l)[j].0 == inorder(t)[j].0;
      } else if (j == |inorder(l)|) {
        assert inorder(t)[j] == (k, v);
        InorderContainsKeys(l);
        assert inorder(t)[i].0 in keysOf(l);
        assert inorder(t)[i].0 < inorder(t)[j].0;
      } else if (i == |inorder(l)|) {
        assert inorder(t)[i] == (k, v);
        InorderContainsKeys(r);
        assert inorder(t)[j].0 in keysOf(r);
        assert inorder(t)[i].0 < inorder(t)[j].0;
      } else if (i > |inorder(l)|) {
        AllKeysDifferentInBST(r, i - |inorder(l) + [(k, v)]|, j -  |inorder(l) + [(k, v)]|);
      } else {
        assert (i < |inorder(l)| && j > |inorder(l)|);
        InorderContainsKeys(l);
        InorderContainsKeys(r);
        assert inorder(t)[i].0 in keysOf(l);
        assert inorder(t)[j].0 in keysOf(r);
      }
    }
  }
}


lemma InorderAndModel(t: Tree, i: nat)
  requires 0 <= i < |inorder(t)|
  requires isBST(t)
  ensures inorder(t)[i].0 in mapModel(t) && mapModel(t)[inorder(t)[i].0] == inorder(t)[i].1
{  
  assert t.Node?;
  assert inorder(t) == inorder(t.left) + [(t.k, t.v)] + inorder(t.right);
  assert mapModel(t) == mapModel(t.left) + map [t.k := t.v] + mapModel(t.right);

  if (i < |inorder(t.left)|) {
    InorderAndModel(t.left, i);
    assert inorder(t.left)[i].0 in mapModel(t.left);
    assert inorder(t.left)[i].0 !in mapModel(t.right) by {
      if (inorder(t.left)[i].0 in mapModel(t.right)) {
        var pos := InorderAndModelInverse(t.right, inorder(t.left)[i].0);
        assert inorder(t.right)[pos].0 == inorder(t.left)[i].0;
        assert inorder(t)[|inorder(t.left) + [(t.k, t.v)]| + pos].0 == inorder(t)[i].0;
        assert 0 <= i < |inorder(t.left) + [(t.k, t.v)]| + pos < |inorder(t)|;
        AllKeysDifferentInBST(t, i, |inorder(t.left) + [(t.k, t.v)]| + pos);
      }
    }
    assert inorder(t.left)[i].0 != t.k by {
      AllKeysDifferentInBST(t, i, |inorder(t.left)|);
    }
  } else if (i == |inorder(t.left)|) {
    assert t.k !in mapModel(t.right) by {
      if (t.k in mapModel(t.right)) {
        var pos := InorderAndModelInverse(t.right, t.k);
        assert inorder(t.right)[pos].0 == t.k;
        assert inorder(t)[|inorder(t.left) + [(t.k, t.v)]| + pos].0 == inorder(t)[i].0;
        assert 0 <= i < |inorder(t.left) + [(t.k, t.v)]| + pos < |inorder(t)|;
        AllKeysDifferentInBST(t, i, |inorder(t.left) + [(t.k, t.v)]| + pos);
      }
    }
  } else {
    InorderAndModel(t.right, i - |inorder(t.left) + [(t.k, t.v)]|);
  }
}


lemma InorderAndModelInverse(t: Tree, k: K) returns (pos: nat)
  requires k in mapModel(t)
  ensures 0 <= pos < |inorder(t)| && inorder(t)[pos] == (k, mapModel(t)[k])
{
  assert t.Node?;
  assert mapModel(t) == mapModel(t.left) + map [t.k := t.v] + mapModel(t.right);
  assert inorder(t) == inorder(t.left) + [(t.k, t.v)] + inorder(t.right);

  if (k in mapModel(t.right)) {
    var pr := InorderAndModelInverse(t.right, k);
    pos := |inorder(t.left) + [(t.k, t.v)]| + pr;
  } else if (k == t.k) {
    pos := |inorder(t.left)|;
  } else {
    var pr := InorderAndModelInverse(t.left, k);
    pos := pr;
  }
}

lemma SearchInList(l: seq<pairKV>, p: pairKV) returns (i: nat)
  requires p in l
  ensures 0 <= i < |l| && l[i] == p
{
  if (l[|l|-1] == p) {
    i := |l| - 1;
  } else {
    assert p in l[..|l|-1];
    i := SearchInList(l[..|l|-1], p);
  }
}
  

class UnorderedMap {
  var tree: Tree
  ghost var iterators: set<UnorderedMapIterator>
   
  

  function Repr(): set<object>
    reads this
  {
    {this} + this.iterators
  }

  predicate Valid()
    reads this, Repr()
  {
    isBST(tree)
    && forall it | it in iterators :: it.Parent() == this && {it} !! {this}
  }

  function Model(): map<K,V>
    reads this, Repr()
    requires Valid()
  {
    mapModel(tree)        
  }

  
  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == map[]
  
  function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|

  function Iterators(): set<UnorderedMapIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
  { iterators }

/*
  method AddToIterators(it: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires it.Valid() && it.Parent() == this && {it} !! {this}
    ensures Valid()
    ensures it.Valid() && it.Parent() == this
    ensures Iterators() == old(Iterators()) + {it} && {it} !! {this}
    ensures it.Traversed() == old(it.Traversed())
    ensures forall it' | it' in old(Iterators()) && old(it'.Valid()) && it' != it ::
      it'.Valid() && 
      (it'.HasNext() <==> old(it'.HasNext())) && it'.Traversed() == old(it'.Traversed()) && (it'.HasNext() ==> it'.Peek()==old(it'.Peek()))
    ensures Model() == old(Model())
  {
    iterators := iterators + {it};
  }
  */

  method First() returns (it: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed() == {} 
    // TODO: ¿Por qué es necesario esto?
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))
    {
      it := new UnorderedMapIterator(this);
      iterators := iterators + { it };
    }

  method contains(k: K) returns (b: bool)
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures b == (k in Model()) 
  
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())


  method at(k: K) returns (v: V)
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    requires k in Model()
    ensures Valid()
    ensures v == Model()[k] 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())

  method add(k: K,v: V)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())[k := v] 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())

  // TODO: erase o remove? Uniformizar!
  method remove(k: int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) - {k}

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())

  method find(k: K) returns (newt: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model() == old(Model())
    
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent() == this
    ensures k in old(Model()) ==> newt.HasNext() && key(newt.Peek()) == k
    ensures k !in old(Model()) ==> newt.Traversed() == Model().Keys // TODO: ¿No sería mejor !newt.HasNext()?

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt} + old(Iterators())

  method insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())[k := v]

    ensures fresh(newt)
    ensures Iterators() == {newt} + old(Iterators())
    ensures newt.Valid() && newt.Parent()==this  
    ensures newt.HasNext() && newt.Peek()==(k,v)

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
    ensures Model() == map k | k in old(Model()) && k != old(key(mid.Peek())) :: old(Model())[k]
    ensures |Model()| == |old(Model())|-1

    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent() == this 
    ensures next.Traversed() == old(mid.Traversed()) 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
 
}

