include "../../../src/linear/impl/ArrayList.dfy"


class ArrayListIteratorImpl extends ArrayListIterator {
  var parent: ArrayListImpl
  var node: nat;//el indice exterior--corresponde a (parent.c+node)%parent.list.Length

  predicate Valid()
    reads this, parent, parent.Repr()
  {
    && parent.Valid()
    && 0<=node<=parent.nelems
  }

  function Parent(): ArrayList
    reads this
  {
    parent
  }

  function Index(): nat
    reads this, parent, parent.Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Index() <= |Parent().Model()|
  {
    node
  }

  constructor(l: ArrayListImpl)
    requires l.Valid()
    ensures Valid()
    ensures parent == l
    ensures Index() == 0
  {
    parent := l;
    node := 0;
  }

  constructor CopyCtr(it: ArrayListIteratorImpl)
    requires it.Valid()
    ensures Valid()
    ensures parent == it.parent
    ensures node == it.node
  {
    parent := it.parent;
    node := it.node;
  }

  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() <==> Index() < |Parent().Model()|
  {
    node < parent.nelems
  }

  method Next() returns (x: int)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    requires allocated(Parent())
   //requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Index()) < Index()
    ensures old(Parent()) == Parent()
    ensures old(Index()) < |Parent().Model()|
    ensures old(Parent().Model()) == Parent().Model()
    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Index() == old(it.Index()))
    ensures forall x | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures forall x | x in Parent().Repr() :: allocated(x)
  {parent.modelIndex(parent.list,parent.c,parent.nelems);
    x := parent.list[(parent.c+node)%parent.list.Length];
    node := node+1;
  }

  function method Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() == Parent().Model()[Index()]
  { parent.modelIndex(parent.list,parent.c,parent.nelems);
    parent.list[(parent.c+node)%parent.list.Length]
  }

  method Copy() returns (it: ArrayListIterator)
    modifies Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures fresh(it)
    ensures Valid()
    ensures it.Valid()
    ensures Parent().Valid()
    ensures it in Parent().Iterators()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == old(Parent())
    ensures Parent() == it.Parent()
    ensures Index() == it.Index()
    ensures it.Valid()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
    ensures Parent().Model() == old(Parent().Model())
    ensures forall x | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures forall x | x in Parent().Repr() :: allocated(x)
  {
    it := new ArrayListIteratorImpl.CopyCtr(this);
    parent.iters := {it} + parent.iters;
  }
}
class ArrayListImpl extends ArrayList {
  var list: array<int>;
  var c: nat;
  var nelems: nat;
  var iters: set<ArrayListIteratorImpl>;

  function ReprDepth(): nat
    ensures ReprDepth() > 0
  {
    1
  }

  function Repr0(): set<object>
    reads this
  {
    {this, list}+iters
  }

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= ReprDepth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)
  {
    if n == 0 then
      Repr0()
    else
      ReprFamily(n-1)
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());
  {}

function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|
  {
     nelems
  }

  predicate Valid()
    reads this, Repr()
  {
    0 <= c < list.Length && 0 <= nelems <= list.Length
    && forall it | it in iters :: it.parent == this && {it} !! {this,list}

  }

  function Model(): seq<int> // Los elementos estan en [c..(c+nelems)%Length) circularmente
    reads this, Repr()
    requires Valid()
  {
    ModelAux(list,c,nelems)
  }

  function ModelAux(a:array<int>,c:nat,nelems:nat):seq<int>
    reads a
    requires 0 <= c < a.Length && 0 <= nelems <= a.Length
    ensures |ModelAux(a,c,nelems)|==nelems
  {
   
    if nelems == 0 then
      []
    else if c + nelems <= a.Length then
      a[c..c+nelems]
    else
      a[c..a.Length] + a[0..(c+nelems)%a.Length]
  }

lemma modelIndexAux(a:array<int>,c:nat,nelems:nat,k:nat)
    requires 0 <= c < a.Length && 0 <= nelems <= a.Length
    requires 0<=k<nelems
    ensures ModelAux(a,c,nelems)[k]==a[(c+k)%a.Length]
{ modulo(c+k,a.Length);
  assert c+k<a.Length ==> ModelAux(a,c,nelems)[k]==a[(c+k)];
  assume c+k>=a.Length ==> ModelAux(a,c,nelems)[k]==a[(c+k)%a.Length];
}

lemma modelIndex(a:array<int>,c:nat,nelems:nat)
    requires 0 <= c < a.Length && 0 <= nelems <= a.Length
    ensures forall k| 0<=k<nelems ::  ModelAux(a,c,nelems)[k]==a[(c+k)%a.Length]
{
forall k| 0<=k<nelems
  ensures ModelAux(a,c,nelems)[k]==a[(c+k)%a.Length]
  {modelIndexAux(a,c,nelems,k);}


}

  lemma incDeque(a:array<int>,c:nat,nelems:nat)
    requires 0<=c<a.Length &&0<nelems<=a.Length
    ensures ModelAux(a,c,nelems)==[a[c]]+ModelAux(a,(c+1)%a.Length,nelems-1)
  {
    if c + 1 < a.Length {
      assert ModelAux(a,c,nelems)==[a[c]]+ModelAux(a,(c+1),nelems-1);
      assert (c+1)%a.Length==c+1;
    }
  }

  lemma incEnque(a:array<int>,c:nat,nelems:nat)
    requires 0 <= c < a.Length && 0 <= nelems < a.Length
    ensures ModelAux(a, c, nelems+1) == ModelAux(a, c, nelems) + [a[(c+nelems)%a.Length]]
  {
    if c + nelems < a.Length { // consecutive nelems+1 elements [c..c+nelems]
      assert ModelAux(a, c, nelems+1)
        == ModelAux(a, c, nelems) + [a[(c+nelems)%a.Length]];
    } else { //elements [c..a.Length] followed by [0..(c+nelems+1)%a.Length]
      assert c+nelems+1 > a.Length && ((c+nelems+1)%a.Length)
        == (c+nelems) % a.Length+1;
      assert a[c..a.Length] + a[0..(c+nelems+1)%a.Length]
        == a[c..a.Length]+a[0..(c+nelems)%a.Length]+[a[(c+nelems)%a.Length]];
    }
  }


function Iterators(): set<ArrayListIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    {
      iters

     }

  method Begin() returns (it: ArrayListIterator)
    modifies this, Repr()
    requires Valid()
    requires forall it | it in Iterators() :: allocated(it)
    ensures Valid()
    ensures Model() == old(Model())
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Index() == 0
    ensures it.Parent() == this
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    {
      it:=new ArrayListIteratorImpl(this);
      iters:={it}+iters;

    }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    nelems == 0
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    list := new int[10];
    c:=0;
    nelems:=0;
    iters:={};
  }

 
  // Auxiliary method to duplicate space
  method grow()
    modifies Repr()
    requires Valid()
    requires forall it | it in iters ::allocated(it)
    ensures Valid()
    ensures nelems==old(nelems)
    ensures Model()==old(Model())
    ensures Iterators()==old(Iterators())
    ensures list.Length>old(list.Length)
    ensures c+nelems<list.Length
    ensures forall it | it in iters ::allocated(it)
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
  {
      ghost var oldList := ModelAux(list,c,nelems);
      ghost var oldIterators:=Iterators();
      var aux: array<int> := new int[2*list.Length+1];
      assert fresh(aux);
      assert forall it | it in iters ::{it}!!{this,list,aux}; 
      var i := 0;
      while i < nelems
        decreases nelems-i
        invariant 0 <= i <= nelems <= list.Length < aux.Length
        invariant nelems == old(nelems)
        invariant 0 <= c < list.Length == old(list.Length)
        invariant ModelAux(aux, 0, i) == ModelAux(list, c, i)
        invariant ModelAux(list, c, nelems) == oldList
        invariant forall it |it in iters ::allocated(it)
        invariant forall it | it in iters ::{it}!!{this,list,aux}
        invariant Valid() && Iterators()==oldIterators
      {
        aux[i] := list[(c+i)%list.Length];
        i := i+1;
        assert aux[i-1] == list[(c+i-1)%list.Length];
        incEnque(aux, 0, old(i));
        incEnque(list, c, i-1);
      }
      assert ModelAux(aux, 0, nelems) == ModelAux(list, c, nelems) == oldList;

      list := aux;
      c := 0;
     // assert Iterators()==oldIterators;
      
      
  }

  function method Back(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Back() == Model()[|Model()|-1]
    { 
      /*if (c+nelems)==0 then list[list.Length-1]
      else list[(c+nelems-1)%list.Length]*/
      assert (c+nelems)==0 ==> (c+nelems-1)%list.Length==list.Length-1;
      list[(c+nelems-1)%list.Length]
    }

  method PushBack(x: int)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
    ensures Iterators() == old(Iterators())
    //ensures forall it | it in Iterators() && old(it.Valid()) ::
    //  it.Valid() // && it.Index() == old(it.Index())
  {
    ghost var oldList := ModelAux(list,c,nelems);
    if nelems == list.Length {
      grow();
    }
    assert ModelAux(list, c, nelems) == oldList;
    
    list[(c+nelems)%list.Length] := x;

     
    modulo(c+nelems,list.Length);
    assert c+nelems<list.Length ==> (c+nelems)%list.Length==c+nelems;
    assert c+nelems<list.Length ==> list[c..c+nelems]== oldList;
    assert c+nelems>=list.Length ==> list[c..list.Length]+list[0..(c+nelems)%list.Length]==oldList;
     
   
    nelems := nelems + 1;

    incEnque(list, c, nelems-1);
  }


lemma modulo(a:int,b:int)
requires b!=0
ensures 0<=a<b ==> a/b==0 && a%b==a
{}
method PopBack() returns (x: int)
    modifies Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() 
                        && old(it.Valid()) && old(it.Index())<old(|Model()|-1)
                       :: it.Valid() && it.Index()==old(it.Index())
    

    { ghost var aux:set<ArrayListIteratorImpl>:=iters;
      x:=list[(c+nelems-1)%list.Length];
      nelems:=nelems-1;
    //assert c+nelems==0 ==> (c+nelems-1)%list.Length==list.Length-1;
    assert forall it | it in Iterators() &&old(it.Valid()) 
         && old(it.Index())<old(|Model()|-1):: it.Valid() && it.Index()==old(it.Index());
     
   

    
}


function method Front(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]
  {
    list[c]
  }
  method PushFront(x: int)
    modifies this, Repr()
    requires Valid()
    // requires forall x | x in Repr() :: allocated(x)
    requires forall x | x in Iterators() :: allocated(x)
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    
{
  ghost var oldList := ModelAux(list,c,nelems);
    if nelems == list.Length {
      grow();
    }
    assert ModelAux(list, c, nelems) == oldList;
    if (c==0) {c:=list.Length-1;}
    else {c:=c-1;}
    list[c]:= x;
    nelems := nelems + 1;
    //incEnque(list, c, nelems-1);
  

}

  method PopFront() returns (x: int)
    modifies Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
    ensures Iterators() == old(Iterators())

  {
    x := list[c];
    c := (c+1) % list.Length;
    nelems := nelems-1;
    incDeque(list, old(c), old(nelems));
    // assert ModelAux(list,old(c),f,old(nelems))==[list[old(c)]]+ModelAux(list,(old(c)+1)%list.Length,f,nelems);
  }

method Insert(mid: ArrayListIterator, x: int)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index())+1)
    ensures Iterators() == old(Iterators())
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
    
   
}
