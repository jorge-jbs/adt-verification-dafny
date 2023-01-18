 include "../../../src/ADT.dfy"


trait UnorderedSetIterator<A> {
  function Parent(): UnorderedSet<A>
    reads this

  predicate Valid()
    reads this, Parent(), Parent().Repr()
    ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

  function Traversed():set<A>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed() <= Parent().Model()

  function Peek?():A
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    requires HasPeek?()
    ensures Peek?() in Parent().Model() && Peek?() !in Traversed()
  
  predicate HasPeek?()
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasPeek?()  <==> Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasPeek?() ==> Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
  
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
    ensures Traversed() == {old(Peek?())}+old(Traversed()) 
    
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && (it != this ==> it.Traversed() == old(it.Traversed())
                         && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?())))

  method Peek() returns (p:A) 
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

    ensures Traversed() == old(Traversed()) && Peek?()==old(Peek?()) // no debería ser necesario pero lo es 
    ensures p == Peek?()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Traversed() == old(it.Traversed())
      && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?()))

  method Copy() returns (it: UnorderedSetIterator<A>)
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

trait UnorderedSet<A(==)> extends ADT<set<A>> {

  predicate Empty?()
    reads this, Repr()
    requires Valid()
  {
    Model() == {}
  }

  method Empty() returns (b: bool)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures b == Empty?()

    ensures Iterators() >= old(Iterators())

  method Size() returns (s: nat)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s == |Model()|

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Traversed() == old(it.Traversed()) 
      && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?()))


  function Iterators(): set<UnorderedSetIterator<A>>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

  method First() returns (it: UnorderedSetIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())

    ensures fresh(it)
    ensures Iterators() >= {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed()=={} 
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Traversed() == old(it.Traversed()) 
      && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?()))

  method Contains(x:A) returns (b:bool)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures b == (x in Model())

    ensures Iterators() >= old(Iterators())


  method Add(x:A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + {x} 

    ensures Iterators() >= old(Iterators())

  method Remove(x:A) 
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model()== old(Model()) - {x} 

    ensures Iterators() >= old(Iterators())

  method Find(x:A) returns (newt:UnorderedSetIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model()==old(Model())
    
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent() == this
    ensures x in old(Model()) ==> newt.HasPeek?() && newt.Peek?() == x //DUDA: newt.Traversed()
    ensures x !in old(Model()) ==> newt.Traversed() == Model()

    ensures Iterators() >= {newt}+old(Iterators())

  method Insert(mid: UnorderedSetIterator<A>, x: A) returns (newt:UnorderedSetIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + {x}

    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()

    ensures fresh(newt)
    ensures newt.Valid() && newt.Parent()==this  
    ensures newt.HasPeek?() && newt.Peek?()==x  //DUDA: newt.Traversed()
    ensures Iterators() >= {newt}+old(Iterators())
     //points either to the inserted elemento or to the already existing one
 



  method Erase(mid:UnorderedSetIterator<A>) returns (next: UnorderedSetIterator<A>)
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
    ensures Model()== old(Model())-{old(mid.Peek?())}
    
    ensures fresh(next)
    ensures next.Valid() && next.Parent() == this 
    ensures next.Traversed() == old(mid.Traversed()) //DUDA
    ensures Iterators() >= {next}+old(Iterators())

}

method {:verify true} main(s:UnorderedSet<int>)
  modifies s, s.Repr()
  requires allocated(s.Repr())
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures allocated(s.Repr())

  requires s.Valid() && s.Empty?()
  ensures s.Valid()
{
 assert s.Model()=={};
 s.Add(2); s.Add(4); s.Add(6);
 assert s.Model()=={2,4,6};
 var it := s.First();
 assert it.Traversed()=={};
 //assert it.Peek()==4; //Falla, se sabe cual es traversed pero no Peek
 var cont:=0; 
 var b := it.HasPeek();
  while (b)
     decreases |s.Model()|-|it.Traversed()|
     invariant it.Valid() && it.Parent()==s  
     invariant s.Valid()
     invariant fresh(s.Repr()-old(s.Repr()))
     invariant allocated(s.Repr())
     invariant b == it.HasPeek?()    
    {
     var aux := it.Peek();
     if (aux%2==0) {cont:=cont+1;} 
     it.Next();
     b := it.HasPeek();
    } 
  assert !it.HasPeek?();  
  assert it.Traversed()==s.Model();  
}

method {:verify true} otry(s:UnorderedSet<int>)
  modifies s, s.Repr()
  requires allocated(s.Repr())
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures allocated(s.Repr())

  requires s.Valid() && s.Empty?()
  ensures s.Valid()
{
   s.Add(3);
   s.Add(4);
   assert 3 in s.Model();
   assert 4 in s.Model();
   assert s.Model() == {3,4};
   s.Add(4);
   assert s.Model() == {3,4};
   s.Remove(2);
   assert s.Model() == {3,4};
   s.Remove(3);
   assert s.Model() == {4};
   s.Remove(4);
   assert s.Model() == {};
   s.Add(2); s.Add(7); s.Add(0); s.Add(1);s.Add(10);

 var b := s.Contains(10);
 assert b;

  /* var s1:set<int>;
   var s2:set<int>;
   s1:={1,2,4};
   s2:={0,1,2,3,4,8};
   assert s1<=s2;
   assert |s1|<=|s2|;*/


  //var 
  var it2:=s.First();
  it2:=s.Find(2);
  assert it2.Peek?()==2 && it2.Peek?()!=3;


  //var x:=it2.Next();
  it2:=s.Erase(it2);
  
  it2:=s.Insert(it2,3);
  assert it2.Peek?()==3 && it2.Peek?()!=2;

 
  var it3:=s.Find(7);
  it3:=s.Insert(it3,5);
  assert it3.Peek?()==5;
  it3:=s.Insert(it3,12);
  assert it3.Peek?()==12;
  it3.Next();
  assert 12 in it3.Traversed();
   
}