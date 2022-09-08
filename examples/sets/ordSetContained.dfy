include "../../src/Utils.dfy"
include "../../src/tree/layer1/OrderedSet.dfy"




method ordSetContained(s1:OrderedSet,s2:OrderedSet) returns (b:bool)
modifies s1, s1.Repr(), s2, s2.Repr()
requires s1.Valid() && s2.Valid()
requires forall x | x in s1.Repr() :: allocated(x)
requires forall x | x in s2.Repr() :: allocated(x)

requires ({s1} + s1.Repr()) !! ({s2}+s2.Repr())
ensures s1.Valid() && s2.Valid()
ensures s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
ensures b == (s1.Model() <= s2.Model())

ensures forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
ensures fresh(s1.Repr()-old(s1.Repr()))
ensures forall x | x in s1.Repr() :: allocated(x)

ensures forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
ensures fresh(s2.Repr()-old(s2.Repr()))
ensures forall x | x in s2.Repr() :: allocated(x)

ensures s1.Iterators()>=old(s1.Iterators()) && s2.Iterators()>=old(s2.Iterators())
{
 var it1:=s1.First(); var x1:int; var x2:int;
 assert it1.Traversed()=={};
 var it2:=s2.First(); b:=true;
 assert it1.Traversed()==it2.Traversed()=={};
 while (it1.HasNext() && it2.HasNext() && b)
  // decreases s1.Model()+s2.Model()-(it1.Traversed()+it2.Traversed()),b
   decreases s2.Model()-it2.Traversed(),b
   invariant s1.Valid() && s2.Valid() 
   invariant ({s1} + s1.Repr()) !! ({s2}+s2.Repr()) 
   invariant s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
   invariant it1.Valid() && it2.Valid() 
   invariant it1 in s1.Iterators() && it2 in s2.Iterators()
   invariant it1.Parent()==s1 && it2.Parent()==s2
   invariant it1.Traversed()<=s1.Model() && it2.Traversed()<=s2.Model()
   //invariant !it2.HasNext()==> b
   invariant b ==> it1.Traversed() <= it2.Traversed()
   invariant !b ==> !(it1.Traversed() <= s2.Model())
   invariant it1.HasNext() ==> it1.Peek() !in it2.Traversed()
   invariant forall u | u in it2.Traversed() && it1.Traversed()<s1.Model() :: u<it1.Peek()

   invariant forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
   invariant forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
   invariant forall x | x in s1.Repr() :: allocated(x)
   invariant forall x | x in s2.Repr() :: allocated(x)
   invariant s1.Iterators() >= old(s1.Iterators()) && s2.Iterators() >= old(s2.Iterators())

 { 
  if (it1.Peek()==it2.Peek())
  { 
        x1 := it1.Next(); x2:=it2.Next(); 
   
  }
  else if (it1.Peek()<it2.Peek())
   { 
      assert s2.Model()==it2.Traversed()+{it2.Peek()}+(s2.Model()-it2.Traversed()-{it2.Peek()});
      assert it1.Peek() !in it2.Traversed();
      assert forall z | z in s2.Model()-it2.Traversed()-{it2.Peek()} :: it1.Peek() < it2.Peek() < z;
     b:=false;  
     x1:=it1.Next();
    }
  else { 
    x2 := it2.Next();
    }
  
 }
  
  b:=b && !it1.HasNext();

}

