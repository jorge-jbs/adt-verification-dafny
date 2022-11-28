include "../src/linear/layer2/ArrayList.dfy"
include "iterators/FillArray.dfy"
include "iterators/DupElements.dfy"


class Person{
  var id:nat;
  var age:nat;
  var name:string;

  constructor(i:nat,a:nat,n:string)
  {
    id:=i;
    age:=a;
    name:=n;
  }
  method changeName(n:string)
  modifies this
  {
   name:=n;

  }
}

method Test(l:LinkedList<Person>,persons:array<Person>)
modifies l, l.Repr(),persons
requires allocated(l.Repr())
requires l.Valid()

requires {persons} !! {l}+l.Repr()
requires persons.Length == |l.Model()|

ensures l.Valid()
ensures Dup(persons[..]) == l.Model()

{
  FillArray(l,persons);
  var clara := new Person(1,48,"Clara");
 // l.PushBack(clara);
 // var _ := l.PopBack();
 DupElements(l);
}

method Test2(l:List<Person>,persons:array<Person>)
modifies l, l.Repr(),persons
requires allocated(l.Repr())
requires l.Valid()
requires !l.Empty?()

requires {persons} !! {l}+l.Repr()
requires persons.Length == |l.Model()|

ensures l.Valid()
ensures persons[..] == old(l.Model())
ensures l.Model() == old(l.Model()[1..])

{
  FillArray(l,persons);
  assert persons[..] == old(l.Model()); 
  var it := l.Begin();
  var b := it.HasNext();
  var clara := new Person(1,48,"Clara");
  it := l.Erase(it);
  assert persons[0]==old(l.Model()[0]);
  assert !l.Empty?() ==> l.Model()[0]==old(l.Model()[1]);


  /*while b
  decreases |l.Model()| - it.Index()
  invariant fresh(l.Repr()-old(l.Repr()))
  invariant allocated(l.Repr())
 
 invariant persons[..] == old(l.Model())
  invariant l.Valid()
  invariant it.Valid()
  invariant it.Parent() == l
  invariant b == it.HasNext?()
  {
   var x:Person := it.Peek();
   //x := it.Next();
   if (x==clara) {
      it := l.Erase(it);
      }
   else 
     {x := it.Next();} 
   b := it.HasNext(); 
 
  } */
}