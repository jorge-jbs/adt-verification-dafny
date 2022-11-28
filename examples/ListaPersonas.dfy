include "../src/linear/layer2/ArrayList.dfy"
include "iterators/FillArray.dfy"

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

method Test(l:List<Person>,persons:array<Person>)
modifies l, l.Repr(),persons
requires allocated(l.Repr())
requires l.Valid()

requires {persons} !! {l}+l.Repr()
requires persons.Length == |l.Model()|

ensures l.Valid()
ensures persons[..] == l.Model()

{
  FillArray(l,persons);
  var clara := new Person(1,48,"Clara");
 // l.PushBack(clara);
 // var _ := l.PopBack();
}