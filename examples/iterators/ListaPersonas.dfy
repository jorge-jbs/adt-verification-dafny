include "../../src/linear/layer2/ArrayList.dfy"
include "../../examples/iterators/FillArray.dfy"
include "../../examples/iterators/DupElements.dfy"


class Person {
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
requires !l.Empty?()

requires {persons} !! {l}+l.Repr()
requires persons.Length == |l.Model()|

ensures l.Valid()
{
  FillArray(l,persons);
  var clara := new Person(1,48,"Clara");
  /*l.PushBack(clara);
  var _ := l.PopBack();*/
 
 assert forall i | 0<=i<|l.Model()| :: persons[i]==l.Model()[i];

 var it := l.First();
 it.Set(clara);
 assert forall i | 1<=i<|l.Model()| :: persons[i]==l.Model()[i];
 assert l.Model()[0]==clara;
 assert persons[0]==old(l.Model()[0]);
 
 DupElements(l);
 assert l.Model()[0]==l.Model()[1]==clara;

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
  var it := l.First();
  var b := it.HasPeek();
  var clara := new Person(1,48,"Clara");
  it := l.Erase(it);
  assert persons[0]==old(l.Model()[0]);
  assert !l.Empty?() ==> l.Model()[0]==old(l.Model()[1]);

  /*b := it.HasPeek();
  while b
  decreases |l.Model()| - it.Index()
  invariant fresh(l.Repr()-old(l.Repr()))
  invariant allocated(l.Repr())
 
 invariant persons[..] == old(l.Model())
  invariant l.Valid()
  invariant it.Valid()
  invariant it.Parent() == l
  invariant b == it.HasPeek?()
  {
   var x:Person := it.Peek();
   if (x==clara) {
      it := l.Erase(it);
      }
   else 
     {it.Next();} 
   b := it.HasPeek(); 
 
  } */
}