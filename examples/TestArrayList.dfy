include "../src/linear/layer2/ArrayList.dfy"


 method Test(l: ArrayList<int>)
  requires l.Valid() && l.Model() == []
  requires forall x | x in l.Repr() :: allocated(x)
  modifies l, l.Repr()
{
  l.PushBack(10);
  l.PushBack(20);
  l.PushBack(30);
  var model := [10, 20, 30];
  assert l.Model() == model;

  var it := l.First();
  assert it.Parent().Model()[it.Index()] == 10;
  var _ := l.PopFront();
  assert l.Model() == model[1..];
  assert  it.Parent().Model()[it.Index()] == 20;
  var _ := l.PopFront();
  assert l.Model() == model[2..];
  assert  it.Parent().Model()[it.Index()] == 30;
  it.Next();
  assert !it.HasPeek?();
  var _ := l.PopFront();
  // assert it.Valid();    // assertion violation
}


method Test2(l1: ArrayList<int>, l2: ArrayList<int>)
  requires l1.Valid() && l2.Valid()
  requires forall x | x in l1.Repr() :: allocated(x)
  requires forall x | x in l2.Repr() :: allocated(x)
  requires {l1} + l1.Repr() !! {l2} + l2.Repr()
  requires l1.Model() == [1, 2, 3] && l2.Model() == [4, 5, 6]
  modifies l1, l2, l1.Repr(), l2.Repr()
{
  var model2 := l2.Model();
  var it1 := l1.First();
  var it2 := l2.First();
  assert it1.Parent().Model()[it1.Index()] == 1 && it2.Parent().Model()[it2.Index()] == 4;
  it1.Next();
  assert it1.Parent().Model()[it1.Index()] == 2 && it2.Parent().Model()[it2.Index()] == 4;
  var _ := l2.PopFront();
  assert l2.Model() == model2[1..];
  assert it1.Parent().Model()[it1.Index()]== 2 && it2.Parent().Model()[it2.Index()] == 5;
}
