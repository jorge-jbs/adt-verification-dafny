include "reordenando-la-cola.dfy"
include "../../../src/Stack/SinglyLinkedStackImpl.dfy"
include "../../../src/Queue/SinglyLinkedQueueImpl.dfy"
include "../../../src/Stack/ArrayStackImpl.dfy"
include "../../../src/Queue/ArrayQueueImpl.dfy"
include "../../../src/ArrayList/ArrayListImpl.dfy"

module QueueReorder{
  import opened Reorder
  import opened ArrayStackImpl
  import opened ArrayQueueImpl
  import opened ArrayListImpl
  import opened SinglyLinkedStackImpl
  import opened SinglyLinkedQueueImpl

method {:extern} Scan() returns (x: nat)

method ScanArray(n: nat) returns (v: array<int>)
  ensures v.Length == n
  ensures fresh(v)
{
  v := new int[n];
  var i := 0;
  while i < n
  {
    v[i] := Scan();
    i := i + 1;
  }
}

method {:verify true} Main()
  decreases *
{
  while true
    decreases *
  {
    var n := Scan();
    // assume n >= 0;
    if n == 0 {
      break;
    } else {
      var v := ScanArray(n);

      var neg := new SinglyLinkedStackImpl();
      var pos := new SinglyLinkedQueueImpl();

      //var neg := new ArrayStackImpl();
      //var pos := new ArrayQueueImpl();
      /*
      Ejemplo para ver que puedo crear un iterador en cualquier parte de la lista
      

      var l := new ArrayListImpl<int>();
      l.PushBack(3);
      l.PushFront(4);
      var it := l.First();
      assert it.Index() ==0;
      it.Next();
      assert |l.Model()|==2;
      */
     
      
       
       assert {v} !! {neg} + neg.Repr();
       assert {v} !! {pos} + pos.Repr();
       assert {pos} + pos.Repr() !! {neg} + neg.Repr();
       assert neg.Valid();
       assert neg.Empty?();
       assert pos.Valid();
       assert pos.Empty?();
       assume forall i | 0 <= i < v.Length - 1 :: Int.Abs(v[i]) <= Int.Abs(v[i+1]);
      
      Reorder.Reorder(neg, pos, v);
      var i := 0;
      while i < n
      {
        print v[i];
        if i != n-1 {
          print " ";
        }
        i := i + 1;
      }
      print "\n";
    }
  }
}

}