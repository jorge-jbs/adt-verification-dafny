include "../Stack/StackSpec.dfy"
include "QueueSpec.dfy"
include "../Stack/SinglyLinkedStackImpl.dfy"
include "../Collections/Int.dfy"
include "../Collections/Seq.dfy"


module QueueImpl2Stack{
   import opened QueueSpec
   import opened StackSpec
   import opened SinglyLinkedStackImpl
   import opened Int
   import opened Seq
   export provides QueueSpec, StackSpec, SinglyLinkedStackImpl, Int, Seq
          reveals QueueImpl2Stack
          provides QueueImpl2Stack.Model, QueueImpl2Stack.Valid, QueueImpl2Stack.ReprFamily
          provides QueueImpl2Stack.Empty, QueueImpl2Stack.Size
          provides QueueImpl2Stack.Front, QueueImpl2Stack.Enqueue, QueueImpl2Stack.Dequeue

class QueueImpl2Stack<A> extends Queue<A> {
  var inbox: Stack<A>
  var outbox: Stack<A>

  ghost function ReprFamily(n: nat): set<object>
    decreases n
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)
  //*
  {
    if n == 0 then
      {inbox, outbox}
    else if n <= inbox.ReprDepth + 1 && n <= outbox.ReprDepth + 1 then
      {inbox, outbox} + inbox.ReprFamily(n-1) + outbox.ReprFamily(n-1)
    else if n > inbox.ReprDepth + 1 && n <= outbox.ReprDepth + 1 then
      {inbox, outbox} + inbox.Repr() + outbox.ReprFamily(n-1)
    else if n <= inbox.ReprDepth + 1 && n > outbox.ReprDepth + 1 then
      {inbox, outbox} + inbox.ReprFamily(n-1) + outbox.Repr()
    else
      {inbox, outbox} + inbox.Repr() + outbox.Repr()
  }

  ghost predicate Valid()
    reads this, Repr()
  {
    && ReprDepth == Max(inbox.ReprDepth, outbox.ReprDepth) + 1
    && assert ReprFamily(0) <= ReprFamily(ReprDepth); true
    && {inbox} + inbox.Repr() !! {outbox} + outbox.Repr()
    && this !in {inbox} + inbox.Repr()
    && this !in {outbox} + outbox.Repr()
    && inbox.Valid()
    && outbox.Valid()
  }

  ghost function Model(): seq<A>
    reads this, Repr()
    requires Valid()
  {
    outbox.Model() + Seq.Rev(inbox.Model())
  }

  constructor ()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
    ensures allocated(Repr())
  {
    var inbox := new SinglyLinkedStackImpl();
    var outbox := new SinglyLinkedStackImpl();
    var maxDepth := MMax(inbox.ReprDepth, outbox.ReprDepth);
    ReprDepth := maxDepth + 1;
    this.inbox := inbox;
    this.outbox := outbox;
    new;
    assert Repr() == {inbox, outbox} + inbox.Repr() + outbox.Repr();
  }

  lemma notEmpty()
    requires Valid()
    ensures Empty?() <==> inbox.Empty?() && outbox.Empty?()
  { 
    assert Model() == [] <==> outbox.Model() == [] && inbox.Model() == [];
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
  {
    var binbox := inbox.Empty();
    var boutbox := outbox.Empty();
    b := binbox && boutbox;
  }

  method Size() returns (s: nat)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s==|Model()| 
  { var isize := inbox.Size();
    var osize := outbox.Size();
    s := isize + osize;
  }

  method Transfer()
    modifies Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !inbox.Empty?()
    requires outbox.Empty?()
    ensures Valid()
    ensures inbox.Empty?()
    ensures outbox.Model() == Seq.Rev(old(inbox.Model()))
    ensures Model() == old(Model())
  { var b := inbox.Empty();
    while !b
      decreases |inbox.Model()|
      invariant allocated(Repr())
      invariant fresh(Repr()-old(Repr()))
      invariant Valid()
      invariant b == inbox.Empty?()
      invariant Seq.Rev(inbox.Model()) + outbox.Model() == Seq.Rev(old(inbox.Model()))

    { 
      label bodyLoop :
      
      var x := inbox.Pop();
      outbox.Push(x);
      
      assert outbox.Model() == [x] + old@bodyLoop(outbox.Model());

      b := inbox.Empty();
     
      calc {
        Seq.Rev(inbox.Model()) + outbox.Model();
        {assert outbox.Model() == [x] + old@bodyLoop(outbox.Model());} 
        Seq.Rev(inbox.Model()) + ([x] + old@bodyLoop(outbox.Model()));
        (Seq.Rev(inbox.Model()) + [x]) + old@bodyLoop(outbox.Model());
        Seq.Rev([x] + inbox.Model()) + old@bodyLoop(outbox.Model());
        Seq.Rev(old@bodyLoop(inbox.Model())) + old@bodyLoop(outbox.Model());
        Seq.Rev(old(inbox.Model()));
        
      }     
    }
    assert outbox.Model() == Seq.Rev(old(inbox.Model()));
    assert Model() == old(Model());
  }

  method Front() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]
  { 
    notEmpty();
    assert !inbox.Empty?() || !outbox.Empty?();
    
    var b := outbox.Empty();
    if b 
    {
      Transfer();
    }
    x := outbox.Top();
  }

  method Enqueue(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
  {
    inbox.Push(x);
    calc == {
      Model();
      outbox.Model() + Seq.Rev(inbox.Model());
      outbox.Model() + Seq.Rev([x] + old(inbox.Model()));
      outbox.Model() + Seq.Rev(old(inbox.Model())) + [x];
      old(Model()) + [x];
    }
  }

  
  method Dequeue() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures [x] + Model() == old(Model())
  { 
    notEmpty();
    assert !inbox.Empty?() || !outbox.Empty?();
    
    var b := outbox.Empty();
    if b 
    {
      Transfer();
    }
    
    label PostTrans:
    
    x := outbox.Pop();
    
    calc == {
      [x] + Model();
      {assert Model() == outbox.Model() + Seq.Rev(inbox.Model());}
      [x] + outbox.Model() + Seq.Rev(inbox.Model());
      old@PostTrans(outbox.Model()) + Seq.Rev(inbox.Model());
      old(Model());
    }
  }
}
}
