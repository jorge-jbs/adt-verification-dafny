include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"
include "../../../../src/tree/layer4/TRBTree/MoveRed.dfy"

module TRBTree.RemoveMinMaintainingPrev {
  import opened KeyValue
  import opened Utils
  import opened Utils.Option
  import opened Utils.Printer
  import opened Color
  import opened Base
  import opened Res = Restore
  import opened MoveRed

  function method RemoveMinMaintainingPrevP(p: pointer): option<(pointer, K, V)>
    requires p.Child?
    requires p.child.Node?
    decreases sizeWithPointersP(p)
  {
    RemoveMinMaintainingPrev(p.child)
  }

  function method RemoveMinMaintainingPrev(t: rbtree): option<(pointer, K, V)>
    requires t.Node?
    decreases sizeWithPointers(t)
  {
    if IsThreadOrEmpty(t.left) then
      var _ :- Guard(t.right.Thread? || t.right == Child(Empty));
      Some((Thread(t.key), t.key, t.value))
    else
      var t' :-
        if isBlackP(t.left) && !isRedP(t.left.child.left) then
          var _ :- Guard(t.right.Child? && t.right.child.Node?);
          MoveRedLeftSize(t);
          Some(MoveRedLeft(t))
        else
          Some(t);
      var (l', minK, minV) :- RemoveMinMaintainingPrevP(t'.left);
      Some((Child(Restore(Node(l', t'.key, t'.value, t'.right, t'.color))), minK, minV))
  }

  method {:main} RemoveMinMaintainingPrevTest1()
  {
    var t1 := ThreadedTreeExample1();
    var t1' := ConditionalReddenRoot(t1);
    assert ThreadedTreeRoot(t1);
    assert RedBlackTreeRoot(t1);
    assert SearchTree(t1);
    var (t2, minK, minV) := RemoveMinMaintainingPrev(t1').unwrap;
    var t2' := BlackenRoot(t2.child);
    assert minK == 1;
    print rbtreeToString(t1') + "\n\n";
    print rbtreeToString(t2') + "\n\n";
    assert ThreadedTreeRec(Thread(1), t2', Child(Empty));
    //assert ThreadedTreeRoot(t2');
    assert RedBlackTree(t2');
    assert RedBlackTreeRoot(t2');
    assert SearchTree(t2');

/*
    //print rbtreeToString(Restore(Node(Child(Empty), 2, 0, Child(Node(Thread(2), 3, 0, Thread(4), Red)), Black))) + "\n\n";
    //print rbtreeToString(MoveRedLeft(t1')) + "\n\n";
    //print rbtreeToString(MoveRedLeft(MoveRedLeft(t1').left.child)) + "\n\n";

    calc == {
      RemoveMinMaintainingPrev(t1').unwrap.0;
      Child(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1').left).unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color)));
      Child(Restore(Node(Child(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(MoveRedLeft(t1').left.child).left).unwrap.0, MoveRedLeft(t1').left.child.key, MoveRedLeft(t1').left.child.value, MoveRedLeft(t1').left.child.right, MoveRedLeft(t1').left.child.color))), t1'.key, t1'.value, t1'.right, t1'.color)));
    }
    //print rbtreeToString(Restore(Node(MoveRedLeft(t1').left.unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color)));
    //print rbtreeToString(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1').left).unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color)) + "\n\n";
    //print rbtreeToString(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1').left).unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color))) + "\n\n";

    var t1'left' := MoveRedLeft(t1').left.child;
    print rbtreeToString(t1'left') + "\n\n";
    print rbtreeToString(RemoveMinMaintainingPrev(t1'left').unwrap.0.child) + "\n\n";
    print rbtreeToString(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1'left').left).unwrap.0, t1'left'.key, t1'left'.value, t1'left'.right, t1'left'.color)) + "\n\n";
    print rbtreeToString(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1'left').left).unwrap.0, t1'left'.key, t1'left'.value, t1'left'.right, t1'left'.color))) + "\n\n";

    calc == {
      RemoveMinMaintainingPrev(t1'left').unwrap.0;
      Child(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1'left').left).unwrap.0, t1'left'.key, t1'left'.value, t1'left'.right, t1'left'.color)));
    }

    var t1'leftleft' := MoveRedLeft(t1'left').left.child;
    print rbtreeToString(t1'leftleft') + "\n\n";
    print rbtreeToString(t2') + "\n\n";
    */
  }

  method RemoveMinMaintainingPrevTest2()
  {
    var t1 := ThreadedTreeExample1();
    var t1' := ConditionalReddenRoot(t1);
    print rbtreeToString(t1') + "\n\n";
    print pointerToString(RemoveMinMaintainingPrev(t1'.right.child).unwrap.0) + "\n\n";
  }

  lemma RemoveMinMaintainingPrevPSpec(p: pointer)
    decreases sizeWithPointersP(p)

    requires p.Child?
    requires p.child.Node?
    requires SearchTree(p.child)
    requires RedBlackTree(p.child)
    requires !(isRed(p.child) && isRedP(p.child.left))
    requires isRed(p.child) || isRedP(p.child.left)

    ensures RemoveMinMaintainingPrevP(p).Some?
    ensures keysP(RemoveMinMaintainingPrevP(p).unwrap.0) == keys(p.child) - {RemoveMinMaintainingPrevP(p).unwrap.1}
    ensures RemoveMinMaintainingPrevP(p).unwrap.1 in keys(p.child)
    //ensures forall k | k in keys(p.child) :: RemoveMinMaintainingPrevP(p).unwrap.1 <= k
    ensures forall k | k in keysP(RemoveMinMaintainingPrevP(p).unwrap.0) :: RemoveMinMaintainingPrevP(p).unwrap.1 < k

    ensures SearchTreeP(RemoveMinMaintainingPrevP(p).unwrap.0)
    ensures RedBlackTreeP(RemoveMinMaintainingPrevP(p).unwrap.0)
    ensures BlackHeightP(RemoveMinMaintainingPrevP(p).unwrap.0) == BlackHeight(p.child)
    ensures isRedP(RemoveMinMaintainingPrevP(p).unwrap.0) ==> !isRedP(RemoveMinMaintainingPrevP(p).unwrap.0.child.left)
    ensures !isRed(p.child) ==> !isRedP(RemoveMinMaintainingPrevP(p).unwrap.0)
  {
    RemoveMinMaintainingPrevSpec(p.child);
  }

  lemma SetDiffComm<K>(r: set<K>, k: K, s: set<K>)
    requires k !in s
    ensures r - {k} + s == r + s - {k}
  {}

  lemma RemoveMinMaintainingPrevSpec(t: rbtree)
    decreases sizeWithPointers(t)

    requires t.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRedP(t.left))
    requires isRed(t) || isRedP(t.left)

    ensures RemoveMinMaintainingPrev(t).Some?
    ensures keysP(RemoveMinMaintainingPrev(t).unwrap.0) == keys(t) - {RemoveMinMaintainingPrev(t).unwrap.1}
    ensures RemoveMinMaintainingPrev(t).unwrap.1 in keys(t)
    //ensures forall k | k in keys(t) :: RemoveMinMaintainingPrev(t).unwrap.1 <= k
    ensures forall k | k in keysP(RemoveMinMaintainingPrev(t).unwrap.0) :: RemoveMinMaintainingPrev(t).unwrap.1 < k

    ensures SearchTreeP(RemoveMinMaintainingPrev(t).unwrap.0)
    ensures RedBlackTreeP(RemoveMinMaintainingPrev(t).unwrap.0)
    ensures BlackHeightP(RemoveMinMaintainingPrev(t).unwrap.0) == BlackHeight(t)
    ensures isRedP(RemoveMinMaintainingPrev(t).unwrap.0) ==> !isRedP(RemoveMinMaintainingPrev(t).unwrap.0.child.left)
    ensures !isRed(t) ==> !isRedP(RemoveMinMaintainingPrev(t).unwrap.0)
  {
    if IsThreadOrEmpty(t.left) {
    } else {
      var pt' :=
        if isBlackP(t.left) && !isRedP(t.left.child.left) then
          var _ :- Guard(t.right.Child? && t.right.child.Node?);
          MoveRedLeftSize(t);
          Some(MoveRedLeft(t))
        else
          Some(t);
      assert pt'.Some?;
      var t' := pt'.unwrap;
      if isBlackP(t.left) && !isRedP(t.left.child.left) {
        MoveRedLeftSpec(t);
      }
      RemoveMinMaintainingPrevPSpec(t'.left);
      assert RemoveMinMaintainingPrevP(t'.left).Some?;
      assert forall m | m in keysP(t'.left) :: m < t'.key;
      var (l', minK, minV) := RemoveMinMaintainingPrevP(t'.left).unwrap;
      var t'' :=
        Node(
          l',
          t'.key,
          t'.value,
          t'.right,
          t'.color
        );
      var t''' := Restore(t'');
      RestoreSpec(t'');
      calc == {
        keysP(RemoveMinMaintainingPrev(t).unwrap.0);
        keys(t''');
        keys(t'');
        keysP(l') + {t'.key} + keysP(t'.right);
        (keysP(t'.left) - {minK} + {t'.key}) + keysP(t'.right);
        { SetDiffComm(keysP(t'.left), minK, {t'.key}); }
        (keysP(t'.left) + {t'.key} - {minK}) + keysP(t'.right);
        { SetDiffComm(keysP(t'.left) + {t'.key}, minK, keysP(t'.right)); }
        keysP(t'.left) + {t'.key} + keysP(t'.right) - {minK};
        keys(t') - {minK};
        keys(t) - {minK};
      }
    }
  }

  lemma RemoveMinMaintainingPrevPThreaded(prev: threadOrEmpty, p: pointer, next: threadOrEmpty)
    decreases sizeWithPointersP(p)

    requires p.Child?
    requires p.child.Node?
    requires ThreadedTreeRec(prev, p.child, next)
    requires RemoveMinMaintainingPrevP(p).Some?
    ensures ThreadedTreeRecPL(
      Thread(RemoveMinMaintainingPrevP(p).unwrap.1),
      RemoveMinMaintainingPrevP(p).unwrap.0,
      next
    )
  {
    RemoveMinMaintainingPrevThreaded(prev, p.child, next);
  }

  lemma RemoveMinMaintainingPrevThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty)
    decreases sizeWithPointers(t)

    requires t.Node?
    requires ThreadedTreeRec(prev, t, next)
    requires RemoveMinMaintainingPrev(t).Some?
    ensures ThreadedTreeRecPL(
      Thread(RemoveMinMaintainingPrev(t).unwrap.1),
      RemoveMinMaintainingPrev(t).unwrap.0,
      next
    )
  {
    if IsThreadOrEmpty(t.left) {
    } else {
      var pt' :=
        if isBlackP(t.left) && !isRedP(t.left.child.left) then
          var _ :- Guard(t.right.Child? && t.right.child.Node?);
          MoveRedLeftSize(t);
          Some(MoveRedLeft(t))
        else
          Some(t);
      assert pt'.Some?;
      var t' := pt'.unwrap;
      if isBlackP(t.left) && !isRedP(t.left.child.left) {
        MoveRedLeftThreaded(prev, t, next);
      }
      RemoveMinMaintainingPrevPThreaded(prev, t'.left, Thread(t'.key));
      assert RemoveMinMaintainingPrevP(t'.left).Some?;
      var (l', minK, minV) := RemoveMinMaintainingPrevP(t'.left).unwrap;
      var t'' :=
        Node(
          l',
          t'.key,
          t'.value,
          t'.right,
          t'.color
        );
      var t''' := Restore(t'');
      RestoreThreaded(Thread(minK), t'', next);
    }
  }
}
