include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"
include "../../../../src/tree/layer4/TRBTree/MoveRed.dfy"
include "../../../../src/tree/layer4/TRBTree/RemoveMinMaintainingPrev.dfy"
include "../../../../src/tree/layer4/TRBTree/UpdatePrev.dfy"
include "../../../../src/tree/layer4/TRBTree/UpdateNext.dfy"

module TRBTree.Remove {
  import opened KeyValue
  import opened Utils
  import opened Utils.Option
  import opened Color
  import opened Base
  import opened Rotate
  import opened Res = Restore
  import opened MoveRed
  import opened RM = RemoveMinMaintainingPrev
  import opened UP = UpdatePrev
  import opened UN = UpdateNext

  function method RemoveP(
      p: pointer, 
      isLeft: bool,
      k: K
    ): option<pointer>
    decreases sizeWithPointersP(p)
  {
    match p {
      case Thread(k) => Some(Thread(k))
      case Child(t) => Remove(t, isLeft, k)
    }
  }

  function method Remove(
      t: rbtree, 
      isLeft: bool,
      k: K
    ): option<pointer>
    decreases sizeWithPointers(t)
  {
    if t.Empty? then
      Some(Child(t))
    else
      if t.key > k then
        var t' :-
          if isBlackP(t.left) && !isRedP(t.left.child.left) then
            var _ :- Guard(t.right.Child? && t.right.child.Node?);
            MoveRedLeftSize(t);
            Some(MoveRedLeft(t))
          else
            Some(t);
        var l' :- RemoveP(t'.left, true, k);
        Some(Child(Restore(Node(
          l',
          t'.key,
          t'.value,
          t'.right,
          t'.color
        ))))
      else
        var t' :=
          if isRedP(t.left) then
            assert RotateRight(t).right.Child?;
            RotateRightSizeWithPointers(t);
            RotateRight(t)
          else
            t;
        if k == t'.key && IsThreadOrEmpty(t'.right) then
          if isLeft then
            Some(t'.left)
          else
            Some(t'.right)
        else
          var t'' :-
            if isBlackP(t'.right) && !isRedP(t'.right.child.left) then
              var _ :- Guard(t.left.Child? && t.left.child.Node?);
              MoveRedRightSize(t');
              Some(MoveRedRight(t'))
            else
              Some(t');
          if k != t''.key then
            var r' :- RemoveP(t''.right, false, k);
            Some(Child(Restore(Node(
              t''.left,
              t''.key,
              t''.value,
              r',
              t''.color
            ))))
          else
            var (r', minK, minV) :- RemoveMinMaintainingPrev(t''.right.child, false);
            Some(Child(Restore(Node(
              UpdateNextP(Thread(minK), t''.left),
              minK,
              minV,
              r',
              t''.color
            ))))
  }

  method {:verify false} RemoveTest1()
  {
    var t1 := ThreadedTreeExample1();
    var t1' := ConditionalReddenRoot(t1);
    assert ThreadedTreeRoot(t1);
    assert RedBlackTreeRoot(t1);
    assert SearchTree(t1);
    var t2 := Remove(t1', true, 1).unwrap.child;
    var t2' := BlackenRoot(t2);
    print rbtreeToString(t1') + "\n\n";
    print rbtreeToString(t2') + "\n\n";
    assert ThreadedTreeRoot(t2');
    assert RedBlackTree(t2');
    assert RedBlackTreeRoot(t2');
    assert SearchTree(t2');
    /*
    var t3 := BlackenRoot(Remove(ConditionalReddenRoot(t2'), true, 2).unwrap.child);
    print rbtreeToString(t3) + "\n\n";
    assert ThreadedTreeRoot(t3);
    assert RedBlackTree(t3);
    assert RedBlackTreeRoot(t3);
    assert SearchTree(t3);
    var t4 := BlackenRoot(Remove(ConditionalReddenRoot(t3), true, 3).unwrap.child);
    print rbtreeToString(t4) + "\n\n";
    assert ThreadedTreeRoot(t4);
    assert RedBlackTree(t4);
    assert RedBlackTreeRoot(t4);
    assert SearchTree(t4);
    var t5 := BlackenRoot(Remove(ConditionalReddenRoot(t4), true, 4).unwrap.child);
    print rbtreeToString(t5) + "\n\n";
    assert ThreadedTreeRoot(t5);
    assert RedBlackTree(t5);
    assert RedBlackTreeRoot(t5);
    assert SearchTree(t5);
    */
  }
}
