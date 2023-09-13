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

  function method RemoveP(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, k: K): option<pointer>
    decreases sizeWithPointersP(p)
  {
    match p {
      case Thread(k) => Some(Thread(k))
      case Child(t) =>
        var t' :- Remove(prev, t, next, k);
        Some(Child(t'))
    }
  }

  function method Remove(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty, k: K): option<rbtree>
    decreases sizeWithPointers(t)
  {
    if t.Empty? then
      Some(t)
    else
      if t.key > k then
        var t' :-
          if isBlackP(t.left) && !isRedP(t.left.child.left) then
            var _ :- Guard(t.right.Child? && t.right.child.Node?);
            MoveRedLeftSize(t);
            Some(MoveRedLeft(t))
          else
            Some(t);
        var l' :- RemoveP(prev, t'.left, Thread(t'.key), k);
        Some(Restore(Node(
          if IsThreadOrEmpty(l') then prev else l',
          t'.key,
          t'.value,
          t'.right,
          t'.color
        )))
      else
        var t' :=
          if isRedP(t.left) then
            assert RotateRight(t).right.Child?;
            RotateRightSizeWithPointers(t);
            RotateRight(t)
          else
            t;
        if k == t'.key && (t'.right.Thread? || t'.right.child.Empty?) then
          Some(Empty())
        else
          var t'' :-
            if isBlackP(t'.right) && !isRedP(t'.right.child.left) then
              var _ :- Guard(t.left.Child? && t.left.child.Node?);
              MoveRedRightSize(t');
              Some(MoveRedRight(t'))
            else
              Some(t');
          if k != t''.key then
            var r' :- RemoveP(Thread(t''.key), t''.right, next, k);
            Some(Restore(Node(
              t''.left,
              t''.key,
              t''.value,
              if IsThreadOrEmpty(r') then next else r',
              t''.color
            )))
          else
            var rRight := t''.right.child.right;
            var (r', minK, minV) :- RemoveMinMaintainingPrev(t''.right.child);
            Some(Restore(Node(
              UpdateNextP(Thread(minK), t''.left),
              minK,
              minV,
              if IsThreadOrEmpty(r') then rRight else r',
              t''.color
            )))
  }

  method {:verify false} RemoveTest1()
  {
    var t1 := ThreadedTreeExample1();
    var t1' := ConditionalReddenRoot(t1);
    assert ThreadedTreeRoot(t1);
    assert RedBlackTreeRoot(t1);
    assert SearchTree(t1);
    var t2 := Remove(Child(Empty), t1', Child(Empty), 1).unwrap;
    var t2' := BlackenRoot(t2);
    print rbtreeToString(t1') + "\n\n";
    print rbtreeToString(t2') + "\n\n";
    assert ThreadedTreeRoot(t2');
    assert RedBlackTree(t2');
    assert RedBlackTreeRoot(t2');
    assert SearchTree(t2');
    /*
    var t3 := BlackenRoot(Remove(Child(Empty), ConditionalReddenRoot(t2'), Child(Empty), 2).unwrap);
    print rbtreeToString(t3) + "\n\n";
    assert ThreadedTreeRoot(t3);
    assert RedBlackTree(t3);
    assert RedBlackTreeRoot(t3);
    assert SearchTree(t3);
    var t4 := BlackenRoot(Remove(Child(Empty), ConditionalReddenRoot(t3), Child(Empty), 3).unwrap);
    print rbtreeToString(t4) + "\n\n";
    assert ThreadedTreeRoot(t4);
    assert RedBlackTree(t4);
    assert RedBlackTreeRoot(t4);
    assert SearchTree(t4);
    var t5 := BlackenRoot(Remove(Child(Empty), ConditionalReddenRoot(t4), Child(Empty), 4).unwrap);
    print rbtreeToString(t5) + "\n\n";
    assert ThreadedTreeRoot(t5);
    assert RedBlackTree(t5);
    assert RedBlackTreeRoot(t5);
    assert SearchTree(t5);
    */
  }
}
