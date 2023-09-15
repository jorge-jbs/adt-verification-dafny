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
        Some(Child(Restore(t'.(left := l'))))
      else
        var t' :=
          if isRedP(t.left) then
            RotateRightSizeWithPointers(t);
            RotateRight(t)
          else
            t;
        if k == t'.key && IsThreadOrEmpty(t'.right) then
          var _ :- Guard(IsThreadOrEmpty(t'.left));
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
            Some(Child(Restore(t''.(right := r'))))
          else
            var (r', minK, minV) :- RemoveMinMaintainingPrev(t''.right.child, false);
            var _ :- Guard(!IsThreadOrEmpty(t''.left));
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

  lemma RemovePSpec(p: pointer, isLeft: bool, k: K)
    decreases sizeWithPointersP(p)

    requires SearchTreeP(p)
    requires RedBlackTreeP(p)
    requires p.Thread? || p.child.Empty? || isRedP(p) || isRedP(p.child.left)
    requires !(isRedP(p) && isRedP(p.child.left))

    ensures RemoveP(p, isLeft, k).Some?
    ensures SearchTreeP(RemoveP(p, isLeft, k).unwrap)
    ensures RedBlackTreeP(RemoveP(p, isLeft, k).unwrap)
    ensures BlackHeightP(RemoveP(p, isLeft, k).unwrap) == BlackHeightP(p)
    ensures isRedP(RemoveP(p, isLeft, k).unwrap) ==> !isRedP(RemoveP(p, isLeft, k).unwrap.child.left)
    ensures !isRedP(p) ==> !isRedP(RemoveP(p, isLeft, k).unwrap)

    ensures keysP(RemoveP(p, isLeft, k).unwrap) == keysP(p) - {k}
  {
    match p {
      case Thread(k) => {}
      case Child(t) => {
        RemoveSpec(t, isLeft, k);
      }
    }
  }

  lemma RemoveSpec(t: rbtree, isLeft: bool, k: K)  // 60"
    decreases sizeWithPointers(t)

    requires SearchTree(t)
    requires RedBlackTree(t)
    requires t.Empty? || isRed(t) || isRedP(t.left)
    requires !(isRed(t) && isRedP(t.left))

    ensures Remove(t, isLeft, k).Some?
    ensures SearchTreeP(Remove(t, isLeft, k).unwrap)
    ensures RedBlackTreeP(Remove(t, isLeft, k).unwrap)
    ensures BlackHeightP(Remove(t, isLeft, k).unwrap) == BlackHeight(t)
    ensures isRedP(Remove(t, isLeft, k).unwrap) ==> !isRedP(Remove(t, isLeft, k).unwrap.child.left)
    ensures !isRed(t) ==> !isRedP(Remove(t, isLeft, k).unwrap)

    ensures keysP(Remove(t, isLeft, k).unwrap) == keys(t) - {k}
  {
    if t.Empty? {
    } else {
      if t.key > k {  // 6"
        var t' :=
          if isBlackP(t.left) && !isRedP(t.left.child.left) then
            MoveRedLeftSize(t);
            MoveRedLeft(t)
          else
            t;
        if isBlackP(t.left) && !isRedP(t.left.child.left) {
          MoveRedLeftSpec(t);
        }
        RemovePSpec(t'.left, true, k);
        var l' := RemoveP(t'.left, true, k).unwrap;
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
      } else {
        var t' :=
          if isRedP(t.left) then
            RotateRightSizeWithPointers(t);
            RotateRight(t)
          else
            t;
        if isRedP(t.left) {
          RotateRightSpec(t);
        }
        if k == t'.key && IsThreadOrEmpty(t'.right) {
        } else {
          var t'' :=
            if isBlackP(t'.right) && !isRedP(t'.right.child.left) then
              MoveRedRightSize(t');
              MoveRedRight(t')
            else
              t';
          if isBlackP(t'.right) && !isRedP(t'.right.child.left) {
            MoveRedRightSpec(t');
          }
          if k != t''.key {  // 22"
            RemovePSpec(t''.right, false, k);
            var r' := RemoveP(t''.right, false, k).unwrap;
            var t''' :=
              Node(
                t''.left,
                t''.key,
                t''.value,
                r',
                t''.color
              );
            var t'''' := Restore(t''');
            RestoreSpec(t''');
          } else {  // 16"
            RemoveMinMaintainingPrevPSpec(t''.right, false);
            assert forall m | m in keysP(t''.right) :: t''.key < m;
            var (r', minK, minV) := RemoveMinMaintainingPrevP(t''.right, false).unwrap;
            var t''' :=
              Node(
                UpdateNextP(Thread(minK), t''.left),
                minK,
                minV,
                r',
                t''.color
              );
            UpdateNextPSpec(Thread(minK), t''.left);
            var t'''' := Restore(t''');
            RestoreSpec(t''');
          }
        }
      }
    }
  }

  lemma RemovePThreaded(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, isLeft: bool, k: K)
    decreases sizeWithPointersP(p)

    requires ThreadedTreeRecPCond(prev, p, next, isLeft)
    requires RemoveP(p, isLeft, k).Some?
    ensures ThreadedTreeRecPCond(prev, RemoveP(p, isLeft, k).unwrap, next, isLeft)
  {
    match p {
      case Thread(k) => {}
      case Child(t) => {
        if t.Node? {
          RemoveThreaded(prev, t, next, isLeft, k);
        }
      }
    }
  }

  lemma RemoveThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty, isLeft: bool, k: K)  // 24"
    decreases sizeWithPointers(t)

    requires t.Node?
    requires ThreadedTreeRec(prev, t, next)
    requires Remove(t, isLeft, k).Some?
    ensures ThreadedTreeRecPCond(prev, Remove(t, isLeft, k).unwrap, next, isLeft)
  {
    if t.key > k {
      var t' :=
        if isBlackP(t.left) && !isRedP(t.left.child.left) then
          MoveRedLeftSize(t);
          MoveRedLeft(t)
        else
          t;
      if isBlackP(t.left) && !isRedP(t.left.child.left) {
        MoveRedLeftThreaded(prev, t, next);
      }
      RemovePThreaded(prev, t'.left, Thread(t'.key), true, k);
      var l' := RemoveP(t'.left, true, k).unwrap;
      var t'' :=
        Node(
          l',
          t'.key,
          t'.value,
          t'.right,
          t'.color
        );
      var t''' := Restore(t'');
      RestoreThreaded(prev, t'', next);
    } else {
      var t' :=
        if isRedP(t.left) then
          RotateRightSizeWithPointers(t);
          RotateRight(t)
        else
          t;
      if isRedP(t.left) {
        RotateRightThreaded(prev, t, next);
      }
      if k == t'.key && IsThreadOrEmpty(t'.right) {
      } else {
        var t'' :=
          if isBlackP(t'.right) && !isRedP(t'.right.child.left) then
            MoveRedRightSize(t');
            MoveRedRight(t')
          else
            t';
        if isBlackP(t'.right) && !isRedP(t'.right.child.left) {
          MoveRedRightThreaded(prev, t', next);
        }
        if k != t''.key {  // 22"
          RemovePThreaded(Thread(t''.key), t''.right, next, false, k);
          var r' := RemoveP(t''.right, false, k).unwrap;
          assert ThreadedTreeRecPR(Thread(t''.key), t''.right, next);
          var t''' :=
            Node(
              t''.left,
              t''.key,
              t''.value,
              r',
              t''.color
            );
          var t'''' := Restore(t''');
          RestoreThreaded(prev, t''', next);
        } else {  // 16"
          RemoveMinMaintainingPrevPThreaded(Thread(t''.key), t''.right, next, false);
          var (r', minK, minV) := RemoveMinMaintainingPrevP(t''.right, false).unwrap;
          var t''' :=
            Node(
              UpdateNextP(Thread(minK), t''.left),
              minK,
              minV,
              r',
              t''.color
            );
          UpdateNextPThreaded(Thread(minK), prev, t''.left, Thread(t''.key));
          var t'''' := Restore(t''');
          RestoreThreaded(prev, t''', next);
        }
      }
    }
  }
}
