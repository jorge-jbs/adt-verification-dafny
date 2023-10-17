include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"
include "../../../../src/tree/layer4/TRBTree/MoveRed.dfy"
include "../../../../src/tree/layer4/TRBTree/RemoveMinMaintainingPrev.dfy"
include "../../../../src/tree/layer4/TRBTree/UpdateNext.dfy"

module {:options "-functionSyntax:4"} TRBTree.Remove {
  import opened KeyValue
  import opened Utils
  import opened Utils.Option
  import opened Color
  import opened Base
  import opened Rotate
  import opened Res = Restore
  import opened MoveRed
  import opened RM = RemoveMinMaintainingPrev
  import opened UN = UpdateNext

  function Remove(
      t: trbtreeOrThread,
      isLeft: bool,
      k: K
    ): option<trbtreeOrThread>
    decreases size(t)
  {
    match t
    case Empty|Thread(_) => Some(t)
    case Node(_, _, _, _, _) =>
      if t.key > k then
        var t' :-
          if isBlack(t.left) && !isRed(t.left.left) then
            var _ :- Guard(t.right.Node?);
            MoveRedLeftSize(t);
            Some(MoveRedLeft(t))
          else
            Some(t);
        var l' :- Remove(t'.left, true, k);
        Some(Restore(t'.(left := l')))
      else
        var t' :=
          if isRed(t.left) then
            RotateRightSize(t);
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
            if isBlack(t'.right) && !isRed(t'.right.left) then
              var _ :- Guard(t.left.Node?);
              MoveRedRightSize(t');
              Some(MoveRedRight(t'))
            else
              Some(t');
          if k != t''.key then
            var r' :- Remove(t''.right, false, k);
            Some(Restore(t''.(right := r')))
          else
            var (r', minK, minV) :- RemoveMinMaintainingPrev(t''.right, false);
            var _ :- Guard(!IsThreadOrEmpty(t''.left));
            Some(Restore(Node(
              UpdateNext(Thread(minK), t''.left),
              minK,
              minV,
              r',
              t''.color
            )))
  }

  method RemoveTest1()
  {
    var t1 := ThreadedTreeExample1();
    var t1' := ConditionalReddenRoot(t1);
    assert ThreadedTreeRoot(t1);
    assert RedBlackTreeRoot(t1);
    assert SearchTree(t1);
    var t2 := Remove(t1', true, 1).unwrap;
    var t2' := BlackenRoot(t2);
    print trbtreeToString(t1') + "\n\n";
    print trbtreeToString(t2') + "\n\n";
    assert ThreadedTreeRoot(t2');
    assert RedBlackTree(t2');
    assert RedBlackTreeRoot(t2');
    assert SearchTree(t2');
    /*
    var t3 := BlackenRoot(Remove(ConditionalReddenRoot(t2'), true, 2).unwrap);
    print trbtreeToString(t3) + "\n\n";
    assert ThreadedTreeRoot(t3);
    assert RedBlackTree(t3);
    assert RedBlackTreeRoot(t3);
    assert SearchTree(t3);
    var t4 := BlackenRoot(Remove(ConditionalReddenRoot(t3), true, 3).unwrap);
    print trbtreeToString(t4) + "\n\n";
    assert ThreadedTreeRoot(t4);
    assert RedBlackTree(t4);
    assert RedBlackTreeRoot(t4);
    assert SearchTree(t4);
    var t5 := BlackenRoot(Remove(ConditionalReddenRoot(t4), true, 4).unwrap);
    print trbtreeToString(t5) + "\n\n";
    assert ThreadedTreeRoot(t5);
    assert RedBlackTree(t5);
    assert RedBlackTreeRoot(t5);
    assert SearchTree(t5);
    */
  }

  lemma RemoveSpec(t: trbtreeOrThread, isLeft: bool, k: K)
    decreases size(t)

    requires SearchTree(t)
    requires RedBlackTree(t)
    requires t.Empty? || t.Thread? || isRed(t) || isRed(t.left)
    requires !(isRed(t) && isRed(t.left))

    ensures Remove(t, isLeft, k).Some?
    ensures SearchTree(Remove(t, isLeft, k).unwrap)
    ensures RedBlackTree(Remove(t, isLeft, k).unwrap)
    ensures BlackHeight(Remove(t, isLeft, k).unwrap) == BlackHeight(t)
    ensures isRed(Remove(t, isLeft, k).unwrap) ==> !isRed(Remove(t, isLeft, k).unwrap.left)
    ensures !isRed(t) ==> !isRed(Remove(t, isLeft, k).unwrap)

    ensures keys(Remove(t, isLeft, k).unwrap) == keys(t) - {k}
  {
    if t.Empty? || t.Thread? {
    } else {
      if t.key > k {  // 6"
        var t' :=
          if isBlack(t.left) && !isRed(t.left.left) then
            MoveRedLeftSize(t);
            MoveRedLeft(t)
          else
            t;
        if isBlack(t.left) && !isRed(t.left.left) {
          MoveRedLeftSpec(t);
        }
        RemoveSpec(t'.left, true, k);
        var l' := Remove(t'.left, true, k).unwrap;
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
          if isRed(t.left) then
            RotateRightSize(t);
            RotateRight(t)
          else
            t;
        if isRed(t.left) {
          RotateRightSpec(t);
        }
        if k == t'.key && IsThreadOrEmpty(t'.right) {
        } else {
          var t'' :=
            if isBlack(t'.right) && !isRed(t'.right.left) then
              MoveRedRightSize(t');
              MoveRedRight(t')
            else
              t';
          if isBlack(t'.right) && !isRed(t'.right.left) {
            MoveRedRightSpec(t');
          }
          if k != t''.key {  // 22"
            RemoveSpec(t''.right, false, k);
            var r' := Remove(t''.right, false, k).unwrap;
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
            RemoveMinMaintainingPrevSpec(t''.right, false);
            assert forall m | m in keys(t''.right) :: t''.key < m;
            var (r', minK, minV) := RemoveMinMaintainingPrev(t''.right, false).unwrap;
            var t''' :=
              Node(
                UpdateNext(Thread(minK), t''.left),
                minK,
                minV,
                r',
                t''.color
              );
            UpdateNextSpec(Thread(minK), t''.left);
            var t'''' := Restore(t''');
            RestoreSpec(t''');
          }
        }
      }
    }
  }

 lemma RemoveThreaded(
      prev: threadOrEmpty, 
      t: trbtreeOrThread, 
      next: threadOrEmpty, 
      isLeft: bool, 
      k: K
    )
    decreases size(t)

    requires Remove(t, isLeft, k).Some?
    requires ThreadedTreeRecCond(prev, t, next, isLeft)
    ensures ThreadedTreeRecCond(prev, Remove(t, isLeft, k).unwrap, next, isLeft)
  {
    if t.Empty? || t.Thread? {
    } else if t.key > k {
      var t' :=
        if isBlack(t.left) && !isRed(t.left.left) then
          MoveRedLeftSize(t);
          MoveRedLeft(t)
        else
          t;
      if isBlack(t.left) && !isRed(t.left.left) {
        MoveRedLeftThreaded(prev, t, next);
      }
      RemoveThreaded(prev, t'.left, Thread(t'.key), true, k);
      var l' := Remove(t'.left, true, k).unwrap;
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
        if isRed(t.left) then
          RotateRightSize(t);
          RotateRight(t)
        else
          t;
      if isRed(t.left) {
        RotateRightThreaded(prev, t, next);
      }
      if k == t'.key && IsThreadOrEmpty(t'.right) {
        if isLeft {
          assert ThreadedTreeRecL(prev, t'.left, Thread(t.key));
        } else {
          assert ThreadedTreeRecR(Thread(t.key), t'.right, next);
        }
      } else {
        var t'' :=
          if isBlack(t'.right) && !isRed(t'.right.left) then
            MoveRedRightSize(t');
            MoveRedRight(t')
          else
            t';
        if isBlack(t'.right) && !isRed(t'.right.left) {
          MoveRedRightThreaded(prev, t', next);
        }
        if k != t''.key {
          RemoveThreaded(Thread(t''.key), t''.right, next, false, k);
          var r' := Remove(t''.right, false, k).unwrap;
          assert ThreadedTreeRecR(Thread(t''.key), t''.right, next);
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
        } else {
          assert ThreadedTreeNe(Thread(t''.key), t''.right, next) by {
            assert ThreadedTreeNe(prev, t'', next);
            assert ThreadedTreeRecR(Thread(t''.key), t''.right, next);
          }
          RemoveMinMaintainingPrevThreaded(Thread(t''.key), t''.right, next, false);
          var (r', minK, minV) := RemoveMinMaintainingPrev(t''.right, false).unwrap;
          var t''' :=
            Node(
              UpdateNext(Thread(minK), t''.left),
              minK,
              minV,
              r',
              t''.color
            );
          assert ThreadedTreeNe(prev, t''.left, Thread(t''.key)) by {
            assert ThreadedTreeNe(prev, t'', next);
            assert ThreadedTreeRecL(prev, t''.left, Thread(t''.key));
          }
          UpdateNextThreaded(Thread(minK), prev, t''.left, Thread(t''.key));
          var t'''' := Restore(t''');
          RestoreThreaded(prev, t''', next);
        }
      }
    }
  }
}
