include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/Collections/Option.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"
include "../../../../src/tree/layer4/TRBTree/MoveRed.dfy"
include "../../../../src/tree/layer4/TRBTree/RemoveMinMaintainingPrev.dfy"
include "../../../../src/tree/layer4/TRBTree/UpdateNext.dfy"

module {:options "-functionSyntax:4"} TRBTree.Remove {
  import opened KeyValue
  import opened Option
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

  predicate IsRemoved(t: trbtreeOrThread, isLeft: bool, k: K)
    decreases size(t)
    requires Remove(t, isLeft, k).Some?
{
    match t
    case Empty|Thread(_) => false
    case Node(_, _, _, _, _) =>
      if t.key > k then
        var t' :=
          if isBlack(t.left) && !isRed(t.left.left) then
            MoveRedLeftSize(t);
            MoveRedLeft(t)
          else
            t;
        IsRemoved(t'.left, true, k)
      else
        var t' :=
          if isRed(t.left) then
            RotateRightSize(t);
            RotateRight(t)
          else
            t;
        if k == t'.key && IsThreadOrEmpty(t'.right) then
          true
        else
          var t'' :=
            if isBlack(t'.right) && !isRed(t'.right.left) then
              MoveRedRightSize(t');
              MoveRedRight(t')
            else
              t';
          if k != t''.key then
            IsRemoved(t''.right, false, k)
          else
            true
  }

  lemma IsRemovedSpec(t: trbtreeOrThread, isLeft: bool, k: K)
    decreases size(t)
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires t.Empty? || t.Thread? || isRed(t) || isRed(t.left)
    requires !(isRed(t) && isRed(t.left))
    requires Remove(t, isLeft, k).Some?
    ensures IsRemoved(t, isLeft, k) <==> k in keys(t)
  {
    if t.Empty? || t.Thread? {
    } else {
      if t.key > k {
        var t' :=
          if isBlack(t.left) && !isRed(t.left.left) then
            MoveRedLeftSize(t);
            MoveRedLeft(t)
          else
            t;
        if isBlack(t.left) && !isRed(t.left.left) {
          MoveRedLeftSpec(t);
        }
        IsRemovedSpec(t'.left, true, k);
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
          if k != t''.key {
            IsRemovedSpec(t''.right, false, k);
          } else {
          }
        }
      }
    }
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

  lemma RemoveSize(t: trbtreeOrThread, isLeft: bool, k: K)
    decreases size(t)
    requires Remove(t, isLeft, k).Some?
    ensures
      if IsRemoved(t, isLeft, k) then
        size(Remove(t, isLeft, k).unwrap) == size(t) - 1
      else
        size(Remove(t, isLeft, k).unwrap) == size(t)
  {
    if t.Empty? || t.Thread? {
    } else {
      if t.key > k {
        var t' :=
          if isBlack(t.left) && !isRed(t.left.left) then
            MoveRedLeftSize(t);
            MoveRedLeft(t)
          else
            t;
        if isBlack(t.left) && !isRed(t.left.left) {
          MoveRedLeftSize(t);
        }
        RemoveSize(t'.left, true, k);
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
        RestoreSize(t'');
      } else {
        var t' :=
          if isRed(t.left) then
            RotateRightSize(t);
            RotateRight(t)
          else
            t;
        if isRed(t.left) {
          RotateRightSize(t);
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
            MoveRedRightSize(t');
          }
          if k != t''.key {
            RemoveSize(t''.right, false, k);
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
            RestoreSize(t''');
          } else {
            RemoveMinMaintainingPrevSize(t''.right, false);
            var (r', minK, minV) := RemoveMinMaintainingPrev(t''.right, false).unwrap;
            var t''' :=
              Node(
                UpdateNext(Thread(minK), t''.left),
                minK,
                minV,
                r',
                t''.color
              );
            UpdateNextSize(Thread(minK), t''.left);
            var t'''' := Restore(t''');
            RestoreSize(t''');
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

  lemma RemoveModelLemmaL<A, B>(a: map<A, B>, b: map<A, B>, c: map<A, B>, k: A)
    requires k !in b
    requires k !in c
    ensures (a - {k}) + b + c == (a + b + c) - {k}
  {}

  lemma RemoveModelLemmaR<A, B>(a: map<A, B>, b: map<A, B>, c: map<A, B>, k: A)
    requires k !in a
    requires k !in b
    ensures a + b + (c - {k}) == (a + b + c) - {k}
  {}

  lemma RemoveModelLemmaMin1<A, B>(a: map<A, B>, b: map<A, B>, k: A, v: B)
    requires k in b.Keys
    requires b[k] == v
    ensures a + map[k := v] + (b - {k}) == a + b
  {}

  lemma RemoveModelLemmaMin2<A, B>(a: map<A, B>, b: map<A, B>, k: A, v: B)
    requires k !in a.Keys
    requires k !in b.Keys
    ensures (a + map[k := v] + b) - {k} == a + b
  {}

  lemma RemoveModel(t: trbtreeOrThread, isLeft: bool, k: K)  // 2'
    decreases size(t)

    requires SearchTree(t)
    requires RedBlackTree(t)
    requires t.Empty? || t.Thread? || isRed(t) || isRed(t.left)
    requires !(isRed(t) && isRed(t.left))

    ensures Remove(t, isLeft, k).Some?
    ensures toMapRec(Remove(t, isLeft, k).unwrap) == toMapRec(t) - {k}
  {
    if t.Empty? || t.Thread? {
      //assume false;
    } else {
      if t.key > k {  // 22"
        //assume false;
        var t' :=
          if isBlack(t.left) && !isRed(t.left.left) then
            MoveRedLeftSize(t);
            MoveRedLeft(t)
          else
            t;
        if isBlack(t.left) && !isRed(t.left.left) {
          MoveRedLeftSpec(t);
          MoveRedLeftModel(t);
        }
        RemoveSpec(t'.left, true, k);
        RemoveModel(t'.left, true, k);
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
        assert Remove(t, isLeft, k).Some?;
        calc == {
          toMapRec(Remove(t, isLeft, k).unwrap);
          toMapRec(t''');
          toMapRec(Restore(t''));
          { RestoreModel(t''); }
          toMapRec(t'');
          toMapRec(t''.left)
            + map[t''.key := t''.value]
            + toMapRec(t''.right);
          toMapRec(Remove(t'.left, true, k).unwrap)
            + map[t'.key := t'.value]
            + toMapRec(t'.right);
          (toMapRec(t'.left) - {k})
            + map[t'.key := t'.value]
            + toMapRec(t'.right);
          {
            assert k !in toMapRec(t'.right) by {
              ToMapRec(t'.right);
            }
            RemoveModelLemmaL(
              toMapRec(t'.left),
              map[t'.key := t'.value],
              toMapRec(t'.right),
              k
            );
          }
          (toMapRec(t'.left)
            + map[t'.key := t'.value]
            + toMapRec(t'.right)) - {k};
          toMapRec(t') - {k};
          toMapRec(t) - {k};
        }
      } else {
        var t' :=
          if isRed(t.left) then
            RotateRightSize(t);
            RotateRight(t)
          else
            t;
        if isRed(t.left) {
          RotateRightSpec(t);
          RotateRightModel(t);
        }
        if k == t'.key && IsThreadOrEmpty(t'.right) {
          //assume false;
        } else {
          var t'' :=
            if isBlack(t'.right) && !isRed(t'.right.left) then
              MoveRedRightSize(t');
              MoveRedRight(t')
            else
              t';
          if isBlack(t'.right) && !isRed(t'.right.left) {
            MoveRedRightSpec(t');
            MoveRedRightModel(t');
          }
          if k != t''.key {  // 33"
            //assume false;
            RemoveSpec(t''.right, false, k);
            RemoveModel(t''.right, false, k);
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
            calc == {
              toMapRec(Remove(t, isLeft, k).unwrap);
              toMapRec(t'''');
              toMapRec(Restore(t'''));
              { RestoreModel(t'''); }
              toMapRec(t''');
              toMapRec(t'''.left)
                + map[t'''.key := t'''.value]
                + toMapRec(t'''.right);
              toMapRec(t''.left)
                + map[t''.key := t''.value]
                + toMapRec(Remove(t''.right, false, k).unwrap);
              { RemoveModel(t''.right, false, k); }
              toMapRec(t''.left)
                + map[t''.key := t''.value]
                + (toMapRec(t''.right) - {k});
              {
                assert k !in toMapRec(t''.left) by {
                  ToMapRec(t''.left);
                }
                RemoveModelLemmaR(
                  toMapRec(t''.left),
                  map[t''.key := t''.value],
                  toMapRec(t''.right),
                  k
                );
              }
              (toMapRec(t''.left)
                + map[t''.key := t''.value]
                + toMapRec(t''.right)) - {k};
              toMapRec(t'') - {k};
              toMapRec(t') - {k};
              toMapRec(t) - {k};
            }
          } else {  // 60"
            //assume false;
            RemoveMinMaintainingPrevSpec(t''.right, false);
            RemoveMinMaintainingPrevModel(t''.right, false);
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
            UpdateNextModel(Thread(minK), t''.left);
            var t'''' := Restore(t''');
            RestoreSpec(t''');
            RestoreModel(t''');
            calc == {
              toMapRec(Remove(t, isLeft, k).unwrap);
              toMapRec(t'''');
              toMapRec(Restore(t'''));
              { RestoreModel(t'''); }
              toMapRec(t''');
              toMapRec(t'''.left)
                + map[t'''.key := t'''.value]
                + toMapRec(t'''.right);
              toMapRec(UpdateNext(Thread(minK), t''.left))
                + map[minK := minV]
                + toMapRec(RemoveMinMaintainingPrev(t''.right, false).unwrap.0);
              toMapRec(t''.left)
                + map[minK := minV]
                + (toMapRec(t''.right) - {minK});
              {
                RemoveModelLemmaMin1(
                  toMapRec(t''.left),
                  toMapRec(t''.right),
                  minK, minV
                );
              }
              toMapRec(t''.left) + toMapRec(t''.right);
              {
                assert k !in toMapRec(t''.left).Keys by {
                  ToMapRec(t''.left);
                }
                assert k !in toMapRec(t''.right).Keys by {
                  ToMapRec(t''.right);
                }
                RemoveModelLemmaMin2(
                  toMapRec(t''.left),
                  toMapRec(t''.right),
                  k, t''.value
                );
              }
              (toMapRec(t''.left)
                + map[k := t''.value]
                + toMapRec(t''.right)) - {k};
              (toMapRec(t''.left)
                + map[t''.key := t''.value]
                + toMapRec(t''.right)) - {k};
              toMapRec(t'') - {k};
              toMapRec(t') - {k};
              toMapRec(t) - {k};
            }
          }
        }
      }
    }
  }
}
