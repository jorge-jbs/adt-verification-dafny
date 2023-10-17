include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Base.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Restore.dfy"
include "../../../../src/tree/layer4/AltTRBTree/MoveRed.dfy"

module {:options "-functionSyntax:4"} TRBTree.RemoveMinMaintainingPrev {
  import opened KeyValue
  import opened Utils
  import opened Utils.Option
  import opened Utils.Printer
  import opened Color
  import opened Base
  import opened Res = Restore
  import opened MoveRed

  function RemoveMinMaintainingPrev(t: trbtreeOrThread, isLeft: bool): option<(trbtreeOrThread, K, V)>
    requires t.Node?
    decreases size(t)
  {
    match t.left
    case Empty|Thread(_) =>
      var _ :- Guard(t.right.Empty? || t.right.Thread?);
      if isLeft then
        Some((Thread(t.key), t.key, t.value))
      else
        Some((t.right, t.key, t.value))
    case Node(_, _, _, _, _) =>
      var t' :-
        if isBlack(t.left) && !isRed(t.left.left) then
          var _ :- Guard(t.right.Node?);
          MoveRedLeftSize(t);
          Some(MoveRedLeft(t))
        else
          Some(t);
      assert size(t'.left) < size(t) by {
        calc {
          size(t'.left);
          == size(t'.left);
          < size(t');
          == size(t);
        }
      }
      var (l', minK, minV) :- RemoveMinMaintainingPrev(t'.left, true);
      Some((Restore(Node(l', t'.key, t'.value, t'.right, t'.color)), minK, minV))
  }

  method {:main} RemoveMinMaintainingPrevTest1()
  {
    var t1 := ThreadedTreeExample1();
    var t1' := ConditionalReddenRoot(t1);
    assert ThreadedTreeRoot(t1);
    assert RedBlackTreeRoot(t1);
    assert SearchTree(t1);
    var (t2, minK, minV) := RemoveMinMaintainingPrev(t1', true).unwrap;
    var t2' := BlackenRoot(t2);
    assert minK == 1;
    print trbtreeToString(t1') + "\n\n";
    print trbtreeToString(t2') + "\n\n";
    assert ThreadedTreeNe(Thread(1), t2', Empty);
    //assert ThreadedTreeRoot(t2');
    assert RedBlackTree(t2');
    assert RedBlackTreeRoot(t2');
    assert SearchTree(t2');

/*
    //print trbtreeToString(Restore(Node(Child(Empty), 2, 0, Child(Node(Thread(2), 3, 0, Thread(4), Red)), Black))) + "\n\n";
    //print trbtreeToString(MoveRedLeft(t1')) + "\n\n";
    //print trbtreeToString(MoveRedLeft(MoveRedLeft(t1').left.child)) + "\n\n";

    calc == {
      RemoveMinMaintainingPrev(t1').unwrap.0;
      Child(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1').left).unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color)));
      Child(Restore(Node(Child(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(MoveRedLeft(t1').left.child).left).unwrap.0, MoveRedLeft(t1').left.child.key, MoveRedLeft(t1').left.child.value, MoveRedLeft(t1').left.child.right, MoveRedLeft(t1').left.child.color))), t1'.key, t1'.value, t1'.right, t1'.color)));
    }
    //print trbtreeToString(Restore(Node(MoveRedLeft(t1').left.unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color)));
    //print trbtreeToString(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1').left).unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color)) + "\n\n";
    //print trbtreeToString(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1').left).unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color))) + "\n\n";

    var t1'left' := MoveRedLeft(t1').left.child;
    print trbtreeToString(t1'left') + "\n\n";
    print trbtreeToString(RemoveMinMaintainingPrev(t1'left').unwrap.0.child) + "\n\n";
    print trbtreeToString(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1'left').left).unwrap.0, t1'left'.key, t1'left'.value, t1'left'.right, t1'left'.color)) + "\n\n";
    print trbtreeToString(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1'left').left).unwrap.0, t1'left'.key, t1'left'.value, t1'left'.right, t1'left'.color))) + "\n\n";

    calc == {
      RemoveMinMaintainingPrev(t1'left').unwrap.0;
      Child(Restore(Node(RemoveMinMaintainingPrevP(MoveRedLeft(t1'left').left).unwrap.0, t1'left'.key, t1'left'.value, t1'left'.right, t1'left'.color)));
    }

    var t1'leftleft' := MoveRedLeft(t1'left').left.child;
    print trbtreeToString(t1'leftleft') + "\n\n";
    print trbtreeToString(t2') + "\n\n";
    */
  }

  method RemoveMinMaintainingPrevTest2()
  {
    var t1 := ThreadedTreeExample1();
    var t1' := ConditionalReddenRoot(t1);
    print trbtreeToString(t1') + "\n\n";
    print trbtreeToString(RemoveMinMaintainingPrev(t1'.right, true).unwrap.0) + "\n\n";
  }

  lemma SetDiffComm<K>(r: set<K>, k: K, s: set<K>)
    requires k !in s
    ensures r - {k} + s == r + s - {k}
  {}

  lemma RemoveMinMaintainingPrevSpec(t: trbtreeOrThread, isLeft: bool)
    decreases size(t)

    requires t.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    requires isRed(t) || isRed(t.left)

    ensures RemoveMinMaintainingPrev(t, isLeft).Some?
    ensures keys(RemoveMinMaintainingPrev(t, isLeft).unwrap.0) == keys(t) - {RemoveMinMaintainingPrev(t, isLeft).unwrap.1}
    ensures RemoveMinMaintainingPrev(t, isLeft).unwrap.1 in keys(t)
    //ensures forall k | k in keys(t) :: RemoveMinMaintainingPrev(t, isLeft).unwrap.1 <= k
    ensures forall k | k in keys(RemoveMinMaintainingPrev(t, isLeft).unwrap.0) :: RemoveMinMaintainingPrev(t, isLeft).unwrap.1 < k

    ensures SearchTree(RemoveMinMaintainingPrev(t, isLeft).unwrap.0)
    ensures RedBlackTree(RemoveMinMaintainingPrev(t, isLeft).unwrap.0)
    ensures BlackHeight(RemoveMinMaintainingPrev(t, isLeft).unwrap.0) == BlackHeight(t)
    ensures isRed(RemoveMinMaintainingPrev(t, isLeft).unwrap.0) ==> !isRed(RemoveMinMaintainingPrev(t, isLeft).unwrap.0.left)
    ensures !isRed(t) ==> !isRed(RemoveMinMaintainingPrev(t, isLeft).unwrap.0)
  {
    if IsThreadOrEmpty(t.left) {
    } else {
      var pt' :=
        if isBlack(t.left) && !isRed(t.left.left) then
          var _ :- Guard(t.right.Node?);
          MoveRedLeftSize(t);
          Some(MoveRedLeft(t))
        else
          Some(t);
      assert pt'.Some?;
      var t' := pt'.unwrap;
      if isBlack(t.left) && !isRed(t.left.left) {
        MoveRedLeftSpec(t);
      }
      RemoveMinMaintainingPrevSpec(t'.left, true);
      assert RemoveMinMaintainingPrev(t'.left, true).Some?;
      assert forall m | m in keys(t'.left) :: m < t'.key;
      var (l', minK, minV) := RemoveMinMaintainingPrev(t'.left, true).unwrap;
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
        keys(RemoveMinMaintainingPrev(t, true).unwrap.0);
        keys(t''');
        keys(t'');
        keys(l') + {t'.key} + keys(t'.right);
        (keys(t'.left) - {minK} + {t'.key}) + keys(t'.right);
        { SetDiffComm(keys(t'.left), minK, {t'.key}); }
        (keys(t'.left) + {t'.key} - {minK}) + keys(t'.right);
        { SetDiffComm(keys(t'.left) + {t'.key}, minK, keys(t'.right)); }
        keys(t'.left) + {t'.key} + keys(t'.right) - {minK};
        keys(t') - {minK};
        keys(t) - {minK};
      }
    }
  }

  lemma RemoveMinMaintainingPrevThreaded(
      prev: threadOrEmpty, 
      t: trbtree, 
      next: threadOrEmpty, 
      isLeft: bool
    )
    decreases size(t)

    requires t.Node?
    requires ThreadedTreeNe(prev, t, next)
    requires RemoveMinMaintainingPrev(t, isLeft).Some?
    ensures ThreadedTreeRecCond(
      Thread(RemoveMinMaintainingPrev(t, isLeft).unwrap.1),
      RemoveMinMaintainingPrev(t, isLeft).unwrap.0,
      next,
      isLeft
    )
  {
    if t.left.Empty? || t.left.Thread? {
    } else {
      var pt' :=
        if isBlack(t.left) && !isRed(t.left.left) then
          var _ :- Guard(t.right.Node?);
          MoveRedLeftSize(t);
          Some(MoveRedLeft(t))
        else
          Some(t);
      assert pt'.Some?;
      var t' := pt'.unwrap;
      if isBlack(t.left) && !isRed(t.left.left) {
        MoveRedLeftThreaded(prev, t, next);
      }
      RemoveMinMaintainingPrevThreaded(prev, t'.left, Thread(t'.key), true);
      assert RemoveMinMaintainingPrev(t'.left, true).Some?;
      var (l', minK, minV) := RemoveMinMaintainingPrev(t'.left, true).unwrap;
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
