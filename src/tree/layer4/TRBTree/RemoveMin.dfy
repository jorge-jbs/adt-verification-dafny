include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"
include "../../../../src/tree/layer4/TRBTree/MoveRed.dfy"

module {:options "-functionSyntax:4"} TRBTree.RemoveMin {
  import opened KeyValue
  import opened Utils
  import opened Utils.Option
  import opened Utils.Printer
  import opened Color
  import opened Base
  import opened Res = Restore
  import opened MoveRed

  function RemoveMinP(p: pointer): option<(pointer, K, V)>
    requires p.Child?
    requires p.child.Node?
    decreases sizeWithPointersP(p)
  {
    RemoveMin(p.child)
  }

  function RemoveMin(t: rbtree): option<(pointer, K, V)>
    requires t.Node?
    decreases sizeWithPointers(t)
  {
    if IsThreadOrEmpty(t.left) then
      var _ :- Guard(t.right.Thread? || t.right == Child(Empty));
      Some((t.left, t.key, t.value))
    else
      var t' :-
        if isBlackP(t.left) && !isRedP(t.left.child.left) then
          var _ :- Guard(t.right.Child? && t.right.child.Node?);
          MoveRedLeftSize(t);
          Some(MoveRedLeft(t))
        else
          Some(t);
      var (l', minK, minV) :- RemoveMinP(t'.left);
      Some((Child(Restore(Node(l', t'.key, t'.value, t'.right, t'.color))), minK, minV))
  }

  method RemoveMinTest1()
  {
    var t1 := ThreadedTreeExample1();
    var t1' := ConditionalReddenRoot(t1);
    assert ThreadedTreeRoot(t1);
    assert RedBlackTreeRoot(t1);
    assert SearchTree(t1);
    var (t2, minK, minV) := RemoveMin(t1').unwrap;
    var t2' := BlackenRoot(t2.child);
    assert minK == 1;
    print rbtreeToString(t1') + "\n\n";
    print rbtreeToString(t2') + "\n\n";
    assert ThreadedTreeRoot(t2');
    assert RedBlackTree(t2');
    assert RedBlackTreeRoot(t2');
    assert SearchTree(t2');

/*
    //print rbtreeToString(Restore(Node(Child(Empty), 2, 0, Child(Node(Thread(2), 3, 0, Thread(4), Red)), Black))) + "\n\n";
    //print rbtreeToString(MoveRedLeft(t1')) + "\n\n";
    //print rbtreeToString(MoveRedLeft(MoveRedLeft(t1').left.child)) + "\n\n";

    calc == {
      RemoveMin(t1').unwrap.0;
      Child(Restore(Node(RemoveMinP(MoveRedLeft(t1').left).unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color)));
      Child(Restore(Node(Child(Restore(Node(RemoveMinP(MoveRedLeft(MoveRedLeft(t1').left.child).left).unwrap.0, MoveRedLeft(t1').left.child.key, MoveRedLeft(t1').left.child.value, MoveRedLeft(t1').left.child.right, MoveRedLeft(t1').left.child.color))), t1'.key, t1'.value, t1'.right, t1'.color)));
    }
    //print rbtreeToString(Restore(Node(MoveRedLeft(t1').left.unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color)));
    //print rbtreeToString(Node(RemoveMinP(MoveRedLeft(t1').left).unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color)) + "\n\n";
    //print rbtreeToString(Restore(Node(RemoveMinP(MoveRedLeft(t1').left).unwrap.0, t1'.key, t1'.value, t1'.right, t1'.color))) + "\n\n";

    var t1'left' := MoveRedLeft(t1').left.child;
    print rbtreeToString(t1'left') + "\n\n";
    print rbtreeToString(RemoveMin(t1'left').unwrap.0.child) + "\n\n";
    print rbtreeToString(Node(RemoveMinP(MoveRedLeft(t1'left').left).unwrap.0, t1'left'.key, t1'left'.value, t1'left'.right, t1'left'.color)) + "\n\n";
    print rbtreeToString(Restore(Node(RemoveMinP(MoveRedLeft(t1'left').left).unwrap.0, t1'left'.key, t1'left'.value, t1'left'.right, t1'left'.color))) + "\n\n";

    calc == {
      RemoveMin(t1'left').unwrap.0;
      Child(Restore(Node(RemoveMinP(MoveRedLeft(t1'left').left).unwrap.0, t1'left'.key, t1'left'.value, t1'left'.right, t1'left'.color)));
    }

    var t1'leftleft' := MoveRedLeft(t1'left').left.child;
    print rbtreeToString(t1'leftleft') + "\n\n";
    print rbtreeToString(t2') + "\n\n";
    */
  }

  method RemoveMinTest2()
  {
    var t1 := ThreadedTreeExample1();
    var t1' := ConditionalReddenRoot(t1);
    print rbtreeToString(t1') + "\n\n";
    print pointerToString(RemoveMin(t1'.right.child).unwrap.0) + "\n\n";
  }

  lemma RemoveMinPSpec(p: pointer)
    decreases sizeWithPointersP(p)

    requires p.Child?
    requires p.child.Node?
    requires SearchTree(p.child)
    requires RedBlackTree(p.child)
    requires !(isRed(p.child) && isRedP(p.child.left))
    requires isRed(p.child) || isRedP(p.child.left)
    
    ensures RemoveMinP(p).Some?
    ensures keysP(RemoveMinP(p).unwrap.0) == keys(p.child) - {RemoveMinP(p).unwrap.1}
    ensures RemoveMinP(p).unwrap.1 in keys(p.child)
    //ensures forall k | k in keys(p.child) :: RemoveMinP(p).unwrap.1 <= k
    ensures forall k | k in keysP(RemoveMinP(p).unwrap.0) :: RemoveMinP(p).unwrap.1 < k

    ensures SearchTreeP(RemoveMinP(p).unwrap.0)
    ensures RedBlackTreeP(RemoveMinP(p).unwrap.0)
    ensures BlackHeightP(RemoveMinP(p).unwrap.0) == BlackHeight(p.child)
    ensures isRedP(RemoveMinP(p).unwrap.0) ==> !isRedP(RemoveMinP(p).unwrap.0.child.left)
    ensures !isRed(p.child) ==> !isRedP(RemoveMinP(p).unwrap.0)
  {
    RemoveMinSpec(p.child);
  }

  lemma SetDiffComm<K>(r: set<K>, k: K, s: set<K>)
    requires k !in s
    ensures r - {k} + s == r + s - {k}
  {}

  lemma RemoveMinSpec(t: rbtree)
    decreases sizeWithPointers(t)

    requires t.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRedP(t.left))
    requires isRed(t) || isRedP(t.left)

    ensures RemoveMin(t).Some?
    ensures keysP(RemoveMin(t).unwrap.0) == keys(t) - {RemoveMin(t).unwrap.1}
    ensures RemoveMin(t).unwrap.1 in keys(t)
    //ensures forall k | k in keys(t) :: RemoveMin(t).unwrap.1 <= k
    ensures forall k | k in keysP(RemoveMin(t).unwrap.0) :: RemoveMin(t).unwrap.1 < k

    ensures SearchTreeP(RemoveMin(t).unwrap.0)
    ensures RedBlackTreeP(RemoveMin(t).unwrap.0)
    ensures BlackHeightP(RemoveMin(t).unwrap.0) == BlackHeight(t)
    ensures isRedP(RemoveMin(t).unwrap.0) ==> !isRedP(RemoveMin(t).unwrap.0.child.left)
    ensures !isRed(t) ==> !isRedP(RemoveMin(t).unwrap.0)
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
      RemoveMinPSpec(t'.left);
      assert RemoveMinP(t'.left).Some?;
      assert forall m | m in keysP(t'.left) :: m < t'.key;
      var (l', minK, minV) := RemoveMinP(t'.left).unwrap;
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
        keysP(RemoveMin(t).unwrap.0);
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
}
