include "../../../../src/tree/layer4/KeyValue.dfy"
include "../../../../src/tree/layer4/RBTree/Base.dfy"
include "../../../../src/tree/layer4/RBTree/RBInsert.dfy"

module RBTree.RBRemove {
  import opened KeyValue

  import opened Base
  import opened Color
  import opened RBInsert

  function method MoveRedLeft(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
  {
    var t' := FlipColors(t);
    if isRed(t'.right.left) then
      var t'' := Node(
        t'.left,
        t'.key,
        t'.value,
        RotateRight(t'.right),
        t'.color
      );
      FlipColors(RotateLeft(t''))
    else
      t'
  }

  lemma MoveRedLeftSpec(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires isRed(t)
    requires isBlack(t.left)
    requires isBlack(t.right)
    requires !isRed(t.left.left)
    ensures keys(t) == keys(FlipColors(t))
    ensures isRed(MoveRedLeft(t).left) || isRed(MoveRedLeft(t).left.left)
    ensures SearchTree(MoveRedLeft(t))
    ensures RedBlackTree(MoveRedLeft(t).left)
    ensures RedBlackTree(MoveRedLeft(t).right)
    //ensures BlackBalanced(MoveRedLeft(t))
    ensures BlackHeight(MoveRedLeft(t).right) == BlackHeight(MoveRedLeft(t).left)
    ensures BlackHeight(MoveRedLeft(t)) == BlackHeight(t)
    ensures size(MoveRedLeft(t)) == size(t)

    ensures
      || isRed(MoveRedLeft(t).left)
      || isRed(MoveRedLeft(t).left.left)
    ensures
      || (!isRed(MoveRedLeft(t)) && isRed(MoveRedLeft(t).left) && isRed(MoveRedLeft(t).right) && !isRed(MoveRedLeft(t).right.left) && !isRed(MoveRedLeft(t).left.left))
      || (isRed(MoveRedLeft(t)) && !isRed(MoveRedLeft(t).left) && !isRed(MoveRedLeft(t).right) && isRed(MoveRedLeft(t).left.left))

/*
    ensures MoveRedLeft(t).color.Red?;
    ensures MoveRedLeft(t).left.color.Black?;
    ensures MoveRedLeft(t).right.color.Black?;
    ensures MoveRedLeft(t).left.left.color.Red?;
    ensures !isRed(MoveRedLeft(t).left.left.left);

    ensures MoveRedLeft(t).left.left.left == t.left.left;
    ensures MoveRedLeft(t).left.left.right == t.left.right;
    ensures MoveRedLeft(t).left.right == t.right.left.left;
    ensures MoveRedLeft(t).right.left == t.right.left.right;
    ensures MoveRedLeft(t).right.right == t.right.right;
    */
  {
    assert size(MoveRedLeft(t)) == size(t) by {
      assert forall t | RotateRight.requires(t) :: size(t) == size(RotateRight(t));
      assert forall t | RotateLeft.requires(t) :: size(t) == size(RotateLeft(t));
      assert forall t | FlipColors.requires(t) :: size(t) == size(FlipColors(t));
    }
    /*
    AllFlipColorsSpec();
    AllRotateLeftSpec();
    AllRotateRightSpec();
    */
    var t' := FlipColors(t);
    FlipColorsSpec(t);
    if isRed(t'.right.left) {
      var t'' := Node(
        t'.left,
        t'.key,
        t'.value,
        RotateRight(t'.right),
        t'.color
      );
      RotateRightSpec(t'.right);
      RotateLeftSpec(t'');
      FlipColorsSpec(RotateLeft(t''));

      var t''' := FlipColors(RotateLeft(t''));
      assert t'''.color.Red?;
      assert t'''.left.color.Black?;
      assert t'''.right.color.Black?;
      assert t'''.left.left.color.Red?;
      assert !isRed(t'''.left.left.left);

      assert t'''.left.left.left == t.left.left;
      assert t'''.left.left.right == t.left.right;
      assert t'''.left.right == t.right.left.left;
      assert t'''.right.left == t.right.left.right;
      assert t'''.right.right == t.right.right;

      assert (t'''.left.right.Node? ==> t'''.left.right.color.Black?);
      assert (t'''.left.left.Node? && t'''.left.left.color.Red? && t'''.left.left.left.Node? ==> t'''.left.left.left.color.Black?);

      assert RedBlackTree(t.left.left);
      assert RedBlackTree(t.left.right);
      assert RedBlackTree(t.right.left);
      assert RedBlackTree(t.right.right);
    } else {
    }
  }

  lemma MoveRedLeftModel(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires isRed(t)
    requires isBlack(t.left)
    requires isBlack(t.right)
    requires !isRed(t.left.left)

    ensures SearchTree(MoveRedLeft(t))
    ensures toMap(MoveRedLeft(t)) == toMap(t)
  {
    MoveRedLeftSpec(t);
    var t' := FlipColors(t);
    FlipColorsSpec(t);
    FlipColorsModel(t);
    if isRed(t'.right.left) {
      var t'' := Node(
        t'.left,
        t'.key,
        t'.value,
        RotateRight(t'.right),
        t'.color
      );
      RotateRightSpec(t'.right);
      RotateRightModel(t'.right);
      RotateLeftSpec(t'');
      RotateLeftModel(t'');
      FlipColorsSpec(RotateLeft(t''));
      FlipColorsModel(RotateLeft(t''));
      calc == {
        toMap(MoveRedLeft(t));
        toMap(FlipColors(RotateLeft(t'')));
        toMap(RotateLeft(t''));
        toMap(t'');
        { toMapLemmas(t''); }
        toMap(t'.left) + map[t'.key := t'.value] + toMap(RotateRight(t'.right));
        toMap(t'.left) + map[t'.key := t'.value] + toMap(t'.right);
        { toMapLemmas(t'); }
        toMap(t');
        toMap(t);
      }
    } else {
    }
  }

  function method MoveRedRight(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
  {
    var t' := FlipColors(t);
    if isRed(t'.left.left) then
      var t'' := FlipColors(RotateRight(t'));
      Node(
        t''.left,
        t''.key,
        t''.value,
        RotateLeft(t''.right),
        t''.color
      )
    else
      t'
  }

  lemma MoveRedRightSpec(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires isRed(t)
    requires isBlack(t.left)
    requires isBlack(t.right)
    requires !isRed(t.right.left)
    ensures keys(t) == keys(FlipColors(t))
    ensures isRed(MoveRedRight(t).right) || isRed(MoveRedRight(t).right.left)
    ensures SearchTree(MoveRedRight(t))
    ensures RedBlackTree(MoveRedRight(t).left)
    ensures RedBlackTree(MoveRedRight(t).right)
    ensures BlackHeight(MoveRedRight(t).right) == BlackHeight(MoveRedRight(t).left)
    ensures BlackHeight(MoveRedRight(t)) == BlackHeight(t)
    ensures size(MoveRedRight(t)) == size(t)
  {
    assert size(MoveRedRight(t)) == size(t) by {
      assert forall t | RotateRight.requires(t) :: size(t) == size(RotateRight(t));
      assert forall t | RotateLeft.requires(t) :: size(t) == size(RotateLeft(t));
      assert forall t | FlipColors.requires(t) :: size(t) == size(FlipColors(t));
    }
    var t' := FlipColors(t);
    FlipColorsSpec(t);
    if isRed(t'.left.left) {
      var t'' := FlipColors(RotateRight(t'));
      var t''' :=
        Node(
          t''.left,
          t''.key,
          t''.value,
          RotateLeft(t''.right),
          t''.color
        );
      RotateRightSpec(t');
      FlipColorsSpec(RotateRight(t'));
      RotateLeftSpec(t''.right);

      assert RedBlackTree(t.left.left);
      assert RedBlackTree(t.left.right);
      assert RedBlackTree(t.right.left);
      assert RedBlackTree(t.right.right);
    }
  }

  lemma MoveRedRightModel(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires isRed(t)
    requires isBlack(t.left)
    requires isBlack(t.right)
    requires !isRed(t.right.left)

    ensures SearchTree(MoveRedRight(t))
    ensures toMap(MoveRedRight(t)) == toMap(t)
  {
    MoveRedRightSpec(t);
    var t' := FlipColors(t);
    FlipColorsSpec(t);
    FlipColorsModel(t);
    if isRed(t'.left.left) {
      var t'' := FlipColors(RotateRight(t'));
      var t''' :=
        Node(
          t''.left,
          t''.key,
          t''.value,
          RotateLeft(t''.right),
          t''.color
        );
      RotateRightSpec(t');
      RotateRightModel(t');
      FlipColorsSpec(RotateRight(t'));
      FlipColorsModel(RotateRight(t'));
      RotateLeftSpec(t''.right);
      RotateLeftModel(t''.right);
      calc == {
        toMap(MoveRedRight(t));
        toMap(t''');
        { toMapLemmas(t'''); }
        toMap(t''.left) + map[t''.key := t''.value] + toMap(RotateLeft(t''.right));
        toMap(t''.left) + map[t''.key := t''.value] + toMap(t''.right);
        { toMapLemmas(t''); }
        toMap(t'');
        toMap(t');
        toMap(t);
      }
    }
  }

  function method RemoveMin(t: rbtree): (rbtree, K, V)
    decreases size(t)
    requires t.Node?
    requires isRed(t) || isRed(t.left)
    requires SearchTree(t)
    requires RedBlackTree(t)
  {
    if t.left.Empty? then
      (t.right, t.key, t.value)
    else
      var t' :=
        if isBlack(t.left) && !isRed(t.left.left) then
          MoveRedLeftSpec(t);
          MoveRedLeft(t)
        else
          t;
      var (l', minK, minV) := RemoveMin(t'.left);
      ( Restore(
          Node(
            l',
            t'.key,
            t'.value,
            t'.right,
            t'.color
          )
        )
      , minK
      , minV
      )
  }

  lemma RemoveMinSpec(t: rbtree)  // 35"
    decreases size(t)

    requires t.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    requires isRed(t) || isRed(t.left)

    ensures keys(RemoveMin(t).0) == keys(t) - {RemoveMin(t).1}
    ensures RemoveMin(t).1 in keys(t)
    //ensures forall k | k in keys(t) :: RemoveMin(t).1 <= k
    ensures forall k | k in keys(RemoveMin(t).0) :: RemoveMin(t).1 < k

    ensures SearchTree(RemoveMin(t).0)
    ensures RedBlackTree(RemoveMin(t).0)
    ensures BlackHeight(RemoveMin(t).0) == BlackHeight(t)
    ensures isRed(RemoveMin(t).0) ==> !isRed(RemoveMin(t).0.left)
    ensures !isRed(t) ==> !isRed(RemoveMin(t).0)
  {
    if t.left.Empty? {
    } else {
      var t' :=
        if isBlack(t.left) && !isRed(t.left.left) then
          MoveRedLeftSpec(t);
          MoveRedLeft(t)
        else
          t;
      if isBlack(t.left) && !isRed(t.left.left) {
        MoveRedLeftSpec(t);
      }
      RemoveMinSpec(t'.left);
      var (l', minK, minV) := RemoveMin(t'.left);
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
        keys(RemoveMin(t).0);
        keys(t''');
        keys(t'');
        keys(l') + {t'.key} + keys(t'.right);
        (keys(t'.left) - {minK}) + {t'.key} + keys(t'.right);
        keys(t'.left) - {minK} + {t'.key} + keys(t'.right);
        { assert minK != t'.key && minK !in keys(t'.right); }
        keys(t'.left) + {t'.key} + keys(t'.right) - {minK};
        keys(t') - {minK};
        keys(t) - {minK};
      }
    }
  }

  lemma MapDiffComm(m: map<K, V>, k: K, p: map<K, V>)
    requires k !in p
    ensures m - {k} + p == m + p - {k}
  {}

  lemma MapDiffAssoc(m: map<K, V>, p: map<K, V>, k: K)
    requires k !in m
    ensures m + (p - {k}) == (m + p) - {k}
  {}

  lemma MapDiffCancel(k: K, v: V, m: map<K, V>)
    requires k in m
    requires m[k] == v
    ensures map[k := v] + (m - {k}) == m
  {}

  lemma RemoveMinModel(t: rbtree)
    decreases size(t)

    requires t.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    requires isRed(t) || isRed(t.left)

    ensures SearchTree(RemoveMin(t).0)
    ensures toMap(RemoveMin(t).0) == toMap(t) - {RemoveMin(t).1}
    ensures RemoveMin(t).1 in toMap(t)
    ensures toMap(t)[RemoveMin(t).1] == RemoveMin(t).2
  {
    RemoveMinSpec(t);
    if t.left.Empty? {
    } else {
      var t' :=
        if isBlack(t.left) && !isRed(t.left.left) then
          MoveRedLeftSpec(t);
          MoveRedLeft(t)
        else
          t;
      if isBlack(t.left) && !isRed(t.left.left) {
        MoveRedLeftModel(t);
      }
      assert toMap(t) == toMap(t');
      RemoveMinModel(t'.left);
      var (l', minK, minV) := RemoveMin(t'.left);
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
      RestoreModel(t'');
      calc == {
        toMap(RemoveMin(t).0);
        toMap(t''');
        toMap(t'');
        { toMapLemmas(t''); }
        toMap(l') + map[t'.key := t'.value] + toMap(t'.right);
        (toMap(t'.left) - {minK}) + map[t'.key := t'.value] + toMap(t'.right);
        toMap(t'.left) - {minK} + map[t'.key := t'.value] + toMap(t'.right);
        { MapDiffComm(toMap(t'.left), minK, map[t'.key := t'.value]); }
        (toMap(t'.left) + map[t'.key := t'.value]) - {minK} + toMap(t'.right);
        { MapDiffComm(toMap(t'.left) + map[t'.key := t'.value], minK, toMap(t'.right)); }
        //{ MapSubMove(toMap(t'.left), minK, map[t'.key := t'.value] + toMap(t'.right)); }
        toMap(t'.left) + map[t'.key := t'.value] + toMap(t'.right) - {minK};
        { toMapLemmas(t'); }
        toMap(t') - {minK};
        toMap(t) - {minK};
      }
    }
  }

  function method Remove(t: rbtree, k: K): rbtree
    decreases size(t)
    requires t.Empty? || isRed(t) || isRed(t.left)
    requires SearchTree(t)
    requires RedBlackTree(t)
  {
    if t.Empty? then
      t
    else
      if t.key > k then
        var t' :=
          if isBlack(t.left) && !isRed(t.left.left) then
            MoveRedLeftSpec(t);
            MoveRedLeft(t)
          else
            t;
        Restore(
          Node(
            Remove(t'.left, k),
            t'.key,
            t'.value,
            t'.right,
            t'.color
          )
        )
        else
          var t' :=
            if isRed(t.left) then
              RotateRightSpec(t);
              RotateRight(t)
            else
              t;
          if k == t'.key && t'.right.Empty? then
            t'.left
          else
            var t'' :=
              if isBlack(t'.right) && !isRed(t'.right.left) then
                MoveRedRightSpec(t');
                MoveRedRight(t')
              else
                t';
            if k != t''.key then
              Restore(
                Node(
                  t''.left,
                  t''.key,
                  t''.value,
                  Remove(t''.right, k),
                  t''.color
                )
              )
            else
              var (r', minK, minV) := RemoveMin(t''.right);
              Restore(
                Node(
                  t''.left,
                  minK,
                  minV,
                  r',
                  t''.color
                )
              )
  }

  lemma RemoveSpec(t: rbtree, k: K)  // 45"
    decreases size(t)

    requires SearchTree(t)
    requires RedBlackTree(t)
    requires t.Empty? || isRed(t) || isRed(t.left)
    requires !(isRed(t) && isRed(t.left))

    ensures SearchTree(Remove(t, k))
    ensures RedBlackTree(Remove(t, k))
    ensures BlackHeight(Remove(t, k)) == BlackHeight(t)
    ensures isRed(Remove(t, k)) ==> !isRed(Remove(t, k).left)
    ensures !isRed(t) ==> !isRed(Remove(t, k))

    ensures keys(Remove(t, k)) == keys(t) - {k}

/*
    ensures elems(Remove(t, k)) == elems(t) - {removedNode}
    ensures removedNode != null ==>
      && removedNode in elems(t)
      && removedNode !in elems(Remove(t, k))
      && removedNode.key == k
    //ensures k !in old(Model(t)) <==> removedNode==null
    //ensures Model(Remove(t, k))==old(Model(t))-{k}
    */
  {
    if t.Empty? {
    } else {
      if t.key > k {  // 7"
        var t' :=
          if isBlack(t.left) && !isRed(t.left.left) then
            MoveRedLeftSpec(t);
            MoveRedLeft(t)
          else
            t;
        var l' := Remove(t'.left, k);
        RemoveSpec(t'.left, k);
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
            RotateRightSpec(t);
            RotateRight(t)
          else
            t;
        if k == t'.key && t'.right.Empty? {
        } else {
          var t'' :=
            if isBlack(t'.right) && !isRed(t'.right.left) then
              MoveRedRightSpec(t');
              MoveRedRight(t')
            else
              t';
          if k != t''.key {  // 11"
            var t''' :=
              Node(
                t''.left,
                t''.key,
                t''.value,
                Remove(t''.right, k),
                t''.color
              );
            RemoveSpec(t''.right, k);
            var t'''' := Restore(t''');
            RestoreSpec(t''');
          } else {  // 7"
            var (r', minK, minV) := RemoveMin(t''.right);
            RemoveMinSpec(t''.right);
            var t''' :=
              Node(
                t''.left,
                minK,
                minV,
                r',
                t''.color
              );
            var t'''' := Restore(t''');
            RestoreSpec(t''');
          }
        }
      }
    }
  }

  lemma RemoveModel(t: rbtree, k: K)  // 33"
    decreases size(t)

    requires SearchTree(t)
    requires RedBlackTree(t)
    requires t.Empty? || isRed(t) || isRed(t.left)
    requires !(isRed(t) && isRed(t.left))

    ensures SearchTree(Remove(t, k))
    ensures toMap(Remove(t, k)) == toMap(t) - {k}
  {
    RemoveSpec(t, k);
    if t.Empty? {
    } else {
      if t.key > k {
        var t' :=
          if isBlack(t.left) && !isRed(t.left.left) then
            MoveRedLeftSpec(t);
            MoveRedLeft(t)
          else
            t;
        if isBlack(t.left) && !isRed(t.left.left) {
          MoveRedLeftModel(t);
        }
        var l' := Remove(t'.left, k);
        RemoveSpec(t'.left, k);
        RemoveModel(t'.left, k);
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
        RestoreModel(t'');
        calc == {
          toMap(Remove(t, k));
          toMap(t''');
          toMap(t'');
          { toMapLemmas(t''); }
          toMap(Remove(t'.left, k)) + map[t'.key := t'.value] + toMap(t'.right);
          toMap(t'.left) - {k} + map[t'.key := t'.value] + toMap(t'.right);
          { MapDiffComm(toMap(t'.left), k, map[t'.key := t'.value]); }
          toMap(t'.left) + map[t'.key := t'.value] - {k} + toMap(t'.right);
          { MapDiffComm(toMap(t'.left) + map[t'.key := t'.value], k, toMap(t'.right)); }
          toMap(t'.left) + map[t'.key := t'.value] + toMap(t'.right) - {k};
          { toMapLemmas(t'); }
          toMap(t') - {k};
          toMap(t) - {k};
        }
      } else {
        var t' :=
          if isRed(t.left) then
            RotateRightSpec(t);
            RotateRight(t)
          else
            t;
        if isRed(t.left) {
          RotateRightModel(t);
        }
        if k == t'.key && t'.right.Empty? {
        } else {
          var t'' :=
            if isBlack(t'.right) && !isRed(t'.right.left) then
              MoveRedRightSpec(t');
              MoveRedRight(t')
            else
              t';
          if isBlack(t'.right) && !isRed(t'.right.left) {
            MoveRedRightModel(t');
          }
          if k != t''.key {
            var t''' :=
              Node(
                t''.left,
                t''.key,
                t''.value,
                Remove(t''.right, k),
                t''.color
              );
            RemoveSpec(t''.right, k);
            RemoveModel(t''.right, k);
            var t'''' := Restore(t''');
            RestoreSpec(t''');
            RestoreModel(t''');
            calc == {
              toMap(Remove(t, k));
              toMap(t'''');
              toMap(t''');
              { toMapLemmas(t'''); }
              toMap(t''.left) + map[t''.key := t''.value] + toMap(Remove(t''.right, k));
              toMap(t''.left) + map[t''.key := t''.value] + (toMap(t''.right) - {k});
              { MapDiffAssoc(toMap(t''.left) + map[t''.key := t''.value], toMap(t''.right), k); }
              (toMap(t''.left) + map[t''.key := t''.value] + toMap(t''.right)) - {k};
              { toMapLemmas(t''); }
              toMap(t'') - {k};
              toMap(t') - {k};
              toMap(t) - {k};
            }
          } else {
            var (r', minK, minV) := RemoveMin(t''.right);
            RemoveMinSpec(t''.right);
            RemoveMinModel(t''.right);
            var t''' :=
              Node(
                t''.left,
                minK,
                minV,
                r',
                t''.color
              );
            var t'''' := Restore(t''');
            RestoreSpec(t''');
            RestoreModel(t''');
            calc == {
              toMap(Remove(t, k));
              toMap(t'''');
              toMap(t''');
              { toMapLemmas(t'''); }
              toMap(t''.left) + map[minK := minV] + toMap(r');
              toMap(t''.left) + map[minK := minV] + (toMap(t''.right) - {minK});
              toMap(t''.left) + (map[minK := minV] + (toMap(t''.right) - {minK}));
              { assert minK in toMap(t''.right); assert toMap(t''.right)[minK] == minV; MapDiffCancel(minK, minV, toMap(t''.right)); }
              toMap(t''.left) + toMap(t''.right);
            }
          }
        }
      }
    }
  }

  function method ReddenRoot(t: rbtree): rbtree
  {
    match t {
      case Empty => Empty
      case Node(l, k, v, r, c) =>
        if l.Node? && l.color.Red? then
          Node(l, k, v, r, c)
        else
          Node(l, k, v, r, Red)
    }
  }

  function method RemoveRoot(t: rbtree, k: K): rbtree
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
  {
    BlackenRoot(Remove(ReddenRoot(t), k))
  }

  lemma RemoveRootSpec(t: rbtree, k: K)
    decreases size(t)

    requires SearchTree(t)
    requires RedBlackTreeRoot(t)

    ensures SearchTree(RemoveRoot(t, k))
    ensures RedBlackTreeRoot(RemoveRoot(t, k))
    ensures keys(RemoveRoot(t, k)) == keys(t) - {k}
  {
    RemoveSpec(ReddenRoot(t), k);
  }
  
  lemma RemoveRootModel(t: rbtree, k: K)
    decreases size(t)

    requires SearchTree(t)
    requires RedBlackTreeRoot(t)

    ensures SearchTree(RemoveRoot(t, k))
    ensures toMap(RemoveRoot(t, k)) == toMap(t) - {k}
  {
    RemoveModel(ReddenRoot(t), k);
  }
}
