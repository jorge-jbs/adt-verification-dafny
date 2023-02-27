include "../../../../src/tree/alt-layer4/KeyValue.dfy"
include "../../../../src/tree/alt-layer4/RBTree/Base.dfy"
include "../../../../src/tree/alt-layer4/RBTree/RBInsert.dfy"

module RBTree.RBRemove {
  import opened KeyValue

  import opened Base
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
    ensures model(MoveRedLeft(t)) == model(t)
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
        model(MoveRedLeft(t));
        model(FlipColors(RotateLeft(t'')));
        model(RotateLeft(t''));
        model(t'');
        { modelLemmas(t''); }
        model(t'.left) + map[t'.key := t'.value] + model(RotateRight(t'.right));
        model(t'.left) + map[t'.key := t'.value] + model(t'.right);
        { modelLemmas(t'); }
        model(t');
        model(t);
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
    ensures model(MoveRedRight(t)) == model(t)
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
        model(MoveRedRight(t));
        model(t''');
        { modelLemmas(t'''); }
        model(t''.left) + map[t''.key := t''.value] + model(RotateLeft(t''.right));
        model(t''.left) + map[t''.key := t''.value] + model(t''.right);
        { modelLemmas(t''); }
        model(t'');
        model(t');
        model(t);
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
    ensures model(RemoveMin(t).0) == model(t) - {RemoveMin(t).1}
    ensures RemoveMin(t).1 in model(t)
    ensures model(t)[RemoveMin(t).1] == RemoveMin(t).2
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
      assert model(t) == model(t');
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
        model(RemoveMin(t).0);
        model(t''');
        model(t'');
        { modelLemmas(t''); }
        model(l') + map[t'.key := t'.value] + model(t'.right);
        (model(t'.left) - {minK}) + map[t'.key := t'.value] + model(t'.right);
        model(t'.left) - {minK} + map[t'.key := t'.value] + model(t'.right);
        { MapDiffComm(model(t'.left), minK, map[t'.key := t'.value]); }
        (model(t'.left) + map[t'.key := t'.value]) - {minK} + model(t'.right);
        { MapDiffComm(model(t'.left) + map[t'.key := t'.value], minK, model(t'.right)); }
        //{ MapSubMove(model(t'.left), minK, map[t'.key := t'.value] + model(t'.right)); }
        model(t'.left) + map[t'.key := t'.value] + model(t'.right) - {minK};
        { modelLemmas(t'); }
        model(t') - {minK};
        model(t) - {minK};
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
    ensures model(Remove(t, k)) == model(t) - {k}
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
          model(Remove(t, k));
          model(t''');
          model(t'');
          { modelLemmas(t''); }
          model(Remove(t'.left, k)) + map[t'.key := t'.value] + model(t'.right);
          model(t'.left) - {k} + map[t'.key := t'.value] + model(t'.right);
          { MapDiffComm(model(t'.left), k, map[t'.key := t'.value]); }
          model(t'.left) + map[t'.key := t'.value] - {k} + model(t'.right);
          { MapDiffComm(model(t'.left) + map[t'.key := t'.value], k, model(t'.right)); }
          model(t'.left) + map[t'.key := t'.value] + model(t'.right) - {k};
          { modelLemmas(t'); }
          model(t') - {k};
          model(t) - {k};
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
              model(Remove(t, k));
              model(t'''');
              model(t''');
              { modelLemmas(t'''); }
              model(t''.left) + map[t''.key := t''.value] + model(Remove(t''.right, k));
              model(t''.left) + map[t''.key := t''.value] + (model(t''.right) - {k});
              { MapDiffAssoc(model(t''.left) + map[t''.key := t''.value], model(t''.right), k); }
              (model(t''.left) + map[t''.key := t''.value] + model(t''.right)) - {k};
              { modelLemmas(t''); }
              model(t'') - {k};
              model(t') - {k};
              model(t) - {k};
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
              model(Remove(t, k));
              model(t'''');
              model(t''');
              { modelLemmas(t'''); }
              model(t''.left) + map[minK := minV] + model(r');
              model(t''.left) + map[minK := minV] + (model(t''.right) - {minK});
              model(t''.left) + (map[minK := minV] + (model(t''.right) - {minK}));
              { assert minK in model(t''.right); assert model(t''.right)[minK] == minV; MapDiffCancel(minK, minV, model(t''.right)); }
              model(t''.left) + model(t''.right);
            }
          }
        }
      }
    }
  }
}
