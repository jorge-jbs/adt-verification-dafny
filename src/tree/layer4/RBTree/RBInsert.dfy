include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/RBTree/Base.dfy"

module RBTree.RBInsert {
  //import opened Utils
  import opened KeyValue
  import opened Color
  import opened Base

  function method FlipColors(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
  {
    Node(
      Node(t.left.left, t.left.key, t.left.value, t.left.right, NegColor(t.left.color)),
      t.key,
      t.value,
      Node(t.right.left, t.right.key, t.right.value, t.right.right, NegColor(t.right.color)),
      NegColor(t.color)
    )
  }

  function method RotateLeft(t: rbtree): rbtree
    requires t.Node?
    requires t.right.Node?
  {
    Node(
      Node(t.left, t.key, t.value, t.right.left, Red),
      t.right.key,
      t.right.value,
      t.right.right,
      t.color
    )
  }

  function method RotateRight(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Node?
  {
    Node(
      t.left.left,
      t.left.key,
      t.left.value,
      Node(t.left.right, t.key, t.value, t.right, Red),
      t.color
    )
  }

  function method Restore(t: rbtree): rbtree
    requires t.Node?
  {
    var t' :=
      if isRed(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRed(t'.left) && isRed(t'.left.left) then
        RotateRight(t')
      else
        t';
    if isRed(t''.left) && isRed(t''.right) then
      FlipColors(t'')
    else
      t''
  }

  function method RBInsert(t: rbtree, k': K, v': V): rbtree
  {
    match t {
      case Empty => Node(Empty, k', v', Empty, Red)
      case Node(l, k, v, r, c) =>
        if k < k' then
          Restore(Node(l, k, v, RBInsert(r, k', v'), c))
        else if k' < k then
          Restore(Node(RBInsert(l, k', v'), k, v, r, c))
        else
          Node(l, k, v', r, c)
    }
  }

  function method BlackenRoot(t: rbtree): rbtree
  {
    match t {
      case Empty => Empty
      case Node(l, k, v, r, c) =>
        Node(l, k, v, r, Black)
    }
  }

  function method RBInsertRoot(t: rbtree, k: K, v: V): rbtree
  {
    BlackenRoot(RBInsert(t, k, v))
  }

  lemma {:verify true} FlipColorsSpec(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires t.left.color == NegColor(t.color)
    requires t.right.color == NegColor(t.color)
    requires SearchTree(t)
    //requires BlackBalanced(t)
    ensures keys(t) == keys(FlipColors(t))
    ensures SearchTree(FlipColors(t))
    //ensures BlackBalanced(FlipColors(t))
    ensures BlackHeight(t) == BlackHeight(FlipColors(t))

    ensures RotateRight(t).color == t.color
    ensures RotateRight(t).right.color == Red
  {}

  lemma {:verify true} RotateLeftSpec(t: rbtree)
    requires t.Node?
    requires isRed(t.right)
    requires SearchTree(t)
    ensures keys(t) == keys(RotateLeft(t))
    ensures SearchTree(RotateLeft(t))
    ensures BlackHeight(RotateLeft(t)) == BlackHeight(t)
  {}

  lemma {:verify true} RotateRightSpec(t: rbtree)
    requires t.Node?
    requires isRed(t.left)
    requires SearchTree(t)
    ensures keys(t) == keys(RotateRight(t))
    ensures SearchTree(RotateRight(t))
    ensures BlackHeight(RotateRight(t)) == BlackHeight(t)
    ensures RedBlackTree(t) ==>
      && RedBlackTree(RotateRight(t).left)
      && RedBlackTree(RotateRight(t).right)
    ensures size(RotateRight(t)) == size(t)
  {
    if RedBlackTree(t) {
      assert RedBlackTree(t.left);
    }
  }

  lemma {:verify true} AllFlipColorsSpec()
    ensures forall t: rbtree
        | t.Node?
        && t.left.Node?
        && t.right.Node?
        && t.left.color == NegColor(t.color)
        && t.right.color == NegColor(t.color)
        && SearchTree(t)
      :: keys(t) == keys(FlipColors(t))
      && SearchTree(FlipColors(t))
      && BlackHeight(t) == BlackHeight(FlipColors(t))
  {}

  lemma {:verify true} AllRotateLeftSpec()
    ensures forall t: rbtree
        | t.Node?
        && isRed(t.right)
        && SearchTree(t)
        && RedBlackTree(t)
      :: keys(t) == keys(RotateLeft(t))
      && SearchTree(RotateLeft(t))
      && BlackHeight(RotateLeft(t)) == BlackHeight(t)
  {}

  lemma {:verify true} AllRotateRightSpec()
    ensures forall t: rbtree
        | t.Node?
        && isRed(t.left)
        && SearchTree(t)
      :: keys(t) == keys(RotateRight(t))
      && SearchTree(RotateRight(t))
      && BlackHeight(RotateRight(t)) == BlackHeight(t)
  {}

  lemma RestoreSpec(t: rbtree)
    requires t.Node?
    requires SearchTree(t)
    requires isRed(t.right) && isRed(t.right.left) ==>
      isBlack(t) && isRed(t.left)
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.right)
    )
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.left.left)
    )
    requires BlackHeight(t.left) == BlackHeight(t.right)
    requires RedBlackTree(t.left)
    requires RedBlackTree(t.right)

    ensures keys(t) == keys(Restore(t))
    ensures SearchTree(Restore(t))
    ensures RedBlackTree(Restore(t))

    ensures BlackHeight(Restore(t)) == BlackHeight(t)
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRed(Restore(t).left)
    ensures isRed(t) ==> isRed(Restore(t))
    ensures isRed(Restore(t)) && isRed(Restore(t).left) ==>
      isRed(t) && (isRed(t.left) || isRed(t.right))
    ensures isRed(Restore(t)) && isBlack(t) ==>
      || (isRed(t.left) && isRed(t.right))
      || (isRed(t.left) && isRed(t.left.left))
  {
    /*
    var t' :=
      if isRed(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRed(t'.left) && isRed(t'.left.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRed(t''.left) && isRed(t''.right) then
        FlipColors(t'')
      else
        t'';


    if isRed(t.right) {
      assert !(
        && isRed(t')
        && isRed(t'.left)
        && isRed(t'.left.left));
      assert RedBlackTree(t'.right);
      assert t'.left.right == t.right.left;
      assert t'.left.right.Node? ==>
        t'.left.right.color == t.right.left.color;
      assert !isRed(t'.left.right) || (
        && isBlack(t)
        && isRed(t.left)
        && isRed(t.right)
        && isRed(t.right.left)
      );
    } else {
      assert RedBlackTree(t'.left);
      assert RedBlackTree(t'.right);
    }

    /*
    assert !(
      && isRed(t')
      && isRed(t'.left)
      && isRed(t'.right));

    assert !isRed(t'.right);
    assert RedBlackTree(t'.right);
    if t'.left.Node? {
      assert RedBlackTree(t'.left.left);
      assert RedBlackTree(t'.left.right);
    }
    */

    if isRed(t'.left) && isRed(t'.left.left) {
      assert isRed(t''.left);
      assert isRed(t''.right);
      assert !isRed(t'');
      assert RedBlackTree(t''.right);
      assert RedBlackTree(t''.left);
    } else {
      assert RedBlackTree(t''.right);
      if t''.left.Node? {
        assert RedBlackTree(t''.left.left);
        assert RedBlackTree(t''.left.right);
        assert BlackHeight(t''.left.left) == BlackHeight(t''.left.right);
        assert (t''.left.left.Node? && t''.left.left.color.Red? && t''.left.left.left.Node? ==> t''.left.left.left.color.Black?);
        assert (t''.left.right.Node? ==> t''.left.right.color.Black?) by {
          if t''.left.right.Node? {
            assert t''.left.right == t''.left.right;
            assert !isRed(t''.left.right);
          }
        }
      }
    }

    assert BlackHeight(t''') == BlackHeight(t);
    assert RedBlackTree(t''') by {
      assert t'''.right.Node? ==> t'''.right.color.Black? by {
        assert !isRed(t'''.right);
      }
      assert t'''.left.Node? && t'''.left.color.Red? && t'''.left.left.Node?
          ==> t'''.left.left.color.Black? by {
        if t'''.left.Node? {
          assert !(isRed(t'''.left) && isRed(t'''.left.left));
        }
      }
      assert BlackHeight(t'''.left) == BlackHeight(t'''.right);
      assert RedBlackTree(t'''.left);
      assert RedBlackTree(t'''.right);
    }
    */
  }

  lemma RBInsertSpec(t: rbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRed(Restore(t).left)
    ensures keys(t) + {k'} == keys(RBInsert(t, k', v'))
    ensures SearchTree(RBInsert(t, k', v'))
    ensures RedBlackTree(RBInsert(t, k', v'))
    ensures BlackHeight(t) == BlackHeight(RBInsert(t, k', v'))
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          RBInsertSpec(l, k, v);
          RestoreSpec(Node(l, k, v, RBInsert(r, k', v'), c));
        } else if k' < k {
          RBInsertSpec(r, k, v);
          RestoreSpec(Node(RBInsert(l, k', v'), k, v, r, c));
        } else {
        }
      }
    }
  }

  // 58"
  lemma FlipColorsModel(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires SearchTree(FlipColors(t))
    ensures model(t) == model(FlipColors(t))
  {
    calc == {
      model(FlipColors(t));
      model(
        Node(
          Node(t.left.left, t.left.key, t.left.value, t.left.right, NegColor(t.left.color)),
          t.key,
          t.value,
          Node(t.right.left, t.right.key, t.right.value, t.right.right, NegColor(t.right.color)),
          NegColor(t.color)
        )
      );
      model(Node(t.left.left, t.left.key, t.left.value, t.left.right, NegColor(t.left.color)))
        + map[t.key := t.value]
        + model(Node(t.right.left, t.right.key, t.right.value, t.right.right, NegColor(t.right.color)));
      model(t.left.left) + map[t.left.key := t.left.value] + model(t.left.right)
        + map[t.key := t.value]
        + model(t.right.left) + map[t.right.key := t.right.value] + model(t.right.right);
      model(Node(t.left.left, t.left.key, t.left.value, t.left.right, t.left.color))
        + map[t.key := t.value]
        + model(Node(t.right.left, t.right.key, t.right.value, t.right.right, t.right.color));
      model(
        Node(
          Node(t.left.left, t.left.key, t.left.value, t.left.right, t.left.color),
          t.key,
          t.value,
          Node(t.right.left, t.right.key, t.right.value, t.right.right, t.right.color),
          t.color
        )
      );
      model(t);
    }
  }

  lemma RotateLeftModel(t: rbtree)
    requires t.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires SearchTree(RotateLeft(t))
    ensures model(t) == model(RotateLeft(t))
  {
    calc == {
      model(RotateLeft(t));
      model(
        Node(
          Node(t.left, t.key, t.value, t.right.left, Red),
          t.right.key,
          t.right.value,
          t.right.right,
          t.color
        )
      );
      model(Node(t.left, t.key, t.value, t.right.left, Red))
        + map[t.right.key := t.right.value]
        + model(t.right.right);
      model(t.left)
        + map[t.key := t.value]
        + model(t.right.left)
        + map[t.right.key := t.right.value]
        + model(t.right.right);
      model(t.left)
        + map[t.key := t.value]
        + model(t.right);
      model(t);
    }
  }

  lemma RotateRightModel(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires SearchTree(t)
    requires SearchTree(RotateRight(t))
    ensures model(t) == model(RotateRight(t))
  {
    calc == {
      model(RotateRight(t));
      model(
        Node(
          t.left.left,
          t.left.key,
          t.left.value,
          Node(t.left.right, t.key, t.value, t.right, Red),
          t.color
        )
      );
      model(t.left.left)
        + map[t.left.key := t.left.value]
        + model(Node(t.left.right, t.key, t.value, t.right, Red));
      model(t.left.left)
        + map[t.left.key := t.left.value]
        + model(t.left.right)
        + map[t.key := t.value]
        + model(t.right);
      model(t.left)
        + map[t.key := t.value]
        + model(t.right);
      model(t);
    }
  }

  lemma RestoreModel(t: rbtree)
    requires t.Node?
    requires SearchTree(t)
    requires isRed(t.right) && isRed(t.right.left) ==>
      isBlack(t) && isRed(t.left)
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.right)
    )
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.left.left)
    )
    requires BlackHeight(t.left) == BlackHeight(t.right)
    requires RedBlackTree(t.left)
    requires RedBlackTree(t.right)

    ensures SearchTree(Restore(t))
    ensures model(t) == model(Restore(t))
  {
    RestoreSpec(t);
    var t' :=
      if isRed(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRed(t'.left) && isRed(t'.left.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRed(t''.left) && isRed(t''.right) then
        FlipColors(t'')
      else
        t'';


    if isRed(t.right) {
      RotateLeftModel(t);
      assert model(RotateLeft(t)) == model(t);
    }
    assert model(t) == model(t');

    if isRed(t'.left) && isRed(t'.left.left) {
      RotateRightModel(t');
      assert model(RotateRight(t')) == model(t');
    }
    assert model(t') == model(t'');

    if isRed(t''.left) && isRed(t''.right) {
      FlipColorsModel(t'');
      assert model(FlipColors(t'')) == model(t'');
    }
    assert model(t'') == model(t''');

    assert t''' == Restore(t);
  }

  // 1'40"
  lemma {:induction} RBInsertModel(t: rbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    requires SearchTree(RBInsert(t, k', v'))
    ensures model(t)[k' := v'] == model(RBInsert(t, k', v'))
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          RBInsertSpec(r, k', v');
          calc == {
            model(RBInsert(Node(l, k, v, r, c), k', v'));
            model(Restore(Node(l, k, v, RBInsert(r, k', v'), c)));
            { RestoreModel(Node(l, k, v, RBInsert(r, k', v'), c)); }
            model(Node(l, k, v, RBInsert(r, k', v'), c));
            { toMap''Lemmas(Node(l, k, v, RBInsert(r, k', v'), c)); }
            model(l) + map[k := v] + model(RBInsert(r, k', v'));
            model(l) + map[k := v] + model(r)[k' := v'];
            model(l) + map[k := v] + model(r) + map[k' := v'];
            model(t) + map[k' := v'];
          }
        } else if k' < k {
          RBInsertSpec(l, k', v');
          calc == {
            model(RBInsert(Node(l, k, v, r, c), k', v'));
            model(Restore(Node(RBInsert(l, k', v'), k, v, r, c)));
            { RestoreModel(Node(RBInsert(l, k', v'), k, v, r, c)); }
            model(Node(RBInsert(l, k', v'), k, v, r, c));
            { toMap''Lemmas(Node(RBInsert(l, k', v'), k, v, r, c)); }
            model(RBInsert(l, k', v')) + map[k := v] + model(r);
            model(l)[k' := v'] + map[k := v] + model(r);
            model(l) + map[k' := v'] + map[k := v] + model(r);
            model(l) + map[k := v] + model(r) + map[k' := v'];
            model(t) + map[k' := v'];
          }
        } else {
        }
      }
    }
  }

  lemma RBInsertRootSpec(t: rbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    ensures keys(t) + {k'} == keys(RBInsert(t, k', v'))
    ensures SearchTree(RBInsertRoot(t, k', v'))
    ensures RedBlackTreeRoot(RBInsertRoot(t, k', v'))
  {
    RBInsertSpec(t, k', v');
  }

  lemma RBInsertRootModel(t: rbtree, k: K, v: V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    requires SearchTree(RBInsertRoot(t, k, v))
    ensures model(t)[k := v] == model(RBInsertRoot(t, k, v))
  {
    RBInsertModel(t, k, v);
  }
}