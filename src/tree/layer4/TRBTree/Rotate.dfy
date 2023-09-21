include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module {:options "-functionSyntax:4"} TRBTree.Rotate {
  import opened Color
  import opened Base

  function RotateLeft(t: rbtree): rbtree
    requires t.Node?
    requires t.right.Child?
    requires t.right.child.Node?
  {
    Node(
      Child(Node(
        t.left,
        t.key,
        t.value,
        if t.right.child.left.Thread? then
          Thread(t.right.child.key)
        else
          t.right.child.left,
        Red
      )),
      t.right.child.key,
      t.right.child.value,
      t.right.child.right,
      t.color
    )
  }

  function RotateRight(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
  {
    Node(
      t.left.child.left,
      t.left.child.key,
      t.left.child.value,
      Child(Node(
        if t.left.child.right.Thread? then
          Thread(t.left.child.key)
        else
          t.left.child.right,
        t.key,
        t.value,
        t.right,
        Red
      )),
      t.color
    )
  }

  lemma RotateLeftSpec(t: rbtree)
    requires t.Node?
    requires isRedP(t.right)
    requires SearchTree(t)
    ensures keys(t) == keys(RotateLeft(t))
    ensures SearchTree(RotateLeft(t))
    ensures BlackHeight(RotateLeft(t)) == BlackHeight(t)
  {
    if t.right.child.left.Thread? {
      assert SearchTreeP(RotateLeft(t).left.child.right);
      assert BlackHeightP(RotateLeft(t).left.child.right) == BlackHeightP(t.right.child.left);
    }
  }

  lemma {:verify false} RotateLeftSize(t: rbtree)
    requires RotateLeft.requires(t)
    ensures size(t) == size(RotateLeft(t))
  {}

  lemma RotateLeftThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    requires ThreadedTreeRec(prev, t, next)
    ensures ThreadedTreeRec(prev, RotateLeft(t), next)
  {
    assert ThreadedTreeRecPL(prev, RotateLeft(t).left, Thread(RotateLeft(t).key)) by {
      assert ThreadedTreeRec(prev, RotateLeft(t).left.child, Thread(RotateLeft(t).key)) by {
        assert ThreadedTreeRecPL(prev, RotateLeft(t).left.child.left, Thread(RotateLeft(t).left.child.key));
        assert ThreadedTreeRecPR(Thread(RotateLeft(t).left.child.key), RotateLeft(t).left.child.right, Thread(RotateLeft(t).key)) by {
          assert ThreadedTreeRecPL(Thread(t.key), t.right.child.left, Thread(t.right.child.key));
        }
      }
    }
    assert ThreadedTreeRecPR(Thread(RotateLeft(t).key), RotateLeft(t).right, next);
  }

  lemma RotateRightSpec(t: rbtree)
    requires t.Node?
    requires isRedP(t.left)
    requires SearchTree(t)
    ensures keys(t) == keys(RotateRight(t))
    ensures SearchTree(RotateRight(t))
    ensures BlackHeight(RotateRight(t)) == BlackHeight(t)
  {
    if t.left.child.right.Thread? {
      assert SearchTreeP(RotateRight(t).right.child.left);
      assert BlackHeightP(RotateRight(t).right.child.left) == BlackHeightP(t.left.child.right);
    }
  }

  lemma RotateRightSize(t: rbtree)
    requires RotateRight.requires(t)
    ensures size(t) == size(RotateRight(t))
  {
    if t.left.child.right.Thread? {
      calc == {
        size(t);

        1 +
        sizeP(t.left) +
        sizeP(t.right);

        1 +
        1 +
        sizeP(t.left.child.left) +
        sizeP(t.left.child.right) +
        sizeP(t.right);

        1 +
        sizeP(t.left.child.left) +
        1 +
        sizeP(Thread(t.left.child.key)) +
        sizeP(t.right);

        1 +
        sizeP(t.left.child.left) +
        sizeP(
          Child(Node(
              Thread(t.left.child.key),
              t.key,
              t.value,
              t.right,
              Red
            ))
        );

        size(
          Node(
            t.left.child.left,
            t.left.child.key,
            t.left.child.value,
            Child(Node(
              if t.left.child.right.Thread? then
                Thread(t.left.child.key)
              else
                t.left.child.right,
              t.key,
              t.value,
              t.right,
              Red
            )),
            t.color
          )
        );
        size(RotateRight(t));
      }
    } else {
      calc == {
        size(t);
        1 +
        sizeP(t.left) +
        sizeP(t.right);
        1 +
        1 +
        sizeP(t.left.child.left) +
        sizeP(t.left.child.right) +
        sizeP(t.right);
        1 +
        sizeP(t.left.child.left) +
        1 +
        sizeP(t.left.child.right) +
        sizeP(t.right);
        1 +
        sizeP(t.left.child.left) +
        sizeP(
          Child(Node(
              t.left.child.right,
              t.key,
              t.value,
              t.right,
              Red
            ))
        );
        size(
          Node(
            t.left.child.left,
            t.left.child.key,
            t.left.child.value,
            Child(Node(
              if t.left.child.right.Thread? then
                Thread(t.left.child.key)
              else
                t.left.child.right,
              t.key,
              t.value,
              t.right,
              Red
            )),
            t.color
          )
        );
        size(RotateRight(t));
      }
    }
  }

  lemma {:verify false} RotateRightSizeWithPointers(t: rbtree)
    requires RotateRight.requires(t)
    ensures sizeWithPointers(t) == sizeWithPointers(RotateRight(t))
  {}

  lemma RotateRightThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires ThreadedTreeRec(prev, t, next)
    ensures ThreadedTreeRec(prev, RotateRight(t), next)
  {
    assert ThreadedTreeRecPL(prev, RotateRight(t).left, Thread(RotateRight(t).key));
    assert ThreadedTreeRecPR(Thread(RotateRight(t).key), RotateRight(t).right, next) by {
      assert ThreadedTreeRec(Thread(RotateRight(t).key), RotateRight(t).right.child, next) by {
        assert ThreadedTreeRecPL(Thread(RotateRight(t).key), RotateRight(t).right.child.left, Thread(RotateRight(t).right.child.key)) by {
          assert ThreadedTreeRecPR(Thread(t.left.child.key), t.left.child.right, Thread(t.key));
        }
        assert ThreadedTreeRecPR(Thread(RotateRight(t).right.child.key), RotateRight(t).right.child.right, next);
      }
    }
  }

  lemma AllRotateLeftSpec()
    ensures forall t: rbtree
        | t.Node?
        && isRedP(t.right)
        && SearchTree(t)
        && RedBlackTree(t)
      :: keys(t) == keys(RotateLeft(t))
      && SearchTree(RotateLeft(t))
      && BlackHeight(RotateLeft(t)) == BlackHeight(t)
  {}

  lemma AllRotateRightSpec()
    ensures forall t: rbtree
        | t.Node?
        && isRedP(t.left)
        && SearchTree(t)
      :: keys(t) == keys(RotateRight(t))
      && SearchTree(RotateRight(t))
      && BlackHeight(RotateRight(t)) == BlackHeight(t)
  {
    forall t: rbtree
        | t.Node?
        && isRedP(t.left)
        && SearchTree(t)
      ensures keys(t) == keys(RotateRight(t))
      ensures SearchTree(RotateRight(t))
      ensures BlackHeight(RotateRight(t)) == BlackHeight(t)
    {
      RotateRightSpec(t);
    }
  }

/*
  // 58"
  lemma {:verify false} RotateLeftModel(t: rbtree)
    requires t.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires SearchTree(RotateLeft(t))
    ensures toMap(t) == toMap(RotateLeft(t))
  {
    calc == {
      toMap(RotateLeft(t));
      toMap(
        Node(
          Node(t.left, t.key, t.value, t.right.left, Red),
          t.right.key,
          t.right.value,
          t.right.right,
          t.color
        )
      );
      toMap(Node(t.left, t.key, t.value, t.right.left, Red))
        + map[t.right.key := t.right.value]
        + toMap(t.right.right);
      toMap(t.left)
        + map[t.key := t.value]
        + toMap(t.right.left)
        + map[t.right.key := t.right.value]
        + toMap(t.right.right);
      toMap(t.left)
        + map[t.key := t.value]
        + toMap(t.right);
      toMap(t);
    }
  }

  lemma {:verify false} RotateRightModel(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires SearchTree(t)
    requires SearchTree(RotateRight(t))
    ensures toMap(t) == toMap(RotateRight(t))
  {
    calc == {
      toMap(RotateRight(t));
      toMap(
        Node(
          t.left.left,
          t.left.key,
          t.left.value,
          Node(t.left.right, t.key, t.value, t.right, Red),
          t.color
        )
      );
      toMap(t.left.left)
        + map[t.left.key := t.left.value]
        + toMap(Node(t.left.right, t.key, t.value, t.right, Red));
      toMap(t.left.left)
        + map[t.left.key := t.left.value]
        + toMap(t.left.right)
        + map[t.key := t.value]
        + toMap(t.right);
      toMap(t.left)
        + map[t.key := t.value]
        + toMap(t.right);
      toMap(t);
    }
  }
*/
}