include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module {:options "-functionSyntax:4"} TRBTree.Rotate {
  import opened Color
  import opened Base

  function RotateLeft(t: trbtree): trbtree
    requires t.Node?
    requires t.right.Node?
  {
    Node(
      Node(
        t.left,
        t.key,
        t.value,
        if t.right.left.Thread? then
          Thread(t.right.key)
        else
          t.right.left,
        Red
      ),
      t.right.key,
      t.right.value,
      t.right.right,
      t.color
    )
  }

  function RotateRight(t: trbtree): trbtree
    requires t.Node?
    requires t.left.Node?
  {
    Node(
      t.left.left,
      t.left.key,
      t.left.value,
      Node(
        if t.left.right.Thread? then
          Thread(t.left.key)
        else
          t.left.right,
        t.key,
        t.value,
        t.right,
        Red
      ),
      t.color
    )
  }
  
  lemma RotateRightRightLeft(t: trbtree)
    requires t.Node?
    requires t.left.Node?
    ensures !t.left.right.Thread? ==> RotateRight(t).right.left == t.left.right
  {}
  
  lemma RotateLeftSpec(t: trbtree)
    requires t.Node?
    requires isRed(t.right)
    requires SearchTree(t)
    ensures keys(t) == keys(RotateLeft(t))
    ensures SearchTree(RotateLeft(t))
    ensures BlackHeight(RotateLeft(t)) == BlackHeight(t)
  {
    if t.right.left.Thread? {
      assert keys(t.right.left) == keys(RotateLeft(t).left.right) == {};
      assert SearchTree(RotateLeft(t).left.right);
      assert BlackHeight(RotateLeft(t).left.right) == BlackHeight(t.right.left);
    }
  }

  lemma {:verify false} RotateLeftSize(t: trbtree)
    requires RotateLeft.requires(t)
    ensures size(t) == size(RotateLeft(t))
  {}

  lemma RotateLeftThreaded(prev: threadOrEmpty, t: trbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.right.Node?
    requires ThreadedTreeNe(prev, t, next)
    ensures ThreadedTreeNe(prev, RotateLeft(t), next)
  {
    assert ThreadedTreeRecL(prev, RotateLeft(t).left, Thread(RotateLeft(t).key)) by {
      assert ThreadedTreeNe(prev, RotateLeft(t).left, Thread(RotateLeft(t).key)) by {
        assert ThreadedTreeRecL(prev, RotateLeft(t).left.left, Thread(RotateLeft(t).left.key));
        assert ThreadedTreeRecR(Thread(RotateLeft(t).left.key), RotateLeft(t).left.right, Thread(RotateLeft(t).key)) by {
          assert ThreadedTreeRecL(Thread(t.key), t.right.left, Thread(t.right.key));
        }
      }
    }
    assert ThreadedTreeRecR(Thread(RotateLeft(t).key), RotateLeft(t).right, next);
  }

  lemma RotateRightSpec(t: trbtree)
    requires t.Node?
    requires isRed(t.left)
    requires SearchTree(t)
    ensures keys(t) == keys(RotateRight(t))
    ensures SearchTree(RotateRight(t))
    ensures BlackHeight(RotateRight(t)) == BlackHeight(t)
  {
    if t.left.right.Thread? {
      assert keys(t.left.right) == keys(RotateRight(t).right.left) == {};
      assert SearchTree(RotateRight(t).right.left);
      assert BlackHeight(RotateRight(t).right.left) == BlackHeight(t.left.right);
    }
  }

  lemma RotateRightSize(t: trbtree)
    requires RotateRight.requires(t)
    ensures size(t) == size(RotateRight(t))
  {
    if t.left.right.Thread? {
      calc == {
        size(t);

        1 +
        size(t.left) +
        size(t.right);

        1 +
        1 +
        size(t.left.left) +
        size(t.left.right) +
        size(t.right);

        1 +
        size(t.left.left) +
        1 +
        size(Thread(t.left.key)) +
        size(t.right);

        1 +
        size(t.left.left) +
        size(Node(
          Thread(t.left.key),
          t.key,
          t.value,
          t.right,
          Red
        ));

        size(
          Node(
            t.left.left,
            t.left.key,
            t.left.value,
            Node(
              if t.left.right.Thread? then
                Thread(t.left.key)
              else
                t.left.right,
              t.key,
              t.value,
              t.right,
              Red
            ),
            t.color
          )
        );
        size(RotateRight(t));
      }
    } else {
      calc == {
        size(t);
        1 +
        size(t.left) +
        size(t.right);
        1 +
        1 +
        size(t.left.left) +
        size(t.left.right) +
        size(t.right);
        1 +
        size(t.left.left) +
        1 +
        size(t.left.right) +
        size(t.right);
        1 +
        size(t.left.left) +
        size(Node(
          t.left.right,
          t.key,
          t.value,
          t.right,
          Red
        ));
        size(
          Node(
            t.left.left,
            t.left.key,
            t.left.value,
            Node(
              if t.left.right.Thread? then
                Thread(t.left.key)
              else
                t.left.right,
              t.key,
              t.value,
              t.right,
              Red
            ),
            t.color
          )
        );
        size(RotateRight(t));
      }
    }
  }

  lemma RotateRightThreaded(prev: threadOrEmpty, t: trbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.left.Node?
    requires ThreadedTreeNe(prev, t, next)
    ensures ThreadedTreeNe(prev, RotateRight(t), next)
  {
    assert ThreadedTreeRecL(prev, RotateRight(t).left, Thread(RotateRight(t).key));
    assert ThreadedTreeRecR(Thread(RotateRight(t).key), RotateRight(t).right, next) by {
      assert ThreadedTreeNe(Thread(RotateRight(t).key), RotateRight(t).right, next) by {
        assert ThreadedTreeRecL(Thread(RotateRight(t).key), RotateRight(t).right.left, Thread(RotateRight(t).right.key)) by {
          assert ThreadedTreeRecR(Thread(t.left.key), t.left.right, Thread(t.key));
        }
        assert ThreadedTreeRecR(Thread(RotateRight(t).right.key), RotateRight(t).right.right, next);
      }
    }
  }

  lemma AllRotateLeftSpec()
    ensures forall t: trbtree
        | t.Node?
        && isRed(t.right)
        && SearchTree(t)
        && RedBlackTree(t)
      :: keys(t) == keys(RotateLeft(t))
      && SearchTree(RotateLeft(t))
      && BlackHeight(RotateLeft(t)) == BlackHeight(t)
  {}

  lemma AllRotateRightSpec()
    ensures forall t: trbtree
        | t.Node?
        && isRed(t.left)
        && SearchTree(t)
      :: keys(t) == keys(RotateRight(t))
      && SearchTree(RotateRight(t))
      && BlackHeight(RotateRight(t)) == BlackHeight(t)
  {
    forall t: trbtree
        | t.Node?
        && isRed(t.left)
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
  lemma {:verify false} RotateLeftModel(t: trbtree)
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

  lemma {:verify false} RotateRightModel(t: trbtree)
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