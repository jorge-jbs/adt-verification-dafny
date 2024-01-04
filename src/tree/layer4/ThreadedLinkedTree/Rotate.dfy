include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.Rotate {
  import opened KeyValue
  import TRBr = TRBTree.Rotate
  import opened T = TTree
  import opened TTNode
  import opened Color

  method RotateLeft(
      node: TTNode,
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttree<TTNode>,
      ghost next: threadOrEmpty<TTNode>
    )
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadRight
    modifies node`right
    modifies node.right`isThreadLeft
    modifies node.right`left
    modifies node.right`color

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures ThreadedNe(prev, newSk, next)
    ensures TreeModelRec(newSk) == TRBr.RotateLeft(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    ghost var t := TreeModelRec(sk);
    assert trl: ThreadedRecL(Thread(sk.data), sk.right.left, Thread(sk.right.data));
    newNode := node.right;
    assert t.right.left.Thread? <==> newNode.isThreadLeft by {
      assert TreeModelRec(sk.right.left) == t.right.left;
    }
    ghost var newSkLeftRight;
    if newNode.isThreadLeft {
      node.right := newNode;
      node.isThreadRight := true;
      newSkLeftRight := T.Thread(newNode);
    } else {
      node.right := newNode.left;
      node.isThreadRight := false;
      newSkLeftRight := sk.right.left;
    }
    ghost var leftRight := TreeModelRec(newSkLeftRight);
    newNode.color := node.color;
    node.color := Red;
    newNode.left := node;
    newNode.isThreadLeft := false;
    newSk := T.Node(T.Node(sk.left, node, newSkLeftRight), newNode, sk.right.right);
    assert ValidRec(newNode, newSk);
    assert elems(newSk) == elems(sk);
    assert ThreadedNe(prev, newSk, next) by {
      assert ThreadedRecL(prev, newSk.left, Thread(newSk.data)) by {
        assert ThreadedNe(prev, newSk.left, Thread(newSk.data)) by {
          assert ThreadedRecL(prev, newSk.left.left, Thread(newSk.left.data));
          assert ThreadedRecR(Thread(newSk.left.data), newSk.left.right, Thread(newSk.data)) by {
            reveal trl;
          }
        }
      }
      assert ThreadedRecR(Thread(newSk.data), newSk.right, next);
    }
    assert TreeModelRec(newSk) == TRBr.RotateLeft(old(TreeModelRec(sk))) by {
      assert leftRight ==
        (if t.right.left.Thread? then
          TRB.Thread(t.right.key)
        else
          t.right.left);
    }
  }

  method RotateRight(
      node: TTNode, 
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttree<TTNode>,
      ghost next: threadOrEmpty<TTNode>
      //parents: set<TTNode>
    )
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadLeft
    modifies node`left
    modifies node.left`isThreadRight
    modifies node.left`right
    modifies node.left`color

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)
    requires node.left != null
    requires !node.isThreadLeft
    requires TreeModelRec(sk).left.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures ThreadedNe(prev, newSk, next)
    ensures TreeModelRec(newSk) == TRBr.RotateRight(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    ghost var t := TreeModelRec(sk);
    assert tlr: ThreadedRecR(Thread(sk.left.data), sk.left.right, Thread(sk.data));
    newNode := node.left;
    assert t.left.right.Thread? <==> newNode.isThreadRight by {
      assert TreeModelRec(sk.left.right) == t.left.right;
    }
    ghost var newSkRightLeft;
    if newNode.isThreadRight {
      node.left := newNode;
      node.isThreadLeft := true;
      newSkRightLeft := T.Thread(newNode);
    } else {
      node.left := newNode.right;
      node.isThreadLeft := false;
      newSkRightLeft := sk.left.right;
    }
    ghost var rightLeft := TreeModelRec(newSkRightLeft);
    newNode.right := node;
    newNode.isThreadRight := false;
    newNode.color := node.color;
    node.color := Red;
    newSk := T.Node(sk.left.left, newNode, T.Node(newSkRightLeft, node, sk.right));
    assert ValidRec(newNode, newSk);
    assert elems(newSk) == elems(sk);
    assert ThreadedNe(prev, newSk, next) by {
      assert ThreadedRecL(prev, newSk.left, Thread(newSk.data));
      assert ThreadedRecR(Thread(newSk.data), newSk.right, next) by {
        assert ThreadedNe(Thread(newSk.data), newSk.right, next) by {
          assert ThreadedRecL(Thread(newSk.data), newSk.right.left, Thread(newSk.right.data)) by {
            reveal tlr;
          }
          assert ThreadedRecR(Thread(newSk.right.data), newSk.right.right, next);
        }
      }
    }
    assert TreeModelRec(newSk) == TRBr.RotateRight(old(TreeModelRec(sk))) by {
      assert rightLeft ==
        (if t.left.right.Thread? then
          TRB.Thread(t.left.key)
        else
          t.left.right);
    }
  }
}
