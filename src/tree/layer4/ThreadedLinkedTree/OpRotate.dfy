include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.OpRotate {
  import opened KeyValue
  import TRBr = TRBTree.Rotate
  import opened T = TTree
  import opened TTNode
  import opened Color

  method OpRotateLeft(node: TTNode, ghost sk: ttree<TTNode>)  // 56"
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadRight
    modifies node`right
    modifies node.right`isThreadLeft
    modifies node.right`left
    modifies node.right`color

    requires OpValidRec(node, sk)
    requires TRBr.RotateLeft.requires(TreeModelRec(sk))
    requires reveal OpValidRec(); assert node.right != null; true

    ensures OpValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBr.RotateLeft(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    ghost var t := TreeModelRec(sk);
    var node' := node.right;
    ghost var newChildLeftRight;
    assert node' in elems(sk) by {
      reveal OpValidRec();
    }
    assert node'.isThreadLeft <==> t.right.child.left.Thread? by {
      reveal OpValidRec();
      reveal OpValidRecP();
      assert node' == node.right == sk.right.child.data;
      assert OpValidRec(node.right, sk.right.child);
      assert OpValidRecP(node.right.left, sk.right.child.left, node.right.isThreadLeft);
      assert OpValidRecP(node'.left, sk.right.child.left, node'.isThreadLeft);
      calc <==> {
        node'.isThreadLeft;
        <==> sk.right.child.left.Thread?;
        <==> TreeModelRecP(sk.right.child.left).Thread?;
        <==> TreeModelRec(sk).right.child.left.Thread?;
      }
    }
    if node'.isThreadLeft {
      node.right := node';
      node.isThreadRight := true;
      newChildLeftRight := T.Thread(node');
      assert OpValidRecP(node.right, newChildLeftRight, true) by {
        reveal OpValidRec();
        reveal OpValidRecP();
      }
      assert TreeModelRecP(newChildLeftRight) == RB.Thread(t.right.child.key) by {
        reveal OpValidRec();
        reveal OpValidRecP();
      }
    } else {
      node.right := node'.left;
      node.isThreadRight := false;
      newChildLeftRight := sk.right.child.left;
      assert OpValidRecP(node.right, newChildLeftRight, false) by {
        reveal OpValidRec();
        reveal OpValidRecP();
      }
      assert TreeModelRecP(newChildLeftRight) == t.right.child.left by {
        reveal OpValidRec();
        reveal OpValidRecP();
      }
    }
    ghost var treeNewChildLeftRight := TreeModelRecP(newChildLeftRight);
    assert OpValidRecP(node.right, newChildLeftRight, node.isThreadRight);
    node'.color := node.color;
    node.color := Red;
    node'.left := node;
    node'.isThreadLeft := false;
    ghost var sk' := T.Node(
      T.Child(T.Node(sk.left, node, newChildLeftRight)),
      node',
      sk.right.child.right
    );
    ghost var t' := TreeModelRec(sk');
    assert
      && OpValidRec(node', sk')
      && elems(sk') == elems(sk)
    by {
      reveal OpValidRec();
      reveal OpValidRecP();
      assert node' !in elemsP(sk'.left);
      assert node' !in elemsP(sk'.right);
      assert elemsP(sk'.left) !! elemsP(sk'.right);

      assert OpValidRec(node'.left, sk'.left.child) by {
        assert OpValidRecP(node'.left.left, sk.left, node'.left.isThreadLeft) by {
          assert node'.left.left == node.left;
          assert unchanged(elemsP(sk.left));
          assert OpValidRecP(node.left, sk.left, node.isThreadLeft);
        }
        assert OpValidRecP(node'.left.right, newChildLeftRight, node'.left.isThreadRight) by {
          assert node'.left.right == node.right;
          assert node'.left.isThreadRight == node.isThreadRight;
          assert OpValidRecP(node.right, newChildLeftRight, node.isThreadRight);
        }
      }
      assert OpValidRecP(node'.right, sk'.right, node'.isThreadRight) by {
        assert node'.right == old(node.right.right);
        assert unchanged(elemsP(sk.right.child.right));
      }
    }
    assert TreeModelRec(sk') == TRBr.RotateLeft(old(TreeModelRec(sk))) by {
      reveal OpValidRec();
      reveal OpValidRecP();
      calc == {
        t'.left.child.right;
        TreeModelRec(sk').left.child.right;
        TreeModelRecP(sk'.left).child.right;
        TreeModelRec(sk'.left.child).right;
        TreeModelRecP(sk'.left.child.right);
        TreeModelRecP(newChildLeftRight);
        treeNewChildLeftRight;
        (if t.right.child.left.Thread? then
          RB.Thread(t.right.child.key)
        else
          t.right.child.left);
      }
    }
    newNode := node';
    newSk := sk';
  }

  method OpRotateRight(node: TTNode, ghost sk: ttree<TTNode>)  // 1"15"
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadLeft
    modifies node`left
    modifies node.left`isThreadRight
    modifies node.left`right
    modifies node.left`color

    requires OpValidRec(node, sk)
    requires TRBr.RotateRight.requires(TreeModelRec(sk))
    requires reveal OpValidRec(); true

    ensures OpValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBr.RotateRight(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    ghost var t := TreeModelRec(sk);
    var node' := node.left;
    assert node' in elems(sk) by {
      reveal OpValidRec();
    }
    assert node'.isThreadRight <==> t.left.child.right.Thread? by {
      reveal OpValidRec();
      reveal OpValidRecP();
      assert node' == node.left == sk.left.child.data;
      assert OpValidRec(node.left, sk.left.child);
      assert OpValidRecP(node.left.right, sk.left.child.right, node.left.isThreadRight);
      assert OpValidRecP(node'.right, sk.left.child.right, node'.isThreadRight);
      calc <==> {
        node'.isThreadRight;
        <==> sk.left.child.right.Thread?;
        <==> TreeModelRecP(sk.left.child.right).Thread?;
        <==> TreeModelRec(sk).left.child.right.Thread?;
      }
    }
    ghost var newChildRightLeft;
    if node'.isThreadRight {
      node.left := node';
      node.isThreadLeft := true;
      newChildRightLeft := T.Thread(node');
      assert OpValidRecP(node.left, newChildRightLeft, true) by {
        reveal OpValidRec();
        reveal OpValidRecP();
      }
      assert TreeModelRecP(newChildRightLeft) == RB.Thread(old(TreeModelRec(sk)).left.child.key) by {
        reveal OpValidRec();
        reveal OpValidRecP();
      }
    } else {
      node.left := node'.right;
      node.isThreadLeft := false;
      newChildRightLeft := sk.left.child.right;
      assert OpValidRecP(node.left, newChildRightLeft, false) by {
        reveal OpValidRec();
        reveal OpValidRecP();
      }
      assert TreeModelRecP(newChildRightLeft) == old(TreeModelRec(sk)).left.child.right by {
        reveal OpValidRec();
        reveal OpValidRecP();
      }
    }
    ghost var treeNewChildRightLeft := TreeModelRecP(newChildRightLeft);
    assert OpValidRecP(node.left, newChildRightLeft, node.isThreadLeft);
    label PreUpdate:
    node'.color := node.color;
    node.color := Red;
    node'.right := node;
    node'.isThreadRight := false;
    ghost var sk' := T.Node(
      sk.left.child.left,
      node',
      T.Child(T.Node(newChildRightLeft, node, sk.right))
    );
    ghost var t' := TreeModelRec(sk');
    assert
      && OpValidRec(node', sk')
      && elems(sk') == elems(sk)
    by {
      reveal OpValidRec();
      reveal OpValidRecP();
      assert node' !in elemsP(sk'.left);
      assert node' !in elemsP(sk'.right);
      assert elemsP(sk'.left) !! elemsP(sk'.right);

      assert OpValidRec(node'.right, sk'.right.child) by {
        assert OpValidRecP(node'.right.right, sk.right, node'.right.isThreadRight) by {
          assert node'.right.right == node.right;
          assert unchanged(elemsP(sk.right));
          assert OpValidRecP(node.right, sk.right, node.isThreadRight);
        }
        assert OpValidRecP(node'.right.left, newChildRightLeft, node'.right.isThreadLeft) by {
          assert node'.right.left == node.left;
          assert node'.right.isThreadLeft == node.isThreadLeft;
          assert unchanged@PreUpdate(elemsP(newChildRightLeft));
          assert node.left == old@PreUpdate(node.left);
          assert node.isThreadLeft == old@PreUpdate(node.isThreadLeft);
          assert OpValidRecP(node.left, newChildRightLeft, node.isThreadLeft);
        }
      }
      assert OpValidRecP(node'.left, sk'.left, node'.isThreadLeft) by {
        assert node'.left == old(node.left.left);
        assert unchanged(elemsP(sk.left.child.left));
      }
    }
    assert TreeModelRec(sk') == TRBr.RotateRight(old(TreeModelRec(sk))) by {
      reveal OpValidRec();
      reveal OpValidRecP();
      calc == {
        t'.right.child.left;
        TreeModelRec(sk').right.child.left;
        TreeModelRecP(sk'.right).child.left;
        TreeModelRec(sk'.right.child).left;
        TreeModelRecP(sk'.right.child.left);
        TreeModelRecP(newChildRightLeft);
        treeNewChildRightLeft;
        (if t.left.child.right.Thread? then
          RB.Thread(t.left.child.key)
        else
          t.left.child.right);
      }
    }
    newNode := node';
    newSk := sk';
  }
}
