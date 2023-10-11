include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/OpFlipColors.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/OpRotate.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/MoveRed.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.OpMoveRed {
  import opened Utils
  import opened KeyValue
  import RB = TRBTree.Base
  import RBf = TRBTree.FlipColors
  import RBr = TRBTree.Rotate
  import RBm = TRBTree.MoveRed
  import opened T = TTree
  import opened FC = FlipColors
  import opened OpR = OpRotate
  import opened TTNode
  import opened Color

  method OpMoveRedLeft(node: TTNode, ghost sk: ttree<TTNode>)  // 1'38"
      returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadLeft
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadRight

    requires OpValidRec(node, sk)
    requires RBm.MoveRedLeft.requires(TreeModelRec(sk))

    ensures OpValidRec(newNode, newSk)
    ensures elems(newSk) == elems(sk)
    ensures TreeModelRec(newSk) == RBm.MoveRedLeft(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
    ensures fresh(elems(newSk)-elems(sk))
  {
    ghost var t := TreeModelRec(sk);
    assert {node, node.left, node.right} <= elems(sk) by {
      //assume false;
      reveal OpValidRec();
    }
    OpFlipColors(node, sk);
    ghost var t' := TreeModelRec(sk);
    assert
      && t'.key == node.key
      && t'.value == node.value
      && t'.color == node.color
    by {
      reveal OpValidRec();
    }
    assert OpValidRec(node.right, sk.right.child) by {
      //assume false;
      reveal OpValidRec();
    }
    isRedLeftPropOp(node.right, sk.right.child);
    if isRedLeft(node.right) {
      assert
        && OpValidRec(node, sk)
        && OpValidRec(node.right, sk.right.child)
        && OpValidRec(node.left, sk.left.child)
        && TRBr.RotateRight.requires(TreeModelRec(sk.right.child))
        && {node, node.right, node.right.left} <= elems(sk)
        && {node, node.right, node.right.left} !! elemsP(sk.left)
        //&& elemsP(sk.left) !! elemsP(sk.right)
      by {
        //assume false;
        reveal OpValidRec();
        reveal OpValidRecP();
        assert {node, node.left, node.right.left} <= elems(sk) by {
          assert sk.left.child.data == node.left by {
            assert OpValidRec(node.left, sk.left.child);
          }
          assert sk.right.child.data == node.right by {
            assert OpValidRec(node.right, sk.right.child);
          }
          assert sk.right.child.left.child.data == node.right.left by {
            assert OpValidRec(node.right.left, sk.right.child.left.child);
          }
        }
      }
      assert nodeNotInSkRight: {node} !! {node.right, node.right.left}
      by {
        reveal OpValidRec();
        reveal OpValidRecP();
        assert sk.right.child.data == node.right by {
          assert OpValidRec(node.right, sk.right.child);
        }
        assert sk.right.child.left.child.data == node.right.left by {
          assert OpValidRec(node.right.left, sk.right.child.left.child);
        }
      }
      label PreRR:
      ghost var newSkRight;
      node.right, newSkRight := OpRotateRight(node.right, sk.right.child);
      ghost var sk' := Node(sk.left, node, Child(newSkRight));
      assert
        && OpValidRec(node, sk')
      by {
        //assume false;
        reveal OpValidRec();
        reveal OpValidRecP();
        assert OpValidRec(node.right, newSkRight);
        assert OpValidRec(node.left, sk.left.child) by {
          //assume false;
          assert unchanged@PreRR(elemsP(sk.left));
        }
      }
      ghost var t'' := TreeModelRec(sk');
      assert t'' == t'.(right := RB.Child(RBr.RotateRight(t'.right.child))) by {
        //assume false;
        calc == {
          t'';
          TreeModelRec(sk');
          TreeModelRec(Node(sk.left, node, Child(newSkRight)));
          RB.Node(TreeModelRecP(sk.left), node.key, node.value, TreeModelRecP(Child(newSkRight)), node.color);
          RB.Node(t'.left, node.key, node.value, TreeModelRecP(Child(newSkRight)), node.color);
          {
            reveal nodeNotInSkRight;
            assert node.key == t'.key;
            assert node.value == t'.value;
            assert node.color == t'.color;
          }
          RB.Node(t'.left, t'.key, t'.value, TreeModelRecP(Child(newSkRight)), t'.color);
          t'.(right := TreeModelRecP(Child(newSkRight)));
          {
            assert TreeModelRec(newSkRight) == RBr.RotateRight(old@PreRR(TreeModelRec(sk.right.child))) by {
              reveal OpValidRec();
              reveal OpValidRecP();
            }
          }
          t'.(right := RB.Child(RBr.RotateRight(t'.right.child)));
        }
      }
      assert
        && OpValidRec(node, sk')
        && TRBr.RotateLeft.requires(TreeModelRec(sk'))
        && {node, node.right} <= elems(sk)
      by {
        //assume false;
        reveal OpValidRec();
        reveal OpValidRecP();
      }
      var node', sk'' := OpRotateLeft(node, sk');
      ghost var t''' := TreeModelRec(sk'');
      assert
        && OpValidRec(node', sk'')
        && TRBf.FlipColors.requires(TreeModelRec(sk''))
        && elems(sk'') == elems(sk)
        && {node', node'.left, node'.right} <= elems(sk)
      by {
        //assume false;
        reveal OpValidRec();
        reveal OpValidRec();
        assert OpValidRec(node', sk'');
        assert TRBf.FlipColors.requires(TreeModelRec(sk''));
        assert elems(sk'') == elems(sk);
        assert {node', node'.left, node'.right} <= elems(sk'') by {
          assert node' == sk''.data by {
            assert OpValidRec(node', sk'');
          }
          assert sk''.data in elems(sk'');
          assert node'.left == sk''.left.child.data by {
            assert OpValidRec(node'.left, sk''.left.child);
          }
          assert sk''.left.child.data in elems(sk'');
          assert node'.right == sk''.right.child.data by {
            assert OpValidRec(node'.right, sk''.right.child);
          }
          assert sk''.right.child.data in elems(sk'');
        }
      }
      OpFlipColors(node', sk'');
      ghost var t'''' := TreeModelRec(sk'');
      assert
        && OpValidRec(node', sk'')
        && elems(sk'') == elems(sk)
      by {
        //assume false;
      }
      assert TreeModelRec(sk'') == RBm.MoveRedLeft(old(TreeModelRec(sk))) by {
        /*
        assert t' == RBf.FlipColors(t);
        calc == {
          RBm.MoveRedLeft(old(TreeModelRec(sk)));
          RBm.MoveRedLeft(t);
          RBf.FlipColors(RBr.RotateLeft(t'.(right := RB.Child(RBr.RotateRight(t'.right.child)))));
          RBf.FlipColors(RBr.RotateLeft(t''));
          RBf.FlipColors(t''');
          t'''';
          TreeModelRec(sk'');
        }
        */
      }
      newNode := node';
      newSk := sk'';
    } else {
      newNode := node;
      newSk := sk;
    }
  }

  method OpMoveRedRight(node: TTNode, ghost sk: ttree<TTNode>)  // 1'15"
      returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadRight
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadLeft

    requires OpValidRec(node, sk)
    requires RBm.MoveRedRight.requires(TreeModelRec(sk))

    ensures OpValidRec(newNode, newSk)
    ensures elems(newSk) == elems(sk)
    ensures TreeModelRec(newSk) == RBm.MoveRedRight(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
    ensures fresh(elems(newSk)-elems(sk))
  {
    ghost var t := TreeModelRec(sk);
    assert {node, node.left, node.right} <= elems(sk) by {
      //assume false;
      reveal OpValidRec();
    }
    OpFlipColors(node, sk);
    assert OpValidRec(node.left, sk.left.child) by {
      //assume false;
      reveal OpValidRec();
    }
    isRedLeftPropOp(node.left, sk.left.child);
    if isRedLeft(node.left) {
      assert
        && OpValidRec(node, sk)
        && {node, node.left} <= elems(sk)
      by {
        //assume false;
        reveal OpValidRec();
      }
      ghost var t' := TreeModelRec(sk);
      var node', sk' := OpRotateRight(node, sk);
      assert
        && OpValidRec(node', sk')
        && {node', node'.left, node'.right} <= elems(sk')
        && TRBf.FlipColors.requires(TreeModelRec(sk'))
      by {
        //assume false;
        reveal OpValidRec();
        assert OpValidRec(node', sk');
        assert {node', node'.left, node'.right} <= elems(sk') by {
          assert sk'.left.child.data == node'.left by {
            assert OpValidRec(node'.left, sk'.left.child);
          }
          assert sk'.right.child.data == node'.right by {
            assert OpValidRec(node'.right, sk'.right.child);
          }
        }
      }
      ghost var t'' := TreeModelRec(sk');
      OpFlipColors(node', sk');
      assert
        && OpValidRec(node'.right, sk'.right.child)
        && node' in elems(sk')
        && {node'.right, node'.right.right} <= elems(sk'.right.child)
        && {node', node'.right, node'.right.right} !! elemsP(sk'.left)
        && node' !in elemsP(sk'.right)
        && TRBr.RotateLeft.requires(TreeModelRec(sk'.right.child))
      by {
        reveal OpValidRec();
        assert OpValidRec(node'.right, sk'.right.child);
        assert {node'.right, node'.right.right} <= elems(sk'.right.child) by {
          assert sk'.right.child.data == node'.right by {
            assert OpValidRec(node'.right, sk'.right.child);
          }
          assert sk'.right.child.right.child.data == node'.right.right by {
            assert OpValidRec(node'.right.right, sk'.right.child.right.child);
          }
        }
      }
      label PreRL:
      ghost var t''' := TreeModelRec(sk');
      ghost var t'''right := TreeModelRec(sk'.right.child);
      ghost var sk''right;
      node'.right, sk''right := OpRotateLeft(node'.right, sk'.right.child);
      ghost var sk'' := Node(sk'.left, node', Child(sk''right));
      ghost var t'''' := TreeModelRec(sk'');
      assert
        && OpValidRec(node', sk'')
        && elems(sk'') == elems(sk)
      by {
        //assume false;
        reveal OpValidRec();
        assert OpValidRec(node', sk'') by {
          assert OpValidRecP(node'.left, sk'.left, node'.isThreadLeft) by {
            assert unchanged@PreRL(elemsP(sk'.left)) by {
              //assume false;
            }
            //assume false;
          }
          assert OpValidRec(node'.right, sk''right) by {
            //assume false;
          }
        }
        assert elems(sk'') == elems(sk);
        //assume false;
      }
      assert TreeModelRec(sk'') == RBm.MoveRedRight(old(TreeModelRec(sk))) by {
        //assume false;
        calc == {
          TreeModelRec(sk'');
          t'''';
          {
            assert t''''.right.child == RBr.RotateLeft(t'''.right.child);
            assert t''''.left == t'''.left;
            assert t''''.key == t'''.key;
            assert t''''.value == t'''.value;
            assert t''''.color == t'''.color;
          }
          RB.Node(
            t'''.left,
            t'''.key,
            t'''.value,
            RB.Child(RBr.RotateLeft(t'''.right.child)),
            t'''.color
          );
          (
            var t'' := RBf.FlipColors(t'');
            RB.Node(
              t''.left,
              t''.key,
              t''.value,
              RB.Child(RBr.RotateLeft(t''.right.child)),
              t''.color
            )
          );
          (
            var t'' := RBf.FlipColors(RBr.RotateRight(t'));
            RB.Node(
              t''.left,
              t''.key,
              t''.value,
              RB.Child(RBr.RotateLeft(t''.right.child)),
              t''.color
            )
          );
          (
            var t' := RBf.FlipColors(t);
            var t'' := RBf.FlipColors(RBr.RotateRight(t'));
            RB.Node(
              t''.left,
              t''.key,
              t''.value,
              RB.Child(RBr.RotateLeft(t''.right.child)),
              t''.color
            )
          );
          RBm.MoveRedRight(t);
          RBm.MoveRedRight(old(TreeModelRec(sk)));
        }
      }
      newNode := node';
      newSk := sk'';
    } else {
      //assume false;
      newNode := node;
      newSk := sk;
    }
  }
}
