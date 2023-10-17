include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/AltThreadedLinkedTree/Restore.dfy"
include "../../../../src/tree/layer4/AltThreadedLinkedTree/MoveRed.dfy"
include "../../../../src/tree/layer4/AltThreadedLinkedTree/RemoveMinMaintainingPrev.dfy"
include "../../../../src/tree/layer4/AltThreadedLinkedTree/UpdateNext.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Base.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/AltTRBTree/MoveRed.dfy"
include "../../../../src/tree/layer4/AltTRBTree/RemoveMinMaintainingPrev.dfy"
include "../../../../src/tree/layer4/AltTRBTree/UpdateNext.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Remove.dfy"
include "../../../../src/tree/layer4/AltTTree.dfy"
include "../../../../src/tree/layer4/AltTTNode2.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.Remove {
  import opened Utils
  import opened Utils.Option
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBf = TRBTree.FlipColors
  import TRBrot = TRBTree.Rotate
  import TRBres = TRBTree.Restore
  import TRBm = TRBTree.MoveRed
  import TRBrm = TRBTree.RemoveMinMaintainingPrev
  import TRBr = TRBTree.Remove
  import opened T = TTree
  import opened Rotate
  import opened MoveRed
  import opened Res = Restore
  import opened RM = RemoveMinMaintainingPrev
  import opened UN = UpdateNext
  import opened TTNode
  import opened Color

  method Remove(
      node: TTNode?,
      isThread: bool,
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttreeOrThread<TTNode>,
      ghost next: threadOrEmpty<TTNode>,
      isLeft: bool,
      k: K
    )
      returns (
        newNode: TTNode?,
        isThreadNewNode: bool,
        ghost newSk: ttreeOrThread<TTNode>
      )
    decreases TRB.size(TreeModelRec(sk))

    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadLeft
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadRight

    requires ValidChild(node, sk, isThread)
    requires ThreadedRecCond(prev, sk, next, isLeft)
    requires TRBr.Remove(TreeModelRec(sk), isLeft, k).Some?

    ensures ValidChild(newNode, newSk, isThreadNewNode)
    ensures ThreadedRecCond(prev, newSk, next, isLeft)
    ensures elems(newSk) <= elems(sk)
    ensures TreeModelRec(newSk) == TRBr.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode := node;
    newSk := sk;
    ghost var t := TreeModelRec(newSk);
    if node == null || isThread {
      isThreadNewNode := isThread;
    } else if node.key > k {
      //assume false;
      isThreadNewNode := false;
      isBlackLeftProp(newNode, newSk);
      if isBlackLeft(newNode) {
        isRedLeftProp(newNode.left, newSk.left);
      }
      if isBlackLeft(newNode) && !isRedLeft(newNode.left) {
        assert newNode.right != null by {
          assert newSk.right.Node?;
          assert ValidRec(newNode.right, newSk.right);
        }
        TRBm.MoveRedLeftSize(TreeModelRec(newSk));
        newNode, newSk := MoveRedLeft(newNode, prev, newSk, next);
      }
      ghost var t' := TreeModelRec(newSk);
      ghost var newSkLeft;
      newNode.left, newNode.isThreadLeft, newSkLeft := Remove(
        newNode.left,
        newNode.isThreadLeft,
        prev,
        newSk.left,
        Thread(newSk.data),
        true,
        k
      );
      newSk := newSk.(left := newSkLeft);
      ghost var t'' := TreeModelRec(newSk);
      assert ValidRec(newNode, newSk) by {
        //assume false;
      }
      assert ThreadedNe(prev, newSk, next) by {
        //assume false;
      }
      newNode, newSk := Restore(newNode, prev, newSk, next);
      ghost var t''' := TreeModelRec(newSk);
      assert TreeModelRec(newSk) == TRBr.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap by {
        calc == {
          TreeModelRec(newSk);
          t''';
          TRBres.Restore(t'');
          //{ assume false; }  // 80"
          TRBres.Restore(t'.(left := TRBr.Remove(t'.left, true, k).unwrap));
          TRBr.Remove(t, isLeft, k).unwrap;
          TRBr.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap;
        }
      }
    } else {
      isRedLeftProp(newNode, newSk);
      if isRedLeft(newNode) {
        assert newNode.left != null by {
          assert newSk.left.Node?;
          assert ValidRec(newNode.left, newSk.left);
        }
        assert {newNode, newNode.left} <= elems(newSk) by {
          //assume false;
          assert ValidRec(newNode, newSk);
          assert ValidRec(newNode.left, newSk.left);
        }
        TRBrot.RotateRightSize(TreeModelRec(newSk));
        newNode, newSk := RotateRight(newNode, prev, newSk, next);
      }
      ghost var t' := TreeModelRec(newSk);
      assert ValidChild(newNode.right, newSk.right, newNode.isThreadRight);
      assert TRB.IsThreadOrEmpty(t'.right) <==> (newNode.right == null || newNode.isThreadRight);
      if k == newNode.key && (newNode.right == null || newNode.isThreadRight) {
        assert newSk.left.Empty? || newSk.left.Thread?;
        if isLeft {
          assert ThreadedRecL(prev, newSk.left, Thread(newSk.data));
          assert ThreadedRecL(prev, newSk.left, next);
          assert ThreadedRecCond(prev, newSk.left, next, true);
          return newNode.left, newNode.isThreadLeft, newSk.left;
        } else {
          assert ThreadedRecR(Thread(newSk.data), newSk.right, next);
          assert ThreadedRecR(prev, newSk.right, next);
          assert ThreadedRecCond(prev, newSk.right, next, false);
          return newNode.right, newNode.isThreadRight, newSk.right;
        }
      } else {
        isBlackRightProp(newNode, newSk);
        if isBlackRight(newNode) {
          isRedLeftProp(newNode.right, newSk.right);
        }
        if isBlackRight(newNode) && !isRedLeft(newNode.right) {
          assert newNode.left != null by {
            assert newSk.left.Node?;
            assert ValidRec(newNode.left, newSk.left);
          }
          TRBm.MoveRedRightSize(TreeModelRec(newSk));
          newNode, newSk := MoveRedRight(newNode, prev, newSk, next);
        }
        ghost var t'' := TreeModelRec(newSk);
        if k != newNode.key {  // 77"
          //assume false;
          isThreadNewNode := false;
          ghost var newSkRight;
          label PreRec:
          newNode.right, newNode.isThreadRight, newSkRight := Remove(
            newNode.right,
            newNode.isThreadRight,
            Thread(newSk.data),
            newSk.right,
            next,
            false,
            k
          );
          newSk := newSk.(right := newSkRight);
          assert unchanged@PreRec(elems(newSk.left));
          ghost var t''' := TreeModelRec(newSk);
          assert ValidRec(newNode, newSk) by {  // 38"
            //assume false;
          }
          newNode, newSk := Restore(newNode, prev, newSk, next);
          ghost var t'''' := TreeModelRec(newSk);
          assert TreeModelRec(newSk) == TRBr.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap by {
            //assume false;
            calc == {
              TreeModelRec(newSk);
              t'''';
              TRBres.Restore(t''');
              //{ assume false; }  // 80"
              TRBres.Restore(t''.(right := TRBr.Remove(t''.right, false, k).unwrap));
              TRBr.Remove(t, isLeft, k).unwrap;
              TRBr.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap;
            }
          }
        } else {  // 4'30"
          ghost var newSkRight;
          var newRight, newIsThreadRight, minNode;
          assert ThreadedNe(Thread(newNode), newSk.right, next) by {
            //assume false;
            assert ThreadedNe(prev, newSk, next);
            assert ThreadedRecR(Thread(newNode), newSk.right, next);
          }
          assert ThreadedNe(prev, newSk.left, Thread(newNode)) by {
            //assume false;
            assert ThreadedNe(prev, newSk, next);
            assert ThreadedRecL(prev, newSk.left, Thread(newNode));
          }
          assert elems(newSk.right) !! elems(newSk.left);

          newRight, newSkRight, newIsThreadRight, minNode := RemoveMinMaintainingPrev(
            newNode.right,
            Thread(newNode),
            newSk.right,
            next,
            false
          );
          label PostRM:
          ghost var r' := TreeModelRec(newSkRight);
          assert ValidChild(newRight, newSkRight, newIsThreadRight);
          assert ThreadedRecR(Thread(minNode), newSkRight, next);

          assert elems(newSkRight) !! elems(newSk.left);
          assert TreeModelRec(newSk.left) == t''.left;  // TODO
          var newLeft := newNode.left;
          ghost var newSkLeft := UpdateNext(newLeft, prev, newSk.left, Thread(newNode), minNode);
          label PostUN:
          ghost var l' := TreeModelRec(newSkLeft);
          assert ValidRec(newLeft, newSkLeft);
          assert newSkLeft.Node? ==> ThreadedNe(prev, newSkLeft, Thread(minNode));

          isThreadNewNode := false;
          minNode.color := newNode.color;
          newNode := minNode;
          newNode.left := newLeft;
          newNode.isThreadLeft := false;
          newNode.right := newRight;
          newNode.isThreadRight := newIsThreadRight;
          newSk := Node(newSkLeft, newNode, newSkRight);
          ghost var t''' := TreeModelRec(newSk);
          assert
            && t'''.left == l'
            && t'''.right == r'
            && t'''.key == minNode.key
            && t'''.value == minNode.value
            && t'''.color == t''.color
          by {
            assert TreeModelRec(newSkLeft) == l' by {
              //assume false;
              assert minNode !in elems(newSkLeft);
              assert unchanged@PostUN(elems(newSkLeft));
            }
            assert TreeModelRec(newSkRight) == r' by {
              //assume false;
              assert minNode !in elems(newSkRight);
              assert unchanged@PostRM(elems(newSkRight));
            }
          }
          assert ValidRec(newNode, newSk) by {
            //assume false;
            assert ValidChild(newRight, newSkRight, newIsThreadRight);
            assert ValidRec(newLeft, newSkLeft);
          }
          assert ThreadedNe(prev, newSk, next);

          newNode, newSk := Restore(newNode, prev, newSk, next);
          ghost var t'''' := TreeModelRec(newSk);
          assert ValidChild(newNode, newSk, isThreadNewNode) by {
            assert ValidRec(newNode, newSk);
          }
          assert ThreadedRecCond(prev, newSk, next, isLeft) by {
            assert ThreadedNe(prev, newSk, next);
          }
          assert elems(newSk) <= elems(sk) by {
          }
          assert TreeModelRec(newSk) == TRBr.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap by {
            //assume false;
            assert TRBrm.RemoveMinMaintainingPrev(t''.right, false).Some? by {
              //assume false;
            }
            calc == {
              TreeModelRec(newSk);
              t'''';
              TRBres.Restore(t''');
              TRBres.Restore(TRB.Node(
                l',
                minNode.key,
                minNode.value,
                r',
                t''.color
              ));
              TRBres.Restore(TRB.Node(
                TRBun.UpdateNext(TRB.Thread(minNode.key), t''.left),
                minNode.key,
                minNode.value,
                r',
                t''.color
              ));
              {
                //assume false;
                assert r' == TRBrm.RemoveMinMaintainingPrev(t''.right, false).unwrap.0;
                assert
                  && minNode.key == TRBrm.RemoveMinMaintainingPrev(t''.right, false).unwrap.1
                  && minNode.value == TRBrm.RemoveMinMaintainingPrev(t''.right, false).unwrap.2
                by {
                  //assume false;
                }
                assert t'' == 
                  (if TRB.isBlack(t'.right) && !TRB.isRed(t'.right.left) then
                    var _ :- Guard(t.left.Node?);
                    TRBm.MoveRedRightSize(t');
                    Some(TRBm.MoveRedRight(t'))
                  else
                    Some(t')).unwrap
                by {
                  //assume false;
                }
                assert t' ==
                  (if TRB.isRed(t.left) then
                    TRBrot.RotateRightSize(t);
                    TRBrot.RotateRight(t)
                  else
                    t)
                by {
                  //assume false;
                }
              }
              TRBr.Remove(t, isLeft, k).unwrap;
              TRBr.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap;
            }
          }
        }
      }
    }
  }
}
