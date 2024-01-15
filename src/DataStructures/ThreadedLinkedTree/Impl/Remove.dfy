include "../../../../src/Collections/Option.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/Restore.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/MoveRed.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/RemoveMinMaintainingPrev.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/UpdateNext.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Rotate.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/MoveRed.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/RemoveMinMaintainingPrev.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Remove.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"

module ThreadedLinkedTree.Impl.Remove {
  import opened Option
  import opened KeyValue
  import opened Model.Color
  import ModelB = Model.Base
  import ModelF = Model.FlipColors
  import ModelRot = Model.Rotate
  import ModelRes = Model.Restore
  import ModelM = Model.MoveRed
  import ModelRM = Model.RemoveMinMaintainingPrev
  import ModelR = Model.Remove
  import ModelUN = Model.UpdateNext
  import opened T = TTree
  import opened Rotate
  import opened MoveRed
  import opened Res = Restore
  import opened RM = RemoveMinMaintainingPrev
  import opened UN = UpdateNext
  import opened TTNode

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
      ghost newSk: ttreeOrThread<TTNode>,
      ghost removedNode: TTNode?,
      isRemoved: bool
    )
    decreases ModelB.size(TreeModelRec(sk))

    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadLeft
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadRight

    requires ValidChild(node, sk, isThread)
    requires ThreadedRecCond(prev, sk, next, isLeft)
    requires ModelR.Remove(TreeModelRec(sk), isLeft, k).Some?

    ensures ValidChild(newNode, newSk, isThreadNewNode)
    ensures ThreadedRecCond(prev, newSk, next, isLeft)
    ensures isRemoved <==> ModelR.IsRemoved(old(TreeModelRec(sk)), isLeft, k)
    ensures elems(newSk) <= elems(sk)
    ensures TreeModelRec(newSk) == ModelR.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap

    ensures removedNode != null <==> isRemoved
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures isRemoved ==> removedNode.key == k && removedNode in elems(sk)

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode := node;
    newSk := sk;
    ghost var t := TreeModelRec(newSk);
    if node == null || isThread {
      isThreadNewNode := isThread;
      removedNode := null;
      isRemoved := false;
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
        ModelM.MoveRedLeftSize(TreeModelRec(newSk));
        newNode, newSk := MoveRedLeft(newNode, prev, newSk, next);
      }
      ghost var t' := TreeModelRec(newSk);
      ghost var newSkLeft;
      newNode.left, newNode.isThreadLeft, newSkLeft, removedNode, isRemoved := Remove(
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
      assert TreeModelRec(newSk) == ModelR.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap by {
        calc == {
          TreeModelRec(newSk);
          t''';
          ModelRes.Restore(t'');
          //{ assume false; }  // 80"
          ModelRes.Restore(t'.(left := ModelR.Remove(t'.left, true, k).unwrap));
          ModelR.Remove(t, isLeft, k).unwrap;
          ModelR.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap;
        }
      }
      assert
        && (removedNode != null <==> isRemoved)
        && elems(newSk) == elems(sk) - {removedNode}
        && (isRemoved ==> removedNode.key == k && removedNode in elems(sk))
      by {
        //assume false;
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
        ModelRot.RotateRightSize(TreeModelRec(newSk));
        newNode, newSk := RotateRight(newNode, prev, newSk, next);
      }
      ghost var t' := TreeModelRec(newSk);
      assert ValidChild(newNode.right, newSk.right, newNode.isThreadRight);
      assert ModelB.IsThreadOrEmpty(t'.right) <==> (newNode.right == null || newNode.isThreadRight);
      if k == newNode.key && (newNode.right == null || newNode.isThreadRight) {
        //assume false;
        assert newSk.left.Empty? || newSk.left.Thread?;
        if isLeft {
          assert ThreadedRecL(prev, newSk.left, Thread(newSk.data));
          assert ThreadedRecL(prev, newSk.left, next);
          assert ThreadedRecCond(prev, newSk.left, next, true);
          return newNode.left, newNode.isThreadLeft, newSk.left, newNode, true;
        } else {
          assert ThreadedRecR(Thread(newSk.data), newSk.right, next);
          assert ThreadedRecR(prev, newSk.right, next);
          assert ThreadedRecCond(prev, newSk.right, next, false);
          return newNode.right, newNode.isThreadRight, newSk.right, newNode, true;
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
          ModelM.MoveRedRightSize(TreeModelRec(newSk));
          newNode, newSk := MoveRedRight(newNode, prev, newSk, next);
        }
        ghost var t'' := TreeModelRec(newSk);
        if k != newNode.key {  // 77"
          //assume false;
          isThreadNewNode := false;
          ghost var newSkRight;
          label PreRec:
          newNode.right, newNode.isThreadRight, newSkRight, removedNode, isRemoved := Remove(
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
          assert TreeModelRec(newSk) == ModelR.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap by {
            //assume false;
            calc == {
              TreeModelRec(newSk);
              t'''';
              ModelRes.Restore(t''');
              //{ assume false; }  // 80"
              ModelRes.Restore(t''.(right := ModelR.Remove(t''.right, false, k).unwrap));
              ModelR.Remove(t, isLeft, k).unwrap;
              ModelR.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap;
            }
          }
          assert
            && (removedNode != null <==> isRemoved)
            && elems(newSk) == elems(sk) - {removedNode}
            && (isRemoved ==> removedNode.key == k && removedNode in elems(sk))
          by {
            //assume false;
          }
        } else {  // 4'30"
          isRemoved := true;
          removedNode := newNode;
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
          newSk := Node(newSkLeft, newNode as TTNode, newSkRight);
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
            //assume false;
            assert ValidRec(newNode, newSk);
          }
          assert ThreadedRecCond(prev, newSk, next, isLeft) by {
            //assume false;
            assert ThreadedNe(prev, newSk, next);
          }
          assert elems(newSk) <= elems(sk) by {
            //assume false;
          }
          assert
            && (removedNode != null <==> isRemoved)
            && elems(newSk) == elems(sk) - {removedNode}
            && (isRemoved ==> removedNode.key == k && removedNode in elems(sk))
          by {
            //assume false;
          }
          assert TreeModelRec(newSk) == ModelR.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap by {
            //assume false;
            assert ModelRM.RemoveMinMaintainingPrev(t''.right, false).Some? by {
              //assume false;
            }
            calc == {
              TreeModelRec(newSk);
              t'''';
              ModelRes.Restore(t''');
              ModelRes.Restore(ModelB.Node(
                l',
                minNode.key,
                minNode.value,
                r',
                t''.color
              ));
              ModelRes.Restore(ModelB.Node(
                ModelUN.UpdateNext(ModelB.Thread(minNode.key), t''.left),
                minNode.key,
                minNode.value,
                r',
                t''.color
              ));
              {
                //assume false;
                assert r' == ModelRM.RemoveMinMaintainingPrev(t''.right, false).unwrap.0;
                assert
                  && minNode.key == ModelRM.RemoveMinMaintainingPrev(t''.right, false).unwrap.1
                  && minNode.value == ModelRM.RemoveMinMaintainingPrev(t''.right, false).unwrap.2
                by {
                  //assume false;
                }
                assert t'' == 
                  (if ModelB.isBlack(t'.right) && !ModelB.isRed(t'.right.left) then
                    var _ :- Guard(t.left.Node?);
                    ModelM.MoveRedRightSize(t');
                    Some(ModelM.MoveRedRight(t'))
                  else
                    Some(t')).unwrap
                by {
                  //assume false;
                }
                assert t' ==
                  (if ModelB.isRed(t.left) then
                    ModelRot.RotateRightSize(t);
                    ModelRot.RotateRight(t)
                  else
                    t)
                by {
                  //assume false;
                }
              }
              ModelR.Remove(t, isLeft, k).unwrap;
              ModelR.Remove(old(TreeModelRec(sk)), isLeft, k).unwrap;
            }
          }
          //assume false;
        }
      }
    }
  }
}
