include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"

module TRBTree.TRBInsert {
  import opened KeyValue
  import opened Color
  import opened Base
  import opened FC = FlipColors
  import opened Rotate
  import opened R = Restore

  function method TRBInsertP(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, k': K, v': V): pointer
    decreases p
  {
    match p {
      case Child(t) => Child(TRBInsert(prev, t, next, k', v'))
      case Thread(k) => Child(Node(prev, k', v', next, Red))
    }
  }

  function method TRBInsert(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty, k': K, v': V): rbtree
    decreases t
  {
    match t {
      case Empty => Node(prev, k', v', next, Red)
      case Node(l, k, v, r, c) =>
        if k < k' then
          Restore(Node(l, k, v, TRBInsertP(Thread(k), r, next, k', v'), c))
        else if k' < k then
          Restore(Node(TRBInsertP(prev, l, Thread(k), k', v'), k, v, r, c))
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

  function method TRBInsertRoot(t: rbtree, k: K, v: V): rbtree
  {
    BlackenRoot(TRBInsert(Child(Empty), t, Child(Empty), k, v))
  }

  lemma TRBInsertPSpec(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, k': K, v': V)
    decreases p
    requires SearchTreeP(p)
    requires RedBlackTreeP(p)
    requires !(isRedP(p) && isRedP(p.child.left))
    ensures isBlackP(p) && isRed(Restore(p.child)) ==>
      !isRedP(Restore(p.child).left)
    ensures keysP(p) + {k'} == keysP(TRBInsertP(prev, p, next, k', v'))
    ensures SearchTreeP(TRBInsertP(prev, p, next, k', v'))
    ensures RedBlackTreeP(TRBInsertP(prev, p, next, k', v'))
    ensures BlackHeightP(p) == BlackHeightP(TRBInsertP(prev, p, next, k', v'))
  {
    match p {
      case Child(t) => {
        TRBInsertSpec(prev, t, next, k', v');
      }
      case Thread(k) => {
      }
    }
  }

  // 7"
  lemma {:verify false} TRBInsertSpec(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRedP(t.left))
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRedP(Restore(t).left)
    ensures keys(t) + {k'} == keys(TRBInsert(prev, t, next, k', v'))
    ensures SearchTree(TRBInsert(prev, t, next, k', v'))
    ensures RedBlackTree(TRBInsert(prev, t, next, k', v'))
    ensures BlackHeight(t) == BlackHeight(TRBInsert(prev, t, next, k', v'))
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          TRBInsertPSpec(Thread(k), r, next, k', v');
          RestoreSpec(Node(l, k, v, TRBInsertP(Thread(k), r, next, k', v'), c));
        } else if k' < k {
          TRBInsertPSpec(prev, l, Thread(k), k', v');
          RestoreSpec(Node(TRBInsertP(prev, l, Thread(k), k', v'), k, v, r, c));
        } else {
        }
      }
    }
  }

  lemma TRBInsertPThreaded(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, k': K, v': V)
    decreases p
    requires ThreadedTreeRecPL(prev, p, next) || ThreadedTreeRecPR(prev, p, next)
    ensures TRBInsertP(prev, p, next, k', v').Child?
    ensures TRBInsertP(prev, p, next, k', v').child.Node?
    ensures ThreadedTreeRecPR(prev, TRBInsertP(prev, p, next, k', v'), next)
    ensures ThreadedTreeRecPL(prev, TRBInsertP(prev, p, next, k', v'), next)
  {
    match p {
      case Child(t) => {
        TRBInsertThreaded(prev, t, next, k', v');
      }
      case Thread(k) => {
      }
    }
  }

  lemma TRBInsertThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires t.Node? ==> ThreadedTreeRec(prev, t, next)
    ensures TRBInsert(prev, t, next, k', v').Node?
    ensures ThreadedTreeRec(prev, TRBInsert(prev, t, next, k', v'), next)
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          TRBInsertPThreaded(Thread(k), r, next, k', v');
          RestoreThreaded(prev, Node(l, k, v, TRBInsertP(Thread(k), r, next, k', v'), c), next);
        } else if k' < k {
          TRBInsertPThreaded(prev, l, Thread(k), k', v');
          RestoreThreaded(prev, Node(TRBInsertP(prev, l, Thread(k), k', v'), k, v, r, c), next);
        } else {
        }
      }
    }
  }

/*
  // 43"
  lemma {:verify false} TRBInsertModel(lt: option<K>, t: rbtree, rt: option<K>, k': K, v': V)
    decreases t
    requires !t.Thread?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    requires SearchTree(TRBInsert(lt, t, rt, k', v'))
    ensures toMap(t)[k' := v'] == toMap(TRBInsert(lt, t, rt, k', v'))
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          if r.Thread? {
            RestoreSpec(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c));
            calc == {
              toMap(TRBInsert(lt, Node(l, k, v, r, c), rt, k', v'));
              toMap(Restore(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c)));
              { RestoreModel(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c)); }
              toMap(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c));
              { toMapLemmas(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c)); }
              toMap(l) + map[k := v] + toMap(Node(Thread(k), k', v', Thread(fromThread(r)), Red));
              { toMapLemmas(Node(Thread(k), k', v', Thread(fromThread(r)), Red)); }
              toMap(l) + map[k := v] + (map[] + map[k' := v'] + map[]);
              toMap(l) + map[k := v] + map[k' := v'];
              (toMap(l) + map[k := v]) + map[k' := v'];
              (toMap(l) + map[k := v] + toMap(r)) + map[k' := v'];
              { toMapLemmas(t); }
              toMap(t) + map[k' := v'];
            }
          } else {
            TRBInsertSpec(Some(k), r, rt, k', v');
            calc == {
              toMap(TRBInsert(lt, Node(l, k, v, r, c), rt, k', v'));
              toMap(Restore(Node(l, k, v, TRBInsert(Some(k), r, rt, k', v'), c)));
              { RestoreModel(Node(l, k, v, TRBInsert(Some(k), r, rt, k', v'), c)); }
              toMap(Node(l, k, v, TRBInsert(Some(k), r, rt, k', v'), c));
              { toMapLemmas(Node(l, k, v, TRBInsert(Some(k), r, rt, k', v'), c)); }
              toMap(l) + map[k := v] + toMap(TRBInsert(Some(k), r, rt, k', v'));
              { TRBInsertModel(Some(k), r, rt, k', v'); }
              toMap(l) + map[k := v] + toMap(r)[k' := v'];
              toMap(l) + map[k := v] + toMap(r) + map[k' := v'];
              toMap(t) + map[k' := v'];
            }
          }
        } else if k' < k {
          if l.Thread? {
            RestoreSpec(Node(Node(Thread(fromThread(l)), k', v', Thread(k), Red), k, v, r, c));
            calc == {
              toMap(TRBInsert(lt, Node(l, k, v, r, c), rt, k', v'));
              toMap(Node(Node(Thread(fromThread(l)), k', v', Thread(k), Red), k, v, r, c));
              toMap(Node(Thread(fromThread(l)), k', v', Thread(k), Red)) + map[k := v] + toMap(r);
              { toMapLemmas(Node(Thread(fromThread(l)), k', v', Thread(k), Red)); }
              (map[] + map[k' := v'] + map[]) + map[k := v] + toMap(r);
              map[k' := v'] + map[k := v] + toMap(r);
              toMap(l) + map[k := v] + toMap(r) + map[k' := v'];
              toMap(t) + map[k' := v'];
            }
          } else {
            TRBInsertSpec(lt, l, Some(k), k', v');
            calc == {
              toMap(TRBInsert(lt, Node(l, k, v, r, c), rt, k', v'));
              toMap(Restore(Node(TRBInsert(lt, l, Some(k), k', v'), k, v, r, c)));
              { RestoreModel(Node(TRBInsert(lt, l, Some(k), k', v'), k, v, r, c)); }
              toMap(Node(TRBInsert(lt, l, Some(k), k', v'), k, v, r, c));
              { toMapLemmas(Node(TRBInsert(lt, l, Some(k), k', v'), k, v, r, c)); }
              toMap(TRBInsert(lt, l, Some(k), k', v')) + map[k := v] + toMap(r);
              { TRBInsertModel(lt, l, Some(k), k', v'); }
              toMap(l)[k' := v'] + map[k := v] + toMap(r);
              toMap(l) + map[k' := v'] + map[k := v] + toMap(r);
              toMap(l) + map[k := v] + toMap(r) + map[k' := v'];
              toMap(t) + map[k' := v'];
            }
          }
        } else {
        }
      }
    }
  }
  */

  lemma TRBInsertRootSpec(t: rbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    ensures keys(t) + {k'} == keys(TRBInsertRoot(t, k', v'))
    ensures SearchTree(TRBInsertRoot(t, k', v'))
    ensures RedBlackTreeRoot(TRBInsertRoot(t, k', v'))
  {
    TRBInsertSpec(Child(Empty), t, Child(Empty), k', v');
  }

  lemma TRBInsertRootThreaded(t: rbtree, k': K, v': V)
    decreases t
    requires ThreadedTreeRoot(t)
    ensures ThreadedTreeRoot(TRBInsertRoot(t, k', v'))
  {
    TRBInsertThreaded(Child(Empty), t, Child(Empty), k', v');
  }

  lemma TRBInsertRootModel(t: rbtree, k: K, v: V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    requires SearchTree(TRBInsertRoot(t, k, v))
    ensures toMap(t)[k := v] == toMap(TRBInsertRoot(t, k, v))
/*
  {
    TRBInsertModel(Nothing, t, Nothing, k, v);
  }
  */
}