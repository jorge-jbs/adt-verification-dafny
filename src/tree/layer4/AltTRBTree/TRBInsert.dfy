include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Base.dfy"
include "../../../../src/tree/layer4/AltTRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Restore.dfy"

module {:options "-functionSyntax:4"} TRBTree.TRBInsert {
  import opened KeyValue
  import opened Color
  import opened Base
  import opened FC = FlipColors
  import opened Rotate
  import opened R = Restore

  function TRBInsert(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V): trbtree
    decreases t
  {
    match t {
      case Empty|Thread(_) => Node(prev, k', v', next, Red)
      case Node(l, k, v, r, c) =>
        if k < k' then
          Restore(Node(l, k, v, TRBInsert(Thread(k), r, next, k', v'), c))
        else if k' < k then
          Restore(Node(TRBInsert(prev, l, Thread(k), k', v'), k, v, r, c))
        else
          Node(l, k, v', r, c)
    }
  }

  function BlackenRoot(t: trbtree): trbtree
  {
    match t {
      case Empty => Empty
      case Node(l, k, v, r, c) =>
        Node(l, k, v, r, Black)
    }
  }

  function TRBInsertRoot(t: trbtree, k: K, v: V): trbtree
  {
    BlackenRoot(TRBInsert(Empty, t, Empty, k, v))
  }

  lemma TRBInsertSpec(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRed(Restore(t).left)
    ensures keys(t) + {k'} == keys(TRBInsert(prev, t, next, k', v'))
    ensures SearchTree(TRBInsert(prev, t, next, k', v'))
    ensures RedBlackTree(TRBInsert(prev, t, next, k', v'))
    ensures BlackHeight(t) == BlackHeight(TRBInsert(prev, t, next, k', v'))
  {
    match t {
      case Empty|Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          TRBInsertSpec(Thread(k), r, next, k', v');
          RestoreSpec(Node(l, k, v, TRBInsert(Thread(k), r, next, k', v'), c));
        } else if k' < k {
          TRBInsertSpec(prev, l, Thread(k), k', v');
          RestoreSpec(Node(TRBInsert(prev, l, Thread(k), k', v'), k, v, r, c));
        } else {
        }
      }
    }
  }

  lemma TRBInsertThreaded(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires t.Node? ==> ThreadedTreeNe(prev, t, next)
    ensures TRBInsert(prev, t, next, k', v').Node?
    ensures ThreadedTreeNe(prev, TRBInsert(prev, t, next, k', v'), next)
  {
    match t {
      case Empty|Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          TRBInsertThreaded(Thread(k), r, next, k', v');
          RestoreThreaded(prev, Node(l, k, v, TRBInsert(Thread(k), r, next, k', v'), c), next);
        } else if k' < k {
          TRBInsertThreaded(prev, l, Thread(k), k', v');
          RestoreThreaded(prev, Node(TRBInsert(prev, l, Thread(k), k', v'), k, v, r, c), next);
        } else {
        }
      }
    }
  }

/*
  // 43"
  lemma {:verify false} TRBInsertModel(lt: option<K>, t: trbtree, rt: option<K>, k': K, v': V)
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

  lemma TRBInsertRootSpec(t: trbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    ensures keys(t) + {k'} == keys(TRBInsertRoot(t, k', v'))
    ensures SearchTree(TRBInsertRoot(t, k', v'))
    ensures RedBlackTreeRoot(TRBInsertRoot(t, k', v'))
  {
    TRBInsertSpec(Empty, t, Empty, k', v');
  }

  lemma TRBInsertRootThreaded(t: trbtree, k': K, v': V)
    decreases t
    requires ThreadedTreeRoot(t)
    ensures ThreadedTreeRoot(TRBInsertRoot(t, k', v'))
  {
    TRBInsertThreaded(Empty, t, Empty, k', v');
  }

  lemma {:verify false} TRBInsertRootModel(t: trbtree, k: K, v: V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    requires SearchTree(TRBInsertRoot(t, k, v))
    ensures toMap(t)[k := v] == toMap(TRBInsertRoot(t, k, v))
  {}
/*
  {
    TRBInsertModel(Nothing, t, Nothing, k, v);
  }
  */
}