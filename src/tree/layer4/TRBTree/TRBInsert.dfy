include "../../../../src/Collections/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"

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
    match t
    case Empty|Thread(_) =>
      Node(prev, k', v', next, Red)
    case Node(l, k, v, r, c) =>
      if k < k' then
        Restore(Node(l, k, v, TRBInsert(Thread(k), r, next, k', v'), c))
      else if k' < k then
        Restore(Node(TRBInsert(prev, l, Thread(k), k', v'), k, v, r, c))
      else
        Node(l, k, v', r, c)
  }

  predicate IsInserted(t: trbtreeOrThread, k': K)
  {
    match t
    case Empty|Thread(_) => true
    case Node(l, k, v, r, c) =>
      if k < k' then
        IsInserted(r, k')
      else if k' < k then
        IsInserted(l, k')
      else
        false
  }

  lemma IsInsertedSpec(t: trbtreeOrThread, k': K)
    requires SearchTree(t)
    ensures IsInserted(t, k') <==> k' !in keys(t)
  {}

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
    ensures !IsInserted(t, k') ==> keys(t) == keys(TRBInsert(prev, t, next, k', v'))
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

  lemma TRBInsertSize(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V)
    decreases t
    ensures
      if IsInserted(t, k') then
        size(TRBInsert(prev, t, next, k', v')) == size(t) + 1
      else
        size(TRBInsert(prev, t, next, k', v')) == size(t)
  {
    match t {
      case Empty|Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          TRBInsertSize(Thread(k), r, next, k', v');
          RestoreSize(Node(l, k, v, TRBInsert(Thread(k), r, next, k', v'), c));
        } else if k' < k {
          TRBInsertSize(prev, l, Thread(k), k', v');
          RestoreSize(Node(TRBInsert(prev, l, Thread(k), k', v'), k, v, r, c));
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
  
  lemma TRBInsertModelLemmaR<A, B>(a: map<A, B>, b: map<A, B>, c: map<A, B>, k: A, v: B)
    ensures a + b + c[k := v] == (a + b + c)[k := v]
  {}

  lemma TRBInsertModelLemmaL<A, B>(a: map<A, B>, b: map<A, B>, c: map<A, B>, k: A, v: B)
    requires k !in b.Keys
    requires k !in c.Keys
    ensures a[k := v] + b + c == (a + b + c)[k := v]
  {}

  lemma TRBInsertModel(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    ensures SearchTree(TRBInsert(prev, t, next, k', v'))
    ensures toMapRec(t)[k' := v'] == toMapRec(TRBInsert(prev, t, next, k', v'))
  {
    match t {
      case Empty|Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          TRBInsertSpec(Thread(k), r, next, k', v');
          RestoreSpec(Node(l, k, v, TRBInsert(Thread(k), r, next, k', v'), c));
          calc == {
            toMapRec(TRBInsert(prev, t, next, k', v'));
            toMapRec(Restore(Node(l, k, v, TRBInsert(Thread(k), r, next, k', v'), c)));
            { RestoreModel(Node(l, k, v, TRBInsert(Thread(k), r, next, k', v'), c)); }
            toMapRec(Node(l, k, v, TRBInsert(Thread(k), r, next, k', v'), c));
            toMapRec(l)
              + map[k := v]
              + toMapRec(TRBInsert(Thread(k), r, next, k', v'));
            { TRBInsertModel(Thread(k), r, next, k', v'); }
            toMapRec(l)
              + map[k := v]
              + toMapRec(r)[k' := v'];
            /*
            {
              TRBInsertModelLemmaR(
                toMapRec(l),
                map[k := v],
                toMapRec(r),
                k',
                v'
              );
            }
            */
            ( toMapRec(l)
                + map[k := v]
                + toMapRec(r))
              [k' := v'];
            toMapRec(t)[k' := v'];
          }
        } else if k' < k {
          TRBInsertSpec(prev, l, Thread(k), k', v');
          RestoreModel(Node(TRBInsert(prev, l, Thread(k), k', v'), k, v, r, c));
          calc == {
            toMapRec(TRBInsert(prev, t, next, k', v'));
            toMapRec(Restore(Node(TRBInsert(prev, l, Thread(k), k', v'), k, v, r, c)));
            { RestoreModel(Node(TRBInsert(prev, l, Thread(k), k', v'), k, v, r, c)); }
            toMapRec(Node(TRBInsert(prev, l, Thread(k), k', v'), k, v, r, c));
            toMapRec(TRBInsert(prev, l, Thread(k), k', v'))
              + map[k := v]
              + toMapRec(r);
            { TRBInsertModel(prev, l, Thread(k), k', v'); }
            toMapRec(l)[k' := v']
              + map[k := v]
              + toMapRec(r);
            {
              assert k' !in toMapRec(r) by {
                assert toMapRec(r).Keys == keys(r) by {
                  ToMapRec(r);
                }
              }
              assert k' != k;
              TRBInsertModelLemmaL(
                toMapRec(l),
                map[k := v],
                toMapRec(r),
                k',
                v'
              );
            }
            ( toMapRec(l)
                + map[k := v]
                + toMapRec(r))
              [k' := v'];
            toMapRec(t)[k' := v'];
          }
        } else {
          assert toMap(t)[k' := v'] == toMap(TRBInsert(prev, t, next, k', v'));
          ToMapRec(t);
          ToMapRec(TRBInsert(prev, t, next, k', v'));
        }
      }
    }
  }

  lemma TRBInsertRootSpec(t: trbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    ensures keys(t) + {k'} == keys(TRBInsertRoot(t, k', v'))
    ensures !IsInserted(t, k') ==> keys(t) == keys(TRBInsertRoot(t, k', v'))
    ensures SearchTree(TRBInsertRoot(t, k', v'))
    ensures RedBlackTreeRoot(TRBInsertRoot(t, k', v'))
  {
    TRBInsertSpec(Empty, t, Empty, k', v');
  }

  lemma TRBInsertRootSize(t: trbtree, k': K, v': V)
    ensures
      if IsInserted(t, k') then
        size(TRBInsertRoot(t, k', v')) == size(t) + 1
      else
        size(TRBInsertRoot(t, k', v')) == size(t)
  {
    TRBInsertSize(Empty, t, Empty, k', v');
  }

  lemma TRBInsertRootThreaded(t: trbtree, k': K, v': V)
    decreases t
    requires ThreadedTreeRoot(t)
    ensures ThreadedTreeRoot(TRBInsertRoot(t, k', v'))
  {
    TRBInsertThreaded(Empty, t, Empty, k', v');
  }

  lemma TRBInsertRootModel(t: trbtree, k: K, v: V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    requires SearchTree(TRBInsertRoot(t, k, v))
    ensures toMapRec(t)[k := v] == toMapRec(TRBInsertRoot(t, k, v))
  {
    TRBInsertModel(Empty, t, Empty, k, v);
  }
}