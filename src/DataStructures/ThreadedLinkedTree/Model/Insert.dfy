include "../../../../src/Collections/KeyValue.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/FlipColors.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Rotate.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Restore.dfy"

module {:options "-functionSyntax:4"} ThreadedLinkedTree.Model.Insert {
  import opened KeyValue
  import opened Color
  import opened Base
  import opened FC = FlipColors
  import opened Rotate
  import opened R = Restore

  function Insert(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V): trbtree
    decreases t
  {
    match t
    case Empty|Thread(_) =>
      Node(prev, k', v', next, Red)
    case Node(l, k, v, r, c) =>
      if k < k' then
        Restore(Node(l, k, v, Insert(Thread(k), r, next, k', v'), c))
      else if k' < k then
        Restore(Node(Insert(prev, l, Thread(k), k', v'), k, v, r, c))
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

  function InsertRoot(t: trbtree, k: K, v: V): trbtree
  {
    BlackenRoot(Insert(Empty, t, Empty, k, v))
  }

  lemma InsertSpec(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRed(Restore(t).left)
    ensures keys(t) + {k'} == keys(Insert(prev, t, next, k', v'))
    ensures !IsInserted(t, k') ==> keys(t) == keys(Insert(prev, t, next, k', v'))
    ensures SearchTree(Insert(prev, t, next, k', v'))
    ensures RedBlackTree(Insert(prev, t, next, k', v'))
    ensures BlackHeight(t) == BlackHeight(Insert(prev, t, next, k', v'))
  {
    match t {
      case Empty|Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          InsertSpec(Thread(k), r, next, k', v');
          RestoreSpec(Node(l, k, v, Insert(Thread(k), r, next, k', v'), c));
        } else if k' < k {
          InsertSpec(prev, l, Thread(k), k', v');
          RestoreSpec(Node(Insert(prev, l, Thread(k), k', v'), k, v, r, c));
        } else {
        }
      }
    }
  }

  lemma InsertSize(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V)
    decreases t
    ensures
      if IsInserted(t, k') then
        size(Insert(prev, t, next, k', v')) == size(t) + 1
      else
        size(Insert(prev, t, next, k', v')) == size(t)
  {
    match t {
      case Empty|Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          InsertSize(Thread(k), r, next, k', v');
          RestoreSize(Node(l, k, v, Insert(Thread(k), r, next, k', v'), c));
        } else if k' < k {
          InsertSize(prev, l, Thread(k), k', v');
          RestoreSize(Node(Insert(prev, l, Thread(k), k', v'), k, v, r, c));
        } else {
        }
      }
    }
  }

  lemma InsertThreaded(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires t.Node? ==> ThreadedTreeNe(prev, t, next)
    ensures Insert(prev, t, next, k', v').Node?
    ensures ThreadedTreeNe(prev, Insert(prev, t, next, k', v'), next)
  {
    match t {
      case Empty|Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          InsertThreaded(Thread(k), r, next, k', v');
          RestoreThreaded(prev, Node(l, k, v, Insert(Thread(k), r, next, k', v'), c), next);
        } else if k' < k {
          InsertThreaded(prev, l, Thread(k), k', v');
          RestoreThreaded(prev, Node(Insert(prev, l, Thread(k), k', v'), k, v, r, c), next);
        } else {
        }
      }
    }
  }
  
  lemma InsertModelLemmaR<A, B>(a: map<A, B>, b: map<A, B>, c: map<A, B>, k: A, v: B)
    ensures a + b + c[k := v] == (a + b + c)[k := v]
  {}

  lemma InsertModelLemmaL<A, B>(a: map<A, B>, b: map<A, B>, c: map<A, B>, k: A, v: B)
    requires k !in b.Keys
    requires k !in c.Keys
    ensures a[k := v] + b + c == (a + b + c)[k := v]
  {}

  lemma InsertModel(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    ensures SearchTree(Insert(prev, t, next, k', v'))
    ensures toMapRec(t)[k' := v'] == toMapRec(Insert(prev, t, next, k', v'))
  {
    match t {
      case Empty|Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          InsertSpec(Thread(k), r, next, k', v');
          RestoreSpec(Node(l, k, v, Insert(Thread(k), r, next, k', v'), c));
          calc == {
            toMapRec(Insert(prev, t, next, k', v'));
            toMapRec(Restore(Node(l, k, v, Insert(Thread(k), r, next, k', v'), c)));
            { RestoreModel(Node(l, k, v, Insert(Thread(k), r, next, k', v'), c)); }
            toMapRec(Node(l, k, v, Insert(Thread(k), r, next, k', v'), c));
            toMapRec(l)
              + map[k := v]
              + toMapRec(Insert(Thread(k), r, next, k', v'));
            { InsertModel(Thread(k), r, next, k', v'); }
            toMapRec(l)
              + map[k := v]
              + toMapRec(r)[k' := v'];
            /*
            {
              InsertModelLemmaR(
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
          InsertSpec(prev, l, Thread(k), k', v');
          RestoreModel(Node(Insert(prev, l, Thread(k), k', v'), k, v, r, c));
          calc == {
            toMapRec(Insert(prev, t, next, k', v'));
            toMapRec(Restore(Node(Insert(prev, l, Thread(k), k', v'), k, v, r, c)));
            { RestoreModel(Node(Insert(prev, l, Thread(k), k', v'), k, v, r, c)); }
            toMapRec(Node(Insert(prev, l, Thread(k), k', v'), k, v, r, c));
            toMapRec(Insert(prev, l, Thread(k), k', v'))
              + map[k := v]
              + toMapRec(r);
            { InsertModel(prev, l, Thread(k), k', v'); }
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
              InsertModelLemmaL(
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
          assert toMap(t)[k' := v'] == toMap(Insert(prev, t, next, k', v'));
          ToMapRec(t);
          ToMapRec(Insert(prev, t, next, k', v'));
        }
      }
    }
  }

  lemma InsertRootSpec(t: trbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    ensures keys(t) + {k'} == keys(InsertRoot(t, k', v'))
    ensures !IsInserted(t, k') ==> keys(t) == keys(InsertRoot(t, k', v'))
    ensures SearchTree(InsertRoot(t, k', v'))
    ensures RedBlackTreeRoot(InsertRoot(t, k', v'))
  {
    InsertSpec(Empty, t, Empty, k', v');
  }

  lemma InsertRootSize(t: trbtree, k': K, v': V)
    ensures
      if IsInserted(t, k') then
        size(InsertRoot(t, k', v')) == size(t) + 1
      else
        size(InsertRoot(t, k', v')) == size(t)
  {
    InsertSize(Empty, t, Empty, k', v');
  }

  lemma InsertRootThreaded(t: trbtree, k': K, v': V)
    decreases t
    requires ThreadedTreeRoot(t)
    ensures ThreadedTreeRoot(InsertRoot(t, k', v'))
  {
    InsertThreaded(Empty, t, Empty, k', v');
  }

  lemma InsertRootModel(t: trbtree, k: K, v: V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    requires SearchTree(InsertRoot(t, k, v))
    ensures toMapRec(t)[k := v] == toMapRec(InsertRoot(t, k, v))
  {
    InsertModel(Empty, t, Empty, k, v);
  }
}