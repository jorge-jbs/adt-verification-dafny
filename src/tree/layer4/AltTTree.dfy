include "../../../src/MUtils.dfy"

module TTree {
  import opened Utils

  datatype ttreeOrThread<A>
    = Empty
    | Thread(thread: A)
    | Node(left: ttreeOrThread<A>, data: A, right: ttreeOrThread<A>)

  type ttree<A> = t: ttreeOrThread<A> | t.Empty? || t.Node? witness Empty
  type nettree<A> = t: ttreeOrThread<A> | t.Node? witness *
  type threadOrEmpty<A> = t: ttreeOrThread<A> | t.Empty? || t.Thread? witness Empty

  function elems<A>(t: ttreeOrThread<A>): set<A>
  {
    match t
    case Empty => {}
    case Thread(_) => {}
    case Node(l, x, r) => elems(l) + {x} + elems(r)
  }

  function elemsAndThreads<A>(t: ttreeOrThread<A>): set<A>
  {
    match t
    case Empty => {}
    case Thread(x) => {x}
    case Node(l, x, r) => elemsAndThreads(l) + {x} + elemsAndThreads(r)
  }

  predicate ThreadsInParentsRec<A>(t: ttreeOrThread<A>, parents: set<A>)
  {
    match t
    case Empty => true
    case Thread(x) => x in parents
    case Node(l, x, r) =>
      && ThreadsInParentsRec(l, parents + {x})
      && ThreadsInParentsRec(r, parents + {x})
  }

  lemma ThreadsInParentsSub<A>(t: ttreeOrThread<A>, parents: set<A>, parents': set<A>)
    requires ThreadsInParentsRec(t, parents)
    requires parents <= parents'
    ensures ThreadsInParentsRec(t, parents')
  {
    match t
    case Empty => {}
    case Thread(_) => {}
    case Node(l, x, r) => {
      ThreadsInParentsSub(l, parents + {x}, parents' + {x});
      ThreadsInParentsSub(r, parents + {x}, parents' + {x});
    }
  }

  lemma AllThreadsInParentsSub<A>()
    ensures
      forall t: ttreeOrThread<A>, parents: set<A>, parents': set<A> |
          && ThreadsInParentsRec(t, parents)
          && parents <= parents' ::
        ThreadsInParentsRec(t, parents')
  {
    forall t: ttreeOrThread<A>, parents: set<A>, parents': set<A> |
        && ThreadsInParentsRec(t, parents)
        && parents <= parents'
      ensures ThreadsInParentsRec(t, parents')
    {
      ThreadsInParentsSub(t, parents, parents');
    }
  }

  predicate ThreadsInParentsRoot<A(==)>(t: ttreeOrThread<A>)
  {
    ThreadsInParentsRec(t, {})
  }

  lemma ElemsAndThreadsRec<A>(t: ttree<A>, parents: set<A>)
      returns (threads: set<A>)
    requires ThreadsInParentsRec(t, parents)
    ensures elemsAndThreads(t) <= elems(t) + parents
    ensures threads <= parents
    ensures elemsAndThreads(t) == elems(t) + threads 
  {
    if t.Node? {
      var threadsL;
      if !t.left.Thread? {
        threadsL := ElemsAndThreadsRec(t.left, parents + {t.data});
      } else {
        threadsL := {t.left.thread};
      }
      var threadsR;
      if !t.right.Thread? {
        threadsR := ElemsAndThreadsRec(t.right, parents + {t.data});
      } else {
        threadsR := {t.right.thread};
      }
      return threadsL + threadsR - {t.data};
    } else {
      return {};
    }
  }

  lemma ElemsAndThreads<A>(t: ttree<A>)
    requires ThreadsInParentsRoot(t)
    ensures elems(t) == elemsAndThreads(t)
  {
    var _ := ElemsAndThreadsRec(t, {});
  }

  function ThreadedRecL<A(==)>(prev: threadOrEmpty<A>, t: ttreeOrThread<A>, next: threadOrEmpty<A>): bool
    decreases t, 1
  {
    match t {
      case Empty => prev.Empty?
      case Thread(k) => prev.Thread? && prev.thread == k
      //case Node(_, _, _, _, _) => ThreadedNe(prev, t, next)
      case Node(l, x, r) =>
        && ThreadedRecL(prev, l, Thread(x))
        && ThreadedRecR(Thread(x), r, next)
    }
  }

  function ThreadedRecR<A(==)>(prev: threadOrEmpty<A>, t: ttreeOrThread<A>, next: threadOrEmpty<A>): bool
    decreases t, 1
  {
    match t {
      case Empty => next.Empty?
      case Thread(x) => next.Thread? && next.thread == x
      //case Node(_, _, _, _, _) => ThreadedNe(prev, t, next)
      case Node(l, x, r) =>
        && ThreadedRecL(prev, l, Thread(x))
        && ThreadedRecR(Thread(x), r, next)
    }
  }

  function ThreadedRecCond<A(==)>(
      prev: threadOrEmpty<A>,
      t: ttreeOrThread<A>,
      next: threadOrEmpty<A>,
      isLeft: bool
    ): bool
  {
    if isLeft then
      ThreadedRecL(prev, t, next)
    else
      ThreadedRecR(prev, t, next)
  }

  function ThreadedNe<A(==)>(prev: threadOrEmpty<A>, t: nettree<A>, next: threadOrEmpty<A>): bool
    decreases t, 0
  {
    match t {
      case Node(l, x, r) =>
        && ThreadedRecL(prev, l, Thread(x))
        && ThreadedRecR(Thread(x), r, next)
    }
  }

  function ThreadedRoot<A(==)>(t: ttree<A>): bool
  {
    t.Empty? || ThreadedNe(Empty, t, Empty)
  }

  predicate Subtree<A(==)>(node: ttreeOrThread<A>, root: ttreeOrThread<A>)
    ensures Subtree(node, root) ==> elems(node) <= elems(root)
    ensures Subtree(node, root) ==> elemsAndThreads(node) <= elemsAndThreads(root)
  {
    || root == node
    || (
      && root.Node?
      && (Subtree(node, root.left) || Subtree(node, root.right)))
  }
}
