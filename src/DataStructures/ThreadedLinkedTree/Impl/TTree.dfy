/*
Abstract threaded tree used to represent the skeleton of a threaded linked tree.
*/

module ThreadedLinkedTree.Impl.TTree {
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

  lemma ElemsInElemsAndThreads<A>(t: ttreeOrThread<A>)
    ensures elems(t) <= elemsAndThreads(t)
  {
    if t.Node? {
      ElemsInElemsAndThreads(t.left);
      ElemsInElemsAndThreads(t.right);
    }
  }

  lemma ElemsAndThreadsRec<A>(
      prev: threadOrEmpty, 
      sk: ttreeOrThread<A>, 
      next: threadOrEmpty, 
      visited: set<A>
    )
      returns (threads: set<A>)
    decreases sk
    requires prev.Thread? ==> prev.thread in visited
    requires next.Thread? ==> next.thread in visited
    requires ThreadedRecL(prev, sk, next) || ThreadedRecR(prev, sk, next)
    ensures elemsAndThreads(sk) <= elems(sk) + visited
    ensures threads <= visited
    ensures elemsAndThreads(sk) == elems(sk) + threads
  {
    match sk
    case Empty => {
      return {};
    }
    case Thread(n) => {
      return {n};
    }
    case Node(l, x, r) => {
      var threadsL := ElemsAndThreadsRec(prev, sk.left, Thread(sk.data), visited + {sk.data});
      var threadsR := ElemsAndThreadsRec(Thread(sk.data), sk.right, next, visited + {sk.data});
      return threadsL + threadsR - {sk.data};
    }
  }

  lemma ElemsAndThreads<A>(t: ttree<A>)
    requires ThreadedRoot(t)
    ensures elems(t) == elemsAndThreads(t)
  {
    var _ := ElemsAndThreadsRec(Empty, t, Empty, {});
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
