include "../../../src/MUtils.dfy"

module TTree {
  import opened Utils

  datatype ttree<A> = Empty | Node(left: ttreePointer<A>, data: A, right: ttreePointer<A>)
  datatype ttreePointer<A> = Child(child: ttree<A>) | Thread(thread: A)

  function method elemsP<A>(p: ttreePointer<A>): set<A>
    ensures p.Child? ==> elemsP(p) == elems(p.child)
  {
    match p {
      case Child(p) => elems(p)
      case Thread(_) => {}
    }
  }

  function method elems<A>(t: ttree<A>): set<A>
    //ensures t.Empty? ==> elems(t) == {}
    //ensures t.Node? ==> elems(t) == elemsP(t.left) + {t.data} + elemsP(t.right)
  {
    match t {
      case Empty => {}
      case Node(l, x, r) => elemsP(l) + {x} + elemsP(r)
    }
  }

  function method elemsAndThreadsP<A>(t: ttreePointer<A>): set<A>
  {
    match t {
      case Child(t) => elemsAndThreads(t)
      case Thread(x) => {x}
    }
  }

  function method elemsAndThreads<A>(t: ttree<A>): set<A>
  {
    match t {
      case Empty => {}
      case Node(l, x, r) => elemsAndThreadsP(l) + {x} + elemsAndThreadsP(r)
    }
  }

  predicate SubtreeP<A>(node: ttree<A>, proot: ttreePointer<A>)
    ensures SubtreeP(node, proot) ==> elems(node) <= elemsP(proot)
    ensures SubtreeP(node, proot) ==> elemsAndThreads(node) <= elemsAndThreadsP(proot)
  {
    match proot {
      case Child(root) => Subtree(node, root)
      case Thread(_) => false
    }
  }

  predicate Subtree<A>(node: ttree<A>, root: ttree<A>)
    ensures Subtree(node, root) ==> elems(node) <= elems(root)
    ensures Subtree(node, root) ==> elemsAndThreads(node) <= elemsAndThreads(root)
  {
    || root == node
    || (
      && root.Node?
      && (SubtreeP(node, root.left) || SubtreeP(node, root.right)))
  }

/*
  function method elemsAndThreads<A>(t: ttree<A>): set<A>
    ensures t.Empty? ==> elemsAndThreads(t) == {}
    ensures t.Thread? ==> elemsAndThreads(t) == {t.thread}
    ensures t.Node? ==> elemsAndThreads(t) == elemsAndThreads(t.left) + {t.data} + elemsAndThreads(t.right)
  {
    match t {
      case Empty => {}
      case Thread(x) => {x}
      case Node(l, x, r) => elemsAndThreads(l) + {x} + elemsAndThreads(r)
    }
  }

  function method subtrees<A(==)>(t: ttree<A>): set<ttree<A>>
    ensures t.Empty? ==> elemsAndThreads(t) == {}
    ensures t.Thread? ==> elemsAndThreads(t) == {t.thread}
    ensures t.Node? ==> elemsAndThreads(t) == elemsAndThreads(t.left) + {t.data} + elemsAndThreads(t.right)
  {
    match t {
      case Empty => {}
      case Thread(x) => {t}
      case Node(l, x, r) => subtrees(l) + {t} + subtrees(r)
    }
  }
  */
}
