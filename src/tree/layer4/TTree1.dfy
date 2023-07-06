include "../../../src/MUtils.dfy"

module Tree {
  import opened Utils

  datatype ttree<A> = Empty | Node(left: ttreePointer<A>, data: A, right: ttreePointer<A>)
  datatype ttreePointer<A> = Child(child: ttree<A>) | Thread(thread: A)

  function method elemsP<A>(t: ttreePointer<A>): set<A>
  {
    match t {
      case Child(t) => elems(t)
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
