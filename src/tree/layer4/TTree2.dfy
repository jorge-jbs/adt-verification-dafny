include "../../../src/MUtils.dfy"

module Tree {
  import opened Utils

  datatype ttree<A> = Empty | Thread(thread: A) | Node(left: ttree<A>, data: A, right: ttree<A>)

  function method elems<A>(t: ttree<A>): set<A>
    ensures t.Empty? || t.Thread? ==> elems(t) == {}
    ensures t.Node? ==> elems(t) == elems(t.left) + {t.data} + elems(t.right)
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, x, r) => elems(l) + {x} + elems(r)
    }
  }

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
}
