datatype Tree<A(==)>
  = Node(root: A, children: set<Tree<A>>)

function method elemsTree<A>(t: Tree<A>): set<A>
{
  match t {
    // case Empty => {}
    case Node(x, children) => {x} + set y, c | c in children && y in elemsTree(c) :: y
  }
}

// function method MapMultiSet<A, B>(f: A -> B, m: multiset<A>): multiset<B>
// {
//   if e :| e in m then
//     multiset{f(e)} + MapMultiSet(f, m - multiset{e})
//   else
//     multiset{}
// }

// function method UnionMultiSet<A>(m: multiset<multiset<A>>): multiset<A>
// {
//   if s :| s in m then
//     s + UnionMultiSet(m - multiset{s})
//   else
//     multiset{}
// }

// function method melems<A>(t: Tree<A>): multiset<A>
// {
//   match t {
//     case Empty => {}
//     case Node(x, children) =>
//       multiset{x}
//       + if children == multiset{} then
//           {}
//         else
//   }
// }
