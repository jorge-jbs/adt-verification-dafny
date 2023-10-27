
  module Array {
    ghost function Elems<A>(l: array<A>): set<A>
      reads l
    {
      set x | x in l[..]
    }

    ghost function Melems<A>(l: array<A>): multiset<A>
      reads l
    {
      multiset(l[..])
    }
  }

 
