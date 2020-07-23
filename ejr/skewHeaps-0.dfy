/*

Skew Heaps
Copyright: Specified and verified by Ricardo Peña, February 2019

*/

// Skew Heaps are just binary trees holding the so-called heap property
datatype Skew = Empty  |  Node (left: Skew, key: int, right: Skew)

// This is the Skew Heap invariant
predicate isSkew (t: Skew)
{
   match t
      case Empty       => true
      case Node(l,x,r) => isSkew(l) && isSkew(r) && heap(l, x, r)
}

// This is the heap property at the root level
predicate heap(l:Skew, x:int, r:Skew)
{
   forall z | z in mset(l) + mset(r) :: x <= z
}

// this is the mathematical model implemented by a Skew Heap
function mset(t:Skew): multiset<int>
{
   match t
      case Empty       => multiset{}
      case Node(l,x,r) => mset(l) + multiset{x} + mset(r)
}

// This funtion joins two Skew heaps in worst case logarithmic time
function method join(t1:Skew, t2:Skew): (res:Skew)
  requires isSkew(t1)
  requires isSkew(t2)
  ensures isSkew(res)
  ensures mset(res) == mset(t1) + mset(t2)
{
    match t1
     case Empty             => t2
     case Node(l1,x1,r1) => match t2
            case Empty          => t1
            case Node(l2,x2,r2) => if x1 <= x2
                                   then Node(join(r1,t2),x1,l1)
                                   else Node(join(t1,r2),x2,l2)
}
/*
   Exercises
*/
// 1. Provide the specification and verification of the above function method join

// 2. Provide the specification, code and verification of the following function method
// It inserts an element in a Skew Heap in worst case logarithmic time
function method insert(x:int, t:Skew): (res:Skew)
  requires isSkew(t)
  ensures isSkew(res)
  ensures mset(res) == mset(t) + multiset{x}
{
  join(Node(Empty, x, Empty), t)
}

// 3. Provide the specification, code and verification of the following function method
// It gets the minimum of a Skew Heap in constant time
function method min(t:Skew): (res: int)
  requires t != Empty
  requires isSkew(t)
  ensures res in mset(t)
  ensures forall z | z in mset(t) :: res <= z
{
  t.key
}

// 4. Provide the specification, code and verification of the following function method
// It deletes the minimum of a Skew Heap in worst case logarithmic time
function method deleteMin(t:Skew): (res:Skew)
  requires t != Empty
  requires isSkew(t)
  ensures mset(res) == mset(t) - multiset{min(t)}
  ensures isSkew(res)
{
  join(t.left, t.right)
}
