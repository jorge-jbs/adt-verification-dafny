/*

Binary Search Trees (BST)
Copyright: Specified and verified by Ricardo Peña, February 2019

*/

// BSTs are binary trees having unique keys and sorted inorder traversal
datatype BST = Empty  |  Node (left: BST, key: int, right: BST)

// This is the BST invariant
predicate isBST (t: BST)
{
  match t
    case Empty       => true
    case Node(l,x,r) => promising(l,x,r) && isBST(l) && isBST(r)
}

// This is the BST property at the root level
predicate promising(l:BST, x:int, r:BST)
{
   (forall z :: z in tset(l) ==> z < x) &&
   (forall z :: z in tset(r) ==> x < z)
}

function tset(t:BST): set<int>
{
   match t
      case Empty       => {}
      case Node(l,x,r) => tset(l)+{x}+tset(r)
}

function inorder(t: BST): seq<int>
{
   match t
      case Empty       => []
      case Node(l,x,r) => inorder(l) + [x] + inorder(r)
}
// It searchs whether an element is present in a BST
function method search(x:int, t:BST): (res:bool)
  requires isBST(t)
  ensures res == (x in tset(t))
{
  match t
    case Empty => false
    case Node(left, key, right) =>
      if x == key then
        true
      else if x < key then
        search(x, left)
      else
        search(x, right)
}

// It inserts an element in a BST
function method insert(x:int, t:BST): (res:BST)
  requires isBST(t)
  ensures  isBST(res)
  ensures  tset(res) == tset(t) + {x}
{
  match t
    case Empty => Node(Empty, x, Empty)
    case Node(left, key, right) =>
      if x == key then
        t
      else if x < key then
        Node(insert(x, left), key, right)
      else
        Node(left, key, insert(x, right))
}

function method union(l: BST, r: BST): (res: BST)
  decreases l
  requires isBST(l)
  requires isBST(r)
  ensures isBST(res)
  ensures tset(res) == tset(l) + tset(r)
{
  match l
    case Empty => r
    case Node(A, x, B) =>
      union(A, union(B, insert(x, r)))
}

// It deletes an element from a BST
function method delete(x:int, t:BST): (res:BST)
  requires isBST(t)
  ensures  isBST(res)
  ensures  tset(res) == tset(t) - {x}
{
  match t
    case Empty => Empty
    case Node(left, key, right) =>
      if x == key then
        match left
          case Empty => right
          case Node(_, _, _) =>
            union(left, right)
      else if x < key then
        Node(delete(x, left), key, right)
      else
        Node(left, key, delete(x, right))
}

// It deletes the minimum element of a non empty BST
function method deleteMin (t: BST): (res: (int, BST))
  requires isBST(t) && t != Empty
  ensures res.0 in tset(t)
  ensures forall x | x in tset(t)-{res.0} :: res.0 < x
  ensures isBST(res.1)
  ensures tset(res.1) == tset(t) - {res.0}
{
  if t.left == Empty then
    (t.key, t.right)
  else
    var rec := deleteMin(t.left);
    (rec.0, Node(rec.1, t.key, t.right))
}

predicate sorted(s: seq<int>)
{
    forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

/*
     Exercises
*/

// 1. Prove the following two lemmas

lemma inorderPreservesSet (t: BST)
  ensures forall z | z in inorder(t) :: z in tset(t)
{
  match t
    case Empty => {}
    case Node(_, _, _) => {}
}

lemma sortedInorder(t: BST)
  requires isBST(t)
  ensures  sorted(inorder(t))
{
  match t
    case Empty => {}
    case Node(l, x, r) => {
      inorderPreservesSet(l);
      inorderPreservesSet(r);
      sortedInorder(l);
      assert sorted(inorder(l));
      sortedInorder(r);
      assert sorted(inorder(r));
      assert forall z | z in inorder(l) :: z < x;
      assert forall z | z in inorder(r) :: x < z;
      if inorder(l) == [] {
        if inorder(r) == [] {
        } else {
          assert inorder(r)[0] in inorder(r);
        }
      } else {
        calc == {
          inorder(t);
          inorder(Node(l, x, r));
          inorder(l) + [x] + inorder(r);
        }
        assert inorder(l)[|inorder(l)|-1] in inorder(l);
        if inorder(r) == [] {
        } else {
          assert inorder(r)[0] in inorder(r);
          assert sorted(inorder(l) + [x] + inorder(r));
          assert sorted(inorder(t));
        }
      }
    }
}

// 2. Program a function mirror which gets the symmetric image of a tree along
//    a vertical axis passing through the root and prove the postcondition shown

function mirror(t:BST):(res:BST)
  ensures tset(res)==tset(t)
{
  match t
    case Empty => Empty
    case Node(l, x, r) => Node(mirror(r), x, mirror(l))
}

// 3. We give you this function returning the reverse of a sequence

function rev <T> (s:seq<T>): (res:seq<T>)
{
   if s==[] then []
            else rev(s[1..]) + [s[0]]
}

lemma revConcat<T>(r: seq<T>, s: seq<T>)
  ensures rev(r + s) == rev(s) + rev(r)
{
  if r == [] {
    if s == [] {
    } else {
      calc == {
        rev([] + s);
        { assert [] + s == s; }
        rev(s);
        rev(s) + rev([]);
      }
    }
  } else {
    calc == {
      rev(r + s);
      rev((r + s)[1..]) + [r[0]];
      { assert (r + s)[1..] == r[1..] + s; }
      rev(r[1..] + s) + [r[0]];
      { revConcat(r[1..], s); }
      rev(s) + rev(r[1..]) + [r[0]];
      rev(s) + rev(r);
    }
  }
}

// then, prove the following additional postcondition for function mirror
// ensures inorder(res) == rev(inorder(t))

lemma mirrorInorder(t: BST)
  ensures inorder(mirror(t)) == rev(inorder(t))
{
  match t
    case Empty => {}
    case Node(l, x, r) => {
      calc == {
        inorder(mirror(Node(l, x, r)));
        inorder(Node(mirror(r), x, mirror(l)));
        inorder(mirror(r)) + [x] + inorder(mirror(l));
        { mirrorInorder(r); mirrorInorder(l); }
        rev(inorder(r)) + [x] + rev(inorder(l));
        { revConcat([x], inorder(r)); }
        rev([x] + inorder(r)) + rev(inorder(l));
        { revConcat(inorder(l), [x] + inorder(r)); }
        rev(inorder(l) + ([x] + inorder(r)));
        {
          assert inorder(l) + ([x] + inorder(r))
            == inorder(l) + [x] + inorder(r);
        }
        rev(inorder(l) + [x] + inorder(r));
        rev(inorder(Node(l, x, r)));
      }
    }
}
