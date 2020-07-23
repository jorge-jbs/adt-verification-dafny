datatype List<T> = Nil | Cons(head:T, tail:List<T>)


function method length<T> (l:List<T>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}
predicate sorted(l:List<int>)
{
    match l
       case Nil         => true
       case Cons(x, xs) =>
            match xs
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}
function elems<T> (l : List<T>) : multiset<T>
{
    match l
       case Nil         => multiset{}
       case Cons(x, xs) => multiset{x} + elems(xs)
}

function sum(l:List<int>): (res:int)
{
    match l
        case Nil         => 0
        case Cons(y, ys) => y + sum(ys)
}
function insert(x: int, l:List<int>): (res:List<int>)
    requires sorted(l)
    ensures sorted(res)
    ensures elems(res) == elems(l) + multiset{x}
{
    match l
        case Nil         => Cons(x, Nil)
        case Cons(y, ys) => if x <= y
                            then Cons(x, l)
                            else Cons(y, insert(x, ys))
}

function delete<T> (x: T, l:List<T>): (res:List<T>)
ensures elems(res) == elems(l) - multiset{x}
{
    match l
        case Nil         => Nil
        case Cons(y, ys) => if x == y
                            then ys
                            else Cons(y, delete(x, ys))
}

function search<T> (x: T, l:List<T>): (res:bool)
ensures res == (x in elems(l))
{
    match l
        case Nil => false
        case Cons(y, ys) => if x == y
                            then true
                            else search(x, ys)
}

function min(x:nat, y:nat): (res:nat)
{
    if x <= y then x else y
}

function take<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == min (n, length(l))
{
    match l
        case Nil         => Nil
        case Cons(y, ys) => if n == 0 then Nil
                            else Cons(y, take(n-1, ys))
}

function drop<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == if length(l) < n then 0 else length(l) - n
{
    match l
        case Nil         => Nil
        case Cons(y, ys) => if n == 0
                            then l
                            else drop(n-1, ys)
}
/*
   Exercises
*/

function split<T> (n : nat, l : List<T>) : (res : (List<T>, List<T>))
  ensures length(res.0) == min (n, length(l))
  ensures length(res.1) == if length(l) < n then 0 else length(l) - n
  ensures elems(l) == elems(res.0) + elems(res.1)
{
  if n == 0 then
    (Nil, l)
  else match l
    case Nil => (Nil, l)
    case Cons(x, xs) =>
      var rec := split(n-1, xs);
      (Cons(x, rec.0), rec.1)
}

function reverseAux(l : List<int>, aux : List<int>) : (res : List<int>)
  ensures elems(res) == elems(l) + elems(aux)
{
  match l
    case Nil => aux
    case Cons(x, xs) => reverseAux(xs, Cons(x, aux))
}

// write the code of this function and verify it
function reverse(l : List<int>) : (res : List<int>)
  ensures elems(res) == elems(l)
{
  reverseAux(l, Nil)
}

// specify, write the code of this function, and verify it

function concat(l1:List<int>,l2:List<int>): (res:List<int>)
  ensures elems(res) == elems(l1) + elems(l2)
// specify, write the code of this function, and verify it
{
  match l1
    case Nil => l2
    case Cons(x, xs) => Cons(x, concat(xs, l2))
}

lemma concatAssoc(l1 : List<int>, l2 : List<int>, l3 : List<int>)
  ensures concat(l1,concat(l2,l3)) == concat(concat(l1,l2),l3)
// prove it
{
  match l1
    case Nil => {}
    case Cons(x, xs) => {
      match l2
        case Nil => {}
        case Cons(y, ys) => {}
    }
}

lemma reverseAuxIdemp(x : int, xs : List<int>, ys : List<int>, zs : List<int>)
  decreases xs
  ensures reverseAux(reverseAux(Cons(x, xs), Nil), Nil) == Cons(x, reverseAux(reverseAux(xs, Nil), Nil))
  //ensures reverseAux(reverseAux(Cons(x, xs), Nil), zs) == Cons(x, reverseAux(reverseAux(xs, ys), zs))
{
  match xs
    case Nil => {
      calc == {
        reverseAux(reverseAux(Cons(x, Nil), Nil), Nil);
        reverseAux(reverseAux(Nil, Cons(x, Nil)), Nil);
        reverseAux(Cons(x, Nil), Nil);
        reverseAux(Nil, Cons(x, Nil));
        Cons(x, Nil);
        Cons(x, reverseAux(reverseAux(Nil, Nil), Nil));
      }
    }
    case Cons(y, xss) => {
      calc == {
        reverseAux(reverseAux(Cons(x, xs), Nil), Nil);
        reverseAux(reverseAux(Cons(x, Cons(y, xss)), Nil), Nil);
        Cons(x, reverseAux(reverseAux(Cons(y, xss), Nil), Nil));
        Cons(x, reverseAux(reverseAux(xs, Nil), Nil));
      }
    }
}
/*
lemma reverseAuxIdemp(x : int, xs : List<int>, ys : List<int>, zs : List<int>)
  decreases xs
  //ensures reverseAux(reverseAux(xs, Cons(x, ys)), zs) == Cons(x, reverseAux(reverseAux(xs, ys), zs))
  //ensures reverseAux(reverseAux(Cons(x, xs), ys), zs) == Cons(x, reverseAux(reverseAux(xs, ys), zs))
  ensures reverseAux(reverseAux(Cons(x, xs), ys), zs) == reverseAux(reverseAux(xs, ys), Cons(x, zs))
{
  match xs
    case Nil => {}
    case Cons(y, xss) => {
      calc == {
        reverseAux(reverseAux(Cons(x, xs), ys), zs);
        reverseAux(reverseAux(Cons(x, Cons(y, xss)), ys), zs);
        Cons(x, reverseAux(reverseAux(xs, ys), zs));
      }
      /*
      calc == {
        reverseAux(reverseAux(xs, Cons(x, ys)), zs);
        reverseAux(reverseAux(Cons(y, xss), Cons(x, ys)), zs);
        reverseAux(reverseAux(xss, Cons(y, Cons(x, ys))), zs);
        { reverseAuxIdemp(y, xss, Cons(x, ys), zs); }
        Cons(y, reverseAux(reverseAux(xss, Cons(x, ys)), zs));
        { reverseAuxIdemp(x, xss, ys, zs); }
        Cons(x, Cons(y, reverseAux(reverseAux(xss, ys), zs)));
        reverseAux(reverseAux(xss, Cons(x, ys)), Cons(y, zs));
        Cons(x, reverseAux(reverseAux(Cons(y, xss), Nil), zs));
      }
      */
    }
}
*/

lemma reverseIdemp(l:List<int>)
  ensures reverse(reverse(l)) == l
  // prove it
{
  match l
    case Nil => {}
    case Cons(x, xs) => {
      calc == {
        reverse(reverse(xs));
        reverseAux(reverseAux(xs, Nil), Nil);
        { reverseIdemp(xs); }
        xs;
      }
      calc == {
        reverse(reverse(Cons(x, xs)));
        reverse(reverseAux(xs, Cons(x, Nil)));
        reverseAux(reverseAux(xs, Cons(x, Nil)), Nil);
        Cons(x, reverseAux(reverseAux(xs, Nil), Nil));
        Cons(x, reverse(reverse(xs)));
        { reverseIdemp(xs); }
        Cons(x, xs);
      }
    }
}
