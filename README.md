# Formally verified ADTs

Library of formally verified abstract data types in Dafny.

## Overview

This work aims to specify, implement and verify common types
of collections, like those found in C++ or Java standard
libraries. These collections are specified as *abstract data
types*, they all extend the [`ADT`](/src/ADT.dfy) trait. Each of
them can have different subtypes for different expected behavior
(e.g., [`ArrayList`](/src/ArrayList/ArrayListSpec.dfy) and
[`LinkedList`](/src/LinkedList/LinkedListSpec.dfy) both extend
[`List`](/src/List/ListSpec.dfy)). Notably, we have made sure to
completely specify the behavior of iterators, which differs between
different ADTs.

All the implementations of the library are formally proven to respect the
specification, thanks to Dafny. Compilation to other languages is planned.

The specifications are designed so that client code that uses them can:

- Have basic security guarantees: the collection is valid and is
  not shared.
- Give formal specifications of the functional behavior of the code:
  like proving that a method that reverses the order of the elements
  of a list actually reverses them.
- Reason about the state of iterators to maintain their invariants and,
  thus, prove that the code is correct.

In essence, **this library allows you to perform the same operations
as in the C++ library, but no unexpected behavior can occur** since you
can formally verify that your code uses the implementation as specified.
On the other side of the spectrum, you can use the ADTs of this library
without doing any verification, and **it is guaranteed that the collection
types of this library will not be a source of bugs**.

## Usage

Currently, this library is under development and is not documented. If
you want to use the library we advice you to wait until it is better
documented or to check the related research of the next section.

<!--
Each [`ADT`](/src/ADT.dfy) provides three definitions:

- `Model`: specifies the underlying mathematical model of the ADT. It
  is an immutable value which should be easy to reason about, like
  Dafny's builtin immutable types.
- `Repr`: all the objects that the ADT has complete ownership of. For each
  method, if `Repr` grows, it must do so by only freshly allocated
  objects.  This ensures that ADTs don't share any memory.
- `Valid`: the invariant that will hold since the object is created until
  it is destroyed.
-->

## Publications

[J. Blázquez, M. Montenegro, C. Segura: Verification of mutable linear
data structures and iterator-based algorithms in Dafny. Journal
of Logical and Algebraic Methods in Programming 134, 100875
(2023).](https://doi.org/10.1016/j.jlamp.2023.100875)

[J. Blázquez, Verification of linked data structures in Dafny, BS
thesis, Facultad de Informática, Universidad Complutense de Madrid
(2021).](https://hdl.handle.net/20.500.14352/73992)

[J. Blázquez, Verification of tree-like data structures with iterators in
Dafny, Master's thesis, Facultad de Informática, Universidad Complutense
de Madrid (2022).](https://hdl.handle.net/20.500.14352/73992)
