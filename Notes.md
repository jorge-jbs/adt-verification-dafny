# Goals

The project would be a success if:

- We verify the implementation of simple linked linear data structures.
- Those structures are useful, i.e. they can be used to write real programs
  (toy examples would suffice).
- We document the methodologies that we have followed and discuss the advantages
  and disadvantages of each.

But we also talked about other extra goals that would be nice if achieved, but
weren't the main goal of the project:

- Verifying iterators
- Verifying other linked data structures that aren't linear.

# History

First, I studied Dafny with some exercises. These exercises didn't necessarily
involve linear linked structures. Shortly after that I began with the
verification of an implementation of singly linked lists, the simplest I could
think of. It was greatly inspired by Rustan Leino's [\[1\]]. But soon we wanted
to explore different possibilities in the design space:

- Should we have a (ghost) field `repr` in **each** `Node`? The alternative is
  having only **one** representation in the `List` class, the class that has all
  the `Node`s.
- Can we remove the ghost field `model` and replace it with a function? This
  would be welcome, since updating the `model` field each time we update the
  list is cumbersome.
- Can we get rid of `repr` too?
- Should `repr` be a set? The alternative is a sequence. In that case it should
  be called `spine`.
- Extra question: if we were implementing trees instead of lists, should the
  representation be a tree too?

We will be answering these questions progressively. Let's start with the field
`model`. We **can** convert that to a function and, in fact, it is fairly
straightforward. We modified our implementation with that change and don't
consider the other possibility since it is better in all respects.

But what about `repr`? Sadly, `repr` cannot be transformed into a function. We
can define `Model()` as a function because we assume that the current list is
`Valid()`. This is needed because we need to know that the list doesn't have
cycles. However, `Valid()` uses the representation. If we were to implement the
representation as a function, `Valid()` and `Repr()` would be mutually
recursive! That is not possible in Dafny.

Other option would be to make `Valid()` not depend on `Repr()`. In order to do
so, we would need to say something like "there exists a set `repr` such
that...". But, Dafny gives us an error if we try that: "a quantifier involved in
a predicate definition is not allowed to depend on the set of allocated
references; Dafny's heuristics can't figure out a bound for the values of
'repr'".

Regarding the first question, I shall talk before about an issue when trying to
implement singly linked lists the same way Leino does it. One of the important
methods of linked lists is the `Insert` method. This method places a new node
after an existing one, that we will call `mid`. When we try to implement it, we
notice that we have to update all the representations before `mid` in order for
them to contain the new node. This is easy to say, but it takes a non-trivial
amount of time to implement (and verify), and the code ends up being quite long
because of all the auxiliary lemmas. I have implemented it and there is a
complete version of `Insert` in the source code. Nonetheless, a better
alternative must exist. That alternative is having the representation stored in
the `List` class, instead of in each `Node`.

When we have the representation externally, everything becomes easier. We can
leverage the power of Dafny proving lemmas about sequences. Suddenly, the
`Insert` method only takes 6 lines of _ghost_ code, some of which are calls to
auxiliary lemmas that are called in almost every method.

This version of "external" representation with the representation replaced by a
`spine` has been our baseline version. All other list implementations are based
on this one. We have only preservered the previous one to compare it against the
new one.

[\[1\]]:
  https://drive.google.com/file/d/1zU4sUuMVSS0LHSKRQlg5jr-Mm_XsTO5E/view?usp=sharing
