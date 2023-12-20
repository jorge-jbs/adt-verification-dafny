// -----------------------------------------------------

lemma cosa(x: nat)
    ensures x > 0

method m(x: nat)
    ensures (cosa(x); true)

method test(x: nat) {
    m(x);
    // assert x > 0;
}

// -----------------------------------------------------

trait Madre {
    predicate p(x: nat)

    method m(x: nat)
        ensures p(x)
}


class Hija extends Madre {
    predicate p(x: nat)

    predicate q(x: nat)

    lemma DimeQueQImplicaP(x: nat)
        requires q(x)
        ensures p(x)

    method m(x: nat)
        ensures q(x)
        ensures (assert p(x) by {DimeQueQImplicaP(x);} p(x))
        // ensures p(x)
        // ensures (DimeQueQImplicaP(x); p(x))
    {
        assume q(x);
//        DimeQueQImplicaP(x);
    }
}


method UsoHija(h: Hija, x: nat)
{
    h.m(x);
    assert h.q(x);
     h.DimeQueQImplicaP(x);//necessary
    assert h.p(x);
}
