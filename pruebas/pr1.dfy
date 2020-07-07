predicate IsFibonacci(n : nat, m : nat)
{
    (n == 0 ==> m == 1)
    &&
    (n == 1 ==> m == 1)
    &&
    (n >= 2 ==>
      exists a : nat ::
      exists b : nat ::
          IsFibonacci(n-1, a) && IsFibonacci(n-2, b) && m == a + b)
}

method Fibonacci(n : nat) returns (m : nat)
    ensures IsFibonacci(n, m)
{
    m := 1;
    var p := 1;
    var i := 0;
    assert IsFibonacci(0, m);
    assert IsFibonacci(1, p);
    while i < n
        invariant IsFibonacci(i, m) && IsFibonacci(i+1, p)
        invariant i <= n
    {
        /*
        assert IsFibonacci(i, m) && IsFibonacci(i+1, p);
        var M := m;
        var P := p;
        assert IsFibonacci(i, M) && IsFibonacci(i+1, P);
        m := P;
        assert IsFibonacci(i+1, m);
        p := M + P;
        assert IsFibonacci(i+2, p);
        */
        m, p := p, m+p;
        i := i + 1;
    }
}

method Main() {
    var m := Fibonacci(10);
    print m;
}
