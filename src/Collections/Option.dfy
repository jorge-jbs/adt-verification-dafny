
  module Option {
    datatype option<A> = Some(unwrap: A) | Nothing {
      ghost predicate IsFailure() {
        Nothing?
      }

      ghost function PropagateFailure<A>(): option<A>
        requires IsFailure()
      {
        Nothing
      }

      ghost function Extract(): A
        requires Some?
      {
        this.unwrap
      }
    }

    ghost function FromSome<A>(ox: option<A>): A
      requires ox.Some?
    {
      match ox {
        case Some(x) => x
      }
    }

    ghost function Bind<A, B>(m: option<A>, k: A --> option<B>): option<B>
      requires m.Nothing? || k.requires(m.unwrap)
    {
      match m {
        case Some(x) => k(x)
        case Nothing() => Nothing
      }
    }

    ghost function Guard(b: bool): option<()>
    {
      if b then
        Some(())
      else
        Nothing
    }
  }

