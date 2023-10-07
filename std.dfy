
module def.std {

  datatype Option<+T> = Some(value: T) | None {
    predicate IsFailure() {
      None?
    }

    function PropagateFailure<U>(): Option<U>
      requires None?
    {
      None
    }

    function Extract(): T
      requires Some? {
      value
    }

    function UnwrapOr(default: T): T {
      match this
      case Some(v) => v
      case None() => default
    }
  }

  datatype Result<+T, +E> = Ok(value: T) | Err(error: E) {
    predicate IsFailure() {
      Err?
    }

    function PropagateFailure<U>(): Result<U, E>
      requires Err?
    {
      Err(error)
    }

    function Extract(): T
      requires Ok?
    {
      value
    }

    function Map<U>(f: T -> U): Result<U, E>
    {
      if Ok? then Ok(f(value)) else PropagateFailure()
    }

    function MapErr<F>(f: E -> F): Result<T, F>
    {
      if Ok? then Ok(value) else Err(f(error))
    }
  }

  function optguard(b : bool) : Option<()> {
    if b then Some(()) else None
  }

  function lookup<T,U>(m : map<T,U>, t : T) : Option<U>
  {
    if t in m then Some(m[t]) else None
  }


  opaque function mapM<T,U,V>(f : U -> Option<V>, m : map<T,U>) : (res : Option<map<T,V>>)
    ensures res.Some? ==> forall k :: k in res.value ==> k in m && f(m[k]).Some? && f(m[k]).value == res.value[k]
    ensures (forall k :: k in m ==> f(m[k]).Some?) ==> res.Some? && m.Keys <= res.value.Keys
  {
    if (forall k :: k in m ==> f(m[k]).Some?) then Some(map k | k in m :: f(m[k]).value)
    else None
  }
}