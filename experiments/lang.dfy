module lang {
  datatype Term  =
    | Lit(v : Val)
    | Var(x : string)
    | Add(e : Term, e': Term)
    | Sub(e : Term, e': Term)
    | Div(e : Term, e' : Term)
    | Or(e : Term, e' : Term)
    | And(e : Term, e' : Term)
    | Eq(e : Term, e' : Term)
    | Record(em : seq<(string,Term)>)
    | RecordProj(e : Term, f : string)
    | If(eb : Term, e : Term, e' : Term)

  datatype Val = IntVal(v : int) | BoolVal(b : bool) | RecordVal(m : map<string,Val>)

  type Env = map<string,Val>

  datatype Ty = IntTy | BoolTy | RecordTy(rm : map<string,Ty>)

  type Ctx = map<string,Ty>


  function subty(t : Ty, t' : Ty) : bool {
    match (t,t') {
      case (IntTy,IntTy) => true
      case (BoolTy,BoolTy) => true
      case (RecordTy(m),RecordTy(m')) => forall k :: k in m' ==> k in m && subty(m[k],m'[k])
      case _ => false
    }
  }

  lemma subtyRefl(t : Ty)
    ensures subty(t,t)
  {
    match t {
      case BoolTy =>
      case IntTy =>
      case RecordTy(m) =>
    }
  }
  lemma subtyTrans(t1 : Ty, t2 : Ty, t3 : Ty)
    requires subty(t1,t2)
    requires subty(t2,t3)
    ensures subty(t1,t3)
  {
    match (t1,t2,t3) {
      case (BoolTy,BoolTy,BoolTy) => 
      case (IntTy,IntTy,IntTy) => 
      case (RecordTy(mt1),RecordTy(m2),RecordTy(mt3)) => 
    }
  }

}

