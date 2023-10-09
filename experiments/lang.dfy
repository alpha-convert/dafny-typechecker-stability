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

}

