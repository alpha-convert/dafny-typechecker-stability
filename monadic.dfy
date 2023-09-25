include "std.dfy"
include "util.dfy"

import opened def.std
import opened util

// datatype Option<A> = Some(value: A) | None

datatype Term  =
  | Var(x : string)
  | Add(e : Term, e': Term)
  | Or(e : Term, e' : Term)
  | EqZ(e : Term)
  | Record(em : seq<(string,Term)>)

datatype Val = IntVal(v : int) | BoolVal(b : bool) | RecordVal(m : map<string,Val>)

type Env = map<string,Val>

function eval(env : Env, e : Term) : Option<Val> {
  match e {
    case Var(x) => if x in env then Some(env[x]) else None
    case Add(e,e') => 
        var v1 :- eval(env,e);
        var v2 :- eval(env,e');
        valAdd(v1,v2)
    case Or(e,e') =>
        var v1 :- eval(env,e);
        var v2 :- eval(env,e');
        valOr(v1,v2)
    case EqZ(e) => 
        var v :- eval(env,e);
        valEqZ(v)
    case Record(em) => match evalRecord(env,em) {
      case Some(m) => Some(RecordVal(m))
      case _ => None
    }
  }
}

function valAdd(v1 : Val, v2 : Val) : Option<Val> {
    match (v1,v2) {
        case (IntVal(n), IntVal(m)) => Some (IntVal (n + m))
        case _ => None
    }
}

function valOr(v1 : Val, v2 : Val) : Option<Val> {
    match (v1,v2) {
        case (BoolVal(n), BoolVal(m)) => Some (BoolVal (n || m))
        case _ => None
    }
}

function valEqZ(v : Val) : Option<Val> {
    match v {
        case IntVal(n) => if n == 0 then Some(BoolVal(true)) else Some(BoolVal(false))
        case _ => None
    }
}

function evalRecord(env : Env, es : seq<(string,Term)>) : Option<map<string,Val>> {
  if es == [] then Some(map[])
  else
    var k := es[0].0;
    var v :- eval(env,es[0].1);
    var vm :- evalRecord(env,es[1..]);
    if k in vm.Keys then Some(vm) else Some(vm[k := v])
}

datatype Ty = IntTy | BoolTy | RecordTy(rm : map<string,Ty>)

type Ctx = map<string,Ty>

function infer(ctx : Ctx, e : Term) : Option<Ty> {
  match e {
    case Var(x) => if x in ctx then Some(ctx[x]) else None
    case Add(e,e') => 
        var t1 :- infer(ctx,e);
        var t2 :- infer(ctx,e');
        var _ :- guard(t1 == IntTy);
        var _ :- guard(t2 == IntTy);
        Some(IntTy)

    case Or(e,e') =>
        var t1 :- infer(ctx,e);
        var t2 :- infer(ctx,e');
        var _ :- guard(t1 == BoolTy);
        var _ :- guard(t2 == BoolTy);
        Some(BoolTy)

    case EqZ(e) => 
        var t :- infer(ctx,e);
        var _ :- guard(t == BoolTy);
        Some(BoolTy)

    case Record(es) =>
        var tm :- inferRecord(ctx,es);
        Some(RecordTy(tm))
  }
}

function inferRecord(ctx : Ctx, es : seq<(string,Term)>) : Option<map<string,Ty>> {
  if es == [] then Some(map[])
  else
    var k := es[0].0;
    match (infer(ctx,es[0].1), inferRecord(ctx,es[1..])) {
      case (Some(t),Some(tm)) => if k in tm then Some(tm) else Some(tm[k := t])
      case _ => None
    }
}

function valHasType(v : Val, t : Ty) : bool {
  match (v,t) {
    case (IntVal(_),IntTy) => true
    case (BoolVal(_), BoolTy) => true
    case (RecordVal(mv),RecordTy(mt)) => forall k :: k in mt.Keys ==> k in mv && valHasType(mv[k],mt[k])
    case _ => false
  }
}

lemma sound (env : Env, ctx : Ctx, e : Term)
  requires forall k :: k in ctx ==> k in env && valHasType(env[k],ctx[k])
  requires infer(ctx,e).Some?
  ensures eval(env,e).Some? && valHasType(eval(env,e).value,infer(ctx,e).value)
{
  match e {
    case Var(_) =>
    case Add(e,e') => sound(env,ctx,e); sound(env,ctx,e');
    case Or(e,e') => sound(env,ctx,e); sound(env,ctx,e');
    case EqZ(e) => sound(env,ctx,e);
    case Record(es) =>
      var mt :| inferRecord(ctx,es) == Some(mt);
      invertRecordTck(ctx,es);
      forall i | 0 <= i < |es|
        ensures eval(env,es[i].1).Some? && valHasType(eval(env,es[i].1).value,infer(ctx,es[i].1).value)
      {
        sound(env,ctx,es[i].1);
      }
      recordEvalLemma(env,es);
  }
}

lemma invertRecordTck(ctx : Ctx, es : seq<(string,Term)>)
  requires inferRecord(ctx,es).Some?
  ensures forall i | 0 <= i < |es| :: infer(ctx,es[i].1).Some?
  // Every result term in es typechecks, and every key appears in the result.
  ensures forall i | 0 <= i < |es| :: es[i].0 in inferRecord(ctx,es).value.Keys
  //For every key in the output, it existed in the input, and its type is the result of inferring the type of the last instance of k.
  ensures forall k | k in inferRecord(ctx,es).value.Keys :: KeyExists(k,es) && infer(ctx,LastOfKey(k,es)).value == inferRecord(ctx,es).value[k]
{}

lemma recordEvalLemma(env : Env, es : seq<(string,Term)>)
  requires forall i | 0 <= i < |es| :: eval(env,es[i].1).Some?
  ensures evalRecord(env,es).Some?
  ensures forall i | 0 <= i < |es| :: es[i].0 in evalRecord(env,es).value.Keys
  ensures forall k | k in evalRecord(env,es).value.Keys :: KeyExists(k,es) && eval(env,LastOfKey(k,es)).value == evalRecord(env,es).value[k]
{
}