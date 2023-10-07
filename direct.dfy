include "std.dfy"
include "util.dfy"
include "lang.dfy"

import opened def.std
import opened util
import opened lang

function eval(env : Env, e : Term) : Option<Val> {
  match e {
    case Lit(v) => Some(v)
    case Var(x) => if x in env then Some(env[x]) else None
    case Add(e1,e2) => match (eval(env,e1),eval(env,e2)) {
                        case (Some(IntVal(v1)),Some(IntVal(v2))) => Some(IntVal(v1 + v2)) 
                        case _ => None
                      }
    case Sub(e1,e2) => match (eval(env,e1),eval(env,e2)) {
                        case (Some(IntVal(v1)),Some(IntVal(v2))) => Some(IntVal(v1 - v2)) 
                        case _ => None
                      }
    case Or(e1,e2) => match (eval(env,e1),eval(env,e2)) {
                        case (Some(BoolVal(b1)),Some(BoolVal(b2))) => Some(BoolVal(b1 || b2)) 
                        case _ => None
                      }
    case And(e1,e2) => match (eval(env,e1),eval(env,e2)) {
                        case (Some(BoolVal(b1)),Some(BoolVal(b2))) => Some(BoolVal(b1 && b2)) 
                        case _ => None
                      }
    case Eq(e1,e2) => match (eval(env,e1),eval(env,e2)) {
                        case (Some(v1),Some(v2)) => Some(BoolVal(v1 == v2)) 
                        case _ => None
                      }
    case Record(em) => match evalRecord(env,em) {
      case Some(m) => Some(RecordVal(m))
      case _ => None
    }
    case RecordProj(e',f) => match eval(env,e') {
      case Some(RecordVal(m)) => if f in m then Some(m[f]) else None
      case _ => None
    }
    case If(eb,e1,e2) => match eval(env,eb) {
      case Some(BoolVal(b)) => if b then eval(env,e1) else eval(env,e2)
      case _ => None
    }
  }
}

function evalRecord(env : Env, es : seq<(string,Term)>) : Option<map<string,Val>> {
  if es == [] then Some(map[])
  else
    var k := es[0].0;
    match (eval(env,es[0].1), evalRecord(env,es[1..])) {
      case (Some(v), Some(vm)) => if k in vm.Keys then Some(vm) else Some(vm[k := v])
      case _ => None
    }
}

function infer(ctx : Ctx, e : Term) : Option<Ty> {
  match e {
    case Lit(v) => Some(inferVal(v))
    case Var(x) => if x in ctx then Some(ctx[x]) else None
    case Add(e1,e2) => match (infer(ctx,e1),infer(ctx,e2)) {
      case (Some(IntTy),Some(IntTy)) => Some(IntTy)
      case _ => None
    }
    case Sub(e1,e2) => match (infer(ctx,e1),infer(ctx,e2)) {
      case (Some(IntTy),Some(IntTy)) => Some(IntTy)
      case _ => None
    }
    case Or(e1,e2) => match (infer(ctx,e1),infer(ctx,e2)) {
      case (Some(BoolTy),Some(BoolTy)) => Some(BoolTy)
      case _ => None
    }
    case And(e1,e2) => match (infer(ctx,e1),infer(ctx,e2)) {
      case (Some(BoolTy),Some(BoolTy)) => Some(BoolTy)
      case _ => None
    }
    case Eq(e1,e2) => match (infer(ctx,e1),infer(ctx,e2)) {
      case (Some(_),Some(_)) => Some(BoolTy)
      case _ => None
    }
    case Record(es) => match inferRecord(ctx,es) {
      case Some(tm) => Some(RecordTy(tm))
      case _ => None
    }
    case RecordProj(e',f) => match infer(ctx,e') {
      case Some(RecordTy(tm)) => if f in tm then Some(tm[f]) else None
      case _ => None
    }
    case If(eb,e1,e2) => match (infer(ctx,eb),infer(ctx,e1),infer(ctx,e2)) {
      case (Some(BoolTy),Some(t1),Some(t2)) => if t1 == t2 then Some(t1) else None
      case _ => None
    }
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

function inferVal(v : Val) : Ty
  decreases v , 1
{
  match v {
    case IntVal(_) => IntTy
    case BoolVal(_) => BoolTy
    case RecordVal(m) => RecordTy(map k | k in m :: inferVal(m[k]))
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

lemma inferValSound(v : Val)
  ensures valHasType(v,inferVal(v))
{}

predicate envHasCtx(env : Env, ctx : Ctx){
    forall k :: k in ctx ==> k in env && valHasType(env[k],ctx[k])
}



lemma soundDirect(env : Env, ctx : Ctx, e : Term)
  requires envHasCtx(env,ctx)
  requires infer(ctx,e).Some?
  ensures eval(env,e).Some? && valHasType(eval(env,e).value,infer(ctx,e).value)
{
  match e {
    case Var(_) =>
    case Lit(v) => inferValSound(v);
    case Add(e1,e2) => soundDirect(env,ctx,e1); soundDirect(env,ctx,e2);
    case Sub(e1,e2) => soundDirect(env,ctx,e1); soundDirect(env,ctx,e2);
    case Or(e1,e2) => soundDirect(env,ctx,e1); soundDirect(env,ctx,e2);
    case And(e1,e2) => soundDirect(env,ctx,e1); soundDirect(env,ctx,e2);
    case Eq(e1,e2) => soundDirect(env,ctx,e1); soundDirect(env,ctx,e2);
    case Record(es) =>
      var mt :| inferRecord(ctx,es) == Some(mt);
      invertRecordTck(ctx,es);
      forall i | 0 <= i < |es|
        ensures eval(env,es[i].1).Some? && valHasType(eval(env,es[i].1).value,infer(ctx,es[i].1).value)
      {
        soundDirect(env,ctx,es[i].1);
      }
      recordEvalLemma(env,es);
    case RecordProj(e',f) => soundDirect(env,ctx,e');
    case If(eb,e1,e2) => soundDirect(env,ctx,eb); soundDirect(env,ctx,e1); soundDirect(env,ctx,e2);
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
{}