include "std.dfy"
include "util.dfy"
include "lang.dfy"

import opened def.std
import opened util
import opened lang

function eval(env : Env, e : Term) : Option<Val> {
  match e {
    case Var(x) => if x in env then Some(env[x]) else None
    case Add(e,e') => match (eval(env,e),eval(env,e')) {
                        case (Some(IntVal(v1)),Some(IntVal(v2))) => Some(IntVal(v1 + v2)) 
                        case _ => None
                      }
    case Sub(e,e') => match (eval(env,e),eval(env,e')) {
                        case (Some(IntVal(v1)),Some(IntVal(v2))) => Some(IntVal(v1 - v2)) 
                        case _ => None
                      }
    case Or(e,e') => match (eval(env,e),eval(env,e')) {
                        case (Some(BoolVal(b1)),Some(BoolVal(b2))) => Some(BoolVal(b1 || b2)) 
                        case _ => None
                      }
    case And(e,e') => match (eval(env,e),eval(env,e')) {
                        case (Some(BoolVal(b1)),Some(BoolVal(b2))) => Some(BoolVal(b1 && b2)) 
                        case _ => None
                      }
    case Record(em) => match evalRecord(env,em) {
      case Some(m) => Some(RecordVal(m))
      case _ => None
    }
    case RecordProj(e,f) => match eval(env,e) {
      case Some(RecordVal(m)) => if f in m then Some(m[f]) else None
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
    case Var(x) => if x in ctx then Some(ctx[x]) else None
    case Add(e,e') => match (infer(ctx,e),infer(ctx,e')) {
      case (Some(IntTy),Some(IntTy)) => Some(IntTy)
      case _ => None
    }
    case Sub(e,e') => match (infer(ctx,e),infer(ctx,e')) {
      case (Some(IntTy),Some(IntTy)) => Some(IntTy)
      case _ => None
    }
    case Or(e,e') => match (infer(ctx,e),infer(ctx,e')) {
      case (Some(BoolTy),Some(BoolTy)) => Some(BoolTy)
      case _ => None
    }
    case And(e,e') => match (infer(ctx,e),infer(ctx,e')) {
      case (Some(BoolTy),Some(BoolTy)) => Some(BoolTy)
      case _ => None
    }
    case Record(es) => match inferRecord(ctx,es) {
      case Some(tm) => Some(RecordTy(tm))
      case _ => None
    }
    case RecordProj(e,f) => match infer(ctx,e) {
      case Some(RecordTy(tm)) => if f in tm then Some(tm[f]) else None
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
    case Sub(e,e') => sound(env,ctx,e); sound(env,ctx,e');
    case Or(e,e') => sound(env,ctx,e); sound(env,ctx,e');
    case And(e,e') => sound(env,ctx,e); sound(env,ctx,e');
    case Record(es) =>
      var mt :| inferRecord(ctx,es) == Some(mt);
      invertRecordTck(ctx,es);
      forall i | 0 <= i < |es|
        ensures eval(env,es[i].1).Some? && valHasType(eval(env,es[i].1).value,infer(ctx,es[i].1).value)
      {
        sound(env,ctx,es[i].1);
      }
      recordEvalLemma(env,es);
    case RecordProj(e,f) => sound(env,ctx,e);
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