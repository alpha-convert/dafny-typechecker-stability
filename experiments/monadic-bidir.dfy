include "std.dfy"
include "util.dfy"
include "lang.dfy"
include "evaluator.dfy"

import opened def.std
import opened util
import opened lang
import opened evaluator

datatype TckErr = TckErr

function infer(ctx : Ctx, e : Term) : Result<Ty,TckErr>
    decreases e, 0
{
  match e {
    case Var(x) => if x in ctx then Ok(ctx[x]) else Err(TckErr)
    case Lit(v) => Ok(inferVal(v))
    case Add(e1,e2) => 
        var _ :- check(ctx,e1,IntTy);
        var _ :- check(ctx,e2,IntTy);
        Ok(IntTy)
    case Sub(e1,e2) => 
        var _ :- check(ctx,e1,IntTy);
        var _ :- check(ctx,e2,IntTy);
        Ok(IntTy)
    case Div(e1,e2) => 
        var _ :- check(ctx,e1,IntTy);
        var _ :- check(ctx,e2,IntTy);
        Ok(IntTy)
    case Or(e1,e2) =>
        var _ :- check(ctx,e1,BoolTy);
        var _ :- check(ctx,e2,BoolTy);
        Ok(BoolTy)
    case And(e1,e2) =>
        var _ :- check(ctx,e1,BoolTy);
        var _ :- check(ctx,e2,BoolTy);
        Ok(BoolTy)
    case Eq(e1,e2) =>
        var _ :- infer(ctx,e1);
        var _ :- infer(ctx,e2);
        Ok(BoolTy)
    case Record(es) =>
        var tm :- inferRecordExpr(ctx,es);
        Ok(RecordTy(tm))
    case RecordProj(e',f) =>
        var m :- inferRecordTy(ctx,e');
        lookup(m,f,TckErr)
    case If(eb,e1,e2) =>
      var _ :- check(ctx,eb,BoolTy);
      var t :- infer(ctx,e1);
      var _ :- check(ctx,e2,t);
      Ok(t)
  }
}

function inferIntTy(ctx : Ctx, e : Term) : Result<(),TckErr>
    decreases e, 1
{
    var t :- infer(ctx,e);
    match t {
        case IntTy => Ok(())
        case _ => Err(TckErr)
    }
}

function inferBoolTy(ctx : Ctx, e : Term) : Result<(),TckErr>
    decreases e, 1
{
    var t :- infer(ctx,e);
    match t {
        case BoolTy => Ok(())
        case _ => Err(TckErr)
    }
}

function inferRecordTy(ctx : Ctx, e : Term) : Result<map<string,Ty>,TckErr>
    decreases e, 1
{
    var t :- infer(ctx,e);
    match t {
        case RecordTy(m) => Ok(m)
        case _ => Err(TckErr)
    }
}

function inferRecordExpr(ctx : Ctx, es : seq<(string,Term)>) : Result<map<string,Ty>,TckErr>
    decreases es
{
  if es == [] then Ok(map[])
  else
    var k := es[0].0;
    var t :- infer(ctx,es[0].1);
    var tm :- inferRecordExpr(ctx,es[1..]);
    if k in tm then Ok(tm) else Ok(tm[k := t])
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


function check(ctx : Ctx, e : Term, t : Ty) : Result<(),TckErr>
  decreases e , 1
{
  var t' :- infer(ctx,e);
  if subty(t',t) then Ok(()) else Err(TckErr)
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



lemma valHasTypeSubtyCompat (v : Val, t : Ty, t' : Ty)
  requires valHasType(v,t)
  requires subty(t,t')
  ensures valHasType(v,t')
{}

predicate envHasCtx(env : Env, ctx : Ctx){
    forall k :: k in ctx ==> k in env && valHasType(env[k],ctx[k])
}


lemma soundBidir (env : Env, ctx : Ctx, e : Term, t : Ty)
  requires envHasCtx(env,ctx)
  requires check(ctx,e,t).Ok?
  ensures (eval(env,e).Ok? && valHasType(eval(env,e).value,t)) || (eval(env,e).Err? && eval(env,e).error == DivByZeroErr)
{
  match e {
    case Var(x) => valHasTypeSubtyCompat(env[x],ctx[x],t);
    case Lit(v) => inferValSound(v); valHasTypeSubtyCompat(v,inferVal(v),t);
    case Add(e1,e2) => soundBidir(env,ctx,e1,IntTy); soundBidir(env,ctx,e2,IntTy);
    case Sub(e1,e2) => soundBidir(env,ctx,e1,IntTy); soundBidir(env,ctx,e2,IntTy);
    case Div(e1,e2) => soundBidir(env,ctx,e1,IntTy); soundBidir(env,ctx,e2,IntTy);
    case Or(e1,e2) => soundBidir(env,ctx,e1,BoolTy); soundBidir(env,ctx,e2,BoolTy);
    case And(e1,e2) => soundBidir(env,ctx,e1,BoolTy); soundBidir(env,ctx,e2,BoolTy);
    case Eq(e1,e2) =>
    subtyRefl(infer(ctx,e1).value);
    subtyRefl(infer(ctx,e2).value);
    soundBidir(env,ctx,e1,infer(ctx,e1).value);
    soundBidir(env,ctx,e2,infer(ctx,e2).value);
    case Record(es) =>
      var mt :| inferRecordExpr(ctx,es) == Ok(mt);
      assert subty(RecordTy(mt),t);
      invertRecordTck(ctx,es);
      forall i | 0 <= i < |es|
        ensures (eval(env,es[i].1).Ok? && valHasType(eval(env,es[i].1).value,infer(ctx,es[i].1).value)) || (eval(env,es[i].1).Err? && eval(env,es[i].1).error == DivByZeroErr)
      {
        subtyRefl(infer(ctx,es[i].1).value);
        soundBidir(env,ctx,es[i].1,infer(ctx,es[i].1).value);
      }
      if(forall i | 0 <= i < |es| :: (eval(env,es[i].1).Ok? && valHasType(eval(env,es[i].1).value,infer(ctx,es[i].1).value))) {
        evalRecordExprLemmaOk(env,es);
        valHasTypeSubtyCompat(eval(env,Record(es)).value,RecordTy(mt),t);
      } else {
        evalRecordExprLemmaErr(env,es);
      }
    case RecordProj(e',f) =>
      var mt := inferRecordTy(ctx,e').value;
      subtyRefl(RecordTy(mt));
      soundBidir(env,ctx,e',RecordTy(mt));
      if(evalRecord(env,e').Ok?){
        valHasTypeSubtyCompat(evalRecord(env,e').value[f],mt[f],t);
      }
    case If(eb,e1,e2) =>
      soundBidir(env,ctx,eb,BoolTy);
      subtyRefl(infer(ctx,e1).value);
      soundBidir(env,ctx,e1,infer(ctx,e1).value);
      soundBidir(env,ctx,e2,infer(ctx,e1).value);
      if(eval(env,eb).Ok?) {
        if(evalBool(env,eb).value && eval(env,e1).Ok?) {
          valHasTypeSubtyCompat(eval(env,e1).value,infer(ctx,e1).value,t);
        } else if (!evalBool(env,eb).value && eval(env,e2).Ok?){
          valHasTypeSubtyCompat(eval(env,e2).value,infer(ctx,e1).value,t);
        }
      }
  }
}

lemma invertRecordTck(ctx : Ctx, es : seq<(string,Term)>)
  requires inferRecordExpr(ctx,es).Ok?
  ensures forall i | 0 <= i < |es| :: infer(ctx,es[i].1).Ok?
  // Every result term in es typechecks, and every key appears in the result.
  ensures forall i | 0 <= i < |es| :: es[i].0 in inferRecordExpr(ctx,es).value.Keys
  //For every key in the output, it existed in the input, and its type is the result of inferring the type of the last instance of k.
  ensures forall k | k in inferRecordExpr(ctx,es).value.Keys :: KeyExists(k,es) && infer(ctx,LastOfKey(k,es)).value == inferRecordExpr(ctx,es).value[k]
{}