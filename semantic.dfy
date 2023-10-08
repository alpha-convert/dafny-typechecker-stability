include "std.dfy"
include "util.dfy"
include "lang.dfy"
include "evaluator.dfy"

import opened def.std
import opened util
import opened lang
import opened evaluator


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

function infer(ctx : Ctx, e : Term) : Option<Ty>

    decreases e, 0
{
  match e {
    case Var(x) => if x in ctx then Some(ctx[x]) else None
    case Lit(v) => Some(inferVal(v))
    case Add(e1,e2) => 
        var _ :- check(ctx,e1,IntTy);
        var _ :- check(ctx,e2,IntTy);
        Some(IntTy)
    case Sub(e1,e2) => 
        var _ :- check(ctx,e1,IntTy);
        var _ :- check(ctx,e2,IntTy);
        Some(IntTy)
    case Or(e1,e2) =>
        var _ :- check(ctx,e1,BoolTy);
        var _ :- check(ctx,e2,BoolTy);
        Some(BoolTy)
    case And(e1,e2) =>
        var _ :- check(ctx,e1,BoolTy);
        var _ :- check(ctx,e2,BoolTy);
        Some(BoolTy)
    case Eq(e1,e2) =>
        var _ :- infer(ctx,e1);
        var _ :- infer(ctx,e2);
        Some(BoolTy)
    case Record(es) =>
        var tm :- inferRecordExpr(ctx,es);
        Some(RecordTy(tm))
    
    case RecordProj(e',f) =>
        var m :- inferRecordTy(ctx,e');
        lookup(m,f)
    case If(eb,e1,e2) =>
      var _ :- check(ctx,eb,BoolTy);
      var t :- infer(ctx,e1);
      var _ :- check(ctx,e2,t);
      Some(t)
  }
}

function inferIntTy(ctx : Ctx, e : Term) : Option<()>
    decreases e, 1
{
    var t :- infer(ctx,e);
    match t {
        case IntTy => Some(())
        case _ => None
    }
}

function inferBoolTy(ctx : Ctx, e : Term) : Option<()>
    decreases e, 1
{
    var t :- infer(ctx,e);
    match t {
        case BoolTy => Some(())
        case _ => None
    }
}

function inferRecordTy(ctx : Ctx, e : Term) : Option<map<string,Ty>>
    decreases e, 1
{
    var t :- infer(ctx,e);
    match t {
        case RecordTy(m) => Some(m)
        case _ => None
    }
}

function inferRecordExpr(ctx : Ctx, es : seq<(string,Term)>) : Option<map<string,Ty>>
    decreases es
{
  if es == [] then Some(map[])
  else
    var k := es[0].0;
    var t :- infer(ctx,es[0].1);
    var tm :- inferRecordExpr(ctx,es[1..]);
    if k in tm then Some(tm) else Some(tm[k := t])
}

lemma invertRecordTck(ctx : Ctx, es : seq<(string,Term)>)
  requires inferRecordExpr(ctx,es).Some?
  ensures forall i | 0 <= i < |es| :: infer(ctx,es[i].1).Some?
  // Every result term in es typechecks, and every key appears in the result.
  ensures forall i | 0 <= i < |es| :: es[i].0 in inferRecordExpr(ctx,es).value.Keys
  //For every key in the output, it existed in the input, and its type is the result of inferring the type of the last instance of k.
  ensures forall k | k in inferRecordExpr(ctx,es).value.Keys :: KeyExists(k,es) && infer(ctx,LastOfKey(k,es)).value == inferRecordExpr(ctx,es).value[k]
{}



function inferVal(v : Val) : Ty
  decreases v , 1
{
  match v {
    case IntVal(_) => IntTy
    case BoolVal(_) => BoolTy
    case RecordVal(m) => RecordTy(map k | k in m :: inferVal(m[k]))
  }
}


function check(ctx : Ctx, e : Term, t : Ty) : Option<()>
  decreases e , 1
{
  var t' :- infer(ctx,e);
  if subty(t',t) then Some(()) else None
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

opaque ghost predicate isSafe(env : Env, e : Term, t : Ty) {
  eval(env,e).Some? && valHasType(eval(env,e).value,t)
}

opaque ghost predicate isSafeAtSomeType(env : Env, e : Term) {
  exists t :: isSafe(env,e,t)
}

lemma hideTheType(env : Env, e : Term, t : Ty)
  requires isSafe(env,e,t)
  ensures isSafeAtSomeType(env,e)
{
  reveal isSafe();
  reveal isSafeAtSomeType();
}

lemma isSafeSubtyCompat(env : Env, e : Term, t : Ty, t' : Ty)
  requires subty(t,t')
  requires isSafe(env,e,t)
  ensures isSafe(env,e,t')
{
  reveal isSafe();
  valHasTypeSubtyCompat(eval(env,e).value,t,t');
}

lemma varIsSafe(env : Env, x : string, t : Ty)
  requires x in env
  requires valHasType(env[x],t)
  ensures isSafe(env,Var(x),t)
{
  reveal isSafe();
}

lemma litIsSafe(env : Env, v : Val)
  ensures isSafe(env,Lit(v),inferVal(v))
{
  reveal isSafe();
}

lemma addIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafe(env,e1,IntTy)
  requires isSafe(env,e2,IntTy)
  ensures isSafe(env,Add(e1,e2),IntTy)
{
  reveal isSafe();
  assert eval(env,Add(e1,e2)).Some?;
}

lemma subIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafe(env,e1,IntTy)
  requires isSafe(env,e2,IntTy)
  ensures isSafe(env,Sub(e1,e2),IntTy)
{
  reveal isSafe();
  assert eval(env,Sub(e1,e2)).Some?;
}

lemma andIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafe(env,e1,BoolTy)
  requires isSafe(env,e2,BoolTy)
  ensures isSafe(env,And(e1,e2),BoolTy)
{
  reveal isSafe();
  assert eval(env,And(e1,e2)).Some?;
}

lemma orIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafe(env,e1,BoolTy)
  requires isSafe(env,e2,BoolTy)
  ensures isSafe(env,Or(e1,e2),BoolTy)
{
  reveal isSafe();
  assert eval(env,Or(e1,e2)).Some?;
}

lemma eqIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafeAtSomeType(env,e1)
  requires isSafeAtSomeType(env,e2)
  ensures isSafe(env,Eq(e1,e2),BoolTy)
{
  reveal isSafe();
  reveal isSafeAtSomeType();
  assert eval(env,Eq(e1,e2)).Some?;
}

lemma recordExprIsSafe(env : Env, es : seq<(string,Term)>, mt : map<string,Ty>)
  //every expression is safe at some type
  requires forall i :: 0 <= i < |es| ==> isSafeAtSomeType(env,es[i].1)
  // and the last instance of every required key is safe at the correct type.
  requires forall k :: k in mt ==> KeyExists(k,es) && isSafe(env,LastOfKey(k,es),mt[k])
  ensures isSafe(env,Record(es),RecordTy(mt))
{
  reveal isSafe();
  reveal isSafeAtSomeType();
  forall i | 0 <= i < |es|
    ensures eval(env,es[i].1).Some?
  {
    assert isSafeAtSomeType(env,es[i].1);
    var t :| isSafe(env,es[i].1,t);
    assert eval(env,es[i].1).Some?;
  } 
  evalRecordExprLemma(env,es);
}
    // lemma evalRecordExprLemma(env : Env, es : seq<(string,Term)>)
    // requires forall i | 0 <= i < |es| :: eval(env,es[i].1).Some?
    // ensures evalRecordExpr(env,es).Some?
    // ensures forall i | 0 <= i < |es| :: es[i].0 in evalRecordExpr(env,es).value.Keys
    // ensures forall k | k in evalRecordExpr(env,es).value.Keys :: KeyExists(k,es) && eval(env,LastOfKey(k,es)).value == evalRecordExpr(env,es).value[k]
    // {}

lemma recordProjIsSafe(env : Env, e : Term, k : string, mt : map<string,Ty>)
  requires isSafe(env,e,RecordTy(mt))
  requires k in mt
  ensures isSafe(env,RecordProj(e,k),mt[k])
{
  reveal isSafe();
  assert valHasType(RecordVal(evalRecord(env,e).value),RecordTy(mt));
}

lemma ifIsSafe(env : Env, eb : Term, e : Term, e' : Term, t : Ty)
  requires isSafe(env,eb,BoolTy)
  requires isSafe(env,e,t)
  requires isSafe(env,e',t)
  ensures isSafe(env,If(eb,e,e'),t)
{
  reveal isSafe();
  assert evalBool(env,eb).Some?;
}

predicate envHasCtx(env : Env, ctx : Ctx){
    forall k :: k in ctx ==> k in env && valHasType(env[k],ctx[k])
}

lemma soundSemantic (env : Env, ctx : Ctx, e : Term, t : Ty)
  requires envHasCtx(env,ctx)
  requires check(ctx,e,t).Some?
  ensures isSafe(env,e,t)
{
  match e {
    case Var(x) => varIsSafe(env,x,ctx[x]); isSafeSubtyCompat(env,e,ctx[x],t);
    case Lit(v) => litIsSafe(env,v); isSafeSubtyCompat(env,e,inferVal(v),t);
    case Add(e1,e2) => soundSemantic(env,ctx,e1,IntTy); soundSemantic(env,ctx,e2,IntTy); addIsSafe(env,e1,e2);
    case Sub(e1,e2) => soundSemantic(env,ctx,e1,IntTy); soundSemantic(env,ctx,e2,IntTy); subIsSafe(env,e1,e2);
    case Or(e1,e2) => soundSemantic(env,ctx,e1,BoolTy); soundSemantic(env,ctx,e2,BoolTy); orIsSafe(env,e1,e2);
    case And(e1,e2) => soundSemantic(env,ctx,e1,BoolTy); soundSemantic(env,ctx,e2,BoolTy); andIsSafe(env,e1,e2);
    case Eq(e1,e2) => 
    subtyRefl(infer(ctx,e1).value);
    subtyRefl(infer(ctx,e2).value);
    soundSemantic(env,ctx,e1,infer(ctx,e1).value);
    soundSemantic(env,ctx,e2,infer(ctx,e2).value);
    hideTheType(env,e1,infer(ctx,e1).value);
    hideTheType(env,e2,infer(ctx,e2).value);
    eqIsSafe(env,e1,e2);
    case Record(es) =>
      var mt :| inferRecordExpr(ctx,es) == Some(mt);
      assert subty(RecordTy(mt),t);
      invertRecordTck(ctx,es);
      
      assert forall i :: 0 <= i < |es| ==> isSafeAtSomeType(env,es[i].1) by {
        forall i | 0 <= i < |es|
          ensures isSafeAtSomeType(env,es[i].1)
        {
          var t := infer(ctx,es[i].1).value;
          subtyRefl(t);
          soundSemantic(env,ctx,es[i].1,t);
          hideTheType(env,es[i].1,t);
        }
      }

      assert (forall k :: k in mt ==> KeyExists(k,es) && isSafe(env,LastOfKey(k,es),mt[k])) by {
        forall k | k in mt
          ensures KeyExists(k,es)
          ensures isSafe(env,LastOfKey(k,es),mt[k])
        {
          assert infer(ctx,LastOfKey(k,es)).value == mt[k];
          subtyRefl(mt[k]);
          soundSemantic(env,ctx,LastOfKey(k,es),mt[k]);
        }
      }

      recordExprIsSafe(env,es,mt);
      isSafeSubtyCompat(env,e,RecordTy(mt),t);
      
    case RecordProj(e',f) =>
      var mt := inferRecordTy(ctx,e').value;
      subtyRefl(RecordTy(mt));
      soundSemantic(env,ctx,e',RecordTy(mt));
      recordProjIsSafe(env,e',f,mt);
      isSafeSubtyCompat(env,e,mt[f],t);
    case If(eb,e1,e2) =>
      soundSemantic(env,ctx,eb,BoolTy);
      subtyRefl(infer(ctx,e1).value);
      soundSemantic(env,ctx,e1,infer(ctx,e1).value);
      soundSemantic(env,ctx,e2,infer(ctx,e1).value);
      ifIsSafe(env,eb,e1,e2,infer(ctx,e1).value);
      isSafeSubtyCompat(env,e,infer(ctx,e1).value,t);
  }
}