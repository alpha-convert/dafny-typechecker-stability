include "std.dfy"
include "util.dfy"
include "lang.dfy"
include "evaluator.dfy"

import opened def.std
import opened util
import opened lang
import opened evaluator




datatype TckErr = TckErr

opaque function infer(ctx : Ctx, e : Term) : Result<Ty,TckErr>

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

opaque function inferIntTy(ctx : Ctx, e : Term) : Result<(),TckErr>
    decreases e, 1
{
    var t :- infer(ctx,e);
    match t {
        case IntTy => Ok(())
        case _ => Err(TckErr)
    }
}

opaque function inferBoolTy(ctx : Ctx, e : Term) : Result<(),TckErr>
    decreases e, 1
{
    var t :- infer(ctx,e);
    match t {
        case BoolTy => Ok(())
        case _ => Err(TckErr)
    }
}

opaque function inferRecordTy(ctx : Ctx, e : Term) : Result<map<string,Ty>,TckErr>
    decreases e, 1
{
    var t :- infer(ctx,e);
    match t {
        case RecordTy(m) => Ok(m)
        case _ => Err(TckErr)
    }
}

opaque function inferRecordExpr(ctx : Ctx, es : seq<(string,Term)>) : Result<map<string,Ty>,TckErr>
    decreases es
{
  if es == [] then Ok(map[])
  else
    var k := es[0].0;
    var t :- infer(ctx,es[0].1);
    var tm :- inferRecordExpr(ctx,es[1..]);
    if k in tm then Ok(tm) else Ok(tm[k := t])
}

lemma invertRecordTck(ctx : Ctx, es : seq<(string,Term)>)
  requires inferRecordExpr(ctx,es).Ok?
  ensures forall i | 0 <= i < |es| :: infer(ctx,es[i].1).Ok?
  // Every result term in es typechecks, and every key appears in the result.
  ensures forall i | 0 <= i < |es| :: es[i].0 in inferRecordExpr(ctx,es).value.Keys
  //For every key in the output, it existed in the input, and its type is the result of inferring the type of the last instance of k.
  ensures forall k | k in inferRecordExpr(ctx,es).value.Keys :: KeyExists(k,es) && infer(ctx,LastOfKey(k,es)).value == inferRecordExpr(ctx,es).value[k]
{
  reveal check();
  reveal infer();
  reveal inferRecordExpr();
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

opaque function check(ctx : Ctx, e : Term, t : Ty) : Result<(),TckErr>
  decreases e , 1
{
  var t' :- infer(ctx,e);
  if subty(t',t) then Ok(()) else Err(TckErr)
}


ghost predicate someTypeChecks(ctx : Ctx, e : Term)
{
  exists t :: check(ctx,e,t).Ok?
}

lemma invertVarCheck(ctx : Ctx, x : string, t : Ty)
    requires check(ctx,Var(x),t).Ok? 
    ensures x in ctx
    ensures subty(ctx[x],t)
{
    reveal check();
    reveal infer();
}

lemma invertLitCheck(ctx : Ctx, v : Val, t : Ty)
    requires check(ctx,Lit(v),t).Ok?
    ensures subty(inferVal(v),t)
{
    reveal infer();
    reveal check();
}

lemma invertAddCheck(ctx : Ctx, e1 : Term, e2 : Term, t : Ty)
    requires check(ctx,Add(e1,e2),t).Ok?
    ensures check(ctx,e1,IntTy).Ok?
    ensures check(ctx,e2,IntTy).Ok?
    ensures t == IntTy
{
    reveal infer();
    reveal check();
}

lemma invertSubCheck(ctx : Ctx, e1 : Term, e2 : Term, t : Ty)
    requires check(ctx,Sub(e1,e2),t).Ok?
    ensures check(ctx,e1,IntTy).Ok?
    ensures check(ctx,e2,IntTy).Ok?
    ensures t == IntTy
{
    reveal infer();
    reveal check();
}

lemma invertDivCheck(ctx : Ctx, e1 : Term, e2 : Term, t : Ty)
    requires check(ctx,Div(e1,e2),t).Ok?
    ensures check(ctx,e1,IntTy).Ok?
    ensures check(ctx,e2,IntTy).Ok?
    ensures t == IntTy
{
    reveal infer();
    reveal check();
}

lemma invertAndCheck(ctx : Ctx, e1 : Term, e2 : Term, t : Ty)
    requires check(ctx,And(e1,e2),t).Ok?
    ensures check(ctx,e1,BoolTy).Ok?
    ensures check(ctx,e2,BoolTy).Ok?
    ensures t == BoolTy
{
    reveal check();
    reveal infer();
}

lemma invertOrCheck(ctx : Ctx, e1 : Term, e2 : Term, t : Ty)
    requires check(ctx,Or(e1,e2),t).Ok?
    ensures check(ctx,e1,BoolTy).Ok?
    ensures check(ctx,e2,BoolTy).Ok?
    ensures t == BoolTy
{
    reveal check();
    reveal infer();
}

lemma invertEqCheck(ctx : Ctx, e1 : Term, e2 : Term, t : Ty)
    requires check(ctx,Eq(e1,e2),t).Ok?
    ensures exists t1 :: check(ctx,e1,t1).Ok?
    ensures exists t2 :: check(ctx,e2,t2).Ok?
    ensures t == BoolTy
{
    reveal check();
    reveal infer();
    assert infer(ctx,e1).Ok?;
    assert infer(ctx,e2).Ok?;
    subtyRefl(infer(ctx,e1).value);
    subtyRefl(infer(ctx,e2).value);
    assert check(ctx,e1,infer(ctx,e1).value).Ok?;
    assert check(ctx,e2,infer(ctx,e2).value).Ok?;
}

lemma invertRecordProjCheck(ctx : Ctx, e : Term, k : string, t : Ty)
  requires check(ctx,RecordProj(e,k),t).Ok?
  ensures exists mt :: check(ctx,e,RecordTy(mt)).Ok? && k in mt && subty(mt[k],t)
{
  reveal check();
  reveal infer();
  reveal inferRecordTy();
  var mt := inferRecordTy(ctx,e).value;
  subtyRefl(RecordTy(mt));
}

lemma invertRecordTckRaw(ctx : Ctx, es : seq<(string,Term)>)
  requires inferRecordExpr(ctx,es).Ok?
  ensures forall i | 0 <= i < |es| :: infer(ctx,es[i].1).Ok?
  // Every result term in es typechecks, and every key appears in the result.
  ensures forall i | 0 <= i < |es| :: es[i].0 in inferRecordExpr(ctx,es).value.Keys
  //For every key in the output, it existed in the input, and its type is the result of inferring the type of the last instance of k.
  ensures forall k | k in inferRecordExpr(ctx,es).value.Keys :: KeyExists(k,es) && infer(ctx,LastOfKey(k,es)).value == inferRecordExpr(ctx,es).value[k]
{
  reveal check();
  reveal infer();
  reveal inferRecordExpr();
}



lemma invertRecordCheck(ctx : Ctx, es : seq<(string,Term)>, t : Ty)
  requires check(ctx,Record(es),t).Ok?
  ensures inferRecordExpr(ctx,es).Ok?
  ensures forall i :: 0 <= i < |es| ==> someTypeChecks(ctx,es[i].1)

  ensures exists mt :: t == RecordTy(mt) && (forall k :: k in mt ==> KeyExists(k,es) && check(ctx,LastOfKey(k,es),mt[k]).Ok?)
{
  reveal check();
  reveal infer();
  reveal inferRecordExpr();
  invertRecordTckRaw(ctx,es);

  forall i | 0 <= i < |es|
    ensures exists t :: check(ctx,es[i].1,t).Ok?
  {
    assert infer(ctx,es[i].1).Ok?;
    subtyRefl(infer(ctx,es[i].1).value);
    assert check(ctx,es[i].1,infer(ctx,es[i].1).value).Ok?;
  }

}

lemma invertIfCheck(ctx : Ctx, eb : Term, e : Term, e' : Term, t : Ty)
    requires check(ctx,If(eb,e,e'),t).Ok?
    ensures check(ctx,eb,BoolTy).Ok?
    ensures check(ctx,e,t).Ok?
    ensures check(ctx,e',t).Ok?
{
    reveal check();
    reveal infer();
    assert infer(ctx,e).Ok?;
    assert check(ctx,e',infer(ctx,e).value).Ok?;
    // assert infer(ctx,e').Ok?;
    // assert check(ctx,e,t).Ok?;
    assert subty(infer(ctx,e').value,infer(ctx,e).value);
    subtyTrans(infer(ctx,e').value,infer(ctx,e).value,t);
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
  (eval(env,e).Ok? && valHasType(eval(env,e).value,t)) || (eval(env,e).Err? && eval(env,e).error == DivByZeroErr)
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
  if(eval(env,e).Ok?){
    valHasTypeSubtyCompat(eval(env,e).value,t,t');
  }
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
  if(eval(env,e1).Ok? && eval(env,e2).Ok?) {
    assert eval(env,Add(e1,e2)).Ok?;
  } else {
    assert eval(env,Add(e1,e2)).Err?;
    assert eval(env,Add(e1,e2)).error == DivByZeroErr;
  }
}

lemma subIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafe(env,e1,IntTy)
  requires isSafe(env,e2,IntTy)
  ensures isSafe(env,Sub(e1,e2),IntTy)
{
  reveal isSafe();
  if(eval(env,e1).Ok? && eval(env,e2).Ok?) {
    assert eval(env,Sub(e1,e2)).Ok?;
  } else {
    assert eval(env,Sub(e1,e2)).Err?;
    assert eval(env,Div(e1,e2)).error == DivByZeroErr;
  }
}

lemma divIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafe(env,e1,IntTy)
  requires isSafe(env,e2,IntTy)
  ensures isSafe(env,Div(e1,e2),IntTy)
{
  reveal isSafe();
  if(eval(env,e1).Ok? && eval(env,e2).Ok? && evalInt(env,e2).value != 0) {
    assert eval(env,Div(e1,e2)).Ok?;
  } else {
    assert eval(env,Div(e1,e2)).Err?;
    assert eval(env,Div(e1,e2)).error == DivByZeroErr;
  }
}

lemma andIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafe(env,e1,BoolTy)
  requires isSafe(env,e2,BoolTy)
  ensures isSafe(env,And(e1,e2),BoolTy)
{
  reveal isSafe();
  if(eval(env,e1).Ok? && eval(env,e2).Ok?) {
    assert eval(env,And(e1,e2)).Ok?;
  } else {
    assert eval(env,And(e1,e2)).Err?;
    assert eval(env,And(e1,e2)).error == DivByZeroErr;
  }
}

lemma orIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafe(env,e1,BoolTy)
  requires isSafe(env,e2,BoolTy)
  ensures isSafe(env,Or(e1,e2),BoolTy)
{
  reveal isSafe();
  if(eval(env,e1).Ok? && eval(env,e2).Ok?) {
    assert eval(env,Or(e1,e2)).Ok?;
  } else {
    assert eval(env,Or(e1,e2)).Err?;
    assert eval(env,Or(e1,e2)).error == DivByZeroErr;
  }
}

lemma eqIsSafe(env : Env, e1 : Term, e2 : Term)
  requires isSafeAtSomeType(env,e1)
  requires isSafeAtSomeType(env,e2)
  ensures isSafe(env,Eq(e1,e2),BoolTy)
{
  reveal isSafe();
  reveal isSafeAtSomeType();
  if(eval(env,e1).Ok? && eval(env,e2).Ok?) {
    assert eval(env,Eq(e1,e2)).Ok?;
  } else {
    assert eval(env,Eq(e1,e2)).Err?;
  }
}

lemma recordExprIsSafe(env : Env, es : seq<(string,Term)>, mt : map<string,Ty>)
  //every expression is safe at Ok type
  requires forall i :: 0 <= i < |es| ==> isSafeAtSomeType(env,es[i].1)
  // and the last instance of every required key is safe at the correct type.
  requires forall k :: k in mt ==> KeyExists(k,es) && isSafe(env,LastOfKey(k,es),mt[k])
  ensures isSafe(env,Record(es),RecordTy(mt))
{
  reveal isSafe();
  reveal isSafeAtSomeType();
  if(forall i | 0 <= i < |es| :: eval(env,es[i].1).Ok?){
    evalRecordExprLemmaOk(env,es);
  } else {
    evalRecordExprLemmaErr(env,es);
  }
  
}
    // lemma evalRecordExprLemma(env : Env, es : seq<(string,Term)>)
    // requires forall i | 0 <= i < |es| :: eval(env,es[i].1).Ok?
    // ensures evalRecordExpr(env,es).Ok?
    // ensures forall i | 0 <= i < |es| :: es[i].0 in evalRecordExpr(env,es).value.Keys
    // ensures forall k | k in evalRecordExpr(env,es).value.Keys :: KeyExists(k,es) && eval(env,LastOfKey(k,es)).value == evalRecordExpr(env,es).value[k]
    // {}

lemma recordProjIsSafe(env : Env, e : Term, k : string, mt : map<string,Ty>)
  requires isSafe(env,e,RecordTy(mt))
  requires k in mt
  ensures isSafe(env,RecordProj(e,k),mt[k])
{
  reveal isSafe();
  if(evalRecord(env,e).Ok?){
    assert valHasType(RecordVal(evalRecord(env,e).value),RecordTy(mt));
  }
}

lemma ifIsSafe(env : Env, eb : Term, e : Term, e' : Term, t : Ty)
  requires isSafe(env,eb,BoolTy)
  requires isSafe(env,e,t)
  requires isSafe(env,e',t)
  ensures isSafe(env,If(eb,e,e'),t)
{
  reveal isSafe();
  if(evalBool(env,eb).Ok?){

  }
}



predicate envHasCtx(env : Env, ctx : Ctx){
    forall k :: k in ctx ==> k in env && valHasType(env[k],ctx[k])
}

lemma soundInversionSemantic (env : Env, ctx : Ctx, e : Term, t : Ty)
  requires envHasCtx(env,ctx)
  requires check(ctx,e,t).Ok?
  ensures isSafe(env,e,t)
{
  match e {
    case Var(x) => invertVarCheck(ctx,x,t); varIsSafe(env,x,ctx[x]); isSafeSubtyCompat(env,e,ctx[x],t);
    case Lit(v) => invertLitCheck(ctx,v,t); litIsSafe(env,v); isSafeSubtyCompat(env,e,inferVal(v),t);
    case Add(e1,e2) => invertAddCheck(ctx,e1,e2,t); soundInversionSemantic(env,ctx,e1,IntTy); soundInversionSemantic(env,ctx,e2,IntTy); addIsSafe(env,e1,e2);
    case Sub(e1,e2) => invertSubCheck(ctx,e1,e2,t); soundInversionSemantic(env,ctx,e1,IntTy); soundInversionSemantic(env,ctx,e2,IntTy); subIsSafe(env,e1,e2);
    case Div(e1,e2) => invertDivCheck(ctx,e1,e2,t); soundInversionSemantic(env,ctx,e1,IntTy); soundInversionSemantic(env,ctx,e2,IntTy); divIsSafe(env,e1,e2);
    case Or(e1,e2) => invertOrCheck(ctx,e1,e2,t); soundInversionSemantic(env,ctx,e1,BoolTy); soundInversionSemantic(env,ctx,e2,BoolTy); orIsSafe(env,e1,e2);
    case And(e1,e2) => invertAndCheck(ctx,e1,e2,t); soundInversionSemantic(env,ctx,e1,BoolTy); soundInversionSemantic(env,ctx,e2,BoolTy); andIsSafe(env,e1,e2);
    case Eq(e1,e2) => invertEqCheck(ctx,e1,e2,t);
    var t1 :| check(ctx,e1,t1).Ok?;
    var t2 :| check(ctx,e2,t2).Ok?;
    soundInversionSemantic(env,ctx,e1,t1);
    soundInversionSemantic(env,ctx,e2,t2);
    hideTheType(env,e1,t1);
    hideTheType(env,e2,t2);
    eqIsSafe(env,e1,e2);
    case Record(es) =>
      invertRecordCheck(ctx,es,t);
      var mt :| t == RecordTy(mt) && (forall k :: k in mt ==> KeyExists(k,es) && check(ctx,LastOfKey(k,es),mt[k]).Ok?);
      assert forall i :: 0 <= i < |es| ==> someTypeChecks(ctx,es[i].1);
      
      assert forall i :: 0 <= i < |es| ==> isSafeAtSomeType(env,es[i].1) by {
        forall i | 0 <= i < |es|
          ensures isSafeAtSomeType(env,es[i].1)
        {
          assert someTypeChecks(ctx,es[i].1);
          var t' :| check(ctx,es[i].1,t').Ok?;
          soundInversionSemantic(env,ctx,es[i].1,t');
          hideTheType(env,es[i].1,t');
        }
      }

      assert (forall k :: k in mt ==> KeyExists(k,es) && isSafe(env,LastOfKey(k,es),mt[k])) by {
        forall k | k in mt
          ensures KeyExists(k,es)
          ensures isSafe(env,LastOfKey(k,es),mt[k])
        {
          assert check(ctx,LastOfKey(k,es),mt[k]).Ok?;
          soundInversionSemantic(env,ctx,LastOfKey(k,es),mt[k]);
        }
      }
      recordExprIsSafe(env,es,mt);
      
    case RecordProj(e',f) =>
      invertRecordProjCheck(ctx,e',f,t);
      var mt :| check(ctx,e',RecordTy(mt)).Ok? && f in mt && subty(mt[f],t);
      soundInversionSemantic(env,ctx,e',RecordTy(mt));
      recordProjIsSafe(env,e',f,mt);
      isSafeSubtyCompat(env,e,mt[f],t);
    case If(eb,e1,e2) =>
      invertIfCheck(ctx,eb,e1,e2,t);
      soundInversionSemantic(env,ctx,eb,BoolTy);
      soundInversionSemantic(env,ctx,e1,t);
      soundInversionSemantic(env,ctx,e2,t);
      ifIsSafe(env,eb,e1,e2,t);
  }
}