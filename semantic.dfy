include "std.dfy"
include "util.dfy"
include "lang.dfy"

import opened def.std
import opened util
import opened lang


// datatype Option<A> = Some(value: A) | None
function eval(env : Env, e : Term) : Option<Val>
    decreases e , 0
{
  match e {
    case Var(x) => lookup(env,x)
    case Lit(v) => Some(v)
    case Add(e1,e2) => 
      var n1 :- evalInt(env,e1);
      var n2 :- evalInt(env,e2);
      Some(IntVal(n1 + n2))
    case Sub(e1,e2) => 
      var n1 :- evalInt(env,e1);
      var n2 :- evalInt(env,e2);
      Some(IntVal(n1 - n2))
    case Or(e1,e2) =>
      var b1 :- evalBool(env,e1);
      var b2 :- evalBool(env,e2);
      Some(BoolVal(b1 || b2))
    case And(e1,e2) =>
      var b1 :- evalBool(env,e1);
      var b2 :- evalBool(env,e2);
      Some(BoolVal(b1 && b2))
    case Eq(e1,e2) => 
      var v1 :- eval(env,e1);
      var v2 :- eval(env,e2);
      Some(BoolVal(v1 == v2))
    case Record(em) =>
      var m :- evalRecordExpr(env,em);
      Some(RecordVal(m))
    case RecordProj(e',f) => 
      var m :- evalRecord(env,e');
      lookup(m,f)
    case If(eb,e1,e2) =>
      var b :- evalBool(env,eb);
      if b then eval(env,e1) else eval(env,e2)
  }
}

function evalInt(env : Env, e : Term) : Option<int>
    decreases e , 1
{
    var v :- eval(env,e);
    match v {
        case IntVal(n) => Some(n)
        case _ => None
    }
}

function evalBool(env : Env, e : Term) : Option<bool>
    decreases e , 1
{
    var v :- eval(env,e);
    match v {
        case BoolVal(b) => Some(b)
        case _ => None
    }
}

function evalRecord(env : Env, e : Term) : Option<map<string,Val>>
    decreases e , 1
{
    var v :- eval(env,e);
    match v {
        case RecordVal(m) => Some(m)
        case _ => None
    }
}

function evalRecordExpr(env : Env, es : seq<(string,Term)>) : Option<map<string,Val>>
    decreases es
{
  if es == [] then Some(map[])
  else
    var k := es[0].0;
    var v :- eval(env,es[0].1);
    var vm :- evalRecordExpr(env,es[1..]);
    if k in vm.Keys then Some(vm) else Some(vm[k := v])
}

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

lemma soundBidir (env : Env, ctx : Ctx, e : Term, t : Ty)
  requires forall k :: k in ctx ==> k in env && valHasType(env[k],ctx[k])
  requires check(ctx,e,t).Some?
  ensures eval(env,e).Some? && valHasType(eval(env,e).value,t)
{
  match e {
    case Var(x) => valHasTypeSubtyCompat(env[x],ctx[x],t);
    case Lit(v) => inferValSound(v); valHasTypeSubtyCompat(v,inferVal(v),t);
    case Add(e1,e2) => soundBidir(env,ctx,e1,IntTy); soundBidir(env,ctx,e2,IntTy);
    case Sub(e1,e2) => soundBidir(env,ctx,e1,IntTy); soundBidir(env,ctx,e2,IntTy);
    case Or(e1,e2) => soundBidir(env,ctx,e1,BoolTy); soundBidir(env,ctx,e2,BoolTy);
    case And(e1,e2) => soundBidir(env,ctx,e1,BoolTy); soundBidir(env,ctx,e2,BoolTy);
    case Eq(e1,e2) =>
    subtyRefl(infer(ctx,e1).value);
    subtyRefl(infer(ctx,e2).value);
    soundBidir(env,ctx,e1,infer(ctx,e1).value);
    soundBidir(env,ctx,e2,infer(ctx,e2).value);
    case Record(es) =>
      var mt :| inferRecordExpr(ctx,es) == Some(mt);
      assert subty(RecordTy(mt),t);
      invertRecordTck(ctx,es);
      forall i | 0 <= i < |es|
        ensures eval(env,es[i].1).Some? && valHasType(eval(env,es[i].1).value,infer(ctx,es[i].1).value)
      {
        subtyRefl(infer(ctx,es[i].1).value);
        soundBidir(env,ctx,es[i].1,infer(ctx,es[i].1).value);
      }
      recordEvalLemma(env,es);
      valHasTypeSubtyCompat(eval(env,Record(es)).value,RecordTy(mt),t);
    case RecordProj(e',f) =>
      var mt := inferRecordTy(ctx,e').value;
      subtyRefl(RecordTy(mt));
      soundBidir(env,ctx,e',RecordTy(mt));
      valHasTypeSubtyCompat(evalRecord(env,e').value[f],mt[f],t);
    case If(eb,e1,e2) =>
      soundBidir(env,ctx,eb,BoolTy);
      subtyRefl(infer(ctx,e1).value);
      soundBidir(env,ctx,e1,infer(ctx,e1).value);
      soundBidir(env,ctx,e2,infer(ctx,e1).value);
      valHasTypeSubtyCompat(eval(env,e1).value,infer(ctx,e1).value,t);
      valHasTypeSubtyCompat(eval(env,e2).value,infer(ctx,e1).value,t);
  }
}

lemma invertRecordTck(ctx : Ctx, es : seq<(string,Term)>)
  requires inferRecordExpr(ctx,es).Some?
  ensures forall i | 0 <= i < |es| :: infer(ctx,es[i].1).Some?
  // Every result term in es typechecks, and every key appears in the result.
  ensures forall i | 0 <= i < |es| :: es[i].0 in inferRecordExpr(ctx,es).value.Keys
  //For every key in the output, it existed in the input, and its type is the result of inferring the type of the last instance of k.
  ensures forall k | k in inferRecordExpr(ctx,es).value.Keys :: KeyExists(k,es) && infer(ctx,LastOfKey(k,es)).value == inferRecordExpr(ctx,es).value[k]
{}

lemma recordEvalLemma(env : Env, es : seq<(string,Term)>)
  requires forall i | 0 <= i < |es| :: eval(env,es[i].1).Some?
  ensures evalRecordExpr(env,es).Some?
  ensures forall i | 0 <= i < |es| :: es[i].0 in evalRecordExpr(env,es).value.Keys
  ensures forall k | k in evalRecordExpr(env,es).value.Keys :: KeyExists(k,es) && eval(env,LastOfKey(k,es)).value == evalRecordExpr(env,es).value[k]
{}