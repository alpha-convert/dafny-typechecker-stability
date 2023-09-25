include "std.dfy"
include "util.dfy"

import opened def.std
import opened util

// datatype Option<A> = Some(value: A) | None

datatype Term  =
  | Var(x : string)
  | Add(e : Term, e': Term)
  | Sub(e : Term, e': Term)
  | Or(e : Term, e' : Term)
  | And(e : Term, e' : Term)
  | Eq(e : Term, e' : Term)
  | Record(em : seq<(string,Term)>)
  | RecordHas(e : Term, f : string)
  | RecordProj(e : Term, f : string)
  | If(eb : Term, e : Term, e' : Term)

datatype Val = IntVal(v : int) | BoolVal(b : bool) | RecordVal(m : map<string,Val>)

type Env = map<string,Val>

function eval(env : Env, e : Term) : Option<Val>
    decreases e , 0
{
  match e {
    case Var(x) => lookup(env,x)
    case Add(e,e') => 
      var n1 :- evalInt(env,e);
      var n2 :- evalInt(env,e');
      Some(IntVal(n1 + n2))
    case Sub(e,e') => 
      var n1 :- evalInt(env,e);
      var n2 :- evalInt(env,e');
      Some(IntVal(n1 - n2))
    case Or(e,e') =>
      var b1 :- evalBool(env,e);
      var b2 :- evalBool(env,e');
      Some(BoolVal(b1 || b2))
    case And(e,e') =>
      var b1 :- evalBool(env,e);
      var b2 :- evalBool(env,e');
      Some(BoolVal(b1 && b2))
    case Eq(e,e') => 
      var v :- eval(env,e);
      var v' :- eval(env,e');
      Some(BoolVal(v == v'))
    case Record(em) =>
      var m :- evalRecordExpr(env,em);
      Some(RecordVal(m))
    case RecordHas(e,f) =>
      var m :- evalRecord(env,e);
      Some(BoolVal(f in m))
    case RecordProj(e,f) => 
      var m :- evalRecord(env,e);
      lookup(m,f)
    case If(eb,e,e') =>
      var b :- evalBool(env,eb);
      if b then eval(env,e) else eval(env,e')
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

datatype Ty = IntTy | BoolTy | RecordTy(rm : map<string,Ty>)

type Ctx = map<string,Ty>

function infer(ctx : Ctx, e : Term) : Option<Ty>
    decreases e, 0
{
  match e {
    case Var(x) => if x in ctx then Some(ctx[x]) else None
    case Add(e,e') => 
      var _ :- inferIntTy(ctx,e);
      var _ :- inferIntTy(ctx,e');
      Some(IntTy)
    case Sub(e,e') => 
      var _ :- inferIntTy(ctx,e);
      var _ :- inferIntTy(ctx,e');
      Some(IntTy)
    case Or(e,e') =>
      var _ :- inferBoolTy(ctx,e);
      var _ :- inferBoolTy(ctx,e');
      Some(BoolTy)
    case And(e,e') =>
      var _ :- inferBoolTy(ctx,e);
      var _ :- inferBoolTy(ctx,e');
      Some(BoolTy)
    case Eq(e,e') =>
      var _ :- infer(ctx,e);
      var _ :- infer(ctx,e');
      Some(BoolTy)
    case Record(es) =>
      var tm :- inferRecordExpr(ctx,es);
      Some(RecordTy(tm))
    case RecordHas(e,f) =>
      var _ :- inferRecordTy(ctx,e);
      Some(BoolTy)
    case RecordProj(e,f) =>
      var m :- inferRecordTy(ctx,e);
      lookup(m,f)
    case If(eb,e,e') =>
      var _ :- inferBoolTy(ctx,eb);
      var t1 :- infer(ctx,e);
      var t2 :- infer(ctx,e');
      if t1 == t2 then Some(t1) else None
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
    case Eq(e,e') => sound(env,ctx,e); sound(env,ctx,e');
    case Record(es) =>
      var mt :| inferRecordExpr(ctx,es) == Some(mt);
      invertRecordTck(ctx,es);
      forall i | 0 <= i < |es|
        ensures eval(env,es[i].1).Some? && valHasType(eval(env,es[i].1).value,infer(ctx,es[i].1).value)
      {
        sound(env,ctx,es[i].1);
      }
      recordEvalLemma(env,es);
    case RecordHas(e,f) => sound(env,ctx,e);
    case RecordProj(e,f) => sound(env,ctx,e);
    case If(eb,e,e') => sound(env,ctx,eb); sound(env,ctx,e); sound(env,ctx,e');
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
{
}