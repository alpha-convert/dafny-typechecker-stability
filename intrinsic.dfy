include "std.dfy"
include "util.dfy"
include "lang.dfy"

import opened def.std
import opened util
import opened lang

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


predicate envHasCtx(env : Env, ctx : Ctx){
    forall k :: k in ctx ==> k in env && valHasType(env[k],ctx[k])
}


// datatype Option<A> = Some(value: A) | None
function evalIntrinsic(ghost ctx : Ctx, ghost t : Ty, env : Env, e : Term) : (res : Val)
    requires envHasCtx(env,ctx)
    requires check(ctx,e,t).Some?
    ensures valHasType(res,t)
    decreases e , 0
{
  ghost var t' :| infer(ctx,e) == Some(t');
  assert subty(t',t);
  assert (forall v :: valHasType(v,t') ==> valHasType(v,t)) by {
    forall v : Val | valHasType(v,t')
      ensures valHasType(v,t) {
        valHasTypeSubtyCompat(v,t',t);
      }
  }
  match e {
    case Var(x) => assert check(ctx,Var(x),t).Some?; env[x]
    case Lit(v) => inferValSound(v); v
    case Add(e1,e2) => 
      ghost var t2 :| check(ctx,e2,t2).Some?;
      var IntVal(n1) := evalIntrinsic(ctx,IntTy,env,e1);
      var IntVal(n2) := evalIntrinsic(ctx,t2,env,e2);
      IntVal(n1 + n2)
    case Sub(e1,e2) => 
      var IntVal(n1) := evalIntrinsic(ctx,IntTy,env,e1);
      var IntVal(n2) := evalIntrinsic(ctx,IntTy,env,e2);
      IntVal(n1 - n2)
    case Or(e1,e2) =>
      var BoolVal(b1) := evalIntrinsic(ctx,BoolTy,env,e1);
      var BoolVal(b2) := evalIntrinsic(ctx,BoolTy,env,e2);
      BoolVal(b1 || b2)
    case And(e1,e2) =>
      var BoolVal(b1) := evalIntrinsic(ctx,BoolTy,env,e1);
      var BoolVal(b2) := evalIntrinsic(ctx,BoolTy,env,e2);
      BoolVal(b1 && b2)
    case Eq(e1,e2) => 
      ghost var t1 :| infer(ctx,e1) == Some(t1);
      ghost var t2 :| infer(ctx,e2) == Some(t2);
      subtyRefl(t1);
      subtyRefl(t2);
      var v1 := evalIntrinsic(ctx,t1,env,e1);
      var v2 := evalIntrinsic(ctx,t2,env,e2);
      BoolVal(v1 == v2)
    case Record(es) =>
      ghost var mt :| inferRecordExpr(ctx,es) == Some(mt);
      RecordVal(evalIntrinsicRecordExpr(ctx,mt,env,es))
    case RecordProj(e',f) => 
      ghost var mt :| inferRecordTy(ctx,e') == Some(mt);
      subtyRefl(RecordTy(mt));
      var RecordVal(m) := evalIntrinsic(ctx,RecordTy(mt),env,e');
      m[f]
    case If(eb,e1,e2) =>
      ghost var t1 :| infer(ctx,e1) == Some(t1);
      subtyRefl(t1);
      var BoolVal(b) := evalIntrinsic(ctx,BoolTy,env,eb);
      var v := if b then evalIntrinsic(ctx,t1,env,e1) else evalIntrinsic(ctx,t1,env,e2);
      v
  }
}
// lemma invertRecordTck(ctx : Ctx, es : seq<(string,Term)>)
//   requires inferRecordExpr(ctx,es).Some?
//   ensures forall i | 0 <= i < |es| :: infer(ctx,es[i].1).Some?
//   // Every result term in es typechecks, and every key appears in the result.
//   ensures forall i | 0 <= i < |es| :: es[i].0 in inferRecordExpr(ctx,es).value.Keys
//   //For every key in the output, it existed in the input, and its type is the result of inferring the type of the last instance of k.
//   ensures forall k | k in inferRecordExpr(ctx,es).value.Keys :: KeyExists(k,es) && infer(ctx,LastOfKey(k,es)).value == inferRecordExpr(ctx,es).value[k]
// {}

function evalIntrinsicRecordExpr(ghost ctx : Ctx, ghost mt : map<string,Ty>, env : Env, es : seq<(string,Term)>) : (res : map<string,Val>)
    requires envHasCtx(env,ctx)
    requires inferRecordExpr(ctx,es).Some? && inferRecordExpr(ctx,es).value == mt;
    // requires forall i | 0 <= i < |es| :: es[i].0 in mt.Keys
    // requires forall i | 0 <= i < |es| :: infer(ctx,es[i].1).Some?
    // requires forall k | k in mt.Keys :: KeyExists(k,es) && infer(ctx,LastOfKey(k,es)).value == mt[k]

    ensures forall k :: k in mt.Keys ==> k in res && valHasType(res[k],mt[k])


    decreases es
{
  if es == [] then map[]
  else
    var k := es[0].0;
    ghost var es0t :| infer(ctx,es[0].1) == Some(es0t);
    subtyRefl(es0t);
    assert check(ctx,es[0].1,es0t).Some?;
    var v := evalIntrinsic(ctx,es0t,env,es[0].1);
    ghost var mt' :| inferRecordExpr(ctx,es[1..]) == Some(mt');
    invertRecordTck(ctx,es[1..]);
    var vm := evalIntrinsicRecordExpr(ctx,mt',env,es[1..]);

    assert mt'.Keys <= mt.Keys;
    invertRecordTck(ctx,es);
    assume false;

    if k in vm then
      vm
    else
      vm[k := v]
}

// lemma soundBidir (env : Env, ctx : Ctx, e : Term, t : Ty)
//   requires forall k :: k in ctx ==> k in env && valHasType(env[k],ctx[k])
//   requires check(ctx,e,t).Some?
//   ensures evalIntrinsic(env,e).Some? && valHasType(evalIntrinsic(env,e).value,t)
// {
//   match e {
//     case Var(x) => valHasTypeSubtyCompat(env[x],ctx[x],t);
//     case Lit(v) => inferValSound(v); valHasTypeSubtyCompat(v,inferVal(v),t);
//     case Add(e1,e2) => soundBidir(env,ctx,e1,IntTy); soundBidir(env,ctx,e2,IntTy);
//     case Sub(e1,e2) => soundBidir(env,ctx,e1,IntTy); soundBidir(env,ctx,e2,IntTy);
//     case Or(e1,e2) => soundBidir(env,ctx,e1,BoolTy); soundBidir(env,ctx,e2,BoolTy);
//     case And(e1,e2) => soundBidir(env,ctx,e1,BoolTy); soundBidir(env,ctx,e2,BoolTy);
//     case Eq(e1,e2) =>
//     subtyRefl(infer(ctx,e1).value);
//     subtyRefl(infer(ctx,e2).value);
//     soundBidir(env,ctx,e1,infer(ctx,e1).value);
//     soundBidir(env,ctx,e2,infer(ctx,e2).value);
//     case Record(es) =>
//       var mt :| inferRecordExpr(ctx,es) == Some(mt);
//       assert subty(RecordTy(mt),t);
//       invertRecordTck(ctx,es);
//       forall i | 0 <= i < |es|
//         ensures evalIntrinsic(env,es[i].1).Some? && valHasType(evalIntrinsic(env,es[i].1).value,infer(ctx,es[i].1).value)
//       {
//         subtyRefl(infer(ctx,es[i].1).value);
//         soundBidir(env,ctx,es[i].1,infer(ctx,es[i].1).value);
//       }
//       recordevalIntrinsicLemma(env,es);
//       valHasTypeSubtyCompat(evalIntrinsic(env,Record(es)).value,RecordTy(mt),t);
//     case RecordProj(e',f) =>
//       var mt := inferRecordTy(ctx,e').value;
//       subtyRefl(RecordTy(mt));
//       soundBidir(env,ctx,e',RecordTy(mt));
//       valHasTypeSubtyCompat(evalIntrinsicRecord(env,e').value[f],mt[f],t);
//     case If(eb,e1,e2) =>
//       soundBidir(env,ctx,eb,BoolTy);
//       subtyRefl(infer(ctx,e1).value);
//       soundBidir(env,ctx,e1,infer(ctx,e1).value);
//       soundBidir(env,ctx,e2,infer(ctx,e1).value);
//       valHasTypeSubtyCompat(evalIntrinsic(env,e1).value,infer(ctx,e1).value,t);
//       valHasTypeSubtyCompat(evalIntrinsic(env,e2).value,infer(ctx,e1).value,t);
//   }
// }



// lemma recordevalIntrinsicLemma(env : Env, es : seq<(string,Term)>)
//   requires forall i | 0 <= i < |es| :: evalIntrinsic(env,es[i].1).Some?
//   ensures evalIntrinsicRecordExpr(env,es).Some?
//   ensures forall i | 0 <= i < |es| :: es[i].0 in evalIntrinsicRecordExpr(env,es).value.Keys
//   ensures forall k | k in evalIntrinsicRecordExpr(env,es).value.Keys :: KeyExists(k,es) && evalIntrinsic(env,LastOfKey(k,es)).value == evalIntrinsicRecordExpr(env,es).value[k]
// {}