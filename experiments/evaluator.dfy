include "std.dfy"
include "util.dfy"
include "lang.dfy"


module evaluator {
    import opened def.std
    import opened util
    import opened lang

    datatype EvalErr = DivByZeroErr | RuntimeTyErr | VarNotFoundErr

    function eval(env : Env, e : Term) : Result<Val,EvalErr>
        decreases e , 0
    {
    match e {
        case Var(x) => lookup(env,x,VarNotFoundErr)
        case Lit(v) => Ok(v)
        case Add(e1,e2) => 
            var n1 :- evalInt(env,e1);
            var n2 :- evalInt(env,e2);
            Ok(IntVal(n1 + n2))
        case Sub(e1,e2) => 
            var n1 :- evalInt(env,e1);
            var n2 :- evalInt(env,e2);
            Ok(IntVal(n1 - n2))
        case Div(e1,e2) =>
            var n1 :- evalInt(env,e1);
            var n2 :- evalInt(env,e2);
            if n2 == 0 then Err(DivByZeroErr) else Ok(IntVal(n1 / n2))
        case Or(e1,e2) =>
            var b1 :- evalBool(env,e1);
            var b2 :- evalBool(env,e2);
            Ok(BoolVal(b1 || b2))
        case And(e1,e2) =>
            var b1 :- evalBool(env,e1);
            var b2 :- evalBool(env,e2);
            Ok(BoolVal(b1 && b2))
        case Eq(e1,e2) =>
            var v1 :- eval(env,e1);
            var v2 :- eval(env,e2);
            Ok(BoolVal(v1 == v2))
        case Record(em) =>
            var m :- evalRecordExpr(env,em);
            Ok(RecordVal(m))
        case RecordProj(e',f) => 
            var m :- evalRecord(env,e');
            lookup(m,f,RuntimeTyErr)
        case If(eb,e1,e2) =>
            var b :- evalBool(env,eb);
            if b then eval(env,e1) else eval(env,e2)
    }
    }

    function evalInt(env : Env, e : Term) : Result<int,EvalErr>
        decreases e , 1
    {
        var v :- eval(env,e);
        match v {
            case IntVal(n) => Ok(n)
            case _ => Err(RuntimeTyErr)
        }
    }

    function evalBool(env : Env, e : Term) : Result<bool,EvalErr>
        decreases e , 1
    {
        var v :- eval(env,e);
        match v {
            case BoolVal(b) => Ok(b)
            case _ => Err(RuntimeTyErr)
        }
    }

    function evalRecord(env : Env, e : Term) : Result<map<string,Val>,EvalErr>
        decreases e , 1
    {
        var v :- eval(env,e);
        match v {
            case RecordVal(m) => Ok(m)
            case _ => Err(RuntimeTyErr)
        }
    }

    function evalRecordExpr(env : Env, es : seq<(string,Term)>) : Result<map<string,Val>,EvalErr>
        decreases es
    {
    if es == [] then Ok(map[])
    else
        var k := es[0].0;
        var v :- eval(env,es[0].1);
        var vm :- evalRecordExpr(env,es[1..]);
        if k in vm.Keys then Ok(vm) else Ok(vm[k := v])
    }

    lemma evalRecordExprLemmaOk(env : Env, es : seq<(string,Term)>)
    requires forall i | 0 <= i < |es| :: eval(env,es[i].1).Ok?
    ensures evalRecordExpr(env,es).Ok?
    ensures forall i | 0 <= i < |es| :: es[i].0 in evalRecordExpr(env,es).value.Keys
    ensures forall k | k in evalRecordExpr(env,es).value.Keys :: KeyExists(k,es) && eval(env,LastOfKey(k,es)).value == evalRecordExpr(env,es).value[k]
    {}

    lemma evalRecordExprLemmaErr(env : Env, es : seq<(string,Term)>)
    requires exists i | 0 <= i < |es| :: eval(env,es[i].1).Err?
    ensures evalRecordExpr(env,es).Err? && evalRecordExpr(env,es).error == eval(env,es[FirstError(es,x => eval(env,x))].1).error
    {
        if(eval(env,es[0].1).Ok?){}
    }

}

