include "std.dfy"
include "util.dfy"
include "lang.dfy"


module evaluator {
    import opened def.std
    import opened util
    import opened lang

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

    lemma evalRecordExprLemma(env : Env, es : seq<(string,Term)>)
    requires forall i | 0 <= i < |es| :: eval(env,es[i].1).Some?
    ensures evalRecordExpr(env,es).Some?
    ensures forall i | 0 <= i < |es| :: es[i].0 in evalRecordExpr(env,es).value.Keys
    ensures forall k | k in evalRecordExpr(env,es).value.Keys :: KeyExists(k,es) && eval(env,LastOfKey(k,es)).value == evalRecordExpr(env,es).value[k]
    {}

}

