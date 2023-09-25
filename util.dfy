module util {
    // KeyExists and LastOfKey are helpers about association lists that are used in
    // validation.dfy, so we lift them here.
    // We use these as an abbreviation for the quantifier alternation:
    // exists i :: 0 <= i < |es| && (forall j :: i < j < |es| => ...)
    // This helps dafny prove some of our lemmas about record evaluation and validation.
    ghost predicate KeyExists<K,V>(k: K, es: seq<(K,V)>) {
    exists i :: 0 <= i < |es| && es[i].0 == k
    }

    opaque ghost function LastOfKey<K,V>(k: K, es: seq<(K,V)>): (res: V)
    requires KeyExists(k,es)
    ensures exists i :: 0 <= i < |es| && es[i].0 == k && es[i].1 == res && (forall j | i < j < |es| :: es[j].0 != k)
    {
    if (es[0].0 == k && (forall j | 0 < j < |es| :: es[j].0 != k)) then es[0].1 else LastOfKey(k,es[1..])
    }
}
