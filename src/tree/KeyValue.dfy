module KeyValue {
  type K = int
  type V = int

  function key(p: (K, V)): K
  {
    p.0
  }

  function value(p: (K, V)): V
  {
    p.1
  }

  lemma prove(m: map<K, V>)
    ensures forall k | k in m.Keys :: m[k] in m.Values
    ensures forall p: (K, V) | p in m.Items:: key(p) in m && value(p) == m[key(p)]
    ensures |m| == |m.Keys|
  {}

  /*function Keys(m:map<K,V>): set<K>
       ensures Keys(m)==set k | k in m :: k
      // ensures |Keys(m)|==|m|
       {set k | k in m :: k}
  
    function Pairs(m : map<K,V> ): set<pairKV>
       ensures Pairs(m)== (set k,v | k in m && v == m[k] :: (k,v))
       ensures forall p, p'| p in Pairs(m) && p' in Pairs(m) && p!=p' :: p.0!=p'.0
       ensures forall k, v  | k in m && m[k]==v:: (k,v) in Pairs(m)
       ensures forall k,v | (k,v) in Pairs(m) :: k in m && m[k]==v
      // ensures |Pairs(m)|==|Keys(m)|
       { 
         (set k,v | k in m && v == m[k] :: (k,v))}
  */}
