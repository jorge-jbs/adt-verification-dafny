
module Map{

ghost function Identity(i:int):int
ensures Identity(i)==i
{i}

ghost function IdentityMap(s:set<int>):map<int,int>
ensures forall i | i in s :: i in IdentityMap(s) && (IdentityMap(s))[i]==i 
ensures forall i | i in IdentityMap(s) :: i in s
{ map i | i in s :: i}


ghost function IdSeqMap(xs:seq<int>):map<int,int>
//{map i | -1 <= i <= |xs| :: i}
{ IdentityMap(set i | -1 <= i <= |xs|) }

ghost function BuildMap(s:set<int>,f:int -> int):map<int,int>
ensures forall i | i in s :: i in BuildMap(s,f) && (BuildMap(s,f))[i]==f(i) 
ensures forall i | i in BuildMap(s,f) :: i in s
{ map i | i in s :: f(i)}

ghost function UpdateMap(m1: map<int,int>, m2: map<int,int>): map<int, int>
ensures
  (forall k | k in m1 || k in m2 :: k in UpdateMap(m1, m2)) &&
  (forall k | k in m2 :: UpdateMap(m1, m2)[k] == m2[k]) &&
  (forall k | !(k in m2) && k in m1 :: UpdateMap(m1, m2)[k] == m1[k]) &&
  (forall k | !(k in m2) && !(k in m1) :: !(k in UpdateMap(m1, m2))) &&
  (forall k | k in UpdateMap(m1, m2) :: k in m1 || k in m2)
{
  map k | k in (m1.Keys + m2.Keys) :: if k in m2 then m2[k] else m1[k]
}
}