function identity(i:int):int
ensures identity(i)==i
{i}

function identityMap(s:set<int>):map<int,int>
ensures forall i | i in s :: i in identityMap(s) && (identityMap(s))[i]==i 
{ map i | i in s :: i}



function buildMap(s:set<int>,f:int -> int):map<int,int>
ensures forall i | i in s :: i in buildMap(s,f) && (buildMap(s,f))[i]==f(i) 
{ map i | i in s :: f(i)}

function updateMap(m1: map<int,int>, m2: map<int,int>): map<int, int>
ensures
  (forall k :: k in m1 || k in m2 ==> k in updateMap(m1, m2)) &&
  (forall k :: k in m2 ==> updateMap(m1, m2)[k] == m2[k]) &&
  (forall k :: !(k in m2) && k in m1 ==> updateMap(m1, m2)[k] == m1[k]) &&
  (forall k :: !(k in m2) && !(k in m1) ==> !(k in updateMap(m1, m2)))

{
  map k | k in (m1.Keys + m2.Keys) :: if k in m2 then m2[k] else m1[k]
}
