include "KeyValue.dfy"


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
*/

trait UnorderedMapIterator{

function Parent(): UnorderedMap
    reads this

predicate Valid()
    reads this, Parent(), Parent().Repr()

function Traversed():set<K>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed() <= (Parent().Model().Keys)

function method Peek():pairKV 
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model().Items &&
            key(Peek()) !in Traversed() &&
            // key(Peek()) in Parent().Model() && 
            value(Peek())==Parent().Model()[key(Peek())]
  

 function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext()  <==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasNext() ==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|
  
  method Next() returns (p: pairKV)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())

    ensures p==old(Peek()) && Traversed() == {old(key(Peek()))}+old(Traversed())
    
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek())))

  method Copy() returns (it: UnorderedMapIterator)
    modifies Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures fresh(it)
    ensures Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Valid()
    ensures Parent().Model() == old(Parent().Model())

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)
    
    ensures it.Valid()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Traversed() == it.Traversed() && (it.HasNext() ==> Peek()==it.Peek())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))


}

trait UnorderedMap {
  
   function ReprDepth(): nat
    reads this
    ensures ReprDepth() > 0

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= ReprDepth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)

  function Repr(): set<object>
    reads this, ReprFamily(ReprDepth()-1)
  {
    ReprFamily(ReprDepth())
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());

  predicate Valid()
    reads this, Repr()

  function Model(): map<K,V>
    reads this, Repr()
    requires Valid()

  
  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == map[]
  
 function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|

 function Iterators(): set<UnorderedMapIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

method First() returns (it: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed()=={} 
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

 method contains(k:K) returns (b:bool)
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures b==(k in Model()) 
  
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())


method at(k:K) returns (v:V)
    //modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    requires k in Model()
    ensures Valid()
    //ensures Model()==old(Model())
    ensures v == Model()[k] 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())

 method add(k:K,v:V)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())[k:=v] 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())


method remove(k:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== map k' | k' in old(Model()) && k'!=k::old(Model())[k']

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())



method find(k:K) returns (newt:UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model()==old(Model())
    
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent()==this
    ensures k in old(Model()) ==> newt.HasNext() && key(newt.Peek())==k
    ensures k !in old(Model()) ==> newt.Traversed()==Model().Keys

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt}+old(Iterators())

  method insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt:UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())[k:=v]

    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this  
    ensures newt.HasNext() && newt.Peek()==(k,v)

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    //points either to the inserted elemento or to the already existing one
 



  method erase(mid:UnorderedMapIterator) returns (next: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== map k | k in old(Model()) && k!=old(key(mid.Peek()))::old(Model())[k]
    ensures |Model()|==|old(Model())|-1

    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Traversed()==old(mid.Traversed()) 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
 
}

lemma prove(m:map<K,V>)
ensures forall k | k in m.Keys :: m[k] in m.Values
ensures forall p | p in m.Items:: key(p) in m && value(p)==m[key(p)]
ensures |m|==|m.Keys|
{}


method {:verify true} main(s:UnorderedMap)
modifies s, s.Repr()
requires s.Valid() && s.Empty()
requires forall x | x in s.Repr() :: allocated(x)
ensures s.Valid()
ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)
{
  assert s.Model()==map[];
 s.add(1,2);
 var x:= s.at(1);
 assert s.Model()==map[1:=2];
 s.add(1,3);
 x:=s.at(1);
 assert x==3;

 var z:=s.contains(1);
 assert z;
 z:=s.contains(7);
 assert !z;
 s.add(2,3); s.add(3,4); s.add(4,5);

 var it:=s.First();
 var cont:=0; 
  while (it.HasNext())
     decreases |s.Model()|
    //decreases |s.Model()-it.Model().0|
    //decreases s.Model()-it.Traversed()
     invariant s.Valid() 
     invariant it.Valid() && it in s.Iterators() && it.Parent()==s  
     invariant  forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
     invariant fresh(s.Repr()-old(s.Repr()))
     invariant forall x | x in s.Repr() :: allocated(x)
    {
     it:=s.erase(it);

    } 
   assert it.Traversed()==s.Model().Keys; 

   s.remove(1);
    z:=s.contains(1);
 assert !z;


}