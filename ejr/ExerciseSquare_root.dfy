method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n < (r+1)*(r+1)
{
    r:=0;
	while (r+1)*(r+1) <=n
	 invariant r>=0 && r*r <=n
	 //invariant r>=0
	 //decreases n-r
	  decreases n - r*r
	 // decreases n-(r+1)*(r+1)
	 //decreases r //not correct
	 //decreases r*r-n //not correct
	 {
	   r:=r+1;
	 }


}


method mroot2(n:int) returns (r:int) // Cost O(n)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r+1) * (r+1)
{
  r := n;
	while n < r*r
	  invariant r >= 0 && n < (r+1)*(r+1)  //write the invariant
	  decreases r*r - n //write the bound
	{
	  r := r-1;
	}
}

method mroot3(n:int) returns (r:int) //Cost O(log n)
  requires n >= 0
  ensures r >= 0 && r*r <= n < (r+1)*(r+1)
{
  var y:int;
  var h:int;
  r := 0;
  y := n+1;
  //Search in interval [0,n+1)
  while (y != r+1)
    invariant 0 <= r < y <= n+1
    invariant r*r <= n < y * y
    decreases y - r - 1 // write the bound
  {
    h := (r+y) / 2;
    if (h*h <= n) {
      r := h;
    } else {
      y := h;
    }
  }
}
