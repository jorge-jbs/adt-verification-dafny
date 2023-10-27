module  Int {
  
  ghost function Abs(x: int): int
  {
    if x < 0 then
      -x
    else
      x
  }

  ghost function Max(x: int, y: int): int
  {
    if x < y then
      y
    else
      x
  }

}
  

