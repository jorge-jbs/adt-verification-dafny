module Color {
  datatype Color = Red | Black

  function method NegColor(c: Color): Color
  {
    match c {
      case Black => Red
      case Red => Black
    }
  }
}
