module Color {
  datatype Color = Red | Black

  function method colorToString(c: Color): string
  {
    match c {
      case Black => "Black"
      case Red => "Red"
    }
  }

  function method NegColor(c: Color): Color
  {
    match c {
      case Black => Red
      case Red => Black
    }
  }
}
