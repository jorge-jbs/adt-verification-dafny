module {:options "-functionSyntax:4"} ThreadedLinkedTree.Model.Color {
  datatype Color = Red | Black

  function colorToString(c: Color): string
  {
    match c {
      case Black => "Black"
      case Red => "Red"
    }
  }

  function NegColor(c: Color): Color
  {
    match c {
      case Black => Red
      case Red => Black
    }
  }
}
