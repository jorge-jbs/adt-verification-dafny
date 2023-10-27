module Printer {
    ghost function natToString(n: nat): string
    {
      match n {
        case 0 => "0"
        case 1 => "1"
        case 2 => "2"
        case 3 => "3"
        case 4 => "4"
        case 5 => "5"
        case 6 => "6"
        case 7 => "7"
        case 8 => "8"
        case 9 => "9"
        case _ => natToString(n / 10) + natToString(n % 10)
      }
    }

    ghost function intToString(n: int): string
    {
      if n < 0 then
        "-" + natToString(-n)
      else
        "" + natToString(n)
    }
  }