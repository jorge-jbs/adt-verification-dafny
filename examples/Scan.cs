using System;

namespace _module {
    partial class __default {
        public static void Scan(out System.Numerics.BigInteger x) {
            x = 0;
            int n = Console.Read();
            while (n == ' ' || n == '\t' || n == '\n' || n == '\r' || n == -1)
                n = Console.Read();
            bool pos = true;
            if (n == '-') {
                pos = false;
                n = Console.Read();
            } else if (n == '+') {
                pos = true;
                n = Console.Read();
            }
            while (n >= '0' && n <= '9') {
                x = x * 10 + n - '0';
                n = Console.Read();
            }
            if (!pos)
                x *= -1;
        }
    }
}
