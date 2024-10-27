import {
  Var,
  App,
  Abs,
  Nat,
  Let,
  Pi,
  Zero,
  Suc,
  NatElim,
  Num,
  pretty,
} from "./syntax.ts";
import { normalize } from "./normalize.ts";

////////////////////////////////////////////////////////////////////////////////

const ex = Let(
  [
    [
      "plus",
      Pi([[["_", "_"], Nat]], Nat),
      Abs(
        ["m", "n"],
        App(NatElim, Abs("_", Nat), Var("n"), Abs("_", Suc), Var("m"))
      ),
    ],
    [
      "mult",
      Pi([[["_", "_"], Nat]], Nat),
      Abs(
        ["m", "n"],
        App(
          NatElim,
          Abs("_", Nat),
          Zero,
          Abs("_", App(Var("plus"), Var("n"))),
          Var("m")
        )
      ),
    ],
  ],
  App(Var("plus"), Num(2), App(Var("mult"), Num(8), Num(5)))
);

console.log("-- pretty --\n");
console.log(pretty(0, ex));
console.log("\n-- normalized --\n");
console.log(pretty(0, normalize({}, ex)));
