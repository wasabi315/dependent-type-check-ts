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
  Refl,
} from "./syntax.ts";
import { normalize, evaluate } from "./normalize.ts";
import { check } from "./typecheck.ts";
import { VNat, VEq, VNum } from "./value.ts";

////////////////////////////////////////////////////////////////////////////////

const ex = Let(
  [
    "plus",
    Pi(Nat, Nat, Nat),
    Abs(
      "m",
      "n",
      App(NatElim, Abs("_", Nat), Var("n"), Abs("_", Suc), Var("m"))
    ),
  ],
  [
    "mult",
    Pi(Nat, Nat, Nat),
    Abs(
      "m",
      "n",
      App(
        NatElim,
        Abs("_", Nat),
        Zero,
        Abs("_", App(Var("plus"), Var("n"))),
        Var("m")
      )
    ),
  ],
  App(Var("plus"), Num(2), App(Var("mult"), Num(8), Num(5)))
);

console.log("-- pretty --\n");
console.log(pretty(0, ex));
console.log("\n-- normalized --\n");
console.log(pretty(0, normalize({}, ex)));

check({}, {}, App(Refl, Nat, Num(42)), VEq(VNat, evaluate({}, ex), VNum(42)));
