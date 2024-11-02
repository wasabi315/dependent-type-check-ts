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
  Eq,
  Type,
  EqElim,
} from "./syntax.ts";
import { normalize } from "./normalize.ts";
import { check } from "./typecheck.ts";
import { VNat } from "./value.ts";

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
  [
    "cong",
    Pi(
      ["A", Type],
      ["B", Type],
      ["f", Pi(Var("A"), Var("B"))],
      ["x", Var("A")],
      ["y", Var("A")],
      App(Eq, Var("A"), Var("x"), Var("y")),
      App(Eq, Var("B"), App(Var("f"), Var("x")), App(Var("f"), Var("y")))
    ),
    Abs(
      "A",
      "B",
      "f",
      "x",
      App(
        EqElim,
        Var("A"),
        Var("x"),
        Abs(
          "y",
          "_",
          App(Eq, Var("B"), App(Var("f"), Var("x")), App(Var("f"), Var("y")))
        ),
        App(Refl, Var("B"), App(Var("f"), Var("x")))
      )
    ),
  ],
  [
    "plus-identity-right",
    Pi(["n", Nat], App(Eq, Nat, App(Var("plus"), Var("n"), Zero), Var("n"))),
    App(
      NatElim,
      Abs("n", App(Eq, Nat, App(Var("plus"), Var("n"), Zero), Var("n"))),
      App(Refl, Nat, Zero),
      Abs(
        "n",
        App(
          Var("cong"),
          Nat,
          Nat,
          Suc,
          App(Var("plus"), Var("n"), Zero),
          Var("n")
        )
      )
    ),
  ],
  App(Var("plus"), Num(2), App(Var("mult"), Num(8), Num(5)))
);

console.log("-- pretty --\n");
console.log(pretty(0, ex));
console.log("\n-- normalized --\n");
console.log(pretty(0, normalize({}, ex)));
console.log("\n-- typecheck --\n");
check({}, {}, ex, VNat);
console.log("OK");
