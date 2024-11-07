import { TypeCheckError } from "./common.ts";
import {
  Var,
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
    Pi(Nat(), Nat(), Nat()),
    Abs(
      "m",
      "n",
      NatElim()(Abs("_", Nat()), Var("n"), Abs("_", Suc()), Var("m"))
    ),
  ],
  [
    "mult",
    Pi(Nat(), Nat(), Nat()),
    Abs(
      "m",
      "n",
      NatElim()(
        Abs("_", Nat()),
        Zero(),
        Abs("_", Var("plus")(Var("n"))),
        Var("m")
      )
    ),
  ],
  [
    "cong",
    Pi(
      ["A", "B", Type()],
      ["f", Pi(Var("A"), Var("B"))],
      ["x", "y", Var("A")],
      Eq()(Var("A"), Var("x"), Var("y")),
      Eq()(Var("B"), Var("f")(Var("x")), Var("f")(Var("y")))
    ),
    Abs(
      "A",
      "B",
      "f",
      "x",
      EqElim()(
        Var("A"),
        Var("x"),
        Abs("y", "_", Eq()(Var("B"), Var("f")(Var("x")), Var("f")(Var("y")))),
        Refl()(Var("B"), Var("f")(Var("x")))
      )
    ),
  ],
  [
    "plus-identity-right",
    Pi(["n", Nat()], Eq()(Nat(), Var("plus")(Var("n"), Zero()), Var("n"))),
    NatElim()(
      Abs("n", Eq()(Nat(), Var("plus")(Var("n"), Zero()), Var("n"))),
      Refl()(Nat(), Zero()),
      Abs(
        "n",
        Var("cong")(
          Nat(),
          Nat(),
          Suc(),
          Var("plus")(Var("n"), Zero()),
          Var("n")
        )
      )
    ),
  ],
  Var("plus")(Num(2), Var("mult")(Num(8), Num(5)))
);

function main() {
  console.log("-- pretty --\n");
  console.log(pretty(0, ex));
  console.log("\n-- typecheck --\n");
  try {
    check({}, {}, ex, VNat);
    console.log("OK");
  } catch (e) {
    if (e instanceof TypeCheckError) {
      console.error(`ERR at ${e.pos}`);
      console.error(e.message);
      return;
    }
    throw e;
  }
  console.log("\n-- normalize --\n");
  console.log(pretty(0, normalize({}, ex)));
}

main();
