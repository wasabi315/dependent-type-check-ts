import { Name, freshen } from "./common.ts";
import {
  Env,
  SNil,
  VApp,
  VEq,
  VNat,
  VPi,
  VRefl,
  VSuc,
  VType,
  VVar,
  VZero,
  conv,
} from "./value.ts";
import { evaluate, quote } from "./normalize.ts";
import { Term, pretty } from "./syntax.ts";

////////////////////////////////////////////////////////////////////////////////

export type Ctx = Record<Name, VType>;

export const check = (env: Env, ctx: Ctx, term: Term, type: VType): void => {
  switch (term.tag) {
    case "Let": {
      check(env, ctx, term.type, VType);
      const vt = evaluate(env, term.type);
      check(env, ctx, term.bound, vt);
      const v = evaluate(env, term.bound);
      return check(
        { ...env, [term.name]: v },
        { ...ctx, [term.name]: vt },
        term.body,
        type
      );
    }
    case "Abs": {
      if (type.tag === "VPi") {
        const x = freshen(env, term.name);
        const v = VVar(x, SNil);
        return check(
          { ...env, [term.name]: v },
          { ...ctx, [term.name]: type.domain },
          term.body,
          type.body(v)
        );
      }
    }
  }
  const ty = infer(env, ctx, term);
  if (!conv(env, ty, type)) {
    throw new Error(
      `type mismatch: ${pretty(0, quote(env, ty))} != ${pretty(
        0,
        quote(env, type)
      )} when checking ${pretty(0, term)}`
    );
  }
};

export const infer = (env: Env, ctx: Ctx, term: Term): VType => {
  switch (term.tag) {
    case "Var":
      return ctx[term.name];
    case "App": {
      const funcType = infer(env, ctx, term.func);
      if (funcType.tag !== "VPi") {
        throw new Error(`expected a function`);
      }
      check(env, ctx, term.arg, funcType.domain);
      const argValue = evaluate(env, term.arg);
      return funcType.body(argValue);
    }
    case "Abs":
      throw new Error(`can't infer type of abstraction`);
    case "Let": {
      check(env, ctx, term.type, VType);
      const vt = evaluate(env, term.type);
      check(env, ctx, term.bound, vt);
      const v = evaluate(env, term.bound);
      return infer(
        { ...env, [term.name]: v },
        { ...ctx, [term.name]: vt },
        term.body
      );
    }
    case "Type":
      return VType;
    case "Pi": {
      check(env, ctx, term.domain, VType);
      const v = VVar(term.name, SNil);
      const domainValue = evaluate(env, term.domain);
      check(
        { ...env, [term.name]: v },
        { ...ctx, [term.name]: domainValue },
        term.body,
        VType
      );
      return VType;
    }
    case "Nat":
      return VType;
    case "Zero":
      return VNat;
    case "Suc":
      return sucType;
    case "NatElim":
      return natElimType;
    case "Eq":
      return eqType;
    case "Refl":
      return reflType;
    case "EqElim":
      return eqElimType;
  }
};

export const sucType = VPi("_", VNat, (_) => VNat);

// (P : Nat -> Type) -> P 0 -> ((n : Nat) -> P n -> P (suc n)) -> (n : Nat) -> P n
export const natElimType = VPi(
  "P",
  VPi("_", VNat, (_) => VType),
  (P) =>
    VPi("Pz", VApp(P, VZero), (_) =>
      VPi(
        "Ps",
        VPi("n", VNat, (n) => VPi("_", VApp(P, n), (_) => VApp(P, VSuc(n)))),
        (_) => VPi("n", VNat, (n) => VApp(P, n))
      )
    )
);

// (A : Type) -> A -> A -> Type
export const eqType = VPi("A", VType, (A) =>
  VPi("_", A, (_) => VPi("_", A, (_) => VType))
);

// (A : Type) (x : A) -> Eq A x x
export const reflType = VPi("A", VType, (A) =>
  VPi("x", A, (x) => VEq(A, x, x))
);

// (A : Type) (x : A) (P : (y : A) -> Eq A x y -> Type) (Prefl : P x (refl A x)) (y : A) (p : Eq A x y) -> P y p
export const eqElimType = VPi("A", VType, (A) =>
  VPi("x", A, (x) =>
    VPi(
      "P",
      VPi("y", A, (y) => VPi("_", VEq(A, x, y), (_) => VType)),
      (P) =>
        VPi("_", VApp(VApp(P, x), VRefl(A, x)), (_) =>
          VPi("y", A, (y) => VPi("p", VEq(A, x, y), (p) => VApp(VApp(P, y), p)))
        )
    )
  )
);
