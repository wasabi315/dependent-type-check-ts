import { Name, freshen, Lazy, wrap, lazy, TypeCheckError } from "./common.ts";
import {
  Env,
  VApp,
  VArr,
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

export type Ctx = Record<Name, Lazy<VType>>;

export const check = (env: Env, ctx: Ctx, term: Term, type: VType): void => {
  try {
    switch (term.tag) {
      case "Let": {
        check(env, ctx, term.type, VType);
        const vType = evaluate(env, term.type);
        check(env, ctx, term.bound, vType);
        const vBound = lazy(() => evaluate(env, term.bound));
        return check(
          { ...env, [term.name_]: vBound },
          { ...ctx, [term.name_]: wrap(vType) },
          term.body,
          type
        );
      }
      case "Abs": {
        if (type.tag !== "VPi") {
          break;
        }
        const param = freshen(env, term.param);
        const vParam = VVar(param);
        return check(
          { ...env, [term.param]: wrap(vParam) },
          { ...ctx, [term.param]: wrap(type.domain) },
          term.body,
          type.codom(vParam)
        );
      }
    }

    const ty = infer(env, ctx, term);
    if (!conv(env, ty, type)) {
      throw new TypeCheckError(
        `Type mismatch:
    When checking ${pretty(0, term)}
    Expected: ${pretty(0, quote(env, type))}
    Actual: ${pretty(0, quote(env, ty))}`
      );
    }
  } catch (e) {
    if (e instanceof TypeCheckError && !e.pos) {
      e.pos = term.pos;
    }
    throw e;
  }
};

export const infer = (env: Env, ctx: Ctx, term: Term): VType => {
  switch (term.tag) {
    case "Var":
      if (!ctx[term.name_]) {
        throw new TypeCheckError(`Unknown variable "${term.name_}"`);
      }
      return ctx[term.name_].value;
    case "App": {
      const funcType = infer(env, ctx, term.func);
      if (funcType.tag !== "VPi") {
        throw new TypeCheckError(`Expected a function`);
      }
      check(env, ctx, term.arg, funcType.domain);
      const argValue = evaluate(env, term.arg);
      return funcType.codom(argValue);
    }
    case "Abs":
      throw new TypeCheckError(`Can't infer type of abstraction`);
    case "Let": {
      check(env, ctx, term.type, VType);
      const vType = evaluate(env, term.type);
      check(env, ctx, term.bound, vType);
      const vBound = lazy(() => evaluate(env, term.bound));
      return infer(
        { ...env, [term.name_]: vBound },
        { ...ctx, [term.name_]: wrap(vType) },
        term.body
      );
    }
    case "Type":
      return VType;
    case "Pi": {
      check(env, ctx, term.domain, VType);
      const vParam = wrap(VVar(term.param));
      const vDomain = lazy(() => evaluate(env, term.domain));
      check(
        { ...env, [term.param]: vParam },
        { ...ctx, [term.param]: vDomain },
        term.codom,
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

export const sucType = VArr(VNat, VNat);

// (P : Nat -> Type) -> P 0 -> ((n : Nat) -> P n -> P (suc n)) -> (n : Nat) -> P n
export const natElimType = VPi("P", VArr(VNat, VType), (P) =>
  VArr(
    VApp(P, VZero),
    VArr(
      VPi("n", VNat, (n) => VArr(VApp(P, n), VApp(P, VSuc(n)))),
      VPi("n", VNat, (n) => VApp(P, n))
    )
  )
);

// (A : Type) -> A -> A -> Type
export const eqType = VPi("A", VType, (A) => VArr(A, VArr(A, VType)));

// (A : Type) (x : A) -> Eq A x x
export const reflType = VPi("A", VType, (A) =>
  VPi("x", A, (x) => VEq(A, x, x))
);

// (A : Type) (x : A) (P : (y : A) -> Eq A x y -> Type) -> P x (refl A x) -> (y : A) (p : Eq A x y) -> P y p
export const eqElimType = VPi("A", VType, (A) =>
  VPi("x", A, (x) =>
    VPi(
      "P",
      VPi("y", A, (y) => VArr(VEq(A, x, y), VType)),
      (P) =>
        VArr(
          VApp(VApp(P, x), VRefl(A, x)),
          VPi("y", A, (y) => VPi("p", VEq(A, x, y), (p) => VApp(VApp(P, y), p)))
        )
    )
  )
);
