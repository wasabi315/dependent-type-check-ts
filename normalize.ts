import { freshen } from "./common.ts";
import {
  Term,
  Type,
  Var,
  App,
  Abs,
  Pi,
  Nat,
  Zero,
  Suc,
  NatElim,
  Eq,
  Refl,
  EqElim,
} from "./syntax.ts";
import {
  Env,
  Value,
  VEqElim,
  VNatElim,
  Spine,
  SNil,
  VApp,
  VAbs,
  VEq,
  VNat,
  VPi,
  VRefl,
  VSuc,
  VType,
  VVar,
  VZero,
} from "./value.ts";

////////////////////////////////////////////////////////////////////////////////
// Eval

export const evaluate = (env: Env, term: Term): Value => {
  switch (term.tag) {
    case "Var":
      return env[term.name];
    case "App":
      return VApp(evaluate(env, term.func), evaluate(env, term.arg));
    case "Abs":
      return VAbs(term.name, (arg) =>
        evaluate({ ...env, [term.name]: arg }, term.body)
      );
    case "Let": {
      const bound = evaluate(env, term.bound);
      return evaluate({ ...env, [term.name]: bound }, term.body);
    }
    case "Type":
      return VType;
    case "Pi":
      return VPi(term.name, evaluate(env, term.domain), (dom) =>
        evaluate({ ...env, [term.name]: dom }, term.body)
      );
    case "Nat":
      return VNat;
    case "Zero":
      return VZero;
    case "Suc":
      return VAbs("n", (n) => VSuc(n));
    case "NatElim":
      return VAbs("P", (P) =>
        VAbs("Pz", (Pz) =>
          VAbs("Ps", (Ps) => VAbs("n", (n) => VNatElim(P, Pz, Ps, n)))
        )
      );
    case "Eq":
      return VAbs("A", (A) => VAbs("x", (x) => VAbs("y", (y) => VEq(A, x, y))));
    case "Refl":
      return VAbs("A", (A) => VAbs("x", (x) => VRefl(A, x)));
    case "EqElim":
      return VAbs("A", (A) =>
        VAbs("x", (x) =>
          VAbs("P", (P) =>
            VAbs("Prefl", (Prefl) =>
              VAbs("y", (y) => VAbs("p", (p) => VEqElim(A, x, P, Prefl, y, p)))
            )
          )
        )
      );
  }
};

////////////////////////////////////////////////////////////////////////////////
// Quote

export const quote = (env: Env, value: Value): Term => {
  switch (value.tag) {
    case "VVar":
      return quoteSpine(env, Var(value.name), value.spine);
    case "VAbs": {
      const x = freshen(env, value.name);
      const v = VVar(x, SNil);
      return Abs(x, quote({ ...env, [value.name]: v }, value.func(v)));
    }
    case "VPi": {
      const x = freshen(env, value.name);
      const v = VVar(x, SNil);
      return Pi(
        [[x, quote(env, value.domain)]],
        quote({ ...env, [value.name]: v }, value.body(v))
      );
    }
    case "VType":
      return Type;
    case "VNat":
      return Nat;
    case "VZero":
      return Zero;
    case "VSuc":
      return App(Suc, quote(env, value.n));
    case "VEq":
      return App(
        Eq,
        quote(env, value.A),
        quote(env, value.x),
        quote(env, value.y)
      );
    case "VRefl":
      return App(Refl, quote(env, value.A), quote(env, value.x));
  }
};

export const quoteSpine = (env: Env, head: Term, spine: Spine): Term => {
  switch (spine.tag) {
    case "SNil":
      return head;
    case "SApp":
      return App(quoteSpine(env, head, spine.spine), quote(env, spine.arg));
    case "SNatElim":
      return App(
        NatElim,
        quote(env, spine.P),
        quote(env, spine.Pz),
        quote(env, spine.Ps),
        quoteSpine(env, head, spine.spine)
      );
    case "SEqElim":
      return App(
        EqElim,
        quote(env, spine.A),
        quote(env, spine.x),
        quote(env, spine.P),
        quote(env, spine.Prefl),
        quote(env, spine.y),
        quoteSpine(env, head, spine.spine)
      );
  }
};

////////////////////////////////////////////////////////////////////////////////
// Normalize

export const normalize = (env: Env, term: Term): Term =>
  quote(env, evaluate(env, term));
