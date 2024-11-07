import { freshen, lazy, wrap } from "./common.ts";
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
  Neutral,
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
      return env[term.name_].value;
    case "App":
      return VApp(evaluate(env, term.func), evaluate(env, term.arg));
    case "Abs":
      return VAbs(term.param, (arg) =>
        evaluate({ ...env, [term.param]: wrap(arg) }, term.body)
      );
    case "Let": {
      const bound = lazy(() => evaluate(env, term.bound));
      return evaluate({ ...env, [term.name_]: bound }, term.body);
    }
    case "Type":
      return VType;
    case "Pi": {
      const domain = evaluate(env, term.domain);
      return VPi(term.param, domain, (dom) =>
        evaluate({ ...env, [term.param]: wrap(dom) }, term.codom)
      );
    }
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
    case "VNeutral":
      return quoteNeutral(env, value.neutral);
    case "VAbs": {
      const param = freshen(env, value.param);
      const vParam = VVar(param);
      return Abs(
        param,
        quote({ ...env, [value.param]: wrap(vParam) }, value.func(vParam))
      );
    }
    case "VPi": {
      const param = freshen(env, value.param);
      const vParam = VVar(param);
      return Pi(
        [param, quote(env, value.domain)],
        quote({ ...env, [value.param]: wrap(vParam) }, value.codom(vParam))
      );
    }
    case "VType":
      return Type();
    case "VNat":
      return Nat();
    case "VZero":
      return Zero();
    case "VSuc":
      return Suc()(quote(env, value.n));
    case "VEq":
      return Eq()(
        quote(env, value.A),
        quote(env, value.x),
        quote(env, value.y)
      );
    case "VRefl":
      return Refl()(quote(env, value.A), quote(env, value.x));
  }
};

export const quoteNeutral = (env: Env, neutral: Neutral): Term => {
  switch (neutral.tag) {
    case "NVar":
      return Var(neutral.name);
    case "NApp":
      return App(quoteNeutral(env, neutral.func), quote(env, neutral.arg));
    case "NNatElim":
      return NatElim()(
        quote(env, neutral.P),
        quote(env, neutral.Pz),
        quote(env, neutral.Ps),
        quoteNeutral(env, neutral.n)
      );
    case "NEqElim":
      return EqElim()(
        quote(env, neutral.A),
        quote(env, neutral.x),
        quote(env, neutral.P),
        quote(env, neutral.Prefl),
        quote(env, neutral.y),
        quoteNeutral(env, neutral.p)
      );
  }
};

////////////////////////////////////////////////////////////////////////////////
// Normalize

export const normalize = (env: Env, term: Term): Term =>
  quote(env, evaluate(env, term));
