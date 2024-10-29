import { Name, freshen, Lazy, wrap, lazy } from "./common.ts";
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

////////////////////////////////////////////////////////////////////////////////
// Values and Spines

export type Value =
  | { tag: "VVar"; name: Name; spine: Spine }
  | { tag: "VAbs"; name: Name; func: (arg: Lazy<Value>) => Value }
  | { tag: "VPi"; name: Name; domain: VType; body: (dom: Lazy<Value>) => VType }
  | { tag: "VType" }
  | { tag: "VNat" }
  | { tag: "VZero" }
  | { tag: "VSuc"; n: Lazy<Value> }
  | { tag: "VEq"; A: Lazy<VType>; x: Lazy<Value>; y: Lazy<Value> }
  | { tag: "VRefl"; A: Lazy<VType>; x: Lazy<Value> };

export type VType = Value;

export type Spine =
  | { tag: "SNil" }
  | { tag: "SApp"; spine: Spine; arg: Lazy<Value> }
  | {
      tag: "SNatElim";
      P: Lazy<VType>;
      Pz: Lazy<Value>;
      Ps: Lazy<Value>;
      spine: Spine;
    }
  | {
      tag: "SEqElim";
      A: Lazy<VType>;
      x: Lazy<Value>;
      P: Lazy<VType>;
      Prefl: Lazy<Value>;
      y: Lazy<Value>;
      spine: Spine;
    };

export type Env = Record<Name, Lazy<Value>>;

////////////////////////////////////////////////////////////////////////////////
// Constructors

export const VVar = (name: Name, spine: Spine): Value => ({
  tag: "VVar",
  name,
  spine,
});

export const VAbs = (name: Name, func: (arg: Lazy<Value>) => Value): Value => ({
  tag: "VAbs",
  name,
  func,
});

export const VPi = (
  name: Name,
  domain: VType,
  body: (dom: Lazy<Value>) => VType
): VType => ({ tag: "VPi", name, domain, body });

export const VType: VType = { tag: "VType" };

export const VNat: Value = { tag: "VNat" };

export const VZero: Value = { tag: "VZero" };

export const VSuc = (n: Lazy<Value>): Value => ({ tag: "VSuc", n });

export const VEq = (A: Lazy<VType>, x: Lazy<Value>, y: Lazy<Value>): Value => ({
  tag: "VEq",
  A,
  x,
  y,
});

export const VRefl = (A: Lazy<VType>, x: Lazy<Value>): Value => ({
  tag: "VRefl",
  A,
  x,
});

export const SNil: Spine = { tag: "SNil" };

export const SApp = (spine: Spine, arg: Lazy<Value>): Spine => ({
  tag: "SApp",
  spine,
  arg,
});

export const SNatElim = (
  P: Lazy<VType>,
  Pz: Lazy<Value>,
  Ps: Lazy<Value>,
  spine: Spine
): Spine => ({ tag: "SNatElim", P, Pz, Ps, spine });

export const SEqElim = (
  A: Lazy<VType>,
  x: Lazy<Value>,
  P: Lazy<VType>,
  Prefl: Lazy<Value>,
  y: Lazy<Value>,
  spine: Spine
): Spine => ({ tag: "SEqElim", A, x, P, Prefl, y, spine });

////////////////////////////////////////////////////////////////////////////////
// Eval

export const evaluate = (env: Env, term: Term): Value => {
  switch (term.tag) {
    case "Var":
      return env[term.name].force();
    case "App":
      return VApp(
        evaluate(env, term.func),
        lazy(() => evaluate(env, term.arg))
      );
    case "Abs":
      return VAbs(term.name, (arg) =>
        evaluate({ ...env, [term.name]: arg }, term.body)
      );
    case "Let": {
      const bound = lazy(() => evaluate(env, term.bound));
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
          VAbs("Ps", (Ps) => VAbs("n", (n) => VNatElim(P, Pz, Ps, n.force())))
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
              VAbs("y", (y) =>
                VAbs("p", (p) => VEqElim(A, x, P, Prefl, y, p.force()))
              )
            )
          )
        )
      );
  }
};

export const VApp = (func: Value, arg: Lazy<Value>): Value => {
  switch (func.tag) {
    case "VVar":
      return VVar(func.name, SApp(func.spine, arg));
    case "VAbs":
      return func.func(arg);
  }
  throw new Error("Not a function");
};

export const VNatElim = (
  P: Lazy<VType>,
  Pz: Lazy<Value>,
  Ps: Lazy<Value>,
  n: Value
): Value => {
  switch (n.tag) {
    case "VVar":
      return VVar(n.name, SNatElim(P, Pz, Ps, n.spine));
    case "VZero":
      return Pz.force();
    case "VSuc":
      return VApp(
        VApp(Ps.force(), wrap(n)),
        lazy(() => VNatElim(P, Pz, Ps, n.n.force()))
      );
  }
  throw new Error("Not a number");
};

export const VEqElim = (
  A: Lazy<VType>,
  x: Lazy<Value>,
  P: Lazy<VType>,
  Prefl: Lazy<Value>,
  y: Lazy<Value>,
  p: Value
): Value => {
  switch (p.tag) {
    case "VVar":
      return VVar(p.name, SEqElim(A, x, P, Prefl, y, p.spine));
    case "VRefl":
      return Prefl.force();
  }
  throw new Error("Not an equality");
};

////////////////////////////////////////////////////////////////////////////////
// Quote

export const quote = (env: Env, value: Value): Term => {
  switch (value.tag) {
    case "VVar":
      return quoteSpine(env, Var(value.name), value.spine);
    case "VAbs": {
      const x = freshen(env, value.name);
      const v = wrap(VVar(x, SNil));
      return Abs(x, quote({ ...env, [value.name]: v }, value.func(v)));
    }
    case "VPi": {
      const x = freshen(env, value.name);
      const v = wrap(VVar(x, SNil));
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
      return App(Suc, quote(env, value.n.force()));
    case "VEq":
      return App(
        Eq,
        quote(env, value.A.force()),
        quote(env, value.x.force()),
        quote(env, value.y.force())
      );
    case "VRefl":
      return App(
        Refl,
        quote(env, value.A.force()),
        quote(env, value.x.force())
      );
  }
};

export const quoteSpine = (env: Env, head: Term, spine: Spine): Term => {
  switch (spine.tag) {
    case "SNil":
      return head;
    case "SApp":
      return App(
        quoteSpine(env, head, spine.spine),
        quote(env, spine.arg.force())
      );
    case "SNatElim":
      return App(
        NatElim,
        quote(env, spine.P.force()),
        quote(env, spine.Pz.force()),
        quote(env, spine.Ps.force()),
        quoteSpine(env, head, spine.spine)
      );
    case "SEqElim":
      return App(
        EqElim,
        quote(env, spine.A.force()),
        quote(env, spine.x.force()),
        quote(env, spine.P.force()),
        quote(env, spine.Prefl.force()),
        quote(env, spine.y.force()),
        quoteSpine(env, head, spine.spine)
      );
  }
};

////////////////////////////////////////////////////////////////////////////////
// Normalize

export const normalize = (env: Env, term: Term): Term =>
  quote(env, evaluate(env, term));

////////////////////////////////////////////////////////////////////////////////
// Beta-eta conversion

export const conv = (env: Env, t: Value, u: Value): boolean => {
  if (t.tag === "VType" && u.tag === "VType") {
    return true;
  }
  if (t.tag === "VNat" && u.tag === "VNat") {
    return true;
  }
  if (t.tag === "VZero" && u.tag === "VZero") {
    return true;
  }
  if (t.tag === "VSuc" && u.tag === "VSuc") {
    return conv(env, t.n.force(), u.n.force());
  }
  if (t.tag === "VEq" && u.tag === "VEq") {
    return (
      conv(env, t.A.force(), u.A.force()) &&
      conv(env, t.x.force(), u.x.force()) &&
      conv(env, t.y.force(), u.y.force())
    );
  }
  if (t.tag === "VRefl" && u.tag === "VRefl") {
    return (
      conv(env, t.A.force(), u.A.force()) && conv(env, t.x.force(), u.x.force())
    );
  }
  if (t.tag === "VVar" && u.tag === "VVar") {
    return t.name === u.name && convSpine(env, t.spine, u.spine);
  }
  if (t.tag === "VPi" && u.tag === "VPi") {
    const x = freshen(env, t.name);
    const v = wrap(VVar(x, SNil));
    return (
      conv(env, t.domain, u.domain) &&
      conv({ ...env, [x]: v }, t.body(v), u.body(v))
    );
  }
  if (t.tag === "VAbs" && u.tag === "VAbs") {
    const x = freshen(env, t.name);
    const v = wrap(VVar(x, SNil));
    return conv({ ...env, [x]: v }, t.func(v), u.func(v));
  }
  // Eta
  if (t.tag === "VAbs") {
    const x = freshen(env, t.name);
    const v = wrap(VVar(x, SNil));
    return conv({ ...env, [x]: v }, t.func(v), VApp(u, v));
  }
  if (u.tag === "VAbs") {
    const x = freshen(env, u.name);
    const v = wrap(VVar(x, SNil));
    return conv({ ...env, [x]: v }, VApp(t, v), u.func(v));
  }
  return false;
};

export const convSpine = (env: Env, r: Spine, s: Spine): boolean => {
  if (r.tag === "SNil" && s.tag === "SNil") {
    return true;
  }
  if (r.tag === "SApp" && s.tag === "SApp") {
    return (
      convSpine(env, r.spine, s.spine) &&
      conv(env, r.arg.force(), s.arg.force())
    );
  }
  if (r.tag === "SNatElim" && s.tag === "SNatElim") {
    return (
      convSpine(env, r.spine, s.spine) &&
      conv(env, r.P.force(), s.P.force()) &&
      conv(env, r.Pz.force(), s.Pz.force()) &&
      conv(env, r.Ps.force(), s.Ps.force())
    );
  }
  if (r.tag === "SEqElim" && s.tag === "SEqElim") {
    return (
      convSpine(env, r.spine, s.spine) &&
      conv(env, r.A.force(), s.A.force()) &&
      conv(env, r.x.force(), s.x.force()) &&
      conv(env, r.P.force(), s.P.force()) &&
      conv(env, r.Prefl.force(), s.Prefl.force()) &&
      conv(env, r.y.force(), s.y.force())
    );
  }
  return false;
};
