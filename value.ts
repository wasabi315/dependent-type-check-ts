import { Name, freshen, Lazy, wrap } from "./common.ts";

////////////////////////////////////////////////////////////////////////////////
// Values and Neutrals

export type Value =
  | { tag: "VNeutral"; neutral: Neutral }
  | { tag: "VAbs"; param: Name; func: (arg: Value) => Value }
  | {
      tag: "VPi";
      param: Name;
      domain: VType;
      codom: (arg: VType) => VType;
    }
  | { tag: "VType" }
  | { tag: "VNat" }
  | { tag: "VZero" }
  | { tag: "VSuc"; n: Value }
  | { tag: "VEq"; A: VType; x: Value; y: Value }
  | { tag: "VRefl"; A: VType; x: Value };

export type VType = Value;

export type Neutral =
  | { tag: "NVar"; name: Name }
  | { tag: "NApp"; func: Neutral; arg: Value }
  | {
      tag: "NNatElim";
      P: VType;
      Pz: Value;
      Ps: Value;
      n: Neutral;
    }
  | {
      tag: "NEqElim";
      A: VType;
      x: Value;
      P: VType;
      Prefl: Value;
      y: Value;
      p: Neutral;
    };

export type Env = Record<Name, Lazy<Value>>;

////////////////////////////////////////////////////////////////////////////////
// Constructors

export const VNeutral = (neutral: Neutral): Value => ({
  tag: "VNeutral",
  neutral,
});

export const VAbs = (param: Name, func: (arg: Value) => Value): Value => ({
  tag: "VAbs",
  param,
  func,
});

export const VPi = (
  param: Name,
  domain: VType,
  codom: (arg: Value) => VType
): VType => ({ tag: "VPi", param, domain, codom });

export const VArr = (domain: VType, codom: VType): VType =>
  VPi("_", domain, (_) => codom);

export const VType: VType = { tag: "VType" };

export const VNat: Value = { tag: "VNat" };

export const VZero: Value = { tag: "VZero" };

export const VSuc = (n: Value): Value => ({ tag: "VSuc", n });

export const VNum = (n: number): Value => {
  let v: Value = VZero;
  for (let i = 0; i < n; i++) {
    v = VSuc(v);
  }
  return v;
};

export const VEq = (A: VType, x: Value, y: Value): Value => ({
  tag: "VEq",
  A,
  x,
  y,
});

export const VRefl = (A: VType, x: Value): Value => ({
  tag: "VRefl",
  A,
  x,
});

export const NVar = (name: Name): Neutral => ({ tag: "NVar", name });

export const NApp = (func: Neutral, arg: Value): Neutral => ({
  tag: "NApp",
  func,
  arg,
});

export const NNatElim = (
  P: VType,
  Pz: Value,
  Ps: Value,
  n: Neutral
): Neutral => ({ tag: "NNatElim", P, Pz, Ps, n });

export const NEqElim = (
  A: VType,
  x: Value,
  P: VType,
  Prefl: Value,
  y: Value,
  p: Neutral
): Neutral => ({ tag: "NEqElim", A, x, P, Prefl, y, p });

////////////////////////////////////////////////////////////////////////////////

export const VVar = (name: Name): Value => VNeutral(NVar(name));

export const VApp = (func: Value, arg: Value): Value => {
  switch (func.tag) {
    case "VNeutral":
      return VNeutral(NApp(func.neutral, arg));
    case "VAbs":
      return func.func(arg);
  }
  throw new Error("Not a function");
};

export const VNatElim = (P: VType, Pz: Value, Ps: Value, n: Value): Value => {
  switch (n.tag) {
    case "VNeutral":
      return VNeutral(NNatElim(P, Pz, Ps, n.neutral));
    case "VZero":
      return Pz;
    case "VSuc":
      return VApp(VApp(Ps, n.n), VNatElim(P, Pz, Ps, n.n));
  }
  throw new Error("Not a natural number");
};

export const VEqElim = (
  A: VType,
  x: Value,
  P: VType,
  Prefl: Value,
  y: Value,
  p: Value
): Value => {
  switch (p.tag) {
    case "VNeutral":
      return VNeutral(NEqElim(A, x, P, Prefl, y, p.neutral));
    case "VRefl":
      return Prefl;
  }
  throw new Error("Not an equality");
};

export const VSucAbs = VAbs("n", (n) => VSuc(n));

export const VNatElimAbs = VAbs("P", (P) =>
  VAbs("Pz", (Pz) =>
    VAbs("Ps", (Ps) => VAbs("n", (n) => VNatElim(P, Pz, Ps, n)))
  )
);

export const VEqAbs = VAbs("A", (A) =>
  VAbs("x", (x) => VAbs("y", (y) => VEq(A, x, y)))
);

export const VReflAbs = VAbs("A", (A) => VAbs("x", (x) => VRefl(A, x)));

export const VEqElimAbs = VAbs("A", (A) =>
  VAbs("x", (x) =>
    VAbs("P", (P) =>
      VAbs("Prefl", (Prefl) =>
        VAbs("y", (y) => VAbs("p", (p) => VEqElim(A, x, P, Prefl, y, p)))
      )
    )
  )
);

////////////////////////////////////////////////////////////////////////////////
// Beta-eta conversion

export const conv = (env: Env, term1: Value, term2: Value): boolean => {
  if (term1.tag === "VType" && term2.tag === "VType") {
    return true;
  }
  if (term1.tag === "VNat" && term2.tag === "VNat") {
    return true;
  }
  if (term1.tag === "VZero" && term2.tag === "VZero") {
    return true;
  }
  if (term1.tag === "VSuc" && term2.tag === "VSuc") {
    return conv(env, term1.n, term2.n);
  }
  if (term1.tag === "VEq" && term2.tag === "VEq") {
    return (
      conv(env, term1.A, term2.A) &&
      conv(env, term1.x, term2.x) &&
      conv(env, term1.y, term2.y)
    );
  }
  if (term1.tag === "VRefl" && term2.tag === "VRefl") {
    return conv(env, term1.A, term2.A) && conv(env, term1.x, term2.x);
  }
  if (term1.tag === "VNeutral" && term2.tag === "VNeutral") {
    return convNeutral(env, term1.neutral, term2.neutral);
  }
  if (term1.tag === "VPi" && term2.tag === "VPi") {
    const param = freshen(env, term1.param);
    const vParam = VVar(param);
    return (
      conv(env, term1.domain, term2.domain) &&
      conv(
        { ...env, [param]: wrap(vParam) },
        term1.codom(vParam),
        term2.codom(vParam)
      )
    );
  }
  if (term1.tag === "VAbs" && term2.tag === "VAbs") {
    const param = freshen(env, term1.param);
    const vParam = VVar(param);
    return conv(
      { ...env, [param]: wrap(vParam) },
      term1.func(vParam),
      term2.func(vParam)
    );
  }
  // Eta
  if (term1.tag === "VAbs") {
    const param = freshen(env, term1.param);
    const vParam = VVar(param);
    return conv(
      { ...env, [param]: wrap(vParam) },
      term1.func(vParam),
      VApp(term2, vParam)
    );
  }
  if (term2.tag === "VAbs") {
    const param = freshen(env, term2.param);
    const vParam = VVar(param);
    return conv(
      { ...env, [param]: wrap(vParam) },
      VApp(term1, vParam),
      term2.func(vParam)
    );
  }
  return false;
};

export const convNeutral = (env: Env, m: Neutral, n: Neutral): boolean => {
  if (m.tag === "NVar" && n.tag === "NVar") {
    return m.name === n.name;
  }
  if (m.tag === "NApp" && n.tag === "NApp") {
    return convNeutral(env, m.func, n.func) && conv(env, m.arg, n.arg);
  }
  if (m.tag === "NNatElim" && n.tag === "NNatElim") {
    return (
      convNeutral(env, m.n, n.n) &&
      conv(env, m.P, n.P) &&
      conv(env, m.Pz, n.Pz) &&
      conv(env, m.Ps, n.Ps)
    );
  }
  if (m.tag === "NEqElim" && n.tag === "NEqElim") {
    return (
      convNeutral(env, m.p, n.p) &&
      conv(env, m.A, n.A) &&
      conv(env, m.x, n.x) &&
      conv(env, m.P, n.P) &&
      conv(env, m.Prefl, n.Prefl) &&
      conv(env, m.y, n.y)
    );
  }
  return false;
};
