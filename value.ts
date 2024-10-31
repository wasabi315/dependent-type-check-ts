import { Name, freshen } from "./common.ts";

////////////////////////////////////////////////////////////////////////////////
// Values and Neutrals

export type Value =
  | { tag: "VNeutral"; neutral: Neutral }
  | { tag: "VAbs"; name: Name; func: (arg: Value) => Value }
  | { tag: "VPi"; name: Name; domain: VType; body: (dom: Value) => VType }
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

export type Env = Record<Name, Value>;

////////////////////////////////////////////////////////////////////////////////
// Constructors

export const VNeutral = (neutral: Neutral): Value => ({
  tag: "VNeutral",
  neutral,
});

export const VAbs = (name: Name, func: (arg: Value) => Value): Value => ({
  tag: "VAbs",
  name,
  func,
});

export const VPi = (
  name: Name,
  domain: VType,
  body: (dom: Value) => VType
): VType => ({ tag: "VPi", name, domain, body });

export const VArr = (domain: VType, codomain: VType): VType =>
  VPi("_", domain, (_) => codomain);

export const VType: VType = { tag: "VType" };

export const VNat: Value = { tag: "VNat" };

export const VZero: Value = { tag: "VZero" };

export const VSuc = (n: Value): Value => ({ tag: "VSuc", n });

export const VNum = (n: number): Value => {
  let value: Value = VZero;
  for (let i = 0; i < n; i++) {
    value = VSuc(value);
  }
  return value;
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
      return VApp(VApp(Ps, n), VNatElim(P, Pz, Ps, n.n));
  }
  throw new Error("Not a number");
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
    return conv(env, t.n, u.n);
  }
  if (t.tag === "VEq" && u.tag === "VEq") {
    return conv(env, t.A, u.A) && conv(env, t.x, u.x) && conv(env, t.y, u.y);
  }
  if (t.tag === "VRefl" && u.tag === "VRefl") {
    return conv(env, t.A, u.A) && conv(env, t.x, u.x);
  }
  if (t.tag === "VNeutral" && u.tag === "VNeutral") {
    return convNeutral(env, t.neutral, u.neutral);
  }
  if (t.tag === "VPi" && u.tag === "VPi") {
    const x = freshen(env, t.name);
    const v = VVar(x);
    return (
      conv(env, t.domain, u.domain) &&
      conv({ ...env, [x]: v }, t.body(v), u.body(v))
    );
  }
  if (t.tag === "VAbs" && u.tag === "VAbs") {
    const x = freshen(env, t.name);
    const v = VVar(x);
    return conv({ ...env, [x]: v }, t.func(v), u.func(v));
  }
  // Eta
  if (t.tag === "VAbs") {
    const x = freshen(env, t.name);
    const v = VVar(x);
    return conv({ ...env, [x]: v }, t.func(v), VApp(u, v));
  }
  if (u.tag === "VAbs") {
    const x = freshen(env, u.name);
    const v = VVar(x);
    return conv({ ...env, [x]: v }, VApp(t, v), u.func(v));
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
