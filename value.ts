import { Name, freshen } from "./common.ts";

////////////////////////////////////////////////////////////////////////////////
// Values and Spines

export type Value =
  | { tag: "VVar"; name: Name; spine: Spine }
  | { tag: "VAbs"; name: Name; func: (arg: Value) => Value }
  | { tag: "VPi"; name: Name; domain: VType; body: (dom: Value) => VType }
  | { tag: "VType" }
  | { tag: "VNat" }
  | { tag: "VZero" }
  | { tag: "VSuc"; n: Value }
  | { tag: "VEq"; A: VType; x: Value; y: Value }
  | { tag: "VRefl"; A: VType; x: Value };

export type VType = Value;

export type Spine =
  | { tag: "SNil" }
  | { tag: "SApp"; spine: Spine; arg: Value }
  | {
      tag: "SNatElim";
      P: VType;
      Pz: Value;
      Ps: Value;
      spine: Spine;
    }
  | {
      tag: "SEqElim";
      A: VType;
      x: Value;
      P: VType;
      Prefl: Value;
      y: Value;
      spine: Spine;
    };

export type Env = Record<Name, Value>;

////////////////////////////////////////////////////////////////////////////////
// Constructors

export const VVar = (name: Name, spine: Spine): Value => ({
  tag: "VVar",
  name,
  spine,
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

export const SNil: Spine = { tag: "SNil" };

export const SApp = (spine: Spine, arg: Value): Spine => ({
  tag: "SApp",
  spine,
  arg,
});

export const SNatElim = (
  P: VType,
  Pz: Value,
  Ps: Value,
  spine: Spine
): Spine => ({ tag: "SNatElim", P, Pz, Ps, spine });

export const SEqElim = (
  A: VType,
  x: Value,
  P: VType,
  Prefl: Value,
  y: Value,
  spine: Spine
): Spine => ({ tag: "SEqElim", A, x, P, Prefl, y, spine });

////////////////////////////////////////////////////////////////////////////////

export const VApp = (func: Value, arg: Value): Value => {
  switch (func.tag) {
    case "VVar":
      return VVar(func.name, SApp(func.spine, arg));
    case "VAbs":
      return func.func(arg);
  }
  throw new Error("Not a function");
};

export const VNatElim = (P: VType, Pz: Value, Ps: Value, n: Value): Value => {
  switch (n.tag) {
    case "VVar":
      return VVar(n.name, SNatElim(P, Pz, Ps, n.spine));
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
    case "VVar":
      return VVar(p.name, SEqElim(A, x, P, Prefl, y, p.spine));
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
  if (t.tag === "VVar" && u.tag === "VVar") {
    return t.name === u.name && convSpine(env, t.spine, u.spine);
  }
  if (t.tag === "VPi" && u.tag === "VPi") {
    const x = freshen(env, t.name);
    const v = VVar(x, SNil);
    return (
      conv(env, t.domain, u.domain) &&
      conv({ ...env, [x]: v }, t.body(v), u.body(v))
    );
  }
  if (t.tag === "VAbs" && u.tag === "VAbs") {
    const x = freshen(env, t.name);
    const v = VVar(x, SNil);
    return conv({ ...env, [x]: v }, t.func(v), u.func(v));
  }
  // Eta
  if (t.tag === "VAbs") {
    const x = freshen(env, t.name);
    const v = VVar(x, SNil);
    return conv({ ...env, [x]: v }, t.func(v), VApp(u, v));
  }
  if (u.tag === "VAbs") {
    const x = freshen(env, u.name);
    const v = VVar(x, SNil);
    return conv({ ...env, [x]: v }, VApp(t, v), u.func(v));
  }
  return false;
};

export const convSpine = (env: Env, r: Spine, s: Spine): boolean => {
  if (r.tag === "SNil" && s.tag === "SNil") {
    return true;
  }
  if (r.tag === "SApp" && s.tag === "SApp") {
    return convSpine(env, r.spine, s.spine) && conv(env, r.arg, s.arg);
  }
  if (r.tag === "SNatElim" && s.tag === "SNatElim") {
    return (
      convSpine(env, r.spine, s.spine) &&
      conv(env, r.P, s.P) &&
      conv(env, r.Pz, s.Pz) &&
      conv(env, r.Ps, s.Ps)
    );
  }
  if (r.tag === "SEqElim" && s.tag === "SEqElim") {
    return (
      convSpine(env, r.spine, s.spine) &&
      conv(env, r.A, s.A) &&
      conv(env, r.x, s.x) &&
      conv(env, r.P, s.P) &&
      conv(env, r.Prefl, s.Prefl) &&
      conv(env, r.y, s.y)
    );
  }
  return false;
};
