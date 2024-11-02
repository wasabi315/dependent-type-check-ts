import { Name, NonEmpty } from "./common.ts";

////////////////////////////////////////////////////////////////////////////////
// Terms

export type Term =
  | { tag: "Var"; name: Name } // x
  | { tag: "App"; func: Term; arg: Term } // t u
  | { tag: "Abs"; param: Name; body: Term } // λx. t
  | { tag: "Let"; name: Name; type: Type; bound: Term; body: Term } // let x: a = t in u
  | { tag: "Type" } // Type
  | { tag: "Pi"; param: Name; domain: Type; codom: Type } // (x : A) → B
  | { tag: "Nat" } // Natural number
  | { tag: "Zero" } // 0
  | { tag: "Suc" } // 1 + _
  | { tag: "NatElim" } // Standard eliminator for natural numbers
  | { tag: "Eq" } // Equality
  | { tag: "Refl" } // Reflextivity
  | { tag: "EqElim" }; // Standard eliminator for equality, also known as J

export type Type = Term;

////////////////////////////////////////////////////////////////////////////////
// (Sugared) Constructors

export const Var = (name: Name): Term => ({ tag: "Var", name });

export const App = (func: Term, ...args: Term[]): Term =>
  args.reduce((func, arg) => ({ tag: "App", func, arg }), func);

export const Abs = (...paramsBody: [...NonEmpty<Name>, Term]): Term => {
  const params = paramsBody.slice(0, -1) as NonEmpty<Name>;
  const body = paramsBody[paramsBody.length - 1] as Term;
  return params.reduceRight(
    (body, param) => ({ tag: "Abs", param, body }),
    body
  );
};

export const Let = (
  ...bindingsBody: [...NonEmpty<[Name, Type, Term]>, Term]
): Term => {
  const bindings = bindingsBody.slice(0, -1) as NonEmpty<[Name, Type, Term]>;
  const body = bindingsBody[bindingsBody.length - 1] as Term;
  return bindings.reduceRight(
    (body, [name, type, bound]) => ({ tag: "Let", name, type, bound, body }),
    body
  );
};

export const Type: Type = { tag: "Type" };

export const Pi = (
  ...domainsCodom: [...NonEmpty<[Name, Type] | Type>, Type]
): Type => {
  const domains = domainsCodom.slice(0, -1) as NonEmpty<[Name, Type] | Type>;
  const codom = domainsCodom[domainsCodom.length - 1] as Type;
  return domains.reduceRight<Type>(
    (codom, domain) =>
      domain instanceof Array
        ? { tag: "Pi", param: domain[0], domain: domain[1], codom }
        : { tag: "Pi", param: "_", domain, codom },
    codom
  );
};

export const Nat: Type = { tag: "Nat" };

export const Zero: Term = { tag: "Zero" };

export const Suc: Term = { tag: "Suc" };

export const Num = (n: number): Term => {
  let term: Term = Zero;
  for (let i = 0; i < n; i++) {
    term = App(Suc, term);
  }
  return term;
};

export const NatElim: Term = { tag: "NatElim" };

export const Eq: Type = { tag: "Eq" };

export const Refl: Term = { tag: "Refl" };

export const EqElim: Term = { tag: "EqElim" };

////////////////////////////////////////////////////////////////////////////////
// Pretty-printing

const parensIf = (cond: boolean, str: string): string =>
  cond ? `(${str})` : str;

const APP_PREC = 2;
const PI_PREC = 1;
const ABS_LET_PREC = 0;

export const pretty = (prec: number, term: Term): string => {
  const prettyAbs = (firstParam: Name, body: Term): string => {
    const params = [firstParam];
    while (body.tag === "Abs") {
      params.push(body.param);
      body = body.body;
    }
    return `λ ${params.join(" ")}. ${pretty(ABS_LET_PREC, body)}`;
  };

  const prettyPi = (firstDomain: [Name, Type], body: Type): string => {
    const domains = [firstDomain];
    while (body.tag === "Pi" && body.param !== "_") {
      domains.push([body.param, body.domain]);
      body = body.codom;
    }
    return `${domains
      .map(([name, domain]) => `(${name}: ${pretty(PI_PREC, domain)})`)
      .join(" ")} → ${pretty(PI_PREC, body)}`;
  };

  const prettySuc = (prec: number, body: Term): string => {
    let n = 1;
    while (body.tag === "App" && body.func.tag === "Suc") {
      n++;
      body = body.arg;
    }
    if (body.tag === "Zero") {
      return n.toString();
    }
    return parensIf(prec > APP_PREC, `${n}+ ${pretty(APP_PREC, body)}`);
  };

  switch (term.tag) {
    case "Var":
      return term.name;
    case "App":
      if (term.func.tag === "Suc") {
        return prettySuc(prec, term.arg);
      }
      return parensIf(
        prec > APP_PREC,
        `${pretty(APP_PREC, term.func)} ${pretty(APP_PREC + 1, term.arg)}`
      );
    case "Abs":
      return parensIf(prec > ABS_LET_PREC, prettyAbs(term.param, term.body));
    case "Let":
      return parensIf(
        prec > ABS_LET_PREC,
        `let ${term.name}: ${pretty(ABS_LET_PREC, term.type)} =
  ${pretty(ABS_LET_PREC, term.bound)}
in

${pretty(ABS_LET_PREC, term.body)}`
      );
    case "Type":
      return "Type";
    case "Pi":
      if (term.param === "_") {
        return parensIf(
          prec > PI_PREC,
          `${pretty(APP_PREC, term.domain)} → ${pretty(PI_PREC, term.codom)}`
        );
      }
      return parensIf(
        prec > PI_PREC,
        prettyPi([term.param, term.domain], term.codom)
      );
    case "Nat":
      return "Nat";
    case "Zero":
      return "0";
    case "Suc":
      return "suc";
    case "NatElim":
      return "natElim";
    case "Eq":
      return "Eq";
    case "Refl":
      return "refl";
    case "EqElim":
      return "eqElim";
  }
};
