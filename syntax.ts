import { Name, NonEmpty } from "./common.ts";

////////////////////////////////////////////////////////////////////////////////
// Terms

export type Term =
  | { tag: "Var"; name_: Name } // x
  | { tag: "App"; func: Term; arg: Term } // t u
  | { tag: "Abs"; param: Name; body: Term } // λx. t
  | { tag: "Let"; name_: Name; type: Type; bound: Term; body: Term } // let x: a = t in u
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

export type AppTerm = Term & { (...args: Term[]): AppTerm };

export const toAppTerm = (term: Term): AppTerm => {
  const appTerm = (...args: Term[]): AppTerm => App(term, ...args);
  return Object.assign(appTerm, term);
};

export const Var = (name: Name): AppTerm =>
  toAppTerm({ tag: "Var", name_: name });

export const App = (func: Term, ...args: Term[]): AppTerm =>
  toAppTerm(args.reduce((func, arg) => ({ tag: "App", func, arg }), func));

export const Abs = (...paramsBody: [...NonEmpty<Name>, Term]): AppTerm => {
  const params = paramsBody.slice(0, -1) as NonEmpty<Name>;
  const body = paramsBody[paramsBody.length - 1] as Term;
  return toAppTerm(
    params.reduceRight((body, param) => ({ tag: "Abs", param, body }), body)
  );
};

export const Let = (
  ...bindingsBody: [...NonEmpty<[Name, Type, Term]>, Term]
): AppTerm => {
  const bindings = bindingsBody.slice(0, -1) as NonEmpty<[Name, Type, Term]>;
  const body = bindingsBody[bindingsBody.length - 1] as Term;
  return toAppTerm(
    bindings.reduceRight(
      (body, [name_, type, bound]) => ({
        tag: "Let",
        name_,
        type,
        bound,
        body,
      }),
      body
    )
  );
};

export const Type: AppTerm = toAppTerm({ tag: "Type" });

export const Pi = (
  ...domainsCodom: [...NonEmpty<[...NonEmpty<Name>, Type] | Type>, Type]
): AppTerm => {
  const domains = domainsCodom.slice(0, -1) as NonEmpty<
    [...NonEmpty<Name>, Type] | Type
  >;
  const codom = domainsCodom[domainsCodom.length - 1] as Type;
  return toAppTerm(
    domains.reduceRight<Type>((codom, domain) => {
      if (!(domain instanceof Array)) {
        return { tag: "Pi", param: "_", domain, codom };
      }
      const params = domain.slice(0, -1) as NonEmpty<Name>;
      const domainType = domain[domain.length - 1] as Type;
      return params.reduceRight(
        (codom, param) => ({ tag: "Pi", param, domain: domainType, codom }),
        codom
      );
    }, codom)
  );
};

export const Nat: AppTerm = toAppTerm({ tag: "Nat" });

export const Zero: AppTerm = toAppTerm({ tag: "Zero" });

export const Suc: AppTerm = toAppTerm({ tag: "Suc" });

export const Num = (n: number): AppTerm => {
  let term: AppTerm = Zero;
  for (let i = 0; i < n; i++) {
    term = Suc(term);
  }
  return term;
};

export const NatElim: AppTerm = toAppTerm({ tag: "NatElim" });

export const Eq: AppTerm = toAppTerm({ tag: "Eq" });

export const Refl: AppTerm = toAppTerm({ tag: "Refl" });

export const EqElim: AppTerm = toAppTerm({ tag: "EqElim" });

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
      return term.name_;
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
        `let ${term.name_}: ${pretty(ABS_LET_PREC, term.type)} =
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
