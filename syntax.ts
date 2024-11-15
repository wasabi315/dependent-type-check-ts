import { Name, NonEmpty } from "./common.ts";

////////////////////////////////////////////////////////////////////////////////
// Terms

export type WithPos<T> = T & { pos?: string };

export type Term = WithPos<
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
  | { tag: "EqElim" } // Standard eliminator for equality, also known as J
>;

export type Type = Term;

////////////////////////////////////////////////////////////////////////////////
// (Sugared) Constructors

export type AppTerm = Term & { (...args: NonEmpty<Term>): AppTerm };

export const toAppTerm = (term: Term): AppTerm =>
  Object.assign(App.bind(null, term), term);

const attachPos = <T extends Term>(term: T): T => {
  // Ref: https://stackoverflow.com/questions/2343343/how-can-i-determine-the-current-line-number-in-javascript
  const err = new Error();
  const stack = err!.stack!.split(/\r\n|\n/);
  const pos = stack[3].split("at ")[1];
  term.pos = pos;
  return term;
};

const splitLast = <T extends Array<unknown>, R>(arr: [...T, R]): [T, R] => {
  const init = arr.slice(0, -1) as T;
  const last = arr.at(-1) as R;
  return [init, last];
};

export const Var = (name: Name): AppTerm =>
  attachPos(toAppTerm({ tag: "Var", name_: name }));

export const App = (func: Term, ...args: NonEmpty<Term>): AppTerm =>
  attachPos(
    toAppTerm(args.reduce((func, arg) => ({ tag: "App", func, arg }), func))
  );

export const Abs = (...paramsBody: [...NonEmpty<Name>, Term]): AppTerm => {
  const [params, body] = splitLast(paramsBody);
  return attachPos(
    toAppTerm(
      params.reduceRight((body, param) => ({ tag: "Abs", param, body }), body)
    )
  );
};

export type Definition = [Name, Type, Term];

export const Let = (
  ...bindingsBody: [...NonEmpty<Definition>, Term]
): AppTerm => {
  const [bindings, body] = splitLast(bindingsBody);
  return attachPos(
    toAppTerm(
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
    )
  );
};

export const Type: () => AppTerm = () => attachPos(toAppTerm({ tag: "Type" }));

export const Pi = (
  ...domainsCodom: [...NonEmpty<[...NonEmpty<Name>, Type] | Type>, Type]
): AppTerm => {
  const [domains, codom] = splitLast(domainsCodom);
  return attachPos(
    toAppTerm(
      domains.reduceRight<Type>((codom, domain) => {
        if (!(domain instanceof Array)) {
          return { tag: "Pi", param: "_", domain, codom };
        }
        const [params, domainType] = splitLast(domain);
        return params.reduceRight(
          (codom, param) => ({ tag: "Pi", param, domain: domainType, codom }),
          codom
        );
      }, codom)
    )
  );
};

export const Nat: () => AppTerm = () => attachPos(toAppTerm({ tag: "Nat" }));

export const Zero: () => AppTerm = () => attachPos(toAppTerm({ tag: "Zero" }));

export const Suc: () => AppTerm = () => attachPos(toAppTerm({ tag: "Suc" }));

export const Num = (n: number): AppTerm => {
  let term: Term = { tag: "Zero" };
  for (let i = 0; i < n; i++) {
    term = { tag: "App", func: { tag: "Suc" }, arg: term };
  }
  return attachPos(toAppTerm(term));
};

export const NatElim: () => AppTerm = () =>
  attachPos(toAppTerm({ tag: "NatElim" }));

export const Eq: () => AppTerm = () => attachPos(toAppTerm({ tag: "Eq" }));

export const Refl: () => AppTerm = () => attachPos(toAppTerm({ tag: "Refl" }));

export const EqElim: () => AppTerm = () =>
  attachPos(toAppTerm({ tag: "EqElim" }));

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
