export type Name = string;

export const freshen = (env: Record<Name, unknown>, name: Name): Name => {
  if (name === "_") {
    return name;
  }
  while (env[name]) {
    name += "'";
  }
  return name;
};

// Utils

export type NonEmpty<T> = [T, ...T[]];

export type OneOrMore<T> = T | NonEmpty<T>;
