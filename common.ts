export type Name = string;

export const freshen = (dict: Record<Name, unknown>, name: Name): Name => {
  if (name === "_") {
    return name;
  }
  while (dict[name]) {
    name += "'";
  }
  return name;
};

// Lazy values

export type Lazy<T> = { force(): T };

export const wrap = <T>(value: T): Lazy<T> => ({ force: () => value });
export const lazy = <T>(f: () => T): Lazy<T> => ({
  force() {
    const value = f();
    this.force = () => value;
    return value;
  },
});

// Utils

export type NonEmpty<T> = [T, ...T[]];

export type OneOrMore<T> = T | NonEmpty<T>;
