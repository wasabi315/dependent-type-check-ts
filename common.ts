// Names

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

// Lazy evaluation

export type Lazy<T> = {
  readonly value: T;
};

export const wrap = <T>(value: T): Lazy<T> => ({ value });

export const lazy = <T>(f: () => T): Lazy<T> =>
  ({
    get value() {
      const x = f();
      delete this.value;
      this.value = x;
      return x;
    },
  } satisfies { value?: T } as Lazy<T>);

// Utils

export type NonEmpty<T> = [T, ...T[]];
