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
// Ref: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Functions/get#smart_self-overwriting_lazy_getters

export type Lazy<T> = {
  readonly value: T;
};

export const wrap = <T>(value: T): Lazy<T> => ({ value });

export const lazy = <T>(f: () => T): Lazy<T> =>
  ({
    get value() {
      delete this.value;
      this.value = f();
      return this.value;
    },
  } satisfies { value?: T } as Lazy<T>);

// Utils

export type NonEmpty<T> = [T, ...T[]];

// Error

export class TypeCheckError extends Error {
  constructor(message: string, public pos?: string) {
    super(message);
    Object.setPrototypeOf(this, TypeCheckError.prototype);
  }
}
