/*
 *This module defines an option type, which is a type that can either contain a value or be empty.
 *This is useful for representing optional values in a type-safe way.
 */
module Optional {

  datatype Option<T> = Some(v: T) | None {
    /**
      * Extract the value contained within this option.
      */
    function Unwrap() : T
      requires this.Some? {
      this.v
    }

    /**
      * Returns the contained value (if it exists) or the default value
      * (otherwise).
      */
    function UnwrapOr(default: T) : T {
      match this
      case Some(v) => v
      case none => default
    }
  }
}
