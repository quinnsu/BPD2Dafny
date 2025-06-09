// Dafny program engine.dfy compiled into JavaScript
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

const BigNumber = require('bignumber.js');
BigNumber.config({ MODULO_MODE: BigNumber.EUCLID })
let _dafny = (function() {
  let $module = {};
  $module.areEqual = function(a, b) {
    if (typeof a === 'string' && b instanceof _dafny.Seq) {
      // Seq.equals(string) works as expected,
      // and the catch-all else block handles that direction.
      // But the opposite direction doesn't work; handle it here.
      return b.equals(a);
    } else if (typeof a === 'number' && BigNumber.isBigNumber(b)) {
      // This conditional would be correct even without the `typeof a` part,
      // but in most cases it's probably faster to short-circuit on a `typeof`
      // than to call `isBigNumber`. (But it remains to properly test this.)
      return b.isEqualTo(a);
    } else if (typeof a !== 'object' || a === null || b === null) {
      return a === b;
    } else if (BigNumber.isBigNumber(a)) {
      return a.isEqualTo(b);
    } else if (a._tname !== undefined || (Array.isArray(a) && a.constructor.name == "Array")) {
      return a === b;  // pointer equality
    } else {
      return a.equals(b);  // value-type equality
    }
  }
  $module.toString = function(a) {
    if (a === null) {
      return "null";
    } else if (typeof a === "number") {
      return a.toFixed();
    } else if (BigNumber.isBigNumber(a)) {
      return a.toFixed();
    } else if (a._tname !== undefined) {
      return a._tname;
    } else {
      return a.toString();
    }
  }
  $module.escapeCharacter = function(cp) {
    let s = String.fromCodePoint(cp.value)
    switch (s) {
      case '\n': return "\\n";
      case '\r': return "\\r";
      case '\t': return "\\t";
      case '\0': return "\\0";
      case '\'': return "\\'";
      case '\"': return "\\\"";
      case '\\': return "\\\\";
      default: return s;
    };
  }
  $module.NewObject = function() {
    return { _tname: "object" };
  }
  $module.InstanceOfTrait = function(obj, trait) {
    return obj._parentTraits !== undefined && obj._parentTraits().includes(trait);
  }
  $module.Rtd_bool = class {
    static get Default() { return false; }
  }
  $module.Rtd_char = class {
    static get Default() { return 'D'; }  // See CharType.DefaultValue in Dafny source code
  }
  $module.Rtd_codepoint = class {
    static get Default() { return new _dafny.CodePoint('D'.codePointAt(0)); }
  }
  $module.Rtd_int = class {
    static get Default() { return BigNumber(0); }
  }
  $module.Rtd_number = class {
    static get Default() { return 0; }
  }
  $module.Rtd_ref = class {
    static get Default() { return null; }
  }
  $module.Rtd_array = class {
    static get Default() { return []; }
  }
  $module.ZERO = new BigNumber(0);
  $module.ONE = new BigNumber(1);
  $module.NUMBER_LIMIT = new BigNumber(0x20).multipliedBy(0x1000000000000);  // 2^53
  $module.Tuple = class Tuple extends Array {
    constructor(...elems) {
      super(...elems);
    }
    toString() {
      return "(" + arrayElementsToString(this) + ")";
    }
    equals(other) {
      if (this === other) {
        return true;
      }
      for (let i = 0; i < this.length; i++) {
        if (!_dafny.areEqual(this[i], other[i])) {
          return false;
        }
      }
      return true;
    }
    static Default(...values) {
      return Tuple.of(...values);
    }
    static Rtd(...rtdArgs) {
      return {
        Default: Tuple.from(rtdArgs, rtd => rtd.Default)
      };
    }
  }
  $module.Set = class Set extends Array {
    constructor() {
      super();
    }
    static get Default() {
      return Set.Empty;
    }
    toString() {
      return "{" + arrayElementsToString(this) + "}";
    }
    static get Empty() {
      if (this._empty === undefined) {
        this._empty = new Set();
      }
      return this._empty;
    }
    static fromElements(...elmts) {
      let s = new Set();
      for (let k of elmts) {
        s.add(k);
      }
      return s;
    }
    contains(k) {
      for (let i = 0; i < this.length; i++) {
        if (_dafny.areEqual(this[i], k)) {
          return true;
        }
      }
      return false;
    }
    add(k) {  // mutates the Set; use only during construction
      if (!this.contains(k)) {
        this.push(k);
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.length !== other.length) {
        return false;
      }
      for (let e of this) {
        if (!other.contains(e)) {
          return false;
        }
      }
      return true;
    }
    get Elements() {
      return this;
    }
    Union(that) {
      if (this.length === 0) {
        return that;
      } else if (that.length === 0) {
        return this;
      } else {
        let s = Set.of(...this);
        for (let k of that) {
          s.add(k);
        }
        return s;
      }
    }
    Intersect(that) {
      if (this.length === 0) {
        return this;
      } else if (that.length === 0) {
        return that;
      } else {
        let s = new Set();
        for (let k of this) {
          if (that.contains(k)) {
            s.push(k);
          }
        }
        return s;
      }
    }
    Difference(that) {
      if (this.length == 0 || that.length == 0) {
        return this;
      } else {
        let s = new Set();
        for (let k of this) {
          if (!that.contains(k)) {
            s.push(k);
          }
        }
        return s;
      }
    }
    IsDisjointFrom(that) {
      for (let k of this) {
        if (that.contains(k)) {
          return false;
        }
      }
      return true;
    }
    IsSubsetOf(that) {
      if (that.length < this.length) {
        return false;
      }
      for (let k of this) {
        if (!that.contains(k)) {
          return false;
        }
      }
      return true;
    }
    IsProperSubsetOf(that) {
      if (that.length <= this.length) {
        return false;
      }
      for (let k of this) {
        if (!that.contains(k)) {
          return false;
        }
      }
      return true;
    }
    get AllSubsets() {
      return this.AllSubsets_();
    }
    *AllSubsets_() {
      // Start by putting all set elements into a list, but don't include null
      let elmts = Array.of(...this);
      let n = elmts.length;
      let which = new Array(n);
      which.fill(false);
      let a = [];
      while (true) {
        yield Set.of(...a);
        // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "a".
        let i = 0;
        for (; i < n && which[i]; i++) {
          which[i] = false;
          // remove elmts[i] from a
          for (let j = 0; j < a.length; j++) {
            if (_dafny.areEqual(a[j], elmts[i])) {
              // move the last element of a into slot j
              a[j] = a[-1];
              a.pop();
              break;
            }
          }
        }
        if (i === n) {
          // we have cycled through all the subsets
          break;
        }
        which[i] = true;
        a.push(elmts[i]);
      }
    }
  }
  $module.MultiSet = class MultiSet extends Array {
    constructor() {
      super();
    }
    static get Default() {
      return MultiSet.Empty;
    }
    toString() {
      let s = "multiset{";
      let sep = "";
      for (let e of this) {
        let [k, n] = e;
        let ks = _dafny.toString(k);
        while (!n.isZero()) {
          n = n.minus(1);
          s += sep + ks;
          sep = ", ";
        }
      }
      s += "}";
      return s;
    }
    static get Empty() {
      if (this._empty === undefined) {
        this._empty = new MultiSet();
      }
      return this._empty;
    }
    static fromElements(...elmts) {
      let s = new MultiSet();
      for (let e of elmts) {
        s.add(e, _dafny.ONE);
      }
      return s;
    }
    static FromArray(arr) {
      let s = new MultiSet();
      for (let e of arr) {
        s.add(e, _dafny.ONE);
      }
      return s;
    }
    cardinality() {
      let c = _dafny.ZERO;
      for (let e of this) {
        let [k, n] = e;
        c = c.plus(n);
      }
      return c;
    }
    clone() {
      let s = new MultiSet();
      for (let e of this) {
        let [k, n] = e;
        s.push([k, n]);  // make sure to create a new array [k, n] here
      }
      return s;
    }
    findIndex(k) {
      for (let i = 0; i < this.length; i++) {
        if (_dafny.areEqual(this[i][0], k)) {
          return i;
        }
      }
      return this.length;
    }
    get(k) {
      let i = this.findIndex(k);
      if (i === this.length) {
        return _dafny.ZERO;
      } else {
        return this[i][1];
      }
    }
    contains(k) {
      return !this.get(k).isZero();
    }
    add(k, n) {
      let i = this.findIndex(k);
      if (i === this.length) {
        this.push([k, n]);
      } else {
        let m = this[i][1];
        this[i] = [k, m.plus(n)];
      }
    }
    update(k, n) {
      let i = this.findIndex(k);
      if (i < this.length && this[i][1].isEqualTo(n)) {
        return this;
      } else if (i === this.length && n.isZero()) {
        return this;
      } else if (i === this.length) {
        let m = this.slice();
        m.push([k, n]);
        return m;
      } else {
        let m = this.slice();
        m[i] = [k, n];
        return m;
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      }
      for (let e of this) {
        let [k, n] = e;
        let m = other.get(k);
        if (!n.isEqualTo(m)) {
          return false;
        }
      }
      return this.cardinality().isEqualTo(other.cardinality());
    }
    get Elements() {
      return this.Elements_();
    }
    *Elements_() {
      for (let i = 0; i < this.length; i++) {
        let [k, n] = this[i];
        while (!n.isZero()) {
          yield k;
          n = n.minus(1);
        }
      }
    }
    get UniqueElements() {
      return this.UniqueElements_();
    }
    *UniqueElements_() {
      for (let e of this) {
        let [k, n] = e;
        if (!n.isZero()) {
          yield k;
        }
      }
    }
    Union(that) {
      if (this.length === 0) {
        return that;
      } else if (that.length === 0) {
        return this;
      } else {
        let s = this.clone();
        for (let e of that) {
          let [k, n] = e;
          s.add(k, n);
        }
        return s;
      }
    }
    Intersect(that) {
      if (this.length === 0) {
        return this;
      } else if (that.length === 0) {
        return that;
      } else {
        let s = new MultiSet();
        for (let e of this) {
          let [k, n] = e;
          let m = that.get(k);
          if (!m.isZero()) {
            s.push([k, m.isLessThan(n) ? m : n]);
          }
        }
        return s;
      }
    }
    Difference(that) {
      if (this.length === 0 || that.length === 0) {
        return this;
      } else {
        let s = new MultiSet();
        for (let e of this) {
          let [k, n] = e;
          let d = n.minus(that.get(k));
          if (d.isGreaterThan(0)) {
            s.push([k, d]);
          }
        }
        return s;
      }
    }
    IsDisjointFrom(that) {
      let intersection = this.Intersect(that);
      return intersection.cardinality().isZero();
    }
    IsSubsetOf(that) {
      for (let e of this) {
        let [k, n] = e;
        let m = that.get(k);
        if (!n.isLessThanOrEqualTo(m)) {
          return false;
        }
      }
      return true;
    }
    IsProperSubsetOf(that) {
      return this.IsSubsetOf(that) && this.cardinality().isLessThan(that.cardinality());
    }
  }
  $module.CodePoint = class CodePoint {
    constructor(value) {
      this.value = value
    }
    equals(other) {
      if (this === other) {
        return true;
      }
      return this.value === other.value
    }
    isLessThan(other) {
      return this.value < other.value
    }
    isLessThanOrEqual(other) {
      return this.value <= other.value
    }
    toString() {
      return "'" + $module.escapeCharacter(this) + "'";
    }
    static isCodePoint(i) {
      return (
        (_dafny.ZERO.isLessThanOrEqualTo(i) && i.isLessThan(new BigNumber(0xD800))) ||
        (new BigNumber(0xE000).isLessThanOrEqualTo(i) && i.isLessThan(new BigNumber(0x11_0000))))
    }
  }
  $module.Seq = class Seq extends Array {
    constructor(...elems) {
      super(...elems);
    }
    static get Default() {
      return Seq.of();
    }
    static Create(n, init) {
      return Seq.from({length: n}, (_, i) => init(new BigNumber(i)));
    }
    static UnicodeFromString(s) {
      return new Seq(...([...s].map(c => new _dafny.CodePoint(c.codePointAt(0)))))
    }
    toString() {
      return "[" + arrayElementsToString(this) + "]";
    }
    toVerbatimString(asLiteral) {
      if (asLiteral) {
        return '"' + this.map(c => _dafny.escapeCharacter(c)).join("") + '"';
      } else {
        return this.map(c => String.fromCodePoint(c.value)).join("");
      }
    }
    static update(s, i, v) {
      if (typeof s === "string") {
        let p = s.slice(0, i);
        let q = s.slice(i.toNumber() + 1);
        return p.concat(v, q);
      } else {
        let t = s.slice();
        t[i] = v;
        return t;
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.length !== other.length) {
        return false;
      }
      for (let i = 0; i < this.length; i++) {
        if (!_dafny.areEqual(this[i], other[i])) {
          return false;
        }
      }
      return true;
    }
    static contains(s, k) {
      if (typeof s === "string") {
        return s.includes(k);
      } else {
        for (let x of s) {
          if (_dafny.areEqual(x, k)) {
            return true;
          }
        }
        return false;
      }
    }
    get Elements() {
      return this;
    }
    get UniqueElements() {
      return _dafny.Set.fromElements(...this);
    }
    static Concat(a, b) {
      if (typeof a === "string" || typeof b === "string") {
        // string concatenation, so make sure both operands are strings before concatenating
        if (typeof a !== "string") {
          // a must be a Seq
          a = a.join("");
        }
        if (typeof b !== "string") {
          // b must be a Seq
          b = b.join("");
        }
        return a + b;
      } else {
        // ordinary concatenation
        let r = Seq.of(...a);
        r.push(...b);
        return r;
      }
    }
    static JoinIfPossible(x) {
      try { return x.join(""); } catch(_error) { return x; }
    }
    static IsPrefixOf(a, b) {
      if (b.length < a.length) {
        return false;
      }
      for (let i = 0; i < a.length; i++) {
        if (!_dafny.areEqual(a[i], b[i])) {
          return false;
        }
      }
      return true;
    }
    static IsProperPrefixOf(a, b) {
      if (b.length <= a.length) {
        return false;
      }
      for (let i = 0; i < a.length; i++) {
        if (!_dafny.areEqual(a[i], b[i])) {
          return false;
        }
      }
      return true;
    }
  }
  $module.Map = class Map extends Array {
    constructor() {
      super();
    }
    static get Default() {
      return Map.of();
    }
    toString() {
      return "map[" + this.map(maplet => _dafny.toString(maplet[0]) + " := " + _dafny.toString(maplet[1])).join(", ") + "]";
    }
    static get Empty() {
      if (this._empty === undefined) {
        this._empty = new Map();
      }
      return this._empty;
    }
    findIndex(k) {
      for (let i = 0; i < this.length; i++) {
        if (_dafny.areEqual(this[i][0], k)) {
          return i;
        }
      }
      return this.length;
    }
    get(k) {
      let i = this.findIndex(k);
      if (i === this.length) {
        return undefined;
      } else {
        return this[i][1];
      }
    }
    contains(k) {
      return this.findIndex(k) < this.length;
    }
    update(k, v) {
      let m = this.slice();
      m.updateUnsafe(k, v);
      return m;
    }
    // Similar to update, but make the modification in-place.
    // Meant to be used in the map constructor.
    updateUnsafe(k, v) {
      let m = this;
      let i = m.findIndex(k);
      m[i] = [k, v];
      return m;
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.length !== other.length) {
        return false;
      }
      for (let e of this) {
        let [k, v] = e;
        let w = other.get(k);
        if (w === undefined || !_dafny.areEqual(v, w)) {
          return false;
        }
      }
      return true;
    }
    get Keys() {
      let s = new _dafny.Set();
      for (let e of this) {
        let [k, v] = e;
        s.push(k);
      }
      return s;
    }
    get Values() {
      let s = new _dafny.Set();
      for (let e of this) {
        let [k, v] = e;
        s.add(v);
      }
      return s;
    }
    get Items() {
      let s = new _dafny.Set();
      for (let e of this) {
        let [k, v] = e;
        s.push(_dafny.Tuple.of(k, v));
      }
      return s;
    }
    Merge(that) {
      let m = that.slice();
      for (let e of this) {
        let [k, v] = e;
        let i = m.findIndex(k);
        if (i == m.length) {
          m[i] = [k, v];
        }
      }
      return m;
    }
    Subtract(keys) {
      if (this.length === 0 || keys.length === 0) {
        return this;
      }
      let m = new Map();
      for (let e of this) {
        let [k, v] = e;
        if (!keys.contains(k)) {
          m[m.length] = e;
        }
      }
      return m;
    }
  }
  $module.newArray = function(initValue, ...dims) {
    return { dims: dims, elmts: buildArray(initValue, ...dims) };
  }
  $module.BigOrdinal = class BigOrdinal {
    static get Default() {
      return _dafny.ZERO;
    }
    static IsLimit(ord) {
      return ord.isZero();
    }
    static IsSucc(ord) {
      return ord.isGreaterThan(0);
    }
    static Offset(ord) {
      return ord;
    }
    static IsNat(ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }
  $module.BigRational = class BigRational {
    static get ZERO() {
      if (this._zero === undefined) {
        this._zero = new BigRational(_dafny.ZERO);
      }
      return this._zero;
    }
    constructor (n, d) {
      // requires d === undefined || 1 <= d
      this.num = n;
      this.den = d === undefined ? _dafny.ONE : d;
      // invariant 1 <= den || (num == 0 && den == 0)
    }
    static get Default() {
      return _dafny.BigRational.ZERO;
    }
    // We need to deal with the special case `num == 0 && den == 0`, because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore `den` when `num` is 0.
    toString() {
      if (this.num.isZero() || this.den.isEqualTo(1)) {
        return this.num.toFixed() + ".0";
      }
      let answer = this.dividesAPowerOf10(this.den);
      if (answer !== undefined) {
        let n = this.num.multipliedBy(answer[0]);
        let log10 = answer[1];
        let sign, digits;
        if (this.num.isLessThan(0)) {
          sign = "-"; digits = n.negated().toFixed();
        } else {
          sign = ""; digits = n.toFixed();
        }
        if (log10 < digits.length) {
          let digitCount = digits.length - log10;
          return sign + digits.slice(0, digitCount) + "." + digits.slice(digitCount);
        } else {
          return sign + "0." + "0".repeat(log10 - digits.length) + digits;
        }
      } else {
        return "(" + this.num.toFixed() + ".0 / " + this.den.toFixed() + ".0)";
      }
    }
    isPowerOf10(x) {
      if (x.isZero()) {
        return undefined;
      }
      let log10 = 0;
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.isEqualTo(1)) {
          return log10;
        } else if (x.mod(10).isZero()) {
          log10++;
          x = x.dividedToIntegerBy(10);
        } else {
          return undefined;
        }
      }
    }
    dividesAPowerOf10(i) {
      let factor = _dafny.ONE;
      let log10 = 0;
      if (i.isLessThanOrEqualTo(_dafny.ZERO)) {
        return undefined;
      }

      // invariant: 1 <= i && i * 10^log10 == factor * old(i)
      while (i.mod(10).isZero()) {
        i = i.dividedToIntegerBy(10);
       log10++;
      }

      while (i.mod(5).isZero()) {
        i = i.dividedToIntegerBy(5);
        factor = factor.multipliedBy(2);
        log10++;
      }
      while (i.mod(2).isZero()) {
        i = i.dividedToIntegerBy(2);
        factor = factor.multipliedBy(5);
        log10++;
      }

      if (i.isEqualTo(_dafny.ONE)) {
        return [factor, log10];
      } else {
        return undefined;
      }
    }
    toBigNumber() {
      if (this.num.isZero() || this.den.isEqualTo(1)) {
        return this.num;
      } else if (this.num.isGreaterThan(0)) {
        return this.num.dividedToIntegerBy(this.den);
      } else {
        return this.num.minus(this.den).plus(1).dividedToIntegerBy(this.den);
      }
    }
    isInteger() {
      return this.equals(new _dafny.BigRational(this.toBigNumber(), _dafny.ONE));
    }
    // Returns values such that aa/dd == a and bb/dd == b.
    normalize(b) {
      let a = this;
      let aa, bb, dd;
      if (a.num.isZero()) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.isZero()) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        let gcd = BigNumberGcd(a.den, b.den);
        let xx = a.den.dividedToIntegerBy(gcd);
        let yy = b.den.dividedToIntegerBy(gcd);
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num.multipliedBy(yy);
        bb = b.num.multipliedBy(xx);
        dd = a.den.multipliedBy(yy);
      }
      return [aa, bb, dd];
    }
    compareTo(that) {
      // simple things first
      let asign = this.num.isZero() ? 0 : this.num.isLessThan(0) ? -1 : 1;
      let bsign = that.num.isZero() ? 0 : that.num.isLessThan(0) ? -1 : 1;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      let [aa, bb, dd] = this.normalize(that);
      if (aa.isLessThan(bb)) {
        return -1;
      } else if (aa.isEqualTo(bb)){
        return 0;
      } else {
        return 1;
      }
    }
    equals(that) {
      return this.compareTo(that) === 0;
    }
    isLessThan(that) {
      return this.compareTo(that) < 0;
    }
    isAtMost(that) {
      return this.compareTo(that) <= 0;
    }
    plus(b) {
      let [aa, bb, dd] = this.normalize(b);
      return new BigRational(aa.plus(bb), dd);
    }
    minus(b) {
      let [aa, bb, dd] = this.normalize(b);
      return new BigRational(aa.minus(bb), dd);
    }
    negated() {
      return new BigRational(this.num.negated(), this.den);
    }
    multipliedBy(b) {
      return new BigRational(this.num.multipliedBy(b.num), this.den.multipliedBy(b.den));
    }
    dividedBy(b) {
      let a = this;
      // Compute the reciprocal of b
      let bReciprocal;
      if (b.num.isGreaterThan(0)) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(b.den.negated(), b.num.negated());
      }
      return a.multipliedBy(bReciprocal);
    }
  }
  $module.EuclideanDivisionNumber = function(a, b) {
    if (0 <= a) {
      if (0 <= b) {
        // +a +b: a/b
        return Math.floor(a / b);
      } else {
        // +a -b: -(a/(-b))
        return -Math.floor(a / -b);
      }
    } else {
      if (0 <= b) {
        // -a +b: -((-a-1)/b) - 1
        return -Math.floor((-a-1) / b) - 1;
      } else {
        // -a -b: ((-a-1)/(-b)) + 1
        return Math.floor((-a-1) / -b) + 1;
      }
    }
  }
  $module.EuclideanDivision = function(a, b) {
    if (a.isGreaterThanOrEqualTo(0)) {
      if (b.isGreaterThanOrEqualTo(0)) {
        // +a +b: a/b
        return a.dividedToIntegerBy(b);
      } else {
        // +a -b: -(a/(-b))
        return a.dividedToIntegerBy(b.negated()).negated();
      }
    } else {
      if (b.isGreaterThanOrEqualTo(0)) {
        // -a +b: -((-a-1)/b) - 1
        return a.negated().minus(1).dividedToIntegerBy(b).negated().minus(1);
      } else {
        // -a -b: ((-a-1)/(-b)) + 1
        return a.negated().minus(1).dividedToIntegerBy(b.negated()).plus(1);
      }
    }
  }
  $module.EuclideanModuloNumber = function(a, b) {
    let bp = Math.abs(b);
    if (0 <= a) {
      // +a: a % bp
      return a % bp;
    } else {
      // c = ((-a) % bp)
      // -a: bp - c if c > 0
      // -a: 0 if c == 0
      let c = (-a) % bp;
      return c === 0 ? c : bp - c;
    }
  }
  $module.ShiftLeft = function(b, n) {
    return b.multipliedBy(new BigNumber(2).exponentiatedBy(n));
  }
  $module.ShiftRight = function(b, n) {
    return b.dividedToIntegerBy(new BigNumber(2).exponentiatedBy(n));
  }
  $module.RotateLeft = function(b, n, w) {  // truncate(b << n) | (b >> (w - n))
    let x = _dafny.ShiftLeft(b, n).mod(new BigNumber(2).exponentiatedBy(w));
    let y = _dafny.ShiftRight(b, w - n);
    return x.plus(y);
  }
  $module.RotateRight = function(b, n, w) {  // (b >> n) | truncate(b << (w - n))
    let x = _dafny.ShiftRight(b, n);
    let y = _dafny.ShiftLeft(b, w - n).mod(new BigNumber(2).exponentiatedBy(w));;
    return x.plus(y);
  }
  $module.BitwiseAnd = function(a, b) {
    let r = _dafny.ZERO;
    const m = _dafny.NUMBER_LIMIT;  // 2^53
    let h = _dafny.ONE;
    while (!a.isZero() && !b.isZero()) {
      let a0 = a.mod(m);
      let b0 = b.mod(m);
      r = r.plus(h.multipliedBy(a0 & b0));
      a = a.dividedToIntegerBy(m);
      b = b.dividedToIntegerBy(m);
      h = h.multipliedBy(m);
    }
    return r;
  }
  $module.BitwiseOr = function(a, b) {
    let r = _dafny.ZERO;
    const m = _dafny.NUMBER_LIMIT;  // 2^53
    let h = _dafny.ONE;
    while (!a.isZero() && !b.isZero()) {
      let a0 = a.mod(m);
      let b0 = b.mod(m);
      r = r.plus(h.multipliedBy(a0 | b0));
      a = a.dividedToIntegerBy(m);
      b = b.dividedToIntegerBy(m);
      h = h.multipliedBy(m);
    }
    r = r.plus(h.multipliedBy(a | b));
    return r;
  }
  $module.BitwiseXor = function(a, b) {
    let r = _dafny.ZERO;
    const m = _dafny.NUMBER_LIMIT;  // 2^53
    let h = _dafny.ONE;
    while (!a.isZero() && !b.isZero()) {
      let a0 = a.mod(m);
      let b0 = b.mod(m);
      r = r.plus(h.multipliedBy(a0 ^ b0));
      a = a.dividedToIntegerBy(m);
      b = b.dividedToIntegerBy(m);
      h = h.multipliedBy(m);
    }
    r = r.plus(h.multipliedBy(a | b));
    return r;
  }
  $module.BitwiseNot = function(a, bits) {
    let r = _dafny.ZERO;
    let h = _dafny.ONE;
    for (let i = 0; i < bits; i++) {
      let bit = a.mod(2);
      if (bit.isZero()) {
        r = r.plus(h);
      }
      a = a.dividedToIntegerBy(2);
      h = h.multipliedBy(2);
    }
    return r;
  }
  $module.Quantifier = function(vals, frall, pred) {
    for (let u of vals) {
      if (pred(u) !== frall) { return !frall; }
    }
    return frall;
  }
  $module.PlusChar = function(a, b) {
    return String.fromCharCode(a.charCodeAt(0) + b.charCodeAt(0));
  }
  $module.UnicodePlusChar = function(a, b) {
    return new _dafny.CodePoint(a.value + b.value);
  }
  $module.MinusChar = function(a, b) {
    return String.fromCharCode(a.charCodeAt(0) - b.charCodeAt(0));
  }
  $module.UnicodeMinusChar = function(a, b) {
    return new _dafny.CodePoint(a.value - b.value);
  }
  $module.AllBooleans = function*() {
    yield false;
    yield true;
  }
  $module.AllChars = function*() {
    for (let i = 0; i < 0x10000; i++) {
      yield String.fromCharCode(i);
    }
  }
  $module.AllUnicodeChars = function*() {
    for (let i = 0; i < 0xD800; i++) {
      yield new _dafny.CodePoint(i);
    }
    for (let i = 0xE0000; i < 0x110000; i++) {
      yield new _dafny.CodePoint(i);
    }
  }
  $module.AllIntegers = function*() {
    yield _dafny.ZERO;
    for (let j = _dafny.ONE;; j = j.plus(1)) {
      yield j;
      yield j.negated();
    }
  }
  $module.IntegerRange = function*(lo, hi) {
    if (lo === null) {
      while (true) {
        hi = hi.minus(1);
        yield hi;
      }
    } else if (hi === null) {
      while (true) {
        yield lo;
        lo = lo.plus(1);
      }
    } else {
      while (lo.isLessThan(hi)) {
        yield lo;
        lo = lo.plus(1);
      }
    }
  }
  $module.SingleValue = function*(v) {
    yield v;
  }
  $module.HaltException = class HaltException extends Error {
    constructor(message) {
      super(message)
    }
  }
  $module.HandleHaltExceptions = function(f) {
    try {
      f()
    } catch (e) {
      if (e instanceof _dafny.HaltException) {
        process.stdout.write("[Program halted] " + e.message + "\n")
        process.exitCode = 1
      } else {
        throw e
      }
    }
  }
  $module.FromMainArguments = function(args) {
    var a = [...args];
    a.splice(0, 2, args[0] + " " + args[1]);
    return a;
  }
  $module.UnicodeFromMainArguments = function(args) {
    return $module.FromMainArguments(args).map(_dafny.Seq.UnicodeFromString);
  }
  return $module;

  // What follows are routines private to the Dafny runtime
  function buildArray(initValue, ...dims) {
    if (dims.length === 0) {
      return initValue;
    } else {
      let a = Array(dims[0].toNumber());
      let b = Array.from(a, (x) => buildArray(initValue, ...dims.slice(1)));
      return b;
    }
  }
  function arrayElementsToString(a) {
    // like `a.join(", ")`, but calling _dafny.toString(x) on every element x instead of x.toString()
    let s = "";
    let sep = "";
    for (let x of a) {
      s += sep + _dafny.toString(x);
      sep = ", ";
    }
    return s;
  }
  function BigNumberGcd(a, b){  // gcd of two non-negative BigNumber's
    while (true) {
      if (a.isZero()) {
        return b;
      } else if (b.isZero()) {
        return a;
      }
      if (a.isLessThan(b)) {
        b = b.modulo(a);
      } else {
        a = a.modulo(b);
      }
    }
  }
})();
// Dafny program systemModulePopulator.dfy compiled into JavaScript
let _System = (function() {
  let $module = {};

  $module.nat = class nat {
    constructor () {
    }
    static get Default() {
      return _dafny.ZERO;
    }
    static _Is(__source) {
      let _0_x = (__source);
      return (_dafny.ZERO).isLessThanOrEqualTo(_0_x);
    }
  };

  return $module;
})(); // end of module _System
let Optional = (function() {
  let $module = {};


  $module.Option = class Option {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Some(v) {
      let $dt = new Option(0);
      $dt.v = v;
      return $dt;
    }
    static create_None() {
      let $dt = new Option(1);
      return $dt;
    }
    get is_Some() { return this.$tag === 0; }
    get is_None() { return this.$tag === 1; }
    get dtor_v() { return this.v; }
    toString() {
      if (this.$tag === 0) {
        return "Optional.Option.Some" + "(" + _dafny.toString(this.v) + ")";
      } else if (this.$tag === 1) {
        return "Optional.Option.None";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.v, other.v);
      } else if (this.$tag === 1) {
        return other.$tag === 1;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Optional.Option.create_None();
    }
    static Rtd() {
      return class {
        static get Default() {
          return Option.Default();
        }
      };
    }
    Unwrap() {
      let _this = this;
      return (_this).dtor_v;
    };
    UnwrapOr(_$$_default) {
      let _this = this;
      let _source0 = _this;
      {
        if (_source0.is_Some) {
          let _0_v = (_source0).v;
          return _0_v;
        }
      }
      {
        let _1_none = _source0;
        return _$$_default;
      }
    };
  }
  return $module;
})(); // end of module Optional
let ProcessDefinition = (function() {
  let $module = {};


  $module.NodeType = class NodeType {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_StartEvent() {
      let $dt = new NodeType(0);
      return $dt;
    }
    static create_EndEvent() {
      let $dt = new NodeType(1);
      return $dt;
    }
    static create_Task(taskType) {
      let $dt = new NodeType(2);
      $dt.taskType = taskType;
      return $dt;
    }
    static create_Gateway(gatewayType) {
      let $dt = new NodeType(3);
      $dt.gatewayType = gatewayType;
      return $dt;
    }
    static create_IntermediateEvent(eventType) {
      let $dt = new NodeType(4);
      $dt.eventType = eventType;
      return $dt;
    }
    get is_StartEvent() { return this.$tag === 0; }
    get is_EndEvent() { return this.$tag === 1; }
    get is_Task() { return this.$tag === 2; }
    get is_Gateway() { return this.$tag === 3; }
    get is_IntermediateEvent() { return this.$tag === 4; }
    get dtor_taskType() { return this.taskType; }
    get dtor_gatewayType() { return this.gatewayType; }
    get dtor_eventType() { return this.eventType; }
    toString() {
      if (this.$tag === 0) {
        return "ProcessDefinition.NodeType.StartEvent";
      } else if (this.$tag === 1) {
        return "ProcessDefinition.NodeType.EndEvent";
      } else if (this.$tag === 2) {
        return "ProcessDefinition.NodeType.Task" + "(" + _dafny.toString(this.taskType) + ")";
      } else if (this.$tag === 3) {
        return "ProcessDefinition.NodeType.Gateway" + "(" + _dafny.toString(this.gatewayType) + ")";
      } else if (this.$tag === 4) {
        return "ProcessDefinition.NodeType.IntermediateEvent" + "(" + _dafny.toString(this.eventType) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1;
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.taskType, other.taskType);
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.gatewayType, other.gatewayType);
      } else if (this.$tag === 4) {
        return other.$tag === 4 && _dafny.areEqual(this.eventType, other.eventType);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ProcessDefinition.NodeType.create_StartEvent();
    }
    static Rtd() {
      return class {
        static get Default() {
          return NodeType.Default();
        }
      };
    }
  }

  $module.TaskType = class TaskType {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_UserTask() {
      let $dt = new TaskType(0);
      return $dt;
    }
    static create_ServiceTask() {
      let $dt = new TaskType(1);
      return $dt;
    }
    static create_ScriptTask() {
      let $dt = new TaskType(2);
      return $dt;
    }
    static create_BusinessRuleTask() {
      let $dt = new TaskType(3);
      return $dt;
    }
    get is_UserTask() { return this.$tag === 0; }
    get is_ServiceTask() { return this.$tag === 1; }
    get is_ScriptTask() { return this.$tag === 2; }
    get is_BusinessRuleTask() { return this.$tag === 3; }
    static get AllSingletonConstructors() {
      return this.AllSingletonConstructors_();
    }
    static *AllSingletonConstructors_() {
      yield TaskType.create_UserTask();
      yield TaskType.create_ServiceTask();
      yield TaskType.create_ScriptTask();
      yield TaskType.create_BusinessRuleTask();
    }
    toString() {
      if (this.$tag === 0) {
        return "ProcessDefinition.TaskType.UserTask";
      } else if (this.$tag === 1) {
        return "ProcessDefinition.TaskType.ServiceTask";
      } else if (this.$tag === 2) {
        return "ProcessDefinition.TaskType.ScriptTask";
      } else if (this.$tag === 3) {
        return "ProcessDefinition.TaskType.BusinessRuleTask";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1;
      } else if (this.$tag === 2) {
        return other.$tag === 2;
      } else if (this.$tag === 3) {
        return other.$tag === 3;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ProcessDefinition.TaskType.create_UserTask();
    }
    static Rtd() {
      return class {
        static get Default() {
          return TaskType.Default();
        }
      };
    }
  }

  $module.GatewayType = class GatewayType {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_ExclusiveGateway() {
      let $dt = new GatewayType(0);
      return $dt;
    }
    static create_ParallelGateway() {
      let $dt = new GatewayType(1);
      return $dt;
    }
    static create_InclusiveGateway() {
      let $dt = new GatewayType(2);
      return $dt;
    }
    static create_EventBasedGateway() {
      let $dt = new GatewayType(3);
      return $dt;
    }
    get is_ExclusiveGateway() { return this.$tag === 0; }
    get is_ParallelGateway() { return this.$tag === 1; }
    get is_InclusiveGateway() { return this.$tag === 2; }
    get is_EventBasedGateway() { return this.$tag === 3; }
    static get AllSingletonConstructors() {
      return this.AllSingletonConstructors_();
    }
    static *AllSingletonConstructors_() {
      yield GatewayType.create_ExclusiveGateway();
      yield GatewayType.create_ParallelGateway();
      yield GatewayType.create_InclusiveGateway();
      yield GatewayType.create_EventBasedGateway();
    }
    toString() {
      if (this.$tag === 0) {
        return "ProcessDefinition.GatewayType.ExclusiveGateway";
      } else if (this.$tag === 1) {
        return "ProcessDefinition.GatewayType.ParallelGateway";
      } else if (this.$tag === 2) {
        return "ProcessDefinition.GatewayType.InclusiveGateway";
      } else if (this.$tag === 3) {
        return "ProcessDefinition.GatewayType.EventBasedGateway";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1;
      } else if (this.$tag === 2) {
        return other.$tag === 2;
      } else if (this.$tag === 3) {
        return other.$tag === 3;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ProcessDefinition.GatewayType.create_ExclusiveGateway();
    }
    static Rtd() {
      return class {
        static get Default() {
          return GatewayType.Default();
        }
      };
    }
  }

  $module.EventType = class EventType {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_MessageEvent() {
      let $dt = new EventType(0);
      return $dt;
    }
    static create_TimerEvent() {
      let $dt = new EventType(1);
      return $dt;
    }
    static create_SignalEvent() {
      let $dt = new EventType(2);
      return $dt;
    }
    static create_ErrorEvent() {
      let $dt = new EventType(3);
      return $dt;
    }
    get is_MessageEvent() { return this.$tag === 0; }
    get is_TimerEvent() { return this.$tag === 1; }
    get is_SignalEvent() { return this.$tag === 2; }
    get is_ErrorEvent() { return this.$tag === 3; }
    static get AllSingletonConstructors() {
      return this.AllSingletonConstructors_();
    }
    static *AllSingletonConstructors_() {
      yield EventType.create_MessageEvent();
      yield EventType.create_TimerEvent();
      yield EventType.create_SignalEvent();
      yield EventType.create_ErrorEvent();
    }
    toString() {
      if (this.$tag === 0) {
        return "ProcessDefinition.EventType.MessageEvent";
      } else if (this.$tag === 1) {
        return "ProcessDefinition.EventType.TimerEvent";
      } else if (this.$tag === 2) {
        return "ProcessDefinition.EventType.SignalEvent";
      } else if (this.$tag === 3) {
        return "ProcessDefinition.EventType.ErrorEvent";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1;
      } else if (this.$tag === 2) {
        return other.$tag === 2;
      } else if (this.$tag === 3) {
        return other.$tag === 3;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ProcessDefinition.EventType.create_MessageEvent();
    }
    static Rtd() {
      return class {
        static get Default() {
          return EventType.Default();
        }
      };
    }
  }

  $module.Node = class Node {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_ProcessNode(id, name, nodeType, incoming, outgoing) {
      let $dt = new Node(0);
      $dt.id = id;
      $dt.name = name;
      $dt.nodeType = nodeType;
      $dt.incoming = incoming;
      $dt.outgoing = outgoing;
      return $dt;
    }
    get is_ProcessNode() { return this.$tag === 0; }
    get dtor_id() { return this.id; }
    get dtor_name() { return this.name; }
    get dtor_nodeType() { return this.nodeType; }
    get dtor_incoming() { return this.incoming; }
    get dtor_outgoing() { return this.outgoing; }
    toString() {
      if (this.$tag === 0) {
        return "ProcessDefinition.Node.ProcessNode" + "(" + this.id.toVerbatimString(true) + ", " + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.nodeType) + ", " + _dafny.toString(this.incoming) + ", " + _dafny.toString(this.outgoing) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.id, other.id) && _dafny.areEqual(this.name, other.name) && _dafny.areEqual(this.nodeType, other.nodeType) && _dafny.areEqual(this.incoming, other.incoming) && _dafny.areEqual(this.outgoing, other.outgoing);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ProcessDefinition.Node.create_ProcessNode(_dafny.Seq.UnicodeFromString(""), _dafny.Seq.UnicodeFromString(""), ProcessDefinition.NodeType.Default(), _dafny.Set.Empty, _dafny.Set.Empty);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Node.Default();
        }
      };
    }
  }

  $module.SequenceFlow = class SequenceFlow {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Flow(id, sourceRef, targetRef, condition) {
      let $dt = new SequenceFlow(0);
      $dt.id = id;
      $dt.sourceRef = sourceRef;
      $dt.targetRef = targetRef;
      $dt.condition = condition;
      return $dt;
    }
    get is_Flow() { return this.$tag === 0; }
    get dtor_id() { return this.id; }
    get dtor_sourceRef() { return this.sourceRef; }
    get dtor_targetRef() { return this.targetRef; }
    get dtor_condition() { return this.condition; }
    toString() {
      if (this.$tag === 0) {
        return "ProcessDefinition.SequenceFlow.Flow" + "(" + this.id.toVerbatimString(true) + ", " + this.sourceRef.toVerbatimString(true) + ", " + this.targetRef.toVerbatimString(true) + ", " + _dafny.toString(this.condition) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.id, other.id) && _dafny.areEqual(this.sourceRef, other.sourceRef) && _dafny.areEqual(this.targetRef, other.targetRef) && _dafny.areEqual(this.condition, other.condition);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ProcessDefinition.SequenceFlow.create_Flow(_dafny.Seq.UnicodeFromString(""), _dafny.Seq.UnicodeFromString(""), _dafny.Seq.UnicodeFromString(""), Optional.Option.Default());
    }
    static Rtd() {
      return class {
        static get Default() {
          return SequenceFlow.Default();
        }
      };
    }
  }

  $module.ProcessDef = class ProcessDef {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_ProcessDefinition(id, name, nodes, flows, startNodes, endNodes) {
      let $dt = new ProcessDef(0);
      $dt.id = id;
      $dt.name = name;
      $dt.nodes = nodes;
      $dt.flows = flows;
      $dt.startNodes = startNodes;
      $dt.endNodes = endNodes;
      return $dt;
    }
    get is_ProcessDefinition() { return this.$tag === 0; }
    get dtor_id() { return this.id; }
    get dtor_name() { return this.name; }
    get dtor_nodes() { return this.nodes; }
    get dtor_flows() { return this.flows; }
    get dtor_startNodes() { return this.startNodes; }
    get dtor_endNodes() { return this.endNodes; }
    toString() {
      if (this.$tag === 0) {
        return "ProcessDefinition.ProcessDef.ProcessDefinition" + "(" + this.id.toVerbatimString(true) + ", " + this.name.toVerbatimString(true) + ", " + _dafny.toString(this.nodes) + ", " + _dafny.toString(this.flows) + ", " + _dafny.toString(this.startNodes) + ", " + _dafny.toString(this.endNodes) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.id, other.id) && _dafny.areEqual(this.name, other.name) && _dafny.areEqual(this.nodes, other.nodes) && _dafny.areEqual(this.flows, other.flows) && _dafny.areEqual(this.startNodes, other.startNodes) && _dafny.areEqual(this.endNodes, other.endNodes);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ProcessDefinition.ProcessDef.create_ProcessDefinition(_dafny.Seq.UnicodeFromString(""), _dafny.Seq.UnicodeFromString(""), _dafny.Map.Empty, _dafny.Map.Empty, _dafny.Set.Empty, _dafny.Set.Empty);
    }
    static Rtd() {
      return class {
        static get Default() {
          return ProcessDef.Default();
        }
      };
    }
  }
  return $module;
})(); // end of module ProcessDefinition
let Token = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Token._default";
    }
    _parentTraits() {
      return [];
    }
    static ValidTokenCollection(tc) {
      if ((new BigNumber(((tc).dtor_tokens).length)).isEqualTo(_dafny.ZERO)) {
        return ((tc).dtor_nextTokenId).isEqualTo(_dafny.ZERO);
      } else {
        return ((_dafny.ZERO).isLessThan((tc).dtor_nextTokenId)) && (_dafny.Quantifier(((tc).dtor_tokens).Keys.Elements, true, function (_forall_var_0) {
          let _0_tokenId = _forall_var_0;
          return !(((tc).dtor_tokens).contains(_0_tokenId)) || ((_0_tokenId).isLessThan((tc).dtor_nextTokenId));
        }));
      }
    };
    static Create() {
      return Token.Collection.create_TokenCollection(_dafny.Map.Empty.slice(), _dafny.ZERO, _dafny.ZERO);
    };
    static CreateToken(tc, location) {
      let _0_tokenId = (tc).dtor_nextTokenId;
      let _1_token = Token.T.create_Token(_0_tokenId, location, Token.TokenStatus.create_Active(), Optional.Option.create_None(), _dafny.Set.fromElements(), (tc).dtor_currentTime, _dafny.Seq.of(location));
      let _2_newTokens = ((tc).dtor_tokens).update(_0_tokenId, _1_token);
      let _3_newTc = function (_pat_let0_0) {
        return function (_4_dt__update__tmp_h0) {
          return function (_pat_let1_0) {
            return function (_5_dt__update_hnextTokenId_h0) {
              return function (_pat_let2_0) {
                return function (_6_dt__update_htokens_h0) {
                  return Token.Collection.create_TokenCollection(_6_dt__update_htokens_h0, _5_dt__update_hnextTokenId_h0, (_4_dt__update__tmp_h0).dtor_currentTime);
                }(_pat_let2_0);
              }(_2_newTokens);
            }(_pat_let1_0);
          }((_0_tokenId).plus(_dafny.ONE));
        }(_pat_let0_0);
      }(tc);
      return _dafny.Tuple.of(_3_newTc, _0_tokenId);
    };
    static CreateTokensForFlows(tokens, flows, flowDefinitions) {
      if ((new BigNumber((flows).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Tuple.of(tokens, _dafny.Set.fromElements());
      } else {
        let _0_flowId = Token.__default.PickOne(flows);
        let _1_remainingFlows = (flows).Difference(_dafny.Set.fromElements(_0_flowId));
        let _2_targetNodeId = ((flowDefinitions).get(_0_flowId)).dtor_targetRef;
        let _let_tmp_rhs0 = Token.__default.CreateToken(tokens, _2_targetNodeId);
        let _3_tokensWithNew = (_let_tmp_rhs0)[0];
        let _4_newTokenId = (_let_tmp_rhs0)[1];
        let _let_tmp_rhs1 = Token.__default.CreateTokensForFlows(_3_tokensWithNew, _1_remainingFlows, flowDefinitions);
        let _5_finalTokens = (_let_tmp_rhs1)[0];
        let _6_remainingTokenIds = (_let_tmp_rhs1)[1];
        return _dafny.Tuple.of(_5_finalTokens, (_6_remainingTokenIds).Union(_dafny.Set.fromElements(_4_newTokenId)));
      }
    };
    static MoveToken(tc, tokenId, newLocation) {
      let _pat_let_tv0 = newLocation;
      let _pat_let_tv1 = newLocation;
      let _0_token = ((tc).dtor_tokens).get(tokenId);
      let _1_updatedToken = function (_pat_let3_0) {
        return function (_2_dt__update__tmp_h0) {
          return function (_pat_let4_0) {
            return function (_3_dt__update_hpath_h0) {
              return function (_pat_let5_0) {
                return function (_4_dt__update_hlocation_h0) {
                  return Token.T.create_Token((_2_dt__update__tmp_h0).dtor_id, _4_dt__update_hlocation_h0, (_2_dt__update__tmp_h0).dtor_status, (_2_dt__update__tmp_h0).dtor_parentToken, (_2_dt__update__tmp_h0).dtor_childTokens, (_2_dt__update__tmp_h0).dtor_creationTime, _3_dt__update_hpath_h0);
                }(_pat_let5_0);
              }(_pat_let_tv1);
            }(_pat_let4_0);
          }(_dafny.Seq.Concat((_0_token).dtor_path, _dafny.Seq.of(_pat_let_tv0)));
        }(_pat_let3_0);
      }(_0_token);
      let _5_dt__update__tmp_h1 = tc;
      let _6_dt__update_htokens_h0 = ((tc).dtor_tokens).update(tokenId, _1_updatedToken);
      return Token.Collection.create_TokenCollection(_6_dt__update_htokens_h0, (_5_dt__update__tmp_h1).dtor_nextTokenId, (_5_dt__update__tmp_h1).dtor_currentTime);
    };
    static ConsumeToken(tc, tokenId) {
      let _0_token = ((tc).dtor_tokens).get(tokenId);
      let _1_updatedToken = function (_pat_let6_0) {
        return function (_2_dt__update__tmp_h0) {
          return function (_pat_let7_0) {
            return function (_3_dt__update_hstatus_h0) {
              return Token.T.create_Token((_2_dt__update__tmp_h0).dtor_id, (_2_dt__update__tmp_h0).dtor_location, _3_dt__update_hstatus_h0, (_2_dt__update__tmp_h0).dtor_parentToken, (_2_dt__update__tmp_h0).dtor_childTokens, (_2_dt__update__tmp_h0).dtor_creationTime, (_2_dt__update__tmp_h0).dtor_path);
            }(_pat_let7_0);
          }(Token.TokenStatus.create_Consumed());
        }(_pat_let6_0);
      }(_0_token);
      let _4_dt__update__tmp_h1 = tc;
      let _5_dt__update_htokens_h0 = ((tc).dtor_tokens).update(tokenId, _1_updatedToken);
      return Token.Collection.create_TokenCollection(_5_dt__update_htokens_h0, (_4_dt__update__tmp_h1).dtor_nextTokenId, (_4_dt__update__tmp_h1).dtor_currentTime);
    };
    static ConsumeTokens(tc, tokenIds) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((tokenIds).length)).isEqualTo(_dafny.ZERO)) {
          return tc;
        } else {
          let _0_tokenId = Token.__default.PickOne(tokenIds);
          let _1_remainingIds = (tokenIds).Difference(_dafny.Set.fromElements(_0_tokenId));
          let _2_tc_k = Token.__default.ConsumeToken(tc, _0_tokenId);
          let _in0 = _2_tc_k;
          let _in1 = _1_remainingIds;
          tc = _in0;
          tokenIds = _in1;
          continue TAIL_CALL_START;
        }
      }
    };
    static PickOne(s) {
      return function (_let_dummy_8) {
        let _0_x = undefined;
        L_ASSIGN_SUCH_THAT_0: {
          for (const _assign_such_that_0 of (s).Elements) {
            _0_x = _assign_such_that_0;
            if ((s).contains(_0_x)) {
              break L_ASSIGN_SUCH_THAT_0;
            }
          }
          throw new Error("assign-such-that search produced no value");
        }
        return _0_x;
      }(0);
    };
    static SplitToken(tc, tokenId, targetLocations) {
      let _0_tc_k = Token.__default.ConsumeToken(tc, tokenId);
      let _1_parentToken = ((tc).dtor_tokens).get(tokenId);
      return Token.__default.SplitTokenHelper(_0_tc_k, tokenId, targetLocations, _dafny.ZERO, _dafny.Set.fromElements());
    };
    static SplitTokenHelper(tc, parentId, locations, index, createdTokens) {
      TAIL_CALL_START: while (true) {
        let _pat_let_tv0 = createdTokens;
        let _pat_let_tv1 = tc;
        let _pat_let_tv2 = parentId;
        let _pat_let_tv3 = parentId;
        if ((index).isEqualTo(new BigNumber((locations).length))) {
          let _0_parentToken = ((tc).dtor_tokens).get(parentId);
          let _1_updatedParent = function (_pat_let9_0) {
            return function (_2_dt__update__tmp_h0) {
              return function (_pat_let10_0) {
                return function (_3_dt__update_hchildTokens_h0) {
                  return Token.T.create_Token((_2_dt__update__tmp_h0).dtor_id, (_2_dt__update__tmp_h0).dtor_location, (_2_dt__update__tmp_h0).dtor_status, (_2_dt__update__tmp_h0).dtor_parentToken, _3_dt__update_hchildTokens_h0, (_2_dt__update__tmp_h0).dtor_creationTime, (_2_dt__update__tmp_h0).dtor_path);
                }(_pat_let10_0);
              }(((_0_parentToken).dtor_childTokens).Union(_pat_let_tv0));
            }(_pat_let9_0);
          }(_0_parentToken);
          return _dafny.Tuple.of(function (_pat_let11_0) {
  return function (_4_dt__update__tmp_h1) {
    return function (_pat_let12_0) {
      return function (_5_dt__update_htokens_h0) {
        return Token.Collection.create_TokenCollection(_5_dt__update_htokens_h0, (_4_dt__update__tmp_h1).dtor_nextTokenId, (_4_dt__update__tmp_h1).dtor_currentTime);
      }(_pat_let12_0);
    }(((_pat_let_tv1).dtor_tokens).update(_pat_let_tv2, _1_updatedParent));
  }(_pat_let11_0);
}(tc), createdTokens);
        } else {
          let _let_tmp_rhs0 = Token.__default.CreateToken(tc, (locations)[index]);
          let _6_tc_k = (_let_tmp_rhs0)[0];
          let _7_newTokenId = (_let_tmp_rhs0)[1];
          let _8_newToken = ((_6_tc_k).dtor_tokens).get(_7_newTokenId);
          let _9_updatedToken = function (_pat_let13_0) {
            return function (_10_dt__update__tmp_h2) {
              return function (_pat_let14_0) {
                return function (_11_dt__update_hparentToken_h0) {
                  return Token.T.create_Token((_10_dt__update__tmp_h2).dtor_id, (_10_dt__update__tmp_h2).dtor_location, (_10_dt__update__tmp_h2).dtor_status, _11_dt__update_hparentToken_h0, (_10_dt__update__tmp_h2).dtor_childTokens, (_10_dt__update__tmp_h2).dtor_creationTime, (_10_dt__update__tmp_h2).dtor_path);
                }(_pat_let14_0);
              }(Optional.Option.create_Some(_pat_let_tv3));
            }(_pat_let13_0);
          }(_8_newToken);
          let _12_tc_k_k = function (_pat_let15_0) {
            return function (_13_dt__update__tmp_h3) {
              return function (_pat_let16_0) {
                return function (_14_dt__update_htokens_h1) {
                  return Token.Collection.create_TokenCollection(_14_dt__update_htokens_h1, (_13_dt__update__tmp_h3).dtor_nextTokenId, (_13_dt__update__tmp_h3).dtor_currentTime);
                }(_pat_let16_0);
              }(((_6_tc_k).dtor_tokens).update(_7_newTokenId, _9_updatedToken));
            }(_pat_let15_0);
          }(_6_tc_k);
          let _in0 = _12_tc_k_k;
          let _in1 = parentId;
          let _in2 = locations;
          let _in3 = (index).plus(_dafny.ONE);
          let _in4 = (createdTokens).Union(_dafny.Set.fromElements(_7_newTokenId));
          tc = _in0;
          parentId = _in1;
          locations = _in2;
          index = _in3;
          createdTokens = _in4;
          continue TAIL_CALL_START;
        }
      }
    };
    static FindCommonParent(tc, tokenIds) {
      if ((new BigNumber((tokenIds).length)).isEqualTo(_dafny.ZERO)) {
        return Optional.Option.create_None();
      } else {
        let _0_tokenId = Token.__default.PickOne(tokenIds);
        let _1_token = ((tc).dtor_tokens).get(_0_tokenId);
        if (((_1_token).dtor_parentToken).is_None) {
          return Optional.Option.create_None();
        } else {
          let _2_parent = ((_1_token).dtor_parentToken).Unwrap();
          let _3_allHaveSameParent = _dafny.Quantifier((tokenIds).Elements, true, function (_forall_var_0) {
            let _4_id = _forall_var_0;
            return !((tokenIds).contains(_4_id)) || ((((((tc).dtor_tokens).get(_4_id)).dtor_parentToken).is_Some) && ((((((tc).dtor_tokens).get(_4_id)).dtor_parentToken).Unwrap()).isEqualTo(_2_parent)));
          });
          if (_3_allHaveSameParent) {
            return Optional.Option.create_Some(_2_parent);
          } else {
            return Optional.Option.create_None();
          }
        }
      }
    };
    static UpdateParentReferences(tc, oldTokenIds, newTokenId) {
      TAIL_CALL_START: while (true) {
        let _pat_let_tv0 = newTokenId;
        let _pat_let_tv1 = tc;
        if ((new BigNumber((oldTokenIds).length)).isEqualTo(_dafny.ZERO)) {
          return tc;
        } else {
          let _0_tokenId = Token.__default.PickOne(oldTokenIds);
          let _1_remainingIds = (oldTokenIds).Difference(_dafny.Set.fromElements(_0_tokenId));
          let _2_token = ((tc).dtor_tokens).get(_0_tokenId);
          if (((_2_token).dtor_parentToken).is_Some) {
            let _3_parentId = ((_2_token).dtor_parentToken).Unwrap();
            let _4_parentToken = ((tc).dtor_tokens).get(_3_parentId);
            let _5_updatedParent = function (_pat_let17_0) {
              return function (_6_dt__update__tmp_h0) {
                return function (_pat_let18_0) {
                  return function (_7_dt__update_hchildTokens_h0) {
                    return Token.T.create_Token((_6_dt__update__tmp_h0).dtor_id, (_6_dt__update__tmp_h0).dtor_location, (_6_dt__update__tmp_h0).dtor_status, (_6_dt__update__tmp_h0).dtor_parentToken, _7_dt__update_hchildTokens_h0, (_6_dt__update__tmp_h0).dtor_creationTime, (_6_dt__update__tmp_h0).dtor_path);
                  }(_pat_let18_0);
                }((((_4_parentToken).dtor_childTokens).Difference(_dafny.Set.fromElements(_0_tokenId))).Union(_dafny.Set.fromElements(_pat_let_tv0)));
              }(_pat_let17_0);
            }(_4_parentToken);
            let _8_tc_k = function (_pat_let19_0) {
              return function (_9_dt__update__tmp_h1) {
                return function (_pat_let20_0) {
                  return function (_10_dt__update_htokens_h0) {
                    return Token.Collection.create_TokenCollection(_10_dt__update_htokens_h0, (_9_dt__update__tmp_h1).dtor_nextTokenId, (_9_dt__update__tmp_h1).dtor_currentTime);
                  }(_pat_let20_0);
                }(((_pat_let_tv1).dtor_tokens).update(_3_parentId, _5_updatedParent));
              }(_pat_let19_0);
            }(tc);
            let _in0 = _8_tc_k;
            let _in1 = _1_remainingIds;
            let _in2 = newTokenId;
            tc = _in0;
            oldTokenIds = _in1;
            newTokenId = _in2;
            continue TAIL_CALL_START;
          } else {
            let _in3 = tc;
            let _in4 = _1_remainingIds;
            let _in5 = newTokenId;
            tc = _in3;
            oldTokenIds = _in4;
            newTokenId = _in5;
            continue TAIL_CALL_START;
          }
        }
      }
    };
    static SuspendToken(tc, tokenId) {
      let _0_token = ((tc).dtor_tokens).get(tokenId);
      let _1_updatedToken = function (_pat_let21_0) {
        return function (_2_dt__update__tmp_h0) {
          return function (_pat_let22_0) {
            return function (_3_dt__update_hstatus_h0) {
              return Token.T.create_Token((_2_dt__update__tmp_h0).dtor_id, (_2_dt__update__tmp_h0).dtor_location, _3_dt__update_hstatus_h0, (_2_dt__update__tmp_h0).dtor_parentToken, (_2_dt__update__tmp_h0).dtor_childTokens, (_2_dt__update__tmp_h0).dtor_creationTime, (_2_dt__update__tmp_h0).dtor_path);
            }(_pat_let22_0);
          }(Token.TokenStatus.create_Suspended());
        }(_pat_let21_0);
      }(_0_token);
      let _4_dt__update__tmp_h1 = tc;
      let _5_dt__update_htokens_h0 = ((tc).dtor_tokens).update(tokenId, _1_updatedToken);
      return Token.Collection.create_TokenCollection(_5_dt__update_htokens_h0, (_4_dt__update__tmp_h1).dtor_nextTokenId, (_4_dt__update__tmp_h1).dtor_currentTime);
    };
    static ResumeToken(tc, tokenId) {
      let _0_token = ((tc).dtor_tokens).get(tokenId);
      let _1_updatedToken = function (_pat_let23_0) {
        return function (_2_dt__update__tmp_h0) {
          return function (_pat_let24_0) {
            return function (_3_dt__update_hstatus_h0) {
              return Token.T.create_Token((_2_dt__update__tmp_h0).dtor_id, (_2_dt__update__tmp_h0).dtor_location, _3_dt__update_hstatus_h0, (_2_dt__update__tmp_h0).dtor_parentToken, (_2_dt__update__tmp_h0).dtor_childTokens, (_2_dt__update__tmp_h0).dtor_creationTime, (_2_dt__update__tmp_h0).dtor_path);
            }(_pat_let24_0);
          }(Token.TokenStatus.create_Active());
        }(_pat_let23_0);
      }(_0_token);
      let _4_dt__update__tmp_h1 = tc;
      let _5_dt__update_htokens_h0 = ((tc).dtor_tokens).update(tokenId, _1_updatedToken);
      return Token.Collection.create_TokenCollection(_5_dt__update_htokens_h0, (_4_dt__update__tmp_h1).dtor_nextTokenId, (_4_dt__update__tmp_h1).dtor_currentTime);
    };
    static GetTokensAtNode(tc, nodeId) {
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of ((tc).dtor_tokens).Keys.Elements) {
          let _0_tokenId = _compr_0;
          if (_System.nat._Is(_0_tokenId)) {
            if ((((tc).dtor_tokens).contains(_0_tokenId)) && (_dafny.areEqual((((tc).dtor_tokens).get(_0_tokenId)).dtor_location, nodeId))) {
              _coll0.add(_0_tokenId);
            }
          }
        }
        return _coll0;
      }();
    };
    static HasActiveTokens(tc) {
      return _dafny.Quantifier(((tc).dtor_tokens).Keys.Elements, false, function (_exists_var_0) {
        let _0_tokenId = _exists_var_0;
        return (((tc).dtor_tokens).contains(_0_tokenId)) && (_dafny.areEqual((((tc).dtor_tokens).get(_0_tokenId)).dtor_status, Token.TokenStatus.create_Active()));
      });
    };
    static HasTokensAtNodes(tc, nodeIds) {
      return _dafny.Quantifier(((tc).dtor_tokens).Keys.Elements, false, function (_exists_var_0) {
        let _0_tokenId = _exists_var_0;
        return (((tc).dtor_tokens).contains(_0_tokenId)) && ((nodeIds).contains((((tc).dtor_tokens).get(_0_tokenId)).dtor_location));
      });
    };
    static GetActiveNodes(tc) {
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of ((tc).dtor_tokens).Keys.Elements) {
          let _0_tokenId = _compr_0;
          if (((tc).dtor_tokens).contains(_0_tokenId)) {
            _coll0.add((((tc).dtor_tokens).get(_0_tokenId)).dtor_location);
          }
        }
        return _coll0;
      }();
    };
    static AdvanceTime(tc, timeIncrement) {
      let _0_dt__update__tmp_h0 = tc;
      let _1_dt__update_hcurrentTime_h0 = ((tc).dtor_currentTime).plus(timeIncrement);
      return Token.Collection.create_TokenCollection((_0_dt__update__tmp_h0).dtor_tokens, (_0_dt__update__tmp_h0).dtor_nextTokenId, _1_dt__update_hcurrentTime_h0);
    };
    static GetTokenPath(tc, tokenId) {
      return (((tc).dtor_tokens).get(tokenId)).dtor_path;
    };
    static HasVisitedNode(tc, tokenId, nodeId) {
      return _dafny.Seq.contains((((tc).dtor_tokens).get(tokenId)).dtor_path, nodeId);
    };
    static GetTokensByStatus(tc, status) {
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of ((tc).dtor_tokens).Keys.Elements) {
          let _0_tokenId = _compr_0;
          if (_System.nat._Is(_0_tokenId)) {
            if ((((tc).dtor_tokens).contains(_0_tokenId)) && (_dafny.areEqual((((tc).dtor_tokens).get(_0_tokenId)).dtor_status, status))) {
              _coll0.add(_0_tokenId);
            }
          }
        }
        return _coll0;
      }();
    };
    static GetExecutionTrace(tc) {
      if ((new BigNumber(((tc).dtor_tokens).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.of();
      } else {
        let _0_startTokenId = Token.__default.GetEarliestToken(tc);
        return (((tc).dtor_tokens).get(_0_startTokenId)).dtor_path;
      }
    };
    static GetEarliestToken(tc) {
      let _0_tokenIds = function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of ((tc).dtor_tokens).Keys.Elements) {
          let _1_tokenId = _compr_0;
          if (_System.nat._Is(_1_tokenId)) {
            if (((tc).dtor_tokens).contains(_1_tokenId)) {
              _coll0.add(_1_tokenId);
            }
          }
        }
        return _coll0;
      }();
      let _2_firstId = Token.__default.PickOne(_0_tokenIds);
      return Token.__default.FindEarliestTokenHelper(tc, (_0_tokenIds).Difference(_dafny.Set.fromElements(_2_firstId)), _2_firstId);
    };
    static FindEarliestTokenHelper(tc, remainingIds, currentEarliest) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((remainingIds).length)).isEqualTo(_dafny.ZERO)) {
          return currentEarliest;
        } else {
          let _0_tokenId = Token.__default.PickOne(remainingIds);
          let _1_newRemaining = (remainingIds).Difference(_dafny.Set.fromElements(_0_tokenId));
          if (((((tc).dtor_tokens).get(_0_tokenId)).dtor_creationTime).isLessThan((((tc).dtor_tokens).get(currentEarliest)).dtor_creationTime)) {
            let _in0 = tc;
            let _in1 = _1_newRemaining;
            let _in2 = _0_tokenId;
            tc = _in0;
            remainingIds = _in1;
            currentEarliest = _in2;
            continue TAIL_CALL_START;
          } else {
            let _in3 = tc;
            let _in4 = _1_newRemaining;
            let _in5 = currentEarliest;
            tc = _in3;
            remainingIds = _in4;
            currentEarliest = _in5;
            continue TAIL_CALL_START;
          }
        }
      }
    };
    static GetActiveTokens(tc) {
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of ((tc).dtor_tokens).Keys.Elements) {
          let _0_tokenId = _compr_0;
          if (_System.nat._Is(_0_tokenId)) {
            if ((((tc).dtor_tokens).contains(_0_tokenId)) && (_dafny.areEqual((((tc).dtor_tokens).get(_0_tokenId)).dtor_status, Token.TokenStatus.create_Active()))) {
              _coll0.add(_0_tokenId);
            }
          }
        }
        return _coll0;
      }();
    };
    static ReactivateToken(tc, tokenId) {
      let _0_token = ((tc).dtor_tokens).get(tokenId);
      let _1_updatedToken = function (_pat_let25_0) {
        return function (_2_dt__update__tmp_h0) {
          return function (_pat_let26_0) {
            return function (_3_dt__update_hstatus_h0) {
              return Token.T.create_Token((_2_dt__update__tmp_h0).dtor_id, (_2_dt__update__tmp_h0).dtor_location, _3_dt__update_hstatus_h0, (_2_dt__update__tmp_h0).dtor_parentToken, (_2_dt__update__tmp_h0).dtor_childTokens, (_2_dt__update__tmp_h0).dtor_creationTime, (_2_dt__update__tmp_h0).dtor_path);
            }(_pat_let26_0);
          }(Token.TokenStatus.create_Active());
        }(_pat_let25_0);
      }(_0_token);
      let _4_dt__update__tmp_h1 = tc;
      let _5_dt__update_htokens_h0 = ((tc).dtor_tokens).update(tokenId, _1_updatedToken);
      return Token.Collection.create_TokenCollection(_5_dt__update_htokens_h0, (_4_dt__update__tmp_h1).dtor_nextTokenId, (_4_dt__update__tmp_h1).dtor_currentTime);
    };
    static SetTokenError(tc, tokenId, errorMsg) {
      let _0_token = ((tc).dtor_tokens).get(tokenId);
      let _1_updatedToken = function (_pat_let27_0) {
        return function (_2_dt__update__tmp_h0) {
          return function (_pat_let28_0) {
            return function (_3_dt__update_hstatus_h0) {
              return Token.T.create_Token((_2_dt__update__tmp_h0).dtor_id, (_2_dt__update__tmp_h0).dtor_location, _3_dt__update_hstatus_h0, (_2_dt__update__tmp_h0).dtor_parentToken, (_2_dt__update__tmp_h0).dtor_childTokens, (_2_dt__update__tmp_h0).dtor_creationTime, (_2_dt__update__tmp_h0).dtor_path);
            }(_pat_let28_0);
          }(Token.TokenStatus.create_Error());
        }(_pat_let27_0);
      }(_0_token);
      let _4_dt__update__tmp_h1 = tc;
      let _5_dt__update_htokens_h0 = ((tc).dtor_tokens).update(tokenId, _1_updatedToken);
      return Token.Collection.create_TokenCollection(_5_dt__update_htokens_h0, (_4_dt__update__tmp_h1).dtor_nextTokenId, (_4_dt__update__tmp_h1).dtor_currentTime);
    };
    static SetTokenWaiting(tc, tokenId) {
      let _0_token = ((tc).dtor_tokens).get(tokenId);
      let _1_updatedToken = function (_pat_let29_0) {
        return function (_2_dt__update__tmp_h0) {
          return function (_pat_let30_0) {
            return function (_3_dt__update_hstatus_h0) {
              return Token.T.create_Token((_2_dt__update__tmp_h0).dtor_id, (_2_dt__update__tmp_h0).dtor_location, _3_dt__update_hstatus_h0, (_2_dt__update__tmp_h0).dtor_parentToken, (_2_dt__update__tmp_h0).dtor_childTokens, (_2_dt__update__tmp_h0).dtor_creationTime, (_2_dt__update__tmp_h0).dtor_path);
            }(_pat_let30_0);
          }(Token.TokenStatus.create_Waiting());
        }(_pat_let29_0);
      }(_0_token);
      let _4_dt__update__tmp_h1 = tc;
      let _5_dt__update_htokens_h0 = ((tc).dtor_tokens).update(tokenId, _1_updatedToken);
      return Token.Collection.create_TokenCollection(_5_dt__update_htokens_h0, (_4_dt__update__tmp_h1).dtor_nextTokenId, (_4_dt__update__tmp_h1).dtor_currentTime);
    };
    static SetTokenActive(tc, tokenId) {
      let _0_token = ((tc).dtor_tokens).get(tokenId);
      let _1_updatedToken = function (_pat_let31_0) {
        return function (_2_dt__update__tmp_h0) {
          return function (_pat_let32_0) {
            return function (_3_dt__update_hstatus_h0) {
              return Token.T.create_Token((_2_dt__update__tmp_h0).dtor_id, (_2_dt__update__tmp_h0).dtor_location, _3_dt__update_hstatus_h0, (_2_dt__update__tmp_h0).dtor_parentToken, (_2_dt__update__tmp_h0).dtor_childTokens, (_2_dt__update__tmp_h0).dtor_creationTime, (_2_dt__update__tmp_h0).dtor_path);
            }(_pat_let32_0);
          }(Token.TokenStatus.create_Active());
        }(_pat_let31_0);
      }(_0_token);
      let _4_dt__update__tmp_h1 = tc;
      let _5_dt__update_htokens_h0 = ((tc).dtor_tokens).update(tokenId, _1_updatedToken);
      return Token.Collection.create_TokenCollection(_5_dt__update_htokens_h0, (_4_dt__update__tmp_h1).dtor_nextTokenId, (_4_dt__update__tmp_h1).dtor_currentTime);
    };
    static GetWaitingTokens(tc) {
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of ((tc).dtor_tokens).Keys.Elements) {
          let _0_tokenId = _compr_0;
          if (_System.nat._Is(_0_tokenId)) {
            if ((((tc).dtor_tokens).contains(_0_tokenId)) && (_dafny.areEqual((((tc).dtor_tokens).get(_0_tokenId)).dtor_status, Token.TokenStatus.create_Waiting()))) {
              _coll0.add(_0_tokenId);
            }
          }
        }
        return _coll0;
      }();
    };
  };

  $module.TokenStatus = class TokenStatus {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Active() {
      let $dt = new TokenStatus(0);
      return $dt;
    }
    static create_Waiting() {
      let $dt = new TokenStatus(1);
      return $dt;
    }
    static create_Consumed() {
      let $dt = new TokenStatus(2);
      return $dt;
    }
    static create_Suspended() {
      let $dt = new TokenStatus(3);
      return $dt;
    }
    static create_Error() {
      let $dt = new TokenStatus(4);
      return $dt;
    }
    get is_Active() { return this.$tag === 0; }
    get is_Waiting() { return this.$tag === 1; }
    get is_Consumed() { return this.$tag === 2; }
    get is_Suspended() { return this.$tag === 3; }
    get is_Error() { return this.$tag === 4; }
    static get AllSingletonConstructors() {
      return this.AllSingletonConstructors_();
    }
    static *AllSingletonConstructors_() {
      yield TokenStatus.create_Active();
      yield TokenStatus.create_Waiting();
      yield TokenStatus.create_Consumed();
      yield TokenStatus.create_Suspended();
      yield TokenStatus.create_Error();
    }
    toString() {
      if (this.$tag === 0) {
        return "Token.TokenStatus.Active";
      } else if (this.$tag === 1) {
        return "Token.TokenStatus.Waiting";
      } else if (this.$tag === 2) {
        return "Token.TokenStatus.Consumed";
      } else if (this.$tag === 3) {
        return "Token.TokenStatus.Suspended";
      } else if (this.$tag === 4) {
        return "Token.TokenStatus.Error";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1;
      } else if (this.$tag === 2) {
        return other.$tag === 2;
      } else if (this.$tag === 3) {
        return other.$tag === 3;
      } else if (this.$tag === 4) {
        return other.$tag === 4;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Token.TokenStatus.create_Active();
    }
    static Rtd() {
      return class {
        static get Default() {
          return TokenStatus.Default();
        }
      };
    }
  }

  $module.T = class T {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Token(id, location, status, parentToken, childTokens, creationTime, path) {
      let $dt = new T(0);
      $dt.id = id;
      $dt.location = location;
      $dt.status = status;
      $dt.parentToken = parentToken;
      $dt.childTokens = childTokens;
      $dt.creationTime = creationTime;
      $dt.path = path;
      return $dt;
    }
    get is_Token() { return this.$tag === 0; }
    get dtor_id() { return this.id; }
    get dtor_location() { return this.location; }
    get dtor_status() { return this.status; }
    get dtor_parentToken() { return this.parentToken; }
    get dtor_childTokens() { return this.childTokens; }
    get dtor_creationTime() { return this.creationTime; }
    get dtor_path() { return this.path; }
    toString() {
      if (this.$tag === 0) {
        return "Token.T.Token" + "(" + _dafny.toString(this.id) + ", " + this.location.toVerbatimString(true) + ", " + _dafny.toString(this.status) + ", " + _dafny.toString(this.parentToken) + ", " + _dafny.toString(this.childTokens) + ", " + _dafny.toString(this.creationTime) + ", " + _dafny.toString(this.path) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.id, other.id) && _dafny.areEqual(this.location, other.location) && _dafny.areEqual(this.status, other.status) && _dafny.areEqual(this.parentToken, other.parentToken) && _dafny.areEqual(this.childTokens, other.childTokens) && _dafny.areEqual(this.creationTime, other.creationTime) && _dafny.areEqual(this.path, other.path);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Token.T.create_Token(_dafny.ZERO, _dafny.Seq.UnicodeFromString(""), Token.TokenStatus.Default(), Optional.Option.Default(), _dafny.Set.Empty, _dafny.ZERO, _dafny.Seq.of());
    }
    static Rtd() {
      return class {
        static get Default() {
          return T.Default();
        }
      };
    }
  }

  $module.Collection = class Collection {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_TokenCollection(tokens, nextTokenId, currentTime) {
      let $dt = new Collection(0);
      $dt.tokens = tokens;
      $dt.nextTokenId = nextTokenId;
      $dt.currentTime = currentTime;
      return $dt;
    }
    get is_TokenCollection() { return this.$tag === 0; }
    get dtor_tokens() { return this.tokens; }
    get dtor_nextTokenId() { return this.nextTokenId; }
    get dtor_currentTime() { return this.currentTime; }
    toString() {
      if (this.$tag === 0) {
        return "Token.Collection.TokenCollection" + "(" + _dafny.toString(this.tokens) + ", " + _dafny.toString(this.nextTokenId) + ", " + _dafny.toString(this.currentTime) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.tokens, other.tokens) && _dafny.areEqual(this.nextTokenId, other.nextTokenId) && _dafny.areEqual(this.currentTime, other.currentTime);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Token.Collection.create_TokenCollection(_dafny.Map.Empty, _dafny.ZERO, _dafny.ZERO);
    }
    static Rtd() {
      return class {
        static get Default() {
          return Collection.Default();
        }
      };
    }
  }
  return $module;
})(); // end of module Token
let Variables = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Variables._default";
    }
    _parentTraits() {
      return [];
    }
    static EmptyVariables() {
      return _dafny.Map.Empty.slice();
    };
    static SetVariable(vars, name, value) {
      return (vars).update(name, value);
    };
    static GetVariable(vars, name) {
      if ((vars).contains(name)) {
        return Optional.Option.create_Some((vars).get(name));
      } else {
        return Optional.Option.create_None();
      }
    };
  };

  $module.VariableValue = class VariableValue {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_StringValue(stringValue) {
      let $dt = new VariableValue(0);
      $dt.stringValue = stringValue;
      return $dt;
    }
    static create_IntValue(intValue) {
      let $dt = new VariableValue(1);
      $dt.intValue = intValue;
      return $dt;
    }
    static create_BoolValue(boolValue) {
      let $dt = new VariableValue(2);
      $dt.boolValue = boolValue;
      return $dt;
    }
    static create_ListValue(values) {
      let $dt = new VariableValue(3);
      $dt.values = values;
      return $dt;
    }
    static create_ObjectValue(fields) {
      let $dt = new VariableValue(4);
      $dt.fields = fields;
      return $dt;
    }
    get is_StringValue() { return this.$tag === 0; }
    get is_IntValue() { return this.$tag === 1; }
    get is_BoolValue() { return this.$tag === 2; }
    get is_ListValue() { return this.$tag === 3; }
    get is_ObjectValue() { return this.$tag === 4; }
    get dtor_stringValue() { return this.stringValue; }
    get dtor_intValue() { return this.intValue; }
    get dtor_boolValue() { return this.boolValue; }
    get dtor_values() { return this.values; }
    get dtor_fields() { return this.fields; }
    toString() {
      if (this.$tag === 0) {
        return "Variables.VariableValue.StringValue" + "(" + this.stringValue.toVerbatimString(true) + ")";
      } else if (this.$tag === 1) {
        return "Variables.VariableValue.IntValue" + "(" + _dafny.toString(this.intValue) + ")";
      } else if (this.$tag === 2) {
        return "Variables.VariableValue.BoolValue" + "(" + _dafny.toString(this.boolValue) + ")";
      } else if (this.$tag === 3) {
        return "Variables.VariableValue.ListValue" + "(" + _dafny.toString(this.values) + ")";
      } else if (this.$tag === 4) {
        return "Variables.VariableValue.ObjectValue" + "(" + _dafny.toString(this.fields) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.stringValue, other.stringValue);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.intValue, other.intValue);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && this.boolValue === other.boolValue;
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.values, other.values);
      } else if (this.$tag === 4) {
        return other.$tag === 4 && _dafny.areEqual(this.fields, other.fields);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return Variables.VariableValue.create_StringValue(_dafny.Seq.UnicodeFromString(""));
    }
    static Rtd() {
      return class {
        static get Default() {
          return VariableValue.Default();
        }
      };
    }
  }
  return $module;
})(); // end of module Variables
let Seq = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Seq._default";
    }
    _parentTraits() {
      return [];
    }
    static First(xs) {
      return (xs)[_dafny.ZERO];
    };
    static DropFirst(xs) {
      return (xs).slice(_dafny.ONE);
    };
    static Last(xs) {
      return (xs)[(new BigNumber((xs).length)).minus(_dafny.ONE)];
    };
    static DropLast(xs) {
      return (xs).slice(0, (new BigNumber((xs).length)).minus(_dafny.ONE));
    };
    static Filter(f, xs) {
      let _0___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((xs).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_0___accumulator, _dafny.Seq.of());
        } else {
          _0___accumulator = _dafny.Seq.Concat(_0___accumulator, (((f)((xs)[_dafny.ZERO])) ? (_dafny.Seq.of((xs)[_dafny.ZERO])) : (_dafny.Seq.of())));
          let _in0 = f;
          let _in1 = (xs).slice(_dafny.ONE);
          f = _in0;
          xs = _in1;
          continue TAIL_CALL_START;
        }
      }
    };
  };
  return $module;
})(); // end of module Seq
let ExecutionContext = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "ExecutionContext._default";
    }
    _parentTraits() {
      return [];
    }
    static CreateInitialContext() {
      return ExecutionContext.Context.create_ExecutionContext(_dafny.Seq.UnicodeFromString(""), _dafny.ZERO, _dafny.Seq.of());
    };
    static InitializeExecutionQueue(context, activeTokens) {
      let _0_tokenSequence = ExecutionContext.__default.SetToSequence(activeTokens);
      let _1_dt__update__tmp_h0 = context;
      let _2_dt__update_hexecutionQueue_h0 = _0_tokenSequence;
      return ExecutionContext.Context.create_ExecutionContext((_1_dt__update__tmp_h0).dtor_lastExecutedNode, (_1_dt__update__tmp_h0).dtor_executionStep, _2_dt__update_hexecutionQueue_h0);
    };
    static EnqueueToken(context, tokenId) {
      let _0_dt__update__tmp_h0 = context;
      let _1_dt__update_hexecutionQueue_h0 = _dafny.Seq.Concat((context).dtor_executionQueue, _dafny.Seq.of(tokenId));
      return ExecutionContext.Context.create_ExecutionContext((_0_dt__update__tmp_h0).dtor_lastExecutedNode, (_0_dt__update__tmp_h0).dtor_executionStep, _1_dt__update_hexecutionQueue_h0);
    };
    static DequeueToken(context) {
      let _0_tokenId = Seq.__default.First((context).dtor_executionQueue);
      let _1_newQueue = Seq.__default.DropFirst((context).dtor_executionQueue);
      let _2_newContext = function (_pat_let33_0) {
        return function (_3_dt__update__tmp_h0) {
          return function (_pat_let34_0) {
            return function (_4_dt__update_hexecutionQueue_h0) {
              return ExecutionContext.Context.create_ExecutionContext((_3_dt__update__tmp_h0).dtor_lastExecutedNode, (_3_dt__update__tmp_h0).dtor_executionStep, _4_dt__update_hexecutionQueue_h0);
            }(_pat_let34_0);
          }(_1_newQueue);
        }(_pat_let33_0);
      }(context);
      return _dafny.Tuple.of(_2_newContext, _0_tokenId);
    };
    static PeekFirstToken(context) {
      return Seq.__default.First((context).dtor_executionQueue);
    };
    static PeekLastToken(context) {
      return Seq.__default.Last((context).dtor_executionQueue);
    };
    static FilterExecutionQueue(context, isValid) {
      return ExecutionContext.__default.FilterExecutionQueueHelper((context).dtor_executionQueue, isValid);
    };
    static FilterExecutionQueueHelper(queue, isValid) {
      if ((new BigNumber((queue).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.of();
      } else {
        let _0_first = (queue)[_dafny.ZERO];
        let _1_rest = ExecutionContext.__default.FilterExecutionQueueHelper((queue).slice(_dafny.ONE), isValid);
        if ((isValid)(_0_first)) {
          return _dafny.Seq.Concat(_dafny.Seq.of(_0_first), _1_rest);
        } else {
          return _1_rest;
        }
      }
    };
    static IsExecutionQueueEmpty(context) {
      return (new BigNumber(((context).dtor_executionQueue).length)).isEqualTo(_dafny.ZERO);
    };
    static SetToSequence(s) {
      let _0___accumulator = _dafny.Seq.of();
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((s).length)).isEqualTo(_dafny.ZERO)) {
          return _dafny.Seq.Concat(_0___accumulator, _dafny.Seq.of());
        } else {
          let _1_x = Token.__default.PickOne(s);
          _0___accumulator = _dafny.Seq.Concat(_0___accumulator, _dafny.Seq.of(_1_x));
          let _in0 = (s).Difference(_dafny.Set.fromElements(_1_x));
          s = _in0;
          continue TAIL_CALL_START;
        }
      }
    };
    static GetCurrentNodes(tokenCollection) {
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of (Token.__default.GetActiveTokens(tokenCollection)).Elements) {
          let _0_tokenId = _compr_0;
          if ((Token.__default.GetActiveTokens(tokenCollection)).contains(_0_tokenId)) {
            _coll0.add((((tokenCollection).dtor_tokens).get(_0_tokenId)).dtor_location);
          }
        }
        return _coll0;
      }();
    };
    static ComputeContext(tokenCollection, lastExecutedNode, previousContext) {
      let _0_activeTokens = Token.__default.GetActiveTokens(tokenCollection);
      let _1_tokenSequence = ExecutionContext.__default.SetToSequence(_0_activeTokens);
      return ExecutionContext.Context.create_ExecutionContext(lastExecutedNode, ((previousContext).dtor_executionStep).plus(_dafny.ONE), _1_tokenSequence);
    };
    static ValidContext(context) {
      return (_dafny.ZERO).isLessThanOrEqualTo((context).dtor_executionStep);
    };
    static ValidContextWithTokens(context, tokenCollection) {
      return (((ExecutionContext.__default.ValidContext(context)) && (_dafny.Quantifier(((context).dtor_executionQueue).UniqueElements, true, function (_forall_var_0) {
        let _0_tokenId = _forall_var_0;
        return !(_dafny.Seq.contains((context).dtor_executionQueue, _0_tokenId)) || (((tokenCollection).dtor_tokens).contains(_0_tokenId));
      }))) && (_dafny.Quantifier(((context).dtor_executionQueue).UniqueElements, true, function (_forall_var_1) {
        let _1_tokenId = _forall_var_1;
        return !(_dafny.Seq.contains((context).dtor_executionQueue, _1_tokenId)) || (_dafny.areEqual((((tokenCollection).dtor_tokens).get(_1_tokenId)).dtor_status, Token.TokenStatus.create_Active()));
      }))) && (_dafny.Quantifier(((tokenCollection).dtor_tokens).Keys.Elements, true, function (_forall_var_2) {
        let _2_tokenId = _forall_var_2;
        return !((((tokenCollection).dtor_tokens).contains(_2_tokenId)) && (_dafny.areEqual((((tokenCollection).dtor_tokens).get(_2_tokenId)).dtor_status, Token.TokenStatus.create_Active()))) || (_dafny.Seq.contains((context).dtor_executionQueue, _2_tokenId));
      }));
    };
    static CreateConsistentContext(tokenCollection, lastExecutedNode, executionStep) {
      let _0_activeTokens = Token.__default.GetActiveTokens(tokenCollection);
      let _1_tokenSequence = ExecutionContext.__default.SetToSequence(_0_activeTokens);
      return ExecutionContext.Context.create_ExecutionContext(lastExecutedNode, executionStep, _1_tokenSequence);
    };
    static SafeEnqueueToken(context, tokenId, tokenCollection) {
      let _0_dt__update__tmp_h0 = context;
      let _1_dt__update_hexecutionQueue_h0 = _dafny.Seq.Concat((context).dtor_executionQueue, _dafny.Seq.of(tokenId));
      return ExecutionContext.Context.create_ExecutionContext((_0_dt__update__tmp_h0).dtor_lastExecutedNode, (_0_dt__update__tmp_h0).dtor_executionStep, _1_dt__update_hexecutionQueue_h0);
    };
    static SafeDequeueToken(context, tokenCollection) {
      let _0_tokenId = Seq.__default.First((context).dtor_executionQueue);
      let _1_newQueue = Seq.__default.DropFirst((context).dtor_executionQueue);
      let _2_newContext = function (_pat_let35_0) {
        return function (_3_dt__update__tmp_h0) {
          return function (_pat_let36_0) {
            return function (_4_dt__update_hexecutionQueue_h0) {
              return ExecutionContext.Context.create_ExecutionContext((_3_dt__update__tmp_h0).dtor_lastExecutedNode, (_3_dt__update__tmp_h0).dtor_executionStep, _4_dt__update_hexecutionQueue_h0);
            }(_pat_let36_0);
          }(_1_newQueue);
        }(_pat_let35_0);
      }(context);
      return _dafny.Tuple.of(_2_newContext, _0_tokenId);
    };
  };

  $module.Context = class Context {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_ExecutionContext(lastExecutedNode, executionStep, executionQueue) {
      let $dt = new Context(0);
      $dt.lastExecutedNode = lastExecutedNode;
      $dt.executionStep = executionStep;
      $dt.executionQueue = executionQueue;
      return $dt;
    }
    get is_ExecutionContext() { return this.$tag === 0; }
    get dtor_lastExecutedNode() { return this.lastExecutedNode; }
    get dtor_executionStep() { return this.executionStep; }
    get dtor_executionQueue() { return this.executionQueue; }
    toString() {
      if (this.$tag === 0) {
        return "ExecutionContext.Context.ExecutionContext" + "(" + this.lastExecutedNode.toVerbatimString(true) + ", " + _dafny.toString(this.executionStep) + ", " + _dafny.toString(this.executionQueue) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.lastExecutedNode, other.lastExecutedNode) && _dafny.areEqual(this.executionStep, other.executionStep) && _dafny.areEqual(this.executionQueue, other.executionQueue);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return ExecutionContext.Context.create_ExecutionContext(_dafny.Seq.UnicodeFromString(""), _dafny.ZERO, _dafny.Seq.of());
    }
    static Rtd() {
      return class {
        static get Default() {
          return Context.Default();
        }
      };
    }
  }
  return $module;
})(); // end of module ExecutionContext
let BPMNState = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "BPMNState._default";
    }
    _parentTraits() {
      return [];
    }
    static ValidState(state) {
      let _source0 = state;
      {
        if (_source0.is_NotStarted) {
          let _0_processDefinition = (_source0).processDefinition;
          let _1_initialVariables = (_source0).initialVariables;
          return BPMNState.__default.ValidProcessDefinition(_0_processDefinition);
        }
      }
      {
        if (_source0.is_Running) {
          let _2_process = (_source0).process;
          return ((Token.__default.HasActiveTokens((_2_process).dtor_tokenCollection)) && (Token.__default.ValidTokenCollection((_2_process).dtor_tokenCollection))) && (BPMNState.__default.ValidProcessState(_2_process));
        }
      }
      {
        if (_source0.is_Completed) {
          let _3_process = (_source0).process;
          return ((!(Token.__default.HasActiveTokens((_3_process).dtor_tokenCollection))) && (Token.__default.ValidTokenCollection((_3_process).dtor_tokenCollection))) && (BPMNState.__default.ValidProcessState(_3_process));
        }
      }
      {
        if (_source0.is_Terminated) {
          let _4_process = (_source0).process;
          return (Token.__default.ValidTokenCollection((_4_process).dtor_tokenCollection)) && (BPMNState.__default.ValidProcessState(_4_process));
        }
      }
      {
        let _5_process = (_source0).process;
        return true;
      }
    };
    static ValidProcessState(process) {
      return (((_dafny.Quantifier((Token.__default.GetActiveTokens((process).dtor_tokenCollection)).Elements, true, function (_forall_var_0) {
        let _0_tokenId = _forall_var_0;
        return !((Token.__default.GetActiveTokens((process).dtor_tokenCollection)).contains(_0_tokenId)) || (((((process).dtor_tokenCollection).dtor_tokens).contains(_0_tokenId)) && ((((process).dtor_processDefinition).dtor_nodes).contains(((((process).dtor_tokenCollection).dtor_tokens).get(_0_tokenId)).dtor_location)));
      })) && (_dafny.Quantifier((((process).dtor_context).dtor_executionQueue).UniqueElements, true, function (_forall_var_1) {
        let _1_tokenId = _forall_var_1;
        return !(_dafny.Seq.contains(((process).dtor_context).dtor_executionQueue, _1_tokenId)) || (((((process).dtor_tokenCollection).dtor_tokens).contains(_1_tokenId)) && (_dafny.areEqual(((((process).dtor_tokenCollection).dtor_tokens).get(_1_tokenId)).dtor_status, Token.TokenStatus.create_Active())));
      }))) && (_dafny.Quantifier((Token.__default.GetActiveTokens((process).dtor_tokenCollection)).Elements, true, function (_forall_var_2) {
        let _2_tokenId = _forall_var_2;
        return !((Token.__default.GetActiveTokens((process).dtor_tokenCollection)).contains(_2_tokenId)) || (_dafny.Seq.contains(((process).dtor_context).dtor_executionQueue, _2_tokenId));
      }))) && (ExecutionContext.__default.ValidContext((process).dtor_context));
    };
    static ValidProcessDefinition(processDefinition) {
      let _pat_let_tv0 = processDefinition;
      let _pat_let_tv1 = processDefinition;
      return (((((((_dafny.ZERO).isLessThan(new BigNumber(((processDefinition).dtor_startNodes).length))) && ((_dafny.ZERO).isLessThan(new BigNumber(((processDefinition).dtor_endNodes).length)))) && (_dafny.Quantifier(((processDefinition).dtor_startNodes).Elements, true, function (_forall_var_0) {
        let _0_nodeId = _forall_var_0;
        return !(((processDefinition).dtor_startNodes).contains(_0_nodeId)) || (((processDefinition).dtor_nodes).contains(_0_nodeId));
      }))) && (_dafny.Quantifier(((processDefinition).dtor_endNodes).Elements, true, function (_forall_var_1) {
        let _1_nodeId = _forall_var_1;
        return !(((processDefinition).dtor_endNodes).contains(_1_nodeId)) || (((processDefinition).dtor_nodes).contains(_1_nodeId));
      }))) && (_dafny.Quantifier(((processDefinition).dtor_flows).Keys.Elements, true, function (_forall_var_2) {
        let _2_flowId = _forall_var_2;
        return !(((processDefinition).dtor_flows).contains(_2_flowId)) || (function (_pat_let37_0) {
          return function (_3_flow) {
            return (((_pat_let_tv0).dtor_nodes).contains((_3_flow).dtor_sourceRef)) && (((_pat_let_tv1).dtor_nodes).contains((_3_flow).dtor_targetRef));
          }(_pat_let37_0);
        }(((processDefinition).dtor_flows).get(_2_flowId)));
      }))) && (_dafny.Quantifier(((processDefinition).dtor_nodes).Keys.Elements, true, function (_forall_var_3) {
        let _4_nodeId = _forall_var_3;
        return !(((processDefinition).dtor_nodes).contains(_4_nodeId)) || (_dafny.Quantifier(((((processDefinition).dtor_nodes).get(_4_nodeId)).dtor_outgoing).Elements, true, function (_forall_var_4) {
          let _5_flowId = _forall_var_4;
          return !(((((processDefinition).dtor_nodes).get(_4_nodeId)).dtor_outgoing).contains(_5_flowId)) || (((processDefinition).dtor_flows).contains(_5_flowId));
        }));
      }))) && (_dafny.Quantifier(((processDefinition).dtor_nodes).Keys.Elements, true, function (_forall_var_5) {
        let _6_nodeId = _forall_var_5;
        return !(((processDefinition).dtor_nodes).contains(_6_nodeId)) || (_dafny.Quantifier(((((processDefinition).dtor_nodes).get(_6_nodeId)).dtor_incoming).Elements, true, function (_forall_var_6) {
          let _7_flowId = _forall_var_6;
          return !(((((processDefinition).dtor_nodes).get(_6_nodeId)).dtor_incoming).contains(_7_flowId)) || (((processDefinition).dtor_flows).contains(_7_flowId));
        }));
      }));
    };
    static CreateInitialState(processDefinition, initialVariables) {
      return BPMNState.State.create_NotStarted(processDefinition, initialVariables);
    };
    static CanComplete(state) {
      let _0_process = (state).dtor_process;
      let _1_activeTokens = Token.__default.GetActiveTokens((_0_process).dtor_tokenCollection);
      return _dafny.Quantifier((_1_activeTokens).Elements, true, function (_forall_var_0) {
        let _2_tokenId = _forall_var_0;
        return !((_1_activeTokens).contains(_2_tokenId)) || ((((_0_process).dtor_processDefinition).dtor_endNodes).contains(((((_0_process).dtor_tokenCollection).dtor_tokens).get(_2_tokenId)).dtor_location));
      });
    };
    static CreateDummyProcessDef() {
      return ProcessDefinition.ProcessDef.create_ProcessDefinition(_dafny.Seq.UnicodeFromString("dummy"), _dafny.Seq.UnicodeFromString("dummy"), _dafny.Map.Empty.slice().updateUnsafe(_dafny.Seq.UnicodeFromString("start"),ProcessDefinition.Node.create_ProcessNode(_dafny.Seq.UnicodeFromString("start"), _dafny.Seq.UnicodeFromString("start"), ProcessDefinition.NodeType.create_StartEvent(), _dafny.Set.fromElements(), _dafny.Set.fromElements())), _dafny.Map.Empty.slice(), _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("start")), _dafny.Set.fromElements());
    };
    static GetCurrentLocations(state) {
      return ExecutionContext.__default.GetCurrentNodes(((state).dtor_process).dtor_tokenCollection);
    };
    static GetPrimaryLocation(state) {
      let _0_process = (state).dtor_process;
      let _1_activeTokens = Token.__default.GetActiveTokens((_0_process).dtor_tokenCollection);
      if ((new BigNumber((_1_activeTokens).length)).isEqualTo(_dafny.ONE)) {
        let _2_tokenId = Token.__default.PickOne(_1_activeTokens);
        return Optional.Option.create_Some(((((_0_process).dtor_tokenCollection).dtor_tokens).get(_2_tokenId)).dtor_location);
      } else {
        return Optional.Option.create_None();
      }
    };
    static IsAtNode(state, nodeId) {
      let _0_currentNodes = ExecutionContext.__default.GetCurrentNodes(((state).dtor_process).dtor_tokenCollection);
      return (_0_currentNodes).contains(nodeId);
    };
    static UpdateProcessContext(process, lastExecutedNode) {
      let _0_updatedContext = ExecutionContext.__default.CreateConsistentContext((process).dtor_tokenCollection, lastExecutedNode, ((process).dtor_context).dtor_executionStep);
      return BPMNState.ProcessObj.create_Process((process).dtor_processId, (process).dtor_tokenCollection, (process).dtor_globalVariables, (process).dtor_processDefinition, (process).dtor_executionHistory, _0_updatedContext);
    };
    static CreateDeadlockError(process, details) {
      return BPMNState.State.create_Error(process, BPMNState.ErrorCode.create_DeadlockError(details));
    };
    static CreateTokenError(process, tokenId, message) {
      return BPMNState.State.create_Error(process, BPMNState.ErrorCode.create_TokenError(tokenId, message));
    };
    static CreateExecutionError(process, nodeId, message) {
      return BPMNState.State.create_Error(process, BPMNState.ErrorCode.create_ExecutionError(nodeId, message));
    };
    static CreateFlowError(process, flowId, message) {
      return BPMNState.State.create_Error(process, BPMNState.ErrorCode.create_FlowError(flowId, message));
    };
    static CreateValidationError(process, message) {
      return BPMNState.State.create_Error(process, BPMNState.ErrorCode.create_ValidationError(message));
    };
    static CreateRuntimeError(process, message) {
      return BPMNState.State.create_Error(process, BPMNState.ErrorCode.create_RuntimeError(message));
    };
    static get BPMN__PROCESS__WITNESS() {
      return BPMNState.ProcessObj.create_Process(_dafny.Seq.UnicodeFromString("witness"), Token.__default.Create(), Variables.__default.EmptyVariables(), BPMNState.__default.CreateDummyProcessDef(), _dafny.Seq.of(), ExecutionContext.__default.CreateInitialContext());
    };
    static get BPMN__RUNNING__PROCESS__WITNESS() {
      let _0_emptyTokens = Token.__default.Create();
      let _let_tmp_rhs0 = Token.__default.CreateToken(_0_emptyTokens, _dafny.Seq.UnicodeFromString("start"));
      let _1_tokensWithOne = (_let_tmp_rhs0)[0];
      let _2_tokenId = (_let_tmp_rhs0)[1];
      let _3_consistentContext = ExecutionContext.__default.CreateConsistentContext(_1_tokensWithOne, _dafny.Seq.UnicodeFromString("start"), _dafny.ZERO);
      return BPMNState.ProcessObj.create_Process(_dafny.Seq.UnicodeFromString("witness"), _1_tokensWithOne, Variables.__default.EmptyVariables(), BPMNState.__default.CreateDummyProcessDef(), _dafny.Seq.of(), _3_consistentContext);
    };
  };

  $module.ErrorCode = class ErrorCode {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_ValidationError(message) {
      let $dt = new ErrorCode(0);
      $dt.message = message;
      return $dt;
    }
    static create_RuntimeError(message) {
      let $dt = new ErrorCode(1);
      $dt.message = message;
      return $dt;
    }
    static create_TimeoutError(message) {
      let $dt = new ErrorCode(2);
      $dt.message = message;
      return $dt;
    }
    static create_ResourceError(message) {
      let $dt = new ErrorCode(3);
      $dt.message = message;
      return $dt;
    }
    static create_DeadlockError(details) {
      let $dt = new ErrorCode(4);
      $dt.details = details;
      return $dt;
    }
    static create_ExecutionError(nodeId, message) {
      let $dt = new ErrorCode(5);
      $dt.nodeId = nodeId;
      $dt.message = message;
      return $dt;
    }
    static create_FlowError(flowId, message) {
      let $dt = new ErrorCode(6);
      $dt.flowId = flowId;
      $dt.message = message;
      return $dt;
    }
    static create_TokenError(tokenId, message) {
      let $dt = new ErrorCode(7);
      $dt.tokenId = tokenId;
      $dt.message = message;
      return $dt;
    }
    static create_DefinitionError(message) {
      let $dt = new ErrorCode(8);
      $dt.message = message;
      return $dt;
    }
    get is_ValidationError() { return this.$tag === 0; }
    get is_RuntimeError() { return this.$tag === 1; }
    get is_TimeoutError() { return this.$tag === 2; }
    get is_ResourceError() { return this.$tag === 3; }
    get is_DeadlockError() { return this.$tag === 4; }
    get is_ExecutionError() { return this.$tag === 5; }
    get is_FlowError() { return this.$tag === 6; }
    get is_TokenError() { return this.$tag === 7; }
    get is_DefinitionError() { return this.$tag === 8; }
    get dtor_message() { return this.message; }
    get dtor_details() { return this.details; }
    get dtor_nodeId() { return this.nodeId; }
    get dtor_flowId() { return this.flowId; }
    get dtor_tokenId() { return this.tokenId; }
    toString() {
      if (this.$tag === 0) {
        return "BPMNState.ErrorCode.ValidationError" + "(" + this.message.toVerbatimString(true) + ")";
      } else if (this.$tag === 1) {
        return "BPMNState.ErrorCode.RuntimeError" + "(" + this.message.toVerbatimString(true) + ")";
      } else if (this.$tag === 2) {
        return "BPMNState.ErrorCode.TimeoutError" + "(" + this.message.toVerbatimString(true) + ")";
      } else if (this.$tag === 3) {
        return "BPMNState.ErrorCode.ResourceError" + "(" + this.message.toVerbatimString(true) + ")";
      } else if (this.$tag === 4) {
        return "BPMNState.ErrorCode.DeadlockError" + "(" + this.details.toVerbatimString(true) + ")";
      } else if (this.$tag === 5) {
        return "BPMNState.ErrorCode.ExecutionError" + "(" + this.nodeId.toVerbatimString(true) + ", " + this.message.toVerbatimString(true) + ")";
      } else if (this.$tag === 6) {
        return "BPMNState.ErrorCode.FlowError" + "(" + this.flowId.toVerbatimString(true) + ", " + this.message.toVerbatimString(true) + ")";
      } else if (this.$tag === 7) {
        return "BPMNState.ErrorCode.TokenError" + "(" + _dafny.toString(this.tokenId) + ", " + this.message.toVerbatimString(true) + ")";
      } else if (this.$tag === 8) {
        return "BPMNState.ErrorCode.DefinitionError" + "(" + this.message.toVerbatimString(true) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.message, other.message);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.message, other.message);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.message, other.message);
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.message, other.message);
      } else if (this.$tag === 4) {
        return other.$tag === 4 && _dafny.areEqual(this.details, other.details);
      } else if (this.$tag === 5) {
        return other.$tag === 5 && _dafny.areEqual(this.nodeId, other.nodeId) && _dafny.areEqual(this.message, other.message);
      } else if (this.$tag === 6) {
        return other.$tag === 6 && _dafny.areEqual(this.flowId, other.flowId) && _dafny.areEqual(this.message, other.message);
      } else if (this.$tag === 7) {
        return other.$tag === 7 && _dafny.areEqual(this.tokenId, other.tokenId) && _dafny.areEqual(this.message, other.message);
      } else if (this.$tag === 8) {
        return other.$tag === 8 && _dafny.areEqual(this.message, other.message);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return BPMNState.ErrorCode.create_ValidationError(_dafny.Seq.UnicodeFromString(""));
    }
    static Rtd() {
      return class {
        static get Default() {
          return ErrorCode.Default();
        }
      };
    }
  }

  $module.ProcessObj = class ProcessObj {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Process(processId, tokenCollection, globalVariables, processDefinition, executionHistory, context) {
      let $dt = new ProcessObj(0);
      $dt.processId = processId;
      $dt.tokenCollection = tokenCollection;
      $dt.globalVariables = globalVariables;
      $dt.processDefinition = processDefinition;
      $dt.executionHistory = executionHistory;
      $dt.context = context;
      return $dt;
    }
    get is_Process() { return this.$tag === 0; }
    get dtor_processId() { return this.processId; }
    get dtor_tokenCollection() { return this.tokenCollection; }
    get dtor_globalVariables() { return this.globalVariables; }
    get dtor_processDefinition() { return this.processDefinition; }
    get dtor_executionHistory() { return this.executionHistory; }
    get dtor_context() { return this.context; }
    toString() {
      if (this.$tag === 0) {
        return "BPMNState.ProcessObj.Process" + "(" + this.processId.toVerbatimString(true) + ", " + _dafny.toString(this.tokenCollection) + ", " + _dafny.toString(this.globalVariables) + ", " + _dafny.toString(this.processDefinition) + ", " + _dafny.toString(this.executionHistory) + ", " + _dafny.toString(this.context) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.processId, other.processId) && _dafny.areEqual(this.tokenCollection, other.tokenCollection) && _dafny.areEqual(this.globalVariables, other.globalVariables) && _dafny.areEqual(this.processDefinition, other.processDefinition) && _dafny.areEqual(this.executionHistory, other.executionHistory) && _dafny.areEqual(this.context, other.context);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return BPMNState.ProcessObj.create_Process(_dafny.Seq.UnicodeFromString(""), Token.Collection.Default(), _dafny.Map.Empty, ProcessDefinition.ProcessDef.Default(), _dafny.Seq.of(), ExecutionContext.Context.Default());
    }
    static Rtd() {
      return class {
        static get Default() {
          return ProcessObj.Default();
        }
      };
    }
  }

  $module.State = class State {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_NotStarted(processDefinition, initialVariables) {
      let $dt = new State(0);
      $dt.processDefinition = processDefinition;
      $dt.initialVariables = initialVariables;
      return $dt;
    }
    static create_Running(process) {
      let $dt = new State(1);
      $dt.process = process;
      return $dt;
    }
    static create_Completed(process, output) {
      let $dt = new State(2);
      $dt.process = process;
      $dt.output = output;
      return $dt;
    }
    static create_Terminated(process) {
      let $dt = new State(3);
      $dt.process = process;
      return $dt;
    }
    static create_Error(process, errorCode) {
      let $dt = new State(4);
      $dt.process = process;
      $dt.errorCode = errorCode;
      return $dt;
    }
    get is_NotStarted() { return this.$tag === 0; }
    get is_Running() { return this.$tag === 1; }
    get is_Completed() { return this.$tag === 2; }
    get is_Terminated() { return this.$tag === 3; }
    get is_Error() { return this.$tag === 4; }
    get dtor_processDefinition() { return this.processDefinition; }
    get dtor_initialVariables() { return this.initialVariables; }
    get dtor_process() { return this.process; }
    get dtor_output() { return this.output; }
    get dtor_errorCode() { return this.errorCode; }
    toString() {
      if (this.$tag === 0) {
        return "BPMNState.State.NotStarted" + "(" + _dafny.toString(this.processDefinition) + ", " + _dafny.toString(this.initialVariables) + ")";
      } else if (this.$tag === 1) {
        return "BPMNState.State.Running" + "(" + _dafny.toString(this.process) + ")";
      } else if (this.$tag === 2) {
        return "BPMNState.State.Completed" + "(" + _dafny.toString(this.process) + ", " + _dafny.toString(this.output) + ")";
      } else if (this.$tag === 3) {
        return "BPMNState.State.Terminated" + "(" + _dafny.toString(this.process) + ")";
      } else if (this.$tag === 4) {
        return "BPMNState.State.Error" + "(" + _dafny.toString(this.process) + ", " + _dafny.toString(this.errorCode) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.processDefinition, other.processDefinition) && _dafny.areEqual(this.initialVariables, other.initialVariables);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.process, other.process);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.process, other.process) && _dafny.areEqual(this.output, other.output);
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.process, other.process);
      } else if (this.$tag === 4) {
        return other.$tag === 4 && _dafny.areEqual(this.process, other.process) && _dafny.areEqual(this.errorCode, other.errorCode);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return BPMNState.State.create_NotStarted(ProcessDefinition.ProcessDef.Default(), _dafny.Map.Empty);
    }
    static Rtd() {
      return class {
        static get Default() {
          return State.Default();
        }
      };
    }
  }

  $module.WaitCondition = class WaitCondition {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_MessageWait(messageType) {
      let $dt = new WaitCondition(0);
      $dt.messageType = messageType;
      return $dt;
    }
    static create_TimerWait(duration) {
      let $dt = new WaitCondition(1);
      $dt.duration = duration;
      return $dt;
    }
    static create_UserTaskWait(taskId) {
      let $dt = new WaitCondition(2);
      $dt.taskId = taskId;
      return $dt;
    }
    static create_ExternalServiceWait(serviceId) {
      let $dt = new WaitCondition(3);
      $dt.serviceId = serviceId;
      return $dt;
    }
    get is_MessageWait() { return this.$tag === 0; }
    get is_TimerWait() { return this.$tag === 1; }
    get is_UserTaskWait() { return this.$tag === 2; }
    get is_ExternalServiceWait() { return this.$tag === 3; }
    get dtor_messageType() { return this.messageType; }
    get dtor_duration() { return this.duration; }
    get dtor_taskId() { return this.taskId; }
    get dtor_serviceId() { return this.serviceId; }
    toString() {
      if (this.$tag === 0) {
        return "BPMNState.WaitCondition.MessageWait" + "(" + this.messageType.toVerbatimString(true) + ")";
      } else if (this.$tag === 1) {
        return "BPMNState.WaitCondition.TimerWait" + "(" + _dafny.toString(this.duration) + ")";
      } else if (this.$tag === 2) {
        return "BPMNState.WaitCondition.UserTaskWait" + "(" + this.taskId.toVerbatimString(true) + ")";
      } else if (this.$tag === 3) {
        return "BPMNState.WaitCondition.ExternalServiceWait" + "(" + this.serviceId.toVerbatimString(true) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.messageType, other.messageType);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.duration, other.duration);
      } else if (this.$tag === 2) {
        return other.$tag === 2 && _dafny.areEqual(this.taskId, other.taskId);
      } else if (this.$tag === 3) {
        return other.$tag === 3 && _dafny.areEqual(this.serviceId, other.serviceId);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return BPMNState.WaitCondition.create_MessageWait(_dafny.Seq.UnicodeFromString(""));
    }
    static Rtd() {
      return class {
        static get Default() {
          return WaitCondition.Default();
        }
      };
    }
  }

  $module.ExecutionEvent = class ExecutionEvent {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Event(timestamp, nodeId, eventType, tokenId, data) {
      let $dt = new ExecutionEvent(0);
      $dt.timestamp = timestamp;
      $dt.nodeId = nodeId;
      $dt.eventType = eventType;
      $dt.tokenId = tokenId;
      $dt.data = data;
      return $dt;
    }
    get is_Event() { return this.$tag === 0; }
    get dtor_timestamp() { return this.timestamp; }
    get dtor_nodeId() { return this.nodeId; }
    get dtor_eventType() { return this.eventType; }
    get dtor_tokenId() { return this.tokenId; }
    get dtor_data() { return this.data; }
    toString() {
      if (this.$tag === 0) {
        return "BPMNState.ExecutionEvent.Event" + "(" + _dafny.toString(this.timestamp) + ", " + this.nodeId.toVerbatimString(true) + ", " + _dafny.toString(this.eventType) + ", " + _dafny.toString(this.tokenId) + ", " + _dafny.toString(this.data) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.timestamp, other.timestamp) && _dafny.areEqual(this.nodeId, other.nodeId) && _dafny.areEqual(this.eventType, other.eventType) && _dafny.areEqual(this.tokenId, other.tokenId) && _dafny.areEqual(this.data, other.data);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return BPMNState.ExecutionEvent.create_Event(_dafny.ZERO, _dafny.Seq.UnicodeFromString(""), BPMNState.EventType.Default(), _dafny.ZERO, _dafny.Map.Empty);
    }
    static Rtd() {
      return class {
        static get Default() {
          return ExecutionEvent.Default();
        }
      };
    }
  }

  $module.EventType = class EventType {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_NodeEntered() {
      let $dt = new EventType(0);
      return $dt;
    }
    static create_NodeExited() {
      let $dt = new EventType(1);
      return $dt;
    }
    static create_TokenCreated() {
      let $dt = new EventType(2);
      return $dt;
    }
    static create_TokenConsumed() {
      let $dt = new EventType(3);
      return $dt;
    }
    static create_VariableUpdated() {
      let $dt = new EventType(4);
      return $dt;
    }
    static create_ErrorOccurred() {
      let $dt = new EventType(5);
      return $dt;
    }
    get is_NodeEntered() { return this.$tag === 0; }
    get is_NodeExited() { return this.$tag === 1; }
    get is_TokenCreated() { return this.$tag === 2; }
    get is_TokenConsumed() { return this.$tag === 3; }
    get is_VariableUpdated() { return this.$tag === 4; }
    get is_ErrorOccurred() { return this.$tag === 5; }
    static get AllSingletonConstructors() {
      return this.AllSingletonConstructors_();
    }
    static *AllSingletonConstructors_() {
      yield EventType.create_NodeEntered();
      yield EventType.create_NodeExited();
      yield EventType.create_TokenCreated();
      yield EventType.create_TokenConsumed();
      yield EventType.create_VariableUpdated();
      yield EventType.create_ErrorOccurred();
    }
    toString() {
      if (this.$tag === 0) {
        return "BPMNState.EventType.NodeEntered";
      } else if (this.$tag === 1) {
        return "BPMNState.EventType.NodeExited";
      } else if (this.$tag === 2) {
        return "BPMNState.EventType.TokenCreated";
      } else if (this.$tag === 3) {
        return "BPMNState.EventType.TokenConsumed";
      } else if (this.$tag === 4) {
        return "BPMNState.EventType.VariableUpdated";
      } else if (this.$tag === 5) {
        return "BPMNState.EventType.ErrorOccurred";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1;
      } else if (this.$tag === 2) {
        return other.$tag === 2;
      } else if (this.$tag === 3) {
        return other.$tag === 3;
      } else if (this.$tag === 4) {
        return other.$tag === 4;
      } else if (this.$tag === 5) {
        return other.$tag === 5;
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return BPMNState.EventType.create_NodeEntered();
    }
    static Rtd() {
      return class {
        static get Default() {
          return EventType.Default();
        }
      };
    }
  }

  $module.ExecutingState = class ExecutingState {
    constructor () {
    }
    static get Witness() {
      return BPMNState.State.create_Running(BPMNState.__default.BPMN__RUNNING__PROCESS__WITNESS);
    }
    static get Default() {
      return BPMNState.ExecutingState.Witness;
    }
    static _Is(__source) {
      let _4_s = __source;
      return ((_4_s).is_Running) && (Token.__default.HasActiveTokens(((_4_s).dtor_process).dtor_tokenCollection));
    }
  };

  $module.TerminatedState = class TerminatedState {
    constructor () {
    }
    static get Witness() {
      return BPMNState.State.create_Terminated(BPMNState.__default.BPMN__PROCESS__WITNESS);
    }
    static get Default() {
      return BPMNState.TerminatedState.Witness;
    }
    static _Is(__source) {
      let _5_s = __source;
      return (_5_s).is_Terminated;
    }
  };

  $module.CompletedState = class CompletedState {
    constructor () {
    }
    static get Witness() {
      return BPMNState.State.create_Completed(BPMNState.__default.BPMN__PROCESS__WITNESS, Variables.__default.EmptyVariables());
    }
    static get Default() {
      return BPMNState.CompletedState.Witness;
    }
    static _Is(__source) {
      let _6_s = __source;
      return ((_6_s).is_Completed) && (!(Token.__default.HasActiveTokens(((_6_s).dtor_process).dtor_tokenCollection)));
    }
  };
  return $module;
})(); // end of module BPMNState
let ExecutionInit = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "ExecutionInit._default";
    }
    _parentTraits() {
      return [];
    }
    static InitializeExecution(processDef) {
      let _0_emptyTokens = Token.__default.Create();
      let _1_startNodeId = ExecutionInit.__default.PickOneString((processDef).dtor_startNodes);
      let _let_tmp_rhs0 = Token.__default.CreateToken(_0_emptyTokens, _1_startNodeId);
      let _2_tokensWithStart = (_let_tmp_rhs0)[0];
      let _3_startTokenId = (_let_tmp_rhs0)[1];
      let _4_initialContext = ExecutionContext.__default.CreateConsistentContext(_2_tokensWithStart, _1_startNodeId, _dafny.ZERO);
      let _5_process = BPMNState.ProcessObj.create_Process(_dafny.Seq.Concat(_dafny.Seq.UnicodeFromString("instance-"), (processDef).dtor_id), _2_tokensWithStart, Variables.__default.EmptyVariables(), processDef, _dafny.Seq.of(), _4_initialContext);
      let _6_activeTokens = Token.__default.GetActiveTokens(_2_tokensWithStart);
      return BPMNState.State.create_Running(_5_process);
    };
    static ProcessStartEvent(state) {
      let _0_process = (state).dtor_process;
      let _1_activeTokens = Token.__default.GetActiveTokens((_0_process).dtor_tokenCollection);
      let _2_tokenId = Token.__default.PickOne(_1_activeTokens);
      let _3_tokensAfterConsume = Token.__default.ConsumeToken((_0_process).dtor_tokenCollection, _2_tokenId);
      let _4_currentLocation = ((((_0_process).dtor_tokenCollection).dtor_tokens).get(_2_tokenId)).dtor_location;
      let _5_outgoingFlows = ((((_0_process).dtor_processDefinition).dtor_nodes).get(_4_currentLocation)).dtor_outgoing;
      let _6_flowId = Token.__default.PickOne(_5_outgoingFlows);
      let _7_nextNodeId = ((((_0_process).dtor_processDefinition).dtor_flows).get(_6_flowId)).dtor_targetRef;
      let _let_tmp_rhs0 = Token.__default.CreateToken(_3_tokensAfterConsume, _7_nextNodeId);
      let _8_tokensWithNext = (_let_tmp_rhs0)[0];
      let _9_nextTokenId = (_let_tmp_rhs0)[1];
      let _10_newActiveTokens = Token.__default.GetActiveTokens(_8_tokensWithNext);
      let _11_updatedContext = ExecutionContext.__default.CreateConsistentContext(_8_tokensWithNext, _7_nextNodeId, (((_0_process).dtor_context).dtor_executionStep).plus(_dafny.ONE));
      let _12_newProcess = BPMNState.ProcessObj.create_Process((_0_process).dtor_processId, _8_tokensWithNext, (_0_process).dtor_globalVariables, (_0_process).dtor_processDefinition, (_0_process).dtor_executionHistory, _11_updatedContext);
      return BPMNState.State.create_Running(_12_newProcess);
    };
    static PickOneString(s) {
      return function (_let_dummy_38) {
        let _0_x = undefined;
        L_ASSIGN_SUCH_THAT_0: {
          for (const _assign_such_that_0 of (s).Elements) {
            _0_x = _assign_such_that_0;
            if ((s).contains(_0_x)) {
              break L_ASSIGN_SUCH_THAT_0;
            }
          }
          throw new Error("assign-such-that search produced no value");
        }
        return _0_x;
      }(0);
    };
    static CanStartProcess(processDefinition) {
      return ((((((((new BigNumber(((processDefinition).dtor_startNodes).length)).isEqualTo(_dafny.ONE)) && ((_dafny.ZERO).isLessThan(new BigNumber(((processDefinition).dtor_endNodes).length)))) && (_dafny.Quantifier(((processDefinition).dtor_startNodes).Elements, true, function (_forall_var_0) {
        let _0_startNodeId = _forall_var_0;
        return !(((processDefinition).dtor_startNodes).contains(_0_startNodeId)) || (((processDefinition).dtor_nodes).contains(_0_startNodeId));
      }))) && (_dafny.Quantifier(((processDefinition).dtor_endNodes).Elements, true, function (_forall_var_1) {
        let _1_endNodeId = _forall_var_1;
        return !(((processDefinition).dtor_endNodes).contains(_1_endNodeId)) || (((processDefinition).dtor_nodes).contains(_1_endNodeId));
      }))) && (_dafny.Quantifier(((processDefinition).dtor_startNodes).Elements, true, function (_forall_var_2) {
        let _2_startNodeId = _forall_var_2;
        return !(((processDefinition).dtor_startNodes).contains(_2_startNodeId)) || (((((processDefinition).dtor_nodes).get(_2_startNodeId)).dtor_incoming).equals(_dafny.Set.fromElements()));
      }))) && (_dafny.Quantifier(((processDefinition).dtor_startNodes).Elements, true, function (_forall_var_3) {
        let _3_startNodeId = _forall_var_3;
        return !(((processDefinition).dtor_startNodes).contains(_3_startNodeId)) || ((_dafny.ZERO).isLessThan(new BigNumber(((((processDefinition).dtor_nodes).get(_3_startNodeId)).dtor_outgoing).length)));
      }))) && (_dafny.Quantifier(((processDefinition).dtor_startNodes).Elements, true, function (_forall_var_4) {
        let _4_startNodeId = _forall_var_4;
        return !(((processDefinition).dtor_startNodes).contains(_4_startNodeId)) || (_dafny.Quantifier(((((processDefinition).dtor_nodes).get(_4_startNodeId)).dtor_outgoing).Elements, true, function (_forall_var_5) {
          let _5_flowId = _forall_var_5;
          return !(((((processDefinition).dtor_nodes).get(_4_startNodeId)).dtor_outgoing).contains(_5_flowId)) || (((processDefinition).dtor_flows).contains(_5_flowId));
        }));
      }))) && (_dafny.Quantifier(((processDefinition).dtor_endNodes).Elements, true, function (_forall_var_6) {
        let _6_endNodeId = _forall_var_6;
        return !(((processDefinition).dtor_endNodes).contains(_6_endNodeId)) || (((((processDefinition).dtor_nodes).get(_6_endNodeId)).dtor_outgoing).equals(_dafny.Set.fromElements()));
      }));
    };
    static CanExecuteStartEvent(state) {
      return ((((state).is_Running) && (Token.__default.HasActiveTokens(((state).dtor_process).dtor_tokenCollection))) && (BPMNState.__default.ValidProcessDefinition(((state).dtor_process).dtor_processDefinition))) && (ExecutionInit.__default.ValidStartEventExecution((state).dtor_process));
    };
    static ValidStartEventExecution(process) {
      return (((new BigNumber((((process).dtor_processDefinition).dtor_startNodes).length)).isEqualTo(_dafny.ONE)) && (ExecutionInit.__default.ValidActiveTokensAtStart(process))) && (ExecutionInit.__default.ValidFlowStructure(process));
    };
    static ValidActiveTokensAtStart(process) {
      return _dafny.Quantifier((Token.__default.GetActiveTokens((process).dtor_tokenCollection)).Elements, true, function (_forall_var_0) {
        let _0_tokenId = _forall_var_0;
        return !((Token.__default.GetActiveTokens((process).dtor_tokenCollection)).contains(_0_tokenId)) || ((((((process).dtor_tokenCollection).dtor_tokens).contains(_0_tokenId)) && ((((process).dtor_processDefinition).dtor_startNodes).contains(((((process).dtor_tokenCollection).dtor_tokens).get(_0_tokenId)).dtor_location))) && ((((process).dtor_processDefinition).dtor_nodes).contains(((((process).dtor_tokenCollection).dtor_tokens).get(_0_tokenId)).dtor_location)));
      });
    };
    static ValidFlowStructure(process) {
      let _pat_let_tv0 = process;
      let _pat_let_tv1 = process;
      let _pat_let_tv2 = process;
      let _pat_let_tv3 = process;
      let _pat_let_tv4 = process;
      return _dafny.Quantifier((Token.__default.GetActiveTokens((process).dtor_tokenCollection)).Elements, true, function (_forall_var_0) {
        let _0_tokenId = _forall_var_0;
        return !((Token.__default.GetActiveTokens((process).dtor_tokenCollection)).contains(_0_tokenId)) || (function (_pat_let39_0) {
          return function (_1_location) {
            return (((((_pat_let_tv0).dtor_processDefinition).dtor_nodes).contains(_1_location)) && ((_dafny.ZERO).isLessThan(new BigNumber((((((_pat_let_tv1).dtor_processDefinition).dtor_nodes).get(_1_location)).dtor_outgoing).length)))) && (_dafny.Quantifier((((((_pat_let_tv2).dtor_processDefinition).dtor_nodes).get(_1_location)).dtor_outgoing).Elements, true, function (_forall_var_1) {
              let _2_flowId = _forall_var_1;
              return !((((((_pat_let_tv3).dtor_processDefinition).dtor_nodes).get(_1_location)).dtor_outgoing).contains(_2_flowId)) || ((((_pat_let_tv4).dtor_processDefinition).dtor_flows).contains(_2_flowId));
            }));
          }(_pat_let39_0);
        }(((((process).dtor_tokenCollection).dtor_tokens).get(_0_tokenId)).dtor_location));
      });
    };
    static CanExecuteToken(state, tokenId) {
      let _pat_let_tv0 = state;
      let _0_token = ((((state).dtor_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _1_location = (_0_token).dtor_location;
      return (((((state).dtor_process).dtor_processDefinition).dtor_nodes).contains(_1_location)) && (function (_pat_let40_0) {
        return function (_2_node) {
          return function () {
            let _source0 = (_2_node).dtor_nodeType;
            {
              if (_source0.is_StartEvent) {
                return ExecutionInit.__default.CanExecuteStartEvent(_pat_let_tv0);
              }
            }
            {
              if (_source0.is_EndEvent) {
                return true;
              }
            }
            {
              if (_source0.is_Task) {
                return true;
              }
            }
            {
              if (_source0.is_Gateway) {
                return true;
              }
            }
            {
              return true;
            }
          }();
        }(_pat_let40_0);
      }(((((state).dtor_process).dtor_processDefinition).dtor_nodes).get(_1_location)));
    };
  };
  return $module;
})(); // end of module ExecutionInit
let Arrays = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "Arrays._default";
    }
    _parentTraits() {
      return [];
    }
    static IndexOf(xs, v) {
      let _0___accumulator = _dafny.ZERO;
      TAIL_CALL_START: while (true) {
        if (_dafny.areEqual((xs)[_dafny.ZERO], v)) {
          return (_dafny.ZERO).plus(_0___accumulator);
        } else {
          _0___accumulator = (_0___accumulator).plus(_dafny.ONE);
          let _in0 = (xs).slice(_dafny.ONE);
          let _in1 = v;
          xs = _in0;
          v = _in1;
          continue TAIL_CALL_START;
        }
      }
    };
    static EqualsExcept(lhs, rhs, address, length) {
      return (((new BigNumber((lhs).length)).isEqualTo(new BigNumber((rhs).length))) && (_dafny.areEqual((lhs).slice(0, address), (rhs).slice(0, address)))) && (_dafny.areEqual((lhs).slice((address).plus(length)), (rhs).slice((address).plus(length))));
    };
    static Copy(src, dst, start) {
      let _0_end = (start).plus(new BigNumber((src).length));
      return _dafny.Seq.Create(new BigNumber((dst).length), ((_1_start, _2_end, _3_src, _4_dst) => function (_5_i) {
        return ((((_1_start).isLessThanOrEqualTo(_5_i)) && ((_5_i).isLessThan(_2_end))) ? ((_3_src)[(_5_i).minus(_1_start)]) : ((_4_dst)[_5_i]));
      })(start, _0_end, src, dst));
    };
  };
  return $module;
})(); // end of module Arrays
let ExecutionEngine = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "ExecutionEngine._default";
    }
    _parentTraits() {
      return [];
    }
    static ExecuteStep(state) {
      let _0_process = (state).dtor_process;
      let _1_context = (_0_process).dtor_context;
      if ((new BigNumber(((_1_context).dtor_executionQueue).length)).isEqualTo(_dafny.ZERO)) {
        return BPMNState.State.create_Terminated(_0_process);
      } else {
        let _2_executableTokensFromQueue = ExecutionEngine.__default.GetExecutableTokensFromQueue(state);
        if ((new BigNumber((_2_executableTokensFromQueue).length)).isEqualTo(_dafny.ZERO)) {
          return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_DeadlockError(_dafny.Seq.UnicodeFromString("No tokens can be executed in current state")));
        } else {
          let _3_tokenToExecute = Seq.__default.First(_2_executableTokensFromQueue);
          return ExecutionEngine.__default.ExecuteTokenStep(state, _3_tokenToExecute);
        }
      }
    };
    static Execute(state) {
      while ((_dafny.ZERO).isLessThan(new BigNumber(((((state).dtor_process).dtor_context).dtor_executionQueue).length))) {
        let _0_process;
        _0_process = (state).dtor_process;
        let _let_tmp_rhs0 = ExecutionContext.__default.DequeueToken(((state).dtor_process).dtor_context);
        let _1_newContext = (_let_tmp_rhs0)[0];
        let _2_tokenId = (_let_tmp_rhs0)[1];
        let _3_token;
        _3_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(_2_tokenId);
        let _4_currentNode;
        _4_currentNode = (((_0_process).dtor_processDefinition).dtor_nodes).get((_3_token).dtor_location);
        let _5_newState;
        let _source0 = (_4_currentNode).dtor_nodeType;
        Lmatch0: {
          {
            if (_source0.is_StartEvent) {
              if (ExecutionInit.__default.CanExecuteStartEvent(state)) {
                _5_newState = ExecutionEngine.__default.ExecuteStartEvent(state);
              } else {
                _5_newState = state;
              }
              break Lmatch0;
            }
          }
          {
            if (_source0.is_EndEvent) {
              if ((state).is_Running) {
                _5_newState = ExecutionEngine.__default.ExecuteEndEvent(state, _2_tokenId);
              } else {
                _5_newState = BPMNState.State.create_Error((state).dtor_process, BPMNState.ErrorCode.create_ExecutionError((_3_token).dtor_location, _dafny.Seq.UnicodeFromString("Invalid state for EndEvent")));
              }
              break Lmatch0;
            }
          }
          {
            if (_source0.is_Task) {
              let _6_taskType = (_source0).taskType;
              _5_newState = ExecutionEngine.__default.ExecuteTask(state, _2_tokenId, _6_taskType);
              break Lmatch0;
            }
          }
          {
            if (_source0.is_Gateway) {
              let _7_gatewayType = (_source0).gatewayType;
              _5_newState = ExecutionEngine.__default.ExecuteGateway(state, _2_tokenId, _7_gatewayType);
              break Lmatch0;
            }
          }
          {
            let _8_eventType = (_source0).eventType;
            _5_newState = ExecutionEngine.__default.ExecuteIntermediateEvent(state, _2_tokenId, _8_eventType);
          }
        }
      }
      return;
    }
    static CanExecuteTokenImmediately(state, tokenId) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_location = (_1_token).dtor_location;
      if ((((_0_process).dtor_processDefinition).dtor_nodes).contains(_2_location)) {
        let _3_node = (((_0_process).dtor_processDefinition).dtor_nodes).get(_2_location);
        let _source0 = (_3_node).dtor_nodeType;
        {
          if (_source0.is_Gateway) {
            let gatewayType0 = (_source0).gatewayType;
            if (gatewayType0.is_ParallelGateway) {
              if ((_dafny.ONE).isLessThan(new BigNumber(((_3_node).dtor_incoming).length))) {
                let _4_tokensAtLocation = ExecutionEngine.__default.GetActiveTokensAtLocation((_0_process).dtor_tokenCollection, _2_location);
                return (new BigNumber((_4_tokensAtLocation).length)).isEqualTo(new BigNumber(((_3_node).dtor_incoming).length));
              } else {
                return true;
              }
            }
          }
        }
        {
          if (_source0.is_Gateway) {
            return true;
          }
        }
        {
          return true;
        }
      } else {
        return false;
      }
    };
    static GetImmediatelyExecutableTokens(state) {
      let _0_process = (state).dtor_process;
      let _1_context = (_0_process).dtor_context;
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of ((_1_context).dtor_executionQueue).Elements) {
          let _2_tokenId = _compr_0;
          if (_System.nat._Is(_2_tokenId)) {
            if ((((_dafny.Seq.contains((_1_context).dtor_executionQueue, _2_tokenId)) && ((((_0_process).dtor_tokenCollection).dtor_tokens).contains(_2_tokenId))) && (_dafny.areEqual(((((_0_process).dtor_tokenCollection).dtor_tokens).get(_2_tokenId)).dtor_status, Token.TokenStatus.create_Active()))) && (ExecutionEngine.__default.CanExecuteTokenImmediately(state, _2_tokenId))) {
              _coll0.add(_2_tokenId);
            }
          }
        }
        return _coll0;
      }();
    };
    static GetExecutableTokensFromQueue(state) {
      return ExecutionEngine.__default.FilterExecutableTokens((((state).dtor_process).dtor_context).dtor_executionQueue, state);
    };
    static FilterExecutableTokens(queue, state) {
      if ((new BigNumber((queue).length)).isEqualTo(_dafny.ZERO)) {
        return _dafny.Seq.of();
      } else {
        let _0_tokenId = Seq.__default.First(queue);
        let _1_rest = ExecutionEngine.__default.FilterExecutableTokens(Seq.__default.DropFirst(queue), state);
        if (((((((state).dtor_process).dtor_tokenCollection).dtor_tokens).contains(_0_tokenId)) && (_dafny.areEqual((((((state).dtor_process).dtor_tokenCollection).dtor_tokens).get(_0_tokenId)).dtor_status, Token.TokenStatus.create_Active()))) && (ExecutionEngine.__default.CanExecuteTokenImmediately(state, _0_tokenId))) {
          return _dafny.Seq.Concat(_dafny.Seq.of(_0_tokenId), _1_rest);
        } else {
          return _1_rest;
        }
      }
    };
    static ExecuteTokenStep(state, tokenId) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_currentNode = (((_0_process).dtor_processDefinition).dtor_nodes).get((_1_token).dtor_location);
      let _source0 = (_2_currentNode).dtor_nodeType;
      {
        if (_source0.is_StartEvent) {
          if (ExecutionInit.__default.CanExecuteStartEvent(state)) {
            return ExecutionEngine.__default.ExecuteStartEvent(state);
          } else {
            return state;
          }
        }
      }
      {
        if (_source0.is_EndEvent) {
          return ExecutionEngine.__default.ExecuteEndEvent(state, tokenId);
        }
      }
      {
        if (_source0.is_Task) {
          let _3_taskType = (_source0).taskType;
          return ExecutionEngine.__default.ExecuteTask(state, tokenId, _3_taskType);
        }
      }
      {
        if (_source0.is_Gateway) {
          let _4_gatewayType = (_source0).gatewayType;
          return ExecutionEngine.__default.ExecuteGateway(state, tokenId, _4_gatewayType);
        }
      }
      {
        let _5_eventType = (_source0).eventType;
        return ExecutionEngine.__default.ExecuteIntermediateEvent(state, tokenId, _5_eventType);
      }
    };
    static ExecuteStartEvent(state) {
      return ExecutionInit.__default.ProcessStartEvent(state);
    };
    static ExecuteEndEvent(state, tokenId) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_tokensAfterConsume = Token.__default.ConsumeToken((_0_process).dtor_tokenCollection, tokenId);
      let _3_newHistory = _dafny.Seq.Concat((_0_process).dtor_executionHistory, _dafny.Seq.of(BPMNState.ExecutionEvent.create_Event(_dafny.ZERO, (_1_token).dtor_location, BPMNState.EventType.create_NodeExited(), tokenId, Variables.__default.EmptyVariables())));
      let _4_updatedContext = ExecutionContext.__default.ComputeContext(_2_tokensAfterConsume, (_1_token).dtor_location, (_0_process).dtor_context);
      let _5_updatedProcess = BPMNState.ProcessObj.create_Process((_0_process).dtor_processId, _2_tokensAfterConsume, (_0_process).dtor_globalVariables, (_0_process).dtor_processDefinition, _3_newHistory, _4_updatedContext);
      let _6_remainingActiveTokens = Token.__default.GetActiveTokens(_2_tokensAfterConsume);
      if ((new BigNumber((_6_remainingActiveTokens).length)).isEqualTo(_dafny.ZERO)) {
        return BPMNState.State.create_Completed(_5_updatedProcess, (_0_process).dtor_globalVariables);
      } else {
        return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_ExecutionError((_1_token).dtor_location, _dafny.Seq.UnicodeFromString("Invalid state for EndEvent")));
      }
    };
    static ExecuteTask(state, tokenId, taskType) {
      let _source0 = taskType;
      {
        if (_source0.is_UserTask) {
          return ExecutionEngine.__default.ExecuteUserTask(state, tokenId);
        }
      }
      {
        if (_source0.is_ServiceTask) {
          return ExecutionEngine.__default.ExecuteServiceTask(state, tokenId);
        }
      }
      {
        let _0_ManualTask = _source0;
        return ExecutionEngine.__default.ExecuteManualTask(state, tokenId);
      }
    };
    static ExecuteGateway(state, tokenId, gatewayType) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_currentNode = (((_0_process).dtor_processDefinition).dtor_nodes).get((_1_token).dtor_location);
      let _3_outgoingFlows = (_2_currentNode).dtor_outgoing;
      let _4_incomingFlows = (_2_currentNode).dtor_incoming;
      let _source0 = gatewayType;
      {
        if (_source0.is_ParallelGateway) {
          if ((_dafny.ONE).isLessThan(new BigNumber((_3_outgoingFlows).length))) {
            if (ExecutionEngine.__default.CanExecuteParallelFork(state, tokenId, _3_outgoingFlows)) {
              return ExecutionEngine.__default.ExecuteParallelFork(state, tokenId, _3_outgoingFlows);
            } else {
              return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_DefinitionError(_dafny.Seq.UnicodeFromString("outgoingFlows should be greater than 1")));
            }
          } else if ((_dafny.ONE).isLessThan(new BigNumber((_4_incomingFlows).length))) {
            if (ExecutionEngine.__default.CanExecuteParallelJoin(state, tokenId)) {
              return ExecutionEngine.__default.ExecuteParallelJoin(state, tokenId);
            } else {
              return state;
            }
          } else {
            return ExecutionEngine.__default.ExecuteSimplePassThrough(state, tokenId);
          }
        }
      }
      {
        return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_DefinitionError(_dafny.Seq.UnicodeFromString("Invalid gateway type")));
      }
    };
    static DetectDeadlock(state) {
      let _source0 = state;
      {
        if (_source0.is_Running) {
          let _0_process = (_source0).process;
          let _1_activeTokens = Token.__default.GetActiveTokens((_0_process).dtor_tokenCollection);
          return _dafny.Quantifier((_1_activeTokens).Elements, true, function (_forall_var_0) {
            let _2_tokenId = _forall_var_0;
            if (_System.nat._Is(_2_tokenId)) {
              return !((_1_activeTokens).contains(_2_tokenId)) || (!(ExecutionEngine.__default.CanExecuteToken(state, _2_tokenId)));
            } else {
              return true;
            }
          });
        }
      }
      {
        return false;
      }
    };
    static CanExecuteToken(state, tokenId) {
      if (_dafny.areEqual((((((state).dtor_process).dtor_tokenCollection).dtor_tokens).get(tokenId)).dtor_status, Token.TokenStatus.create_Active())) {
        return ExecutionEngine.__default.CanExecuteTokenImmediately(state, tokenId);
      } else {
        return false;
      }
    };
    static ExecuteIntermediateEvent(state, tokenId, eventType) {
      return state;
    };
    static ExecuteUserTask(state, tokenId) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_currentNode = (((_0_process).dtor_processDefinition).dtor_nodes).get((_1_token).dtor_location);
      let _3_outgoingFlows = (_2_currentNode).dtor_outgoing;
      if ((new BigNumber((_3_outgoingFlows).length)).isEqualTo(_dafny.ONE)) {
        let _4_flowId = Token.__default.PickOne(_3_outgoingFlows);
        if ((((_0_process).dtor_processDefinition).dtor_flows).contains(_4_flowId)) {
          let _5_nextNodeId = ((((_0_process).dtor_processDefinition).dtor_flows).get(_4_flowId)).dtor_targetRef;
          let _6_tokensAfterConsume = Token.__default.ConsumeToken((_0_process).dtor_tokenCollection, tokenId);
          let _let_tmp_rhs0 = Token.__default.CreateToken(_6_tokensAfterConsume, _5_nextNodeId);
          let _7_tokensWithNext = (_let_tmp_rhs0)[0];
          let _8_nextTokenId = (_let_tmp_rhs0)[1];
          let _9_newHistory = _dafny.Seq.Concat((_0_process).dtor_executionHistory, _dafny.Seq.of(BPMNState.ExecutionEvent.create_Event(_dafny.ZERO, (_1_token).dtor_location, BPMNState.EventType.create_NodeExited(), tokenId, Variables.__default.EmptyVariables()), BPMNState.ExecutionEvent.create_Event(_dafny.ONE, _5_nextNodeId, BPMNState.EventType.create_NodeEntered(), _8_nextTokenId, Variables.__default.EmptyVariables())));
          let _10_updatedContext = ExecutionContext.__default.CreateConsistentContext(_7_tokensWithNext, _5_nextNodeId, (((_0_process).dtor_context).dtor_executionStep).plus(_dafny.ONE));
          let _11_updatedProcess = BPMNState.ProcessObj.create_Process((_0_process).dtor_processId, _7_tokensWithNext, (_0_process).dtor_globalVariables, (_0_process).dtor_processDefinition, _9_newHistory, _10_updatedContext);
          return BPMNState.State.create_Running(_11_updatedProcess);
        } else {
          return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_FlowError(_4_flowId, _dafny.Seq.UnicodeFromString("Flow not found in process definition")));
        }
      } else {
        return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_ExecutionError((_1_token).dtor_location, _dafny.Seq.UnicodeFromString("UserTask should not have multiple outgoing flows")));
      }
    };
    static ExecuteServiceTask(state, tokenId) {
      return ExecutionEngine.__default.ExecuteSimpleTask(state, tokenId, _dafny.Seq.UnicodeFromString("ServiceTask"));
    };
    static ExecuteManualTask(state, tokenId) {
      return ExecutionEngine.__default.ExecuteSimpleTask(state, tokenId, _dafny.Seq.UnicodeFromString("ManualTask"));
    };
    static ExecuteSimpleTask(state, tokenId, taskType) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_currentNode = (((_0_process).dtor_processDefinition).dtor_nodes).get((_1_token).dtor_location);
      let _3_outgoingFlows = (_2_currentNode).dtor_outgoing;
      if ((new BigNumber((_3_outgoingFlows).length)).isEqualTo(_dafny.ONE)) {
        let _4_flowId = Token.__default.PickOne(_3_outgoingFlows);
        if ((((_0_process).dtor_processDefinition).dtor_flows).contains(_4_flowId)) {
          let _5_nextNodeId = ((((_0_process).dtor_processDefinition).dtor_flows).get(_4_flowId)).dtor_targetRef;
          let _6_tokensAfterConsume = Token.__default.ConsumeToken((_0_process).dtor_tokenCollection, tokenId);
          let _let_tmp_rhs0 = Token.__default.CreateToken(_6_tokensAfterConsume, _5_nextNodeId);
          let _7_tokensWithNext = (_let_tmp_rhs0)[0];
          let _8_nextTokenId = (_let_tmp_rhs0)[1];
          let _9_newHistory = _dafny.Seq.Concat((_0_process).dtor_executionHistory, _dafny.Seq.of(BPMNState.ExecutionEvent.create_Event(_dafny.ZERO, (_1_token).dtor_location, BPMNState.EventType.create_NodeExited(), tokenId, Variables.__default.EmptyVariables()), BPMNState.ExecutionEvent.create_Event(_dafny.ONE, _5_nextNodeId, BPMNState.EventType.create_NodeEntered(), _8_nextTokenId, Variables.__default.EmptyVariables())));
          let _10_updatedProcess = BPMNState.ProcessObj.create_Process((_0_process).dtor_processId, _7_tokensWithNext, (_0_process).dtor_globalVariables, (_0_process).dtor_processDefinition, _9_newHistory, (_0_process).dtor_context);
          let _11_updatedContext = ExecutionContext.__default.ComputeContext((_10_updatedProcess).dtor_tokenCollection, _5_nextNodeId, (_0_process).dtor_context);
          return BPMNState.State.create_Running(BPMNState.ProcessObj.create_Process((_0_process).dtor_processId, _7_tokensWithNext, (_0_process).dtor_globalVariables, (_0_process).dtor_processDefinition, _9_newHistory, _11_updatedContext));
        } else {
          return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_FlowError(_4_flowId, _dafny.Seq.UnicodeFromString("Flow not found in process definition")));
        }
      } else {
        return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_ExecutionError((_1_token).dtor_location, _dafny.Seq.Concat(taskType, _dafny.Seq.UnicodeFromString(" should have exactly one outgoing flow"))));
      }
    };
    static ExecuteParallelGateway(state, tokenId) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_currentNode = (((_0_process).dtor_processDefinition).dtor_nodes).get((_1_token).dtor_location);
      let _3_outgoingFlows = (_2_currentNode).dtor_outgoing;
      let _4_incomingFlows = (_2_currentNode).dtor_incoming;
      if ((_dafny.ONE).isLessThan(new BigNumber((_3_outgoingFlows).length))) {
        if (_dafny.Quantifier((_3_outgoingFlows).Elements, true, function (_forall_var_0) {
          let _5_flowId = _forall_var_0;
          return !((_3_outgoingFlows).contains(_5_flowId)) || ((((_0_process).dtor_processDefinition).dtor_flows).contains(_5_flowId));
        })) {
          return ExecutionEngine.__default.ExecuteParallelFork(state, tokenId, _3_outgoingFlows);
        } else {
          return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_ExecutionError((_1_token).dtor_location, _dafny.Seq.UnicodeFromString("Some outgoing flows not found in process definition")));
        }
      } else if ((_dafny.ONE).isLessThan(new BigNumber((_4_incomingFlows).length))) {
        if (ExecutionEngine.__default.CanExecuteParallelJoin(state, tokenId)) {
          return ExecutionEngine.__default.ExecuteParallelJoin(state, tokenId);
        } else {
          return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_ExecutionError((_1_token).dtor_location, _dafny.Seq.UnicodeFromString("Cannot execute parallel join")));
        }
      } else {
        return ExecutionEngine.__default.ExecuteSimplePassThrough(state, tokenId);
      }
    };
    static ExecuteParallelFork(state, tokenId, outgoingFlows) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_tokensAfterConsume = Token.__default.ConsumeToken((_0_process).dtor_tokenCollection, tokenId);
      let _3_targetNodes = function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of (outgoingFlows).Elements) {
          let _4_flowId = _compr_0;
          if ((outgoingFlows).contains(_4_flowId)) {
            _coll0.add(((((_0_process).dtor_processDefinition).dtor_flows).get(_4_flowId)).dtor_targetRef);
          }
        }
        return _coll0;
      }();
      let _let_tmp_rhs0 = Token.__default.CreateTokensForFlows(_2_tokensAfterConsume, outgoingFlows, ((_0_process).dtor_processDefinition).dtor_flows);
      let _5_finalTokens = (_let_tmp_rhs0)[0];
      let _6_newTokenIds = (_let_tmp_rhs0)[1];
      let _7_targetNodes = function () {
        let _coll1 = new _dafny.Set();
        for (const _compr_1 of (outgoingFlows).Elements) {
          let _8_flowId = _compr_1;
          if ((outgoingFlows).contains(_8_flowId)) {
            _coll1.add(((((_0_process).dtor_processDefinition).dtor_flows).get(_8_flowId)).dtor_targetRef);
          }
        }
        return _coll1;
      }();
      let _9_exitEvent = BPMNState.ExecutionEvent.create_Event(_dafny.ZERO, (_1_token).dtor_location, BPMNState.EventType.create_NodeExited(), tokenId, Variables.__default.EmptyVariables());
      let _10_enterEvents = ExecutionEngine.__default.CreateEnterEvents(_6_newTokenIds, outgoingFlows, ((_0_process).dtor_processDefinition).dtor_flows);
      let _11_newHistory = _dafny.Seq.Concat(_dafny.Seq.Concat((_0_process).dtor_executionHistory, _dafny.Seq.of(_9_exitEvent)), _10_enterEvents);
      let _12_lastExecutedNode = (_1_token).dtor_location;
      let _13_updatedContext = ExecutionContext.__default.CreateConsistentContext(_5_finalTokens, _12_lastExecutedNode, (((_0_process).dtor_context).dtor_executionStep).plus(_dafny.ONE));
      let _14_result = BPMNState.State.create_Running(BPMNState.ProcessObj.create_Process((_0_process).dtor_processId, _5_finalTokens, (_0_process).dtor_globalVariables, (_0_process).dtor_processDefinition, _11_newHistory, _13_updatedContext));
      return _14_result;
    };
    static GetTokensAtLocation(tokens, location) {
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of ((tokens).dtor_tokens).Keys.Elements) {
          let _0_tokenId = _compr_0;
          if (_System.nat._Is(_0_tokenId)) {
            if (((((tokens).dtor_tokens).contains(_0_tokenId)) && (_dafny.areEqual((((tokens).dtor_tokens).get(_0_tokenId)).dtor_location, location))) && (_dafny.areEqual((((tokens).dtor_tokens).get(_0_tokenId)).dtor_status, Token.TokenStatus.create_Active()))) {
              _coll0.add(_0_tokenId);
            }
          }
        }
        return _coll0;
      }();
    };
    static ConsumeMultipleTokens(tokens, tokensToConsume) {
      TAIL_CALL_START: while (true) {
        if ((new BigNumber((tokensToConsume).length)).isEqualTo(_dafny.ZERO)) {
          return tokens;
        } else {
          let _0_tokenId = Token.__default.PickOne(tokensToConsume);
          let _1_remainingTokens = (tokensToConsume).Difference(_dafny.Set.fromElements(_0_tokenId));
          let _2_tokensAfterOne = Token.__default.ConsumeToken(tokens, _0_tokenId);
          let _in0 = _2_tokensAfterOne;
          let _in1 = _1_remainingTokens;
          tokens = _in0;
          tokensToConsume = _in1;
          continue TAIL_CALL_START;
        }
      }
    };
    static ExecuteSimplePassThrough(state, tokenId) {
      return ExecutionEngine.__default.ExecuteSimpleTask(state, tokenId, _dafny.Seq.UnicodeFromString("Gateway"));
    };
    static CreateEnterEvents(tokenIds, flows, flowDefinitions) {
      return _dafny.Seq.of();
    };
    static CanExecuteGateway(state, tokenId) {
      return (((Token.__default.GetActiveTokens(((state).dtor_process).dtor_tokenCollection)).contains(tokenId)) && (((((state).dtor_process).dtor_tokenCollection).dtor_tokens).contains(tokenId))) && (((((state).dtor_process).dtor_processDefinition).dtor_nodes).contains((((((state).dtor_process).dtor_tokenCollection).dtor_tokens).get(tokenId)).dtor_location));
    };
    static CanExecuteParallelFork(state, tokenId, outgoingFlows) {
      return (((BPMNState.__default.ValidProcessDefinition(((state).dtor_process).dtor_processDefinition)) && (ExecutionEngine.__default.CanExecuteGateway(state, tokenId))) && ((_dafny.ONE).isLessThan(new BigNumber((outgoingFlows).length)))) && (_dafny.Quantifier((outgoingFlows).Elements, true, function (_forall_var_0) {
        let _0_flowId = _forall_var_0;
        return !((outgoingFlows).contains(_0_flowId)) || (((((state).dtor_process).dtor_processDefinition).dtor_flows).contains(_0_flowId));
      }));
    };
    static CountActiveTokens(state) {
      return new BigNumber((Token.__default.GetActiveTokens(((state).dtor_process).dtor_tokenCollection)).length);
    };
    static GetActiveTokensAtLocation(tokens, location) {
      return function () {
        let _coll0 = new _dafny.Set();
        for (const _compr_0 of ((tokens).dtor_tokens).Keys.Elements) {
          let _0_tokenId = _compr_0;
          if (_System.nat._Is(_0_tokenId)) {
            if (((((tokens).dtor_tokens).contains(_0_tokenId)) && (_dafny.areEqual((((tokens).dtor_tokens).get(_0_tokenId)).dtor_location, location))) && (_dafny.areEqual((((tokens).dtor_tokens).get(_0_tokenId)).dtor_status, Token.TokenStatus.create_Active()))) {
              _coll0.add(_0_tokenId);
            }
          }
        }
        return _coll0;
      }();
    };
    static ExecuteParallelJoin(state, tokenId) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_currentNode = (((_0_process).dtor_processDefinition).dtor_nodes).get((_1_token).dtor_location);
      let _3_location = (_1_token).dtor_location;
      let _4_tokensAtLocation = ExecutionEngine.__default.GetActiveTokensAtLocation((_0_process).dtor_tokenCollection, _3_location);
      let _5_tokensAfterConsume = Token.__default.ConsumeTokens((_0_process).dtor_tokenCollection, _4_tokensAtLocation);
      if ((new BigNumber(((_2_currentNode).dtor_outgoing).length)).isEqualTo(_dafny.ONE)) {
        let _6_outgoingFlow = Token.__default.PickOne((_2_currentNode).dtor_outgoing);
        if ((((_0_process).dtor_processDefinition).dtor_flows).contains(_6_outgoingFlow)) {
          let _7_nextNodeId = ((((_0_process).dtor_processDefinition).dtor_flows).get(_6_outgoingFlow)).dtor_targetRef;
          let _let_tmp_rhs0 = Token.__default.CreateToken(_5_tokensAfterConsume, _7_nextNodeId);
          let _8_finalTokens = (_let_tmp_rhs0)[0];
          let _9_newTokenId = (_let_tmp_rhs0)[1];
          let _10_newHistory = _dafny.Seq.Concat((_0_process).dtor_executionHistory, _dafny.Seq.of(BPMNState.ExecutionEvent.create_Event(_dafny.ZERO, _3_location, BPMNState.EventType.create_NodeExited(), tokenId, Variables.__default.EmptyVariables()), BPMNState.ExecutionEvent.create_Event(_dafny.ONE, _7_nextNodeId, BPMNState.EventType.create_NodeEntered(), _9_newTokenId, Variables.__default.EmptyVariables())));
          let _11_updatedContext = ExecutionContext.__default.CreateConsistentContext(_8_finalTokens, _3_location, (((_0_process).dtor_context).dtor_executionStep).plus(_dafny.ONE));
          let _12_result = BPMNState.State.create_Running(BPMNState.ProcessObj.create_Process((_0_process).dtor_processId, _8_finalTokens, (_0_process).dtor_globalVariables, (_0_process).dtor_processDefinition, _10_newHistory, _11_updatedContext));
          let _13_originalActiveTokens = Token.__default.GetActiveTokens((_0_process).dtor_tokenCollection);
          let _14_consumedTokens = _4_tokensAtLocation;
          let _15_remainingActiveTokens = (_13_originalActiveTokens).Difference(_14_consumedTokens);
          let _16_newlyCreatedTokens = _dafny.Set.fromElements(_9_newTokenId);
          return _12_result;
        } else {
          return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_FlowError(_6_outgoingFlow, _dafny.Seq.UnicodeFromString("Outgoing flow not found")));
        }
      } else {
        return BPMNState.State.create_Error(_0_process, BPMNState.ErrorCode.create_ExecutionError((_1_token).dtor_location, _dafny.Seq.UnicodeFromString("Parallel join should have exactly one outgoing flow")));
      }
    };
    static CanExecuteParallelJoin(state, tokenId) {
      let _0_process = (state).dtor_process;
      let _1_token = (((_0_process).dtor_tokenCollection).dtor_tokens).get(tokenId);
      let _2_node = (((_0_process).dtor_processDefinition).dtor_nodes).get((_1_token).dtor_location);
      return (((((Token.__default.GetActiveTokens(((state).dtor_process).dtor_tokenCollection)).contains(tokenId)) && (((((state).dtor_process).dtor_tokenCollection).dtor_tokens).contains(tokenId))) && (_dafny.areEqual((((((state).dtor_process).dtor_tokenCollection).dtor_tokens).get(tokenId)).dtor_status, Token.TokenStatus.create_Active()))) && (((((state).dtor_process).dtor_processDefinition).dtor_nodes).contains((((((state).dtor_process).dtor_tokenCollection).dtor_tokens).get(tokenId)).dtor_location))) && ((new BigNumber((ExecutionEngine.__default.GetActiveTokensAtLocation((_0_process).dtor_tokenCollection, (_1_token).dtor_location)).length)).isEqualTo(new BigNumber(((_2_node).dtor_incoming).length)));
    };
  };
  return $module;
})(); // end of module ExecutionEngine
let _module = (function() {
  let $module = {};

  return $module;
})(); // end of module _module

// ===================================
// BPMN 引擎调试代码
// ===================================

/**
 * 创建包含并行网关的BPMN流程定义
 * 流程：开始事件 -> 并行分叉 -> [任务1, 任务2] -> 并行汇聚 -> 结束事件
 */
function createSimpleProcess() {
    console.log('🏗️  Creating BPMN process with parallel gateways...');
    
    try {
        // 创建节点
        const startNode = ProcessDefinition.Node.create_ProcessNode(
            _dafny.Seq.UnicodeFromString("start"),
            _dafny.Seq.UnicodeFromString("开始事件"),
            ProcessDefinition.NodeType.create_StartEvent(),
            _dafny.Set.Empty,  // no incoming flows
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("flow1"))  // to parallel fork
        );

        // 并行分叉网关
        const forkNode = ProcessDefinition.Node.create_ProcessNode(
            _dafny.Seq.UnicodeFromString("fork"),
            _dafny.Seq.UnicodeFromString("并行分叉"),
            ProcessDefinition.NodeType.create_Gateway(ProcessDefinition.GatewayType.create_ParallelGateway()),
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("flow1")),  // from start
            _dafny.Set.fromElements(
                _dafny.Seq.UnicodeFromString("flow2"), 
                _dafny.Seq.UnicodeFromString("flow3")
            )  // to task1 and task2
        );

        // 并行任务1
        const task1Node = ProcessDefinition.Node.create_ProcessNode(
            _dafny.Seq.UnicodeFromString("task1"),
            _dafny.Seq.UnicodeFromString("用户任务1"),
            ProcessDefinition.NodeType.create_Task(ProcessDefinition.TaskType.create_UserTask()),
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("flow2")),  // from fork
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("flow4"))   // to join
        );

        // 并行任务2
        const task2Node = ProcessDefinition.Node.create_ProcessNode(
            _dafny.Seq.UnicodeFromString("task2"),
            _dafny.Seq.UnicodeFromString("用户任务2"),
            ProcessDefinition.NodeType.create_Task(ProcessDefinition.TaskType.create_ServiceTask()),
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("flow3")),  // from fork
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("flow5"))   // to join
        );

        // 并行汇聚网关
        const joinNode = ProcessDefinition.Node.create_ProcessNode(
            _dafny.Seq.UnicodeFromString("join"),
            _dafny.Seq.UnicodeFromString("并行汇聚"),
            ProcessDefinition.NodeType.create_Gateway(ProcessDefinition.GatewayType.create_ParallelGateway()),
            _dafny.Set.fromElements(
                _dafny.Seq.UnicodeFromString("flow4"), 
                _dafny.Seq.UnicodeFromString("flow5")
            ),  // from task1 and task2
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("flow6"))   // to end
        );

        const endNode = ProcessDefinition.Node.create_ProcessNode(
            _dafny.Seq.UnicodeFromString("end"),
            _dafny.Seq.UnicodeFromString("结束事件"),
            ProcessDefinition.NodeType.create_EndEvent(),
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("flow6")),  // from join
            _dafny.Set.Empty  // no outgoing flows
        );

        // 创建流程（sequence flows）
        const flow1 = ProcessDefinition.SequenceFlow.create_Flow(
            _dafny.Seq.UnicodeFromString("flow1"),
            _dafny.Seq.UnicodeFromString("start"),
            _dafny.Seq.UnicodeFromString("fork"),
            Optional.Option.create_None()
        );

        const flow2 = ProcessDefinition.SequenceFlow.create_Flow(
            _dafny.Seq.UnicodeFromString("flow2"),
            _dafny.Seq.UnicodeFromString("fork"),
            _dafny.Seq.UnicodeFromString("task1"),
            Optional.Option.create_None()
        );

        const flow3 = ProcessDefinition.SequenceFlow.create_Flow(
            _dafny.Seq.UnicodeFromString("flow3"),
            _dafny.Seq.UnicodeFromString("fork"),
            _dafny.Seq.UnicodeFromString("task2"),
            Optional.Option.create_None()
        );

        const flow4 = ProcessDefinition.SequenceFlow.create_Flow(
            _dafny.Seq.UnicodeFromString("flow4"),
            _dafny.Seq.UnicodeFromString("task1"),
            _dafny.Seq.UnicodeFromString("join"),
            Optional.Option.create_None()
        );

        const flow5 = ProcessDefinition.SequenceFlow.create_Flow(
            _dafny.Seq.UnicodeFromString("flow5"),
            _dafny.Seq.UnicodeFromString("task2"),
            _dafny.Seq.UnicodeFromString("join"),
            Optional.Option.create_None()
        );

        const flow6 = ProcessDefinition.SequenceFlow.create_Flow(
            _dafny.Seq.UnicodeFromString("flow6"),
            _dafny.Seq.UnicodeFromString("join"),
            _dafny.Seq.UnicodeFromString("end"),
            Optional.Option.create_None()
        );

        // 创建节点映射
        const nodes = _dafny.Map.Empty
            .update(_dafny.Seq.UnicodeFromString("start"), startNode)
            .update(_dafny.Seq.UnicodeFromString("fork"), forkNode)
            .update(_dafny.Seq.UnicodeFromString("task1"), task1Node)
            .update(_dafny.Seq.UnicodeFromString("task2"), task2Node)
            .update(_dafny.Seq.UnicodeFromString("join"), joinNode)
            .update(_dafny.Seq.UnicodeFromString("end"), endNode);

        // 创建流程映射
        const flows = _dafny.Map.Empty
            .update(_dafny.Seq.UnicodeFromString("flow1"), flow1)
            .update(_dafny.Seq.UnicodeFromString("flow2"), flow2)
            .update(_dafny.Seq.UnicodeFromString("flow3"), flow3)
            .update(_dafny.Seq.UnicodeFromString("flow4"), flow4)
            .update(_dafny.Seq.UnicodeFromString("flow5"), flow5)
            .update(_dafny.Seq.UnicodeFromString("flow6"), flow6);

        // 创建流程定义
        const processDefinition = ProcessDefinition.ProcessDef.create_ProcessDefinition(
            _dafny.Seq.UnicodeFromString("parallel-process"),
            _dafny.Seq.UnicodeFromString("并行网关流程"),
            nodes,
            flows,
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("start")),
            _dafny.Set.fromElements(_dafny.Seq.UnicodeFromString("end"))
        );

        console.log('✅ Process definition created successfully');
        console.log('📊 Nodes:', nodes.Keys.length);
        console.log('🔗 Flows:', flows.Keys.length);
        console.log('🔀 Parallel gateways: 2 (fork & join)');
        console.log('👥 Parallel tasks: 2 (task1 & task2)');
        
        return processDefinition;
        
    } catch (error) {
        console.error('❌ Error creating process definition:', error);
        throw error;
    }
}

/**
 * 初始化流程状态
 */
function initializeProcess(processDefinition) {
    console.log('\n⚙️  Initializing process...');
    
    try {
        // 验证流程定义
        const isValid = BPMNState.__default.ValidProcessDefinition(processDefinition);
        console.log('🔍 Process definition valid:', isValid);
        
        if (!isValid) {
            throw new Error('Invalid process definition');
        }

        // 创建初始变量
        const initialVariables = Variables.__default.EmptyVariables();
        
        // 创建初始状态
        const initialState = BPMNState.__default.CreateInitialState(processDefinition, initialVariables);
        
        console.log('✅ Process initialized successfully');
        console.log('📁 State type:', initialState.is_NotStarted ? 'NotStarted' : 'Other');
        
        return initialState;
        
    } catch (error) {
        console.error('❌ Error initializing process:', error);
        throw error;
    }
}

/**
 * 启动流程
 */
function startProcess(initialState) {
    console.log('\n🚀 Starting process...');
    
    try {
        // 检查是否可以启动
        const canStart = ExecutionInit.__default.CanStartProcess(initialState.dtor_processDefinition);
        console.log('🔍 Can start process:', canStart);
        
        if (!canStart) {
            throw new Error('Cannot start process - no valid start events');
        }

        // 初始化执行
        const runningState = ExecutionInit.__default.InitializeExecution(initialState.dtor_processDefinition);
        
        console.log('✅ Process started successfully');
        console.log('📁 State type:', runningState.is_Running ? 'Running' : 'Other');
        
        if (runningState.is_Running) {
            const activeTokens = Token.__default.GetActiveTokens(runningState.dtor_process.dtor_tokenCollection);
            console.log('🎯 Active tokens:', activeTokens.length);
        }
        
        return runningState;
        
    } catch (error) {
        console.error('❌ Error starting process:', error);
        throw error;
    }
}

/**
 * 执行流程（多步执行）
 */
function executeProcess(runningState) {
    console.log('\n⚡ Executing process...');
    
    try {
        let currentState = runningState;
        let stepCount = 0;
        const maxSteps = 10; // 防止无限循环
        
        while (currentState.is_Running && stepCount < maxSteps) {
            stepCount++;
            console.log(`\n📍 Step ${stepCount}:`);
            
            // 获取当前活跃令牌
            const activeTokens = Token.__default.GetActiveTokens(currentState.dtor_process.dtor_tokenCollection);
            console.log('🎯 Active tokens:', activeTokens.length);
            
            if (activeTokens.length === 0) {
                console.log('⏹️  No active tokens, process should terminate');
                break;
            }
            
            // 显示当前位置
            const currentLocations = BPMNState.__default.GetCurrentLocations(currentState);
            console.log('📍 Current locations:', Array.from(currentLocations.Elements).map(loc => loc.toString()));
            
            // 执行一步
            const nextState = ExecutionEngine.__default.ExecuteStep(currentState);
            
            // 检查状态变化
            if (nextState.is_Running) {
                console.log('✅ Step executed, still running');
                currentState = nextState;
            } else if (nextState.is_Completed) {
                console.log('🎉 Process completed!');
                currentState = nextState;
                break;
            } else if (nextState.is_Terminated) {
                console.log('🛑 Process terminated');
                currentState = nextState;
                break;
            } else if (nextState.is_Error) {
                console.log('❌ Process error:', nextState.dtor_errorCode.toString());
                currentState = nextState;
                break;
            } else {
                console.log('❓ Unknown state type');
                break;
            }
        }
        
        if (stepCount >= maxSteps) {
            console.log('⚠️  Maximum steps reached, stopping execution');
        }
        
        console.log(`\n📊 Execution completed in ${stepCount} steps`);
        return currentState;
        
    } catch (error) {
        console.error('❌ Error executing process:', error);
        throw error;
    }
}

/**
 * 显示执行历史
 */
function displayExecutionHistory(state) {
    if (!state.is_Running && !state.is_Completed && !state.is_Terminated) {
        return;
    }
    
    console.log('\n📜 Execution History:');
    const history = state.dtor_process.dtor_executionHistory;
    
    for (let i = 0; i < history.length; i++) {
        const event = history[i];
        console.log(`  ${i + 1}. [${event.dtor_timestamp}] ${event.dtor_eventType.toString()} at ${event.dtor_nodeId.toString()}`);
    }
}

/**
 * 主执行函数
 */
function main() {
    console.log('🎬 BPMN Engine 调试开始');
    console.log('=' .repeat(50));
    
    try {
        // 1. 创建流程定义
        const processDefinition = createSimpleProcess();
        
        // 2. 初始化流程
        const initialState = initializeProcess(processDefinition);
        
        // 3. 启动流程
        const runningState = startProcess(initialState);
        
        // 4. 执行流程
        const finalState = executeProcess(runningState);
        
        // 5. 显示执行历史
        displayExecutionHistory(finalState);
        
        // 6. 显示最终结果
        console.log('\n' + '='.repeat(50));
        console.log('📋 执行总结');
        console.log('='.repeat(50));
        
        if (finalState.is_Completed) {
            console.log('🎉 状态: 已完成');
        } else if (finalState.is_Terminated) {
            console.log('🛑 状态: 已终止');
        } else if (finalState.is_Error) {
            console.log('❌ 状态: 错误');
            if (finalState.dtor_errorCode.dtor_message) {
                console.log('💬 错误信息:', finalState.dtor_errorCode.dtor_message.toString());
            }
            if (finalState.dtor_errorCode.dtor_nodeId) {
                console.log('📍 错误节点:', finalState.dtor_errorCode.dtor_nodeId.toString());
            }
        } else if (finalState.is_Running) {
            console.log('⏸️  状态: 仍在运行');
        } else {
            console.log('❓ 状态: 未知');
        }
        
        console.log('\n✨ BPMN Engine 调试完成!');
        
    } catch (error) {
        console.error('\n💥 严重错误:', error);
        console.error('📍 错误位置:', error.stack);
        
        // 尝试提供更多调试信息
        console.log('\n🔍 调试信息:');
        console.log('- 检查所有模块是否正确加载');
        console.log('- 验证 Dafny 运行时是否可用');
        console.log('- 确认数据类型构造是否正确');
    }
}

// 检查运行时环境
function checkEnvironment() {
    console.log('🔍 检查运行时环境...');
    
    try {
        // 检查 Dafny 运行时
        if (typeof _dafny === 'undefined') {
            console.error('❌ Dafny 运行时未加载');
            return false;
        }
        console.log('✅ Dafny 运行时已加载');
        
        // 检查主要模块 - 直接检查变量
        if (typeof ProcessDefinition === 'undefined') {
            console.error('❌ ProcessDefinition 模块未加载');
            return false;
        }
        console.log('✅ ProcessDefinition 模块已加载');
        
        if (typeof BPMNState === 'undefined') {
            console.error('❌ BPMNState 模块未加载');
            return false;
        }
        console.log('✅ BPMNState 模块已加载');
        
        if (typeof Token === 'undefined') {
            console.error('❌ Token 模块未加载');
            return false;
        }
        console.log('✅ Token 模块已加载');
        
        if (typeof Variables === 'undefined') {
            console.error('❌ Variables 模块未加载');
            return false;
        }
        console.log('✅ Variables 模块已加载');
        
        if (typeof ExecutionInit === 'undefined') {
            console.error('❌ ExecutionInit 模块未加载');
            return false;
        }
        console.log('✅ ExecutionInit 模块已加载');
        
        if (typeof ExecutionEngine === 'undefined') {
            console.error('❌ ExecutionEngine 模块未加载');
            return false;
        }
        console.log('✅ ExecutionEngine 模块已加载');
        
        if (typeof ExecutionContext === 'undefined') {
            console.error('❌ ExecutionContext 模块未加载');
            return false;
        }
        console.log('✅ ExecutionContext 模块已加载');
        
        if (typeof Optional === 'undefined') {
            console.error('❌ Optional 模块未加载');
            return false;
        }
        console.log('✅ Optional 模块已加载');
        
        console.log('✅ 所有模块检查通过');
        return true;
        
    } catch (error) {
        console.error('❌ 环境检查失败:', error);
        return false;
    }
}

// 立即执行环境检查和主函数
if (checkEnvironment()) {
    main();
} else {
    console.error('💥 环境检查失败，无法运行 BPMN Engine');
} 