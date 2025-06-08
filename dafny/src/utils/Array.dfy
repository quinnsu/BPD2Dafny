module Arrays {


  /* For an element that occurs at least once in a sequence, the index of its
     first occurrence is returned. */
  function {:opaque} IndexOf<T(==)>(xs: seq<T>, v: T): (i: nat)
    requires v in xs
    ensures i < |xs| && xs[i] == v
    ensures forall j :: 0 <= j < i ==> xs[j] != v
  {
    if xs[0] == v then 0 else 1 + IndexOf(xs[1..], v)
  }
  
     /**
     * Everything is the same, except for those elements within the given region.
     */
    predicate EqualsExcept<T(==)>(lhs:seq<T>, rhs:seq<T>, address:nat, length: nat)
    // Data region must be within available memory
    requires address + length <= |lhs| {
        // Memory sizes are the same
        |lhs| == |rhs| &&
        // Check nothing below data region changed
        lhs[..address] == rhs[..address] &&
        // Check nothing above data region changed
        lhs[address+length..] == rhs[address+length..]
    }
    /**
     * Copy a sequence of bytes from into another at a given starting position.
     */
    opaque function Copy<T>(src: seq<T>, dst: seq<T>, start: nat) : (result:seq<T>)
    // Must have enough space in the destination sequence.
    requires (start+|src|) <= |dst|
    // Resulting array unchanged in size
    ensures |result| == |dst|
    // Affected region matches source array
    ensures src == result[start .. (start+|src|)]
    // Everything unchanged outside affected region
    ensures EqualsExcept(dst,result,start,|src|)
    {
        // Precompute end within destination
        var end := start+|src|;
        // Construct the sequence!
        seq(|dst|, i requires i >= 0 && i < |dst| => if (i >= start && i<end) then src[i-start] else dst[i])
    }
}