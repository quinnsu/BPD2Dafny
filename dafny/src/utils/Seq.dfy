module Seq {


      /* Returns the first element of a non-empty sequence. */
  function First<T>(xs: seq<T>): T
    requires |xs| > 0
  {
    xs[0]
  }

   /* Returns the subsequence of a non-empty sequence obtained by
     dropping the first element. */
  function DropFirst<T>(xs: seq<T>): seq<T>
    requires |xs| > 0
  {
    xs[1..]
  }

  /* Returns the last element of a non-empty sequence. */
  function Last<T>(xs: seq<T>): T
    requires |xs| > 0
  {
    xs[|xs|-1]
  }

  /* Returns the subsequence of a non-empty sequence obtained by
     dropping the last element. */
  function DropLast<T>(xs: seq<T>): seq<T>
    requires |xs| > 0
  {
    xs[..|xs|-1]
  }

    /* The concatenation of two subsequences of a non-empty sequence, the first obtained 
     from dropping the last element, the second consisting only of the last 
     element, is the original sequence. */
  lemma LemmaLast<T>(xs: seq<T>)
    requires |xs| > 0
    ensures DropLast(xs) + [Last(xs)] == xs
  {
  }

  /* The last element of two concatenated sequences, the second one being non-empty, will be the 
     last element of the latter sequence. */
  lemma LemmaAppendLast<T>(xs: seq<T>, ys: seq<T>)
    requires 0 < |ys|
    ensures Last(xs + ys) == Last(ys)
  {
  }

  /* The concatenation of sequences is associative. */
  lemma LemmaConcatIsAssociative<T>(xs: seq<T>, ys: seq<T>, zs: seq<T>)
    ensures xs + (ys + zs) == (xs + ys) + zs
  {
}


  /* Returns the subsequence consisting of those elements of a sequence that satisfy a given 
     predicate. */
  function {:opaque} Filter<T>(f: (T ~> bool), xs: seq<T>): (result: seq<T>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
    ensures |result| <= |xs|
    ensures forall i: nat :: i < |result| && f.requires(result[i]) ==> f(result[i])
  {
    if |xs| == 0 then []
    else (if f(xs[0]) then [xs[0]] else []) + Filter(f, xs[1..])
  }

  
}