// Specifying and implementing IsPrime

/*{*//*}
*/
ghost predicate IsPrimeSpec(candidate:nat)
{
  // FIXME: fill in here (solution: 3 lines)
  if candidate < 2 then false
  else forall k:nat | 1 < k < candidate :: k*(candidate/k) != candidate
  // END EDIT
}

// illustrate IsPrimeSpec on a few examples (note that the verifier is able to
// check these only with some help to find divisors for non-prime numbers)
lemma ConstantObligations()
  ensures !IsPrimeSpec(0)
  ensures !IsPrimeSpec(1)
  ensures IsPrimeSpec(2)
  ensures IsPrimeSpec(3)
  ensures !IsPrimeSpec(4)
  ensures !IsPrimeSpec(6)
  ensures IsPrimeSpec(7)
  ensures !IsPrimeSpec(9)
{
  // FIXME: fill in here (solution: 3 lines)
  // Add assertions here to prove the composite numbers have divisors.
  assert 2*(4/2) == 4;
  assert 2*(6/2) == 6;
  assert 3*(9/3) == 9;
  // END EDIT
}

lemma CompositeIsntPrime(p: nat)
  requires 1 < p
  ensures !IsPrimeSpec(p*66)
{
  // FIXME: fill in here (solution: 1 line)
  assert 66*((p*66)/66) == (p*66);
  // END EDIT
}


// ================================================
// Implementing a check for IsPrime
// ================================================

// Let's try "implementing" (with a recursive function) a check for
// primeness.

// A recursive implementation of IsPrime. The function HasDivisorBelow should
// check if n is divisible by something between 1 and limit (including limit,
// not including 1).
function
  HasDivisorBelow(n:nat, limit:nat): bool
  requires limit >= 1
{
  // FIXME: fill in here (solution: 3 lines)
  if limit == 1 then false
  else if limit*(n/limit) == n then true
  else HasDivisorBelow(n, limit - 1) // Replace with an appropriate definition
  // END EDIT
}

function IsPrime(n: nat): bool {
  if n <= 1 then false else
  !HasDivisorBelow(n, n-1)
}

// You'll now prove IsPrime(n) == IsPrimeSpec(n). This will require a helper
// lemma to deal with the recursion.

// An intermediate spec for what HasDivisorBelow returns. The solution is
// expressed using an exists; you may find it more natural to write a forall.
//
// We add {:induction false} to avoid Dafny doing some extra work
// automatically. This forces you to write a proof which is more instructive in
// this case (and is needed in more complex examples).
lemma {:induction false} HasDivisorBelow_ok(n: nat, limit: nat)
  requires 1 <= limit
  // FIXME: fill in here (solution: 3 lines)
  ensures forall k | 1 <= k <= limit :: (k*(n/k) == n) ==> true
  // END EDIT
{
  // FIXME: fill in here (solution: 5 lines)
  // END EDIT
}

lemma IsPrime_ok(n: nat)
  ensures IsPrime(n) == IsPrimeSpec(n)
{
  // FIXME: fill in here (solution: 4 lines)
   // This proof should work if your postcondition for HasDivisorBelow_ok is
   // correct, but you can change it if needed.
   if n <= 2 {
     return;
   }
  HasDivisorBelow_ok(n, n-1);
  // END EDIT
}
