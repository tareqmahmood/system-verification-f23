
// Model a lock service that consists of a single server and an
// arbitrary number of clients.
//
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
//
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
//
// The safety property is that no two clients ever hold the lock
// simultaneously.

// FIXME: fill in here (solution: 13 lines)
datatype Variables = Variables(owner: nat, knows: seq<bool>) {
  ghost predicate WellFormed() {
    && |knows| > 0   // client + server
    && 0 <= owner <= |knows|  // server is |knows|
    && (owner < |knows| ==> knows[owner])
    && (forall c :: 0 <= c < |knows| && c != owner ==> !knows[c])
  }
}
// END EDIT


ghost predicate Init(v:Variables) {
  && v.WellFormed()
  // FIXME: fill in here (solution: 3 lines)
  && v.owner == |v.knows|
  && forall c :: 0 <= c < |v.knows| ==> !v.knows[c]
  // END EDIT
}
// FIXME: fill in here (solution: 23 lines)
ghost predicate TransferLock(v: Variables, v':Variables, clientIndex: nat)
{
  && v.WellFormed() && v'.WellFormed()
  && |v.knows| == |v'.knows|
  && clientIndex < |v.knows|
  && v.owner == |v.knows|
  // && (forall c :: 0 <= c < |v.knows| ==> !v.knows[c])
  && v'.owner == clientIndex
  && v'.knows[clientIndex]
  // && (forall c :: 1 <= c < |v'.knows| && c != clientIndex ==> !v'.knows[c])
}

ghost predicate RevokeLock(v: Variables, v':Variables, clientIndex: nat)
{
  && v.WellFormed() && v'.WellFormed()
  && |v.knows| == |v'.knows|
  && clientIndex < |v.knows|
  && v.owner == clientIndex
  && v.knows[clientIndex]
  // && (forall c :: 1 <= c < |v.knows| && c != clientIndex ==> !v.knows[c])
  && v'.owner == |v.knows|
  // && (forall c :: 1 <= c < |v'.knows| ==> !v'.knows[c])
}
// END EDIT
// Jay-Normal-Form: pack all the nondeterminism into a single object
// that gets there-exist-ed once.
datatype Step =
    // FIXME: fill in here (solution: 2 lines)
   | TransferLockStep(c: nat)
   | RevokeLockStep(c: nat)
    // END EDIT

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  // FIXME: fill in here (solution: 2 lines)
   case TransferLockStep(c) => TransferLock(v, v', c)
   case RevokeLockStep(c) => RevokeLock(v, v', c)
  // END EDIT
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

// A good definition of safety for the lock server is that no two clients
// may hold the lock simultaneously. This predicate should capture that
// idea in terms of the Variables you have defined.
ghost predicate Safety(v:Variables) {
  // FIXME: fill in here (solution: 10 lines)
  && v.WellFormed()
  && forall c1, c2 :: (0 <= c1 < |v.knows| && 0 <= c2 < |v.knows| && c1 < c2) ==> (!v.knows[c1] || !v.knows[c2])
  // END EDIT
}


// This predicate should be true if and only if the client with index `clientIndex`
// has the lock acquired.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed()
{
  // FIXME: fill in here (solution: 1 line)
  && v.WellFormed()
  && clientIndex < |v.knows|
  && v.owner == clientIndex
  && v.knows[clientIndex]
  // END EDIT
}

// Show a behavior that the system can release a lock from clientA and deliver
// it to clientB.
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (behavior:seq<Variables>)
  requires clientA == 2
  requires clientB == 0
  ensures 2 <= |behavior|  // precondition for index operators below
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]) // Behavior satisfies your state machine
  ensures forall i | 0 <= i < |behavior| :: Safety(behavior[i]) // Behavior always satisfies the Safety predicate
  ensures behavior[|behavior|-1].WellFormed() // precondition for calling ClientHoldsLock
  ensures ClientHoldsLock(behavior[1], clientA) // first clientA acquires lock
  ensures ClientHoldsLock(behavior[|behavior|-1], clientB) // eventually clientB acquires lock
{
  // FIXME: fill in here (solution: 9 lines)
  var v0 := Variables(owner := 3, knows := [false, false, false]);
  var v1 := Variables(owner := 2, knows := [false, false, true]);
  var s0 := TransferLockStep(2);
  assert(NextStep(v0, v1, s0));

  var v2 := Variables(owner := 3, knows := [false, false, false]);
  var s1 := RevokeLockStep(2);
  assert(NextStep(v1, v2, s1));

  var v3 := Variables(owner := 0, knows := [true, false, false]);
  var s2 := TransferLockStep(0);
  assert(NextStep(v2, v3, s2));

  behavior := [v0, v1, v2, v3];
  // END EDIT
}
