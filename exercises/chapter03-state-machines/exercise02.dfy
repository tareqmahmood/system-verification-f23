
// Define the state machine for the Dining Philosophers.
// There are N philosophers sitting around a round table.
// Between every pair of philosophers lies a chopstick.
// Every philosopher has three possible actions:
//  * Acquire the chopstick to their left.
//  * Acquire the chopstick to their right.
//  * Release both chopsticks (in a single step).
//
// (Nota bene: The dining philosophers problem is used to illustrate deadlocks
// and deadlock-freedom. We're not doing any of that here, just using the
// example to teach you to set up a state machine model.)

// Define all the relevant state in this datatype.
// FIXME: fill in here (solution: 8 lines)
datatype Variables = Variables(tableSize: nat, owner: seq<int>)
{
  ghost predicate WellFormed() {
    && 0 < tableSize
    && |owner| == tableSize
    && (forall cs :: 0 <= cs < |owner| ==> 0 <= owner[cs] <= tableSize)
    && (forall cs :: 0 <= cs < |owner| && 0 < owner[cs] ==> cs == leftChopstick(owner[cs], tableSize) || cs == rightChopstick(owner[cs], tableSize))
  }
}
// END EDIT

ghost predicate Init(v:Variables) {
  // FIXME: fill in here (solution: 3 lines)
  && v.WellFormed()
  && forall p :: p in v.owner ==> p == 0
                 // END EDIT
}

// FIXME: fill in here (solution: 11 lines)
// (optional) Add any helper functions desired here

function rightChopstick(philosopherIndex:nat, tableSize:nat): int
  requires 1 <= tableSize
  requires 1 <= philosopherIndex <= tableSize
{
  philosopherIndex - 1
}

function leftChopstick(philosopherIndex:nat, tableSize:nat): int
  requires 1 <= tableSize
  requires 1 <= philosopherIndex <= tableSize
{
  if philosopherIndex == tableSize then 0
  else philosopherIndex
}

function rightPhilosopher(philosopherIndex:nat, tableSize:nat): nat
  requires 1 <= tableSize
  requires 1 <= philosopherIndex <= tableSize
{
  if philosopherIndex == 1 then tableSize
  else philosopherIndex - 1
}

function leftPhilosopher(philosopherIndex:nat, tableSize:nat): nat
  requires 1 <= tableSize
  requires 1 <= philosopherIndex <= tableSize
{
  if philosopherIndex == tableSize then 1
  else philosopherIndex + 1
}

// END EDIT

// Philosopher with index philosopherIndex acquires left chopstick
ghost predicate AcquireLeft(v:Variables, v':Variables, philosopherIndex:nat) {
  // FIXME: fill in here (solution: 5 lines)
  && v.WellFormed() && v'.WellFormed()
  && v.tableSize == v'.tableSize
  && 1 <= philosopherIndex <= v.tableSize
  && 0 <= leftChopstick(philosopherIndex, v.tableSize) < |v.owner|
  && v.owner[leftChopstick(philosopherIndex, v.tableSize)] == 0
  && v'.owner[leftChopstick(philosopherIndex, v.tableSize)] == philosopherIndex
  && forall cs :: 0 <= cs < |v.owner| && cs != leftChopstick(philosopherIndex, v.tableSize) ==> v.owner[cs] == v'.owner[cs]
                  // END EDIT
}

// Philosopher with index philosopherIndex acquires right chopstick
ghost predicate AcquireRight(v:Variables, v':Variables, philosopherIndex:nat) {
  // FIXME: fill in here (solution: 5 lines)
  && v.WellFormed() && v'.WellFormed()
  && v.tableSize == v'.tableSize
  && 1 <= philosopherIndex <= v.tableSize
  && 0 <= rightChopstick(philosopherIndex, v.tableSize) < |v.owner|
  && v.owner[rightChopstick(philosopherIndex, v.tableSize)] == 0
  && v'.owner[rightChopstick(philosopherIndex, v.tableSize)] == philosopherIndex
  && forall cs :: 0 <= cs < |v.owner| && cs != rightChopstick(philosopherIndex, v.tableSize) ==> v.owner[cs] == v'.owner[cs]
                  // END EDIT
}

// Philosopher with index philosopherIndex releases both chopsticks
ghost predicate ReleaseBoth(v:Variables, v':Variables, philosopherIndex:nat) {
  // FIXME: fill in here (solution: 5 lines)
  && v.WellFormed() && v'.WellFormed()
  && v.tableSize == v'.tableSize
  && 1 <= philosopherIndex <= v.tableSize
  && 0 <= leftChopstick(philosopherIndex, v.tableSize) < |v.owner|
  && 0 <= rightChopstick(philosopherIndex, v.tableSize) < |v.owner|
  && v.owner[leftChopstick(philosopherIndex, v.tableSize)] == philosopherIndex
  && v.owner[rightChopstick(philosopherIndex, v.tableSize)] == philosopherIndex
  && v'.owner[leftChopstick(philosopherIndex, v.tableSize)] == 0
  && v'.owner[rightChopstick(philosopherIndex, v.tableSize)] == 0
  && forall cs :: 0 <= cs < |v.owner| && cs != rightChopstick(philosopherIndex, v.tableSize) && cs != leftChopstick(philosopherIndex, v.tableSize) ==> v.owner[cs] == v'.owner[cs]
                  // END EDIT
}

datatype Step =
    // FIXME: fill in here (solution: 3 lines)
  | AcquireLeftStep(p: nat)
  | AcquireRightStep(p: nat)
  | ReleaseBothStep(p: nat)
    // END EDIT

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  // FIXME: fill in here (solution: 3 lines)
  case AcquireLeftStep(p) => AcquireLeft(v, v', p)  // Replace me
  case AcquireRightStep(p) => AcquireRight(v, v', p)
  case ReleaseBothStep(p) => ReleaseBoth(v, v', p)
  // END EDIT
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

// This predicate should be true if and only if no philosopher holds a
// chopstick.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate NoSticksAcquired(v: Variables)
  requires v.WellFormed()
{
  // FIXME: fill in here (solution: 8 lines)
  forall p :: p in v.owner ==> p == 0
              // END EDIT
}

// Change this predicate to be true if and only if philosopher
// `philosopherIndex` holds both of their chopsticks.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate BothSticksAcquired(v: Variables, philosopherIndex: nat)
  requires philosopherIndex < v.tableSize
  requires v.WellFormed()
{
  // FIXME: fill in here (solution: 6 lines)
  && 1 <= philosopherIndex
  && v.owner[leftChopstick(philosopherIndex, v.tableSize)] == philosopherIndex
  && v.owner[rightChopstick(philosopherIndex, v.tableSize)] == philosopherIndex
     // END EDIT
}

// Show that, in the Init state, no philosopher has chopsticks.
lemma InitProperty(v: Variables, philosopherIndex:nat)
  requires Init(v)
  ensures NoSticksAcquired(v)
{
  // FIXME: fill in here (solution: 0 lines)
  // Add a proof (if needed).
  // END EDIT
}


// Show a behavior that evolves from the init state to one where a philosopher
// has completed acquiring both chopsticks.
lemma PseudoLiveness(philosopherIndex:nat) returns (behavior:seq<Variables>)
  requires philosopherIndex == 1
  ensures 0 < |behavior|  // precondition for index operators below
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]) // Behavior satisfies your state machine
  ensures forall i | 0 <= i < |behavior| :: behavior[i].tableSize == 3
  ensures behavior[|behavior|-1].WellFormed() // precondition for calling BothSticksAcquired
  ensures BothSticksAcquired(behavior[|behavior|-1], philosopherIndex)  // Behavior ultimately achieves acquisition for philosopherIndex
{
  // FIXME: fill in here (solution: 6 lines)
  var v0 := Variables(tableSize := 3, owner := [0, 0, 0]);
  var v1 := Variables(tableSize := 3, owner := [1, 0, 0]);
  var s0 := AcquireRightStep(1);
  assert(NextStep(v0, v1, s0));
  // assert(Next(v0, v1));

  var v2 := Variables(tableSize := 3, owner := [1, 1, 0]);
  var s1 := AcquireLeftStep(1);
  assert(NextStep(v1, v2, s1));
  // assert(Next(v1, v2));

  behavior := [v0, v1, v2];

  // END EDIT
}
