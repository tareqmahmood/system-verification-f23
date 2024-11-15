// Two Phase Commit Safety Proof
// Prove that the 2PC distributed system (from exercise01) accomplishes the Safety spec (from exercise02)

include "exercise02.dfy"

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened Obligations

  // This is a conjunct of the inductive invariant, indicating that the messages carrying
  // decisions should reflect the votes of the participants as relayed to the coordinator
  ghost predicate DecisionMsgsAgreeWithDecision(v: Variables)
    requires v.WF()
  {
    // FIXME: fill in here (solution: 5 lines)
    true
    && v.WF()
    // if there is a message from the coord, the participant must have voted Yes
    && (forall i:HostId, d:Decision | ValidParticipantId(v, i) && MessageDecision(i, d) in v.network.sentMsgs :: (
      && CoordinatorVars(v).decision == Some(d)
      && ParticipantVars(v, i).c.preference == Yes
      && (exists m:Message | m in v.network.sentMsgs :: m == MessageResponse(i, Yes))
    ))
    // if participant voted No, there should be no message from him and to him
    && (forall i: HostId | ValidParticipantId(v, i) && ParticipantVars(v, i).c.preference == No :: (
      && !(exists m:Message | m in v.network.sentMsgs :: m == MessageResponse(i, Yes))
      && !(exists m:Message | m in v.network.sentMsgs :: m == MessageResponse(i, No))
      && !(exists m:Message | m in v.network.sentMsgs :: m == MessageDecision(i, Commit))
      && !(exists m:Message | m in v.network.sentMsgs :: m == MessageDecision(i, Abort))
    ))
    // END EDIT
  }

  // We use this block of code to define additional invariants. We recommend you
  // define predicates for the individual parts of your invariant, to make
  // debugging easier.
  // FIXME: fill in here (solution: 20 lines)
  // END EDIT


  ghost predicate Inv(v: Variables)
  {
    && v.WF()
       // FIXME: fill in here (solution: 2 lines)
       // END EDIT
       // We give you the blueprint for one invariant to get you started...
    && DecisionMsgsAgreeWithDecision(v)
       // ...but you'll need more.
    && Safety(v)
  }

  lemma InitImpliesInv(v: Variables)
    requires Init(v)
    ensures Inv(v)
  {
    // FIXME: fill in here (solution: 3 lines)
    // END EDIT
  }

  lemma InvInductive(v: Variables, v': Variables)
    requires Inv(v)
    requires Next(v, v')
    ensures Inv(v')
  {
    //(not all of the below but much of it)
    // FIXME: fill in here (solution: 59 lines)
    // END EDIT
  }

  lemma InvImpliesSafety(v: Variables)
    requires Inv(v)
    ensures Safety(v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
