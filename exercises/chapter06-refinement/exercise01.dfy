// State Machine Spec for Atomic Commit
// Build an abstract behavioral model that captures the
// semantics of an evolving system to use as a refinement
// reference for its more-complicated implementation.

// Define the specification of atomic commit in the form of a state
// machine.
//
// The abstract model doesn't worry about network communication. Instead,
// it models the input:
//     - which participants prefer which outcomes
// and the outputs:
//     - what each participant thinks the decision was
// This definition should make it obvious by inspection that the output
// decisions all agree (AC1) and they output decisions that comply with the
// input preferences (AC3, AC4).
//
// In exercise03 of this chapter, we'll show refinement: that the 2PC protocol
// correctly computes a decision based on all participants' preferences.
//
// Note that this is an assumed-correct spec. This file already passes Dafny,
// but it's a terrible spec, because it doesn't say anything useful. Consider
// running your result past an instructor in office hours to be sure it's a good
// spec.

include "UtilitiesLibrary.dfy"
include "CommitTypes.dfy"

// This is the specification state machine. It defines what the implementation
// is trying to accomplish, while ignoring all implementation details.
module AtomicCommit {
  import opened CommitTypes
  import opened UtilitiesLibrary

  type ParticipantId = nat

  // We'll give you the state data structure; it'll be your job to define the
  // actions.

  // The preferences are inputs to the algorithm and are held constant. The
  // outputs are the decisions observed by the participants - the coordinator's
  // decision is considered internal by this specification.  None? capture the
  // idea that initially nobody knows the decision.  In your actions, make AC2
  // abundantly obvious: once a None? turns into a Some?, it can't ever change.
  datatype Variables = Variables(preferences: seq<Vote>, decisions: seq<Option<Decision>>)
  {
    ghost predicate ValidParticipant(idx: ParticipantId) {
      idx < |preferences|
    }

    ghost predicate WF() {
      && |decisions| == |preferences|
    }
  }

  ghost predicate Init(v: Variables)
  {
    // DONE: fill in here (solution: 2 lines)
    && v.WF()
    && (forall idx:ParticipantId | v.ValidParticipant(idx) :: v.decisions[idx].None?)
    // END EDIT
  }

  // We can tell what the ultimate decision has to be just from the constants.
  // Define that in this function, and then use it to constrain what actions
  // can happen in the state machine.
  ghost function UltimateDecision(prefs: seq<Vote>) : Decision
  {
    // DONE: fill in here (solution: 1 line)
    if (exists i:ParticipantId | 0 <= i < |prefs| :: prefs[i] == No) then Abort
    else Commit
    // END EDIT
  }

  // Define your step predicates here
  // DONE: fill in here (solution: 9 lines)
  ghost predicate NoOp(v:Variables, v':Variables, event:Event)
  {
    && v.WF()
    && v'.WF()
    && v' == v
    && event == NoOpEvent()
  }

  ghost predicate Decide(v:Variables, v':Variables, event:Event, i:ParticipantId)
  {
    && v.WF()
    && v'.WF()
    && v.preferences == v'.preferences
    && event == ParticipantLearnsEvent(i)
    && v.ValidParticipant(i)
    && v.decisions[i].None?
    && (v'.decisions[i] == Some(UltimateDecision(v.preferences)))
    && (forall j:ParticipantId | j != i && v.ValidParticipant(j) :: v.decisions[j] == v'.decisions[j])
  }
  // END EDIT

  // JayNF
  datatype Step =
      // DONE: fill in here (solution: 1 line)
    | NoOpStep()
    | DecideStep(i:ParticipantId)
      // END EDIT

  ghost predicate NextStep(v: Variables, v': Variables, event: Event, step: Step)
  {
    && v.WF()
    && v'.preferences == v.preferences
    && (
         match step
         // DONE: fill in here (solution: 1 line)
         case NoOpStep() => NoOp(v, v', event)
         case DecideStep(i) => Decide(v, v',  event, i)
         // END EDIT
       )
  }

  ghost predicate Next(v: Variables, v': Variables, event: Event)
  {
    exists step :: NextStep(v, v', event, step)
  }

  ghost predicate ExecutionSatisfiesSpec(ex: seq<Variables>, evs: seq<Event>)
  {
    && 0 < |ex|
    && |evs| == |ex| - 1
    && (forall i | 0 < i < |ex| :: ex[i].WF())
    && Init(ex[0])
    && (forall i | 0 <= i < |ex|-1 :: Next(ex[i], ex[i+1], evs[i]))
  }

  // Show us an execution that satisfies your state machine and arrives at Commit.
  lemma PseudoLivenessCommit() returns (ex: seq<Variables>, evs: seq<Event>)
    ensures |ex| >= 1
    ensures forall i | 0 <= i < |ex| :: ex[i].preferences == [Yes, Yes]
    ensures UltimateDecision(ex[0].preferences) == Commit
    ensures ExecutionSatisfiesSpec(ex, evs)
    // At the end, everybody learns Commit.
    ensures Last(ex).decisions[0] == Some(Commit)
    ensures Last(ex).decisions[1] == Some(Commit)
  {
    // FIXME: fill in here (solution: 9 lines)

    var v1 := Variables(
      preferences := [Yes, Yes],
      decisions := [None, None]
    );
    assert Init(v1);

    var e1 := ParticipantLearnsEvent(0);
    var s1 := DecideStep(0);
    var v2 := Variables(
      preferences := [Yes, Yes],
      decisions := [Some(Commit), None]
    );
    assert NextStep(v1, v2, e1, s1);
    assert ExecutionSatisfiesSpec([v1, v2], [e1]);

    var e2 := ParticipantLearnsEvent(1);
    var s2 := DecideStep(1);
    var v3 := Variables(
      preferences := [Yes, Yes],
      decisions := [Some(Commit), Some(Commit)]
    );
    assert NextStep(v2, v3, e2, s2);
    assert ExecutionSatisfiesSpec([v1, v2, v3], [e1, e2]);

    ex := [v1, v2, v3];
    evs := [e1, e2];

    // END EDIT
  }

  // Show us another execution that satisfies your state machine and arrives at Abort.
  lemma PseudoLivenessAbort() returns (ex: seq<Variables>, evs: seq<Event>)
    ensures |ex| >= 1
    ensures forall i | 0 <= i < |ex| :: ex[i].preferences == [Yes, No]
    ensures UltimateDecision(ex[0].preferences) == Abort
    ensures ExecutionSatisfiesSpec(ex, evs)
    // At the end, everybody learns Abort.
    ensures Last(ex).decisions[0] == Some(Abort)
    ensures Last(ex).decisions[1] == Some(Abort)
  {
    // FIXME: fill in here (solution: 10 lines)
    var v1 := Variables(
      preferences := [Yes, No],
      decisions := [None, None]
    );
    assert Init(v1);
    assert v1.preferences[1] == No;
    assert UltimateDecision(v1.preferences) == Abort;

    var e1 := ParticipantLearnsEvent(0);
    var s1 := DecideStep(0);
    var v2 := Variables(
      preferences := [Yes, No],
      decisions := [Some(Abort), None]
    );
    assert NextStep(v1, v2, e1, s1);
    assert ExecutionSatisfiesSpec([v1, v2], [e1]);

    var e2 := ParticipantLearnsEvent(1);
    var s2 := DecideStep(1);
    var v3 := Variables(
      preferences := [Yes, No],
      decisions := [Some(Abort), Some(Abort)]
    );
    assert NextStep(v2, v3, e2, s2);
    assert ExecutionSatisfiesSpec([v1, v2, v3], [e1, e2]);

    ex := [v1, v2, v3];
    evs := [e1, e2];
    // END EDIT
  }
}
