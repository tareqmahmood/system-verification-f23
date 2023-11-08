// Two Phase Commit Safety Specification Predicate
// Express the English Atomic Commit safety properties as predicates
// over the compound state machine model from exercise01.

// 2PC should satisfy the Atomic Commit specification. English design doc:
//
// AC-1: All processes that reach a decision reach the same one.
// AC-3: If any host has a No preference, then the decision must be Abort.
// AC-4: If all processes prefer Yes, then the decision must be Commit.
//
// Note that the full Atomic Commit spec includes these additional properties,
// but you should ignore them for this exercise:
// AC-2: (stability) A process cannot reverse its decision after it has reached one.
//       (best modeled with refinement)
// AC-5: (liveness) All processes eventually decide.

// Note that this specification depends on your model from exercise 1, so you
// should write your spec accordingly. Of course, that also means
// double-checking that your model performs all actions as described.
include "exercise01.dfy"

module Obligations {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
    // Here are some handy accessor functions for dereferencing the coordinator
    // and the participants out of the sequence in Hosts.
  ghost function CoordinatorVars(v: Variables) : CoordinatorHost.Variables
    requires v.WF()
  {
    Last(v.hosts).coordinator
  }

  ghost predicate ValidParticipantId(v: Variables, hostid: HostId)
  {
    hostid < |v.hosts|-1
  }

  ghost function ParticipantVars(v: Variables, hostid: HostId) : ParticipantHost.Variables
    requires v.WF()
    requires ValidParticipantId(v, hostid)
  {
    v.hosts[hostid].participant
  }

  // FIXME: fill in here (solution: 8 lines)
  ghost predicate HaveSameDecision(v: Variables, i: HostId, j: HostId)
  {
    && v.WF()
    && ValidParticipantId(v, i) 
    && ValidParticipantId(v, j)
    && ParticipantVars(v, i).decision.Some? 
    && ParticipantVars(v, j).decision.Some?
    && ParticipantVars(v, i).decision.value == ParticipantVars(v, j).decision.value
  }

  ghost predicate VotedNo(v: Variables, i: HostId)
  {
    && v.WF()
    && ValidParticipantId(v, i) 
    && ParticipantVars(v, i).c.preference == No
  }

  ghost predicate VotedYes(v: Variables, i: HostId)
  {
    && v.WF()
    && ValidParticipantId(v, i) 
    && ParticipantVars(v, i).c.preference == Yes
  }

  ghost predicate AnyParticipantVotedNo(v: Variables)
  {
    && v.WF()
    && (exists i : HostId :: VotedNo(v, i))
  }

  ghost predicate AllParticipantVotedYes(v: Variables)
  {
    && v.WF()
    && (forall i : HostId :: VotedYes(v, i))
  }

  ghost predicate AllReachedDecision(v: Variables)
  {
    && v.WF()
    && (forall i : HostId | ValidParticipantId(v, i) :: ParticipantVars(v, i).decision.Some?)
  }

  ghost predicate AllDecided(v: Variables, decision: Decision)
    requires AllReachedDecision(v)
  {
    && v.WF()
    && (forall i : HostId | ValidParticipantId(v, i) :: ParticipantVars(v, i).decision.value == decision)
  }

  // END EDIT

  // AC-1: All processes that reach a decision reach the same one.
  ghost predicate SafetyAC1(v: Variables)
    requires v.WF()
  {
    // All hosts that reach a decision reach the same one
    // FIXME: fill in here (solution: 4 lines)
    && (forall i, j : HostId | ValidParticipantId(v, i) && ValidParticipantId(v, j) && i != j :: HaveSameDecision(v, i, j))
    // END EDIT
  }

  // AC2 is sort of a history predicate; we're going to ignore it.

  // AC-3: If any host has a No preference, then the decision must be Abort.
  ghost predicate SafetyAC3(v: Variables)
    requires v.WF()
  {
    // FIXME: fill in here (solution: 6 lines)
    AnyParticipantVotedNo(v) ==> (AllReachedDecision(v) ==> AllDecided(v, Abort))
    // END EDIT
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  ghost predicate SafetyAC4(v: Variables)
    requires v.WF()
  {
    // FIXME: fill in here (solution: 5 lines)
    AllParticipantVotedYes(v) ==> (AllReachedDecision(v) ==> AllDecided(v, Commit))
    // END EDIT
  }

  // AC5 is a liveness proprety, we're definitely going to ignore it.

  ghost predicate Safety(v: Variables)
    requires v.WF()
  {
    && SafetyAC1(v)
    && SafetyAC3(v)
    && SafetyAC4(v)
  }
}
