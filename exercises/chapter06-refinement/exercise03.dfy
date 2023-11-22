// Refinement proof for 2PC
// Show that Two Phase Commit refines the Atomic Commit sate machine spec.

// This proof shouldn't be terribly brutal, since you have a roadmap for the
// relevant invariants from chapter05. You can discard the AC properties (since
// those are proven about the spec in exercise03, and therefore about any state
// machine that refines the spec).

include "exercise01.dfy"

// We have provided you with a copy of our solution to chapter05 exercises
// here. We're building on its state machine, so of course we need its definition.
// The Safety property that chapter 05 considered a "spec" is no longer a spec since
// we're going to use an abstract spec that the protocol refines; however,
// it's still really useful as an invariant, so we'll incorporate that
// property and its proof here as well.
include "ch05exercise03.dfy"

// This Dafny "abstract module" establishes the proof obligations for the
// refinement: later in the file you will be obligated to fill in the function
// and lemma bodies in a module that `refines` this one.
// (This structure is a nice way to separate the statement of the theorem from
// its proof.)
abstract module RefinementTheorem {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary
  import opened DistributedSystem
  import opened TwoPCInvariantProof
  import AtomicCommit

  ghost function VariablesAbstraction(v: DistributedSystem.Variables) : AtomicCommit.Variables
    requires v.WF()

  ghost predicate Inv(v: DistributedSystem.Variables)

  lemma RefinementInit(v: DistributedSystem.Variables)
    requires DistributedSystem.Init(v)
    ensures Inv(v)
    ensures AtomicCommit.Init(VariablesAbstraction(v))

  lemma RefinementNext(v: DistributedSystem.Variables, v': DistributedSystem.Variables, event: Event)
    requires DistributedSystem.Next(v, v', event)
    requires Inv(v)
    ensures Inv(v')
    ensures AtomicCommit.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event) ||
            (VariablesAbstraction(v) == VariablesAbstraction(v') && event == NoOpEvent)

}

module RefinementProof refines RefinementTheorem {
  // No imports needed because we inherited them from the abstract module RefinementTheorem
  import opened Obligations
  import opened CoordinatorHost

  // Here are some handy accessor functions for dereferencing the coordinator
  // and the participants out of the sequence in Hosts.
  ghost function CoordinatorVars(v: DistributedSystem.Variables) : CoordinatorHost.Variables
    requires v.WF()
  {
    Last(v.hosts).coordinator
  }

  // Here's a handy function to save you some typing.
  ghost function ParticipantCount(v: DistributedSystem.Variables) : nat
    requires v.WF()
  {
    CoordinatorVars(v).c.participantCount
  }

  // The main challenge of setting up a refinement: abstracting from the
  // low-level (protocol) state to the high-level (spec) state.
  ghost function Preferences(v: DistributedSystem.Variables) : seq<Vote>
    requires v.WF()
  {
    // DONE: fill in here (solution: 1 line)
    seq(ParticipantCount(v), index requires 0 <= index < ParticipantCount(v) => v.hosts[index].participant.c.preference)
    // END EDIT
  }

  ghost function VariablesAbstraction(v: DistributedSystem.Variables) : AtomicCommit.Variables
  {
    // DONE: fill in here (solution: 3 lines)
    var decisions := seq(ParticipantCount(v), index requires 0 <= index < ParticipantCount(v) => v.hosts[index].participant.decision);
    AtomicCommit.Variables(Preferences(v), decisions)   // Replace me
    // END EDIT
  }

  ghost predicate Inv(v: DistributedSystem.Variables)
  {
    // Just point at the invariant from the chapter05 proof (in exercise03).
    // Be certain to fully-qualify the invariant name (mention its module
    // explicitly) to avoid inadvertently referring to the shadowing definition
    // RefinementTheorem.Inv.
    // DONE: fill in here (solution: 1 line)
    // && v.WF()
    && TwoPCInvariantProof.Inv(v)
    // END EDIT
  }

  lemma RefinementInit(v: DistributedSystem.Variables)
    // Obligations inherited from RefinementTheorem.RefinementInit
    // requires DistributedSystem.Init(v)
    // ensures Inv(v)
    // ensures AtomicCommit.Init(VariablesAbstraction(v))
  {
  }

  lemma RefinementNext(v: DistributedSystem.Variables, v': DistributedSystem.Variables, event: Event)
    // Obligations inherited from RefinementTheorem.RefinementNext
    // requires DistributedSystem.Next(v, v', event)
    // requires Inv(v)
    // ensures Inv(v')
    // ensures AtomicCommit.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    // Advice: appeal to the existing proof to get Inv(v')!
    assert Inv(v);
    assert Inv(v') by {
      // DONE: fill in here (solution: 1 line)
      TwoPCInvariantProof.InvInductive(v, v', event);
      // END EDIT
    }

    // The "new" part of this proof is to explain which AtomicCommit
    // (spec-level) action happened in response to each 2PC (protocol-level)
    // action. So the general strategy is: use skolemization (var :|) to "learn"
    // which thing happened in the DistributedSystem, split the cases, and
    // assert the right AtomicCommit.NextStep() predicate. Mostly, Dafny needs
    // those asserts because they're witnesses to the `exists` in AtomicCommit.Next().
    // DONE: fill in here (solution: 51 lines)
    assert AtomicCommit.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event) by {
      // from ch05exercise03.dfy
      var step :| DistributedSystem.NextStep(v, v', event, step);
      assert step.HostActionStep?;
      var hostId := step.hostId;
      var msgOps := step.msgOps;
      if v.hosts[hostId].CoordinatorVariables? {
        // assert event.NoOpEvent?;
        // coordinator proof
        // assert hostId == |v.hosts| - 1; // this is the coordinator
        // assert forall hostId':HostId | ValidParticipantId(v, hostId') ::
        //     ParticipantVars(v', hostId') == ParticipantVars(v, hostId');
        // var cstep :| CoordinatorHost.NextStep(CoordinatorVars(v), CoordinatorVars(v'), cstep, msgOps, event);
        // match cstep {
        //   case SendReqStep => { return; }
        //   case LearnVoteStep => { return; }
        //   case DecideStep(decision) => { return; }
        // }
        return;
      } else {
        // participant proof
        assert v.hosts[hostId].ParticipantVariables?;
        var pstep :| ParticipantHost.NextStep(ParticipantVars(v, hostId), ParticipantVars(v', hostId), pstep, msgOps, event);
        assert ParticipantVars(v', hostId).c == ParticipantVars(v, hostId).c;
        assert forall hostId':HostId | ValidParticipantId(v, hostId') && hostId' != hostId
            :: ParticipantVars(v', hostId') == ParticipantVars(v, hostId');
        match pstep {
          case VoteStep => {
            assert CoordinatorVars(v') == CoordinatorVars(v);
            assert CoordinatorStateSupportedByVote(v');
            if ParticipantVars(v, hostId).c.preference.No? {
              assert ParticipantVars(v', hostId).decision.Some?;
              assert ParticipantVars(v', hostId).decision.value == Abort;

              if ParticipantVars(v, hostId).decision.None? {
                assert VariablesAbstraction(v).decisions[hostId].None?;
                assert VariablesAbstraction(v).preferences[hostId].No?;
                assert AtomicCommit.NextStep(
                  VariablesAbstraction(v), 
                  VariablesAbstraction(v'), 
                  event, 
                  AtomicCommit.DecideStep(hostId)
                );
                return;
              }
              else {
                // assert AtomicCommit.NextStep(
                //   VariablesAbstraction(v), 
                //   VariablesAbstraction(v'), 
                //   event, 
                //   AtomicCommit.NoOpStep()
                // );
                return;
              }

              // if event.ParticipantLearnsEvent? {
              //   assert ParticipantVars(v, hostId).decision.None?;
              //   return;
              // }
              // else {
              //   assert event.NoOpEvent?;
              //   return;
              // }
            }
            assert ParticipantVars(v', hostId) == ParticipantVars(v, hostId);
            assert SafetyAC1(v');
            assert SafetyAC3(v');
            assert SafetyAC4(v');
            return;
          }
          case LearnDecisionStep => { 
            if ParticipantVars(v, hostId).decision.None? {
              // assert event.ParticipantLearnsEvent?;
              assert (forall i:HostId | i < ParticipantCount(v) :: ParticipantVars(v, i).c.preference == VariablesAbstraction(v).preferences[i]);
              assert AtomicCommit.NextStep(
                VariablesAbstraction(v), 
                VariablesAbstraction(v'), 
                event, 
                AtomicCommit.DecideStep(hostId)
              );
              return;
            }
            else {
              // assert AtomicCommit.NextStep(
              //   VariablesAbstraction(v), 
              //   VariablesAbstraction(v'), 
              //   event, 
              //   AtomicCommit.NoOpStep()
              // );
              return;
            }
            return;
          }
        }
      }
    }
    // END EDIT
  }
}
