// A synchronous model of two-phase commit, without a network between hosts.

datatype Option<T> = Some(value: T) | None

datatype Vote = Yes | No
datatype Decision = Commit | Abort

datatype Participant = Participant(pref: Vote, decision: Option<Decision>)
datatype Coordinator = Coordinator(prefs: seq<Option<Vote>>, decision: Option<Decision>)

datatype Variables = Variables(participants: seq<Participant>, coordinator: Coordinator)
{
  ghost predicate WF() {
    |coordinator.prefs| == |participants|
  }

  ghost predicate ValidId(i: int) {
    0 <= i < |participants|
  }
}

ghost predicate Init(v: Variables) {
  && v.WF()
  && (forall i | v.ValidId(i) :: v.participants[i].decision.None?) // pref is arbitrary
  && (forall i | v.ValidId(i) :: v.coordinator.prefs[i] == None)
  && v.coordinator.decision == None
}

datatype Step =
    /* | VoteReq */ // instead of a VoteReq step, participants can always send pref
  | VoteRespStep(i: nat) // one participant sends its pref to coordinator
  | CoordDecideStep // coordinator decides when it has all prefs
  | DecisionAnnounceStep(i: nat, decision: Decision) // coordinator tells one participant the outcome

ghost predicate VoteResp(v: Variables, v': Variables, step: Step)
  requires step.VoteRespStep?
{
  && v.WF()
  && v.ValidId(step.i)
  && var pref := v.participants[step.i].pref;
  && v'.coordinator.prefs == v.coordinator.prefs[step.i := Some(pref)]
  && v'.coordinator.decision == v.coordinator.decision
  && v'.participants == v.participants
}

ghost predicate CoordinatorDecide(v: Variables, v': Variables, step: Step)
  requires step.CoordDecideStep?
{
  && v.WF()
  && (forall i | v.ValidId(i) :: v.coordinator.prefs[i].Some?)
  && v'.coordinator.prefs == v.coordinator.prefs
     // tareq
  && v.coordinator.decision.None?
     //
  && v'.coordinator.decision ==
     Some(if (forall i | v.ValidId(i) :: v.coordinator.prefs[i].value == Yes) then Commit else Abort)
  && v'.participants == v.participants
}

ghost predicate DecisionAnnounce(v: Variables, v': Variables, step: Step)
  requires step.DecisionAnnounceStep?
{
  && v.WF()
  && var i := step.i;
  && v.ValidId(i)
  && v.coordinator.decision.Some?
  && v.coordinator.decision.value == step.decision
  && v'.coordinator == v.coordinator
     // tareq
  && v.participants[i].decision.None?
     //
  && v'.participants == v.participants[i := v.participants[i].(decision := Some(step.decision))]
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case VoteRespStep(i) => VoteResp(v, v', step)
    case CoordDecideStep => CoordinatorDecide(v, v', step)
    case DecisionAnnounceStep(i, decision) => DecisionAnnounce(v, v', step)
  }
}

lemma NextStepDeterministicGivenStep(v: Variables, v'1: Variables, v'2: Variables, step: Step)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  ensures v'1 == v'2
{}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

// participants reach consensus (at most one decision)
ghost predicate Consensus(v: Variables)
  requires v.WF()
{
  forall i, j | v.ValidId(i) && v.ValidId(j) ::
    v.participants[i].decision.Some? && v.participants[j].decision.Some? ==>
      v.participants[i].decision.value == v.participants[j].decision.value
}

// Edit: Start
ghost predicate AllParticipantVotedYes(v: Variables)
{
  && v.WF()
  && forall i | v.ValidId(i) :: v.participants[i].pref == Yes
}

ghost predicate AnyParticipantVotedNo(v: Variables)
{
  && v.WF()
  && exists i | v.ValidId(i) :: v.participants[i].pref == No
}

ghost predicate AllDecided(v: Variables, decision: Decision)
{
  && v.WF()
  && (forall i | v.ValidId(i) :: v.participants[i].decision == Some(decision))
  && v.coordinator.decision == Some(decision)
}
// Edit: End

// must reach commit if all participants vote yes
ghost predicate CommitSafe(v: Variables)
  requires v.WF()
{
  // FIXME: fill in here (solution: 3 lines)
  // if all participants vote yes ==> all decision must be commit
  && (AllDecided(v, Commit) ==> AllParticipantVotedYes(v))
  // END EDIT
}

// must reach abort if any participant votes no
ghost predicate AbortSafe(v: Variables)
  requires v.WF()
{
  // FIXME: fill in here (solution: 3 lines)
  // if any participants vote no ==> all decision must be abort
  && AllDecided(v, Abort) ==> (AnyParticipantVotedNo(v))
  // END EDIT
}

ghost predicate Safety(v: Variables)
{
  && v.WF()
  && Consensus(v)
  && CommitSafe(v)
  && AbortSafe(v)
}

// Define your inductive invariant here.

// FIXME: fill in here (solution: 34 lines)
ghost predicate VoteMatchesCoordinatorData(v: Variables)
{
  && v.WF()
  && forall i | v.ValidId(i) && v.coordinator.prefs[i].Some? :: v.coordinator.prefs[i].value == v.participants[i].pref
}

ghost predicate DecisionAfterAllVotes(v: Variables)
{
  && v.WF()
  && (v.coordinator.decision.Some? ==> (forall i | v.ValidId(i) :: v.coordinator.prefs[i].Some?))
}

ghost predicate ParticipantCannotDecideBeforeCoordinator(v: Variables)
{
  && v.WF()
  && (v.coordinator.decision.None? ==> (forall i | v.ValidId(i) :: v.participants[i].decision.None?))
}

ghost predicate ParticipantReceivedDecisionAfterCoordDecided(v: Variables)
{
  && v.WF()
  && ((forall i | v.ValidId(i) :: v.participants[i].decision.Some?) ==> (
          && v.coordinator.decision.Some?
          && (forall i, j | v.ValidId(i) && v.ValidId(j) :: v.participants[i].decision.value == v.participants[j].decision.value)
        ))
}

ghost predicate CoordMadeCorrectDecision(v: Variables)
{
  && v.WF()
  && ((v.coordinator.decision == Some(Commit)) ==> (forall i | v.ValidId(i) :: v.coordinator.prefs[i] == Some(Yes)))
  && ((v.coordinator.decision == Some(Abort)) ==> (exists i | v.ValidId(i) :: v.coordinator.prefs[i] == Some(No)))
}

ghost predicate CoordCannotDecideBeforeGettingAllPrefs(v: Variables)
{
  && v.WF()
  && ((exists i | v.ValidId(i) :: v.coordinator.prefs[i].None?) ==> ( v.coordinator.decision.None?))
}
// END EDIT

ghost predicate Inv(v: Variables)
{
  // FIXME: fill in here (solution: 5 lines)
  && v.WF()
  && DecisionAfterAllVotes(v)
  && VoteMatchesCoordinatorData(v)
  && ParticipantCannotDecideBeforeCoordinator(v)
  && CoordMadeCorrectDecision(v)
  && CoordCannotDecideBeforeGettingAllPrefs(v)
  // && ParticipantReceivedDecisionAfterCoordDecided(v)
  && Safety(v)
     // END EDIT
}

lemma InvInit(v: Variables)
  requires Init(v)
  ensures Inv(v)
{}

lemma InvInductive(v: Variables, v': Variables)
  requires Inv(v) && Next(v, v')
  ensures Inv(v')
{
  // FIXME: fill in here (solution: 17 lines)
  var step :| NextStep(v, v', step);
  match step {
    case VoteRespStep(i) => {
      return;
    }
    case CoordDecideStep => {
      // assert forall i | v.ValidId(i) :: v.coordinator.prefs[i].Some?;
      // assert v.coordinator.decision.None?;
      return;
    }
    case DecisionAnnounceStep(i, decision) => {
      assert v.coordinator.decision == Some(decision);
      assert v.participants[i].decision.None?;
      assert v'.participants[i].decision == Some(decision);
      // assert (forall j | v'.ValidId(j) :: v'.participants[j].decision == Some(decision));
      return;
    }
  }
  // END EDIT
}

lemma InvSafety(v: Variables)
  requires Inv(v)
  ensures Safety(v)
{
}

lemma SafetyAlwaysHolds(v: Variables, v': Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
  if Init(v) { InvInit(v); }
  if Inv(v) && Next(v, v') { InvInductive(v, v'); }
  if Inv(v) { InvSafety(v); }
}
