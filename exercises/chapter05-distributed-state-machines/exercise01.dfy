// Two Phase Commit Model
// Model a distributed protocol using compound state machines.

// Your goal is to model a 2-Phase Commit protocol. You're modeling a single
// instance of the problem -- a designated coordinator, no concurrent
// instances. Furthermore, you may assume there are no coordinator or
// participant failures. This is indeed a fairly simplistic setting, but it's
// still nontrivial, and is a nice example for reasoning about the
// state-machine composition framework.
//
// The input to the algorithm is that each participant has a Yes/No preference.
// The output is that each participant learns a decision value based on the
// collective preferences.
//
// 2-Phase Commit Protocol English design doc:
//
// 1, Coordinator sends VOTE-REQ to all participants.
// 2. Each participant i sends back Vote(vote_i) to coordinator according to its
//    local preference.
//    Optimization: if vote_i=No then i sets decision_i := Abort (rather than
//    waiting for a decision from the coordinator)
// 3. Coordinator collects votes.
//    If all votes are yes then coordinator sets local decision_c := Commit and
//    sends Commit to all participants.
//      else coordinator sets decision_c := Abort and sends Abort to all
//      participants who voted yes.
// 4. Participants receiving Commit set decision_i := Commit
//
// This file provides a lot of helpful framework. You only need to
// define Types.Message and then fill in the state machine types and actions
// in module CoordinatorHost and module ParticipantHost.
//
// Unlike chapter01, where you could work through each file sequentially,
// WE STRONGLY ENCOURAGE YOU to read the entire file before beginning
// work. Later pieces of the file are helpful, for example by explaining
// the network model you're working in.

include "UtilitiesLibrary.dfy"
include "CommitTypes.dfy"

module Types {
  import opened UtilitiesLibrary
  import opened CommitTypes

  type HostId = nat

  // Have to define our message datatype so network can refer to it.
  // (There are cleverer ways to parameterize the network module, but
  // we're trying to avoid getting fancy with the Dafny module system.)
  datatype Message =
      // FIXME: fill in here (solution: 3 lines)
    | MessageRequest(receiver: HostId)
    | MessageResponse(sender: HostId, vote: Vote)
    | MessageDecision(receiver: HostId, decision: Decision)
      // END EDIT

  // A MessageOps is a "binding variable" used to connect a Host's Next step
  // (what message got received, what got sent?) with the Network (only allow
  // receipt of messages sent prior; record newly-sent messages).
  // Note that both fields are Option. A step predicate can say recv.None?
  // to indicate that it doesn't need to receive a message to occur.
  // It can say send.None? to indicate that it doesn't want to transmit a message.
  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

// There are two host roles in 2PCoordinator and Participant. We'll define
// separate state machines for each.
// This state machine defines how a coordinator host should behave: what state
// it records, and what actions it's allowed to take in response to incoming
// messages (or spontaneously by thinking about its existing state).
module CoordinatorHost {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(participantCount: nat)

  datatype Variables = Variables(
    c: Constants,
    decision: Option<Decision>,
    // FIXME: fill in here (solution: 1 line)
    participant_votes: seq<Option<Vote>>
    // END EDIT
  )
  {
    ghost predicate WF() {
      // FIXME: fill in here (solution: 1 line)
      && c.participantCount > 0
      && c.participantCount == |participant_votes|
         // END EDIT
    }

    ghost predicate HasParticipantCount(participantCount: nat)
    {
      c.participantCount == participantCount
    }
  }

  ghost predicate Init(v: Variables)
  {
    // FIXME: fill in here (solution: 5 lines)
    && v.WF()
    && v.decision.None?
    && (forall i:HostId | i < |v.participant_votes| :: v.participant_votes[i].None?)
    && v.c.participantCount == |v.participant_votes|
       // END EDIT
  }

  // Protocol steps. Define an action predicate for each step of the protocol
  // that the coordinator is involved in.
  // Hint: it's probably easiest to separate the receipt and recording of
  // incoming votes from detecting that all have arrived and making a decision.
  // FIXME: fill in here (solution: 46 lines)

  ghost predicate RequestVote(v: Variables, v': Variables, msgOps: MessageOps, receiver: HostId)
  {
    && v.WF()
    && v'.WF()
    && v'.HasParticipantCount(v.c.participantCount)
    && msgOps.send.Some? // sending something
    && msgOps.send.value == MessageRequest(receiver)
    && receiver < |v.participant_votes| // bound check
    && v.participant_votes[receiver].None? // receiver does not have a decision yet
    && v == v' // no change of state variables
  }

  ghost predicate ReceiveVote(v: Variables, v': Variables, msgOps: MessageOps, sender: HostId, vote: Vote)
  {
    && v.WF()
    && v'.WF()
    && v'.HasParticipantCount(v.c.participantCount)
    && msgOps.recv.Some?  // receiving something
    && msgOps.recv.value == MessageResponse(sender, vote)
    && sender < |v.participant_votes|
    && v.participant_votes[sender].None? // participant has no decision before
    && v'.participant_votes[sender].Some? // he has now
    && v'.participant_votes[sender].value == vote // also assign
       // rest of the state variable same
    && (forall i:HostId | i < |v.participant_votes| && i != sender :: v.participant_votes[i] == v'.participant_votes[i])
    && v.c == v'.c
    && v.decision.None?
    && v'.decision.None?
  }

  // decides
  ghost function Decide(v: Variables): Option<Decision>
  {
    if (forall i:HostId | i < |v.participant_votes| :: v.participant_votes[i] == Some(Yes)) then Some(Commit)
    else Some(Abort)
  }

  ghost predicate DecideVote(v: Variables, v': Variables)
  {
    && v.WF()
    && v'.WF()
    && v'.HasParticipantCount(v.c.participantCount)
    && v.decision.None? // coordinator has no decision before
    && v'.decision.Some? // coordinator will have now
    && (forall i:HostId | i < |v.participant_votes| :: v.participant_votes[i].Some?) // before, all decision should arrive
    && v'.decision == Decide(v) // decision based on logic
       // rest of the state variable same
    && v.c == v'.c
    && v.participant_votes == v'.participant_votes
  }


  ghost predicate AnnounceDecision(v: Variables, v': Variables, msgOps: MessageOps, receiver: HostId, decision: Decision)
  {
    && v.WF()
    && v'.WF()
    && v'.HasParticipantCount(v.c.participantCount)
    && v.decision.Some?
    && v.decision.value == decision
    && receiver < |v.participant_votes|
    && v.participant_votes[receiver].Some?
    && v.participant_votes[receiver].value == Yes
    && msgOps.send.Some?  // receiving something
    && msgOps.send.value == MessageDecision(receiver, decision)
    && v == v'
  }
  // END EDIT

  // JayNF
  datatype Step =
      // FIXME: fill in here (solution: 3 lines)
    | RequestVoteStep(receiver: HostId)
    | ReceiveVoteStep(sender: HostId, vote: Vote)
    | DecideVoteStep
    | AnnounceDecisionStep(receiver: HostId, decision: Decision)
      // END EDIT

  // msgOps is a "binding variable" -- the host and the network have to agree
  // on its assignment to make a valid transition. So the host explains what
  // would happen if it could receive a particular message, and the network
  // decides whether such a message is available for receipt.
  ghost predicate NextStep(v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
    // FIXME: fill in here (solution: 3 lines)
    case RequestVoteStep(receiver) => RequestVote(v, v', msgOps, receiver)
    case ReceiveVoteStep(sender, vote) => ReceiveVote(v, v', msgOps, sender, vote)
    case DecideVoteStep() => DecideVote(v, v')
    case AnnounceDecisionStep(receiver, decision) => AnnounceDecision(v, v', msgOps, receiver, decision)
    // END EDIT
  }

  lemma NextStepDeterministicGivenStep(v: Variables, v'1: Variables, v'2: Variables, step: Step, msgOps: MessageOps)
    requires NextStep(v, v'1, step, msgOps)
    requires NextStep(v, v'2, step, msgOps)
    ensures v'1 == v'2
  {}

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(v, v', step, msgOps)
  }

  // proving correctness of Coordinator
  lemma PseudoLiveness(participantCount: nat) returns (behavior:seq<Variables>, messages:seq<MessageOps>)
    requires participantCount == 1
    ensures 1 < |behavior|
    ensures 0 < |messages|
    ensures |behavior| == |messages| + 1
    ensures Init(behavior[0])
    ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1], messages[i])
    ensures Last(behavior).WF()
    ensures Last(behavior).decision == Some(Commit)
  {
    // --------- BEGIN: INIT -------------

    var v0 := Variables(
      c := Constants(participantCount),
      decision := None,
      participant_votes := [None]
    );
    assert Init(v0);

    // ---------- STEP: REQ -------------

    var m0 := MessageOps(
      recv := None,
      send := Some(MessageRequest(receiver := 0))
    );
    var s0 := RequestVoteStep(receiver := 0);
    var v1 := Variables(
      c := Constants(participantCount),
      decision := None,
      participant_votes := [None]
    );
    assert NextStep(v0, v1, s0, m0);

    // ---------- STEP: RESP -------------

    var m1 := MessageOps(
      recv := Some(MessageResponse(sender := 0, vote := Yes)),
      send := None
    );
    var s1 := ReceiveVoteStep(sender := 0, vote := Yes);
    var v2 := Variables(
      c := Constants(participantCount),
      decision := None,
      participant_votes := [Some(Yes)]
    );
    assert NextStep(v1, v2, s1, m1);

    // ---------- STEP: DECIDE -------------

    var m2 := MessageOps(
      recv := None,
      send := None
    );
    var s2 := DecideVoteStep();
    var v3 := Variables(
      c := Constants(participantCount),
      decision := Some(Commit),
      participant_votes := [Some(Yes)]
    );
    assert NextStep(v2, v3, s2, m2);

    // ========== RETURN ============

    behavior := [v0, v1, v2, v3];
    messages := [m0, m1, m2];
  }
}

module ParticipantHost {
  import opened CommitTypes
  import opened Types
  import opened UtilitiesLibrary

  datatype Constants = Constants(hostId: HostId, preference: Vote)

  datatype Variables = Variables(c: Constants, decision: Option<Decision>)
  {
    ghost predicate WF() {
      // FIXME: fill in here (solution: 1 line)
      && c.hostId >= 0
      && (c.preference == Yes || c.preference == No)
         // END EDIT
    }

    ghost predicate HasHostId(hostId: HostId)
    {
      c.hostId == hostId
    }
  }

  ghost predicate Init(v: Variables)
  {
    // FIXME: fill in here (solution: 1 line)
    && v.WF()
    && v.decision.None?
       // END EDIT
  }

  // Protocol steps. Define an action predicate for each step of the protocol
  // that participant can take.
  // FIXME: fill in here (solution: 20 lines)

  ghost predicate ReceiveRequest(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF()
    && v'.WF()
    && v.c == v'.c
    && v.decision.None? && v'.decision.None? // no decision now
    && msgOps.recv.Some?
    && msgOps.recv.value == MessageRequest(v.c.hostId)
  }

  // ghost predicate ReceiveRespondRequest(v: Variables, v': Variables, msgOps: MessageOps)
  // {
  //   && v.WF()
  //   && v'.WF()
  //   && v.c == v'.c
  //   && v.decision.None? 
  //   && ((v.c.preference == No) ==> (v'.decision.Some? && v'.decision.value == Abort))
  //   && ((v.c.preference == Yes) ==> (v'.decision == v.decision))
  //   && msgOps.send.Some?
  //   && msgOps.send.value == MessageResponse(v.c.hostId, v.c.preference)
  //   && msgOps.recv.Some?
  //   && msgOps.recv.value == MessageRequest(v.c.hostId)
  // }

  ghost predicate RespondVote(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF()
    && v'.WF()
    && v.c == v'.c
    && v.decision.None?
    && ((v.c.preference == No) ==> (v'.decision.Some? && v'.decision.value == Abort))
    && ((v.c.preference == Yes) ==> (v'.decision == v.decision))
    && msgOps.send.Some?
    && msgOps.send.value == MessageResponse(v.c.hostId, v.c.preference)
  }

  ghost predicate ReceiveDecision(v: Variables, v': Variables, msgOps: MessageOps, decision: Decision)
  {
    && v.WF()
    && v'.WF()
    && v.c == v'.c
    && v.c.preference == Yes
    && v.decision.None?
    && v'.decision.Some?
    && v'.decision.value == decision
    && msgOps.recv.Some?
    && msgOps.recv.value == MessageDecision(v.c.hostId, decision)
  }

  // END EDIT

  // JayNF
  datatype Step =
      // FIXME: fill in here (solution: 2 lines)
    | ReceiveRequestStep
    | RespondVoteStep
    | ReceiveDecisionStep(decision: Decision)
      // END EDIT

  ghost predicate NextStep(v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
    // FIXME: fill in here (solution: 2 lines)
    case ReceiveRequestStep => ReceiveRequest(v, v', msgOps)
    case RespondVoteStep => RespondVote(v, v', msgOps)
    case ReceiveDecisionStep(decision) => ReceiveDecision(v, v', msgOps, decision)
    // END EDIT
  }

  lemma NextStepDeterministicGivenStep(v: Variables, v'1: Variables, v'2: Variables, step: Step, msgOps: MessageOps)
    requires NextStep(v, v'1, step, msgOps)
    requires NextStep(v, v'2, step, msgOps)
    ensures v'1 == v'2
  {}

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(v, v', step, msgOps)
  }

  // proving correctness of Participant
  lemma PseudoLiveness(participantCount: nat) returns (behavior:seq<Variables>, messages:seq<MessageOps>)
    requires participantCount == 1
    ensures 1 < |behavior|
    ensures 0 < |messages|
    ensures |behavior| == |messages| + 1
    ensures Init(behavior[0])
    ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1], messages[i])
    ensures Last(behavior).WF()
    ensures Last(behavior).decision == Some(Commit)
  {
    // --------- BEGIN: INIT -------------

    var v0 := Variables(
      c := Constants(hostId := 0, preference := Yes),
      decision := None
    );
    assert Init(v0);

    // ---------- STEP: REQ -------------

    var m0 := MessageOps(
      recv := Some(MessageRequest(receiver := 0)),
      send := None
    );
    var s0 := ReceiveRequestStep();
    var v1 := Variables(
      c := Constants(hostId := 0, preference := Yes),
      decision := None
    );
    assert NextStep(v0, v1, s0, m0);

    // ---------- STEP: RESP -------------

    var m1 := MessageOps(
      recv := None,
      send := Some(MessageResponse(sender := 0, vote := Yes))
    );
    var s1 := RespondVoteStep();
    var v2 := Variables(
      c := Constants(hostId := 0, preference := Yes),
      decision := None
    );
    assert NextStep(v1, v2, s1, m1);

    // ---------- STEP: DECIDE -------------

    var m2 := MessageOps(
      recv := Some(MessageDecision(receiver := 0, decision := Commit)),
      send := None
    );
    var s2 := ReceiveDecisionStep(decision := Commit);
    var v3 := Variables(
      c := Constants(hostId := 0, preference := Yes),
      decision := Some(Commit)
    );
    assert NextStep(v2, v3, s2, m2);

    // ========== RETURN ============

    behavior := [v0, v1, v2, v3];
    messages := [m0, m1, m2];
  }
}

// We define a generic Host as able to be either of the specific roles.
// This is the ultimate (untrusted) definition of the protocol we're
// trying to verify.
// This definition is given to you to clarify how the two protocol roles above
// are pulled together into the ultimate distributed system.
module Host {
  import opened UtilitiesLibrary
  import opened CommitTypes
  import opened Types
  import CoordinatorHost
  import ParticipantHost

  datatype Variables =
    | CoordinatorVariables(coordinator: CoordinatorHost.Variables)
    | ParticipantVariables(participant: ParticipantHost.Variables)
  {
    ghost predicate WF() {
      // subtype WF satisfied
      && (match this
          case CoordinatorVariables(_) => coordinator.WF()
          case ParticipantVariables(_) => participant.WF()
      )
    }
  }

  // What property must be true of any group of hosts to run the protocol?
  // Generic DistributedSystem module calls back into this predicate to ensure
  // that it has a well-formed *group* of hosts.
  ghost predicate GroupWFConstants(grp: seq<Variables>)
  {
    // There must at least be a coordinator
    && 0 < |grp|
       // Last host is a coordinator
    && Last(grp).CoordinatorVariables?
       // All the others are participants
    && (forall hostid:HostId | hostid < |grp|-1 :: grp[hostid].ParticipantVariables?)
       // The coordinator's constants must correctly account for the number of participants
    && Last(grp).coordinator.HasParticipantCount(|grp|-1)
       // The participants's constants must match their group positions.
       // (Actually, they just need to be distinct from one another so we get
       // non-conflicting votes, but this is an easy way to express that property.)
    && (forall hostid:HostId | hostid < |grp|-1
          :: grp[hostid].participant.HasHostId(hostid))
  }

  ghost predicate GroupWF(grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_v)
       // Each host is well-formed
    && (forall hostid:HostId | hostid < |grp_v| :: grp_v[hostid].WF())
  }

  // Generic DistributedSystem module calls back into this predicate to give
  // the protocol an opportunity to set up constraints across the various
  // hosts.  Protocol requires one coordinator and the rest participants;
  // coordinator must know how many participants, and participants must know
  // own ids.
  ghost predicate GroupInit(grp_v: seq<Variables>)
  {
    // constants & variables are well-formed (same number of host slots as constants expect)
    && GroupWF(grp_v)
       // Coordinator is initialized to know about the N-1 participants.
    && CoordinatorHost.Init(Last(grp_v).coordinator)
       // Participants initted with their ids.
    && (forall hostid:HostId | hostid < |grp_v|-1 ::
          ParticipantHost.Init(grp_v[hostid].participant)
       )
  }

  // Dispatch Next to appropriate underlying implementation.
  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF()
       // needed to justify types below
    && v'.CoordinatorVariables? == v.CoordinatorVariables?
    && (match v
        case CoordinatorVariables(_) => CoordinatorHost.Next(v.coordinator, v'.coordinator, msgOps)
        case ParticipantVariables(_) => ParticipantHost.Next(v.participant, v'.participant, msgOps)
       )
  }
}

// The (trusted) model of the environment: There is a network that can only deliver
// messages that some Host (running the protocol) has sent, but once sent, messages
// can be delivered repeatedly and in any order.
// This definition is given to you because it's a common assumption you can
// reuse. Someday you might decide to assume a different network model (e.g.
// reliable or at-most-once delivery), but this is a good place to start.
module Network {
  import opened CommitTypes
  import opened Types

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
       // Record the sent message, if there was one.
    && v'.sentMsgs ==
       v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}

// The (trusted) model of the distributed system: hosts don't share memory. Each
// takes its steps independently, interleaved in nondeterministic order with others.
// They only communicate through the network, and obey the communication model
// established by the Network model.
// This is given to you; it can be reused for just about any shared-nothing-concurrency
// protocol model.
module DistributedSystem {
  import opened UtilitiesLibrary
  import opened CommitTypes
  import opened Types
  import Network
  import Host
  import CoordinatorHost
  import ParticipantHost

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }

    ghost predicate WF() {
      && Host.GroupWF(hosts)
    }
  }

  ghost predicate Init(v: Variables)
  {
    && v.WF()
    && Host.GroupInit(v.hosts)
    && Network.Init(v.network)
  }

  ghost predicate HostAction(v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
  {
    && v.WF()
    && v.ValidHostId(hostid)
    && |v'.hosts| == |v.hosts|
    && Host.Next(v.hosts[hostid], v'.hosts[hostid], msgOps)
       // all other hosts UNCHANGED
    && (forall otherHost:nat | v.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
  }

  // JayNF is pretty simple as there's only a single action disjunct
  datatype Step =
    | HostActionStep(hostId: HostId, msgOps: MessageOps)

  ghost predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    && HostAction(v, v', step.hostId, step.msgOps)
       // network agrees recv has been sent and records sent
    && Network.Next(v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
  }

  ghost function GetDecisionForHost(hv: Host.Variables) : Option<Decision>
  {
    match hv
    case CoordinatorVariables(coordinator) => coordinator.decision
    case ParticipantVariables(participant) => participant.decision
  }

  // Convince us that your model does something
  lemma PseudoLiveness() returns (behavior: seq<Variables>)
    // requires |c.hosts| == 2 // There's exactly one voting participant...
    // requires c.hosts[0].participant.preference.Yes? // ... who wants a Yes.
    // Exhibit a behavior that satisfies your state machine...
    ensures 0 < |behavior|
    ensures Init(behavior[0])
    ensures forall i:nat | i < |behavior|-1 :: Next(behavior[i], behavior[i+1])
    // ...and all the participants arrive at a decision.
    ensures Last(behavior).WF()
    ensures forall hostid:HostId | Last(behavior).ValidHostId(hostid)
              :: GetDecisionForHost(Last(behavior).hosts[hostid]) == Some(Commit)
  {
    // FIXME: fill in here (solution: 60 lines)

    var pid := 0;
    var cid := 1;

    var v0 := Variables(
      hosts := [
        Host.ParticipantVariables(
          ParticipantHost.Variables(
            c := ParticipantHost.Constants(
              hostId := pid,
              preference := Yes
            ),
            decision := None
          )
        ),
        // coordinator is the last host
        Host.CoordinatorVariables(
          CoordinatorHost.Variables(
            c := CoordinatorHost.Constants(
              participantCount := 1
            ),
            decision := None,
            participant_votes := [None]
          )
        )
      ],
      network := Network.Variables(
        sentMsgs := {}
      )
    );

    assert Init(v0);

    // -------------- STEP 1: Request -------------------

    var v1 := Variables(
      hosts := [
        Host.ParticipantVariables(
          ParticipantHost.Variables(
            c := ParticipantHost.Constants(
              hostId := pid,
              preference := Yes
            ),
            decision := None
          )
        ),
        Host.CoordinatorVariables(
          CoordinatorHost.Variables(
            c := CoordinatorHost.Constants(
              participantCount := 1
            ),
            decision := None,
            participant_votes := [None]
          )
        )
      ],
      network := Network.Variables(
        sentMsgs := {
          MessageRequest(receiver := 0)
        }
      )
    );
    var s0 := HostActionStep(
      hostId := cid,
      msgOps := MessageOps(
        recv := None,
        send := Some(MessageRequest(receiver := pid))
      )
    );

    var s0_h := CoordinatorHost.RequestVoteStep(receiver := pid);
    assert CoordinatorHost.NextStep(v0.hosts[cid].coordinator, v1.hosts[cid].coordinator, s0_h, s0.msgOps);
    assert NextStep(v0, v1, s0);
    assert Next(v0, v1);


    // -------------- STEP 1: Receive -------------------

    var v2 := Variables(
      hosts := [
        Host.ParticipantVariables(
          ParticipantHost.Variables(
            c := ParticipantHost.Constants(
              hostId := pid,
              preference := Yes
            ),
            decision := None
          )
        ),
        Host.CoordinatorVariables(
          CoordinatorHost.Variables(
            c := CoordinatorHost.Constants(
              participantCount := 1
            ),
            decision := None,
            participant_votes := [None]
          )
        )
      ],
      network := Network.Variables(
        sentMsgs := {
          MessageRequest(receiver := pid)
        }
      )
    );
    var s1 := HostActionStep(
      hostId := pid,
      msgOps := MessageOps(
        recv := Some(MessageRequest(receiver := pid)),
        send := None
      )
    );

    var s1_h := ParticipantHost.ReceiveRequestStep();
    assert ParticipantHost.NextStep(v1.hosts[pid].participant, v2.hosts[pid].participant, s1_h, s1.msgOps);
    assert NextStep(v1, v2, s1);
    assert Next(v1, v2);


    // -------------- STEP 3: Respond -------------------

    var v3 := Variables(
      hosts := [
        Host.ParticipantVariables(
          ParticipantHost.Variables(
            c := ParticipantHost.Constants(
              hostId := pid,
              preference := Yes
            ),
            decision := None
          )
        ),
        Host.CoordinatorVariables(
          CoordinatorHost.Variables(
            c := CoordinatorHost.Constants(
              participantCount := 1
            ),
            decision := None,
            participant_votes := [None]
          )
        )
      ],
      network := Network.Variables(
        sentMsgs := {
          MessageRequest(receiver := pid),
          MessageResponse(sender := pid, vote := Yes)
        }
      )
    );
    var s2 := HostActionStep(
      hostId := pid,
      msgOps := MessageOps(
        recv := None,
        send := Some(MessageResponse(sender := pid, vote := Yes))
      )
    );

    var s2_h := ParticipantHost.RespondVoteStep();
    assert ParticipantHost.NextStep(v2.hosts[pid].participant, v3.hosts[pid].participant, s2_h, s2.msgOps);
    assert NextStep(v2, v3, s2);
    assert Next(v2, v3);

    // -------------- STEP 4: Receive Vote -------------------

    var v4 := Variables(
      hosts := [
        Host.ParticipantVariables(
          ParticipantHost.Variables(
            c := ParticipantHost.Constants(
              hostId := pid,
              preference := Yes
            ),
            decision := None
          )
        ),
        Host.CoordinatorVariables(
          CoordinatorHost.Variables(
            c := CoordinatorHost.Constants(
              participantCount := 1
            ),
            decision := None,
            participant_votes := [Some(Yes)]
          )
        )
      ],
      network := Network.Variables(
        sentMsgs := {
          MessageRequest(receiver := pid),
          MessageResponse(sender := pid, vote := Yes)
        }
      )
    );
    var s3 := HostActionStep(
      hostId := cid,
      msgOps := MessageOps(
        recv := Some(MessageResponse(sender := pid, vote := Yes)),
        send := None
      )
    );

    var s3_h := CoordinatorHost.ReceiveVoteStep(sender := pid, vote := Yes);
    assert CoordinatorHost.NextStep(v3.hosts[cid].coordinator, v4.hosts[cid].coordinator, s3_h, s3.msgOps);
    assert NextStep(v3, v4, s3);
    assert Next(v3, v4);

    // -------------- STEP 5: Decide -------------------

    var v5 := Variables(
      hosts := [
        Host.ParticipantVariables(
          ParticipantHost.Variables(
            c := ParticipantHost.Constants(
              hostId := pid,
              preference := Yes
            ),
            decision := None
          )
        ),
        Host.CoordinatorVariables(
          CoordinatorHost.Variables(
            c := CoordinatorHost.Constants(
              participantCount := 1
            ),
            decision := Some(Commit),
            participant_votes := [Some(Yes)]
          )
        )
      ],
      network := Network.Variables(
        sentMsgs := {
          MessageRequest(receiver := pid),
          MessageResponse(sender := pid, vote := Yes)
        }
      )
    );
    var s4 := HostActionStep(
      hostId := cid,
      msgOps := MessageOps(
        recv := None,
        send := None
      )
    );

    var s4_h := CoordinatorHost.DecideVoteStep();
    assert CoordinatorHost.NextStep(v4.hosts[cid].coordinator, v5.hosts[cid].coordinator, s4_h, s4.msgOps);
    assert NextStep(v4, v5, s4);
    assert Next(v4, v5);

    // -------------- STEP 6: Announce -------------------

    var v6 := Variables(
      hosts := [
        Host.ParticipantVariables(
          ParticipantHost.Variables(
            c := ParticipantHost.Constants(
              hostId := pid,
              preference := Yes
            ),
            decision := None
          )
        ),
        Host.CoordinatorVariables(
          CoordinatorHost.Variables(
            c := CoordinatorHost.Constants(
              participantCount := 1
            ),
            decision := Some(Commit),
            participant_votes := [Some(Yes)]
          )
        )
      ],
      network := Network.Variables(
        sentMsgs := {
          MessageRequest(receiver := pid),
          MessageResponse(sender := pid, vote := Yes),
          MessageDecision(receiver := pid, decision := Commit)
        }
      )
    );
    var s5 := HostActionStep(
      hostId := cid,
      msgOps := MessageOps(
        recv := None,
        send := Some(MessageDecision(receiver := pid, decision := Commit))
      )
    );

    var s5_h := CoordinatorHost.AnnounceDecisionStep(receiver := pid, decision := Commit);
    assert CoordinatorHost.NextStep(v5.hosts[cid].coordinator, v6.hosts[cid].coordinator, s5_h, s5.msgOps);
    assert NextStep(v5, v6, s5);
    assert Next(v5, v6);

    // -------------- STEP 6: Receive Decision -------------------

    var v7 := Variables(
      hosts := [
        Host.ParticipantVariables(
          ParticipantHost.Variables(
            c := ParticipantHost.Constants(
              hostId := pid,
              preference := Yes
            ),
            decision := Some(Commit)
          )
        ),
        Host.CoordinatorVariables(
          CoordinatorHost.Variables(
            c := CoordinatorHost.Constants(
              participantCount := 1
            ),
            decision := Some(Commit),
            participant_votes := [Some(Yes)]
          )
        )
      ],
      network := Network.Variables(
        sentMsgs := {
          MessageRequest(receiver := pid),
          MessageResponse(sender := pid, vote := Yes),
          MessageDecision(receiver := pid, decision := Commit)
        }
      )
    );
    var s6 := HostActionStep(
      hostId := pid,
      msgOps := MessageOps(
        recv := Some(MessageDecision(receiver := pid, decision := Commit)),
        send := None
      )
    );

    var s6_h := ParticipantHost.ReceiveDecisionStep(decision := Commit);
    assert ParticipantHost.NextStep(v6.hosts[pid].participant, v7.hosts[pid].participant, s6_h, s6.msgOps);
    assert NextStep(v6, v7, s6);
    assert Next(v6, v7);

    // =========== RETURN ==============

    behavior := [v0, v1, v2, v3, v4, v5, v6, v7];

    // END EDIT
  }
}
