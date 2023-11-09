// Midterm Project: Distributed lock server
// Build a distributed lock server. Define how a host implements your
// protocol in host.v.dfy; write your safety spec and proof here.

// This challenge differs from LockServer (from chapters 03 and 04) in two
// ways. First, there is no central server that coordinates the activity.
// Second, the hosts can communicate only via asynchronous messages; a single
// state machine transition cannot simultaneously read or update the state of
// two hosts.
//
// To guard against duplicate messages, the nodes associate a monotonically
// increasing epoch number with the lock. Initially, node 0 holds the lock and
// its epoch number is 1, while all other nodes with an epoch of 0 (and not
// holding the lock). A node that holds the lock can "grant" it to another
// node by sending them a "Grant" message which has an epoch number that is
// greater than the node's epoch number. A node that receives such a message
// will become the new holder and will set its epoch number to the message’s
// epoch number.

// You'll first need to modify 'host.v.dfy' to define the protocol message
// format and the host behavior.
// Then come back here to define the safety condition and prove that the
// distributed system made from that protocol maintains it.

// The ".t.dfy" extension in network.t.dfy and distributed_system.t.dfy
// indicates these files are _trusted_: they are assumed correct. In contrast,
// the ".v.dfy" in host.v.dfy indicates that the code in that file is verified.
// This file (exercise01.dfy) doesn't have an extension. It mixes some trusted
// code (your safety specification and the statement of the safety theorem) and
// untrusted, verified code (your inductive invariant). We mix these only to
// make navigating your code a bit simpler.

include "distributed_system.t.dfy"

module SafetySpec {
  import opened HostIdentifiers
  import DistributedSystem

  // Define this predicate to be true if idx is a valid host ID and that host's
  // Variables indicates that it holds the lock.
  ghost predicate HostHoldsLock(v:DistributedSystem.Variables, idx: int) {
    && v.WF()
    // DONE: fill in here (solution: 4 lines)
    && v.ValidHostId(idx)
    && v.hosts[idx].holdsLock
    // END EDIT
  }

  // No two hosts think they hold the lock simultaneously.
  ghost predicate Safety(v:DistributedSystem.Variables) {
    // DONE: fill in here (solution: 4 lines)
    && (forall i, j : int | HostHoldsLock(v, i) && HostHoldsLock(v, j) :: i == j)
    // && (exists i : int :: HostHoldsLock(v, i))
    // END EDIT
  }
}

module Proof {
  import opened HostIdentifiers
  import Host
  import opened DistributedSystem
  import opened SafetySpec

  // Here's a predicate that will be very useful in constructing inviariant
  // conjuncts. Your job is to figure out what this predicate should say about
  // the message, especially about epoch numbers: intuitively, an in-flight
  // message might be received, but a not-in-flight message will always be
  // ignored by hosts.

  ghost predicate InFlight(v:Variables, message:Host.Message) {
    && v.WF()
    && message in v.network.sentMsgs
    // DONE: fill in here (solution: 2 lines)
    && message.epoch > 0
    && |v.network.sentMsgs| > 0
    && (forall i : int | v.ValidHostId(i) :: message.epoch > v.hosts[i].epoch)
    // && (forall m : Host.Message | m in v.network.sentMsgs :: m != message ==> m.epoch < message.epoch)
    // ...add something about epoch numbers
    // END EDIT
  }


  // DONE: fill in here (solution: 29 lines)

  ghost predicate NoMessage_Implies_Host0HoldsLock(v: Variables)
  {
    && (|v.network.sentMsgs| == 0 && |v.hosts| > 0 ==> (v.hosts[0].epoch == 1 && v.hosts[0].holdsLock))
  }

  ghost predicate ReceivedAGrantMessage(v: Variables, i: HostId, m: Host.Message)
  {
    && v.ValidHostId(i)
    && (m.epoch == v.hosts[i].epoch && v.hosts[i].holdsLock)
  }

  ghost predicate SomeOneReceivedAGrantMessage(v: Variables)
  {
    && (exists i:int, m:Host.Message | !InFlight(v, m) && v.ValidHostId(i) :: ReceivedAGrantMessage(v, i, m))
  }

  ghost predicate SomeMessageReceived_Implies_SomeOneHoldsLock(v: Variables)
  {
    && (|v.network.sentMsgs| > 0 && |v.hosts| > 0 && ThereIsNoInFlightMessage(v) ==> SomeOneReceivedAGrantMessage(v))
  }

  ghost predicate NoTwoHostsHoldingLock(v: Variables)
  {
    && (forall i, j : int | HostHoldsLock(v, i) && HostHoldsLock(v, j) :: i == j)
  }

  ghost predicate ThereIsAnInFlightMessage(v: Variables)
  {
    && (|v.network.sentMsgs| > 0)
    && (exists m:Host.Message :: InFlight(v, m))
  }

  ghost predicate ThereIsNoInFlightMessage(v: Variables)
  {
    && (|v.network.sentMsgs| > 0)
    && (forall m:Host.Message :: !InFlight(v, m))
  }

  ghost predicate OnlyOneHostHoldsLock(v: Variables)
  {
    && v.WF()
    && NoMessage_Implies_Host0HoldsLock(v)
    && SomeMessageReceived_Implies_SomeOneHoldsLock(v)
    && NoTwoHostsHoldingLock(v)
  }

  ghost predicate NoHostHoldsLock(v: Variables)
  {
    && v.WF()
    && ThereIsAnInFlightMessage(v)
    && (forall i:int | v.ValidHostId(i) :: !v.hosts[i].holdsLock)
  }

  ghost predicate AtMostOneHostHoldsLock(v: Variables)
  {
    && v.WF()
    && (OnlyOneHostHoldsLock(v) || NoHostHoldsLock(v))
  }
  // END EDIT

  ghost predicate Inv(v:Variables) {
    // DONE: fill in here (solution: 13 lines)
    // Replace this placeholder with an invariant that's inductive and supports Safety.
    && AtMostOneHostHoldsLock(v)
    // END EDIT
  }

  lemma InvInductive(v: Variables, v': Variables)
    requires Inv(v) && Next(v, v')
    ensures Inv(v')
  {
    // Develop any necessary proof here.
    // DONE: fill in here (solution: 17 lines)
    var step :| NextStep(v, v', step);
    var id := step.id;
    var hstep :| Host.NextStep(v.hosts[id], v'.hosts[id], step.msgOps, hstep);

    // debuging
    match hstep {
      case SendGrantStep(receiver, epoch) => {
        var message := Host.MessageGrant(receiver, epoch);
        assert message.epoch > v'.hosts[id].epoch;
        assert InFlight(v', message);
        assert NoHostHoldsLock(v');
        assert OnlyOneHostHoldsLock(v);
        return;
      }
      case ReceiveGrantStep(epoch) => {
        return;
      }
    }

    // END EDIT
  }

  // debugging
  lemma InvHoldAtInit(v:Variables)
    ensures Init(v) ==> Inv(v)
  {

  }

  // debugging
  lemma InvEnsuresSafety(v:Variables)
    ensures Inv(v) ==> Safety(v)
  {

  }

  lemma SafetyProof(v:Variables, v':Variables)
    ensures Init(v) ==> Inv(v)
    ensures Inv(v) && Next(v, v') ==> Inv(v')
    ensures Inv(v) ==> Safety(v)
  {
    // Develop any necessary proof here.
    // DONE: fill in here (solution: 3 lines)
    // passed wihout proof
    // END EDIT
  }
}
