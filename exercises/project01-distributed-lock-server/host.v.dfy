// Host protocol
// Define the host state machine here: message type, state machine for executing one
// host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.t.dfy"

module Host {
  import opened UtilitiesLibrary
  import opened HostIdentifiers
  import Network

  // Define your Message datatype here.
  datatype Message =
    // DONE: fill in here (solution: 1 line)
    | MessageGrant(receiver: HostId, epoch: nat) // Populate this datatype.
    // END EDIT

  // Define your Host protocol state machine here.
  datatype Constants = Constants(numHosts: nat, myId:HostId)

  datatype Variables = Variables(
    // DONE: fill in here (solution: 2 lines)
     c: Constants,
     epoch: nat,
     holdsLock: bool
    // Fill me in.
    // END EDIT
  )

  // Implemented WF on my own
  {
    ghost predicate WF() {
      && c.numHosts > 1
      && c.myId >= 0 
      && c.myId < c.numHosts
      && epoch >= 0
    }
  }

  // You can assume in Init below that the initial constants are set by the
  // DistributedSystem composite state machine, since we assume the host state
  // machine knows the correct total number of hosts and its own ID.

  ghost predicate Init(v:Variables) {
    // DONE: fill in here (solution: 2 lines)
    && v.WF()
    && (v.c.myId == 0 ==> (v.epoch == 1 && v.holdsLock == true))
    && (v.c.myId != 0 ==> (v.epoch == 0 && v.holdsLock == false))
    // END EDIT
  }
  // DONE: fill in here (solution: 22 lines)

  ghost predicate ReceiveGrant(v: Variables, v': Variables, msgOps: Network.MessageOps<Message>, epoch: nat) {
    && v.WF()
    && v'.WF()
    && v'.c == v.c
    && !v.holdsLock
    && v'.holdsLock
    && v.epoch < epoch
    && v'.epoch == epoch
    && msgOps.recv.Some?
    && msgOps.recv.value == MessageGrant(v.c.myId, epoch)
    && msgOps.recv.None?
  }

  ghost predicate SendGrant(v: Variables, v': Variables, msgOps: Network.MessageOps<Message>, receiver: HostId, epoch: nat) {
    && v.WF()
    && v'.WF()
    && v'.c == v.c
    && v.holdsLock
    && !v'.holdsLock
    && v.epoch == epoch + 1
    && v'.epoch == v.epoch
    && receiver != v.c.myId
    && msgOps.send.Some?
    && msgOps.send.value == MessageGrant(receiver, epoch)
    && msgOps.send.None?
  }

  // END EDIT
  // JayNF
  datatype Step =
      // DONE: fill in here (solution: 2 lines)
     | SendGrantStep(receiver: HostId, epoch: nat)
     | ReceiveGrantStep(epoch: nat)
      // END EDIT

  ghost predicate NextStep(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    && v'.c == v.c
    && match step
       // DONE: fill in here (solution: 2 lines)
        case SendGrantStep(receiver, epoch) => SendGrant(v, v', msgOps, receiver, epoch)
        case ReceiveGrantStep(epoch) => ReceiveGrant(v, v', msgOps, epoch)
       // END EDIT
  }

  lemma NextStepDeterministic(v: Variables, v'1: Variables, v'2: Variables, msgOps: Network.MessageOps<Message>, step: Step)
    requires NextStep(v, v'1, msgOps, step)
    requires NextStep(v, v'2, msgOps, step)
    ensures v'1 == v'2
  {}

  ghost predicate Next(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(v, v', msgOps, step)
  }
}
