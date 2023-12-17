// =============================================================================
// TEAM INFORMATION
// Name: Fariha Tabassum Islam 
// NetID: fislam2@wisc.edu
// Name: Md. Tareq Mahmood
// NetID: mmahmood7@wisc.edu
// =============================================================================


include "UtilitiesLibrary.t.dfy"
include "IMapHelpers.t.dfy"
include "Types.t.dfy"
include "MessageType.v.dfy"
include "Network.t.dfy"

// You'll need protocol steps for Get and Put that respond to requests if
// they're hosted locally, much like in the atomic version of this protocol
// (AtomicKV, seen in the chapter06 demos). These need to set the event to
// GetEvent and PutEvent appropriately: otherwise, you're claiming the key-value
// store implementation always does nothing and never returns results to the
// client. (Such an implementation is technically safe but totally useless and
// not in the spirit of the assignment; to be clear, it's not a real solution.)
//
// In addition, you should capture the idea that keys "live" on different hosts
// *and can move around* from host to host. So, in addition to implementing
// client-visible actions as described in AtomicKV, each host should have a way
// to send part of its state to another host, and to receive the corresponding
// message from another sender. (The messages can move a batch of key-value
// pairs, or a single pair at a time; neither is particularly harder than the
// other.)
//
// Obviously, the hosts must be aware of which fraction of the keyspace they
// own at any given time, so that a host doesn't try to service a Get or Put
// request when the "real state" is off at some other host right now.
//

module Host {
  import opened UtilitiesLibrary
  import opened IMapHelpers
  import opened Types
  import opened MessageType
  import Network

  type HostId = Network.HostId

  datatype Variables = Variables(myId: HostId, m: imap<int, int>)
  {
    ghost predicate GroupWF(assignedId: HostId) {
      && this.myId == assignedId
    }
  }

  ghost predicate Init(v: Variables) {
    // hint: look at IMapHelpers for some tools to write this
    // DONE: fill in here (solution: 2 lines)
    if v.myId == 0
    then v.m == IMapHelpers.ZeroMap()
    else v.m == IMapHelpers.EmptyMap()
      // END EDIT
  }

  datatype Step =
      // DONE: fill in here (solution: 4 lines)
    | InsertStep(key: int, value: int)
    | QueryStep(key: int, value: int)
    | SendStep(toId: HostId, key: int, value: int)
    | ReceiveStep(from: HostId, key: int, value: int)
      // END EDIT

  // Write a predicate for each step here.
  // DONE: fill in here (solution: 53 lines)
  ghost predicate Query(v: Variables, v': Variables, event: Event,
                        msgOps:Network.MessageOps,
                        key: int, value: int)
  {
    && event == GetEvent(key, value)
    && v' == v
    && key in v.m
    && value == v.m[key]
    && msgOps.send.None?
    && msgOps.recv.None?
  }

  ghost predicate Insert(v: Variables, v': Variables, event: Event,
                         msgOps:Network.MessageOps,
                         key: int, value: int)
  {
    && event == PutEvent(key, value)
    && v'.myId == v.myId
    && key in v.m
    && v'.m == v.m[key := value]
    && msgOps.send.None?
    && msgOps.recv.None?
  }

  ghost predicate Send(v: Variables, v': Variables, event: Event,
                       msgOps:Network.MessageOps,
                       toId: HostId, key: int, value: int)
  {
    && event == NoOpEvent()
    && v'.myId == v.myId
    && key in v.m
    && value == v.m[key]
    && var s := iset{key};
    && v'.m == MapRemove(v.m, s)

    && msgOps.recv.None?
    && msgOps.send.Some?
    && msgOps.send.value == Msg(v.myId, toId, key, value)
  }

  ghost predicate Receive(v: Variables, v': Variables, event: Event,
                          msgOps:Network.MessageOps,
                          fromId: HostId, key: int, value: int)
  {
    && event == NoOpEvent()
    && v'.myId == v.myId
    && key !in v.m
    && v'.m == v.m[key := value]

    && msgOps.recv.Some?
    && msgOps.recv.value == Msg(fromId, v.myId, key, value)
    && msgOps.send.None?
  }
  // END EDIT

  ghost predicate NextStep(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event, step: Step)
  {
    match step {
      // boilerplate that dispatches to each of your step's predicates
      // DONE: fill in here (solution: 4 lines)
      case InsertStep(key, value) => Insert(v, v', event, msgOps, key, value)
      case QueryStep(key, value) => Query(v, v', event, msgOps, key, value)
      case SendStep(toId, key, value) => Send(v, v', event, msgOps, toId, key, value)
      case ReceiveStep(from, key, value) => Receive(v, v', event, msgOps, from, key, value)
      // END EDIT
    }
  }

  ghost predicate Next(v: Variables, v': Variables, msgOps: Network.MessageOps, event: Event)
  {
    exists step: Step :: NextStep(v, v', msgOps, event, step)
  }
}
