// =============================================================================
// TEAM INFORMATION
// Name: Fariha Tabassum Islam 
// NetID: fislam2@wisc.edu
// Name: Md. Tareq Mahmood
// NetID: mmahmood7@wisc.edu
// =============================================================================

include "IMapHelpers.t.dfy"
include "RefinementObligation.t.dfy"

module RefinementProof refines RefinementObligation {
  import opened IMapHelpers
  import opened MessageType

  // We give you a strategy for an abstraction relation, turn it into an
  // abstraction function, and give you a few predicate to use in assembling
  // your invariant. This help is because some strategies for doing this proof
  // will result in a huge mess of invariants and/or serious issues with
  // verification performance, and we don't want you to go through that.

  // The strategy consists at a high level of showing that at each point in
  // time, every key has an "owner" that maps it to the correct value. A key can
  // either be owned by a host, or by a message in the network; if it's in the
  // network, clients can't request it until that message is delivered.

  datatype MapOwner = HostOwner(id: HostId) | MessageOwner(msg: Message)

  // OwnerValue should say that k maps to val specifically due to the owner o.
  ghost predicate OwnerValue(v: Variables, o: MapOwner, k: int, val: int)
    requires v.WF()
  {
    match o {
      case HostOwner(id) =>
        // What does it mean for host id to own a key (and assign it the value
        // val)?
        // DONE: fill in here (solution: 3 lines)
        && v.ValidHost(id)
        && k in v.hosts[id].m
        && v.hosts[id].m[k] == val
        && (forall otherId: HostId | v.ValidHost(otherId) && k in v.hosts[otherId].m
              :: otherId == id)
        && (forall msg: Message | msg in v.network.inFlightMessages :: msg.key != k)
      // END EDIT
      case MessageOwner(msg) =>
        // What does it mean for the network to own a key (and assign it the
        // value val)? This is a new concept relative to the atomic demo from
        // chapter06.
        // DONE: fill in here (solution: 3 lines)
        && msg in v.network.inFlightMessages
        && msg.key == k
        && msg.value == val
        && (forall otherMsg: Message | otherMsg in v.network.inFlightMessages && otherMsg.key == k
              :: otherMsg == msg)
        && (forall id: HostId | v.ValidHost(id) :: k !in v.hosts[id].m)
           // END EDIT
    }
  }

  ghost predicate AbstractionRelation(v: Variables, av: AtomicKV.Variables)
  {
    && v.WF()
    && IsFull(av.table)
       // Use OwnerValue to connect v to av
       // DONE: fill in here (solution: 1 line)
    && forall k | IsKey(k) ::
         ( && (k in av.table)
           && exists mo:MapOwner:: OwnerValue(v, mo, k, av.table[k]))
         // END EDIT
  }

  /* Now we give you a library of some predicates to write your invariant. These
   * are made {:opaque}, which means you have to be intentional about how you use
   * them and prove them. Feel free to use `reveal OwnerHasSomeValue` for
   * example, but do so locally within an `assert P by { ... }` or `forall x ::
   * P(x) ensures { ... }` so that the definition isn't visible for the whole
   * proof - that will lead to timeouts and you'll have a Bad Time. */

  // This is a Dafny subset type - it's an imap that is known to be full
  type Owners = m:imap<int, MapOwner> | (forall k | IsKey(k) :: k in m)
    ghost witness imap k :: HostOwner(0)

  ghost predicate {:opaque} OwnerHasSomeValue(v: Variables, owner: Owners)
    requires v.WF()
  {
    && forall k | IsKey(k) :: (exists val :: OwnerValue(v, owner[k], k, val))
  }

  ghost predicate {:opaque} OwnersDistinct(v: Variables, k: int)
    requires v.WF()
  {
    forall o1: MapOwner, o2: MapOwner, val1: int, val2: int ::
      (OwnerValue(v, o1, k, val1) && OwnerValue(v, o2, k, val2)) ==>
        o1 == o2 && val1 == val2
  }

  lemma use_OwnerHasSomeValue(v: Variables, owner: Owners, k: int) returns (val: int)
    requires v.WF()
    requires OwnerHasSomeValue(v, owner)
    ensures OwnerValue(v, owner[k], k, val)
  {
    assert IsKey(k);
    reveal OwnerHasSomeValue();
    val :| OwnerValue(v, owner[k], k, val);
  }

  lemma use_OwnersDistinct(v: Variables, k: int, o1: MapOwner, val1: int, o2: MapOwner, val2: int)
    requires v.WF()
    requires OwnersDistinct(v, k)
    requires OwnerValue(v, o1, k, val1)
    requires OwnerValue(v, o2, k, val2)
    ensures o1 == o2 && val1 == val2
  {
    assert IsKey(k);
    reveal OwnersDistinct();
  }

  // If o owns some value, it is the owner. This is a useful way to use
  // OwnersDistinct without fully revealing it.
  lemma use_OwnerValue(v: Variables, owners: Owners, o: MapOwner, k: int, val: int)
    requires v.WF()
    requires OwnerHasSomeValue(v, owners)
    requires OwnersDistinct(v, k)
    requires OwnerValue(v, o, k, val)
    ensures owners[k] == o
  {
    var val' := use_OwnerHasSomeValue(v, owners, k);
    reveal OwnersDistinct();
  }

  // We give you the abstraction function, which just uses a trick to turn the
  // relation into a function.
  ghost function VariablesAbstraction(v: Variables) : AtomicKV.Variables
  {
    if exists av :: AbstractionRelation(v, av) then
      var av :| AbstractionRelation(v, av); av
    else AtomicKV.Variables(EmptyMap())
  }

  lemma imap_ext_eq(m1: imap<int, int>, m2: imap<int, int>)
    requires IsFull(m1) && IsFull(m2)
    requires forall k: int :: m1[k] == m2[k]
    ensures m1 == m2
  {}

  lemma UniqueAbstraction(v: Variables, av: AtomicKV.Variables, owners: Owners)
    requires AbstractionRelation(v, av)
    requires OwnerHasSomeValue(v, owners)
    ensures VariablesAbstraction(v) == av
  {
    forall k:int | IsKey(k)
      ensures VariablesAbstraction(v).table[k] == av.table[k]
    {
      var val := use_OwnerHasSomeValue(v, owners, k);
    }
    // NOTE: this had to be factored into a lemma to work
    imap_ext_eq(VariablesAbstraction(v).table, av.table);
  }

  ghost predicate Inv(v: Variables)
  {
    // DONE: fill in here (solution: 3 lines)
    && v.WF()
    && (exists owners:Owners :: OwnerHasSomeValue(v, owners)) // Invariant 1
    && (forall k | IsKey(k) :: OwnersDistinct(v, k)) // Invariant 2
    && (exists av :: AbstractionRelation(v, av)) // Invariant 3
       // END EDIT
  }

  ////////////////////////////////////////////////////////////////////////////


  lemma RefinementInit(v: Variables)
    //requires Init(v) // inherited from abstract module
    ensures Inv(v)
    ensures AtomicKV.Init(VariablesAbstraction(v))
  {
    // DONE: fill in here (solution: 12 lines)
    assert Init(v);
    assert v.WF();

    // =================================
    // CHECKING WHAT WE ALREADY KNOW
    assert v.hosts[0].m == ZeroMap();
    assert forall id:HostId | v.ValidHost(id) && id > 0 :: v.hosts[id].m == EmptyMap();
    assert forall k | IsKey(k) :: k in v.hosts[0].m;
    // =================================

    // =================================
    // PROVE INVARIANT
    assert Inv(v) by {

      // // ---- PROVE INVARIANT 0 ----
      // forall k | IsKey(k) ensures KeyHasOwner(v, k) {
      //   assert OwnerValue(v, HostOwner(0), k, v.hosts[0].m[k]);
      //   assert exists mo:MapOwner :: OwnerValue(v, mo, k, 0);
      //   assert KeyHasOwner(v, k);
      // }
      // assert (forall k | IsKey(k) :: KeyHasOwner(v, k));
      // ---- PROVE INVARIANT 1 ----
      assert (exists owners:Owners :: OwnerHasSomeValue(v, owners)) by {
        assert v.hosts[0].m == ZeroMap();
        reveal OwnerHasSomeValue();
        assert forall k | IsKey(k) :: OwnerValue(v, HostOwner(0), k, v.hosts[0].m[k]);
        var owners: imap<int, MapOwner> := imap x | IsKey(x) :: HostOwner(0);
        assert forall k | IsKey(k) :: owners[k] == HostOwner(0);
        assert OwnerHasSomeValue(v, owners);
      }
      // ---- PROVE INVARIANT 2 ----
      assert v.hosts[0].m == ZeroMap();

      forall k | IsKey(k) ensures OwnersDistinct(v, k) {
        // assert OwnerValue(v, HostOwner(0), k, v.hosts[0].m[k]);
        reveal OwnersDistinct();
        assert OwnerValue(v, HostOwner(0), k, v.hosts[0].m[k]);
      }
      assert (forall k | IsKey(k) :: OwnersDistinct(v, k));
      // ---- PROVE INVARIANT 3 ----
      // Strategy: showed what the av should be, then proved that it is an abstraction relation
      assert exists av :: AbstractionRelation(v, av) by {
        var av := AtomicKV.Variables(ZeroMap());
        assert v.hosts[0].m == ZeroMap();
        assert forall id:HostId | v.ValidHost(id) && id > 0 :: v.hosts[id].m == EmptyMap();
        assert IsFull(av.table);
        assert forall k | IsKey(k) :: k in av.table;
        assert forall k | IsKey(k) ::OwnerValue(v, HostOwner(0), k, av.table[k]);
        assert AbstractionRelation(v, av);
      }
    }
    // =================================


    // =================================
    // PROVE REFINEMENT
    // Strategy: Showed what the av should be, then proved that it is an abstraction relation
    assert AtomicKV.Init(VariablesAbstraction(v)) by {
      assert Inv(v);
      assert exists av :: AbstractionRelation(v, av);
      var av := AtomicKV.Variables(ZeroMap());
      assert v.hosts[0].m == ZeroMap();
      assert forall id:HostId | v.ValidHost(id) && id > 0 :: v.hosts[id].m == EmptyMap();
      assert IsFull(av.table);
      assert forall k | IsKey(k) :: k in av.table;
      assert forall k | IsKey(k) ::OwnerValue(v, HostOwner(0), k, av.table[k]);
      assert AbstractionRelation(v, av);
    }
    // =================================
    // END EDIT
  }



  // DONE: fill in here (solution: 204 lines)
  // Your proof goes here. We highly, highly recommend stating and proving a
  // refinement lemma for each step; see the chapter06 demo if you need help
  // structuring that.
  // END EDIT

  ghost predicate KeyHasOwner(v: Variables, k: int)
    requires v.WF()
  {
    exists o:MapOwner, val:int :: OwnerValue(v, o, k, val)
  }

  lemma GetOwner(v:Variables, k:int, val:int) returns (owner: MapOwner)
    requires v.WF()
    requires exists mo:MapOwner :: OwnerValue(v, mo, k, val)
  {
    owner :| OwnerValue(v, owner, k, val);
  }

  lemma OwnersHasValueImpliesKeyHasOwner(v:Variables, owners:Owners, k:int)
    requires v.WF()
    requires OwnerHasSomeValue(v, owners)
    ensures KeyHasOwner(v, k)
  {
    assert IsKey(k);
    reveal OwnerHasSomeValue();
    assert KeyHasOwner(v, k);
  }

  lemma QueryPreservesInvAndRefines(v: Variables, v': Variables, event: Event,
                                    dsstep: Step,step: Host.Step)
    requires NextStep(v, v', event, dsstep)
    requires Inv(v)
    requires Host.NextStep(v.hosts[dsstep.hostId], v'.hosts[dsstep.hostId], dsstep.msgOps, event, step)
    requires step.QueryStep?
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    var msgOps0 := dsstep.msgOps;
    var id0 := dsstep.hostId;
    var key0 := step.key;
    var val0 := step.value;
    assert event.GetEvent?;
    assert event == GetEvent(key0, val0);
    assert msgOps0.send.None?;
    assert msgOps0.recv.None?;

    // =================================
    // CHECKING WHAT WE ALREADY KNOW
    assert v.WF();
    assert Inv(v);
    assert forall k | IsKey(k) :: KeyHasOwner(v, k);
    assert (exists owners:Owners :: OwnerHasSomeValue(v, owners));
    assert (exists av :: AbstractionRelation(v, av));
    assert v == v';
    // =================================


    // =================================
    // PROVE INVARIANT
    assert Inv(v') by {
      assert v'.WF();
      // // ---- PROVE INVARIANT 0 ----
      // assert forall k | IsKey(k) :: KeyHasOwner(v', k);
      // ---- PROVE INVARIANT 1 ----
      assert (exists owners:Owners :: OwnerHasSomeValue(v', owners));
      // ---- PROVE INVARIANT 2 ----
      assert (forall k | IsKey(k) :: OwnersDistinct(v', k));
      // ---- PROVE INVARIANT 3 ----
      assert (exists av :: AbstractionRelation(v', av));
    }
    // ==================================

    assert Inv(v');
    assert (exists owners:Owners :: OwnerHasSomeValue(v', owners));
    // assert (forall k | IsKey(k) :: OwnersDistinct(v', k));
    assert (exists av :: AbstractionRelation(v', av));


    // ==================================
    // PROVE REFINEMENT
    var vSpec := VariablesAbstraction(v);
    var vSpec' := VariablesAbstraction(v');

    assert AtomicKV.Next(vSpec, vSpec', event) by {
      assert AbstractionRelation(v, vSpec);
      assert AbstractionRelation(v', vSpec');
      assert vSpec == vSpec';
      assert key0 in vSpec.table;
      assert key0 in vSpec'.table;
      assert val0 == vSpec.table[key0];
      assert val0 == vSpec'.table[key0];
      assert AtomicKV.Get(vSpec, vSpec', key0, val0);
    }
    // ==================================
  }

  lemma InsertPreservesInvAndRefines(v: Variables, v': Variables, event: Event,
                                     dsstep: Step,step: Host.Step)
    requires NextStep(v, v', event, dsstep)
    requires Inv(v)
    requires Host.NextStep(v.hosts[dsstep.hostId], v'.hosts[dsstep.hostId], dsstep.msgOps, event, step)
    requires step.InsertStep?
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    var msgOps0 := dsstep.msgOps;
    var id0 := dsstep.hostId;
    var key0 := step.key;
    var val0 := step.value;
    assert event.PutEvent?;
    assert msgOps0.send.None?;
    assert msgOps0.recv.None?;

    assert v.WF(); // VERIFIED
    assert Inv(v); // VERIFIED
    assert forall k | IsKey(k) :: KeyHasOwner(v, k); // VERIFIED
    assert (exists owners:Owners :: OwnerHasSomeValue(v, owners)); // VERIFIED
    assert forall k | IsKey(k) :: OwnersDistinct(v, k); // VERIFIED
    assert (exists av :: AbstractionRelation(v, av)); // VERIFIED

    // =================================
    // CHECKING WHAT WE ALREADY KNOW
    // no hosts change except id0
    assert forall id:HostId | v.ValidHost(id) && id != id0 :: v.hosts[id].m == v'.hosts[id].m; // VERIFIED
    // for id0, the key remains the same
    assert forall k | IsKey(k) && k in v.hosts[id0].m :: k in v'.hosts[id0].m; // VERIFIED
    // for id0, the value changes only for key0
    assert forall k | IsKey(k) && k in v.hosts[id0].m && k != key0 :: v.hosts[id0].m[k] == v'.hosts[id0].m[k]; // VERIFIED
    // no messages change in the network
    assert v.network.inFlightMessages == v'.network.inFlightMessages; // VERIFIED
    // the value of key0 changes for id0
    assert v'.hosts[id0].m[key0] == val0; // VERIFIED
    // // host id0 has key0 in v
    // =================================

    var owners0 :| OwnerHasSomeValue(v, owners0);

    // =================================
    // PROVE INVARIANT
    // =================================

    // ---------------------------------
    // ---- PROVE INVARIANT 1 ----
    // ---------------------------------
    // key0 is owned by id0
    assert OwnerValue(v, HostOwner(id0), key0, v.hosts[id0].m[key0]) by {
      var val := use_OwnerHasSomeValue(v, owners0, key0);
      assert val == v.hosts[id0].m[key0];
    }
    assert owners0[key0] == HostOwner(id0) by { // IMPORTANT: times out without this line
      reveal OwnerHasSomeValue();
    }
    // for all keys except key0, the owner and value remain the same
    forall k | IsKey(k) && k != key0
      ensures exists val:int :: OwnerValue(v', owners0[k], k, val) {
      var val := use_OwnerHasSomeValue(v, owners0, k);
      assert OwnerValue(v', owners0[k], k, val);
    }
    // for key0, the owner is id0 and the value is val0
    assert OwnerValue(v', HostOwner(id0), key0, v'.hosts[id0].m[key0]);

    assert forall k | IsKey(k) :: KeyHasOwner(v', k);
    // assert OwnerHasSomeValue owners0
    assert OwnerHasSomeValue(v', owners0) by {
      reveal OwnerHasSomeValue();
    }
    assert (exists owners:Owners :: OwnerHasSomeValue(v', owners));

    assert OwnerHasSomeValue(v', owners0);

    // ---------------------------------
    // ---- PROVE INVARIANT 2 ----
    // ---------------------------------
    forall k | IsKey(k) ensures OwnersDistinct(v', k) {
      assert OwnersDistinct(v, k);
      var val := use_OwnerHasSomeValue(v', owners0, k);
      assert OwnerValue(v', owners0[k], k, val);
      if k == key0 {
        assert owners0[k] == HostOwner(id0);
        assert val == val0;
      }
      assert OwnersDistinct(v', k) by {
        reveal OwnersDistinct(); // Could not avoid it
      }
    }
    assert (forall k | IsKey(k) :: OwnersDistinct(v', k));

    // ---------------------------------
    // ---- PROVE INVARIANT 3 ----
    // ---------------------------------
    assert (exists av :: AbstractionRelation(v', av)) by {
      // Given
      var av :| AbstractionRelation(v, av);
      assert IsFull(av.table);
      assert forall k | IsKey(k) :: k in av.table;
      // Strategy: create an av' that should be an abstraction relation
      var av'table := av.table[key0 := val0];
      var av' := AtomicKV.Variables(av'table);
      // Strategy: prove that the created av' is an abstraction relation
      assert AbstractionRelation(v', av') by {
        assert IsFull(av'.table);
        assert forall k | IsKey(k) :: k in av'.table;
        forall k | IsKey(k) ensures exists mo:MapOwner :: OwnerValue(v', mo, k, av'.table[k]) {
          assert OwnerValue(v', owners0[k], k, av'.table[k]);
          if k == key0 {
            assert OwnerValue(v', owners0[k], k, av'.table[k]);
          } else {
            assert OwnerValue(v', owners0[k], k, av'.table[k]);
          }
        }
      }
    }
    assert (exists av :: AbstractionRelation(v', av));
    assert Inv(v');
    // ==================================
    // END PROVE INVARIANT
    // ==================================

    assert Inv(v');
    assert (exists owners:Owners :: OwnerHasSomeValue(v', owners));
    assert (forall k | IsKey(k) :: OwnersDistinct(v', k));
    assert (exists av :: AbstractionRelation(v', av));

    // ==================================
    // PROVE REFINEMENT
    // ==================================
    var vSpec := VariablesAbstraction(v);
    var vSpec' := VariablesAbstraction(v');
    assert AtomicKV.Put(vSpec, vSpec', key0, val0) by {
      assert AbstractionRelation(v, vSpec);
      assert AbstractionRelation(v', vSpec');
      // Strategy: create an av' that should be an abstraction relation
      var av'table := vSpec.table[key0 := val0];
      var av' := AtomicKV.Variables(av'table);
      // Strategy: prove that the created av' is an abstraction relation
      assert AbstractionRelation(v', av') by {
        assert IsFull(av'.table);
        assert forall k | IsKey(k) :: k in av'.table;
        forall k | IsKey(k) ensures exists mo:MapOwner :: OwnerValue(v', mo, k, av'.table[k]) {
          assert OwnerValue(v', owners0[k], k, av'.table[k]);
          if k == key0 {
            assert OwnerValue(v', owners0[k], k, av'.table[k]);
          } else {
            assert OwnerValue(v', owners0[k], k, av'.table[k]);
          }
        }
      }
      imap_ext_eq(av'.table, vSpec.table[key0 := val0]);
      assert AtomicKV.Put(vSpec, av', key0, val0);
      UniqueAbstraction(v', av', owners0);
    }

    assert AtomicKV.Put(vSpec, vSpec', key0, val0);
    assert AtomicKV.Next(vSpec, vSpec', event);
    // ==================================
    // END PROVE REFINEMENT
    // ==================================
  }

  lemma SendPreservesInvAndRefines(v: Variables, v': Variables, event: Event,
                                   dsstep: Step,step: Host.Step)
    requires NextStep(v, v', event, dsstep)
    requires Inv(v)
    requires Host.NextStep(v.hosts[dsstep.hostId], v'.hosts[dsstep.hostId], dsstep.msgOps, event, step)
    requires step.SendStep?
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {

    var msgOps0 := dsstep.msgOps;
    assert step.SendStep?;
    var id0 := dsstep.hostId;
    var key0 := step.key;
    var keyset0 := iset{key0};
    var val0 := step.value;
    var toId0 := step.toId;
    assert event.NoOpEvent?;
    assert msgOps0.send.Some?;
    assert msgOps0.send.value == Msg(id0, toId0, key0, val0);
    assert msgOps0.recv.None?;
    var msg0 := msgOps0.send.value;


    // =================================
    // CHECKING WHAT WE ALREADY KNOW
    // =================================
    assert v.WF(); // VERIFIED
    assert Inv(v); // VERIFIED
    assert (exists owners:Owners :: OwnerHasSomeValue(v, owners)); // VERIFIED
    assert forall k | IsKey(k) :: KeyHasOwner(v, k); // VERIFIED
    assert forall k | IsKey(k) :: OwnersDistinct(v, k); // VERIFIED
    assert (exists av :: AbstractionRelation(v, av)); // VERIFIED

    // assert v.hosts[id0].m[key0] == val0; // VERIFIED
    // // assert v'.hosts[id0].m == MapRemove(v.hosts[id0].m, iset{key0}); // VERIFIED
    // // no hosts change except id0
    // assert forall id:HostId | v.ValidHost(id) && id != id0 :: v.hosts[id].m == v'.hosts[id].m; // VERIFIED
    // // for id0, the key remains the same except for key0
    // assert v'.hosts[id0].m  == MapRemove(v.hosts[id0].m, keyset0); // VERIFIED
    // assert forall k | k in v.hosts[id0].m && k !in keyset0 :: k in v'.hosts[id0].m; // VERIFIED
    // // for id0, key0 gets removed from v to v'
    // assert  key0 in v.hosts[id0].m && key0 !in v'.hosts[id0].m;
    // // host id0 map is the same in v and v' except for key0
    // assert forall k | IsKey(k) && k in v.hosts[id0].m && k != key0 :: v.hosts[id0].m[k] == v'.hosts[id0].m[k]; // VERIFIED
    // // one inflight msg in the network
    // assert |v.network.inFlightMessages|+1 == |v'.network.inFlightMessages|; // VERIFIED
    // // host id0 has key0 in v
    // assert OwnerValue(v, HostOwner(id0), key0, v.hosts[id0].m[key0]) by {
    //   assert KeyHasOwner(v, key0) by {
    //     reveal OwnerHasSomeValue();
    //   }
    // }
    // // an inflight msg has key0 in v'
    // assert OwnerValue(v', MessageOwner(msg0), key0, val0) by {
    //   assert KeyHasOwner(v', key0) by {
    //     reveal OwnerHasSomeValue();
    //   }
    // }
    // =================================

    var owners0 :| OwnerHasSomeValue(v, owners0);

    // =================================
    // PROVE INVARIANT
    // =================================

    // ---------------------------------
    // ---- PROVE INVARIANT 1 ----
    // ---------------------------------
    // for all keys except key0, the owner and value remain the same
    // key0 is owned by id0
    assert OwnerValue(v, HostOwner(id0), key0, v.hosts[id0].m[key0]) by {
      var val := use_OwnerHasSomeValue(v, owners0, key0);
      assert val == v.hosts[id0].m[key0];
    }
    assert owners0[key0] == HostOwner(id0) by { // IMPORTANT: times out without this line
      reveal OwnerHasSomeValue();
    }
    // for all keys except key0, the owner and value remain the same
    forall k | IsKey(k) && k != key0
      ensures exists val:int :: OwnerValue(v', owners0[k], k, val) {
      var val := use_OwnerHasSomeValue(v, owners0, k);
      assert OwnerValue(v', owners0[k], k, val);
    }
    // for key0, the owner is mgs0 and the value is val0
    assert OwnerValue(v', MessageOwner(msg0), key0, val0);
    // all keys have an owner
    assert forall k | IsKey(k) :: KeyHasOwner(v', k);

    var owners0' := owners0[key0 := MessageOwner(msg0)];
    assert OwnerHasSomeValue(v', owners0') by {
      reveal OwnerHasSomeValue();
    }
    assert (exists owners:Owners :: OwnerHasSomeValue(v', owners));

    assert OwnerHasSomeValue(v', owners0');

    // ---------------------------------
    // ---- PROVE INVARIANT 2 ----
    // ---------------------------------
    assert OwnerHasSomeValue(v', owners0');
    forall k | IsKey(k) ensures OwnersDistinct(v', k) {
      assert OwnersDistinct(v, k);
      if k == key0 {
        assert forall msg:Message | msg in v.network.inFlightMessages :: msg.key != k;
        assert k in v.hosts[id0].m;
        assert forall id:HostId | v.ValidHost(id) && id != id0 :: k !in v.hosts[id].m;
        assert msg0 in v'.network.inFlightMessages && msg0.key == k;
        assert k !in v'.hosts[id0].m;
        reveal OwnersDistinct();
      } else {
        var val := use_OwnerHasSomeValue(v', owners0', k);
        assert OwnerValue(v', owners0'[k], k, val);
        reveal OwnersDistinct();
      }
    }
    assert forall k | IsKey(k) :: OwnersDistinct(v', k);

    // ---------------------------------
    // ---- PROVE INVARIANT 3 ----
    // ---------------------------------

    assert (exists av :: AbstractionRelation(v', av)) by {
      // Given
      var av :| AbstractionRelation(v, av);
      // Strategy: create an av' that should be an abstraction relation
      var av' := av;
      // Strategy: prove that the created av' is an abstraction relation
      assert AbstractionRelation(v', av') by {
        assert IsFull(av'.table);
        assert forall k | IsKey(k) :: k in av'.table;
        forall k | IsKey(k) ensures exists mo:MapOwner :: OwnerValue(v', mo, k, av'.table[k]) {
          if k == key0 {
            assert av'.table[k] == val0;
          } else {
            assert OwnerValue(v, owners0[k], k, av'.table[k]);
          }
        }
      }
    }
    assert (exists av :: AbstractionRelation(v', av));
    assert Inv(v');
    // ==================================
    // END PROVE INVARIANT
    // ==================================


    // ==================================
    // PROVE REFINEMENT
    // ==================================

    var vSpec := VariablesAbstraction(v);
    var vSpec' := VariablesAbstraction(v');
    assert vSpec == vSpec' by {
      assert AbstractionRelation(v, vSpec);
      assert AbstractionRelation(v', vSpec');
      var av' := vSpec;
      // imap_ext_eq(av'.table, vSpec.table);
      assert AbstractionRelation(v', av') by {
        assert IsFull(av'.table);
        assert forall k | IsKey(k) :: k in av'.table;
        forall k | IsKey(k) ensures exists mo:MapOwner :: OwnerValue(v', mo, k, av'.table[k]) {
          if k == key0 {
            assert av'.table[k] == val0;
          } else {
            assert OwnerValue(v, owners0[k], k, av'.table[k]);
          }
        }
      }
      imap_ext_eq(av'.table, vSpec'.table);
    }
    assert vSpec == vSpec';
    assert AtomicKV.NoOp(vSpec, vSpec');
    assert AtomicKV.Next(vSpec, vSpec', event);

    // ==================================
    // END PROVE REFINEMENT
    // ==================================

  }


  lemma ReceivePreservesInvAndRefines(v: Variables, v': Variables, event: Event,
                                      dsstep: Step,step: Host.Step)
    requires NextStep(v, v', event, dsstep)
    requires Inv(v)
    requires Host.NextStep(v.hosts[dsstep.hostId], v'.hosts[dsstep.hostId], dsstep.msgOps, event, step)
    requires step.ReceiveStep?
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {

    var msgOps0 := dsstep.msgOps;
    var id0 := dsstep.hostId;
    var key0 := step.key;
    var keyset0 := iset{key0};
    var val0 := step.value;
    var fromId0 := step.from;
    assert event.NoOpEvent?;
    assert msgOps0.send.None?;
    assert msgOps0.recv.Some?;
    assert msgOps0.recv.value == Msg(fromId0, id0, key0, val0);
    var msg0 := msgOps0.recv.value;

    assert v.WF(); // VERIFIED
    assert Inv(v); // VERIFIED



    // =================================
    // CHECKING WHAT WE ALREADY KNOW
    // =================================
    assert v.WF(); // VERIFIED
    assert Inv(v); // VERIFIED
    assert (exists owners:Owners :: OwnerHasSomeValue(v, owners)); // VERIFIED
    assert forall k | IsKey(k) :: KeyHasOwner(v, k); // VERIFIED
    assert forall k | IsKey(k) :: OwnersDistinct(v, k); // VERIFIED
    assert (exists av :: AbstractionRelation(v, av)); // VERIFIED
    assert v'.hosts[id0].m[key0] == val0; // VERIFIED
    // =================================

    var owners0 :| OwnerHasSomeValue(v, owners0);

    // =================================
    // PROVE INVARIANT
    // =================================

    // ---------------------------------
    // ---- PROVE INVARIANT 1 ----
    // ---------------------------------
    // for key0, the owner is mgs0 and the value is val0
    var msgOwner0 := MessageOwner(msg0);
    assert OwnerValue(v, msgOwner0, key0, val0) by {
      var val := use_OwnerHasSomeValue(v, owners0, key0);
      assert val == msg0.value;
    }
    assert owners0[key0] == MessageOwner(msg0) by { // IMPORTANT: times out without this line
      reveal OwnerHasSomeValue();
    }
    // for all keys except key0, the owner and value remain the same
    forall k | IsKey(k) && k != key0
      ensures exists val:int :: OwnerValue(v', owners0[k], k, val) {
      var val := use_OwnerHasSomeValue(v, owners0, k);
      assert OwnerValue(v', owners0[k], k, val);
    }
    // key0 is later owned by id0
    assert OwnerValue(v', HostOwner(id0), key0, v'.hosts[id0].m[key0]);
    // all keys have an owner
    assert forall k | IsKey(k) :: KeyHasOwner(v', k);

    var owners0' := owners0[key0 := HostOwner(id0)];
    assert OwnerHasSomeValue(v', owners0') by {
      reveal OwnerHasSomeValue();
    }
    assert (exists owners:Owners :: OwnerHasSomeValue(v', owners));

    assert OwnerHasSomeValue(v', owners0');
    // ---------------------------------
    // ---- PROVE INVARIANT 2 ----
    // ---------------------------------
    assert OwnerHasSomeValue(v', owners0');
    forall k | IsKey(k) ensures OwnersDistinct(v', k) {
      assert OwnersDistinct(v, k);
      if k == key0 {
        reveal OwnersDistinct();
      } else {
        var val := use_OwnerHasSomeValue(v', owners0', k);
        assert OwnerValue(v', owners0'[k], k, val);
        reveal OwnersDistinct();
      }
    }
    assert forall k | IsKey(k) :: OwnersDistinct(v', k);

    // ---------------------------------
    // ---- PROVE INVARIANT 3 ----
    // ---------------------------------

    assert (exists av :: AbstractionRelation(v', av)) by {
      // Given
      var av :| AbstractionRelation(v, av);
      // Strategy: create an av' that should be an abstraction relation
      var av' := av;
      // Strategy: prove that the created av' is an abstraction relation
      assert AbstractionRelation(v', av') by {
        assert IsFull(av'.table);
        assert forall k | IsKey(k) :: k in av'.table;
        forall k | IsKey(k) ensures exists mo:MapOwner :: OwnerValue(v', mo, k, av'.table[k]) {
          if k == key0 {
            assert av'.table[k] == val0;
          } else {
            assert OwnerValue(v, owners0[k], k, av'.table[k]);
          }
        }
      }
    }
    assert (exists av :: AbstractionRelation(v', av));
    assert Inv(v');
    // ==================================
    // END PROVE INVARIANT
    // ==================================


    // ==================================
    // PROVE REFINEMENT
    // ==================================

    var vSpec := VariablesAbstraction(v);
    var vSpec' := VariablesAbstraction(v');
    assert vSpec == vSpec' by {
      assert AbstractionRelation(v, vSpec);
      assert AbstractionRelation(v', vSpec');
      var av' := vSpec;
      // imap_ext_eq(av'.table, vSpec.table);
      assert AbstractionRelation(v', av') by {
        assert IsFull(av'.table);
        assert forall k | IsKey(k) :: k in av'.table;
        forall k | IsKey(k) ensures exists mo:MapOwner :: OwnerValue(v', mo, k, av'.table[k]) {
          if k == key0 {
            assert av'.table[k] == val0;
          } else {
            assert OwnerValue(v, owners0[k], k, av'.table[k]);
          }
        }
      }
      imap_ext_eq(av'.table, vSpec'.table);
    }
    assert vSpec == vSpec';
    assert AtomicKV.NoOp(vSpec, vSpec');
    assert AtomicKV.Next(vSpec, vSpec', event);

    // ==================================
    // END PROVE REFINEMENT
    // ==================================

  }

  lemma {:verify true} RefinementNext(v: Variables, v': Variables, event: Event)
    // These requires & ensures all come from RefinementObligations; repeating
    // them here as a nearby crib sheet.
    // requires Next(v, v')
    // requires Inv(v)
    ensures Inv(v')
    ensures AtomicKV.Next(VariablesAbstraction(v), VariablesAbstraction(v'), event)
  {
    var dsstep: Step :| NextStep(v, v', event, dsstep);
    var msgOps := dsstep.msgOps;
    var id := dsstep.hostId;
    assert Host.Next(v.hosts[id], v'.hosts[id], msgOps, event);
    var step: Host.Step :| Host.NextStep(v.hosts[id], v'.hosts[id], msgOps, event, step);
    // All the solution dos here is match on the step and call the lemma for
    // refinement of that step.
    // DONE: fill in here (solution: 14 lines)
    if step.InsertStep? {
      InsertPreservesInvAndRefines(v, v', event, dsstep, step);
    } else if step.QueryStep? {
      QueryPreservesInvAndRefines(v, v', event,  dsstep, step);
    } else if step.SendStep? {
      SendPreservesInvAndRefines(v, v', event,  dsstep, step);
    } else {
      assert step.ReceiveStep?;
      ReceivePreservesInvAndRefines(v, v', event,  dsstep, step);
    }
    // END EDIT
  }


}
