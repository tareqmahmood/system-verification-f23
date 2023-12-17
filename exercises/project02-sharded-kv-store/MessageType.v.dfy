// =============================================================================
// TEAM INFORMATION
// Name: Fariha Tabassum Islam 
// NetID: fislam2@wisc.edu
// Name: Md. Tareq Mahmood
// NetID: mmahmood7@wisc.edu
// =============================================================================

// Model your messages here. This is in its own file, separate from Types.t.dfy,
// because we don't need to trust the messages sent by the protocol for it to be
// correct (hence the .v.dfy extension).

module MessageType {
  datatype Message =
      // FIXME: fill in here (solution: 1 line)
    | Msg(from:nat, toId:nat, key:int, value:int)
      // END EDIT
}
