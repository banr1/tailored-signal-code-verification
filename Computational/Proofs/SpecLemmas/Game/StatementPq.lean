/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementPq

@[expose] public section

set_option autoImplicit false

/-!
# Projected-directory CLI staging definitions and lemmas

**Checked by Lean.** Pure-execution unfolding lemmas for `Dir.cliDrvImpl` and projected `BinState`
staging definitions (`cliPqScheme`, `cliDrvImpl`, `cliPqExpProj`, `CliPqxdhAdvantageProj`) for the
retained-directory CLI equivalence proof.
-/

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

namespace Dir

/-- Run `A` on the retained-directory CLI driver `Dir.cliDrvImpl` from the empty state. -/
def runCliDriver (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (CliDrvM S l)) (mode : BHDrvMode S)
    (A : CliGameAdversary S l (BitVec 512)) :
    StateT (SignalPqxdh.KeyIndState S) ProbComp (Bool × CliDriverState S l) :=
  (simulateQ (cliDrvImpl S l P run W qep decT encT ext mode) A.run).run {}

/-- Embed a pure `SMSchemeR` into `SMSchemeRM ProbComp`. -/
def pureSMSchemeRM {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM ProbComp Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send s m rs := pure (sm.send s m rs)
  receive s c rc := pure (sm.receive s c rc)

theorem cliPqSchemeM_cliRunPure_eq (run : CliRun) (l : Nat)
    {S : SignalPqxdh.Setup} {l' : Nat} (bi : ModelDriverInstance S l')
    (stA0 stB0 : CliPartyState) :
    cliPqSchemeM (cliRunPure run) l bi stA0 stB0 =
      pureSMSchemeRM (cliPqScheme run l bi stA0 stB0) := by
  unfold cliPqSchemeM cliPqScheme pureSMSchemeRM
  congr 1
  funext s c rc
  unfold cliPqReceive
  dsimp only [cliPqReceiveM, cliPqRecvM, cliRunPure]
  cases cliPqLenOk c with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases s.bin.party with
    | A =>
      dsimp only
      cases (c.head? == some wirePrekey) <;> rfl
    | B =>
      dsimp only
      cases bhDecodePreKeyMsgE c with
      | none =>
        dsimp only
        cases (s.bin.bytes.isEmpty || s.bin.epochs.epoch == 0) <;>
          cases (c.head? == some wireWhisper) <;> rfl
      | some m =>
        dsimp only
        cases (s.bin.bytes.isEmpty || s.bin.epochs.epoch == 0) <;>
          split_ifs <;> rfl

private theorem transmitRM_pure_eq {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (q : Party × Msg × Option Coins) :
    transmitRM (pureSMSchemeRM sm) Δ qep cfg q = SM.transmitR sm Δ qep cfg q := by
  rcases q with ⟨P, m, r⟩
  ext gs
  unfold transmitRM SM.transmitR SM.transmitImpl SMSchemeR.sendPart pureSMSchemeRM liftM monadLift
  dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases cfg.sendOK gs P
  · simp only [Bool.not_false, ↓reduceIte]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, pure_bind,
        bind_assoc]
      congr 1
    · simp only [↓reduceIte]

private theorem challRM_pure_eq {Key St Msg Coins RCoins C : Type} [SampleableType Coins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (q : Party × Msg × Msg × Option Coins) :
    challRM (pureSMSchemeRM sm) Δ qep cfg q = SM.challR sm Δ qep cfg q := by
  rcases q with ⟨P, m₀, m₁, r⟩
  ext gs
  unfold challRM SM.challR SM.challImpl SMSchemeR.sendPart pureSMSchemeRM liftM monadLift
  dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases cfg.sendOK gs P
  · simp only [Bool.not_false, ↓reduceIte]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind]
    cases gs.win
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, pure_bind,
        bind_assoc]
      congr 1
    · simp only [↓reduceIte]

private theorem deliverRM_pure_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : SM.ConfigR St Msg C) (q : Party × C) :
    deliverRM (pureSMSchemeRM sm) cfg q = SM.deliverR sm cfg q := by
  rcases q with ⟨P, c⟩
  ext gs
  unfold deliverRM SM.deliverR pureSMSchemeRM liftM monadLift
  dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases gs.win
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases gs.inTransit P.other c with
    | none => rfl
    | some r =>
      simp only [StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc]
      congr 1
  · simp only [↓reduceIte]

private theorem injectRM_pure_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq C] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : SM.ConfigR St Msg C)
    (q : Party × C) :
    injectRM (pureSMSchemeRM sm) Δ qep cfg q = SM.injectR sm Δ qep cfg q := by
  rcases q with ⟨P, c⟩
  ext gs
  unfold injectRM SM.injectR pureSMSchemeRM liftM monadLift
  dsimp only [MonadLiftT.monadLift, instMonadLiftTOfMonadLift, instMonadLiftT, MonadLift.monadLift]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (gs.win || (gs.inTransit P.other c).isSome || !(gs.safeInj Δ) || !(cfg.injOK c))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_lift, pure_bind,
      bind_assoc]
    congr 1
  · simp only [↓reduceIte]

theorem cliOracleImplRM_cliPqSchemeM_pure_eq (run : CliRun) (l : Nat)
    {S : SignalPqxdh.Setup} {l' : Nat} (bi : ModelDriverInstance S l')
    (stA0 stB0 : CliPartyState) (Δ qep : ℕ)
    (cfg : SM.ConfigR CliPartyState (Plain l) Bytes)
    (q : (SM.spec BinState (Plain l) (BitVec 512) Bytes).Domain) :
    cliOracleImplRM CliPartyState.bin (cliPqSchemeM (cliRunPure run) l bi stA0 stB0) Δ qep cfg q =
      cliOracleImplR CliPartyState.bin (cliPqScheme run l bi stA0 stB0) Δ qep cfg q := by
  rw [cliPqSchemeM_cliRunPure_eq]
  rcases q with (((q₁ | q₂) | q₃) | q₄) | q₅
  · exact transmitRM_pure_eq _ Δ qep cfg q₁
  · exact challRM_pure_eq _ Δ qep cfg q₂
  · exact deliverRM_pure_eq _ cfg q₃
  · exact injectRM_pure_eq _ Δ qep cfg q₄
  · rfl

theorem cliRunStdSM_eq (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S l) (i : Nat) (bi : ModelDriverInstance S l)
    (im : ModelDriverInstanceMeta S) (gs : SM.GameState CliPartyState (Plain l) Bytes)
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    cliRunStdSM S l run qep decT encT ds i bi im gs q = (do
      let scheme := cliPqScheme run l bi (gs.st .A) (gs.st .B)
      let cfg := cliConfigSpkS (St := CliPartyState) (Msg := Plain l) decT encT
      let gsIn : SM.GameState CliPartyState (Plain l) Bytes := match q with
        | .inl (.inl (.inr (.B, c))) => bhAlignTransForBob im.bobAccepted bi.meA.regId bi.hdr c gs
        | _ => gs
      let (r, gsOut) ←
        StateT.lift (liftM ((cliOracleImplR CliPartyState.bin scheme (2 + 1) qep cfg q).run gsIn))
      let gs' : SM.GameState CliPartyState (Plain l) Bytes := match q, r with
        | .inl (.inl (.inr (.B, c))), some (.accepted _ _ _) =>
          match gsIn.inTransit .A c with
          | some rMatched =>
            { gsOut with trans := gs.trans.filter (fun rec => rec.pos != rMatched.pos) }
          | none => { gsOut with trans := gs.trans }
        | .inl (.inl (.inr (.B, _))), _ => { gsOut with trans := gs.trans }
        | _, _ => gsOut
      let im' := bhMetaAfterSM ds.toModelDriverState bi im q r
      set { ds with bhInsts := ds.bhInsts.set i { bi with gs := some (cliMapGameState CliPartyState.bin gs') },
                    instMeta := ds.instMeta.set i im',
                    instGs := ds.instGs.set i (some gs') }
      return r) := by
  unfold cliRunStdSM cliRunStdSMM
  dsimp only
  rw [cliOracleImplRM_cliPqSchemeM_pure_eq]
  rfl

private theorem stateT2_lift_cliPqInitM_pure_bind {S : SignalPqxdh.Setup} {l : Nat} {α : Type}
    (run : CliRun) (W : PEParams) (dA : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen)
    (k : Option CliPartyState → CliDrvM S l α) :
    (StateT.lift (StateT.lift (cliPqInitM (cliRunPure run) W dA b t)) >>= k) =
      k (cliPqInit run W dA b t) := by
  ext cds kst
  simp [cliPqInitM, cliRunPure]
  rfl

theorem cliDrvStart_eq (S : SignalPqxdh.Setup) (l : Nat) (P : SignalPqxdh.Primitives)
    (run : CliRun) (W : PEParams) (mode : BHDrvMode S) (sid : SignalPqxdh.SessionId S) :
    cliDrvStart S l P run W mode sid = (do
      let ds ← get
      let some (hdr, bnd, (u_resp, j_resp)) := bhDrvGuard ds.toModelDriverState sid | return none
      let st0 ← StateT.lift get
      let (.drKeyResp _, st1) ←
        StateT.lift (liftM ((SignalPqxdh.pqxdhKeyIndImpl false S P (.testSession sid)).run st0))
        | return none
      let (.spkSkResp spkSk, st) ←
        StateT.lift (liftM ((SignalPqxdh.pqxdhKeyIndImpl false S P (.revealSpkSk u_resp j_resp)).run st1))
        | return none
      let t_dr ← StateT.lift (liftM ($ᵗ List.Vector (BitVec 8) 32))
      let some (_, u_init, _, t_init) := ds.initTapes.find? (fun (s, _, _, _) => s == sid) | return none
      let some (_, initPrinEntry) := st.principals.find? (fun (idx, _) => idx == u_init.val)
        | return none
      let some (_, respPrinEntry) := st.principals.find? (fun (idx, _) => idx == u_resp.val)
        | return none
      let some (_, respSpkEntry) :=
        st.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) | return none
      let opkSk? ← match hdr.opkId? with
        | none => pure (some none)
        | some opkId =>
          match st.opkEntries.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with
          | some (_, oe) => pure (some (some (opkId.toNat, oe.opkSk)))
          | none => pure none
      let some opkOpt := opkSk? | return none
      let some meA := mkMeEStrict u_init.val initPrinEntry.secIKA0 | return none
      let some meB := mkMeEStrict u_resp.val respPrinEntry.secIKA0 | return none
      let some keysB := mkKeysEStrict j_resp.val respSpkEntry opkOpt | return none
      let some bundleE := mkBundleEStrict u_resp.val bnd | return none
      let dA : PqParty :=
        { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB), session := none,
          signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }
      let some stA0 := cliPqInit run W dA bundleE (appendInitiateTape t_init t_dr) | return none
      let stB0Bin : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
      let bi0 : ModelDriverInstance S l :=
        { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
          meA := meA, meB := meB, keysB := keysB, stA0 := stA0.bin, stB0 := stB0Bin, gs := none }
      let stB0 := cliPartyStateB0 W bi0 (cliPqSigsOf st bi0)
      let scheme := cliPqScheme run l bi0 stA0 stB0
      let gsDir : Option (SM.GameState CliPartyState (Plain l) Bytes) :=
        (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk).map
          (fun b => SM.initState scheme.sendPart () b)
      let gs : Option (SM.GameState BinState (Plain l) Bytes) :=
        gsDir.map (cliMapGameState CliPartyState.bin)
      let bi : ModelDriverInstance S l := { bi0 with gs := gs }
      let im0 : ModelDriverInstanceMeta S :=
        { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
      StateT.lift (set st)
      set { ds with bhInsts := ds.bhInsts ++ [bi], instMeta := ds.instMeta ++ [im0],
                    instGs := ds.instGs ++ [gsDir] }
      return some ds.bhInsts.length) := by
  unfold cliDrvStart cliDrvStartM
  simp only [stateT2_lift_cliPqInitM_pure_bind]
  rfl

end Dir

/-! ## Projected-directory staging -/

/-- Encode `st`'s directory with the peer session file replaced by `rec` (omitted when empty). -/
def cliPqDirRaw (W : PEParams) (st : PqParty) (rec : List (BitVec 8)) :
    List (String × List (BitVec 8)) :=
  let hdrOnly : PqParty :=
    { st with session := none, signed := [], oneTime := [], kyberOneTime := [],
              kyberLastResort := [] }
  encodeDir W hdrOnly ++
    (if rec.isEmpty then [] else [(sessionFile (partyAddress st.party.other), rec)]) ++
    (encodeDir W { st with session := none, peerId := none }).drop 3

/-- CLI invocation inputs for party `st` with session record `rec`, extra files, coins, and stdin. -/
def cliPqInputs (W : PEParams) (st : PqParty) (rec : List (BitVec 8)) (cmd : Cmd)
    (extra : List (String × List (BitVec 8))) (coins stdin : List (BitVec 8)) : Inputs :=
  { argv := cmd.argv
    dirs := partyDirs ++ (match cmd with | .init _ dir => [dir] | _ => [])
    files := cliPqDirRaw W st rec ++ extra ++ [(coinsFile, coins)]
    stdin := stdin }

/-- Extract the updated peer session file and stdout on exit `0`. -/
def cliPqAfter (P : Party) : Option Outcome → Option (List (BitVec 8) × List (BitVec 8))
  | some (.exited 0 out fs) => some ((fs (sessionFile (partyAddress P.other))).getD [], out)
  | _ => none

def cliPqDirA {S : SignalPqxdh.Setup} {l : Nat} (bi : ModelDriverInstance S l) : PqParty :=
  { party := .A, me := bi.meA, peerId := some (bhIdKeyOf bi.idBBytes), session := none,
    signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }

/-- Bob's directory after accepting the expected pre-key message of `bi`. -/
def cliPqxdhDirBobAfterAccept {S : SignalPqxdh.Setup} {l : Nat} (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) : PqParty :=
  let m := bhExpectedPreKeyMsg bi.meA.regId bi.hdr []
  let d0 := cliPqxdhDirBobBeforeAccept bi sigs
  removeOpk ((markKyberUsed d0 m).getD d0) m

/-- Reconstructed party directory for `s` in instance `bi`. -/
def cliPqDirOf {S : SignalPqxdh.Setup} {l : Nat} (bi : ModelDriverInstance S l)
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) (s : BinState) : PqParty :=
  match s.party with
  | .A => cliPqDirA bi
  | .B => if s.bytes.isEmpty then cliPqxdhDirBobBeforeAccept bi sigs else cliPqxdhDirBobAfterAccept bi sigs

def cliPqInit (run : CliRun) (W : PEParams) (dA : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) : Option BinState :=
  (cliPqAfter .A (run (pqInitInputs W dA b t))).map fun (recA, _) =>
    { party := .A, bytes := recA, epochs := { epoch := 0, chains := [(⟨b.spkPub⟩, 0)] } }

def cliPqSend (run : CliRun) (W : PEParams) (d : PqParty) (s : BinState)
    (m : List (BitVec 8)) (rs : BitVec 512) : BinState × List (BitVec 8) :=
  match cliPqAfter s.party (run (cliPqInputs W d s.bytes (.send (partyAddress s.party.other)) []
      (LibsignalSpqrV1.coinBytes rs) m)) with
  | some (recB, wire) => ({ party := s.party, bytes := recB, epochs := s.epochs.send s.party }, wire)
  | none => (s, [])

def cliPqRecv (run : CliRun) (W : PEParams) (d : PqParty) (s : BinState)
    (c : List (BitVec 8)) (rc : BitVec 256) : Option (BinState × Nat × Nat × List (BitVec 8)) :=
  (cliPqAfter s.party (run (cliPqInputs W d s.bytes (.recv (partyAddress s.party.other)) []
      (HMAC.keyToBytes32 rc) c))).map fun (recB, pt) =>
    match (bhWireInnerBytes c).map (SignalMessage.tryFrom protoSignalCodec) with
    | some (.ok msg) =>
      let (t, ep') := s.epochs.recv msg.senderRatchetKey
      ({ party := s.party, bytes := recB, epochs := ep' }, t, msg.counter.toNat + 1, pt)
    | _ => ({ party := s.party, bytes := recB, epochs := s.epochs }, s.epochs.epoch, 0, pt)

/-- Projected `BinState` receive step with pre-key header filtering for instance `bi`. -/
def cliPqReceive (run : CliRun) (W : PEParams) (l : Nat) {S : SignalPqxdh.Setup}
    {l' : Nat} (bi : ModelDriverInstance S l')
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64)
    (s : BinState) (c : List (BitVec 8)) (rc : BitVec 256) :
    Option (BinState × Nat × Nat × Plain l) :=
  let call := fun _ : Unit =>
    (cliPqRecv run W (cliPqDirOf bi sigs s) s c rc).map fun x =>
      (x.1, x.2.1, x.2.2.1, padOrTruncatePlain l x.2.2.2)
  if !cliPqLenOk c then none
  else
    match s.party with
    | .A => if c.head? == some wirePrekey then none else call ()
    | .B =>
      match bhDecodePreKeyMsgE c with
      | some m =>
        if s.bytes.isEmpty || s.epochs.epoch == 0 then
          if c == wirePrekey :: (bhExpectedPreKeyMsg bi.meA.regId bi.hdr m.inner).bytes then call ()
          else none
        else if bhHdrOfPreKeyMsg m == bi.hdr then call ()
        else none
      | none =>
        if s.bytes.isEmpty || s.epochs.epoch == 0 then none
        else if c.head? == some wireWhisper then call ()
        else none

/-- Projected `BinState` secure-messaging scheme for instance `bi`. -/
def cliPqScheme (run : CliRun) (W : PEParams) (l : Nat) {S : SignalPqxdh.Setup}
    {l' : Nat} (bi : ModelDriverInstance S l')
    (sigs : List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 64) (stA0 stB0 : BinState) :
    SMSchemeR Unit BinState (Plain l) (BitVec 512) (BitVec 256) Bytes where
  initA _ := stA0
  initB _ := stB0
  send s m rs := cliPqSend run W (cliPqDirOf bi sigs s) s m.toList rs
  receive s c rc := cliPqReceive run W l bi sigs s c rc

def cliDrvStart (S : SignalPqxdh.Setup) (l : Nat) (P : SignalPqxdh.Primitives)
    (run : CliRun) (W : PEParams) (mode : BHDrvMode S) (sid : SignalPqxdh.SessionId S) :
    BHDrvM S l (Option Nat) := do
  let ds ← get
  let some (hdr, bnd, (u_resp, j_resp)) := bhDrvGuard ds sid | return none
  let st0 ← StateT.lift get
  let (.drKeyResp _, st1) ←
    StateT.lift (liftM ((SignalPqxdh.pqxdhKeyIndImpl false S P (.testSession sid)).run st0))
    | return none
  let (.spkSkResp spkSk, st) ←
    StateT.lift (liftM ((SignalPqxdh.pqxdhKeyIndImpl false S P (.revealSpkSk u_resp j_resp)).run st1))
    | return none
  let t_dr ← StateT.lift (liftM ($ᵗ List.Vector (BitVec 8) 32))
  let some (_, u_init, _, t_init) := ds.initTapes.find? (fun (s, _, _, _) => s == sid) | return none
  let some (_, initPrinEntry) := st.principals.find? (fun (idx, _) => idx == u_init.val)
    | return none
  let some (_, respPrinEntry) := st.principals.find? (fun (idx, _) => idx == u_resp.val)
    | return none
  let some (_, respSpkEntry) :=
    st.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) | return none
  let opkSk? ← match hdr.opkId? with
    | none => pure (some none)
    | some opkId =>
      match st.opkEntries.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with
      | some (_, oe) => pure (some (some (opkId.toNat, oe.opkSk)))
      | none => pure none
  let some opkOpt := opkSk? | return none
  let some meA := mkMeEStrict u_init.val initPrinEntry.secIKA0 | return none
  let some meB := mkMeEStrict u_resp.val respPrinEntry.secIKA0 | return none
  let some keysB := mkKeysEStrict j_resp.val respSpkEntry opkOpt | return none
  let some bundleE := mkBundleEStrict u_resp.val bnd | return none
  let dA : PqParty :=
    { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB), session := none,
      signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }
  let some stA0 := cliPqInit run W dA bundleE (appendInitiateTape t_init t_dr) | return none
  let stB0 : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
  let bi0 : ModelDriverInstance S l :=
    { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
      meA := meA, meB := meB, keysB := keysB, stA0 := stA0, stB0 := stB0, gs := none }
  let scheme := cliPqScheme run W l bi0 (cliPqSigsOf st bi0) stA0 stB0
  let gs : Option (SM.GameState BinState (Plain l) Bytes) :=
    (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB spkSk).map
      (fun b => SM.initState scheme.sendPart () b)
  let bi : ModelDriverInstance S l := { bi0 with gs := gs }
  let im0 : ModelDriverInstanceMeta S :=
    { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
  StateT.lift (set st)
  set { ds with bhInsts := ds.bhInsts ++ [bi], instMeta := ds.instMeta ++ [im0] }
  return some ds.bhInsts.length

def cliRunStdSM (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S l) (i : Nat) (bi : ModelDriverInstance S l) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState BinState (Plain l) Bytes)
    (q : (cliGameSmSpec l (BitVec 512)).Domain) :
    BHDrvM S l ((cliGameSmSpec l (BitVec 512)).Range q) := do
  let kst ← StateT.lift get
  let scheme := cliPqScheme run W l bi (cliPqSigsOf kst bi) bi.stA0 bi.stB0
  let cfg := bhConfigSpkS (Msg := Plain l) decT encT
  let gsIn : SM.GameState BinState (Plain l) Bytes := match q with
    | .inl (.inl (.inr (.B, c))) => bhAlignTransForBob im.bobAccepted bi.meA.regId bi.hdr c gs
    | _ => gs
  let (r, gsOut) ← StateT.lift (liftM ((SM.oracleImplR scheme (2 + 1) qep cfg q).run gsIn))
  let gs' : SM.GameState BinState (Plain l) Bytes := match q, r with
    | .inl (.inl (.inr (.B, c))), some (.accepted _ _ _) =>
      match gsIn.inTransit .A c with
      | some rMatched =>
        { gsOut with trans := gs.trans.filter (fun rec => rec.pos != rMatched.pos) }
      | none => { gsOut with trans := gs.trans }
    | .inl (.inl (.inr (.B, _))), _ => { gsOut with trans := gs.trans }
    | _, _ => gsOut
  let im' := bhMetaAfterSM ds bi im q r
  set { ds with bhInsts := ds.bhInsts.set i { bi with gs := some gs' },
                instMeta := ds.instMeta.set i im' }
  return r

def cliStepLocalSM (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : ModelDriverState S l) (i : Nat) (bi : ModelDriverInstance S l) (im : ModelDriverInstanceMeta S)
    (gs : SM.GameState BinState (Plain l) Bytes) :
    (q : (cliGameSmSpec l (BitVec 512)).Domain) →
      BHDrvM S l ((cliGameSmSpec l (BitVec 512)).Range q)
  | .inl (.inl (.inr (.A, c))) => do
    if (bhDecodePreKeyMsgE c).isSome then return none
    else cliRunStdSM S l run W qep decT encT ds i bi im gs (.inl (.inl (.inr (.A, c))))
  | .inl (.inr (.A, c)) => do
    if (bhDecodePreKeyMsgE c).isSome then return none
    else cliRunStdSM S l run W qep decT encT ds i bi im gs (.inl (.inr (.A, c)))
  | .inl (.inl (.inr (.B, c))) => do
    if (bhPartneredInnerBytes im.bobAccepted bi.meA.regId bi.hdr c).isNone then return none
    else cliRunStdSM S l run W qep decT encT ds i bi im gs (.inl (.inl (.inr (.B, c))))
  | .inl (.inr (.B, c)) => do
    if !im.bobAccepted then return none
    else if (bhPartneredInnerBytes true bi.meA.regId bi.hdr c).isNone ||
        bhPartneredInTransitA true bi.meA.regId bi.hdr c gs then return none
    else cliRunStdSM S l run W qep decT encT ds i bi im gs (.inl (.inr (.B, c)))
  | q => cliRunStdSM S l run W qep decT encT ds i bi im gs q

def cliDrvSM (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (run : CliRun) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (BHDrvM S l)) :
    QueryImpl (cliGameDrSpec l (BitVec 512)) (BHDrvM S l) := fun ⟨i, q⟩ => do
  let ds ← get
  if !bhDrvInstClean ds i then return bhSmDefaultWithSpqr q
  else
    match ds.bhInsts[i]?, ds.instMeta[i]? with
    | some bi, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhInstIkACorrupted ds bi then
        let imCorr : ModelDriverInstanceMeta S := { im with bobAccepted := true, ikACorrAtAccept := true }
        set { ds with instMeta := ds.instMeta.set i imCorr }; return bhSmDefaultWithSpqr q
      else
        match bi.gs with
        | none =>
          let r ← ext q
          set { ds with instMeta := ds.instMeta.set i (bhMetaAfterSM ds bi im q r) }; return r
        | some gs => cliStepLocalSM S l run W qep decT encT ds i bi im gs q
    | _, _ => return bhSmDefaultWithSpqr q

def cliDrvCtl (S : SignalPqxdh.Setup) (l : Nat) (P : SignalPqxdh.Primitives)
    (run : CliRun) (W : PEParams) (mode : BHDrvMode S) : QueryImpl (bhDrCtlSpec S) (BHDrvM S l)
  | .startDR sid => cliDrvStart S l P run W mode sid

/-- Full projected CLI oracle implementation over `BHDrvM S l`. -/
def cliDrvImpl (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (BHDrvM S l)) (mode : BHDrvMode S) :
    QueryImpl (cliGameSpec S l (BitVec 512)) (BHDrvM S l) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (BHDrvM S l) + bhDrvKeyInd S l P false +
    cliDrvCtl S l P run W mode + cliDrvSM S l run W qep decT encT ext

def runCliDriver (S : SignalPqxdh.Setup) (l : Nat) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : Nat)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec l (BitVec 512)) (BHDrvM S l)) (mode : BHDrvMode S)
    (A : CliGameAdversary S l (BitVec 512)) :
    StateT (SignalPqxdh.KeyIndState S) ProbComp (Bool × ModelDriverState S l) :=
  (simulateQ (cliDrvImpl S l P run W qep decT encT ext mode) A.run).run {}

/-- Composed `BinState` game interface for the projected CLI experiment. -/
def cliIfaceProj (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (l qep : Nat) {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) : ComposedIface S l where
  St := BinState
  prims := modelPrims X W
  Drv := ModelDriverState S l
  init _ := {}
  impl b := cliDrvImpl S l (modelPrims X W) run W qep decT encT bhNoExtWithSpqr
    (fun _ _ _ _ _ => some b)
  won := driverSomeInstanceWon

/-- Projected CLI security experiment over `cliIfaceProj`. -/
def cliPqExpProj (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (l qep : Nat) {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) (A : CliGameAdversary S l (BitVec 512)) : ProbComp Bool :=
  composedExp (cliIfaceProj S run X W l qep decT encT) A.run

/-- Adversary advantage in the projected CLI security experiment `cliPqExpProj`. -/
noncomputable def CliPqxdhAdvantageProj (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (l qep : Nat) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S l (BitVec 512)) : ℝ≥0∞ :=
  𝒟[cliPqExpProj S run X W l qep decT encT A].boolBias

end CryptoVerification.E2E
