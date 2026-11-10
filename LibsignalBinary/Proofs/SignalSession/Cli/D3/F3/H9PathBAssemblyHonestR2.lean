/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyG2
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# Slot `sEnvs` Wiring for `H9PathBAssemblyG2`

**Checked by Lean.**

Connects `D3MainEntryBudgetFitsCapDom0` to `H9PathBAssemblyG2` over the `RunSlotEnvs` bundle
`hmx_binaryKitRunSlotEnvsSlotOf`, discharging named-writes bounds, `encrypt` semantics alignment,
and `init` frame-pointer invariance internally for `cliRunSemPathB`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2

open Arm64 ProofLib SepProp
open Arm64.Obj (Image MultiPlacement)
open Arm64.Process (bytesOfString)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (IdentityKey SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi (
  PreKeySignalMessage SessionRecord StoreCall fullTrace messageDecryptSignal_trace_prefix
)
open CryptoVerification (
  LibsignalFrozen LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns
)
open CryptoVerification.E2E (
  PEParams UnreachedPqxdhPrimitives partyAddressName pqxdhSpqrModel recvPrekeyState wirePrekey
  wireWhisper
)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal serializeAddrVals)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession (
  CliHooks CliPqxdhInputs Inputs baseKeysFile cliExternsPlaced identityFile libsignalSessionLib
  oneTimeKyberPreKeyFile oneTimePreKeyFile partyAddress sessionFile stdinCapBytes
)
open CryptoVerification.SignalSession.Cli (
  DirGhost IdGhost KyberGhost StoresGhost addressText baseKeysName keyName pathOf removePreKey utf8
)
open CryptoVerification.SignalSession.Cli.MainHops (
  AddrV DirWrOk RunCall StoreCallPeerPlaced StoresWrOk addrParse cliIo cliMainStk cliResStack
  cliRunBudgets cliRunNeeds cliRunSemD2c_placed inputOf keyName_length mainFrameSize
  messageDecryptSignal_calls_peer_placed namedWrites namedWrites_ascii okPeerPath parseArgs
  saveUpd_own saveUpd_peers_path
)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (
  DecPkGhost DecSigGhost EncGhost Init2Data InitGhost RunSem SlotAns addrValOf finish mkSlot
  readBundleV runAns runFiles runRel
)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (
  SessMatchesPm cliAnswers cliFinal cliStep decPkDef decPkDefD2c decPkDefD2c_eq_decPkDef_of_match
  decPkDefD2c_eq_decPkDef_of_noCurrent decPkDefD2c_eq_decPkDef_of_untrusted
  decPkDefD2c_namedWrites_sub decSigDef decSigKey encDef initDef initParty pkRecvCoins pkStoreKeys
  pkToE?
)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine (
  addrValE runAns_pqRecvBad runAns_pqRecvPrekey_eq runAns_pqRecvWhisper_eq
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact (
  w1EncExactCum w1EncExactGrpS w1EncExactLive w1EncExactMaxReq w1EncExactPeak
  w2DecSigExactCum w2DecSigExactGrpS w2DecSigExactLive w2DecSigExactMaxReq w2DecSigExactPeak
)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (
  W1BinarySendDom W1BinarySendParams W2BinaryWhisperDom W2BinaryWhisperParams W3BinaryInitParams
)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0 (
  d3SlotMainFitsOneGiBOf mainEntryBudgetFitsCapOf_pqD3Recv_dom0
  mainEntryBudgetFitsCapOf_pqD3Recv_dom0_of_singleSlot
  mainEntryBudgetFitsCapOf_pqD3Recv_slot_of_caps
)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal (pqRunAns_namedWrites_bounds)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact (hmx_binaryKitRunSlotEnvsSlotOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  W3InitBinaryKitSlotEnvFixed realCliInitBinarySlotEnvFixed
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3 (Block617TransferFixedHyp)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (
  MainOkPathBD3F3 cliRunSemPathB
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (
  CliPqOrD3RecvInputs pqD3ScopedRun
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyG2 (
  h9g_pathB_assembly_of_d2cSlots_and_fitsCap h9g_pathB_assembly_of_fitsCap
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (
  MainIoOfPlaced ReadStdinBoundedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget (
  cliRunArmEnvs cliRunCalleesEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget (
  r2EncGhost r2PeerGhost0
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget (
  r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget (
  CliInitSlotOkPlaced CliRunHooksBundle
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  RunSlotEnvs decSigSlotSpecFrozenPlaced encSlotSpecPlaced slotsOfSigPkFrozenPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (
  PksmTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

/-! ## 1. Honest D3 Slot `sEnvs` Bundles, Congruence & Named-Writes Bounds -/

/-- `RunSlotEnvs` bundle over `(EncSlot, DecSigSlot, realCliInitBinarySlotEnvFixed W, DecPkSlotEnv)`,
definitionally equal to `binaryKitRunSlotEnvsExact` when instantiated in `CliElfLib`. -/
noncomputable abbrev h9r2_honestD3RunSlotEnvs {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs :=
  hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A B
    (realCliInitBinarySlotEnvFixed W) DecPkSlotEnv

/-- `(X, W, γ, tp)`-indexed `RunSlotEnvs` family at `fineHookRustCliAllocBudget γ mmpl tp brkStart`
matching the `sEnvs` parameter shape of `H9PathBAssemblyG2`. -/
noncomputable abbrev h9r2_honestD3FineSlotEnvs
    {mpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (EncSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (mmpl : MultiPlacement) (brkStart : BitVec 64) (B : RunBudgets)
    (DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunSlotEnvs :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  h9r2_honestD3RunSlotEnvs (fun {_M'} A' B' => EncSlot W A' B')
    (fun {_M'} A' B' => DecSigSlot W A' B') W
    (fineHookRustCliAllocBudget γ mmpl tp brkStart) B (DecPkSlotEnv X W γ tp)

private theorem h9r2_w3InitFixed_congr {w₁ w₂ : W3BinaryInitParams}
    (hpeer : w₁.x.peer = w₂.x.peer) (hxF : w₁.x.F = w₂.x.F)
    (hF : w₁.F = w₂.F) (hpk : w₁.peerKey = w₂.peerKey)
    (hspqr : w₁.x_spqr = w₂.x_spqr) (hg : w₁.g_rec = w₂.g_rec) (hr : w₁.r_rec = w₂.r_rec) :
    W3InitBinaryKitSlotEnvFixed w₁ = W3InitBinaryKitSlotEnvFixed w₂ := by
  funext evs
  unfold W3InitBinaryKitSlotEnvFixed
  rw [hpeer, hxF, hF, hpk, hspqr, hg, hr]

/-- Frame-pointer invariance of `realCliInitBinarySlotEnvFixed W`. -/
theorem h9r2_initEnv_r1c_congr (W : CliHooks) (g : RunCall) (d2 : Init2Data) (fsp : BitVec 64) :
    realCliInitBinarySlotEnvFixed W (r1cInitGhost g d2 fsp) =
      realCliInitBinarySlotEnvFixed W (r1cInitGhost g d2 0#64) := by
  funext evs
  apply propext
  constructor
  · rintro ⟨w, hx, hF, hspqr, hgv, halice, hslot⟩
    refine ⟨{ w with x := r1cInitGhost g d2 0#64 }, rfl, hF, hspqr, hgv, halice, ?_⟩
    have heq := h9r2_w3InitFixed_congr (w₁ := w) (w₂ := { w with x := r1cInitGhost g d2 0#64 })
      (by rw [hx]; rfl) (by rw [hx]; rfl) rfl rfl rfl rfl rfl
    exact Eq.mp (congrFun heq evs) hslot
  · rintro ⟨w, hx, hF, hspqr, hgv, halice, hslot⟩
    refine ⟨{ w with x := r1cInitGhost g d2 fsp }, rfl, hF, hspqr, hgv, halice, ?_⟩
    have heq := h9r2_w3InitFixed_congr (w₁ := w) (w₂ := { w with x := r1cInitGhost g d2 fsp })
      (by rw [hx]; rfl) (by rw [hx]; rfl) rfl rfl rfl rfl rfl
    exact Eq.mp (congrFun heq evs) hslot

/-- `(cliRunSemPathB X W).encrypt` coincides with `RunProofs.encDef ⟨W.C, W.Q⟩ scopeIn`. -/
theorem h9r2_cliRunSemPathB_encrypt_eq (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    (cliRunSemPathB X W).encrypt = encDef ⟨W.C, W.Q⟩ scopeIn :=
  rfl

private theorem h9r2_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private def h9r2_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem h9r2_utf8_eq (s : String) : utf8 s = h9r2_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, h9r2_kutf8, List.utf8Encode, h9r2_byteArray_toList_eq_data]

private theorem h9r2_utf8_append (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by
  rw [h9r2_utf8_eq, h9r2_utf8_eq, h9r2_utf8_eq]
  simp [h9r2_kutf8, String.toList_append, List.flatMap_append]

private theorem h9r2_toString_one : toString (1 : Nat) = "1" := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  exact String.toList_inj.mp (by rw [ht1, hd1, String.toList_singleton]; rfl)

private theorem h9r2_sessionFile_partyAddress_eq (P : Party) :
    sessionFile (partyAddress P) = "sessions/" ++ partyAddressName P ++ "." ++ "1" := by
  simp only [sessionFile, partyAddress, CryptoVerification.SignalSession.Address.text,
    h9r2_toString_one, String.append_assoc]

private theorem h9r2_okPeerPath_id (P : Party) :
    okPeerPath P (pathOf (utf8 "identities") (addrValE P).name) := by
  have hpath : pathOf (utf8 "identities") (addrValE P).name =
      utf8 (identityFile (partyAddressName P)) := by
    have hne : utf8 "identities" ≠ [] := by rw [h9r2_utf8_eq]; decide
    simp only [pathOf, hne, ↓reduceIte, addrValE, identityFile]
    rw [← h9r2_utf8_append, ← h9r2_utf8_append]
    rfl
  rw [hpath]
  refine ⟨?_, .inl ?_⟩
  · rw [h9r2_utf8_eq]
    intro b hb
    have hall :
        (h9r2_kutf8 (identityFile (partyAddressName P))).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [h9r2_utf8_eq]
    cases P <;> decide

private theorem h9r2_okPeerPath_sess (P : Party) :
    okPeerPath P (pathOf (utf8 "sessions") (addressText (addrValE P))) := by
  have hpath : pathOf (utf8 "sessions") (addressText (addrValE P)) =
      utf8 (sessionFile (partyAddress P)) := by
    have hne : utf8 "sessions" ≠ [] := by rw [h9r2_utf8_eq]; decide
    have had : addressText (addrValE P) = utf8 (partyAddress P).text := by
      have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
      simp only [addressText, addrValE, CryptoVerification.SignalSession.Cli.decimalText, h1,
        CryptoVerification.SignalSession.Address.text, partyAddress]
      rw [← h9r2_utf8_append, ← h9r2_utf8_append]
    rw [had]
    simp only [pathOf, hne, ↓reduceIte, sessionFile]
    rw [← h9r2_utf8_append, ← h9r2_utf8_append]
    rfl
  rw [hpath]
  refine ⟨?_, .inr ?_⟩
  · rw [h9r2_utf8_eq, h9r2_sessionFile_partyAddress_eq]
    intro b hb
    have hall :
        (h9r2_kutf8 ("sessions/" ++ partyAddressName P ++ "." ++ "1")).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [h9r2_utf8_eq, h9r2_sessionFile_partyAddress_eq]
    cases P <;> decide

private theorem h9r2_list_length_le_flatMap_utf8EncodeChar :
    ∀ l : List Char, l.length ≤ (l.flatMap String.utf8EncodeChar).length
  | [] => Nat.le_refl 0
  | c :: cs => by
    have hc : 1 ≤ (String.utf8EncodeChar c).length := by
      unfold String.utf8EncodeChar; dsimp only
      by_cases h1 : c.val.toNat ≤ 127
      · simp only [h1, ↓reduceIte, List.length_cons, List.length_nil]; omega
      · by_cases h2 : c.val.toNat ≤ 2047
        · simp only [h1, h2, ↓reduceIte, List.length_cons, List.length_nil]; omega
        · by_cases h3 : c.val.toNat ≤ 65535
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
    have ih := h9r2_list_length_le_flatMap_utf8EncodeChar cs
    simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega

private theorem h9r2_string_length_le_utf8_length (s : String) : s.length ≤ (utf8 s).length := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  rw [String.length_ofList]
  have hutf : (utf8 (String.ofList l)).length = (l.flatMap String.utf8EncodeChar).length := by
    simp [utf8, List.utf8Encode, h9r2_byteArray_toList_eq_data]
  rw [hutf]
  exact h9r2_list_length_le_flatMap_utf8EncodeChar l

private theorem h9r2_u32_toString_len_le_10 (id : BitVec 32) :
    (toString id.toNat).length ≤ 10 :=
  Nat.le_trans (h9r2_string_length_le_utf8_length (toString id.toNat)) (keyName_length id)

private theorem h9r2_identityFile_len_le_64 (P : Party) :
    (identityFile (partyAddressName P)).length ≤ 64 := by
  cases P <;> decide

private theorem h9r2_sessionFile_len_le_64 (P : Party) :
    (sessionFile (partyAddress P)).length ≤ 64 := by
  rw [h9r2_sessionFile_partyAddress_eq]
  cases P <;> decide

private theorem h9r2_oneTimeKyberPreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimeKyberPreKeyFile id).length ≤ 64 := by
  have h := h9r2_u32_toString_len_le_10 id
  unfold oneTimeKyberPreKeyFile; rw [String.length_append]
  have hp : ("one-time-kyber-pre-keys/").length = 24 := by decide
  omega

private theorem h9r2_baseKeysFile_len_le_64 (id : BitVec 32) :
    (baseKeysFile id).length ≤ 64 := by
  have h := h9r2_u32_toString_len_le_10 id
  unfold baseKeysFile; simp only [String.length_append]
  have hp1 : ("last-resort-kyber-pre-keys/").length = 27 := by decide
  have hp2 : (".base-keys").length = 10 := by decide
  omega

private theorem h9r2_oneTimePreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimePreKeyFile id).length ≤ 64 := by
  have h := h9r2_u32_toString_len_le_10 id
  unfold oneTimePreKeyFile; rw [String.length_append]
  have hp : ("one-time-pre-keys/").length = 18 := by decide
  omega

private theorem h9r2_setOrPush_length_le_succ
    (xs : List (List (BitVec 8) × List (BitVec 8))) (k v : List (BitVec 8)) :
    (DirGhost.setOrPush k v xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [DirGhost.setOrPush]
  | cons _ _ ih =>
    unfold DirGhost.setOrPush
    split <;> [simp; (simp only [List.length_cons]; omega)]

private theorem h9r2_dirPut_writes_length_le_succ (d : DirGhost) (k v : List (BitVec 8)) :
    (d.put k v).writes.length ≤ d.writes.length + 1 := by
  simp only [DirGhost.writes, DirGhost.put, List.length_map]
  exact h9r2_setOrPush_length_le_succ d.changed k v

private theorem h9r2_saveUpd_peers_writes_length_le_succ (F : FsFiles)
    (idG : IdGhost) (rem : AddrVal) (k : IdentityKey) :
    (idG.saveUpd cliIo.rd F rem k).peers.writes.length ≤ idG.peers.writes.length + 1 ∧
      (idG.saveUpd cliIo.rd F rem k).own = idG.own := by
  refine ⟨?_, saveUpd_own cliIo.rd F idG rem k⟩
  unfold IdGhost.saveUpd
  split
  · exact h9r2_dirPut_writes_length_le_succ idG.peers rem.name k.serialize
  · exact Nat.le_succ _

private theorem h9r2_foldl_cliStep_writes_length_le (F : FsFiles) :
    ∀ (calls : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (calls.foldl (cliStep F) g).writes.length ≤ g.writes.length + calls.length
  | [], g => by simp
  | c :: cs, g => by
    have h1 : (cliStep F g c).writes.length ≤ g.writes.length + 1 := by
      cases c with
      | loadSession _ | isTrustedIdentity _ _ _ => exact Nat.le_succ _
      | saveIdentity rem k =>
        obtain ⟨hp, ho⟩ := h9r2_saveUpd_peers_writes_length_le_succ F g.identity rem k
        dsimp only [cliStep, StoresGhost.writes]; rw [ho]; simp only [List.length_append]; omega
      | storeSession rem r =>
        dsimp only [cliStep, StoresGhost.writes]
        have hs := h9r2_dirPut_writes_length_le_succ g.sessions (addressText rem)
          (CryptoVerification.E2E.Record.encodeRecord r)
        simp only [List.length_append]; omega
    have h2 := h9r2_foldl_cliStep_writes_length_le F cs (cliStep F g c)
    dsimp only [List.foldl, List.length_cons]; omega

private theorem h9r2_storesWrOk_foldl (F : FsFiles) (P : Party) :
    ∀ (cs : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (∀ c ∈ cs, StoreCallPeerPlaced (addrValE P) c) →
      StoresWrOk (okPeerPath P) g →
      g.identity.peers.path = utf8 "identities" →
      g.sessions.path = utf8 "sessions" →
      StoresWrOk (okPeerPath P) (cs.foldl (cliStep F) g) := by
  intro cs
  induction cs with
  | nil => intro g _ hg0 _ _; exact hg0
  | cons c cs' ih =>
    intro g hcs hg0 hp hs
    have hc1 := hcs c List.mem_cons_self
    cases c with
    | loadSession _ | isTrustedIdentity _ _ _ =>
      exact ih g (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hg0 hp hs
    | saveIdentity rem k =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with
          own := by rw [saveUpd_own]; exact hg0.own
          peers := DirWrOk.saveUpd hg0.peers (hp ▸ h9r2_okPeerPath_id P) }
        (by rw [saveUpd_peers_path, hp]) hs
    | storeSession rem _r0 =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with sessions := hg0.sessions.put (hs ▸ h9r2_okPeerPath_sess P) _ } hp hs

private theorem h9r2_decPkDef_writes_len_le_4 {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal}
    {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F (addrValE P) me pm coins = some (some (g', pt))) :
    g'.writes.length ≤ 4 := by
  unfold decPkDef at h
  dsimp only at h
  cases hload : loadRec Scope F (addrValE P) with
  | error _ => rw [hload] at h; cases h
  | ok r =>
    rw [hload] at h; dsimp only at h
    cases htr : StoresGhost.opened.identity.trusted cliIo.rd F (addrValE P) pm.identityKey with
    | error _ => rw [htr] at h; cases h
    | ok tb =>
      cases tb with
      | false => rw [htr] at h; cases h
      | true =>
        rw [htr] at h; dsimp only at h
        cases hcur : r.bind (·.currentSession) with
        | some s =>
          rw [hcur] at h; dsimp only at h
          split at h
          · split at h
            · cases h
            · cases hdec : SessionState.tryDecryptFromRecord W.C
                  (CryptoVerification.E2E.pqxdhSpqrSession W)
                  ((CryptoVerification.E2E.pqxdhSessionParams W).expectedAddrs
                    (initParty (addrValE P)))
                  pm.message .preKey (pkRecvCoins coins) s.state with
              | mk res st1 =>
                rw [hdec] at h
                cases res with
                | ok _ =>
                  dsimp only at h
                  injection h with h1; injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  obtain ⟨hp, ho⟩ := h9r2_saveUpd_peers_writes_length_le_succ F
                    StoresGhost.opened.identity (addrValE P) pm.identityKey
                  have hs := h9r2_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                    (addressText (addrValE P))
                    (CryptoVerification.E2E.Record.encodeRecord
                      { currentSession := some
                          { state := st1, pendingPreKey := none, pendingKyberPreKey := none,
                            localRegistrationId := s.localRegistrationId,
                            remoteRegistrationId := s.remoteRegistrationId,
                            aliceBaseKey := s.aliceBaseKey } })
                  have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                  have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                  have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                  have h0_kot : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                  have h0_klr : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                  have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                  have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                  have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                  dsimp only [StoresGhost.writes]; rw [ho]
                  simp only [List.length_append, h0_own, h0_signed, h0_kot, h0_klr, h0_ot, h0_pub]
                  omega
                | error err => cases err <;> cases h
          · cases h
        | none =>
          rw [hcur] at h; dsimp only at h
          cases hpk : pkToE? pm with
          | none => rw [hpk] at h; cases h
          | some m =>
            rw [hpk] at h; dsimp only at h
            cases hsk : pkStoreKeys F m with
            | none => rw [hsk] at h; cases h
            | some k =>
              rw [hsk] at h
              cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd F with
              | error _ => rw [hkp] at h; cases h
              | ok kp =>
                rw [hkp] at h
                cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
                | error _ => rw [hreg] at h; cases h
                | ok reg =>
                  rw [hreg] at h; dsimp only at h
                  cases hrecv : recvPrekeyState X W
                      (initParty (addrValE P)) ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
                  | none => rw [hrecv] at h; cases h
                  | some o =>
                    rw [hrecv] at h
                    cases o with
                    | none => cases h
                    | some triple =>
                      rcases triple with ⟨x, gs, _⟩
                      dsimp only at h
                      cases hkm : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId
                          pm.signedPreKeyId pm.baseKey with
                      | mk kres kyber' =>
                        rw [hkm] at h
                        cases kres with
                        | error _ => cases h
                        | ok u =>
                          cases u; dsimp only at h
                          injection h with h1; injection h1 with h2
                          obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                          have hkyb : kyber'.oneTime.writes.length + kyber'.lastResort.writes.length ≤ 1 := by
                            unfold KyberGhost.mark at hkm
                            cases hot : StoresGhost.opened.kyber.oneTime.get cliIo.rd F
                                (keyName m.kpkId) with
                            | error _ => rw [hot] at hkm; cases hkm
                            | ok bs =>
                              rw [hot] at hkm
                              cases bs with
                              | cons _ _ =>
                                dsimp only at hkm; injection hkm with _ hk; subst hk; dsimp only
                                have h1 := h9r2_dirPut_writes_length_le_succ
                                  StoresGhost.opened.kyber.oneTime (keyName m.kpkId) []
                                have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                                have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                                omega
                              | nil =>
                                dsimp only at hkm
                                cases hlr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F
                                    (baseKeysName m.kpkId) with
                                | error _ => rw [hlr] at hkm; cases hkm
                                | ok seen =>
                                  rw [hlr] at hkm; dsimp only at hkm
                                  split at hkm
                                  · cases hkm
                                  · split at hkm
                                    · cases hkm
                                    · injection hkm with _ hk; subst hk; dsimp only
                                      have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                                      have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                                      rw [h0a, Nat.zero_add]
                                      exact Nat.le_trans (h9r2_dirPut_writes_length_le_succ _ _ _)
                                        (by rw [h0b])
                          obtain ⟨hp_le, ho⟩ := h9r2_saveUpd_peers_writes_length_le_succ F
                            StoresGhost.opened.identity (addrValE P) pm.identityKey
                          have hs_le := h9r2_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                            (addressText (addrValE P))
                            (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)
                          have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                          have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                          have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                          have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                          have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                          unfold StoresGhost.writes; dsimp only; rw [ho]
                          simp only [List.length_append, h0_own, h0_signed, h0_pub]
                          cases pm.preKeyId with
                          | none =>
                            dsimp only
                            have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                            omega
                          | some j =>
                            dsimp only; unfold removePreKey
                            cases StoresGhost.opened.oneTime.get cliIo.rd F (keyName j) with
                            | error _ =>
                              dsimp only
                              have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                              omega
                            | ok bs =>
                              cases bs with
                              | nil =>
                                dsimp only
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega
                              | cons _ _ =>
                                dsimp only
                                have hot_put := h9r2_dirPut_writes_length_le_succ
                                  StoresGhost.opened.oneTime (keyName j) []
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega

private theorem h9r2_decPkDef_some_some_eq_d2c {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F peer me pm coins = some (some (g', pt))) :
    decPkDefD2c X W Scope F peer me pm coins = some (some (g', pt)) := by
  by_cases htr : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true
  · cases hload : loadRec Scope F peer with
    | error _ =>
      unfold decPkDef at h; simp [hload] at h
    | ok opt =>
      cases opt with
      | none =>
        rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F peer me pm coins
          (fun _ hl => by rw [hload] at hl; cases hl)]
        exact h
      | some r =>
        cases hcur : r.currentSession with
        | none =>
          rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F peer me pm coins
            (fun _ hl => by
              rw [hload] at hl; injection hl with hr; injection hr with hr; subst hr; exact hcur)]
          exact h
        | some s =>
          by_cases hm : SessMatchesPm s pm
          · rw [decPkDefD2c_eq_decPkDef_of_match X W Scope F peer me pm coins hload hcur hm]
            exact h
          · unfold decPkDef at h
            simp [hload, htr, hcur, hm] at h
  · rw [decPkDefD2c_eq_decPkDef_of_untrusted X W Scope F peer me pm coins htr]
    exact h

private theorem h9r2_finish_inv {α : Type} {ans : SlotAns α}
    {outFn : α → List (BitVec 8)} {ws : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : finish ans outFn = some (some (ws, out))) :
    ∃ g' v, ans = some (some (g', v)) ∧ ws = namedWrites g'.writes ∧ out = outFn v := by
  cases ans with
  | none => cases h
  | some o =>
    cases o with
    | none => cases h
    | some gv =>
      rcases gv with ⟨g', v⟩
      dsimp only [finish] at h
      injection h with h1; injection h1 with h2
      obtain ⟨hw, ho⟩ := Prod.mk.inj h2
      exact ⟨g', v, rfl, hw.symm, ho.symm⟩

private theorem h9r2_runAns_some_some_to_d2c
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {S : RunSem}
    (hinit : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (henc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecSig : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hpksm : S.pksmParse = pksmParse)
    {i : Inputs} {nw : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (ha : runAns S i = some (some (nw, out))) :
    runAns (cliRunSemD2c_placed X W) i = some (some (nw, out)) := by
  unfold runAns at ha ⊢
  cases hp : parseArgs uuidTryParse (i.argv.map bytesOfString) with
  | none => rw [hp] at ha; cases ha
  | some c =>
    rw [hp] at ha; dsimp only at ha ⊢
    cases hown : StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") with
    | error _ => rw [hown] at ha; cases ha
    | ok ownB =>
      rw [hown] at ha; dsimp only at ha ⊢
      cases had : addrParse uuidTryParse ownB with
      | none => rw [had] at ha; cases ha
      | some _meV =>
        rw [had] at ha; dsimp only at ha ⊢
        cases c with
        | keygen _ _ => cases ha
        | init peerV dir =>
          dsimp only at ha ⊢
          cases hbv : readBundleV (runFiles i) dir peerV.device with
          | none => rw [hbv] at ha; cases ha
          | some _b =>
            rw [hbv] at ha; dsimp only at ha ⊢
            have hd2c_in : (cliRunSemD2c_placed X W).initiate = initDef X ⟨W.C, W.Q⟩ := rfl
            rw [hinit] at ha; rw [hd2c_in]; exact ha
        | send _peerV =>
          dsimp only at ha ⊢
          rw [henc] at ha; exact ha
        | recv _peerV =>
          dsimp only at ha ⊢
          cases hst : i.stdin with
          | nil => rw [hst] at ha; cases ha
          | cons t rest =>
            rw [hst] at ha; dsimp only at ha ⊢
            by_cases ht2 : t = 2#8
            · simp only [ht2, ↓reduceIte] at ha ⊢
              rw [hdecSig] at ha; exact ha
            · simp only [ht2, ↓reduceIte] at ha ⊢
              by_cases ht3 : t = 3#8
              · simp only [ht3, ↓reduceIte] at ha ⊢
                have hd2c_pk : (cliRunSemD2c_placed X W).pksmParse = pksmParse := rfl
                have hd2c_dp : (cliRunSemD2c_placed X W).decryptPrekey =
                    decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn := rfl
                rw [hpksm] at ha; rw [hd2c_pk, hd2c_dp]
                cases hpm : pksmParse rest with
                | none => rw [hpm] at ha; cases ha
                | some pm =>
                  rw [hpm] at ha; dsimp only at ha ⊢
                  rw [hdecPk] at ha
                  obtain ⟨g', v, hg, hnw, hout⟩ := h9r2_finish_inv ha
                  rw [h9r2_decPkDef_some_some_eq_d2c hg]
                  simp [finish, hnw, hout]
              · simp only [ht3, ↓reduceIte] at ha; cases ha

private theorem h9r2_decSigDef_writes_bounds {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    g'.writes.length ≤ 4 := by
  unfold decSigDef at h
  split at h
  · next _pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    obtain ⟨_k, _r, -, hpref⟩ :=
      messageDecryptSignal_trace_prefix W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
        msg (addrValE P) me (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)
    rw [heq] at hpref
    have hclen : calls.length ≤ 4 := Nat.le_trans hpref.length_le (by simp [fullTrace])
    have hf := h9r2_foldl_cliStep_writes_length_le F calls StoresGhost.opened
    have h0 : StoresGhost.opened.writes.length = 0 := rfl
    dsimp only [cliFinal]; omega
  · cases h
  · cases h

private theorem h9r2_storesWrOk_decSigDef {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold decSigDef at h
  split at h
  · next _pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    have hc := messageDecryptSignal_calls_peer_placed
      W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
      msg (addrValE P) me (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)
    rw [heq] at hc
    exact h9r2_storesWrOk_foldl F P calls StoresGhost.opened hc (StoresWrOk.opened _) rfl rfl
  · cases h
  · cases h

private theorem h9r2_nwDom_pqD3Recv
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {S : RunSem}
    (hinit : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (henc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecSig : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hpksm : S.pksmParse = pksmParse)
    (i : Inputs)
    (nw : List (String × List (BitVec 8))) (out : List (BitVec 8))
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i)
    (ha : runAns S i = some (some (nw, out))) :
    nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64 := by
  have ha_d2c := h9r2_runAns_some_some_to_d2c hinit henc hdecSig hdecPk hpksm ha
  rcases hi with hi_pq | ⟨st, ct, rc, _hwf, rfl⟩
  · exact pqRunAns_namedWrites_bounds hi_pq ha_d2c
  · cases ct with
    | nil =>
      rw [runAns_pqRecvBad S ⟨W.C, W.Q⟩ st [] rc (by decide) (by decide)] at ha; cases ha
    | cons t rest =>
      by_cases ht2 : t = wireWhisper
      · subst ht2
        rw [runAns_pqRecvWhisper_eq S ⟨W.C, W.Q⟩ st rest rc, hdecSig] at ha
        cases hsm : SignalMessage.tryFrom protoSignalCodec rest with
        | error _ => rw [hsm] at ha; cases ha
        | ok msg =>
          rw [hsm] at ha; dsimp only at ha
          obtain ⟨g', _v, hg, rfl, _⟩ := h9r2_finish_inv ha
          have hlen4 : g'.writes.length ≤ 4 := h9r2_decSigDef_writes_bounds hg
          have hwr : StoresWrOk (okPeerPath st.party.other) g' := h9r2_storesWrOk_decSigDef hg
          refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
          have hasc : ∀ w ∈ g'.writes, ∀ b ∈ w.1, b.toNat < 128 :=
            fun w hw => (hwr.writes w hw).1
          rw [namedWrites_ascii g'.writes hasc] at hq
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
          rcases (hwr.writes w hw).2 with hp | hp <;> rw [hp]
          · exact h9r2_identityFile_len_le_64 st.party.other
          · exact h9r2_sessionFile_len_le_64 st.party.other
      · by_cases ht3 : t = wirePrekey
        · subst ht3
          rw [runAns_pqRecvPrekey_eq S ⟨W.C, W.Q⟩ st rest rc, hpksm, hdecPk] at ha
          cases hpm : pksmParse rest with
          | none => rw [hpm] at ha; cases ha
          | some pm =>
            rw [hpm] at ha; dsimp only at ha
            obtain ⟨g', _v, hg, rfl, _⟩ := h9r2_finish_inv ha
            have hg_d2c := h9r2_decPkDef_some_some_eq_d2c hg
            obtain ⟨kpkId, opkId, hsub⟩ := decPkDefD2c_namedWrites_sub hg_d2c
            have hlen4 := h9r2_decPkDef_writes_len_le_4 hg
            refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
            rcases hsub q hq with h | h | h | h | h <;> rw [h]
            · exact h9r2_identityFile_len_le_64 st.party.other
            · exact h9r2_sessionFile_len_le_64 st.party.other
            · exact h9r2_oneTimeKyberPreKeyFile_len_le_64 kpkId
            · exact h9r2_baseKeysFile_len_le_64 kpkId
            · exact h9r2_oneTimePreKeyFile_len_le_64 opkId
        · rw [runAns_pqRecvBad S ⟨W.C, W.Q⟩ st (t :: rest) rc
            (fun h => ht2 (Option.some.inj h)) (fun h => ht3 (Option.some.inj h))] at ha
          cases ha

/-- Named-writes domain bounds (`≤ 4` writes, each path `≤ 64` bytes) for `cliRunSemPathB X W` on
`CliPqOrD3RecvInputs ⟨W.C, W.Q⟩`. -/
theorem h9r2_nwDom_pqD3Recv_pathB (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8))
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i)
    (ha : runAns (cliRunSemPathB X W) i = some (some (nw, out))) :
    nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64 :=
  h9r2_nwDom_pqD3Recv rfl rfl rfl rfl rfl i nw out hi ha

/-! ## 2. `hfitCap` Wiring Lemmas (`D3MainEntryBudgetFitsCapDom0` → `H9PathBAssemblyG2`) -/

/-- Specializes `mainEntryBudgetFitsCapOf_pqD3Recv_dom0_of_singleSlot` to `cliRunSemPathB X W`
and `ReadFileRuleEnvFixed cliIo.rd` over `h9r2_honestD3RunSlotEnvs`. -/
theorem h9r2_fitsCap_pathB_of_dom0_singleSlot [LibsignalPlacement]
    {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A' w1R.B w1R.x)
        w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A' w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A' w2R.B w2R.x)
        w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A' w2R.B w2R.x) w2DecSigExactGrpS)
    (S_decPk : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      (cliRunSemPathB X W).pksmParse rest = some pm →
      SingleSlotFineSpec (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm)))
    (hDecPkCaps : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
      (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
      (hc : g.c = .recv peerV)
      (hst : g.i.stdin = 3#8 :: rest)
      (hpk : (cliRunSemPathB X W).pksmParse rest = some pm),
      let sp := S_decPk g meV peerV rest pm hi_g hp hin hc hst hpk
      sp.cum ≤ w4Cum ∧ sp.live ≤ w4Live ∧ sp.peak ≤ w4Peak ∧
      sp.maxReq ≤ w4MaxReq ∧ sp.grpS ≤ w4GrpS)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (h9r2_honestD3RunSlotEnvs EncSlot DecSigSlot W A B DecPkSlotEnv)
        PksmTryFromEnv (cliRunSemPathB X W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) :=
  mainEntryBudgetFitsCapOf_pqD3Recv_dom0_of_singleSlot
    EncSlot DecSigSlot img (cliRunSemPathB X W) X W A B DecPkSlotEnv
    w4Cum w4Live w4Peak w4MaxReq w4GrpS
    (h9r2_nwDom_pqD3Recv_pathB X W)
    hEncCredit hEncGrp hDecSigCredit hDecSigGrp
    S_decPk hDecPkCaps hDecPkLp hFits
    (h9r2_cliRunSemPathB_encrypt_eq X W)

/-- `PhaseCreditSpec` / `PhaseGroupSpec` variant of `h9r2_fitsCap_pathB_of_dom0_singleSlot`. -/
theorem h9r2_fitsCap_pathB_of_dom0 [LibsignalPlacement]
    {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A' w1R.B w1R.x)
        w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A' w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A' w2R.B w2R.x)
        w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A' w2R.B w2R.x) w2DecSigExactGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      (cliRunSemPathB X W).pksmParse rest = some pm →
      PhaseCreditSpec fineCostModel (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm))
        w4Cum w4Live w4Peak w4MaxReq)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hDecPkGrp : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      (cliRunSemPathB X W).pksmParse rest = some pm →
      PhaseGroupSpec fineCostModel (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm))
        w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (h9r2_honestD3RunSlotEnvs EncSlot DecSigSlot W A B DecPkSlotEnv)
        PksmTryFromEnv (cliRunSemPathB X W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) :=
  mainEntryBudgetFitsCapOf_pqD3Recv_dom0
    EncSlot DecSigSlot img (cliRunSemPathB X W) X W A B DecPkSlotEnv
    w4Cum w4Live w4Peak w4MaxReq w4GrpS
    (h9r2_nwDom_pqD3Recv_pathB X W)
    hEncCredit hEncGrp hDecSigCredit hDecSigGrp
    hDecPkCredit hDecPkLp hDecPkGrp hFits
    (h9r2_cliRunSemPathB_encrypt_eq X W)

/-- Cap-parametric `(enc*, decSig*, w4*)` variant of `h9r2_fitsCap_pathB_of_dom0`. -/
theorem h9r2_fitsCap_pathB_of_slot_caps [LibsignalPlacement]
    {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (encCum encLive encPeak encMaxReq encGrpS : Nat)
    (decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS : Nat)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A' w1R.B w1R.x)
        encCum encLive encPeak encMaxReq)
    (hEncLp : encLive ≤ encPeak)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A'.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A' w1R.B w1R.x) encGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A' w2R.B w2R.x)
        decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
      (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A'.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A' w2R.B w2R.x) decSigGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      (cliRunSemPathB X W).pksmParse rest = some pm →
      PhaseCreditSpec fineCostModel (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm))
        w4Cum w4Live w4Peak w4MaxReq)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hDecPkGrp : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      (cliRunSemPathB X W).pksmParse rest = some pm →
      PhaseGroupSpec fineCostModel (DecPkSlotEnv (r3bDecPkGhost g meV peerV pm))
        w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (h9r2_honestD3RunSlotEnvs EncSlot DecSigSlot W A B DecPkSlotEnv)
        PksmTryFromEnv (cliRunSemPathB X W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) :=
  mainEntryBudgetFitsCapOf_pqD3Recv_slot_of_caps
    EncSlot DecSigSlot img (cliRunSemPathB X W) X W A B DecPkSlotEnv
    encCum encLive encPeak encMaxReq encGrpS
    decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
    w4Cum w4Live w4Peak w4MaxReq w4GrpS
    (h9r2_nwDom_pqD3Recv_pathB X W)
    hEncCredit hEncLp hEncGrp hDecSigCredit hDecSigLp hDecSigGrp
    hDecPkCredit hDecPkLp hDecPkGrp hFits
    (h9r2_cliRunSemPathB_encrypt_eq X W)

/-- Produces the multi-placement `MainEntryBudgetFitsCapOf` hypothesis required by
`H9PathBAssemblyG2` over `h9r2_honestD3FineSlotEnvs`. -/
theorem h9r2_hfitCap_pathB_of_dom0_singleSlot
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {brkStart : BitVec 64}
    (img : Image)
    (EncSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (B : RunBudgets)
    (DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hEncCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseCreditSpec fineCostModel (EncSlot W A' w1R.B w1R.x)
          w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseGroupSpec fineCostModel (EncSlot W A' w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseCreditSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x)
          w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseGroupSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x) w2DecSigExactGrpS)
    (S_decPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        (cliRunSemPathB X W).pksmParse rest = some pm →
        SingleSlotFineSpec (DecPkSlotEnv X W γ tp (r3bDecPkGhost g meV peerV pm)))
    (hDecPkCaps : ∀ (h547 : mpl.base 547 ≠ 0#64)
      (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
      (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
      (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
      (hc : g.c = .recv peerV)
      (hst : g.i.stdin = 3#8 :: rest)
      (hpk : (cliRunSemPathB X W).pksmParse rest = some pm),
      let sp := S_decPk h547 X W γ tp g meV peerV rest pm hi_g hp hin hc hst hpk
      sp.cum ≤ w4Cum ∧ sp.live ≤ w4Live ∧ sp.peak ≤ w4Peak ∧
      sp.maxReq ≤ w4MaxReq ∧ sp.grpS ≤ w4GrpS)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
          (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B
              DecPkSlotEnv X W γ tp)
            PksmTryFromEnv (cliRunSemPathB X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) :=
  fun h547 X W γ tp => by
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    exact h9r2_fitsCap_pathB_of_dom0_singleSlot
      (fun {_M'} A' B' => EncSlot W A' B')
      (fun {_M'} A' B' => DecSigSlot W A' B') img X W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
      (DecPkSlotEnv X W γ tp)
      w4Cum w4Live w4Peak w4MaxReq w4GrpS
      (hEncCredit h547 W) (hEncGrp h547 W)
      (hDecSigCredit h547 W) (hDecSigGrp h547 W)
      (S_decPk h547 X W γ tp) (hDecPkCaps h547 X W γ tp)
      hDecPkLp hFits

theorem h9r2_hfitCap_pathB_of_dom0
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {brkStart : BitVec 64}
    (img : Image)
    (EncSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (B : RunBudgets)
    (DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hEncCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseCreditSpec fineCostModel (EncSlot W A' w1R.B w1R.x)
          w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseGroupSpec fineCostModel (EncSlot W A' w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseCreditSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x)
          w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseGroupSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x) w2DecSigExactGrpS)
    (hDecPkCredit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        (cliRunSemPathB X W).pksmParse rest = some pm →
        PhaseCreditSpec fineCostModel (DecPkSlotEnv X W γ tp (r3bDecPkGhost g meV peerV pm))
          w4Cum w4Live w4Peak w4MaxReq)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hDecPkGrp : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        (cliRunSemPathB X W).pksmParse rest = some pm →
        PhaseGroupSpec fineCostModel (DecPkSlotEnv X W γ tp (r3bDecPkGhost g meV peerV pm))
          w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
          (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B
              DecPkSlotEnv X W γ tp)
            PksmTryFromEnv (cliRunSemPathB X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) :=
  fun h547 X W γ tp => by
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    exact h9r2_fitsCap_pathB_of_dom0
      (fun {_M'} A' B' => EncSlot W A' B')
      (fun {_M'} A' B' => DecSigSlot W A' B') img X W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
      (DecPkSlotEnv X W γ tp)
      w4Cum w4Live w4Peak w4MaxReq w4GrpS
      (hEncCredit h547 W) (hEncGrp h547 W)
      (hDecSigCredit h547 W) (hDecSigGrp h547 W)
      (hDecPkCredit h547 X W γ tp) hDecPkLp (hDecPkGrp h547 X W γ tp) hFits

/-- Cap-parametric `(enc*, decSig*, w4*)` variant of `h9r2_hfitCap_pathB_of_dom0`. -/
theorem h9r2_hfitCap_pathB_of_slot_caps
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    {brkStart : BitVec 64}
    (img : Image)
    (EncSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (B : RunBudgets)
    (DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    (encCum encLive encPeak encMaxReq encGrpS : Nat)
    (decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS : Nat)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hEncCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseCreditSpec fineCostModel (EncSlot W A' w1R.B w1R.x)
          encCum encLive encPeak encMaxReq)
    (hEncLp : encLive ≤ encPeak)
    (hEncGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseGroupSpec fineCostModel (EncSlot W A' w1R.B w1R.x) encGrpS)
    (hDecSigCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseCreditSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x)
          decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hDecSigGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseGroupSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x) decSigGrpS)
    (hDecPkCredit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        (cliRunSemPathB X W).pksmParse rest = some pm →
        PhaseCreditSpec fineCostModel (DecPkSlotEnv X W γ tp (r3bDecPkGhost g meV peerV pm))
          w4Cum w4Live w4Peak w4MaxReq)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hDecPkGrp : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        (cliRunSemPathB X W).pksmParse rest = some pm →
        PhaseGroupSpec fineCostModel (DecPkSlotEnv X W γ tp (r3bDecPkGhost g meV peerV pm))
          w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
          (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
          (RunEnv (cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B
              DecPkSlotEnv X W γ tp)
            PksmTryFromEnv (cliRunSemPathB X W)))
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) :=
  fun h547 X W γ tp => by
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    exact h9r2_fitsCap_pathB_of_slot_caps
      (fun {_M'} A' B' => EncSlot W A' B')
      (fun {_M'} A' B' => DecSigSlot W A' B') img X W
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
      (DecPkSlotEnv X W γ tp)
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS
      (hEncCredit h547 W) hEncLp (hEncGrp h547 W)
      (hDecSigCredit h547 W) hDecSigLp (hDecSigGrp h547 W)
      (hDecPkCredit h547 X W γ tp) hDecPkLp (hDecPkGrp h547 X W γ tp) hFits

/-! ## 3. End-to-End `MainOkPathBD3F3` Assemblers -/

/-- Composes `h9g_pathB_assembly_of_fitsCap` over `h9r2_honestD3FineSlotEnvs` with
`h9r2_initEnv_r1c_congr` and `h9r2_hfitCap_pathB_of_dom0_singleSlot`. -/
theorem h9r2_pathB_assembly_honest_of_dom0_singleSlot
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hFullPl : libsignalSessionLib.Placeable mpl)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (EncSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (B : RunBudgets)
    (DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle
        (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (henc_addr : ∀ W γ tp g peerV peerG meG fsp,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      peerG.val = addrValOf peerV →
      EncSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r2EncGhost g peerG meG fsp) =
        EncSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ W γ tp g fsp w peerV meG msgG m,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      DecSigSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        DecSigSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r3aDecSigGhost0 g peerV meG m))
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      DecPkSlotEnv X W γ tp x = DecPkSlotEnv X W γ tp y)
    (henc : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B
            DecPkSlotEnv X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).encrypt.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hdecSig : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B
            DecPkSlotEnv X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).decryptSignal.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hinit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B
            DecPkSlotEnv X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).initiate.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521))
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B
            DecPkSlotEnv X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hEncCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseCreditSpec fineCostModel (EncSlot W A' w1R.B w1R.x)
          w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseGroupSpec fineCostModel (EncSlot W A' w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseCreditSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x)
          w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseGroupSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x) w2DecSigExactGrpS)
    (S_decPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        (cliRunSemPathB X W).pksmParse rest = some pm →
        SingleSlotFineSpec (DecPkSlotEnv X W γ tp (r3bDecPkGhost g meV peerV pm)))
    (hDecPkCaps : ∀ (h547 : mpl.base 547 ≠ 0#64)
      (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
      (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
      (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
      (hc : g.c = .recv peerV)
      (hst : g.i.stdin = 3#8 :: rest)
      (hpk : (cliRunSemPathB X W).pksmParse rest = some pm),
      let sp := S_decPk h547 X W γ tp g meV peerV rest pm hi_g hp hin hc hst hpk
      sp.cum ≤ w4Cum ∧ sp.live ≤ w4Live ∧ sp.peak ≤ w4Peak ∧
      sp.maxReq ≤ w4MaxReq ∧ sp.grpS ≤ w4GrpS)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainOkPathBD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h9g_pathB_assembly_of_fitsCap hblk hext_nodup hFullPl ghFixed
    (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B DecPkSlotEnv)
    hlibc hTr hG hioOf hstk hHooks
    (fun _X W _γ _tp g d2 fsp => h9r2_initEnv_r1c_congr W g d2 fsp)
    (fun _X W γ tp g peerV peerG meG fsp hp => henc_addr W γ tp g peerV peerG meG fsp hp)
    (fun _X W γ tp g fsp w peerV meG msgG m => hdec_ghost W γ tp g fsp w peerV meG msgG m)
    hdp_ghost
    henc hdecSig hinit hdecPkNeed hdecPk
    (h9r2_hfitCap_pathB_of_dom0_singleSlot hblk hext_nodup img EncSlot DecSigSlot B DecPkSlotEnv
      w4Cum w4Live w4Peak w4MaxReq w4GrpS
      hEncCredit hEncGrp hDecSigCredit hDecSigGrp S_decPk hDecPkCaps hDecPkLp hFits)

/-- Composes `h9g_pathB_assembly_of_d2cSlots_and_fitsCap` over `h9r2_honestD3FineSlotEnvs` with
`h9r2_initEnv_r1c_congr` and `h9r2_hfitCap_pathB_of_dom0_singleSlot`. -/
theorem h9r2_pathB_assembly_honest_d2cSlots_of_dom0_singleSlot
    {elfBytes : List (BitVec 8)} {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt elfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (EncSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (B : RunBudgets)
    (DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle
        (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (henc_addr : ∀ W γ tp g peerV peerG meG fsp,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      peerG.val = addrValOf peerV →
      EncSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r2EncGhost g peerG meG fsp) =
        EncSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ W γ tp g fsp w peerV meG msgG m,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      DecSigSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        DecSigSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r3aDecSigGhost0 g peerV meG m))
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      DecPkSlotEnv X W γ tp x = DecPkSlotEnv X W γ tp y)
    (hW1 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (encSlotSpecPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (EncSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds decPkNeed).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hW2 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (decSigSlotSpecFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (DecSigSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds decPkNeed).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hW3 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliInitSlotOkPlaced mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (realCliInitBinarySlotEnvFixed W) X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B
            DecPkSlotEnv X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hEncCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseCreditSpec fineCostModel (EncSlot W A' w1R.B w1R.x)
          w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseGroupSpec fineCostModel (EncSlot W A' w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseCreditSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x)
          w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseGroupSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x) w2DecSigExactGrpS)
    (S_decPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        (cliRunSemPathB X W).pksmParse rest = some pm →
        SingleSlotFineSpec (DecPkSlotEnv X W γ tp (r3bDecPkGhost g meV peerV pm)))
    (hDecPkCaps : ∀ (h547 : mpl.base 547 ≠ 0#64)
      (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
      (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
      (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
      (hc : g.c = .recv peerV)
      (hst : g.i.stdin = 3#8 :: rest)
      (hpk : (cliRunSemPathB X W).pksmParse rest = some pm),
      let sp := S_decPk h547 X W γ tp g meV peerV rest pm hi_g hp hin hc hst hpk
      sp.cum ≤ w4Cum ∧ sp.live ≤ w4Live ∧ sp.peak ≤ w4Peak ∧
      sp.maxReq ≤ w4MaxReq ∧ sp.grpS ≤ w4GrpS)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hFits : d3SlotMainFitsOneGiBOf
      w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq w1EncExactGrpS
      w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq w2DecSigExactGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainOkPathBD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h9g_pathB_assembly_of_d2cSlots_and_fitsCap hLs hblk hext_nodup ghFixed
    (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B DecPkSlotEnv)
    realCliInitBinarySlotEnvFixed
    hlibc hTr hG hioOf hstk hHooks
    (fun _X _W _γ _tp => rfl)
    (fun _X W _γ _tp g d2 fsp => h9r2_initEnv_r1c_congr W g d2 fsp)
    (fun _X W γ tp g peerV peerG meG fsp hp => henc_addr W γ tp g peerV peerG meG fsp hp)
    (fun _X W γ tp g fsp w peerV meG msgG m => hdec_ghost W γ tp g fsp w peerV meG msgG m)
    hdp_ghost
    hW1 hW2 hW3 hdecPkNeed hdecPk
    (h9r2_hfitCap_pathB_of_dom0_singleSlot hblk hext_nodup img EncSlot DecSigSlot B DecPkSlotEnv
      w4Cum w4Live w4Peak w4MaxReq w4GrpS
      hEncCredit hEncGrp hDecSigCredit hDecSigGrp S_decPk hDecPkCaps hDecPkLp hFits)

/-- Cap-parametric `(enc*, decSig*, w4*)` variant of `h9r2_pathB_assembly_honest_d2cSlots_of_dom0_singleSlot`. -/
theorem h9r2_pathB_assembly_honest_d2cSlots_of_slot_caps
    {elfBytes : List (BitVec 8)} {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt elfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    {CodeOk_real : Memory → Prop}
    {libcAddr brkStart : BitVec 64} {hookStack : Nat}
    (img : Image)
    (EncSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ [LibsignalPlacement] {M' : AllocCostModel},
      CliHooks → RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (B : RunBudgets)
    (DecPkSlotEnv : UnreachedPqxdhPrimitives → CliHooks → GhostName → BitVec 64 →
      DecPkGhost → List AllocEvent → Prop)
    {decPkNeed : Nat}
    (encCum encLive encPeak encMaxReq encGrpS : Nat)
    (decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS : Nat)
    (w4Cum w4Live w4Peak w4MaxReq w4GrpS : Nat)
    (hlibc : libcAddr = (mallocngAddrsOfPlacement mmpl).libc)
    (hTr : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) CodeOk_real libcAddr brkStart cliMainStk)
    (hG : ∀ (γ : GhostName) (tp : BitVec 64),
      @CliGhostAllocHooks (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart)
        cliBudgetLimits ghFixed)
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hstk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk := by decide)
    (hHooks : mpl.base 547 ≠ 0#64 → ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle
        (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W _
        (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (henc_addr : ∀ W γ tp g peerV peerG meG fsp,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      peerG.val = addrValOf peerV →
      EncSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r2EncGhost g peerG meG fsp) =
        EncSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64))
    (hdec_ghost : ∀ W γ tp g fsp w peerV meG msgG m,
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      DecSigSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        DecSigSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B
          (r3aDecSigGhost0 g peerV meG m))
    (hdp_ghost : ∀ X W γ tp (x y : DecPkGhost),
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      DecPkSlotEnv X W γ tp x = DecPkSlotEnv X W γ tp y)
    (hW1 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (encSlotSpecPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (EncSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds decPkNeed).encrypt).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464))
    (hW2 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (mkSlot
          (decSigSlotSpecFrozenPlaced
            (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
            (DecSigSlot W (fineHookRustCliAllocBudget γ mmpl tp brkStart) B)
            (cliRunSemD2c_placed X W))
          (cliRunNeeds decPkNeed).decryptSignal).OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463))
    (hW3 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliInitSlotOkPlaced mmpl ghFixed
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (realCliInitBinarySlotEnvFixed W) X W)
    (hdecPkNeed : decPkNeed ≤ 4194304)
    (hdecPk : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        (slotsOfSigPkFrozenPlaced
          (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliBudgetLimits
          (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B
            DecPkSlotEnv X W γ tp)
          (cliRunSemPathB X W) (cliRunNeeds decPkNeed)).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520))
    (hEncCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseCreditSpec fineCostModel (EncSlot W A' w1R.B w1R.x)
          encCum encLive encPeak encMaxReq)
    (hEncLp : encLive ≤ encPeak)
    (hEncGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w1R : W1BinarySendParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
        g.c = .send peerV →
        w1R.repAlloc = A'.repAlloc →
        W1BinarySendDom (.send peerV) g.i w1R →
        PhaseGroupSpec fineCostModel (EncSlot W A' w1R.B w1R.x) encGrpS)
    (hDecSigCredit : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseCreditSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x)
          decSigCum decSigLive decSigPeak decSigMaxReq)
    (hDecSigLp : decSigLive ≤ decSigPeak)
    (hDecSigGrp : mpl.base 547 ≠ 0#64 →
      ∀ (W : CliHooks) (g : RunCall) (peerV : AddrV) (M' : AllocCostModel)
        (A' : RustCliAllocBudget M') (w2R : W2BinaryWhisperParams),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        g.c = .recv peerV →
        w2R.repAlloc = A'.repAlloc →
        W2BinaryWhisperDom (.recv peerV) g.i w2R →
        PhaseGroupSpec fineCostModel (DecSigSlot W A' w2R.B w2R.x) decSigGrpS)
    (hDecPkCredit : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        (cliRunSemPathB X W).pksmParse rest = some pm →
        PhaseCreditSpec fineCostModel (DecPkSlotEnv X W γ tp (r3bDecPkGhost g meV peerV pm))
          w4Cum w4Live w4Peak w4MaxReq)
    (hDecPkLp : w4Live ≤ w4Peak)
    (hDecPkGrp : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
        (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
        parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
        (inputOf g.i g.c).length ≤ stdinCapBytes →
        g.c = .recv peerV →
        g.i.stdin = 3#8 :: rest →
        (cliRunSemPathB X W).pksmParse rest = some pm →
        PhaseGroupSpec fineCostModel (DecPkSlotEnv X W γ tp (r3bDecPkGhost g meV peerV pm))
          w4GrpS)
    (hFits : d3SlotMainFitsOneGiBOf
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS) :
    MainOkPathBD3F3 mpl mmpl CodeOk_real libcAddr brkStart cliMainStk :=
  h9g_pathB_assembly_of_d2cSlots_and_fitsCap hLs hblk hext_nodup ghFixed
    (h9r2_honestD3FineSlotEnvs hblk hext_nodup EncSlot DecSigSlot mmpl brkStart B DecPkSlotEnv)
    realCliInitBinarySlotEnvFixed
    hlibc hTr hG hioOf hstk hHooks
    (fun _X _W _γ _tp => rfl)
    (fun _X W _γ _tp g d2 fsp => h9r2_initEnv_r1c_congr W g d2 fsp)
    (fun _X W γ tp g peerV peerG meG fsp hp => henc_addr W γ tp g peerV peerG meG fsp hp)
    (fun _X W γ tp g fsp w peerV meG msgG m => hdec_ghost W γ tp g fsp w peerV meG msgG m)
    hdp_ghost
    hW1 hW2 hW3 hdecPkNeed hdecPk
    (h9r2_hfitCap_pathB_of_slot_caps hblk hext_nodup img EncSlot DecSigSlot B DecPkSlotEnv
      encCum encLive encPeak encMaxReq encGrpS
      decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
      w4Cum w4Live w4Peak w4MaxReq w4GrpS
      hEncCredit hEncLp hEncGrp hDecSigCredit hDecSigLp hDecSigGrp
      hDecPkCredit hDecPkLp hDecPkGrp hFits)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2
