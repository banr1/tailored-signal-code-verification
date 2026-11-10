/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser

/-!
# Witness-Free Existential Real CLI Callee Envelopes

Constructs the mode-dispatched guarded-existential `CliRunCalleeEnvs` bundle
`mkExistentialRealCalleeEnvs` and its `CliRealCalleeFineSpecs` witness `existentialRealCalleeFineSpecs`
using `CliPqxdhInputs` and `cliIo_rd_ok_length_le_sessionCapBytes` (`bs.length ≤ 2 MiB` from
`IoHooks.readViewF`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliPqxdhInputs Inputs fileCapBytes)
open CryptoVerification.SignalSession.Cli (ReadRule StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.KitInst
  (cliIdentityStoreSpec cliIdentityVtRoSym cliSessionStoreSpec cliSessionVtRoSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliRd parseArgs readViewF)
open CryptoVerification.SignalSession.Cli.RunCompose ( InitGhost RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (phaseGroupSpec_exists_guarded w3InitiateSlotEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec (CliMainEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs CliRunOpenedEnv)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (CliPqRealCallDomain CliRealCalleeFineSpecs cliPqRealCallDomain_recvPrekey_nonvacuous
   cliRun1MiBCustomPksmCum cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmMaxReq
   cliRun1MiBCustomPksmPeak cliRunOpenedCustomPksmGrpS emptyPhaseCreditSpec emptyPhaseGroupSpec
   recordSerializeCancelEnv_aliceInitiated_fine_groupSpec w3InitRealCum w3InitRealGrpS
   w3InitRealLive w3InitRealMaxReq w3InitRealPeak w3InitReal_caps_le)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec (CliAddrTextEnv CliDirGetEnv CliDirPutEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (CliSessLoadPollEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers
  (w2CliDecryptSlot_polls_cliPqInputs_fine_creditSpec)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (W1SendRealDom W1SendRealParams W1SendRealSlotEnv peer_and_rem_name_le_40_of_send
   w1SendRealDcanCum w1SendRealDcanGrpS w1SendRealDcanLive w1SendRealDcanMaxReq w1SendRealDcanPeak
   w1SendRealDcan_live_le_peak w1SendReal_singleSlotFineSpec_of_rdBounded)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (W2RealRecordSerEnv W2RealTdEnv W2RecvWhisperRealDom W2RecvWhisperRealParams
   W2RecvWhisperRealSlotEnv idPeers_rd_length_le_64_of_cliPqInputs_recv
   peer_and_rem_name_le_40_of_recv w2CliDecryptSlot_polls_cliPqInputs_linked_fine_groupSpec
   w2RealIdentityKitEnv w2RealSessionKitEnv w2RealTd_phaseCredit w2Real_hStoreEq
   w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanGrpS w2RecvWhisperRealDcanLive
   w2RecvWhisperRealDcanMaxReq w2RecvWhisperRealDcanPeak w2RecvWhisperRealDcan_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec (W3InitiateSlotEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
  (RecordAliceInitiatedAnyCkBounds mkW3InitiateSlotParamsDeser
   recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820
   recordSerializeTightCum_aliceInitiatedAnyCk_le_32485
   w3InitiateSlotTightDeltaCum_sessionCap_eq w3InitiateSlotTightDeltaLive
   w3InitiateSlotTightDeltaPeak w3InitiateSlotTightMaxReq w3InitiateSlotTight_real192_eq
   w3InitiateSlot_opened_tight_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4RecvPrekeyRealEnv W4RecvPrekeyRealParams w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4RecvPrekeyRealDomOf cliRealDirectRunCum_i cliRealDirectRunGrpS_i cliRealDirectRunLive_i
   cliRealDirectRunMaxReq_i cliRealDirectRunPeak_i w4RecvPrekeyReal1MiB_i_Cum
   w4RecvPrekeyReal1MiB_i_Live w4RecvPrekeyReal1MiB_i_MaxReq w4RecvPrekeyReal1MiB_i_Peak
   w4RecvPrekeyReal1MiB_i_eq w4RecvPrekeyReal1MiB_i_singleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (PksmCanonSliceEnv pksmCanonSliceCum pksmCanonSliceGrpS pksmCanonSliceLive
   pksmCanonSliceLive_le_peak pksmCanonSliceMaxReq pksmCanonSlicePeak
   pksmCanonSlice_fine_groupSpec pksmCanonSlice_fine_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (RecordDeserializeCancelEnv deserCancelFineCum deserCancelFineGrpS deserCancelFineLive
   deserCancelFineMaxReq deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (ofBytesEnv w2_hLoadEq_of_cliSessionKitBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (recordTryDecryptEnvArgs)

/-! ## Guarded Existential Credit and `cliIo.rd` `2 MiB` Cap -/

private theorem phaseCredit_exists_guarded_u {α : Sort _} {M : AllocCostModel}
    [HasFineReallocCredit M] {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ x, P x → PhaseCreditSpec M (E x) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ x, P x ∧ E x evs) c l p r where
  req_align evs := fun ⟨x, hx, he⟩ => (h x hx).req_align evs he
  credit_le st0 := fun ⟨x, hx, he⟩ => (h x hx).credit_le st0 he

/-- Every successful `cliIo.rd F path = .ok bs` lookup satisfies `bs.length ≤ sessionCapBytes`
(`IoHooks.readViewF` enforces `bs.length ≤ fileCapBytes`). -/
theorem cliIo_rd_ok_length_le_sessionCapBytes (F : FsFiles) (path bs : List (BitVec 8))
    (hrd : cliIo.rd F path = .ok bs) : bs.length ≤ sessionCapBytes := by
  change cliRd F path = .ok bs at hrd
  unfold cliRd at hrd
  split at hrd
  · cases hrd
  · rename_i rbs hrv
    injection hrd with h
    subst h
    unfold readViewF at hrv
    split at hrv
    · cases hrv
    · injection hrv with h
      subst h
      exact Nat.zero_le _
    · split at hrv
      · split at hrv
        · rename_i hle
          injection hrv with h
          subst h
          exact Nat.le_trans hle (by unfold fileCapBytes sessionCapBytes; decide)
        · cases hrv
      · cases hrv
      · injection hrv with h
        subst h
        exact Nat.zero_le _

/-! ## Real Slot Specs for `W1` (`send`) and `W2` (`recv` Whisper) -/

/-- `SingleSlotFineSpec` for `W1SendRealSlotEnv`, discharging the session file-size cap via
`cliIo_rd_ok_length_le_sessionCapBytes`. -/
def w1SendRealSlot_dcan_singleSlotFineSpec_noFb
    {img : Arm64.Obj.Image} {W : PEParams} {i : Inputs} {peerAddr : AddrV}
    (R : W1SendRealParams)
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.send peerAddr))
    (hdom : W1SendRealDom (.send peerAddr) R) :
    SingleSlotFineSpec (W1SendRealSlotEnv img W i R) :=
  let h := hdom peerAddr rfl
  let hn := peer_and_rem_name_le_40_of_send hparse h.1 h.2.1
  let S := w1SendReal_singleSlotFineSpec_of_rdBounded (B := R.B) (img := img)
    RecordDeserializeCancelEnv
    deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq
    deserCancelFineGrpS
    hi hparse h.2.2
    (fun p bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles i) p bs hrd)
    h.1 h.2.1 hn.1 hn.2
    (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
    (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs)
  { cum := w1SendRealDcanCum
    live := w1SendRealDcanLive
    peak := w1SendRealDcanPeak
    maxReq := w1SendRealDcanMaxReq
    grpS := w1SendRealDcanGrpS
    credit := S.credit_spec
    live_le_peak := S.live_le_peak
    groups := S.group_spec }

theorem w2Real_hLoadEq_noFb [LibsignalPlacement] {A : RustAlloc}
    {i : Inputs} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {x : DecryptGhost}
    {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hrem : x.rem.val = peer.val) :
    ∀ evs,
      (w2RealSessionKitEnv A (runFiles i) pathOk peer s1 s2 s3 s4 DeserEnv).loadPollEnv
        StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv (runFiles i) StoresGhost.opened.sessions peer evs :=
  w2_hLoadEq_of_cliSessionKitBudgetEnv
    (A := A) (F := runFiles i) (pathOk := pathOk) (Scope := scopeKit) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (fileCap := sessionCapBytes)
    (vtSym := cliSessionVtRoSym) (idVtSym := cliIdentityVtRoSym)
    (AddrValEnv := fun _ => CliAddrTextEnv peer)
    (GetEnv := CliDirGetEnv (ReadFileRuleEnv cliIo.rd))
    (DeserEnv := ofBytesEnv DeserEnv)
    (SerValEnv := W2RealRecordSerEnv)
    (PutEnv := fun d _ _ => SeqEnv (CliDirPutEnv d [] []) FreeOnlyEvs)
    (DeserByBytesEnv := DeserEnv)
    (rem := x.rem.val)
    hrem (by decide : sessionCapBytes ≤ 2097152)
    (fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles i)
      (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) bs hrd)
    (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)

/-- `SingleSlotFineSpec` for `W2RecvWhisperRealSlotEnv`, discharging the session file-size cap via
`cliIo_rd_ok_length_le_sessionCapBytes`. -/
def w2RecvWhisperRealSlot_dcan_singleSlotFineSpec_noFb [LibsignalPlacement]
    {W : PEParams} {i : Inputs} {peerAddr : AddrV}
    (R : W2RecvWhisperRealParams)
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hdom : W2RecvWhisperRealDom (.recv peerAddr) R) :
    SingleSlotFineSpec (W2RecvWhisperRealSlotEnv W i R) where
  cum := w2RecvWhisperRealDcanCum
  live := w2RecvWhisperRealDcanLive
  peak := w2RecvWhisperRealDcanPeak
  maxReq := w2RecvWhisperRealDcanMaxReq
  grpS := w2RecvWhisperRealDcanGrpS
  credit := by
    obtain ⟨hpeerAddr, hrem, hct⟩ := hdom peerAddr rfl
    obtain ⟨hpeer, hremName, hidKeyLen⟩ := peer_and_rem_name_le_40_of_recv hparse hpeerAddr hrem
    exact w2CliDecryptSlot_polls_cliPqInputs_fine_creditSpec
      R.pathOk R.peer R.s1 R.s2 R.s3 R.s4 R.t1 R.t2 R.t3 R.t4
      R.parse R.x RecordDeserializeCancelEnv R.peer.name.bytes
      (w2RealSessionKitEnv R.A (runFiles i) R.pathOk R.peer R.s1 R.s2 R.s3 R.s4
        RecordDeserializeCancelEnv)
      (w2RealIdentityKitEnv (A := R.A) (runFiles i) R.pathOk R.peer R.t1 R.t2 R.t3 R.t4)
      (W2RealTdEnv W.C.F W.Q.K)
      hi hparse hpeerAddr hrem hpeer hremName hidKeyLen
      (fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles i)
        (pathOf StoresGhost.opened.sessions.path (addressText R.peer.val)) bs hrd)
      (idPeers_rd_length_le_64_of_cliPqInputs_recv hi hparse hpeerAddr)
      (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
      (w2Real_hLoadEq_noFb hrem) (fun _ _ h => h) (fun _ _ h => h)
      (fun rec' evs _ hst => w2Real_hStoreEq rec' evs hst)
      (fun _rec ses G G₁ _hIn _hcur _hgv _hDom _hRel hTop _hVe _hVcp _hPqLt31 _hPqFile =>
        w2RealTd_phaseCredit W.C.F W.Q.K
          (recordTryDecryptEnvArgs (recGhostOf R.x 0#64 G ses.state) G₁) hTop hct)
  live_le_peak := w2RecvWhisperRealDcan_live_le_peak
  groups := by
    obtain ⟨hpeerAddr, hrem, _⟩ := hdom peerAddr rfl
    exact w2CliDecryptSlot_polls_cliPqInputs_linked_fine_groupSpec
      R.pathOk R.peer R.s1 R.s2 R.s3 R.s4 R.t1 R.t2 R.t3 R.t4
      R.parse R.x RecordDeserializeCancelEnv R.peer.name.bytes
      (w2RealSessionKitEnv R.A (runFiles i) R.pathOk R.peer R.s1 R.s2 R.s3 R.s4
        RecordDeserializeCancelEnv)
      (w2RealIdentityKitEnv (A := R.A) (runFiles i) R.pathOk R.peer R.t1 R.t2 R.t3 R.t4)
      hi hparse hpeerAddr hrem
      (fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles i)
        (pathOf StoresGhost.opened.sessions.path (addressText R.peer.val)) bs hrd)
      (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs)
      (w2Real_hLoadEq_noFb hrem) (fun _ _ h => h) (fun _ _ h => h)
      (fun rec' evs _ hst => w2Real_hStoreEq rec' evs hst)

/-! ## Mode-Dispatched Guarded-Existential Real Callee Envelopes -/

/-- Concrete `W3` (`init`) `SingleSlotFineSpec` at `RecordDeserializeCancelEnv`. -/
def w3InitReal_singleSlotFineSpec_noA0
    {x : InitGhost}
    (hpeer : x.peer.name.bytes.length ≤ 40)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    (F : ShaCompress)
    {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost}
    {r_rec : SessionRecord (List (BitVec 8))}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ sessionCapBytes)
    (halice : RecordAliceInitiatedAnyCkBounds g_rec r_rec) :
    SingleSlotFineSpec
      (W3InitiateSlotEnv
        (mkW3InitiateSlotParamsDeser rd RecordDeserializeCancelEnv
          x ownKeyName ownRegName F x_spqr g_rec r_rec)) where
  cum := w3InitRealCum
  live := w3InitRealLive
  peak := w3InitRealPeak
  maxReq := w3InitRealMaxReq
  grpS := w3InitRealGrpS
  credit := by
    have h0 := w3InitiateSlot_opened_tight_phaseCredit
      (mkW3InitiateSlotParamsDeser rd RecordDeserializeCancelEnv
        x ownKeyName ownRegName F x_spqr g_rec r_rec)
      rfl rfl rfl hpeer hkeyName hregName hspqrKey hfileCap
      (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
      (recordSerializeTightCum_aliceInitiatedAnyCk_le_32485 halice)
      (recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820 halice)
      (by decide)
    have hcr : PhaseCreditSpec fineCostModel
        (W3InitiateSlotEnv
          (mkW3InitiateSlotParamsDeser rd RecordDeserializeCancelEnv
            x ownKeyName ownRegName F x_spqr g_rec r_rec))
        (7874410 + deserCancelFineCum)
        (w3InitiateSlotTightDeltaLive sessionCapBytes 0 deserCancelFineLive 0)
        (w3InitiateSlotTightDeltaPeak sessionCapBytes 0 deserCancelFineLive deserCancelFinePeak 0)
        (w3InitiateSlotTightMaxReq sessionCapBytes 0 deserCancelFineMaxReq 3820) := by
      refine h0.mono ?_ (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      rw [w3InitiateSlotTightDeltaCum_sessionCap_eq]
      omega
    obtain ⟨_, _, hlive, hpeak, hreq, _⟩ := w3InitiateSlotTight_real192_eq
    dsimp only [deserCancelFineLive, deserCancelFinePeak, deserCancelFineMaxReq] at hcr
    rw [hlive, hpeak, hreq] at hcr
    exact hcr
  live_le_peak := w3InitReal_caps_le.2.2.1
  groups :=
    w3InitiateSlotEnv_groupSpec fineCostModel
      (mkW3InitiateSlotParamsDeser rd RecordDeserializeCancelEnv
        x ownKeyName ownRegName F x_spqr g_rec r_rec)
      (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs)
      (recordSerializeCancelEnv_aliceInitiated_fine_groupSpec halice)

/-- Call-site parameter bundle for the `W3` (`init`) slot (`W3InitiateSlotEnv` at `RecordDeserializeCancelEnv`). -/
structure W3InitRealParams where
  rd : ReadRule
  x : InitGhost
  ownKeyName : List (BitVec 8)
  ownRegName : List (BitVec 8)
  F : ShaCompress
  x_spqr : InitialStateGhost
  g_rec : RecordGhost
  r_rec : SessionRecord (List (BitVec 8))

/-- Call-site domain guard for `W3InitRealParams` on `.init peerV dir` (`peer.name ≤ 40`,
key/registration/SPQR bounds, `2 MiB` read cap, and `RecordAliceInitiatedAnyCkBounds`). -/
def W3InitRealDom
    (_img : Arm64.Obj.Image) (_S : RunSem) (g : RunCall) (w : W3InitRealParams) : Prop :=
  (∀ peerV dir, g.c = .init peerV dir → w.x.peer.name.bytes.length ≤ 40) ∧
  w.ownKeyName.length ≤ 64 ∧
  w.ownRegName.length ≤ 64 ∧
  w.x_spqr.p.authKey.length ≤ 32 ∧
  (∀ p bs, w.rd w.x.F p = .ok bs → bs.length ≤ sessionCapBytes) ∧
  RecordAliceInitiatedAnyCkBounds w.g_rec w.r_rec

/-- Concrete `W3` (`init`) slot envelope at `W3InitRealParams`. -/
def W3InitRealSlotEnv (w : W3InitRealParams) (evs : List AllocEvent) : Prop :=
  W3InitiateSlotEnv
    (mkW3InitiateSlotParamsDeser w.rd RecordDeserializeCancelEnv
      w.x w.ownKeyName w.ownRegName w.F w.x_spqr w.g_rec w.r_rec)
    evs

/-- Mode-dispatched `CliRunCalleeEnvs` bundle quantifying existentially over guarded call-site
witnesses across all five CLI callee slots (`init`, `send`, `recv` whisper, `PKSM`, `recv-prekey`). -/
def mkExistentialRealCalleeEnvs [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (P : PEParams) (g : RunCall) :
    CliRunCalleeEnvs where
  initEnv := match g.c with
    | .init _ _ => fun evs =>
      ∃ w : W3InitRealParams, W3InitRealDom img S g w ∧ W3InitRealSlotEnv w evs
    | _ => fun _ => False
  encEnv := match g.c with
    | .send _ => fun evs =>
      ∃ w1R : W1SendRealParams, W1SendRealDom g.c w1R ∧ W1SendRealSlotEnv img P g.i w1R evs
    | _ => fun _ => False
  decSigEnv := match g.c with
    | .recv _ => fun evs =>
      ∃ w2R : W2RecvWhisperRealParams,
        W2RecvWhisperRealDom g.c w2R ∧ W2RecvWhisperRealSlotEnv P g.i w2R evs
    | _ => fun _ => False
  pksmEnv := PksmCanonSliceEnv
  decPkEnv := match g.c with
    | .recv _ => fun evs =>
      ∃ w4R : W4RecvPrekeyRealParams,
        W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w4R ∧ W4RecvPrekeyRealEnv w4R evs
    | _ => fun _ => False

theorem existentialW3_credit [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (P : PEParams) (g : RunCall) :
    PhaseCreditSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).initEnv
      w3InitRealCum w3InitRealLive w3InitRealPeak w3InitRealMaxReq := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseCreditSpec _ _ _ _
  · rename_i peerV dir
    exact phaseCredit_exists_guarded_u fun w hw =>
      (w3InitReal_singleSlotFineSpec_noA0 (hw.1 peerV dir rfl) w.F
        hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1 hw.2.2.2.2.2).credit
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _

theorem existentialW3_groups [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (P : PEParams) (g : RunCall) :
    PhaseGroupSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).initEnv
      w3InitRealGrpS := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseGroupSpec _
  · rename_i peerV dir
    exact phaseGroupSpec_exists_guarded fineCostModel fun w hw =>
      (w3InitReal_singleSlotFineSpec_noA0 (hw.1 peerV dir rfl) w.F
        hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1 hw.2.2.2.2.2).groups
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _

theorem existentialW1_credit [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).encEnv
      w1SendRealDcanCum w1SendRealDcanLive w1SendRealDcanPeak w1SendRealDcanMaxReq := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact phaseCredit_exists_guarded_u fun w1R hw1 =>
      (w1SendRealSlot_dcan_singleSlotFineSpec_noFb (img := img) w1R hi hparse hw1).credit
  · exact emptyPhaseCreditSpec _ _ _ _

theorem existentialW1_groups [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseGroupSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).encEnv
      w1SendRealDcanGrpS := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · exact phaseGroupSpec_exists_guarded fineCostModel fun w1R hw1 =>
      (w1SendRealSlot_dcan_singleSlotFineSpec_noFb (img := img) w1R hi hparse hw1).groups
  · exact emptyPhaseGroupSpec _

theorem existentialW2_credit [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).decSigEnv
      w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanLive w2RecvWhisperRealDcanPeak
      w2RecvWhisperRealDcanMaxReq := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact phaseCredit_exists_guarded_u fun w2R hw2 =>
      (w2RecvWhisperRealSlot_dcan_singleSlotFineSpec_noFb w2R hi hparse hw2).credit

theorem existentialW2_groups [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseGroupSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).decSigEnv
      w2RecvWhisperRealDcanGrpS := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · exact phaseGroupSpec_exists_guarded fineCostModel fun w2R hw2 =>
      (w2RecvWhisperRealSlot_dcan_singleSlotFineSpec_noFb w2R hi hparse hw2).groups

theorem existentialW4_credit [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (P : PEParams) (g : RunCall) :
    PhaseCreditSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).decPkEnv
      w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live
      w4RecvPrekeyReal1MiB_i_Peak w4RecvPrekeyReal1MiB_i_MaxReq := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact emptyPhaseCreditSpec _ _ _ _
  · exact phaseCredit_exists_guarded_u fun w4R hw4 =>
      (w4RecvPrekeyReal1MiB_i_singleSlotFineSpec w4R hw4).credit

theorem existentialW4_groups [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (P : PEParams) (g : RunCall) :
    PhaseGroupSpec fineCostModel
      (mkExistentialRealCalleeEnvs img S P g).decPkEnv
      w4RecvPrekeyRealGrpS := by
  rcases g with ⟨i', c', a', res', call', stores', inp', coins'⟩
  cases c'
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · exact emptyPhaseGroupSpec _
  · exact phaseGroupSpec_exists_guarded fineCostModel fun w4R hw4 =>
      (w4RecvPrekeyReal1MiB_i_singleSlotFineSpec w4R hw4).groups

/-- `CliRealCalleeFineSpecs` witness on `mkExistentialRealCalleeEnvs img S P g` under
`CliPqxdhInputs P g.i` and `parseArgs = some g.c`. -/
def existentialRealCalleeFineSpecs [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    CliRealCalleeFineSpecs (mkExistentialRealCalleeEnvs img S P g) where
  initCum := w3InitRealCum
  initLive := w3InitRealLive
  initPeak := w3InitRealPeak
  initMaxReq := w3InitRealMaxReq
  initGrpS := w3InitRealGrpS
  init_spec := existentialW3_credit img S P g
  init_lp := w3InitReal_caps_le.2.2.1
  init_grp := existentialW3_groups img S P g
  encCum := w1SendRealDcanCum
  encLive := w1SendRealDcanLive
  encPeak := w1SendRealDcanPeak
  encMaxReq := w1SendRealDcanMaxReq
  encGrpS := w1SendRealDcanGrpS
  enc_spec := existentialW1_credit img S hi hparse
  enc_lp := w1SendRealDcan_live_le_peak
  enc_grp := existentialW1_groups img S hi hparse
  decSigCum := w2RecvWhisperRealDcanCum
  decSigLive := w2RecvWhisperRealDcanLive
  decSigPeak := w2RecvWhisperRealDcanPeak
  decSigMaxReq := w2RecvWhisperRealDcanMaxReq
  decSigGrpS := w2RecvWhisperRealDcanGrpS
  decSig_spec := existentialW2_credit img S hi hparse
  decSig_lp := w2RecvWhisperRealDcan_live_le_peak
  decSig_grp := existentialW2_groups img S hi hparse
  pksmCum := pksmCanonSliceCum msgCapBytes
  pksmLive := pksmCanonSliceLive msgCapBytes
  pksmPeak := pksmCanonSlicePeak msgCapBytes
  pksmMaxReq := pksmCanonSliceMaxReq msgCapBytes
  pksmGrpS := pksmCanonSliceGrpS msgCapBytes
  pksm_spec := fun _ hrest => pksmCanonSlice_fine_phaseCredit hrest
  pksm_lp := pksmCanonSliceLive_le_peak msgCapBytes
  pksm_grp := fun _ hrest => pksmCanonSlice_fine_groupSpec hrest
  decPkCum := w4RecvPrekeyReal1MiB_i_Cum
  decPkLive := w4RecvPrekeyReal1MiB_i_Live
  decPkPeak := w4RecvPrekeyReal1MiB_i_Peak
  decPkMaxReq := w4RecvPrekeyReal1MiB_i_MaxReq
  decPkGrpS := w4RecvPrekeyRealGrpS
  decPk_spec := existentialW4_credit img S P g
  decPk_lp := w4RecvPrekeyReal1MiB_i_eq.2.2.2.2
  decPk_grp := existentialW4_groups img S P g

/-- Numerical 5-slot `run` bounds for `existentialRealCalleeFineSpecs`. -/
theorem existentialRealCalleeFineSpecs_direct_run_bounds [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    let SE := existentialRealCalleeFineSpecs img S hi hparse
    cliRun1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliRealDirectRunCum_i ∧
    cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      cliRealDirectRunLive_i ∧
    cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
      SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤
      cliRealDirectRunPeak_i ∧
    cliRun1MiBCustomPksmMaxReq SE.pksmMaxReq
      SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤
      cliRealDirectRunMaxReq_i ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
      SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤
      cliRealDirectRunGrpS_i := by
  dsimp only [existentialRealCalleeFineSpecs]
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## Non-Vacuity Witness -/

/-- Allocating `3#8` `recv-prekey` non-vacuity witness on `mkExistentialRealCalleeEnvs`. -/
theorem existentialRealCalleeEnvs_recvPrekey_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) :
    ∃ (P₀ : PEParams) (g₀ : RunCall) (fullLog : List AllocEvent),
      CliPqRealCallDomain P₀ g₀ ∧
      CliMainEnv uuidTryParse
        (fun g' => CliRunOpenedEnv cliIo.rd
          (mkExistentialRealCalleeEnvs img S P₀ g') sessionCapBytes g')
        g₀ none false [] false fullLog ∧
      AllocEvent.alloc 72 ∈ fullLog ∧
      AllocEvent.realloc 1 2048 1569 ∈ fullLog :=
  cliPqRealCallDomain_recvPrekey_nonvacuous (mkExistentialRealCalleeEnvs img S) (fun _ _ => rfl)

end LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
