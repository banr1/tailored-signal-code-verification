/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudgetAux
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers
public import LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# Canonical-Outer `PreKeySignalMessage::try_from` Tight Credit & `CliMainEnv` Integration

On `CliPqxdhInputs`, every pre-key `recv` input (`stdin = 3#8 :: rest`) has canonical outer wire
bytes `rest = m.bytes` for some `m : PreKeyMessageFields` while `m.inner` remains arbitrary
(`SigTryFromCanonInnerEnv`). Because canonical outer decoding executes at most the 4 deterministic
outer `bytes::merge` calls (`preKeyLoopEvents`) rather than an arbitrary `1`-byte `copy_to_bytes`
loop, the `1 MiB` `PreKeySignalMessage::try_from` cumulative bound drops from `204,355,676` B
(`pksmSliceCum msgCapBytes`) to `103,232,265` B (`103,040,325` B using `m.inner.length + 1636 ≤
m.bytes.length`).

Contents:
1. Canonical PKSM slice envelopes (`SigTryFromCanonInnerEnv`, `PksmCanonCoreEnv`,
   `PksmCanonSliceEnv`) and extraction from `CliPqxdhInputs` (`cliPqInputs_recv_prekey_canonical`).
2. `PhaseCreditSpec` and `PhaseGroupSpec` bounds (`pksmCanonSlice_phaseCredit`,
   `pksmCanonSlice_tightInner_phaseCredit`, `pksmCanonSlice_fine_groupSpec`).
3. Containment bridges lifting `PreKeyTryFromOkPlacedBudget.preKeyTryFrom_placed_ok` into
   `PksmCanonSliceEnv`.
4. Concrete allocating non-vacuity witness (`pksmNonVacFields`, `pksmNonVacEvents`).
5. Outer `W4SlotR3bCanonEnv`, `CliRunCanonTightEnv`, and whole-`main` `CliMainEnv` corollaries.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit

open Arm64 (HookSat Program Spec subroutine_ok subroutine_ok_mono)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (SignalMessage SignalProtocolError)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPl_111
   extract_withLsCodeLoaded lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
   lsRustReallocSym lsmpl withLsCodeLoaded)
open CryptoVerification.E2E
  (PEParams PreKeyMessageFields wirePrekey wireWhisper)
open CryptoVerification.E2E.Pqxdh.ResponderWire
  (PreKeyTryFromArgs encodeVarint_1569 preKeyPlacedProg protoBytes_eq_psmRem0
   psmField1 psmField1_some psmField2 psmField2_eq psmField3 psmField3_eq
   psmField4 psmField4_eq psmField5 psmField5_eq psmField6 psmField6_eq
   psmField7 psmField7_eq psmField8 psmField8_eq
   psmRem0 psmRem1 psmRem2 psmRem3 psmRem4 psmRem5 psmRem6 psmRem7 psmRem8)
open CryptoVerification.LibsignalProtoCodec (WireType encodeVarint mergeBytes protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Cmd Inputs partyAddress pqInitInputs pqInputs pqRecvInputs pqSendInputs)
open CryptoVerification.SignalSession.Cli (ReadRule StoresGhost pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AddressCall CallV RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (runFiles)
open CryptoVerification.SignalSession.Cli.RunRefine (parseArgs_init parseArgs_send)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsTrace FreeOnlyEvs
   RustCliAllocBudget SeqEnv rustAllocEvents rustCliAllocBudgetSpec
   rustCliDeallocBudgetSpec rustCliReallocBudgetSpec rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
  (FromSeg2Env FromSeg3Env PreKeyLoopEnv PreKeyPostEnv PreKeySeg2Env PreKeySeg4Env PreKeySeg4OkEnv
   PreKeyTryFromEnv preKeyLoopEvents preKeyTryFromPlacedEnvSpec preKeyTryFromPlacedRawEnvSpec
   preKeyTryFromPlacedRawSpec preKeyTryFromPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudget
  (preKeyTryFrom_placed_ok preKeyTryFrom_placed_ok_of_callees)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudgetAux
  (PreKeyTryCloneOk)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
  (PreKeyDeallocOk PreKeyDropSpeOk)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget
  (PreKeyIntoBoxOk PreKeySigTryFromOk SigTryFromConcreteEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (CliPqDomainCaps dirDomainCaps_opened_own)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB
   fitsEnv_oneGiB_of_group_bounds_S4)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliMainEnv cliMainDeltaCum cliMainDeltaLive cliMainDeltaPeak cliMainMaxReq
   cliMain_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs CliRunEnv CliRunOpenedEnv CliRunSlotCalleeSpecs CliRunTightHyps
   CliRunWrapperEnvs CliRunWrapperSlotSpecs InitArmEnv JoinEnv R0OpenedEnv R2Env R3bEnv
   RecvArmEnv RunArmEnv addressTryParseDeltaCum cliRunDeltaCum
   cliRunDeltaLive cliRunDeltaPeak cliRunMaxReq cliRunOfR0_tight_phaseCredit_of_callees
   cliRunOpenedDeltaCum cliRunOpenedDeltaLive cliRunOpenedDeltaPeak cliRunOpenedMaxReq
   cliRunOpenedTightDeltaCum cliRunOpened_phaseCredit cliRunTightDeltaCum cliRun_phaseCredit
   cliRun_tight_phaseCredit fineCostModel_cliRunTightHyps initArmDeltaCum initArmDeltaLive
   initArmDeltaPeak initArmMaxReq initBundlePaths_phaseCredit pksmSliceCum
   r0Opened_phaseCredit_of_path r2DeltaLive r2DeltaPeak r2MaxReq r2TightDeltaCum
   r3b_phaseCredit runArmTightDeltaCum sigSliceCum sigSliceLive sigSliceMaxReq sigSlicePeak
   sigTryFromSlice_phaseCredit tempFilePostCum utf8_address_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (CliRunSpqrAndInitCaps CliRunTightSpqrCaps cliIo_rd_runFiles_length_le_of_filesBounded
   r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBMaxReq r0Opened1MiBPeak)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (CliRunDeserParamSlotCaps CliRunFineSlotSpecs CliRunTightSlotCaps cliDeserMaxCum
   cliDeserMaxGrpS cliDeserMaxLive cliDeserMaxPeak cliDeserMaxReq
   cliInitSlotCumCap cliInitSlotGrpSCap cliInitSlotLiveCap cliInitSlotPeakCap cliInitSlotReqCap
   cliMainDeserParamStepReserve cliMainStepReserve cliMainTightCumOf cliMainTightGrpSOf
   cliMainTightLiveOf cliMainTightPeakOf cliMainTightRamNeedOf cliMainTightReqOf
   cliMainTightStepReserveOf cliMainTightVaNeedOf
   cliMain_fine_credit_and_groups_of_run cliMain_fitsEnv_of_runFineBounds
   cliMain_fitsTrace_of_runFineBounds cliRecvPrekeySlotCumCap cliRecvPrekeySlotGrpSCap
   cliRecvPrekeySlotLiveCap cliRecvPrekeySlotPeakCap cliRecvPrekeySlotReqCap
   cliRecvWhisperSlotCumCap cliRecvWhisperSlotGrpSCap cliRecvWhisperSlotLiveCap
   cliRecvWhisperSlotPeakCap cliRecvWhisperSlotReqCap cliRunOfR0_fine_groupSpec
   cliSendSlotCumCap cliSendSlotGrpSCap cliSendSlotLiveCap cliSendSlotPeakCap cliSendSlotReqCap
   cliUnifiedDeserRunCumCap cliUnifiedDeserRunGrpSCap cliUnifiedDeserRunLiveCap
   cliUnifiedDeserRunPeakCap cliUnifiedDeserRunReqCap
   initArmEnv_fine_groupSpec r0OpenedEnv_fine_groupSpec r2Env_fine_groupSpec
   r3aEnv_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (pathDeltaCum pathDeltaLive pathDeltaPeak pathMaxReq path_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (IntoBoxedBoundedEnv IntoBoxedOptBoundedEnv SigTryFromBoundedEnv
   SigTryFromCaps SigTryFromErrTailEnv SigTryFromField SigTryFromLoopBoundedEnv SigTryFromPostEnv
   SigTryFromPostOutPreEnv sigTryFromCapDeltaGrpS sigTryFromDeltaCum sigTryFromDeltaGrpS
   sigTryFromDeltaLive sigTryFromDeltaPeak sigTryFromLoopDeltaGrpS sigTryFromLoop_phaseGroup
   sigTryFromMaxReq sigTryFrom_phaseCredit sigTryFrom_phaseGroup)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
  (PreKeyTryFromBoundedEnv WireGroupHyps WireLowInterceptHyps fineCostModel_wireLowInterceptHyps
   preKeyTryFromCapDeltaCum preKeyTryFromCapDeltaGrpS preKeyTryFromCapDeltaLive
   preKeyTryFromCapDeltaPeak preKeyTryFromCapMaxReq preKeyTryFromDeltaCum preKeyTryFromDeltaCum_le_cap
   preKeyTryFromDeltaGrpS preKeyTryFromDeltaGrpS_le_cap preKeyTryFromDeltaLive
   preKeyTryFromDeltaLive_le_cap preKeyTryFromDeltaPeak preKeyTryFromDeltaPeak_le_cap
   preKeyTryFromMaxReq preKeyTryFromMaxReq_le_cap preKeyTryFrom_phaseCredit_of_sig
   preKeyTryFrom_phaseGroup_of_sig wireRemGrows)
open LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers
  (bytesLargeLive bytesLargeLive_zero)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (bytesLargeLive_le_two_mul_of_le_max bytesMergeEventsCore_step_tight
   errTail_nil_or_from_or_push_tight fineCostModel_wireGroupHyps)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (TryCloneFromRefEnv framelessMemcpyBudgetSpec intoBoxedSliceEvents noAllocShimBudgetSpec
   tryCloneFromRefEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (int32MergeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore bytesMergeRawSpec)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux (TryFromEnvGen)
open ProofLib
  (satisfies_pure_sepConj satisfies_sepExists sepConj_assoc sepConj_left_comm sepExists_sepConj_left)

/-! ## Canonical PKSM Slice Envelope & `CliPqxdhInputs` Domain Extraction -/

/-- Lift canonical PQXDH `PreKeyMessageFields` (`PqxdhCorrectModel`) into `ResponderWire`'s
`PreKeyTryFromArgs` (`PreKeyTryFromBase`) at slice pointer `ptr` and output pointer `sret`. -/
def preKeyArgsOfFields (ptr sret : BitVec 64) (m : PreKeyMessageFields) : PreKeyTryFromArgs where
  ptr := ptr
  sret := sret
  regId := m.regId
  opkId := m.opkId
  spkId := m.spkId
  kpkId := m.kpkId
  kyberCt := m.kyberCt
  baseKey := m.baseKey
  idPub := m.idPub
  inner := m.inner

/-- Project `PreKeyTryFromArgs` back to the pointer-free `PreKeyMessageFields` model record. -/
def preKeyFieldsOfArgs (x : PreKeyTryFromArgs) : PreKeyMessageFields where
  regId := x.regId
  opkId := x.opkId
  spkId := x.spkId
  kpkId := x.kpkId
  kyberCt := x.kyberCt
  baseKey := x.baseKey
  idPub := x.idPub
  inner := x.inner

@[simp] theorem preKeyArgsOfFields_bytes (ptr sret : BitVec 64) (m : PreKeyMessageFields) :
    (preKeyArgsOfFields ptr sret m).bytes = m.bytes :=
  rfl

@[simp] theorem preKeyFieldsOfArgs_bytes (x : PreKeyTryFromArgs) :
    (preKeyFieldsOfArgs x).bytes = x.bytes :=
  rfl

@[simp] theorem preKeyArgsOfFields_inner (ptr sret : BitVec 64) (m : PreKeyMessageFields) :
    (preKeyArgsOfFields ptr sret m).inner = m.inner :=
  rfl

@[simp] theorem preKeyArgsOfFields_of_args (ptr sret : BitVec 64) (x : PreKeyTryFromArgs) :
    preKeyArgsOfFields ptr sret (preKeyFieldsOfArgs x) = { x with ptr := ptr, sret := sret } :=
  rfl

@[simp] theorem preKeyFieldsOfArgs_of_fields (ptr sret : BitVec 64) (m : PreKeyMessageFields) :
    preKeyFieldsOfArgs (preKeyArgsOfFields ptr sret m) = m :=
  rfl

/-- `PreKeyTryFromEnv sigEnv x` is independent of the ghost pointers `x.ptr` and `x.sret`. -/
theorem preKeyTryFromEnv_congr_ptrs
    (sigEnv : List (BitVec 8) → List AllocEvent → Prop)
    (ptr sret : BitVec 64) (x : PreKeyTryFromArgs) :
    PreKeyTryFromEnv sigEnv { x with ptr := ptr, sret := sret } = PreKeyTryFromEnv sigEnv x := by
  have hloop : PreKeyLoopEnv { x with ptr := ptr, sret := sret } = PreKeyLoopEnv x := rfl
  have hseg2 : PreKeySeg2Env { x with ptr := ptr, sret := sret } = PreKeySeg2Env x := rfl
  have hseg4 : PreKeySeg4Env { x with ptr := ptr, sret := sret } = PreKeySeg4Env x := by
    funext evs
    unfold PreKeySeg4Env PreKeySeg4OkEnv TryCloneFromRefEnv tryCloneFromRefEvents
    rfl
  unfold PreKeyTryFromEnv PreKeyPostEnv FromSeg2Env FromSeg3Env
  rw [hloop, hseg2, hseg4]

/-- Unconditional wire overhead bound on `PreKeyMessageFields.bytes`:
version byte (`1` B) + `baseKey` (`33` B payload) + `identityKey` (`33` B payload) +
`kyberCiphertext` (`1569` B payload) contribute at least `1,636` bytes on top of `m.inner`
(plus tag and varint headers). -/
theorem PreKeyMessageFields.inner_length_add_1636_le_bytes (m : PreKeyMessageFields) :
    m.inner.length + 1636 ≤ m.bytes.length := by
  let x : PreKeyTryFromArgs := preKeyArgsOfFields 0#64 0#64 m
  have hb : m.bytes = x.bytes := rfl
  have henc33 : (encodeVarint 33#64).length = 1 := by decide
  have hf2 : (psmField2 x).length = 35 := by
    rw [psmField2_eq, List.length_cons, List.length_append, henc33, PreKeyTryFromArgs.bkBytes_length]
  have hf3 : (psmField3 x).length = 35 := by
    rw [psmField3_eq, List.length_cons, List.length_append, henc33, PreKeyTryFromArgs.ikBytes_length]
  have hf4 : m.inner.length ≤ (psmField4 x).length := by
    have hx : x.inner = m.inner := rfl
    simp [psmField4, CryptoGames.LibsignalSessionApi.Prost.bytesField, hx]
    omega
  have hf8 : (psmField8 x).length = 1572 := by
    rw [psmField8_eq, encodeVarint_1569, List.length_cons, List.length_append,
      PreKeyTryFromArgs.kyberBytes_length]
    decide
  rw [hb, PreKeyTryFromArgs.bytes, List.length_cons, protoBytes_eq_psmRem0]
  simp only [psmRem0, psmRem1, psmRem2, psmRem3, psmRem4, psmRem5, psmRem6, psmRem7, psmRem8,
    List.length_append, List.length_nil]
  omega

/-- Unconditional corollary `m.inner.length ≤ m.bytes.length` for every `m : PreKeyMessageFields`. -/
theorem PreKeyMessageFields.inner_length_le_bytes (m : PreKeyMessageFields) :
    m.inner.length ≤ m.bytes.length := by
  have h := PreKeyMessageFields.inner_length_add_1636_le_bytes m
  omega

private theorem seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩
  · exact Or.inl (h1 evs hE1)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ hE1, h2 evs₂ hE2⟩

private theorem phaseCreditSpec_exists_guarded {α : Type} {M : AllocCostModel}
    [HasFineReallocCredit M] {P : α → Prop} {E : α → List AllocEvent → Prop}
    {c l p r : Nat}
    (h : ∀ x : α, P x → PhaseCreditSpec M (E x) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ x : α, P x ∧ E x evs) c l p r where
  req_align evs hEnv := by
    rcases hEnv with ⟨x, hx, hevs⟩
    exact (h x hx).req_align evs hevs
  credit_le st0 {evs} hEnv := by
    rcases hEnv with ⟨x, hx, hevs⟩
    exact (h x hx).credit_le st0 hevs

private theorem phaseCreditSpec_seq_freeOnly_right {M : AllocCostModel}
    [HasFineReallocCredit M] (hM : ModelHyps M)
    {E : List AllocEvent → Prop} {c l p r : Nat}
    (hE : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l (max p l) r :=
  (hE.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Inner `<SignalMessage as TryFrom<&[u8]>>::try_from` envelope covering both
`SigTryFromBoundedEnv` and `TryFromEnvGen.loopOnly` (early loop exit + `FreeOnlyEvs`), so
`SigTryFromConcreteEnv` embeds unconditionally for all `bs : List (BitVec 8)` while retaining
`sigTryFromDelta*` bounds. -/
def SigTryFromCanonInnerEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SigTryFromBoundedEnv ⟨0#64, bs, 0#64⟩ evs ∨
  SeqEnv (SigTryFromLoopBoundedEnv bs.length SigTryFromCaps.zero) FreeOnlyEvs evs

/-- Core canonical-outer allocator event envelope for `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`:
the outer wire slice `rest` is the canonical encoding `m.bytes` of some `m : PreKeyMessageFields`
while `m.inner` stays completely adversarial (`SigTryFromCanonInnerEnv`, `1 × 94·N`). -/
def PksmCanonCoreEnv (rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ m : PreKeyMessageFields,
    rest = m.bytes ∧
    PreKeyTryFromEnv SigTryFromCanonInnerEnv (preKeyArgsOfFields 0#64 0#64 m) evs

/-- Canonical-outer CLI slice envelope for `PreKeySignalMessage::try_from` (`RecvArmEnv` tag `3#8`):
either early/cleanup `FreeOnlyEvs` or `PksmCanonCoreEnv rest` (replacing `PksmTryFromSliceEnv`). -/
def PksmCanonSliceEnv (rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ PksmCanonCoreEnv rest evs

theorem pksmCanonSliceEnv_nil (rest : List (BitVec 8)) : PksmCanonSliceEnv rest [] :=
  Or.inl FreeOnlyEvs.nil

/-- Monotonicity of `PreKeyTryFromEnv` in the inner `SignalMessage::try_from` callee envelope. -/
theorem preKeyTryFromEnv_mono
    {sigEnv₁ sigEnv₂ : List (BitVec 8) → List AllocEvent → Prop}
    (hSig : ∀ bs evs, sigEnv₁ bs evs → sigEnv₂ bs evs)
    (x : PreKeyTryFromArgs) {evs : List AllocEvent}
    (h : PreKeyTryFromEnv sigEnv₁ x evs) :
    PreKeyTryFromEnv sigEnv₂ x evs :=
  seqEnv_mono (fun _ he => he)
    (fun _ hp => seqEnv_mono (fun _ hf => hf)
      (fun _ hs2 => seqEnv_mono (fun _ h2 => h2)
        (fun _ hs3 => seqEnv_mono (hSig x.inner) (fun _ h4 => h4) hs3) hs2) hp) h

theorem pksmCanonCoreEnv_of_bounded {x : PreKeyTryFromArgs} {rest : List (BitVec 8)}
    {evs : List AllocEvent} (hrest : rest = x.bytes) (hevs : PreKeyTryFromBoundedEnv x evs) :
    PksmCanonCoreEnv rest evs := by
  refine ⟨preKeyFieldsOfArgs x, hrest, ?_⟩
  rw [preKeyArgsOfFields_of_args, preKeyTryFromEnv_congr_ptrs]
  exact preKeyTryFromEnv_mono (fun _ _ h => Or.inl h) x hevs

/-- For any CLI call `i` in `CliPqxdhInputs W i` whose `argv` parses as `recv peer` and whose
`stdin` starts with the pre-key wire tag `3#8 :: rest`, `rest` is the canonical wire encoding
`m.bytes` of a `PreKeyMessageFields` `m` with `m.inner.length + 2048 < 2 ^ 32`. -/
theorem cliPqInputs_recv_prekey_canonical {W : PEParams} {i : Inputs} {peer : AddrV}
    {rest : List (BitVec 8)}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hst : i.stdin = 3#8 :: rest) :
    ∃ m : PreKeyMessageFields, rest = m.bytes ∧ m.inner.length + 2048 < 2 ^ 32 := by
  obtain ⟨st, _hwf, hcases⟩ := hi
  rcases hcases with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ | ⟨m, rc, hlen, rfl⟩ |
    ⟨c, rc, _, _hnw, hnp, rfl⟩
  · have ha : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) _).argv := rfl
    rw [ha, parseArgs_init] at hparse
    cases hparse
  · have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_send] at hparse
    cases hparse
  · simp only [pqRecvInputs, pqInputs, wireWhisper] at hst
    injection hst with hb _
    cases hb
  · simp only [pqRecvInputs, pqInputs, wirePrekey] at hst
    injection hst with _ hrest
    exact ⟨m, hrest.symm, hlen⟩
  · simp only [pqRecvInputs, pqInputs] at hst
    subst hst
    exact False.elim (hnp rfl)

/-! ## `PhaseCreditSpec` & `PhaseGroupSpec` Bounds -/

section InnerLoopCredit

private def capsLarge (M : AllocCostModel) [HasFineReallocCredit M] (c : SigTryFromCaps) : Nat :=
  bytesLargeLive M c.rk + bytesLargeLive M c.ct + bytesLargeLive M c.pq + bytesLargeLive M c.ad

private def capsOtherLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (c : SigTryFromCaps) : SigTryFromField → Nat
  | .rk => bytesLargeLive M c.ct + bytesLargeLive M c.pq + bytesLargeLive M c.ad
  | .ct => bytesLargeLive M c.rk + bytesLargeLive M c.pq + bytesLargeLive M c.ad
  | .pq => bytesLargeLive M c.rk + bytesLargeLive M c.ct + bytesLargeLive M c.ad
  | .ad => bytesLargeLive M c.rk + bytesLargeLive M c.ct + bytesLargeLive M c.pq

private def capsSum (c : SigTryFromCaps) : Nat :=
  c.rk + c.ct + c.pq + c.ad

private def capsOtherSum (c : SigTryFromCaps) : SigTryFromField → Nat
  | .rk => c.ct + c.pq + c.ad
  | .ct => c.rk + c.pq + c.ad
  | .pq => c.rk + c.ct + c.ad
  | .ad => c.rk + c.ct + c.pq

private def capsMinSum (S : Nat) (c : SigTryFromCaps) : Nat :=
  min c.rk S + min c.ct S + min c.pq S + min c.ad S

private def capsRemGrows (N : Nat) (c : SigTryFromCaps) : Nat :=
  wireRemGrows N c.rk + wireRemGrows N c.ct + wireRemGrows N c.pq + wireRemGrows N c.ad

private def capsOtherRemGrows (N : Nat) (c : SigTryFromCaps) : SigTryFromField → Nat
  | .rk => wireRemGrows N c.ct + wireRemGrows N c.pq + wireRemGrows N c.ad
  | .ct => wireRemGrows N c.rk + wireRemGrows N c.pq + wireRemGrows N c.ad
  | .pq => wireRemGrows N c.rk + wireRemGrows N c.ct + wireRemGrows N c.ad
  | .ad => wireRemGrows N c.rk + wireRemGrows N c.ct + wireRemGrows N c.pq

private def capsBounded (maxLen : Nat) (c : SigTryFromCaps) : Prop :=
  c.rk ≤ max 8 (2 * maxLen) ∧
  c.ct ≤ max 8 (2 * maxLen) ∧
  c.pq ≤ max 8 (2 * maxLen) ∧
  c.ad ≤ max 8 (2 * maxLen)

private def capsBoundedG (c g : SigTryFromCaps) : Prop :=
  c.rk ≤ max (2 * g.rk) 8 ∧
  c.ct ≤ max (2 * g.ct) 8 ∧
  c.pq ≤ max (2 * g.pq) 8 ∧
  c.ad ≤ max (2 * g.ad) 8

private theorem capsLarge_decomp (M : AllocCostModel) [HasFineReallocCredit M]
    (c : SigTryFromCaps) (f : SigTryFromField) (v : Nat) :
    capsLarge M c = capsOtherLarge M c f + bytesLargeLive M (c.get f) ∧
    capsLarge M (c.set f v) = capsOtherLarge M c f + bytesLargeLive M v := by
  cases f <;> dsimp only [capsLarge, capsOtherLarge, SigTryFromCaps.get, SigTryFromCaps.set] <;>
    exact ⟨by omega, by omega⟩

private theorem capsRemGrows_decomp (N : Nat) (c : SigTryFromCaps) (f : SigTryFromField) (v : Nat) :
    capsRemGrows N c = capsOtherRemGrows N c f + wireRemGrows N (c.get f) ∧
    capsRemGrows N (c.set f v) = capsOtherRemGrows N c f + wireRemGrows N v := by
  cases f <;> dsimp only [capsRemGrows, capsOtherRemGrows, SigTryFromCaps.get, SigTryFromCaps.set] <;>
    exact ⟨by omega, by omega⟩

private theorem capsG_props {c g : SigTryFromCaps} (hcg : capsBoundedG c g)
    (f : SigTryFromField) {v_cap v_g : Nat} (hv : v_cap ≤ max (2 * v_g) 8) :
    capsSum g = capsOtherSum g f + g.get f ∧
    capsSum (g.set f v_g) = capsOtherSum g f + v_g ∧
    c.get f ≤ max (2 * g.get f) 8 ∧
    capsBoundedG (c.set f v_cap) (g.set f v_g) := by
  obtain ⟨h0, h1, h2, h3⟩ := hcg
  cases f <;>
    dsimp only [SigTryFromCaps.get, SigTryFromCaps.set, capsSum, capsOtherSum, capsBoundedG] <;>
    exact ⟨by omega, by omega, by omega, ⟨by omega, by omega, by omega, by omega⟩⟩

private theorem capsMinSum_props {S maxLen : Nat} {c : SigTryFromCaps}
    (hc : capsBounded maxLen c) (f : SigTryFromField) {v : Nat}
    (hle : min (c.get f) S ≤ min v S) (hv : v ≤ max 8 (2 * maxLen)) :
    c.get f ≤ max 8 (2 * maxLen) ∧
    capsBounded maxLen (c.set f v) ∧
    capsMinSum S c ≤ 4 * min (max 8 (2 * maxLen)) S ∧
    capsMinSum S (c.set f v) ≤ 4 * min (max 8 (2 * maxLen)) S ∧
    capsMinSum S (c.set f v) + min (c.get f) S = capsMinSum S c + min v S := by
  obtain ⟨h0, h1, h2, h3⟩ := hc
  cases f <;>
    dsimp only [SigTryFromCaps.get, SigTryFromCaps.set, capsBounded, capsMinSum] at hle ⊢ <;>
    exact ⟨by omega, ⟨by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega⟩

private theorem capsOtherLarge_le_g {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    {c g : SigTryFromCaps} (hcg : capsBoundedG c g) (f : SigTryFromField) :
    capsOtherLarge M c f ≤ 2 * capsOtherSum g f + 24585 := by
  obtain ⟨h0, h1, h2, h3⟩ := hcg
  have l0 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h0
  have l1 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h1
  have l2 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h2
  have l3 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h3
  cases f <;> simp only [capsOtherLarge, capsOtherSum] <;> omega

private theorem capsLarge_le_g {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    {c g : SigTryFromCaps} (hcg : capsBoundedG c g) :
    capsLarge M c ≤ 2 * capsSum g + 32780 := by
  obtain ⟨h0, h1, h2, h3⟩ := hcg
  have l0 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h0
  have l1 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h1
  have l2 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h2
  have l3 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h3
  unfold capsLarge capsSum
  omega

private theorem sigTryFromErrTail_cases {evs : List AllocEvent}
    (h : SigTryFromErrTailEnv evs) :
    evs = [] ∨ evs = rustAllocEvents 72 8 ∨
    evs = rustAllocEvents 72 8 ++ [] ∨
    evs = rustAllocEvents 72 8 ++ rustAllocEvents 128 8 := by
  cases h with
  | nil => exact Or.inl rfl
  | fromOnly => exact Or.inr (Or.inl rfl)
  | fromPush hp =>
    rcases hp with rfl | ⟨_, rfl⟩ | ⟨hpos, _⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · omega

private theorem loop_step_credit_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {S maxLen base rem : Nat}
    (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS128 : 128 ≤ S)
    {caps : SigTryFromCaps} {evs : List AllocEvent}
    (hloop : SigTryFromLoopBoundedEnv rem caps evs) :
    ∀ (st : M.σ) (g : SigTryFromCaps),
      rem ≤ maxLen →
      capsBounded maxLen caps →
      capsBoundedG caps g →
      capsSum g + rem ≤ maxLen →
      HasFineReallocCredit.liveLarge st ≤ base + capsLarge M caps →
      (∀ ev ∈ evs, eventStepReq ev ≤ max 128 (2 * maxLen) ∧ eventStepAlign ev ≤ 16) ∧
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st + 94 * rem +
          4 * (4 * min (max 8 (2 * maxLen)) S - capsMinSum S caps) +
          9539 * capsRemGrows maxLen caps + 19478 ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
        base + (2 * maxLen + 32780) ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
        max (HasFineReallocCredit.peakLarge st) (base + (3 * maxLen + 49170)) := by
  have hS8 : 8 ≤ S := by omega
  induction hloop with
  | @done rem caps evs herr =>
    intro st g _ _ hcg hg_rem hlive
    have hcl := capsLarge_le_g hM hSm hS8 hcg
    have hlive_bd : HasFineReallocCredit.liveLarge st ≤ base + (2 * maxLen + 32780) := by omega
    obtain ⟨hreq, hcum, hlv, hpk⟩ :=
      errTail_nil_or_from_or_push_tight hM (maxLen := maxLen) hSm hS128 st hlive_bd
        (sigTryFromErrTail_cases herr)
    set Mmax := 4 * min (max 8 (2 * maxLen)) S
    set MS := capsMinSum S caps
    set GW := capsRemGrows maxLen caps
    have hcum' : HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st + 94 * rem +
          4 * (Mmax - MS) + 9539 * GW + 19478 :=
      Nat.le_trans hcum (by omega)
    have hpk' : HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
        max (HasFineReallocCredit.peakLarge st) (base + (3 * maxLen + 49170)) :=
      Nat.le_trans hpk (max_le_max (Nat.le_refl _) (by omega))
    exact ⟨hreq, hcum', hlv, hpk'⟩
  | @skipStep rem rem' caps evs hlt _ ih =>
    intro st g hrem hcaps hcg hg_rem hlive
    obtain ⟨hreq, hcum, hlv, hpk⟩ :=
      ih st g (by omega) hcaps hcg (by omega) hlive
    set Mmax := 4 * min (max 8 (2 * maxLen)) S
    set MS := capsMinSum S caps
    set GW := capsRemGrows maxLen caps
    have hmono : 94 * rem' ≤ 94 * rem := Nat.mul_le_mul_left 94 (Nat.le_of_lt hlt)
    exact ⟨hreq, Nat.le_trans hcum (by omega), hlv, hpk⟩
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm _ hrem_step hcap63 _ ih =>
    intro st g hrem hcaps hcg hg_rem hlive
    have hcap64 : caps.get f < 2 ^ 64 := by omega
    have hcap_max : caps.get f ≤ max 8 (2 * maxLen) := by
      obtain ⟨h0, h1, h2, h3⟩ := hcaps
      cases f <;> simp only [SigTryFromCaps.get] <;> omega
    set cap := caps.get f
    set cap' := if v.length ≤ cap then cap else reserveCap cap 0 v.length
    set g_f := g.get f
    set g_f' := if v.length ≤ cap then g_f else v.length
    obtain ⟨hg_sum_pre, _, hcap_g_pre, _⟩ :=
      capsG_props hcg f (v_cap := cap) (v_g := g_f)
        (by obtain ⟨h0, h1, h2, h3⟩ := hcg; dsimp only [cap, g_f]; cases f <;> dsimp only [SigTryFromCaps.get] <;> omega)
    change capsSum g = capsOtherSum g f + g_f at hg_sum_pre
    change cap ≤ max (2 * g_f) 8 at hcap_g_pre
    obtain ⟨hdec_pre, hdec_post⟩ := capsLarge_decomp M caps f cap'
    change capsLarge M caps = capsOtherLarge M caps f + bytesLargeLive M cap at hdec_pre
    have hlive' : HasFineReallocCredit.liveLarge st ≤
        base + capsOtherLarge M caps f + bytesLargeLive M cap := by omega
    obtain ⟨hreq1, hmin_le, _, hcap'_max, hcap'_g, hg_rem', hcum1, hlive1, hpeak1⟩ :=
      bytesMergeEventsCore_step_tight hM hLow hSm hS8 hm hrem_step hrem hcap64 hcap_max
        hcap_g_pre (capsOtherLarge_le_g hM hSm hS8 hcg f) (by omega) st hlive'
    change min cap S ≤ min cap' S at hmin_le
    change cap' ≤ max 8 (2 * maxLen) at hcap'_max
    change cap' ≤ max (2 * g_f') 8 at hcap'_g
    change capsOtherSum g f + g_f' + rem' ≤ maxLen at hg_rem'
    obtain ⟨_, hcaps', _, hms'_le, hms_eq⟩ := capsMinSum_props hcaps f hmin_le hcap'_max
    obtain ⟨_, hg_sum_post, _, hcg'⟩ := capsG_props hcg f hcap'_g
    obtain ⟨hgw_pre, hgw_post⟩ := capsRemGrows_decomp maxLen caps f cap'
    rw [AllocCostModel.stepEvents_append]
    set evs₁ := bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs
    set st₁ := M.stepEvents evs₁ st
    change HasFineReallocCredit.liveLarge st₁ ≤
      base + capsOtherLarge M caps f + bytesLargeLive M cap' at hlive1
    change capsLarge M (caps.set f cap') =
      capsOtherLarge M caps f + bytesLargeLive M cap' at hdec_post
    have hlive1' : HasFineReallocCredit.liveLarge st₁ ≤
        base + capsLarge M (caps.set f cap') := by omega
    obtain ⟨hreq2, hcum2, hlv2, hpk2⟩ :=
      ih st₁ (g.set f g_f') (by omega) hcaps' hcg' (by omega) hlive1'
    set st₂ := M.stepEvents evs₂ st₁
    set Mmax := 4 * min (max 8 (2 * maxLen)) S
    set W := wireRemGrows maxLen cap
    set W' := wireRemGrows maxLen cap'
    set GW_other := capsOtherRemGrows maxLen caps f
    set MS := capsMinSum S caps
    set MS' := capsMinSum S (caps.set f cap')
    set MC := min cap S
    set MC' := min cap' S
    change HasFineReallocCredit.cumSmall st₁ + 9539 * W' ≤
      HasFineReallocCredit.cumSmall st + 94 * (rem - rem') + 4 * (MC' - MC) + 9539 * W at hcum1
    change capsRemGrows maxLen caps = GW_other + W at hgw_pre
    change capsRemGrows maxLen (caps.set f cap') = GW_other + W' at hgw_post
    change MS' ≤ Mmax at hms'_le
    change MS' + MC = MS + MC' at hms_eq
    have hcum_comb : HasFineReallocCredit.cumSmall st₂ ≤
        HasFineReallocCredit.cumSmall st + 94 * rem +
          4 * (Mmax - MS) + 9539 * capsRemGrows maxLen caps + 19478 := by
      have hrem_mul : 94 * (rem - rem') + 94 * rem' = 94 * rem := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
      rw [hgw_post] at hcum2
      rw [hgw_pre]
      omega
    have hpk_comb : HasFineReallocCredit.peakLarge st₂ ≤
        max (HasFineReallocCredit.peakLarge st) (base + (3 * maxLen + 49170)) :=
      Nat.le_trans hpk2 (Nat.max_le.mpr ⟨hpeak1, Nat.le_max_right _ _⟩)
    refine ⟨?_, hcum_comb, hlv2, hpk_comb⟩
    intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · obtain ⟨hr, hal⟩ := hreq1 ev h1
      exact ⟨Nat.le_trans hr (by omega), hal⟩
    · exact hreq2 ev h2

/-- Loop-level `PhaseCreditSpec` for `SigTryFromLoopBoundedEnv N SigTryFromCaps.zero`. -/
theorem sigTryFromLoop_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (N : Nat) :
    PhaseCreditSpec M (SigTryFromLoopBoundedEnv N SigTryFromCaps.zero)
      (94 * N + 16 * min (max 8 (2 * N)) 135167 + 38156 * wireRemGrows N 0 + 19478)
      (2 * N + 32780) (3 * N + 49170) (max 128 (2 * N)) where
  req_align evs hloop := by
    have hzero_bd : capsBounded N SigTryFromCaps.zero := by
      simp [capsBounded, SigTryFromCaps.zero]
    have hzero_g : capsBoundedG SigTryFromCaps.zero SigTryFromCaps.zero := by
      simp [capsBoundedG, SigTryFromCaps.zero]
    have hzero_lg : capsLarge M SigTryFromCaps.zero = 0 := by
      simp [capsLarge, SigTryFromCaps.zero, bytesLargeLive_zero]
    have hzero_sum : capsSum SigTryFromCaps.zero = 0 := rfl
    exact (loop_step_credit_S hM hLow (maxLen := N) (base := HasFineReallocCredit.liveLarge M.init)
      hLow.hSmallMaxEq (by decide) hloop M.init SigTryFromCaps.zero (Nat.le_refl N)
      hzero_bd hzero_g (by omega) (by omega)).1
  credit_le st0 {_} hloop := by
    have hzero_bd : capsBounded N SigTryFromCaps.zero := by
      simp [capsBounded, SigTryFromCaps.zero]
    have hzero_g : capsBoundedG SigTryFromCaps.zero SigTryFromCaps.zero := by
      simp [capsBoundedG, SigTryFromCaps.zero]
    have hzero_lg : capsLarge M SigTryFromCaps.zero = 0 := by
      simp [capsLarge, SigTryFromCaps.zero, bytesLargeLive_zero]
    have hzero_sum : capsSum SigTryFromCaps.zero = 0 := rfl
    have hzero_ms : capsMinSum 135167 SigTryFromCaps.zero = 0 := by
      simp [capsMinSum, SigTryFromCaps.zero]
    have hzero_gw : capsRemGrows N SigTryFromCaps.zero = 4 * wireRemGrows N 0 := by
      simp only [capsRemGrows, SigTryFromCaps.zero]
      omega
    obtain ⟨_, hcum, hlv, hpk⟩ :=
      loop_step_credit_S hM hLow (maxLen := N) (base := HasFineReallocCredit.liveLarge st0)
        hLow.hSmallMaxEq (by decide) hloop st0 SigTryFromCaps.zero (Nat.le_refl N)
        hzero_bd hzero_g (by omega) (by omega)
    rw [hzero_ms, Nat.sub_zero, hzero_gw] at hcum
    set A := min (max 8 (2 * N)) 135167
    set K := wireRemGrows N 0
    exact ⟨Nat.le_trans hcum (by omega), hlv, hpk⟩

end InnerLoopCredit

/-- `PhaseCreditSpec` for `SigTryFromCanonInnerEnv bs` with `sigTryFromDelta*` bounds. -/
theorem sigTryFromCanonInner_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (bs : List (BitVec 8)) :
    let g : TryFromGhost := ⟨0#64, bs, 0#64⟩
    PhaseCreditSpec M (SigTryFromCanonInnerEnv bs)
      (sigTryFromDeltaCum g)
      (sigTryFromDeltaLive g)
      (sigTryFromDeltaPeak g)
      (sigTryFromMaxReq g) := by
  dsimp only
  have h1 := sigTryFrom_phaseCredit hM hLow ⟨0#64, bs, 0#64⟩
  have hloop := (sigTryFromLoop_phaseCredit hM hLow bs.length).seq
    (PhaseCreditSpec.freeOnly_of_hyps hM)
  refine (h1.or hloop).mono ?_ ?_ ?_ ?_
  · unfold sigTryFromDeltaCum
    dsimp only
    omega
  · unfold sigTryFromDeltaLive
    dsimp only
    omega
  · unfold sigTryFromDeltaPeak
    dsimp only
    omega
  · unfold sigTryFromMaxReq
    dsimp only
    omega

/-- `PhaseGroupSpec` for `SigTryFromCanonInnerEnv bs` with `sigTryFromDeltaGrpS` bound. -/
theorem sigTryFromCanonInner_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (bs : List (BitVec 8)) :
    PhaseGroupSpec M (SigTryFromCanonInnerEnv bs) (sigTryFromDeltaGrpS ⟨0#64, bs, 0#64⟩) := by
  have h1 := sigTryFrom_phaseGroup hGrp ⟨0#64, bs, 0#64⟩
  have hloop := (sigTryFromLoop_phaseGroup hGrp bs.length).seq (PhaseGroupSpec.freeOnly M)
  refine (h1.or hloop).mono ?_
  unfold sigTryFromDeltaGrpS sigTryFromLoopDeltaGrpS
  dsimp only
  omega

/-- As-is closed-form cumulative small-allocation bound for `PksmCanonSliceEnv` at slice cap `N`
(`preKeyTryFromCapDeltaCum N N` = `103,232,265` B at `N = msgCapBytes = 1,048,576`). -/
def pksmCanonSliceCum (N : Nat) : Nat :=
  preKeyTryFromCapDeltaCum N N

/-- Tight-inner cumulative bound exploiting `m.inner.length + 1636 ≤ m.bytes.length`
(`preKeyTryFromCapDeltaCum (N - 1636) N` = `103,040,325` B at `N = msgCapBytes = 1,048,576`). -/
def pksmCanonSliceTightInnerCum (N : Nat) : Nat :=
  preKeyTryFromCapDeltaCum (N - 1636) N

/-- Live heap delta bound for `PksmCanonSliceEnv` at slice cap `N` (`8,462,395` B at `1 MiB`). -/
def pksmCanonSliceLive (N : Nat) : Nat :=
  preKeyTryFromCapDeltaLive N N

/-- Peak live heap delta bound for `PksmCanonSliceEnv` at slice cap `N` (`14,811,248` B at `1 MiB`). -/
def pksmCanonSlicePeak (N : Nat) : Nat :=
  preKeyTryFromCapDeltaPeak N N

/-- Maximum single allocation request bound for `PksmCanonSliceEnv` at slice cap `N`
(`2,097,152` B at `1 MiB`). -/
def pksmCanonSliceMaxReq (N : Nat) : Nat :=
  preKeyTryFromCapMaxReq N N

/-- Scaled small-allocation group bound (`PhaseGroupSpec`) for `PksmCanonSliceEnv` at slice cap `N`. -/
def pksmCanonSliceGrpS (N : Nat) : Nat :=
  preKeyTryFromCapDeltaGrpS N N

/-- Tight-inner scaled small-allocation group bound at `M_cap = N - 1636`. -/
def pksmCanonSliceTightInnerGrpS (N : Nat) : Nat :=
  preKeyTryFromCapDeltaGrpS (N - 1636) N

/-- Unconditional `live ≤ peak` inequality (`pksmCanonSliceLive N ≤ pksmCanonSlicePeak N`). -/
theorem pksmCanonSliceLive_le_peak (N : Nat) :
    pksmCanonSliceLive N ≤ pksmCanonSlicePeak N := by
  unfold pksmCanonSliceLive pksmCanonSlicePeak preKeyTryFromCapDeltaLive preKeyTryFromCapDeltaPeak
  omega

/-- Kernel-checked `1 MiB` (`msgCapBytes = 1,048,576`) profile for `PksmCanonSliceEnv`, plus the
exact `101,123,411` B (`101.12 MB`) `Δcum` reduction vs unmodified `pksmSliceCum msgCapBytes`
(`204,355,676` B). -/
theorem pksmCanonSlice1MiB_profile_eq :
    pksmCanonSliceCum msgCapBytes = 103232265 ∧
    pksmCanonSliceTightInnerCum msgCapBytes = 103040325 ∧
    pksmCanonSliceLive msgCapBytes = 8462395 ∧
    pksmCanonSlicePeak msgCapBytes = 14811248 ∧
    pksmCanonSliceMaxReq msgCapBytes = 2097152 ∧
    pksmCanonSliceGrpS msgCapBytes = 2496720998 ∧
    pksmSliceCum msgCapBytes - pksmCanonSliceCum msgCapBytes = 101123411 := by
  decide

private theorem freeOr_zero_left (a : Nat) : max 0 a ≤ a := by omega

/-- `PhaseCreditSpec` for `PreKeyTryFromEnv SigTryFromCanonInnerEnv x`. -/
theorem preKeyTryFromCanonInner_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (x : PreKeyTryFromArgs) :
    PhaseCreditSpec M (PreKeyTryFromEnv SigTryFromCanonInnerEnv x)
      (preKeyTryFromDeltaCum x)
      (preKeyTryFromDeltaLive x)
      (preKeyTryFromDeltaPeak x)
      (preKeyTryFromMaxReq x) :=
  preKeyTryFrom_phaseCredit_of_sig hM hLow x (sigTryFromCanonInner_phaseCredit hM hLow x.inner)

/-- `PhaseGroupSpec` for `PreKeyTryFromEnv SigTryFromCanonInnerEnv x`. -/
theorem preKeyTryFromCanonInner_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x : PreKeyTryFromArgs) :
    PhaseGroupSpec M (PreKeyTryFromEnv SigTryFromCanonInnerEnv x) (preKeyTryFromDeltaGrpS x) :=
  preKeyTryFrom_phaseGroup_of_sig hGrp x (sigTryFromCanonInner_phaseGroup hGrp x.inner)

/-- `PhaseCreditSpec` for `PksmCanonCoreEnv rest` at `rest.length ≤ N` (`preKeyTryFromCapDeltaCum N N`). -/
theorem pksmCanonCore_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rest : List (BitVec 8)} {N : Nat} (hrest : rest.length ≤ N) :
    PhaseCreditSpec M (PksmCanonCoreEnv rest)
      (pksmCanonSliceCum N)
      (pksmCanonSliceLive N)
      (pksmCanonSlicePeak N)
      (pksmCanonSliceMaxReq N) := by
  unfold PksmCanonCoreEnv
  refine phaseCreditSpec_exists_guarded (fun m hm => ?_)
  have hB : (preKeyArgsOfFields 0#64 0#64 m).bytes.length ≤ N := by
    rw [preKeyArgsOfFields_bytes, ← hm]
    exact hrest
  have hIn : (preKeyArgsOfFields 0#64 0#64 m).inner.length ≤ N :=
    Nat.le_trans (PreKeyMessageFields.inner_length_le_bytes m) (hm ▸ hrest)
  exact (preKeyTryFromCanonInner_phaseCredit hM hLow (preKeyArgsOfFields 0#64 0#64 m)).mono
    (preKeyTryFromDeltaCum_le_cap hIn hB)
    (preKeyTryFromDeltaLive_le_cap hIn hB)
    (preKeyTryFromDeltaPeak_le_cap hIn hB)
    (preKeyTryFromMaxReq_le_cap hIn hB)

/-- `PhaseCreditSpec` for `PksmCanonSliceEnv rest` (`103,232,265` B at `1 MiB`), requiring only
`rest.length ≤ N`. -/
theorem pksmCanonSlice_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rest : List (BitVec 8)} {N : Nat} (hrest : rest.length ≤ N) :
    PhaseCreditSpec M (PksmCanonSliceEnv rest)
      (pksmCanonSliceCum N)
      (pksmCanonSliceLive N)
      (pksmCanonSlicePeak N)
      (pksmCanonSliceMaxReq N) :=
  ((PhaseCreditSpec.freeOnly_of_hyps hM).or (pksmCanonCore_phaseCredit hM hLow hrest)).mono
    (freeOr_zero_left _) (freeOr_zero_left _) (freeOr_zero_left _) (freeOr_zero_left _)

/-- Tight-inner `PhaseCreditSpec` for `PksmCanonSliceEnv rest` (`103,040,325` B at `1 MiB`),
using `m.inner.length + 1636 ≤ m.bytes.length`. -/
theorem pksmCanonSlice_tightInner_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rest : List (BitVec 8)} {N : Nat} (hrest : rest.length ≤ N) :
    PhaseCreditSpec M (PksmCanonSliceEnv rest)
      (pksmCanonSliceTightInnerCum N)
      (pksmCanonSliceLive N)
      (pksmCanonSlicePeak N)
      (pksmCanonSliceMaxReq N) := by
  have hCore :
      PhaseCreditSpec M (PksmCanonCoreEnv rest)
        (pksmCanonSliceTightInnerCum N)
        (pksmCanonSliceLive N)
        (pksmCanonSlicePeak N)
        (pksmCanonSliceMaxReq N) := by
    unfold PksmCanonCoreEnv
    refine phaseCreditSpec_exists_guarded (fun m hm => ?_)
    have hB : (preKeyArgsOfFields 0#64 0#64 m).bytes.length ≤ N := by
      rw [preKeyArgsOfFields_bytes, ← hm]
      exact hrest
    have hInTight : (preKeyArgsOfFields 0#64 0#64 m).inner.length ≤ N - 1636 := by
      have h1636 := PreKeyMessageFields.inner_length_add_1636_le_bytes m
      have hlen : m.bytes.length ≤ N := hm ▸ hrest
      simp only [preKeyArgsOfFields_inner]
      omega
    have hIn : (preKeyArgsOfFields 0#64 0#64 m).inner.length ≤ N :=
      Nat.le_trans hInTight (Nat.sub_le N 1636)
    exact (preKeyTryFromCanonInner_phaseCredit hM hLow (preKeyArgsOfFields 0#64 0#64 m)).mono
      (preKeyTryFromDeltaCum_le_cap hInTight hB)
      (preKeyTryFromDeltaLive_le_cap hIn hB)
      (preKeyTryFromDeltaPeak_le_cap hIn hB)
      (preKeyTryFromMaxReq_le_cap hIn hB)
  exact ((PhaseCreditSpec.freeOnly_of_hyps hM).or hCore).mono
    (freeOr_zero_left _) (freeOr_zero_left _) (freeOr_zero_left _) (freeOr_zero_left _)

/-- `fineCostModel` specialization of `pksmCanonSlice_phaseCredit` (`0` `*Hyps` binders). -/
theorem pksmCanonSlice_fine_phaseCredit {rest : List (BitVec 8)} {N : Nat}
    (hrest : rest.length ≤ N) :
    PhaseCreditSpec fineCostModel (PksmCanonSliceEnv rest)
      (pksmCanonSliceCum N)
      (pksmCanonSliceLive N)
      (pksmCanonSlicePeak N)
      (pksmCanonSliceMaxReq N) :=
  pksmCanonSlice_phaseCredit fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps hrest

/-- `fineCostModel` specialization of `pksmCanonSlice_tightInner_phaseCredit` (`0` `*Hyps` binders). -/
theorem pksmCanonSlice_tightInner_fine_phaseCredit {rest : List (BitVec 8)} {N : Nat}
    (hrest : rest.length ≤ N) :
    PhaseCreditSpec fineCostModel (PksmCanonSliceEnv rest)
      (pksmCanonSliceTightInnerCum N)
      (pksmCanonSliceLive N)
      (pksmCanonSlicePeak N)
      (pksmCanonSliceMaxReq N) :=
  pksmCanonSlice_tightInner_phaseCredit fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps
    hrest

/-- `PhaseGroupSpec` for `PksmCanonCoreEnv rest` at `rest.length ≤ N`. -/
theorem pksmCanonCore_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) {rest : List (BitVec 8)} {N : Nat} (hrest : rest.length ≤ N) :
    PhaseGroupSpec M (PksmCanonCoreEnv rest) (pksmCanonSliceGrpS N) where
  groups_le st {evs} hEnv := by
    rcases hEnv with ⟨m, hm, hPre⟩
    have hB : (preKeyArgsOfFields 0#64 0#64 m).bytes.length ≤ N := by
      rw [preKeyArgsOfFields_bytes, ← hm]
      exact hrest
    have hIn : (preKeyArgsOfFields 0#64 0#64 m).inner.length ≤ N :=
      Nat.le_trans (PreKeyMessageFields.inner_length_le_bytes m) (hm ▸ hrest)
    exact ((preKeyTryFromCanonInner_phaseGroup hGrp (preKeyArgsOfFields 0#64 0#64 m)).mono
      (preKeyTryFromDeltaGrpS_le_cap hIn hB)).groups_le st hPre

/-- `PhaseGroupSpec` for `PksmCanonSliceEnv rest` at `rest.length ≤ N`. -/
theorem pksmCanonSlice_phaseGroup {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) {rest : List (BitVec 8)} {N : Nat} (hrest : rest.length ≤ N) :
    PhaseGroupSpec M (PksmCanonSliceEnv rest) (pksmCanonSliceGrpS N) :=
  ((PhaseGroupSpec.freeOnly M).or (pksmCanonCore_phaseGroup hGrp hrest)).mono
    (freeOr_zero_left _)

/-- `fineCostModel` specialization of `pksmCanonSlice_phaseGroup` (`0` `*Hyps` binders). -/
theorem pksmCanonSlice_fine_groupSpec {rest : List (BitVec 8)} {N : Nat}
    (hrest : rest.length ≤ N) :
    PhaseGroupSpec fineCostModel (PksmCanonSliceEnv rest) (pksmCanonSliceGrpS N) :=
  pksmCanonSlice_phaseGroup fineCostModel_wireGroupHyps hrest

/-- Tight-inner `fineCostModel` `PhaseGroupSpec` at `M_cap = N - 1636`. -/
theorem pksmCanonSlice_tightInner_fine_groupSpec {rest : List (BitVec 8)} {N : Nat}
    (hrest : rest.length ≤ N) :
    PhaseGroupSpec fineCostModel (PksmCanonSliceEnv rest) (pksmCanonSliceTightInnerGrpS N) := by
  have hCore : PhaseGroupSpec fineCostModel (PksmCanonCoreEnv rest)
      (pksmCanonSliceTightInnerGrpS N) :=
    { groups_le := fun st {evs} hEnv => by
        rcases hEnv with ⟨m, hm, hPre⟩
        have hB : (preKeyArgsOfFields 0#64 0#64 m).bytes.length ≤ N := by
          rw [preKeyArgsOfFields_bytes, ← hm]
          exact hrest
        have hInTight : (preKeyArgsOfFields 0#64 0#64 m).inner.length ≤ N - 1636 := by
          have h1636 := PreKeyMessageFields.inner_length_add_1636_le_bytes m
          have hlen : m.bytes.length ≤ N := hm ▸ hrest
          simp only [preKeyArgsOfFields_inner]
          omega
        exact ((preKeyTryFromCanonInner_phaseGroup fineCostModel_wireGroupHyps
          (preKeyArgsOfFields 0#64 0#64 m)).mono
          (preKeyTryFromDeltaGrpS_le_cap hInTight hB)).groups_le st hPre }
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hCore).mono (freeOr_zero_left _)

/-! ## Binary Containment Bridge (`PreKeyTryFromOkPlacedBudget` → `PksmCanonSliceEnv`) -/

private def mapSigField :
    LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField → SigTryFromField
  | .rk => .rk
  | .ct => .ct
  | .pq => .pq
  | .ad => .ad

private def mapSigCaps
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps) :
    SigTryFromCaps :=
  ⟨c.rk, c.ct, c.pq, c.ad⟩

private theorem mapSigCaps_get
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) :
    (mapSigCaps c).get (mapSigField f) = c.get f := by
  cases f <;> rfl

private theorem mapSigCaps_set
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) (v : Nat) :
    mapSigCaps (c.set f v) = (mapSigCaps c).set (mapSigField f) v := by
  cases f <;> rfl

private theorem errTail_concrete_sub_bounded {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromErrTailEnv evs) :
    SigTryFromErrTailEnv evs := by
  cases h with
  | nil => exact .nil
  | fromOnly => exact .fromOnly
  | fromPush hp => exact .fromPush hp

private theorem loop_concrete_sub_bounded {rem : Nat}
    {caps : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps}
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromLoopBoundedEnv
      rem caps evs) :
    SigTryFromLoopBoundedEnv rem (mapSigCaps caps) evs := by
  induction h with
  | done ht =>
    exact .done (errTail_concrete_sub_bounded ht)
  | skipStep hlt _ ih =>
    exact .skipStep hlt ih
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm hlen hprog hcap _ ih =>
    rw [← mapSigCaps_get caps f]
    refine .bytesStep (mapSigField f) wt bs v rest hm hlen hprog ?_ ?_
    · rw [mapSigCaps_get]
      exact hcap
    · rw [mapSigCaps_get, ← mapSigCaps_set]
      exact ih

private theorem intoBoxed_concrete_sub_bounded {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.IntoBoxedBoundedEnv bs evs) :
    IntoBoxedBoundedEnv bs evs := by
  rcases h with ⟨cap, h1, h2, rfl⟩
  exact ⟨cap, h1, h2, rfl⟩

private theorem intoBoxedOpt_concrete_sub_bounded {opt : Option (List (BitVec 8))}
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.IntoBoxedOptBoundedEnv
      opt evs) :
    IntoBoxedOptBoundedEnv opt evs := by
  cases opt with
  | none => exact h
  | some ad => exact intoBoxed_concrete_sub_bounded h

private theorem post_concrete_sub_bounded {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.TryFromPostEnv bs evs) :
    SigTryFromPostEnv bs evs := by
  refine seqEnv_mono (fun evs₁ hpre => ?_) (fun _ hf => hf) h
  unfold LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.TryFromPostOutPreEnv at hpre
  unfold SigTryFromPostOutPreEnv
  cases htr : SignalMessage.tryFrom protoSignalCodec bs with
  | error err =>
    rw [htr] at hpre
    exact hpre
  | ok msg =>
    rw [htr] at hpre
    exact seqEnv_mono (fun _ hf => hf)
      (fun _ hok => seqEnv_mono (fun _ hct => intoBoxed_concrete_sub_bounded hct)
        (fun _ hrest => seqEnv_mono (fun _ had => intoBoxedOpt_concrete_sub_bounded had)
          (fun _ hcl => hcl) hrest) hok) hpre

/-- Every event trace in `PreKeyTryFromPostPlacedBBudget.SigTryFromConcreteEnv bs` lies in
`SigTryFromCanonInnerEnv bs`. -/
theorem sigTryFromConcreteEnv_sub_canonInner (bs : List (BitVec 8)) {evs : List AllocEvent}
    (h : SigTryFromConcreteEnv bs evs) :
    SigTryFromCanonInnerEnv bs evs := by
  cases h with
  | nil =>
    exact Or.inl (Or.inl rfl)
  | loopOnly h1 =>
    exact Or.inr (SeqEnv.inl (loop_concrete_sub_bounded h1))
  | loopPost h1 h2 =>
    exact Or.inl (Or.inr (SeqEnv.append (loop_concrete_sub_bounded h1) (post_concrete_sub_bounded h2)))

/-- Monotone lift `PreKeyTryFromEnv SigTryFromConcreteEnv ⊆ PreKeyTryFromEnv SigTryFromCanonInnerEnv`. -/
theorem preKeyTryFromConcrete_sub_canonInner (x : PreKeyTryFromArgs) {evs : List AllocEvent}
    (h : PreKeyTryFromEnv SigTryFromConcreteEnv x evs) :
    PreKeyTryFromEnv SigTryFromCanonInnerEnv x evs :=
  preKeyTryFromEnv_mono (fun bs _ hs => sigTryFromConcreteEnv_sub_canonInner bs hs) x h

/-- Every event list emitted by `PreKeyTryFromOkPlacedBudget.preKeyTryFromPlacedSpec` on canonical
input `x : PreKeyTryFromArgs` with `rest = x.bytes` belongs to `PksmCanonCoreEnv rest`. -/
theorem preKeyTryFromConcrete_sub_pksmCanonCore {x : PreKeyTryFromArgs} {rest : List (BitVec 8)}
    {evs : List AllocEvent} (hrest : rest = x.bytes)
    (h : PreKeyTryFromEnv SigTryFromConcreteEnv x evs) :
    PksmCanonCoreEnv rest evs := by
  refine ⟨preKeyFieldsOfArgs x, hrest, ?_⟩
  rw [preKeyArgsOfFields_of_args, preKeyTryFromEnv_congr_ptrs]
  exact preKeyTryFromConcrete_sub_canonInner x h

/-- Every event list emitted by `PreKeyTryFromOkPlacedBudget.preKeyTryFromPlacedSpec` on canonical
input `x : PreKeyTryFromArgs` (`rest = x.bytes`) belongs to `PksmCanonSliceEnv rest`. -/
theorem preKeyTryFromConcrete_sub_pksmCanonSlice {x : PreKeyTryFromArgs} {rest : List (BitVec 8)}
    {evs : List AllocEvent} (hrest : rest = x.bytes)
    (h : PreKeyTryFromEnv SigTryFromConcreteEnv x evs) :
    PksmCanonSliceEnv rest evs :=
  Or.inr (preKeyTryFromConcrete_sub_pksmCanonCore hrest h)

/-- Direct `PreKeyMessageFields` specialization of `preKeyTryFromConcrete_sub_pksmCanonSlice`. -/
theorem preKeyTryFromConcrete_m_sub_pksmCanonSlice (ptr sret : BitVec 64)
    (m : PreKeyMessageFields) {evs : List AllocEvent}
    (h : PreKeyTryFromEnv SigTryFromConcreteEnv (preKeyArgsOfFields ptr sret m) evs) :
    PksmCanonSliceEnv m.bytes evs :=
  preKeyTryFromConcrete_sub_pksmCanonSlice (preKeyArgsOfFields_bytes ptr sret m).symm h

/-- Contravariant `FitsEnv` transfer from `PksmCanonCoreEnv x.bytes` to Block `111`'s concrete
precondition `FitsEnv M lim st (PreKeyTryFromEnv SigTryFromConcreteEnv x)`. -/
theorem fitsEnv_preKeyTryFromConcrete_of_pksmCanonCore
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {x : PreKeyTryFromArgs}
    (hfit : FitsEnv M lim st (PksmCanonCoreEnv x.bytes)) :
    FitsEnv M lim st (PreKeyTryFromEnv SigTryFromConcreteEnv x) :=
  fun evs hevs => hfit evs (preKeyTryFromConcrete_sub_pksmCanonCore rfl hevs)

/-- Contravariant `FitsEnv` transfer from `PksmCanonSliceEnv x.bytes` to Block `111`'s concrete
precondition `FitsEnv M lim st (PreKeyTryFromEnv SigTryFromConcreteEnv x)`. -/
theorem fitsEnv_preKeyTryFromConcrete_of_pksmCanonSlice
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {x : PreKeyTryFromArgs}
    (hfit : FitsEnv M lim st (PksmCanonSliceEnv x.bytes)) :
    FitsEnv M lim st (PreKeyTryFromEnv SigTryFromConcreteEnv x) :=
  fun evs hevs => hfit evs (preKeyTryFromConcrete_sub_pksmCanonSlice rfl hevs)

/-- Lift any `subroutine_ok` proof for `preKeyTryFromPlacedSpec SigTryFromConcreteEnv` (Block `111`)
to `preKeyTryFromPlacedEnvSpec (fun x => PksmCanonSliceEnv x.bytes)`. -/
theorem subroutine_ok_preKeyTryFromPlaced_canonSlice [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hok : subroutine_ok prog entry (preKeyTryFromPlacedSpec SigTryFromConcreteEnv M A lim)) :
    subroutine_ok prog entry
      (preKeyTryFromPlacedEnvSpec (fun x => PksmCanonSliceEnv x.bytes) M A lim) := by
  refine subroutine_ok_mono hok ?_ ?_
  · rintro ⟨x, st⟩ s0 R hpre
    obtain ⟨hcl, hraw⟩ := extract_withLsCodeLoaded hpre
    dsimp only [preKeyTryFromPlacedSpec, preKeyTryFromPlacedRawSpec, withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    dsimp only [preKeyTryFromPlacedRawEnvSpec] at hraw ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hraw ⊢
    rcases hraw with ⟨⟨hx0, hx1, hlt, hx8, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hlt, hx8, fitsEnv_preKeyTryFromConcrete_of_pksmCanonSlice hfit⟩, hmem⟩
  · rintro ⟨x, st⟩ s0 sf R hpost
    dsimp only [preKeyTryFromPlacedSpec, preKeyTryFromPlacedRawSpec,
      preKeyTryFromPlacedEnvSpec, withLsCodeLoaded, preKeyTryFromPlacedRawEnvSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hevs⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hevs ⊢
    rcases hevs with ⟨⟨htr, hE⟩, hmem⟩
    exact ⟨⟨htr, preKeyTryFromConcrete_sub_pksmCanonSlice rfl hE⟩, hmem⟩

/-- Placed budget subroutine correctness for Block `111` (`PreKeyTryFromOkPlacedBudget`) specialized
directly to `PksmCanonSliceEnv x.bytes` from explicit callee contracts. -/
theorem preKeyTryFrom_placed_ok_of_callees_canonSlice [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withLsCodeLoaded lsmpl (int32MergeSpec A lim)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A lim)))
    (hdealloc : PreKeyDeallocOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hDropSpe : PreKeyDropSpeOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hIntoBox : PreKeyIntoBoxOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hSigTryFrom : PreKeySigTryFromOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hTryClone : PreKeyTryCloneOk (LibsignalCodeLoaded lsmpl) A lim H) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (preKeyTryFromPlacedEnvSpec (fun x => PksmCanonSliceEnv x.bytes) M A lim) :=
  subroutine_ok_preKeyTryFromPlaced_canonSlice
    (preKeyTryFrom_placed_ok_of_callees hint32 hbytes hdealloc hDropSpe hIntoBox hSigTryFrom
      hTryClone)

/-- Placed budget subroutine correctness for Block `111` (`PreKeyTryFromOkPlacedBudget.preKeyTryFrom_placed_ok`,
`:741`) specialized directly to `PksmCanonSliceEnv x.bytes`. -/
theorem preKeyTryFrom_placed_ok_canonSlice [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim_s : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A lim)))
    (hDropSpe : PreKeyDropSpeOk (LibsignalCodeLoaded lsmpl) A lim H)
    (hSigTryFrom : PreKeySigTryFromOk (LibsignalCodeLoaded lsmpl) A lim H) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (preKeyTryFromPlacedEnvSpec (fun x => PksmCanonSliceEnv x.bytes) M A lim) :=
  subroutine_ok_preKeyTryFromPlaced_canonSlice
    (preKeyTryFrom_placed_ok hshim_s hshim halloc hdealloc hrealloc hmemcpy hbytes hDropSpe
      hSigTryFrom)

/-! ## Concrete Allocating Non-Vacuity Witness -/

/-- Concrete canonical `PreKeyMessageFields` witness whose `inner := [0x01#8, 0x42#8]` carries a
valid length-delimited payload (`mergeBytes .lengthDelimited [0x01#8, 0x42#8] = some ([0x42#8], [])`),
driving the allocating `bytes::merge` `94·N` step (`SigTryFromLoopBoundedEnv.bytesStep`). -/
def pksmNonVacFields : PreKeyMessageFields where
  regId := 1#32
  opkId := some 2#32
  spkId := 3#32
  kpkId := 4#32
  kyberCt := List.Vector.replicate 1568 0#8
  baseKey := List.Vector.replicate 32 0#8
  idPub := List.Vector.replicate 32 0#8
  inner := [0x01#8, 0x42#8]

def pksmNonVacArgs : PreKeyTryFromArgs :=
  preKeyArgsOfFields 0#64 0#64 pksmNonVacFields

/-- Inner allocating event trace exercising `SigTryFromLoopBoundedEnv.bytesStep .ct` (`bytes::merge`)
followed by `SigTryFromErrTailEnv.fromOnly` (`.alloc 72`). -/
def pksmNonVacInnerEvs : List AllocEvent :=
  bytesMergeEventsCore .lengthDelimited 0#64 [0x01#8, 0x42#8] ++ rustAllocEvents 72 8

/-- Full allocating trace in `PksmCanonCoreEnv pksmNonVacFields.bytes` exercising:
- outer `preKeyLoopEvents` (4 `bytes::merge` field decodes),
- Seg 2 `into_boxed_slice` on `kyberBytes` at `cap = 2048` (`.realloc 1 2048 1569`),
- Seg 3 `pksmNonVacInnerEvs` (`bytes::merge` `94·N` step + `.alloc 72`),
- Seg 4 `try_clone_from_ref_in` on `pksmNonVacFields.bytes`. -/
def pksmNonVacEvents : List AllocEvent :=
  preKeyLoopEvents pksmNonVacArgs ++
    (intoBoxedSliceEvents ⟨0#64, 2048#64, 0#64, pksmNonVacArgs.kyberBytes⟩ ++
      (pksmNonVacInnerEvs ++ rustAllocEvents pksmNonVacFields.bytes.length 1))

private theorem pksmNonVacInnerEvs_mem :
    SigTryFromCanonInnerEnv pksmNonVacFields.inner pksmNonVacInnerEvs := by
  refine Or.inr (SeqEnv.inl ?_)
  have hm : mergeBytes .lengthDelimited [0x01#8, 0x42#8] = some ([0x42#8], []) := by decide
  exact SigTryFromLoopBoundedEnv.bytesStep (rem := 2) (rem' := 0) (caps := SigTryFromCaps.zero)
    .ct .lengthDelimited [0x01#8, 0x42#8] [0x42#8] []
    hm (by decide) (by decide) (by decide) (SigTryFromLoopBoundedEnv.done .fromOnly)

/-- `pksmNonVacEvents` belongs to `PksmCanonCoreEnv pksmNonVacFields.bytes`. -/
theorem pksmNonVacEvents_mem_core :
    PksmCanonCoreEnv pksmNonVacFields.bytes pksmNonVacEvents := by
  refine ⟨pksmNonVacFields, rfl, ?_⟩
  have hloop : PreKeyLoopEnv pksmNonVacArgs (preKeyLoopEvents pksmNonVacArgs) := rfl
  have hseg2 : PreKeySeg2Env pksmNonVacArgs
      (intoBoxedSliceEvents ⟨0#64, 2048#64, 0#64, pksmNonVacArgs.kyberBytes⟩) :=
    ⟨2048#64, by decide, by decide, rfl⟩
  have hclone : TryCloneFromRefEnv ⟨0#64, pksmNonVacArgs.bytes⟩
      (rustAllocEvents pksmNonVacFields.bytes.length 1) := by
    unfold TryCloneFromRefEnv tryCloneFromRefEvents
    have hne : pksmNonVacArgs.bytes ≠ [] := List.cons_ne_nil _ _
    simp only [hne, ↓reduceIte]
    rfl
  have hseg4 : PreKeySeg4Env pksmNonVacArgs (rustAllocEvents pksmNonVacFields.bytes.length 1) :=
    Or.inr (SeqEnv.inl hclone)
  have hfrom3 : FromSeg3Env SigTryFromCanonInnerEnv pksmNonVacArgs
      (pksmNonVacInnerEvs ++ rustAllocEvents pksmNonVacFields.bytes.length 1) :=
    SeqEnv.append pksmNonVacInnerEvs_mem hseg4
  have hfrom2 : FromSeg2Env SigTryFromCanonInnerEnv pksmNonVacArgs
      (intoBoxedSliceEvents ⟨0#64, 2048#64, 0#64, pksmNonVacArgs.kyberBytes⟩ ++
        (pksmNonVacInnerEvs ++ rustAllocEvents pksmNonVacFields.bytes.length 1)) :=
    SeqEnv.append hseg2 hfrom3
  have hpost : PreKeyPostEnv SigTryFromCanonInnerEnv pksmNonVacArgs
      (intoBoxedSliceEvents ⟨0#64, 2048#64, 0#64, pksmNonVacArgs.kyberBytes⟩ ++
        (pksmNonVacInnerEvs ++ rustAllocEvents pksmNonVacFields.bytes.length 1)) :=
    Or.inr ⟨[], _, rfl, FreeOnlyEvs.nil, hfrom2⟩
  exact SeqEnv.append hloop hpost

/-- `pksmNonVacEvents` belongs to `PksmCanonSliceEnv pksmNonVacFields.bytes`. -/
theorem pksmNonVacEvents_mem_slice :
    PksmCanonSliceEnv pksmNonVacFields.bytes pksmNonVacEvents :=
  Or.inr pksmNonVacEvents_mem_core

private theorem pksmNonVacSeg2_eq :
    intoBoxedSliceEvents ⟨0#64, 2048#64, 0#64, pksmNonVacArgs.kyberBytes⟩ =
      [AllocEvent.realloc 1 2048 1569] := by
  have hlen : pksmNonVacArgs.kyberBytes.length = 1569 :=
    PreKeyTryFromArgs.kyberBytes_length pksmNonVacArgs
  have hcap : ¬ ((2048#64 : BitVec 64).toNat ≤ 1569) := by decide
  have hne : pksmNonVacArgs.kyberBytes ≠ [] := List.cons_ne_nil _ _
  unfold intoBoxedSliceEvents
  simp only [hlen, hcap, hne, ↓reduceIte]
  decide

/-- Kernel-checked confirmation that `pksmNonVacEvents` exercises concrete `.alloc` and `.realloc`
events (not `[]` or `FreeOnlyEvs`). -/
theorem pksmNonVacEvents_allocating :
    AllocEvent.alloc 72 ∈ pksmNonVacEvents ∧
    AllocEvent.realloc 1 2048 1569 ∈ pksmNonVacEvents ∧
    pksmNonVacEvents ≠ [] := by
  have ha72 : AllocEvent.alloc 72 ∈ pksmNonVacInnerEvs := by
    unfold pksmNonVacInnerEvs
    exact List.mem_append_right _ (by decide)
  have ha72' : AllocEvent.alloc 72 ∈ pksmNonVacEvents := by
    unfold pksmNonVacEvents
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ha72))
  have hre : AllocEvent.realloc 1 2048 1569 ∈ pksmNonVacEvents := by
    unfold pksmNonVacEvents
    rw [pksmNonVacSeg2_eq]
    exact List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)
  exact ⟨ha72', hre, List.ne_nil_of_mem ha72'⟩

private theorem pksmNonVacFields_bytes_length_le :
    pksmNonVacFields.bytes.length ≤ msgCapBytes := by
  let x : PreKeyTryFromArgs := pksmNonVacArgs
  have hb : pksmNonVacFields.bytes = x.bytes := rfl
  have henc33 : (encodeVarint 33#64).length = 1 := by decide
  have hf1 : (psmField1 x).length = 2 := by rw [psmField1_some x 2#32 rfl]; decide
  have hf2 : (psmField2 x).length = 35 := by
    rw [psmField2_eq, List.length_cons, List.length_append, henc33, PreKeyTryFromArgs.bkBytes_length]
  have hf3 : (psmField3 x).length = 35 := by
    rw [psmField3_eq, List.length_cons, List.length_append, henc33, PreKeyTryFromArgs.ikBytes_length]
  have hf4 : (psmField4 x).length = 4 := by rw [psmField4_eq x (by decide)]; decide
  have hf5 : (psmField5 x).length = 2 := by rw [psmField5_eq]; decide
  have hf6 : (psmField6 x).length = 2 := by rw [psmField6_eq]; decide
  have hf7 : (psmField7 x).length = 2 := by rw [psmField7_eq]; decide
  have hf8 : (psmField8 x).length = 1572 := by
    rw [psmField8_eq, encodeVarint_1569, List.length_cons, List.length_append,
      PreKeyTryFromArgs.kyberBytes_length]
    decide
  rw [hb, PreKeyTryFromArgs.bytes, List.length_cons, protoBytes_eq_psmRem0]
  simp only [psmRem0, psmRem1, psmRem2, psmRem3, psmRem4, psmRem5, psmRem6, psmRem7, psmRem8,
    List.length_append, List.length_nil, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, msgCapBytes]
  decide

/-- Concrete `FitsEnv fineCostModel cliBudgetLimits` witness for `PksmCanonSliceEnv` on
`pksmNonVacFields.bytes`. -/
theorem pksmNonVacSlice_fitsEnv_cliBudgetLimits :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (PksmCanonSliceEnv pksmNonVacFields.bytes) := by
  have hlen : pksmNonVacFields.bytes.length ≤ msgCapBytes := pksmNonVacFields_bytes_length_le
  have hcr := pksmCanonSlice_fine_phaseCredit hlen
  have hgr := pksmCanonSlice_fine_groupSpec hlen
  exact fitsEnv_oneGiB_of_group_bounds_S4 (lim := cliBudgetLimits) hcr hgr
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-! ## Outer `W4SlotR3bCanonEnv`, `CliRunCanonTightEnv`, & `CliMainEnv` Corollaries -/

/-! ### 5.1 Outer `SlotW4` / `R3b` Canonical Wire + Slot Composition -/

/-- Canonical-outer `R3b` envelope `R3bEnv (PksmCanonSliceEnv rest) DecPkEnv`. -/
def W4SlotR3bCanonEnv (rest : List (BitVec 8)) (DecPkEnv : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  R3bEnv (PksmCanonSliceEnv rest) DecPkEnv evs

def w4SlotR3bCanonDeltaCum (stdinCap decCum : Nat) : Nat :=
  pksmCanonSliceCum stdinCap + decCum

def w4SlotR3bCanonDeltaLive (stdinCap decLive : Nat) : Nat :=
  pksmCanonSliceLive stdinCap + decLive

def w4SlotR3bCanonDeltaPeak (stdinCap decLive decPeak : Nat) : Nat :=
  max
    (max (pksmCanonSlicePeak stdinCap) (pksmCanonSliceLive stdinCap + decPeak))
    (w4SlotR3bCanonDeltaLive stdinCap decLive)

def w4SlotR3bCanonMaxReq (stdinCap decMaxReq : Nat) : Nat :=
  max (pksmCanonSliceMaxReq stdinCap) decMaxReq

theorem w4SlotR3bCanon_live_le_peak (stdinCap decLive decPeak : Nat) :
    w4SlotR3bCanonDeltaLive stdinCap decLive ≤
      w4SlotR3bCanonDeltaPeak stdinCap decLive decPeak :=
  Nat.le_max_right _ _

/-- `PhaseCreditSpec` for `W4SlotR3bCanonEnv rest DecPkEnv`. -/
theorem w4SlotR3bCanon_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M)
    {rest : List (BitVec 8)} {stdinCap : Nat} (hrest : rest.length ≤ stdinCap)
    {DecPkEnv : List AllocEvent → Prop} {decCum decLive decPeak decMaxReq : Nat}
    (hDec : PhaseCreditSpec M DecPkEnv decCum decLive decPeak decMaxReq) :
    PhaseCreditSpec M (W4SlotR3bCanonEnv rest DecPkEnv)
      (w4SlotR3bCanonDeltaCum stdinCap decCum)
      (w4SlotR3bCanonDeltaLive stdinCap decLive)
      (w4SlotR3bCanonDeltaPeak stdinCap decLive decPeak)
      (w4SlotR3bCanonMaxReq stdinCap decMaxReq) := by
  have hFree : PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 := PhaseCreditSpec.freeOnly_of_hyps hM
  have hPksm := pksmCanonSlice_phaseCredit hM hLow hrest
  have hDecFree := phaseCreditSpec_seq_freeOnly_right hM hDec
  have hSeq := hPksm.seq (hFree.or hDecFree)
  refine (hFree.or hSeq).mono ?_ ?_ ?_ ?_
  · unfold w4SlotR3bCanonDeltaCum; simp only [Nat.zero_max]; exact Nat.le_refl _
  · unfold w4SlotR3bCanonDeltaLive; simp only [Nat.zero_max]; exact Nat.le_refl _
  · unfold w4SlotR3bCanonDeltaPeak w4SlotR3bCanonDeltaLive
    omega
  · unfold w4SlotR3bCanonMaxReq; simp only [Nat.zero_max]; exact Nat.le_refl _

/-- `fineCostModel` specialization of `w4SlotR3bCanon_phaseCredit` (`0` `*Hyps` binders). -/
theorem w4SlotR3bCanon_fine_phaseCredit
    {rest : List (BitVec 8)} {stdinCap : Nat} (hrest : rest.length ≤ stdinCap)
    {DecPkEnv : List AllocEvent → Prop} {decCum decLive decPeak decMaxReq : Nat}
    (hDec : PhaseCreditSpec fineCostModel DecPkEnv decCum decLive decPeak decMaxReq) :
    PhaseCreditSpec fineCostModel (W4SlotR3bCanonEnv rest DecPkEnv)
      (w4SlotR3bCanonDeltaCum stdinCap decCum)
      (w4SlotR3bCanonDeltaLive stdinCap decLive)
      (w4SlotR3bCanonDeltaPeak stdinCap decLive decPeak)
      (w4SlotR3bCanonMaxReq stdinCap decMaxReq) :=
  w4SlotR3bCanon_phaseCredit fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps hrest hDec

/-- `PhaseGroupSpec fineCostModel` for `W4SlotR3bCanonEnv rest DecPkEnv` (`R3bEnv`). -/
theorem w4SlotR3bCanon_fine_groupSpec
    {rest : List (BitVec 8)} {DecPkEnv : List AllocEvent → Prop}
    {stdinCap g_decPk : Nat} (hrest : rest.length ≤ stdinCap)
    (hdec : PhaseGroupSpec fineCostModel DecPkEnv g_decPk) :
    PhaseGroupSpec fineCostModel (W4SlotR3bCanonEnv rest DecPkEnv)
      (pksmCanonSliceGrpS stdinCap + g_decPk) := by
  have htail := ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((hdec.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (Nat.le_of_eq (Nat.add_zero _)))).mono (freeOr_zero_left _)
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or
    ((pksmCanonSlice_fine_groupSpec hrest).seq htail)).mono
    (freeOr_zero_left _)

/-- Kernel-checked `1 MiB` `R3b` Path-A (`205,347,739` B) profile with `PksmCanonSliceEnv`
(`308,580,004` B vs `409,703,415` B on unmodified `PksmTryFromSliceEnv`). -/
theorem r3bCanonArm1MiB_c09bTight_deser0_profile_eq :
    pksmCanonSliceCum msgCapBytes + 205347739 = 308580004 ∧
    pksmCanonSliceTightInnerCum msgCapBytes + 205347739 = 308388064 ∧
    pksmCanonSliceLive msgCapBytes + 34901913 = 43364308 ∧
    max (pksmCanonSlicePeak msgCapBytes) (pksmCanonSliceLive msgCapBytes + 34901913) = 43364308 ∧
    max (pksmCanonSliceMaxReq msgCapBytes) 3407872 = 3407872 := by
  decide

/-- Direct `CliPqxdhInputs` pre-key `recv` trace bridge into `W4SlotR3bCanonEnv rest DecPkEnv`:
if `i` is in `CliPqxdhInputs W i`, `argv` parses as `recv peer`, `stdin = 3#8 :: rest`, and Block `111`
emits `evs₁` on the canonical `PreKeyMessageFields` input `m` (`rest = m.bytes`) followed by
`evs₂` in `FreeOnlyEvs` or `SeqEnv DecPkEnv FreeOnlyEvs`, then `evs₁ ++ evs₂` lies in
`W4SlotR3bCanonEnv rest DecPkEnv`. -/
theorem r3bEnv_canon_of_cliPqInputs_recv_prekey
    {W : PEParams} {i : Inputs} {peer : AddrV} {rest : List (BitVec 8)}
    {DecPkEnv : List AllocEvent → Prop} {ptr sret : BitVec 64}
    {evs₁ evs₂ : List AllocEvent}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hst : i.stdin = 3#8 :: rest)
    (hpksm : ∀ m : PreKeyMessageFields, rest = m.bytes →
      PreKeyTryFromEnv SigTryFromConcreteEnv (preKeyArgsOfFields ptr sret m) evs₁)
    (htail : FreeOnlyEvs evs₂ ∨ SeqEnv DecPkEnv FreeOnlyEvs evs₂) :
    W4SlotR3bCanonEnv rest DecPkEnv (evs₁ ++ evs₂) := by
  obtain ⟨m, hm, _⟩ := cliPqInputs_recv_prekey_canonical hi hparse hst
  refine Or.inr (SeqEnv.append ?_ htail)
  rw [hm]
  exact preKeyTryFromConcrete_m_sub_pksmCanonSlice ptr sret m (hpksm m hm)

/-! ### `CliRunCalleeEnvs`, `CliRunOpenedEnv`, & `CliRunCanonTightEnv` Corollaries -/

/-- Sibling of `CliRunWrapperEnvs.toCalleeEnvs` (`CliRunArmsPeak.lean:1537`) wiring
`PksmCanonSliceEnv` in place of `PksmTryFromSliceEnv`. -/
def toCanonCalleeEnvs (W : CliRunWrapperEnvs) : CliRunCalleeEnvs where
  initEnv := W.initEnv
  encEnv := W.encEnv
  decSigEnv := W.decSigEnv
  pksmEnv := PksmCanonSliceEnv
  decPkEnv := W.decPkEnv

/-- Sibling of `CliRunWrapperSlotSpecs.toCalleeSpecs` (`CliRunArmsPeak.lean:1559`) wiring
`pksmCanonSlice_phaseCredit` (`103,232,265` B at `1 MiB`) into `CliRunSlotCalleeSpecs`. -/
def toCanonCalleeSpecs {M : AllocCostModel} [HasFineReallocCredit M]
    {W : CliRunWrapperEnvs} (SW : CliRunWrapperSlotSpecs M W)
    (hM : ModelHyps M) (hLow : WireLowInterceptHyps M) (stdinCap : Nat) :
    CliRunSlotCalleeSpecs M (toCanonCalleeEnvs W) stdinCap where
  initCum := SW.initCum
  initLive := SW.initLive
  initPeak := SW.initPeak
  initMaxReq := SW.initMaxReq
  init_spec := SW.init_spec
  init_lp := SW.init_lp
  encCum := SW.encCum
  encLive := SW.encLive
  encPeak := SW.encPeak
  encMaxReq := SW.encMaxReq
  enc_spec := SW.enc_spec
  enc_lp := SW.enc_lp
  decSigCum := SW.decSigCum
  decSigLive := SW.decSigLive
  decSigPeak := SW.decSigPeak
  decSigMaxReq := SW.decSigMaxReq
  decSig_spec := SW.decSig_spec
  decSig_lp := SW.decSig_lp
  pksmCum := pksmCanonSliceCum stdinCap
  pksmLive := pksmCanonSliceLive stdinCap
  pksmPeak := pksmCanonSlicePeak stdinCap
  pksmMaxReq := pksmCanonSliceMaxReq stdinCap
  pksm_spec := fun _ hrest => pksmCanonSlice_phaseCredit hM hLow hrest
  pksm_lp := pksmCanonSliceLive_le_peak stdinCap
  decPkCum := SW.decPkCum
  decPkLive := SW.decPkLive
  decPkPeak := SW.decPkPeak
  decPkMaxReq := SW.decPkMaxReq
  decPk_spec := SW.decPk_spec
  decPk_lp := SW.decPk_lp

/-- Sibling of `CliRunTightEnvOf` (`CliRunPeakSpec.lean:1059`) using `toCanonCalleeEnvs`. -/
abbrev CliRunCanonTightEnvOf (W : RunCall → CliRunWrapperEnvs) (wireOutCap : Nat)
    (g : RunCall) (evs : List AllocEvent) : Prop :=
  CliRunOpenedEnv cliIo.rd (toCanonCalleeEnvs (W g)) wireOutCap g evs

/-- Sibling of `CliRunTightEnv` (`CliRunPeakSpec.lean:1064`) at `wireOutCap = sessionCapBytes`
(`2 MiB`), using `PksmCanonSliceEnv` on `recv` tag `3#8`. -/
abbrev CliRunCanonTightEnv (W : RunCall → CliRunWrapperEnvs)
    (g : RunCall) (evs : List AllocEvent) : Prop :=
  CliRunCanonTightEnvOf W sessionCapBytes g evs

/-- Sibling of `cliRun_slots_tight_phaseCredit` (`CliRunArmsPeak.lean:1690`) for `toCanonCalleeEnvs`. -/
theorem cliRunCanon_slots_tight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {W : CliRunWrapperEnvs}
    {g : RunCall} {stdinCap maxInitDir fileCap bundleCap : Nat}
    (SW : CliRunWrapperSlotSpecs M W) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    let S := toCanonCalleeSpecs SW hM hLow stdinCap
    PhaseCreditSpec M
      (CliRunEnv uuidTryParse rd StoresGhost.opened.identity.own (toCanonCalleeEnvs W) wireOutCap g)
      (cliRunTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunDeltaLive S maxInitDir fileCap wireOutCap)
      (cliRunDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRun_tight_phaseCredit hM hT hLow (toCanonCalleeSpecs SW hM hLow stdinCap) wireOutCap
    hstdin hownCap hinitDir

/-- Sibling of `cliRunOpened_slots_tight_phaseCredit` (`CliRunArmsPeak.lean:1710`) for
`toCanonCalleeEnvs`. -/
theorem cliRunCanonOpened_slots_tight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {rd : ReadRule} {W : CliRunWrapperEnvs}
    {g : RunCall} {stdinCap maxInitDir fileCap bundleCap : Nat}
    (SW : CliRunWrapperSlotSpecs M W) (wireOutCap : Nat)
    (hstdin : g.i.stdin.length ≤ stdinCap)
    (hownCap : ∀ bs,
      rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = .ok bs →
      bs.length ≤ fileCap)
    (hinitDir : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    let S := toCanonCalleeSpecs SW hM hLow stdinCap
    PhaseCreditSpec M (CliRunOpenedEnv rd (toCanonCalleeEnvs W) wireOutCap g)
      (cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) := by
  exact cliRunOfR0_tight_phaseCredit_of_callees hM hT
    (toCanonCalleeSpecs SW hM hLow stdinCap) wireOutCap
    (r0Opened_phaseCredit_of_path hM
      (path_phaseCredit hM dirDomainCaps_opened_own.path_len_le utf8_address_length_le) hownCap)
    hstdin (initBundlePaths_phaseCredit hM hinitDir)
    (fun _ hrest => sigTryFromSlice_phaseCredit hM hLow hrest)

/-- Sibling of `cliRunTight_phaseCredit` (`CliRunPeakSpec.lean:1085`) for `CliRunCanonTightEnvOf`. -/
theorem cliRunCanonTight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap wireOutCap : Nat}
    (SW : CliRunWrapperSlotSpecs M (W g))
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (hspqr : CliRunSpqrAndInitCaps maxInitDir bundleCap g) :
    let S := toCanonCalleeSpecs SW hM hLow stdinCap
    PhaseCreditSpec M (CliRunCanonTightEnvOf W wireOutCap g)
      (cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunCanonOpened_slots_tight_phaseCredit hM hT hLow SW wireOutCap
    hcaps.stdin_le
    (fun bs hrd => cliIo_rd_runFiles_length_le_of_filesBounded hcaps.files_bounded _ bs hrd)
    hspqr.init_caps

/-- `fineCostModel` specialization of `cliRunCanonTight_phaseCredit` (`0` `*Hyps` binders). -/
theorem cliRunCanonTight_phaseCredit_fine
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap wireOutCap : Nat}
    (SW : CliRunWrapperSlotSpecs fineCostModel (W g))
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (hspqr : CliRunSpqrAndInitCaps maxInitDir bundleCap g) :
    let S := toCanonCalleeSpecs SW fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps
      stdinCap
    PhaseCreditSpec fineCostModel (CliRunCanonTightEnvOf W wireOutCap g)
      (cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunCanonTight_phaseCredit fineCostModel_modelHyps fineCostModel_cliRunTightHyps
    fineCostModel_wireLowInterceptHyps SW hcaps hspqr

/-! ### 5.3 `1 MiB` Closed-Form Slot Profile & `PhaseGroupSpec` for `CliRunCanonTightEnv` -/

def cliRunCanon1MiBSlotCum (initCum encCum decSigCum decPkCum : Nat) : Nat :=
  r0Opened1MiBCum +
    max (initArmDeltaCum (pathDeltaCum 26 16) 1637 initCum)
      (max (r2TightDeltaCum encCum sessionCapBytes)
        (max (sigSliceCum msgCapBytes + decSigCum)
          (pksmCanonSliceCum msgCapBytes + decPkCum)))

def cliRunCanon1MiBSlotLive (initLive encLive decSigLive decPkLive : Nat) : Nat :=
  r0Opened1MiBLive +
    max (initArmDeltaLive (pathDeltaLive 26 16) initLive)
      (max (r2DeltaLive fineCostModel encLive sessionCapBytes)
        (max (sigSliceLive msgCapBytes + decSigLive)
          (pksmCanonSliceLive msgCapBytes + decPkLive)))

def cliRunCanon1MiBSlotPeak (initPeak encLive encPeak decSigPeak decPkPeak : Nat) : Nat :=
  max r0Opened1MiBPeak
    (r0Opened1MiBLive +
      max (initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 initPeak)
        (max (r2DeltaPeak fineCostModel encLive encPeak sessionCapBytes)
          (max (max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + decSigPeak))
            (max (pksmCanonSlicePeak msgCapBytes) (pksmCanonSliceLive msgCapBytes + decPkPeak)))))

def cliRunCanon1MiBSlotMaxReq (initMaxReq encMaxReq decSigMaxReq decPkMaxReq : Nat) : Nat :=
  max r0Opened1MiBMaxReq
    (max (initArmMaxReq (pathMaxReq 26 16) 1637 initMaxReq)
      (max (r2MaxReq encMaxReq sessionCapBytes)
        (max (max (sigSliceMaxReq msgCapBytes) decSigMaxReq)
          (max (pksmCanonSliceMaxReq msgCapBytes) decPkMaxReq))))

/-- Definitional bridge showing `cliRunOpenedTightDelta*` on `toCanonCalleeSpecs` at `1 MiB` equal
`cliRunCanon1MiBSlot*` (`rfl`). -/
theorem cliRunCanonOpened_1MiB_eq_slotProfile {W : CliRunWrapperEnvs}
    (SW : CliRunWrapperSlotSpecs fineCostModel W) :
    let S := toCanonCalleeSpecs SW fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps
      msgCapBytes
    cliRunOpenedTightDeltaCum S 26 sessionCapBytes 1637 sessionCapBytes =
      cliRunCanon1MiBSlotCum SW.initCum SW.encCum SW.decSigCum SW.decPkCum ∧
    cliRunOpenedDeltaLive S 26 sessionCapBytes =
      cliRunCanon1MiBSlotLive SW.initLive SW.encLive SW.decSigLive SW.decPkLive ∧
    cliRunOpenedDeltaPeak S 26 sessionCapBytes 1637 sessionCapBytes =
      cliRunCanon1MiBSlotPeak SW.initPeak SW.encLive SW.encPeak SW.decSigPeak SW.decPkPeak ∧
    cliRunOpenedMaxReq S 26 sessionCapBytes 1637 sessionCapBytes =
      cliRunCanon1MiBSlotMaxReq SW.initMaxReq SW.encMaxReq SW.decSigMaxReq SW.decPkMaxReq :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Witness-free `1 MiB` `PhaseCreditSpec fineCostModel` for `CliRunCanonTightEnv W g` from
`CliRunFineSlotSpecs`. -/
theorem cliRunCanonTight_1MiB_fine_phaseCredit
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    (SW : CliRunFineSlotSpecs (W g))
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g) :
    PhaseCreditSpec fineCostModel (CliRunCanonTightEnv W g)
      (cliRunCanon1MiBSlotCum SW.initCum SW.encCum SW.decSigCum SW.decPkCum)
      (cliRunCanon1MiBSlotLive SW.initLive SW.encLive SW.decSigLive SW.decPkLive)
      (cliRunCanon1MiBSlotPeak SW.initPeak SW.encLive SW.encPeak SW.decSigPeak SW.decPkPeak)
      (cliRunCanon1MiBSlotMaxReq SW.initMaxReq SW.encMaxReq SW.decSigMaxReq SW.decPkMaxReq) :=
  cliRunCanonTight_phaseCredit_fine SW.toWrapperSlotSpecs hcaps hspqr

/-- `PhaseGroupSpec fineCostModel` for `RecvArmEnv stdin DecSigEnv PksmCanonSliceEnv DecPkEnv`. -/
theorem recvArmEnv_canon_fine_groupSpec {stdin : List (BitVec 8)}
    {DecSigEnv DecPkEnv : List AllocEvent → Prop}
    {stdinCap g_decSig g_decPk : Nat}
    (hstdin : stdin.length ≤ stdinCap)
    (hdecSig : PhaseGroupSpec fineCostModel DecSigEnv g_decSig)
    (hdecPk : PhaseGroupSpec fineCostModel DecPkEnv g_decPk) :
    PhaseGroupSpec fineCostModel
      (RecvArmEnv stdin DecSigEnv PksmCanonSliceEnv DecPkEnv)
      (max (sigTryFromCapDeltaGrpS stdinCap + g_decSig)
        (pksmCanonSliceGrpS stdinCap + g_decPk)) := by
  unfold RecvArmEnv
  rcases stdin with _ | ⟨b, rest⟩
  · exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  · have hrest : rest.length ≤ stdinCap := Nat.le_of_succ_le hstdin
    by_cases hb2 : b = 2#8
    · simp only [hb2, ↓reduceIte]
      exact (r3aEnv_fine_groupSpec hrest hdecSig).mono (Nat.le_max_left _ _)
    · simp only [hb2, ↓reduceIte]
      by_cases hb3 : b = 3#8
      · simp only [hb3, ↓reduceIte]
        exact (w4SlotR3bCanon_fine_groupSpec hrest hdecPk).mono (Nat.le_max_right _ _)
      · simp only [hb3, ↓reduceIte]
        exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)

def cliRunCanonArmFineGrpS (stdinCap g_init g_enc g_decSig g_decPk : Nat) : Nat :=
  max (84 * FineScale + g_init)
    (max (g_enc + 3 * FineScale)
      (max (sigTryFromCapDeltaGrpS stdinCap + g_decSig)
        (pksmCanonSliceGrpS stdinCap + g_decPk)))

def cliRunCanonOpenedFineGrpS (stdinCap g_init g_enc g_decSig g_decPk : Nat) : Nat :=
  15 * FineScale + cliRunCanonArmFineGrpS stdinCap g_init g_enc g_decSig g_decPk

/-- Sibling of `cliRunTight_fine_groupSpec` (`CliTopBudgetSpec`) for `CliRunCanonTightEnvOf`. -/
theorem cliRunCanonTight_fine_groupSpec
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap wireOutCap : Nat}
    (SW : CliRunFineSlotSpecs (W g))
    (hstdin : g.i.stdin.length ≤ stdinCap) :
    PhaseGroupSpec fineCostModel (CliRunCanonTightEnvOf W wireOutCap g)
      (cliRunCanonOpenedFineGrpS stdinCap SW.initGrpS SW.encGrpS SW.decSigGrpS SW.decPkGrpS) := by
  have hr0 := r0OpenedEnv_fine_groupSpec cliIo.rd (runFiles g.i)
  have harm : PhaseGroupSpec fineCostModel
      (RunArmEnv cliIo.rd (runFiles g.i) (toCanonCalleeEnvs (W g)) wireOutCap g.i.stdin g.c)
      (cliRunCanonArmFineGrpS stdinCap SW.initGrpS SW.encGrpS SW.decSigGrpS SW.decPkGrpS) := by
    unfold RunArmEnv cliRunCanonArmFineGrpS toCanonCalleeEnvs
    cases g.c with
    | keygen _ _ =>
      exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    | init _ dir =>
      exact (initArmEnv_fine_groupSpec cliIo.rd (runFiles g.i) dir SW.init_grp).mono
        (Nat.le_max_left _ _)
    | send _ =>
      exact (r2Env_fine_groupSpec wireOutCap SW.enc_grp).mono
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    | recv _ =>
      exact (recvArmEnv_canon_fine_groupSpec hstdin SW.decSig_grp SW.decPk_grp).mono
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  exact cliRunOfR0_fine_groupSpec hr0 harm

/-! ### Whole-`main` (`CliMainEnv`) Corollaries for `CliRunCanonTightEnv` -/

/-- Sibling of `cliMain_with_cliRunTight_phaseCredit` (`CliRunPeakSpec.lean:1171`) for
`CliRunCanonTightEnvOf`. -/
theorem cliMain_with_cliRunCanonTight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap wireOutCap maxDir maxName : Nat}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SW : CliRunWrapperSlotSpecs M (W g))
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (hspqr : CliRunSpqrAndInitCaps maxInitDir bundleCap g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ 64)
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName) :
    let S := toCanonCalleeSpecs SW hM hLow stdinCap
    let runCum := cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap
    let runLive := cliRunOpenedDeltaLive S maxInitDir wireOutCap
    let runPeak := cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap
    let runMaxReq := cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap
    PhaseCreditSpec M
      (CliMainEnv uuidParse (CliRunCanonTightEnvOf W wireOutCap) g addrOpt needStdin dirs ok)
      (cliMainDeltaCum stdinCap fileCap runCum ((dirs.map (fun dn => dn.2.length)).sum) maxDir maxName)
      (cliMainDeltaLive stdinCap fileCap runLive)
      (cliMainDeltaPeak stdinCap fileCap runLive runPeak maxDir maxName)
      (cliMainMaxReq stdinCap fileCap runMaxReq maxDir maxName) :=
  cliMain_phaseCredit hM hcaps haddr hdirs (cliRunCanonTight_phaseCredit hM hT hLow SW hcaps hspqr)

/-- Combined whole-`main` `PhaseCreditSpec` + `PhaseGroupSpec` on `fineCostModel` for
`CliMainEnv uuidParse (CliRunCanonTightEnv W)` (`0` `*Hyps` binders). -/
theorem cliMain_with_cliRunCanonTight_fine_credit_and_groups
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SW : CliRunFineSlotSpecs (W g))
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    let runCum := cliRunCanon1MiBSlotCum SW.initCum SW.encCum SW.decSigCum SW.decPkCum
    let runLive := cliRunCanon1MiBSlotLive SW.initLive SW.encLive SW.decSigLive SW.decPkLive
    let runPeak := cliRunCanon1MiBSlotPeak SW.initPeak SW.encLive SW.encPeak SW.decSigPeak SW.decPkPeak
    let runMaxReq := cliRunCanon1MiBSlotMaxReq SW.initMaxReq SW.encMaxReq SW.decSigMaxReq SW.decPkMaxReq
    let runGrpS := cliRunCanonOpenedFineGrpS msgCapBytes SW.initGrpS SW.encGrpS SW.decSigGrpS SW.decPkGrpS
    PhaseCreditSpec fineCostModel
      (CliMainEnv uuidParse (CliRunCanonTightEnv W) g addrOpt needStdin dirs ok)
      (cliMainTightCumOf runCum)
      (cliMainTightLiveOf runLive)
      (cliMainTightPeakOf runLive runPeak)
      (cliMainTightReqOf runMaxReq) ∧
    PhaseGroupSpec fineCostModel
      (CliMainEnv uuidParse (CliRunCanonTightEnv W) g addrOpt needStdin dirs ok)
      (cliMainTightGrpSOf runGrpS) :=
  cliMain_fine_credit_and_groups_of_run hcaps haddr hdirs
    (cliRunCanonTight_1MiB_fine_phaseCredit SW hcaps hspqr)
    (cliRunCanonTight_fine_groupSpec (wireOutCap := sessionCapBytes) SW hcaps.stdin_le)

/-- Parametric-cap whole-`main` `FitsTrace fineCostModel` for `CliRunCanonTightEnv W`. -/
theorem cliMain_canon_fitsTrace_of_runCap
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {runCumCap runLiveCap runPeakCap runReqCap runGrpSCap : Nat}
    (SW : CliRunFineSlotSpecs (W g))
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    (hrc : cliRunCanon1MiBSlotCum SW.initCum SW.encCum SW.decSigCum SW.decPkCum ≤ runCumCap)
    (hrl : cliRunCanon1MiBSlotLive SW.initLive SW.encLive SW.decSigLive SW.decPkLive ≤ runLiveCap)
    (hrp : cliRunCanon1MiBSlotPeak SW.initPeak SW.encLive SW.encPeak SW.decSigPeak SW.decPkPeak ≤ runPeakCap)
    (hrr : cliRunCanon1MiBSlotMaxReq SW.initMaxReq SW.encMaxReq SW.decSigMaxReq SW.decPkMaxReq ≤ runReqCap)
    (hrg : cliRunCanonOpenedFineGrpS msgCapBytes SW.initGrpS SW.encGrpS SW.decSigGrpS SW.decPkGrpS ≤ runGrpSCap)
    (hramCap : cliMainTightRamNeedOf runCumCap runLiveCap runPeakCap runReqCap runGrpSCap ≤ cliOneGiB)
    (hvaCap : cliMainTightVaNeedOf runCumCap runLiveCap runPeakCap runReqCap runGrpSCap ≤ 2 ^ 48)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunCanonTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim (cliMainTightStepReserveOf runReqCap runGrpSCap) fullLog :=
  cliMain_fitsTrace_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs
    (cliRunCanonTight_1MiB_fine_phaseCredit SW hcaps hspqr)
    (cliRunCanonTight_fine_groupSpec (wireOutCap := sessionCapBytes) SW hcaps.stdin_le)
    hrc hrl hrp hrr hrg hramCap hvaCap hEnv

/-- Parametric-cap whole-`main` `FitsEnv fineCostModel` for `CliRunCanonTightEnv W`. -/
theorem cliMain_canon_fitsEnv_of_runCap
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {runCumCap runLiveCap runPeakCap runReqCap runGrpSCap : Nat}
    (SW : CliRunFineSlotSpecs (W g))
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    (hrc : cliRunCanon1MiBSlotCum SW.initCum SW.encCum SW.decSigCum SW.decPkCum ≤ runCumCap)
    (hrl : cliRunCanon1MiBSlotLive SW.initLive SW.encLive SW.decSigLive SW.decPkLive ≤ runLiveCap)
    (hrp : cliRunCanon1MiBSlotPeak SW.initPeak SW.encLive SW.encPeak SW.decSigPeak SW.decPkPeak ≤ runPeakCap)
    (hrr : cliRunCanon1MiBSlotMaxReq SW.initMaxReq SW.encMaxReq SW.decSigMaxReq SW.decPkMaxReq ≤ runReqCap)
    (hrg : cliRunCanonOpenedFineGrpS msgCapBytes SW.initGrpS SW.encGrpS SW.decSigGrpS SW.decPkGrpS ≤ runGrpSCap)
    (hramCap : cliMainTightRamNeedOf runCumCap runLiveCap runPeakCap runReqCap runGrpSCap ≤ cliOneGiB)
    (hvaCap : cliMainTightVaNeedOf runCumCap runLiveCap runPeakCap runReqCap runGrpSCap ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunCanonTightEnv W) g addrOpt needStdin dirs ok) :=
  cliMain_fitsEnv_of_runFineBounds henf hsb hsc hcap hcaps haddr hdirs
    (cliRunCanonTight_1MiB_fine_phaseCredit SW hcaps hspqr)
    (cliRunCanonTight_fine_groupSpec (wireOutCap := sessionCapBytes) SW hcaps.stdin_le)
    hrc hrl hrp hrr hrg hramCap hvaCap

def cliUnifiedCanonDeserRunCumCap (dc : Nat) : Nat :=
  cliRunCanon1MiBSlotCum
    (cliInitSlotCumCap + dc)
    (cliSendSlotCumCap + dc)
    (cliRecvWhisperSlotCumCap + dc)
    (cliRecvPrekeySlotCumCap + dc)

def cliUnifiedCanonDeserRunLiveCap (dl : Nat) : Nat :=
  cliRunCanon1MiBSlotLive
    (cliInitSlotLiveCap + dl)
    (cliSendSlotLiveCap + dl)
    (cliRecvWhisperSlotLiveCap + dl)
    (cliRecvPrekeySlotLiveCap + dl)

def cliUnifiedCanonDeserRunPeakCap (dl dp : Nat) : Nat :=
  cliRunCanon1MiBSlotPeak
    (cliInitSlotPeakCap + dp)
    (cliSendSlotLiveCap + dl)
    (cliSendSlotPeakCap + dp)
    (cliRecvWhisperSlotPeakCap + dp)
    (cliRecvPrekeySlotPeakCap + dp)

def cliUnifiedCanonDeserRunReqCap (dr : Nat) : Nat :=
  cliRunCanon1MiBSlotMaxReq
    (max cliInitSlotReqCap dr)
    (max cliSendSlotReqCap dr)
    (max cliRecvWhisperSlotReqCap dr)
    (max cliRecvPrekeySlotReqCap dr)

def cliUnifiedCanonDeserRunGrpSCap (dg : Nat) : Nat :=
  cliRunCanonOpenedFineGrpS msgCapBytes
    (cliInitSlotGrpSCap + dg)
    (cliSendSlotGrpSCap + dg)
    (cliRecvWhisperSlotGrpSCap + dg)
    (cliRecvPrekeySlotGrpSCap + dg)

def cliMainCanonStepReserve : Nat :=
  cliMainTightStepReserveOf (cliUnifiedCanonDeserRunReqCap 0) (cliUnifiedCanonDeserRunGrpSCap 0)

def cliMainCanonDeserParamStepReserve : Nat :=
  cliMainTightStepReserveOf
    (cliUnifiedCanonDeserRunReqCap cliDeserMaxReq)
    (cliUnifiedCanonDeserRunGrpSCap cliDeserMaxGrpS)

private theorem max4_le_max4 {a1 a2 b1 b2 c1 c2 d1 d2 : Nat}
    (ha : a1 ≤ a2) (hb : b1 ≤ b2) (hc : c1 ≤ c2) (hd : d1 ≤ d2) :
    max a1 (max b1 (max c1 d1)) ≤ max a2 (max b2 (max c2 d2)) :=
  max_le_max ha (max_le_max hb (max_le_max hc hd))

private theorem cliUnifiedCanonDeser_bounds_mono
    {dc dl dp dr dg : Nat} {W : CliRunWrapperEnvs} {SW : CliRunFineSlotSpecs W}
    (hCaps : CliRunDeserParamSlotCaps dc dl dp dr dg SW) :
    cliRunCanon1MiBSlotCum SW.initCum SW.encCum SW.decSigCum SW.decPkCum ≤
      cliUnifiedCanonDeserRunCumCap dc ∧
    cliRunCanon1MiBSlotLive SW.initLive SW.encLive SW.decSigLive SW.decPkLive ≤
      cliUnifiedCanonDeserRunLiveCap dl ∧
    cliRunCanon1MiBSlotPeak SW.initPeak SW.encLive SW.encPeak SW.decSigPeak SW.decPkPeak ≤
      cliUnifiedCanonDeserRunPeakCap dl dp ∧
    cliRunCanon1MiBSlotMaxReq SW.initMaxReq SW.encMaxReq SW.decSigMaxReq SW.decPkMaxReq ≤
      cliUnifiedCanonDeserRunReqCap dr ∧
    cliRunCanonOpenedFineGrpS msgCapBytes SW.initGrpS SW.encGrpS SW.decSigGrpS SW.decPkGrpS ≤
      cliUnifiedCanonDeserRunGrpSCap dg := by
  rcases hCaps with
    ⟨hic, hil, hip, hir, hig,
     hec, hel, hep, her, heg,
     hsc, hsl, hsp, hsr, hsg,
     hpc, hpl, hpp, hpr, hpg⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [cliUnifiedCanonDeserRunCumCap, cliRunCanon1MiBSlotCum, initArmDeltaCum,
      r2TightDeltaCum]
    exact Nat.add_le_add_left
      (max4_le_max4 (by omega) (by omega) (by omega) (by omega)) _
  · simp only [cliUnifiedCanonDeserRunLiveCap, cliRunCanon1MiBSlotLive, initArmDeltaLive,
      r2DeltaLive]
    exact Nat.add_le_add_left
      (max4_le_max4 (by omega) (by omega) (by omega) (by omega)) _
  · unfold cliRunCanon1MiBSlotPeak cliUnifiedCanonDeserRunPeakCap
    have hp_init :
        initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 SW.initPeak ≤
          initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637
            (cliInitSlotPeakCap + dp) := by
      unfold initArmDeltaPeak
      exact max_le_max (Nat.le_refl _)
        (Nat.add_le_add_left (max_le_max (Nat.le_refl _) (Nat.add_le_add_left hip _)) _)
    have hp_enc :
        r2DeltaPeak fineCostModel SW.encLive SW.encPeak sessionCapBytes ≤
          r2DeltaPeak fineCostModel (cliSendSlotLiveCap + dl) (cliSendSlotPeakCap + dp)
            sessionCapBytes := by
      unfold r2DeltaPeak
      exact max_le_max hep (Nat.add_le_add_right hel _)
    have hp_sig :
        max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + SW.decSigPeak) ≤
          max (sigSlicePeak msgCapBytes)
            (sigSliceLive msgCapBytes + (cliRecvWhisperSlotPeakCap + dp)) :=
      max_le_max (Nat.le_refl _) (Nat.add_le_add_left hsp _)
    have hp_pk :
        max (pksmCanonSlicePeak msgCapBytes) (pksmCanonSliceLive msgCapBytes + SW.decPkPeak) ≤
          max (pksmCanonSlicePeak msgCapBytes)
            (pksmCanonSliceLive msgCapBytes + (cliRecvPrekeySlotPeakCap + dp)) :=
      max_le_max (Nat.le_refl _) (Nat.add_le_add_left hpp _)
    exact max_le_max (Nat.le_refl _)
      (Nat.add_le_add_left (max4_le_max4 hp_init hp_enc hp_sig hp_pk) _)
  · unfold cliRunCanon1MiBSlotMaxReq cliUnifiedCanonDeserRunReqCap initArmMaxReq r2MaxReq
    exact max_le_max (Nat.le_refl _)
      (max4_le_max4
        (max_le_max (Nat.le_refl _) (max_le_max (Nat.le_refl _) hir))
        (max_le_max her (Nat.le_refl _))
        (max_le_max (Nat.le_refl _) hsr)
        (max_le_max (Nat.le_refl _) hpr))
  · unfold cliRunCanonOpenedFineGrpS cliUnifiedCanonDeserRunGrpSCap cliRunCanonArmFineGrpS
    exact Nat.add_le_add_left
      (max4_le_max4
        (Nat.add_le_add_left hig _)
        (Nat.add_le_add_right heg _)
        (Nat.add_le_add_left hsg _)
        (Nat.add_le_add_left hpg _)) _

/-- Direct sibling of `CliTopBudgetSpec.cliMain_fitsTrace_fineCostModel` (`:1773`) for
`CliRunCanonTightEnv W` under `CliRunTightSlotCaps SW`. -/
theorem cliMain_canon_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRunTightSlotCaps SW)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunCanonTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliMainCanonStepReserve fullLog := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliUnifiedCanonDeser_bounds_mono hSlots
  exact cliMain_canon_fitsTrace_of_runCap henf hsb hsc hcap SW hcaps hspqr haddr hdirs
    h1 h2 h3 h4 h5 (by decide) (by decide) hEnv

/-- Direct sibling of `CliTopBudgetSpec.cliMain_fitsEnv_fineCostModel` (`:1801`) for
`CliRunCanonTightEnv W` under `CliRunTightSlotCaps SW`. -/
theorem cliMain_canon_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRunTightSlotCaps SW)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunCanonTightEnv W) g addrOpt needStdin dirs ok) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliUnifiedCanonDeser_bounds_mono hSlots
  exact cliMain_canon_fitsEnv_of_runCap henf hsb hsc hcap SW hcaps hspqr haddr hdirs
    h1 h2 h3 h4 h5 (by decide) (by decide)

private theorem deserParamSlotCaps_mono
    {dc1 dl1 dp1 dr1 dg1 dc2 dl2 dp2 dr2 dg2 : Nat}
    {W : CliRunWrapperEnvs} {SW : CliRunFineSlotSpecs W}
    (h : CliRunDeserParamSlotCaps dc1 dl1 dp1 dr1 dg1 SW)
    (hc : dc1 ≤ dc2) (hl : dl1 ≤ dl2) (hp : dp1 ≤ dp2) (hr : dr1 ≤ dr2) (hg : dg1 ≤ dg2) :
    CliRunDeserParamSlotCaps dc2 dl2 dp2 dr2 dg2 SW := by
  rcases h with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
     h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact
    ⟨Nat.le_trans h1 (Nat.add_le_add_left hc _),
     Nat.le_trans h2 (Nat.add_le_add_left hl _),
     Nat.le_trans h3 (Nat.add_le_add_left hp _),
     Nat.le_trans h4 (max_le_max (Nat.le_refl _) hr),
     Nat.le_trans h5 (Nat.add_le_add_left hg _),
     Nat.le_trans h6 (Nat.add_le_add_left hc _),
     Nat.le_trans h7 (Nat.add_le_add_left hl _),
     Nat.le_trans h8 (Nat.add_le_add_left hp _),
     Nat.le_trans h9 (max_le_max (Nat.le_refl _) hr),
     Nat.le_trans h10 (Nat.add_le_add_left hg _),
     Nat.le_trans h11 (Nat.add_le_add_left hc _),
     Nat.le_trans h12 (Nat.add_le_add_left hl _),
     Nat.le_trans h13 (Nat.add_le_add_left hp _),
     Nat.le_trans h14 (max_le_max (Nat.le_refl _) hr),
     Nat.le_trans h15 (Nat.add_le_add_left hg _),
     Nat.le_trans h16 (Nat.add_le_add_left hc _),
     Nat.le_trans h17 (Nat.add_le_add_left hl _),
     Nat.le_trans h18 (Nat.add_le_add_left hp _),
     Nat.le_trans h19 (max_le_max (Nat.le_refl _) hr),
     Nat.le_trans h20 (Nat.add_le_add_left hg _)⟩

/-- Parametric-`DeserEnv` sibling of `CliTopBudgetSpec.cliMain_deserParam_fitsTrace_fineCostModel`
(`:1889`) for `CliRunCanonTightEnv W`. -/
theorem cliMain_canon_deserParam_fitsTrace_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {deserCum deserLive deserPeak deserMaxReq deserGrpS : Nat}
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRunDeserParamSlotCaps deserCum deserLive deserPeak deserMaxReq deserGrpS SW)
    (hdc : deserCum ≤ cliDeserMaxCum)
    (hdl : deserLive ≤ cliDeserMaxLive)
    (hdp : deserPeak ≤ cliDeserMaxPeak)
    (hdr : deserMaxReq ≤ cliDeserMaxReq)
    (hdg : deserGrpS ≤ cliDeserMaxGrpS)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes)
    {fullLog : List AllocEvent}
    (hEnv : CliMainEnv uuidParse (CliRunCanonTightEnv W) g addrOpt needStdin dirs ok fullLog) :
    FitsTrace fineCostModel lim cliMainCanonDeserParamStepReserve fullLog := by
  have hSlotsMax := deserParamSlotCaps_mono hSlots hdc hdl hdp hdr hdg
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliUnifiedCanonDeser_bounds_mono hSlotsMax
  exact cliMain_canon_fitsTrace_of_runCap henf hsb hsc hcap SW hcaps hspqr haddr hdirs
    h1 h2 h3 h4 h5 (by decide) (by decide) hEnv

/-- Parametric-`DeserEnv` sibling of `CliTopBudgetSpec.cliMain_deserParam_fitsEnv_fineCostModel`
for `CliRunCanonTightEnv W`. -/
theorem cliMain_canon_deserParam_fitsEnv_fineCostModel
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap : cliOneGiB ≤ lim.physCap)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    {deserCum deserLive deserPeak deserMaxReq deserGrpS : Nat}
    (SW : CliRunFineSlotSpecs (W g))
    (hSlots : CliRunDeserParamSlotCaps deserCum deserLive deserPeak deserMaxReq deserGrpS SW)
    (hdc : deserCum ≤ cliDeserMaxCum)
    (hdl : deserLive ≤ cliDeserMaxLive)
    (hdp : deserPeak ≤ cliDeserMaxPeak)
    (hdr : deserMaxReq ≤ cliDeserMaxReq)
    (hdg : deserGrpS ≤ cliDeserMaxGrpS)
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ cliMaxAddrTextBytes)
    (hdirs : ((dirs.map (fun dn => dn.2.length)).sum) ≤ cliMaxDirtyEntries ∧
      ∀ dn ∈ dirs, dn.1.length ≤ cliMaxDirPathBytes ∧ ∀ nm ∈ dn.2, nm.length ≤ cliMaxAddrTextBytes) :
    FitsEnv fineCostModel lim fineCostModel.init
      (CliMainEnv uuidParse (CliRunCanonTightEnv W) g addrOpt needStdin dirs ok) := by
  have hSlotsMax := deserParamSlotCaps_mono hSlots hdc hdl hdp hdr hdg
  obtain ⟨h1, h2, h3, h4, h5⟩ := cliUnifiedCanonDeser_bounds_mono hSlotsMax
  exact cliMain_canon_fitsEnv_of_runCap henf hsb hsc hcap SW hcaps hspqr haddr hdirs
    h1 h2 h3 h4 h5 (by decide) (by decide)

end LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
