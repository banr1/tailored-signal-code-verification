/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkLinked
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Encrypt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.V1.SpqrV1FactsPure
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.PanicAndWire

/-!
# Binary-Kit Store-Kit Lift and Per-Arm Callee Slot Bridges

1. Lifts a spare-capacity Block-`52` `SessionRecord::serialize` contract (`RecordSerializeSeqFreeEnv`)
   through Block `570` (`store_session::{closure#0}`) into `SessionOnlyKitPlacedOkSE` at
   `RecordSerializeSeqFreeValidEnv`, specialized to `w1BinarySessKitPlacedBudget` and
   `decBinarySessKitPlacedBudget` on `cliExternsPlaced mmpl W`.
2. Proves the five callee slot containment bridges (`PKSM`, `W3`, `W1`, `W2`, and `W4`) into
   `mkBinaryKitRealCalleeEnvs img S X W g`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots

open Arm64 Arm64.Obj ProofLib
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession
  (IdentityKey Mut OutgoingTripleRatchet PublicKey ShaCompress SignalMessage SignalProtocolError
   aesCbcEncrypt liftE serializeContent)
open CryptoGames.LibsignalSessionApi
  (CiphertextMessage KyberPayload PreKeySignalMessage ProtoPreKeySignalMessage Session
   SessionRecord SystemTime encryptFlat execOk maxUnacknowledgedSessionAge messageEncrypt_eq_flat
   wrapFlat)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.E2E
  (PEParams PreKeyMessageFields UnreachedPqxdhPrimitives pqxdhSpqrModel)
open CryptoVerification.E2E.InMem.SessionStoreImpl (record_sessionRecordAt_eq toRecordGhost)
open CryptoVerification.E2E.Pqxdh.ResponderWire (PreKeyTryFromArgs)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_46 lsProg_52)
open CryptoVerification.E2E.Record.Serialization (CanonRecord SerializeGhost)
open CryptoVerification.E2E.V1 (spqrV1Send_msg_len_le)
open CryptoVerification.LibsignalProtoCodec
  (WireType encodeBytesField encodeKey encodeUint32Field encodeVarint encodeVarintAux
   protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block storePollPlacedOutAt
   withEnvPre withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalPublicApiRepr
  (AddrVal RecordGhost serializeAddrVals sessionRecordAt)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (extHookStack reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost addrBytes okTagVec protocolAddressAt serviceIdParse uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs cliExternsPlaced lsDropOffPlaced_eq lsReadFileSym stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule StoresGhost addressText dirAt pathOf sessStoreBoxAt)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliSessInv cliIdentityVtRoSym cliSessStoreAt cliSessionKitSpecPlaced cliSessionStoreSpec
   cliSessionStoreSpec_storeUpdate_inv cliSessionVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit
  (addrTextNeedPlaced dirPutNeedPlaced loadPollNeed loadPollNeedPlaced loadShimNeed
   loadShimNeedPlaced storePollNeedX storePollNeedXPlaced storeShimNeed storeShimNeedPlaced)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall cliIo cliWrOk coinsOf inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_569 lsProg_570 lsProg_589)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost Init2Data InitGhost PksmGhost RunSem addrValOf runFiles unixEpoch)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks IsFsC cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliAnswers encDef encKey)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (toDecryptGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeIn scopeKit)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_cl_to_lscro ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
  (canonRecord_of_satisfies_sessionRecordAt memRegion_32_cells stackAt_sub_split)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (callAddrNameLen parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (RecordSerializeSeqFreeValidEnv W1BinarySendDom W1BinarySendParams W1SendBinaryKitSlotEnv
   W2BinaryWhisperDom W2BinaryWhisperParams W2RecvWhisperBinaryKitSlotEnv
   W3BinaryInitDom W3BinaryInitParams W3InitBinaryKitSlotEnv
   W4BinaryRecvPrekeyDom W4BinaryRecvPrekeyParams W4BinaryRecvPrekeyWideSlotEnv
   W4CloneACDomEnv W4CloneBDomEnv decBinaryIdKitPlacedBudget decBinarySessKitPlacedBudget
   mkBinaryKitRealCalleeEnvs mkW4RecvPrekeyWideSlotParams w1BinaryIdKitPlacedBudget
   w1BinarySessKitPlacedBudget)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (RecordSerializeSeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec (SpqrSendTightCapEnv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid SessionCloneDom recordGhostValid_of_sessionRecordAt)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot (W2RealTdEnv)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec (RecordAliceInitiatedAnyCkBounds)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (W4DecryptPrekeySplitWideSlotEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4RecvPrekeyRealParams W4RecvPrekeyTryDecACEnv mkW4RecvPrekeySlotParams)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4ArchivedTrialDomOf W4FailedTdDomOf W4RecvPrekeyRealDomOf W4TryDecryptCallDomOf
   W4TryDecryptPathACDomOf)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget (PreKeyTryFromEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget
  (SigTryFromConcreteEnv)
open LibsignalBinary.Proofs.PeakBudget.WireFieldDomainCaps
  (pksmParse_lengths_le signalMessage_tryFrom_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (PksmCanonSliceEnv cliPqInputs_recv_prekey_canonical preKeyArgsOfFields
   preKeyTryFromConcrete_m_sub_pksmCanonSlice preKeyTryFromConcrete_sub_pksmCanonSlice)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (SessionOnlyKitPlacedOkSE kitStorePollPlacedSpec kitStorePollPlacedSpecE)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (serializeStackX)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv SessKitHooksPlaced cliAddrText_placed_ok_of_sessHooks
   cliDirGet_placed_ok_of_sessHooks cliDirPut_placed_ok_of_sessHooks cliSessFutDrop_rocl_placed_ok
   cliSessLoadPoll_rocl_placed_ok cliSessLoadShim_rocl_placed_ok cliSessStoreShim_rocl_placed_ok
   cliSessionKitBudgetEnv cliSessionKitStorePollEnv sessDeserialize_of_sub_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
  (r3bDecPkGhost r3bPksmGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced ReadFileRuleEnv addrTextSpecPlaced dirPutSpecPlaced
   readFileSpecPlaced sessDeserializeSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget
  (CliStorePollEnv serializeCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget
  (addrText_cells_placed_ok dirPut_cells_placed_ok sessStorePollInner_placed_ok
   sessStorePoll_placed_of_inner)

/-! ## 1. `serializeCanonSeqFreeSpecX` and Block `52` → `570` → `SessionOnlyKitPlacedOkSE` Lift -/

private theorem seqEnv_mono {P₁ P₂ Q₁ Q₂ : List AllocEvent → Prop}
    (hP : ∀ e, P₁ e → P₂ e) (hQ : ∀ e, Q₁ e → Q₂ e)
    {evs : List AllocEvent} (h : SeqEnv P₁ Q₁ evs) :
    SeqEnv P₂ Q₂ evs := by
  rcases h with hp | ⟨e₁, e₂, rfl, hp, hq⟩
  · exact Or.inl (hP evs hp)
  · exact Or.inr ⟨e₁, e₂, rfl, hP e₁ hp, hQ e₂ hq⟩

/-- Budget-threaded canonical `SessionRecord::serialize` contract (`lsProg_52`) at `serializeStackX`
with spare-capacity `RecordSerializeSeqFreeEnv x.g x.r` (definitionally equal to
`SerializeSeqFreeXBudget.serializeCanonSeqFreeSpecX`). -/
def serializeCanonSeqFreeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧ CanonRecord x.g x.r ∧
      (encodeRecord x.r).length < 2 ^ 32 ∧
      FitsEnv M lim st (RecordSerializeSeqFreeEnv x.g x.r)⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗ memRegion x.out 32 ∗
      A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ RecordSerializeSeqFreeEnv x.g x.r evs⌝ ∗
      sessionRecordAt A.repAlloc x.self x.g x.r ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (x.out + 8#64) (encodeRecord x.r) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

theorem serialize_cells_seqFree_placed_okX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {calleeStk : Nat}
    (hSer : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hle : serializeStackX ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (serializeCellsSpec A lim RecordSerializeSeqFreeEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨⟨recA, out, g, r, o0, o1, o2, o3, fsp⟩, st⟩ R s0
    hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [serializeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hcanon, hlen, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - serializeStackX)
  let callG : SerializeGhost × M.σ := (⟨recA, out, g, r⟩, st)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)).pre callG s0 ∗
        (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [serializeCanonSeqFreeSpecX, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon, hlen, hfit⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hSer.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, serializeCanonSeqFreeSpecX, serializeCellsSpec, callG] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq
    rcases hq with ⟨bCap, bPtr, hq⟩
    refine ⟨evs, bCap, bPtr, ?_⟩
    rw [vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [okTagVec, stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, serializeCanonSeqFreeSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializeCanonSeqFreeSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializeCanonSeqFreeSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem sessStorePoll_seqFree_placed_ok_of_depsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (_hC : AllocContractsXCliPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (hstk : 0xd0 + max (max addrStk serializeStackX) (max putStk extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim
        (CliStorePollEnv AddrEnv RecordSerializeSeqFreeEnv PutEnv) stk) := by
  have hAddr' := ls_transfer_lscro (callerProg := lsProg_570 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hSer' := ls_transfer_cl_to_lscro (callerProg := lsProg_570 H) hSer (by decide) hSerBlk hSerUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_570 H) hPut (by decide) hPutBlk hPutUnmut
  refine sessStorePoll_placed_of_inner (fun hhi => ?_) hstk
  exact sessStorePollInner_placed_ok
    (addrText_cells_placed_ok hAddr' (by omega) hhi)
    (serialize_cells_seqFree_placed_okX hSer' (by omega) hhi)
    (dirPut_cells_placed_ok hPut' (by omega) hhi)

theorem cliSessStorePoll_rocl_seqFree_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg addrProg serProg putProg : Program}
    {callerBlk addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    (hC : AllocContractsXCliPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim (fun g => AddrValEnv g.val) addrTextNeedPlaced))
    (hSerSeqFree : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv dirPutNeedPlaced))
    (hs4 : storePollNeedXPlaced ≤ s4)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storePollOff)
      (withLsRoCl lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv RecordSerializeSeqFreeValidEnv PutEnv vtSym idVtSym)
          encodeRecord)) := by
  have h570 := sessStorePoll_seqFree_placed_ok_of_depsX hC hAddr hSerSeqFree hPut hs4
    hAddrBlk hAddrUnmut hSerBlk hSerUnmut hPutBlk hPutUnmut
  have h570_kit : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv RecordSerializeSeqFreeValidEnv PutEnv vtSym idVtSym)
          encodeRecord)) := by
    refine subroutine_ok_outcome_intro fun ⟨call, self, d, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
      cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          (Scope call.call.record ∧ (encodeRecord call.call.record).length < 2 ^ 32) ∧
          call.call.addr.val = peer.val ∧
          FitsEnv M lim st
            (cliSessionKitStorePollEnv AddrValEnv RecordSerializeSeqFreeValidEnv PutEnv
              d call.call.addr.val call.call.record)⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
        (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
          dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
          protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
          CryptoVerification.E2E.Record.sessionRecordAt
            A.repAlloc call.call.recA call.call.g call.call.record ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre0
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨_hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hrec, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hrec_sat : s0.mem ⊨
        CryptoVerification.E2E.Record.sessionRecordAt
            A.repAlloc call.call.recA call.call.g call.call.record ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hspatial
    have hrec_repr : s0.mem ⊨
        sessionRecordAt A.repAlloc call.call.recA (toRecordGhost call.call.g) call.call.record ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) := by
      rwa [← record_sessionRecordAt_eq] at hrec_sat
    have hgvalid : RecordGhostValid (toRecordGhost call.call.g) call.call.record :=
      recordGhostValid_of_sessionRecordAt hrec_repr
    have hfit_hop : FitsEnv M lim st
        (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeEnv PutEnv
          ⟨call, self, d⟩) := by
      intro evs he
      exact hfit evs
        (seqEnv_mono (fun _ ha => ha)
          (fun _ h2 =>
            seqEnv_mono (fun _ hs => ⟨toRecordGhost call.call.g, hgvalid, hs⟩) (fun _ hp => hp) h2)
          he)
    have hname : call.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hm_hop : s0.mem ⊨
        (sessStorePollSpecPlaced A lim
          (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeEnv PutEnv) s4).pre
          (⟨call, self, d⟩, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only
      have h1 : s0.mem ⊨
          ⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.call.addr.name.bytes.length < 2 ^ 32 ∧
            (encodeRecord call.call.record).length < 2 ^ 32 ∧
            d.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st
              (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeEnv PutEnv
                ⟨call, self, d⟩)⌝ ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            CryptoVerification.E2E.Record.sessionRecordAt
              A.repAlloc call.call.recA call.call.g call.call.record ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hname ▸ hinv.nameLt, hrec.2, hinv.changedLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h570.mono_outcome (⟨call, self, d⟩, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, ⟨htr, hevs⟩, hm⟩ := hpost
      have hevs_kit :
          cliSessionKitStorePollEnv AddrValEnv RecordSerializeSeqFreeValidEnv PutEnv
            d call.call.addr.val call.call.record evs :=
        seqEnv_mono (fun _ ha => ha)
          (fun _ h2 =>
            seqEnv_mono (fun _ hs => ⟨toRecordGhost call.call.g, hgvalid, hs⟩) (fun _ hp => hp) h2)
          hevs
      have hinv' : CliSessInv rd F0 pathOk Scope peer
          (d.put (addressText call.call.addr.val) (encodeRecord call.call.record)) :=
        cliSessionStoreSpec_storeUpdate_inv (A := A.repAlloc) (b := 0#64)
          (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (ans := .ok ()) hinv haddr hrec
      dsimp only [withLsCodeRoLoaded, kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
        cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok (), evs, ?_⟩
      dsimp only [storePollPlacedOutAt]
      have hgoal : sf.mem ⊨
          ⌜(Except.ok () : Except Unit Unit) = .ok () ∧ sf.trace = s0.trace ++ [] ∧
            cliSessionKitStorePollEnv AddrValEnv RecordSerializeSeqFreeValidEnv PutEnv
              d call.call.addr.val call.call.record evs⌝ ∗
          (⌜CliSessInv rd F0 pathOk Scope peer
              (d.put (addressText call.call.addr.val) (encodeRecord call.call.record))⌝ ∗
            (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 1#8 ∗
              dirAt A.repAlloc self (d.put (addressText call.call.addr.val)
                (encodeRecord call.call.record)) ∗
              (call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (call.out + 8#64) 40 ∗
              protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
              CryptoVerification.E2E.Record.sessionRecordAt
                A.repAlloc call.call.recA call.call.g call.call.record ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨rfl, by rw [List.append_nil]; exact htr, hevs_kit⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv', Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 570) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 570)
    h570_kit hCallerBlk (by decide) (by decide)

theorem cliSessKitOkSE_seqFree_placed_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg serProg : Program} {jRead deserBlk serBlk : Nat}
    [IsLsBlockProg readProg jRead H]
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : SessKitHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSerSeqFree : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        (AddrTextValEnv DecimalEnv) (DirGetEnv PathEnv ReadEnv rd) DeserEnv
        RecordSerializeSeqFreeValidEnv DirPutEnv vtSym idVtSym)
      Scope encodeRecord H := by
  have hAddr := cliAddrText_placed_ok_of_sessHooks hh
  have hGet := cliDirGet_placed_ok_of_sessHooks hpathLen hh hRead hjRead hjRead_unmut
  have hPut := cliDirPut_placed_ok_of_sessHooks hh
  exact
    { loadShim := fun hblk => cliSessLoadShim_rocl_placed_ok hh.alloc hs1 hblk
      loadPoll := fun hblk => cliSessLoadPoll_rocl_placed_ok hh.alloc hAddr hGet hDeser
        (hh.fs (lsProg_569 H) 569) hs2 hblk (by decide) (by decide) (by decide) (by decide)
        hDeserBlk hDeserUnmut
      loadFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk
      storeShim := fun hblk => cliSessStoreShim_rocl_placed_ok hh.alloc hs3 hblk
      storePoll := fun hblk => cliSessStorePoll_rocl_seqFree_placed_ok hh.alloc hAddr hSerSeqFree
        hPut hs4 hblk (by decide) (by decide) hSerBlk hSerUnmut (by decide) (by decide)
      storeFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk }

theorem cliSessKitOkSE_seqFree_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg serProg : Program} {jRead deserBlk serBlk : Nat}
    [IsLsBlockProg readProg jRead H]
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSerSeqFree : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        (AddrTextValEnv DecimalEnv) (DirGetEnv PathEnv ReadEnv rd) DeserEnv
        RecordSerializeSeqFreeValidEnv DirPutEnv vtSym idVtSym)
      Scope encodeRecord H :=
  cliSessKitOkSE_seqFree_placed_of_sessHooks hDropNz hpathLen (SessKitHooksPlaced.of_runHooks hh)
    hRead hDeser hSerSeqFree hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut
    hSerBlk hSerUnmut

theorem cliSessKitOkSE_seqFree_cli_scopeKit_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hDeserScopeKit : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hSerSeqFree : subroutine_ok (lsProg_52 (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 52) (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        (AddrTextValEnv DecimalEnv) (DirGetEnv PathEnv ReadEnv cliIo.rd) DeserEnv
        RecordSerializeSeqFreeValidEnv DirPutEnv vtSym idVtSym)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_placed_of_sessHooks
    (serProg := lsProg_52 (cliGhostExterns g (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) (SessKitHooksPlaced.cli mmpl g W hG hAzFsT hStrFsT)
    hRead (sessDeserialize_of_sub_placed_ok hDeserScopeKit hsub) hSerSeqFree
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut (by decide) (by decide)

/-- Direct `SessionOnlyKitPlacedOkSE` instantiation at `w1BinarySessKitPlacedBudget` on any
`H : LibsignalHooks` (including `cliExternsPlaced mmpl W`). -/
theorem w1BinarySessKitPlaced_okSE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok (lsProg_589 H) (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnv cliIo.rd))))
    (hDeser : subroutine_ok (lsProg_569 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim (ofBytesEnv RecordDeserializeCancelEnv)))
    (hSerSeqFree : subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim))) :
    SessionOnlyKitPlacedOkSE A lim
      (w1SessKitPlaced A.repAlloc B F0 peer)
      (w1BinarySessKitPlacedBudget A.repAlloc B F0 peer)
      scopeKit encodeRecord H :=
  cliSessKitOkSE_seqFree_placed
    (readProg := lsProg_589 H) (jRead := 589)
    (deserProg := lsProg_569 H) (deserBlk := 569)
    (serProg := lsProg_52 H) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) hh hRead hDeser hSerSeqFree
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Direct `SessionOnlyKitPlacedOkSE` instantiation at `decBinarySessKitPlacedBudget` on any
`H : LibsignalHooks` (including `cliExternsPlaced mmpl W`). -/
theorem decBinarySessKitPlaced_okSE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok (lsProg_589 H) (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile (ReadFileRuleEnv cliIo.rd))))
    (hDeser : subroutine_ok (lsProg_569 H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim (ofBytesEnv RecordDeserializeCancelEnv)))
    (hSerSeqFree : subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim))) :
    SessionOnlyKitPlacedOkSE A lim
      (decSessKitPlaced A.repAlloc F0 peer B)
      (decBinarySessKitPlacedBudget A.repAlloc B F0 peer)
      scopeKit encodeRecord H :=
  w1BinarySessKitPlaced_okSE B F0 peer hDropNz hh hRead hDeser hSerSeqFree

/-! ## 2. Pure Length Helpers for `W1`, `W2`, `W3`, and `W4` -/

theorem recv_rest_length_le_msgCapBytes {g : RunCall} {peerV : AddrV}
    {tag : BitVec 8} {rest : List (BitVec 8)}
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = tag :: rest) :
    rest.length ≤ msgCapBytes := by
  have hin_stdin : (tag :: rest).length ≤ stdinCapBytes := by
    simpa [hc, inputOf, CallV.tag, hst] using hin
  have hrest_stdin : rest.length ≤ stdinCapBytes :=
    Nat.le_trans (Nat.le_succ rest.length) hin_stdin
  have hcap_le : stdinCapBytes ≤ msgCapBytes := by
    unfold stdinCapBytes msgCapBytes
    decide
  exact Nat.le_trans hrest_stdin hcap_le

private theorem send_stdin_length_le_msgCapBytes {g : RunCall} {peerV : AddrV}
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .send peerV) :
    g.i.stdin.length ≤ msgCapBytes := by
  have hin_stdin : g.i.stdin.length ≤ stdinCapBytes := by
    simpa [hc, inputOf, CallV.tag] using hin
  have hcap_le : stdinCapBytes ≤ msgCapBytes := by
    unfold stdinCapBytes msgCapBytes
    decide
  exact Nat.le_trans hin_stdin hcap_le

private theorem encodeVarintAux_len_le :
    ∀ (k : Nat) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (encodeVarintAux_len_le k (v >>> 7)) 1

private theorem encodeVarint_len_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_len_le 10 v

private theorem encodeKey_len_le (tag : Nat) (wt : WireType) : (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_len_le _

private theorem encodeUint32Field_len_le (tag : Nat) (ov : Option (BitVec 32)) :
    (encodeUint32Field tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [encodeUint32Field]
  | some v =>
    simp only [encodeUint32Field, List.length_append]
    have h1 := encodeKey_len_le tag .varint
    have h2 := encodeVarint_len_le (v.zeroExtend 64)
    omega

private theorem encodeBytesField_some_len_le (tag : Nat) (bs : List (BitVec 8)) :
    (encodeBytesField tag (some bs)).length ≤ 20 + bs.length := by
  simp only [encodeBytesField, List.length_append]
  have h1 := encodeKey_len_le tag .lengthDelimited
  have h2 := encodeVarint_len_le (BitVec.ofNat 64 bs.length)
  omega

private theorem serializeAddrVals_len_36 {sender recipient : AddrVal} {ad : List (BitVec 8)}
    (h : serializeAddrVals (serviceIdParse uuidTryParse) sender recipient = some ad) :
    ad.length = 36 := by
  unfold serializeAddrVals at h
  rcases hs : serviceIdParse uuidTryParse sender.name with _ | vs <;> rw [hs] at h
  · cases h
  · dsimp only [bind, Option.bind] at h
    rcases hr : serviceIdParse uuidTryParse recipient.name with _ | vr <;> rw [hr] at h
    · cases h
    · simp only [pure, Option.some.injEq] at h
      subst h
      simp only [addrBytes, List.length_append, List.length_cons, List.Vector.toList_length,
        List.length_nil]

private theorem mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a) s = (.ok a, s) := rfl

private theorem mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem mut_exec_get {σ : Type} (s : σ) :
    Mut.exec get s = (.ok s, s) := rfl

private theorem mut_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s') s = (.ok (), s') := rfl

private theorem mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r) s = (r, s) := by
  cases r <;> rfl

private theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  rw [ExceptT.run_bind, StateT.run_bind]
  rcases StateT.run (ExceptT.run m) s with ⟨r, s'⟩
  cases r <;> rfl

private theorem otrEncrypt_serialized_len_le (P : PEParams)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8))
    (otr otr' : OutgoingTripleRatchet (List (BitVec 8))) (msg : SignalMessage)
    (haddrs : ∀ ad, addrs = some ad → ad.length ≤ 36)
    (he : execOk (OutgoingTripleRatchet.encrypt P.C protoSignalCodec (pqxdhSpqrModel P).spqr
      ptext addrs coins) otr = .ok (msg, otr')) :
    msg.serialized.length ≤ ptext.length + 300 := by
  unfold OutgoingTripleRatchet.encrypt execOk at he
  simp only [mut_exec_bind, mut_exec_get] at he
  cases hpan : (pqxdhSpqrModel P).spqr.sendPanics otr.pqrState coins
  case true => simp [hpan, mut_exec_throw] at he
  simp only [hpan, Bool.false_eq_true, ↓reduceIte] at he
  rcases hs : (pqxdhSpqrModel P).spqr.send otr.pqrState coins with _ | ⟨pq', key, pm⟩
  · simp [hs, mut_exec_throw] at he
  · have hpmlen : pm.length ≤ 64 :=
      spqrV1Send_msg_len_le P.C.F P.Q.K otr.pqrState coins pq' key pm hs
    simp only [hs, mut_exec_pure, mut_exec_bind] at he
    rcases hn : otr.senderChainKey.nextChainKey P.C.F with _ | next
    · simp [hn, mut_exec_liftE] at he
    · simp only [hn, mut_exec_liftE, mut_exec_set, Except.ok.injEq, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      have hblk : ∀ l : List (BitVec 128),
          (l.flatMap CryptoGames.CBC.blockToBytesLE).length = 16 * l.length := by
        intro l
        induction l with
        | nil => rfl
        | cons b t ih =>
          have hb : (CryptoGames.CBC.blockToBytesLE b).length = 16 := by
            simp [CryptoGames.CBC.blockToBytesLE]
          simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, hb]
          omega
      have hct : ∀ k iv, (aesCbcEncrypt P.C.E k iv ptext).length = 16 * (ptext.length / 16 + 1) := by
        intro k iv
        unfold aesCbcEncrypt
        rw [hblk, List.Vector.toList_length]
        rfl
      have had6 : (encodeBytesField 6 addrs).length ≤ 56 := by
        cases h_a : addrs with
        | none => simp [encodeBytesField]
        | some ad =>
          have h1 := encodeBytesField_some_len_le 6 ad
          have h2 := haddrs ad h_a
          omega
      have hrk : otr.senderRatchetKey.publicKey.serialize.length = 33 := by
        simp [PublicKey.serialize, List.Vector.toList_length]
      have h5 : (encodeBytesField 5 (if pm.isEmpty then none else some pm)).length ≤
          20 + pm.length := by
        split <;> [simp [encodeBytesField]; exact encodeBytesField_some_len_le 5 pm]
      dsimp only [SignalMessage.new]
      rw [List.length_append]
      refine Nat.le_trans (Nat.add_le_add_left (List.length_take_le 8 _) _) ?_
      dsimp only [serializeContent, protoSignalCodec, CryptoVerification.LibsignalProtoCodec.encode]
      simp only [List.length_append, List.length_cons]
      have h1 := encodeBytesField_some_len_le 1 otr.senderRatchetKey.publicKey.serialize
      have h2 := encodeUint32Field_len_le 2 (some otr.senderChainKey.index)
      have h3 := encodeUint32Field_len_le 3 (some otr.previousCounter)
      have h4 := encodeBytesField_some_len_le 4 (aesCbcEncrypt P.C.E
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).cipherKey
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).iv ptext)
      have h4' := hct ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).cipherKey
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).iv
      omega

private theorem prost_varint_len_le (k : Nat) :
    ∀ n : Nat, n < 128 ^ (k + 1) →
      (CryptoGames.LibsignalSessionApi.Prost.varint n).length ≤ k + 1 := by
  induction k with
  | zero =>
    intro n hn
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    simp [show n < 128 by omega]
  | succ k ih =>
    intro n hn
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    split_ifs with hlt
    · simp
    · simp only [List.length_cons]
      have hpow : 128 ^ (k + 1 + 1) = 128 * 128 ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hdiv : n / 128 < 128 ^ (k + 1) := by omega
      have := ih (n / 128) hdiv
      omega

private theorem prost_uint32Field_len_le {tag : Nat} (ht : tag ≤ 8) (v? : Option (BitVec 32)) :
    (CryptoGames.LibsignalSessionApi.Prost.uint32Field tag v?).length ≤ 10 := by
  cases v? with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.uint32Field]
  | some v =>
    simp only [CryptoGames.LibsignalSessionApi.Prost.uint32Field,
      CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have h1 := prost_varint_len_le 0 (8 * tag + 0) (by omega)
    have h2 := prost_varint_len_le 4 v.toNat (by have := v.isLt; omega)
    omega

private theorem prost_bytesField_opt_len_le {tag : Nat} (ht : tag ≤ 8)
    (bs? : Option (List (BitVec 8))) (B : Nat)
    (hB : ∀ bs, bs? = some bs → bs.length ≤ B ∧ bs.length < 2 ^ 32) :
    (CryptoGames.LibsignalSessionApi.Prost.bytesField tag bs?).length ≤ 10 + B := by
  cases hbs : bs? with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.bytesField]
  | some bs =>
    obtain ⟨hle, hlt⟩ := hB bs hbs
    simp only [CryptoGames.LibsignalSessionApi.Prost.bytesField,
      CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have h1 := prost_varint_len_le 0 (8 * tag + 2) (by omega)
    have h2 := prost_varint_len_le 4 bs.length (by omega)
    omega

private theorem preKeyMsgNew_serialized_len_le
    (ver : BitVec 8) (regId : BitVec 32) (preKeyId : Option (BitVec 32)) (spk : BitVec 32)
    (kp : Option KyberPayload) (baseKey : PublicKey) (ik : IdentityKey) (msg : SignalMessage)
    (hkp : ∀ k, kp = some k → k.ciphertext.length ≤ 1569)
    (hmsg : msg.serialized.length < 2 ^ 32) :
    (PreKeySignalMessage.new ver regId preKeyId spk kp baseKey ik msg).serialized.length ≤
      msg.serialized.length + 1717 := by
  have hbk : baseKey.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  have hik : ik.serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize, List.Vector.toList_length]
  have hf1 := prost_uint32Field_len_le (tag := 1) (by omega) preKeyId
  have hf2 := prost_bytesField_opt_len_le (tag := 2) (by omega)
    (some baseKey.serialize) 33 (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; omega)
  have hf3 := prost_bytesField_opt_len_le (tag := 3) (by omega)
    (some ik.serialize) 33 (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; omega)
  have hf4 := prost_bytesField_opt_len_le (tag := 4) (by omega)
    (some msg.serialized) msg.serialized.length (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; exact ⟨Nat.le_refl _, hmsg⟩)
  have hf5 := prost_uint32Field_len_le (tag := 5) (by omega) (some regId)
  have hf6 := prost_uint32Field_len_le (tag := 6) (by omega) (some spk)
  have hf7 := prost_uint32Field_len_le (tag := 7) (by omega) (kp.map (·.preKeyId))
  have hf8 := prost_bytesField_opt_len_le (tag := 8) (by omega)
    (kp.map (·.ciphertext)) 1569 (by
      intro bs hbs
      rcases h_k : kp with _ | k <;> rw [h_k] at hbs
      · cases hbs
      · simp only [Option.map_some, Option.some.injEq] at hbs
        subst hbs
        have hlen := hkp k h_k
        omega)
  simp only [PreKeySignalMessage.new, ProtoPreKeySignalMessage.encode, List.length_cons,
    List.length_append]
  omega

private theorem loadRec_ok_some_imp_scope {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal} {r : SessionRecord (List (BitVec 8))}
    (hl : loadRec Scope F peer = .ok (some r)) : Scope r := by
  unfold loadRec at hl
  rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (addressText peer) with
    _ | (_ | ⟨b, bs⟩) <;> rw [hget] at hl
  · cases hl
  · cases hl
  · dsimp only at hl
    split_ifs at hl with hex
    simp only [Except.ok.injEq, Option.some.injEq] at hl
    rw [← hl]
    exact (Classical.choose_spec hex).2

private theorem encDef_some_out_bounds (P : PEParams) (F : FsFiles)
    (peer me : AddrVal) (ptext coins : List (BitVec 8)) (f : StoresGhost) (cm : CiphertextMessage)
    (hptext : ptext.length ≤ msgCapBytes)
    (henc : encDef P scopeIn F peer me ptext coins = some (some (f, cm))) :
    match cm with
    | .signalMessage m => m.serialized.length ≤ sessionCapBytes
    | .preKeySignalMessage m => m.serialized.length ≤ sessionCapBytes := by
  unfold encDef at henc
  rcases hme : CryptoGames.LibsignalSessionApi.messageEncrypt P.C protoSignalCodec
      (pqxdhSpqrModel P).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers scopeIn F peer (encKey scopeIn F peer)) ptext peer me unixEpoch coins with
    ⟨err | cm0, calls⟩ <;> rw [hme] at henc
  · cases err <;> simp at henc
  · simp only [Option.some.injEq, Prod.mk.injEq] at henc
    rcases henc with ⟨_, rfl⟩
    have hok : (CryptoGames.LibsignalSessionApi.messageEncrypt P.C protoSignalCodec
        (pqxdhSpqrModel P).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers scopeIn F peer (encKey scopeIn F peer)) ptext peer me unixEpoch coins).1 =
        .ok cm0 := by
      rw [hme]
    set answers := cliAnswers scopeIn F peer (encKey scopeIn F peer)
    simp only [messageEncrypt_eq_flat, encryptFlat] at hok
    rcases hl : answers.loadSession with _ | (_ | r) <;> rw [hl] at hok
    · simp at hok
    · simp at hok
    · have hr_scope : scopeIn r := loadRec_ok_some_imp_scope hl
      simp only at hok
      rcases hc : r.currentSession with _ | s <;> rw [hc] at hok
      · simp at hok
      · obtain ⟨s0, hs0, hSessP⟩ := hr_scope.2
        have hs_eq : s0 = s := Option.some.inj (hs0.symm.trans hc)
        rw [hs_eq] at hSessP
        clear hs0 hs_eq s0
        simp only at hok
        rcases hf : execOk OutgoingTripleRatchet.fromSessionState s.state with _ | ⟨otr, taken⟩ <;>
          rw [hf] at hok
        · simp at hok
        · simp only at hok
          rcases hk : taken.remoteIdentity with _ | remKey <;> rw [hk] at hok
          · simp at hok
          · simp only at hok
            rcases hw : wrapFlat (E := Unit) P.C protoSignalCodec (pqxdhSpqrModel P).spqr
                (serializeAddrVals (serviceIdParse uuidTryParse)) ptext peer me unixEpoch coins
                s otr with _ | ⟨cm1, otr'⟩ <;> rw [hw] at hok
            · simp at hok
            · simp only at hok
              have hcm : cm1 = cm0 := by
                rcases a_t : answers.isTrustedIdentity with _ | (_ | _) <;> rw [a_t] at hok
                · simp at hok
                · simp at hok
                · simp only at hok
                  rcases a_s : answers.saveIdentity with _ | _ <;> rw [a_s] at hok
                  · simp at hok
                  · simp only at hok
                    rcases a_st : answers.storeSession with _ | ⟨⟩ <;> rw [a_st] at hok
                    · simp at hok
                    · simp only [Except.ok.injEq] at hok
                      exact hok
              subst hcm
              simp only [wrapFlat] at hw
              have hcaps : msgCapBytes = stdinCapBytes ∧ sessionCapBytes = 2 * stdinCapBytes ∧
                  stdinCapBytes = 2 ^ 20 := by
                unfold msgCapBytes sessionCapBytes stdinCapBytes
                decide
              rcases hp : s.pendingPreKey with _ | items <;> rw [hp] at hw
              · rcases he : execOk (OutgoingTripleRatchet.encrypt P.C protoSignalCodec
                    (pqxdhSpqrModel P).spqr ptext none coins) otr with _ | ⟨sm, otr''⟩ <;>
                  rw [he] at hw
                · simp at hw
                · simp only [Except.ok.injEq, Prod.mk.injEq] at hw
                  rcases hw with ⟨rfl, _⟩
                  have hsm := otrEncrypt_serialized_len_le P ptext none coins otr otr'' sm
                    (fun _ h => nomatch h) he
                  omega
              · simp only at hw
                rcases h1 : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat with _ | ts <;>
                  rw [h1] at hw
                · simp at hw
                · simp only at hw
                  rcases h2 : ts.checkedAddSecs maxUnacknowledgedSessionAge with _ | expiry <;>
                    rw [h2] at hw
                  · simp at hw
                  · simp only at hw
                    by_cases h3 : expiry.lt unixEpoch = true
                    · simp [h3] at hw
                    · simp only [Bool.eq_false_iff.mpr h3, Bool.false_eq_true, ↓reduceIte] at hw
                      rcases he : execOk (OutgoingTripleRatchet.encrypt P.C protoSignalCodec
                          (pqxdhSpqrModel P).spqr ptext
                          (serializeAddrVals (serviceIdParse uuidTryParse) me peer) coins) otr
                        with _ | ⟨sm, otr''⟩ <;> rw [he] at hw
                      · simp at hw
                      · simp only [Except.ok.injEq, Prod.mk.injEq] at hw
                        rcases hw with ⟨rfl, _⟩
                        have hsm := otrEncrypt_serialized_len_le P ptext
                          (serializeAddrVals (serviceIdParse uuidTryParse) me peer) coins
                          otr otr'' sm
                          (fun ad had => Nat.le_of_eq (serializeAddrVals_len_36 had)) he
                        have hpk := preKeyMsgNew_serialized_len_le
                          otr''.sessionVersion s.localRegistrationId items.preKeyId
                          items.signedPreKeyId
                          (s.pendingKyberPreKey.map fun k => ⟨k.preKeyId, k.ciphertext⟩)
                          items.baseKey otr''.localIdentityKey sm
                          (fun k hk_eq => by
                            rcases hsk : s.pendingKyberPreKey with _ | k0 <;> rw [hsk] at hk_eq
                            · cases hk_eq
                            · simp only [Option.map_some, Option.some.injEq] at hk_eq
                              rw [← hk_eq]
                              exact Nat.le_of_eq (hSessP.2.2.1 k0 hsk))
                          (by omega)
                        omega

/-! ## 3. Call-Site Envelopes and Callee Slot Containment Bridges -/

/-- Binary-kit `W3` (`init`) slot envelope (`InitGhost → List AllocEvent → Prop`,
`RecordAliceInitiatedAnyCkBounds`). -/
def realCliInitBinarySlotEnv (W : CliHooks) (x : InitGhost) (evs : List AllocEvent) : Prop :=
  ∃ w : W3BinaryInitParams,
    w.x = x ∧ w.F = W.C.F ∧
    w.x_spqr.p.authKey.length ≤ 32 ∧
    RecordGhostValid w.g_rec w.r_rec ∧
    RecordAliceInitiatedAnyCkBounds w.g_rec w.r_rec ∧
    W3InitBinaryKitSlotEnv w evs

private theorem w4TryDecryptCallDomOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.W4TryDecryptCall F}
    (h : W4TryDecryptCallDomOf F K c₁ td) :
    W4TryDecryptCallDomOf F K c₂ td :=
  { h with ct_le := Nat.le_trans h.ct_le hc }

private theorem w4FailedTdDomOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂)
    {fc : LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.W4FailedTryDecryptCall F}
    (h : W4FailedTdDomOf F K c₁ fc) :
    W4FailedTdDomOf F K c₂ fc :=
  ⟨w4TryDecryptCallDomOf_mono hc h.td_dom, h.align_le, h.cancel_live⟩

private theorem w4ArchivedTrialDomOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂)
    {tr : LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.W4ArchivedTrial F}
    (h : W4ArchivedTrialDomOf F K c₁ tr) :
    W4ArchivedTrialDomOf F K c₂ tr :=
  ⟨h.enc_le, h.live_le_peak, h.live_le_drop, h.drop_caps, h.tr_gv, h.tr_dom,
    w4FailedTdDomOf_mono hc h.tr_fail⟩

private theorem w4TryDecryptPathACDomOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂)
    {td : LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot.W4TryDecryptCall F}
    (h : W4TryDecryptPathACDomOf F K c₁ td) :
    W4TryDecryptPathACDomOf F K c₂ td :=
  ⟨w4TryDecryptCallDomOf_mono hc h.base, h.zero_skip⟩

/-- Structural call-site guard on `W4RecvPrekeyRealParams` at `(F, K, maxCt, peerVal, files)`
(`rfl`-identical to `RealCliDecPkLinked.W4BinaryCallSiteDom`). -/
abbrev W4BinaryCallSiteDom :=
  LibsignalBinary.Proofs.PeakBudget.RealCliDecPkLinked.W4BinaryCallSiteDom

/-- Widened binary-kit `W4` (`recv-prekey`) slot envelope (`DecPkGhost → List AllocEvent → Prop`)
over `W4BinaryRecvPrekeyParams` and `W4BinaryRecvPrekeyWideSlotEnv`. -/
abbrev realCliDecPkBinaryWideSlotEnv [LibsignalPlacement]
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParams,
    W4BinaryCallSiteDom W.C.F W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnv w4 evs

theorem realCliDecPkBinaryWideSlotEnv_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnv X W x = realCliDecPkBinaryWideSlotEnv X W y := by
  funext evs
  simp only [realCliDecPkBinaryWideSlotEnv, hp, hf, hmsg]

/-- Canonical-outer split `PksmGhost` envelope: `PksmCanonSliceEnv x.bytes` on canonical outer
`PreKeyMessageFields` slices (`∃ m, x.bytes = m.bytes`), and `FallbackEnv x` otherwise. -/
def CanonicalOrFallbackPksmEnv
    (FallbackEnv : PksmGhost → List AllocEvent → Prop)
    (x : PksmGhost) (evs : List AllocEvent) : Prop :=
  ((∃ m : PreKeyMessageFields, x.bytes = m.bytes) ∧ PksmCanonSliceEnv x.bytes evs) ∨
    ((¬ ∃ m : PreKeyMessageFields, x.bytes = m.bytes) ∧ FallbackEnv x evs)

/-- Generic `PKSM` containment into `(mkBinaryKitRealCalleeEnvs img S X W g).pksmEnv` under
`CliPqxdhInputs ⟨W.C, W.Q⟩ g.i` for any `PksmTryFromEnv` implying `PksmCanonSliceEnv x.bytes` on
canonical outer `PreKeyMessageFields`. -/
theorem pksmCanonicalGuard_sub_binaryKit [LibsignalPlacement]
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (peerV : AddrV) (rest : List (BitVec 8))
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    {x : PksmGhost} (hx : x.bytes = rest) {evs : List AllocEvent}
    (himp : (∃ m : PreKeyMessageFields, x.bytes = m.bytes) →
      PksmTryFromEnv x evs → PksmCanonSliceEnv x.bytes evs)
    (hevs : PksmTryFromEnv x evs) :
    (mkBinaryKitRealCalleeEnvs img S X W g).pksmEnv rest evs := by
  obtain ⟨m, hm, _⟩ := cliPqInputs_recv_prekey_canonical hi (hc ▸ hparse) hst
  have hsub : PksmCanonSliceEnv x.bytes evs := himp ⟨m, hx.trans hm⟩ hevs
  simpa [mkBinaryKitRealCalleeEnvs, hx] using hsub

/-- `CanonicalOrFallbackPksmEnv FallbackEnv` containment into
`(mkBinaryKitRealCalleeEnvs img S X W g).pksmEnv` under `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`. -/
theorem pksmCanonicalOrFallback_sub_binaryKit [LibsignalPlacement]
    {FallbackEnv : PksmGhost → List AllocEvent → Prop}
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (peerV : AddrV) (rest : List (BitVec 8))
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    {x : PksmGhost} (hx : x.bytes = rest) {evs : List AllocEvent}
    (hevs : CanonicalOrFallbackPksmEnv FallbackEnv x evs) :
    (mkBinaryKitRealCalleeEnvs img S X W g).pksmEnv rest evs :=
  pksmCanonicalGuard_sub_binaryKit img S X W g peerV rest hi hparse hc hst hx
    (fun hcan h => h.elim And.right (fun hn => False.elim (hn.1 hcan)))
    hevs

/-- `PreKeyTryFromEnv SigTryFromConcreteEnv` containment into
`(mkBinaryKitRealCalleeEnvs img S X W g).pksmEnv` on canonical `PreKeyMessageFields` under
`CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`. -/
theorem pksmPreKeyTryFrom_sub_binaryKit [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (peerV : AddrV) (rest : List (BitVec 8))
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    {ptr sret : BitVec 64} {evs : List AllocEvent}
    (hevs : ∀ m : PreKeyMessageFields, rest = m.bytes →
      PreKeyTryFromEnv SigTryFromConcreteEnv (preKeyArgsOfFields ptr sret m) evs) :
    (mkBinaryKitRealCalleeEnvs img S X W g).pksmEnv rest evs := by
  obtain ⟨m, hm, _⟩ := cliPqInputs_recv_prekey_canonical hi (hc ▸ hparse) hst
  have hsub : PksmCanonSliceEnv m.bytes evs :=
    preKeyTryFromConcrete_m_sub_pksmCanonSlice ptr sret m (hevs m hm)
  simpa [mkBinaryKitRealCalleeEnvs, ← hm] using hsub

/-- `PksmCanonSliceEnv` containment into `(mkBinaryKitRealCalleeEnvs img S X W g).pksmEnv`. -/
theorem pksmCanonSlice_sub_binaryKit [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (rest : List (BitVec 8)) {evs : List AllocEvent}
    (hevs : PksmCanonSliceEnv rest evs) :
    (mkBinaryKitRealCalleeEnvs img S X W g).pksmEnv rest evs :=
  hevs

/-- `W3` (`init`) containment into `(mkBinaryKitRealCalleeEnvs img S X W g).initEnv`. -/
theorem w3_realCliInitBinarySlotEnv_sub_binaryKit [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (peerV : AddrV) (dir : List (BitVec 8)) (d2 : Init2Data)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hc : g.c = .init peerV dir)
    (_hpeerV : d2.peerV = peerV)
    (hpeerVal : d2.peerG.val = addrValOf peerV)
    {evs : List AllocEvent}
    (hevs : realCliInitBinarySlotEnv W (r1cInitGhost g d2 0#64) evs) :
    (mkBinaryKitRealCalleeEnvs img S X W g).initEnv evs := by
  obtain ⟨w, hx, _hF, hspqr, hgv, halice, hslot⟩ := hevs
  have hparse_init :
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.init peerV dir) :=
    hc ▸ hparse
  have hp40 : peerV.name.length ≤ 40 := parseArgs_peer_name_length_le hparse_init
  have hdom : W3BinaryInitDom g.c g.i w := by
    intro pV d hc'
    rcases CallV.init.inj (hc.symm.trans hc') with ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, hspqr, hgv, halice⟩
    · rw [hx]
      exact hpeerVal
    · rw [hx]
      change d2.peerG.val.name.length ≤ 40
      rw [hpeerVal]
      exact hp40
    · rw [hx]
      rfl
  dsimp only [mkBinaryKitRealCalleeEnvs]
  rw [hc]
  exact ⟨w, hc ▸ hdom, hslot⟩

/-- `W1` (`send`) containment into `(mkBinaryKitRealCalleeEnvs img S X W g).encEnv`. -/
theorem w1_cliEncryptSlotEnv_sub_binaryKit [LibsignalPlacement] {M : AllocCostModel}
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (g : RunCall) (meG : AddrGhost) (peerV : AddrV)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .send peerV)
    {evs : List AllocEvent}
    (hevs : CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B SpqrSendTightCapEnv
      (w1BinarySessKitPlacedBudget A.repAlloc B)
      (w1BinaryIdKitPlacedBudget A.repAlloc B)
      (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) evs) :
    (mkBinaryKitRealCalleeEnvs img S X W g).encEnv evs := by
  let w1R : W1BinarySendParams :=
    ⟨A.repAlloc, B, r2PeerGhost0 peerV, r2EncGhost g (r2PeerGhost0 peerV) meG 0#64⟩
  have hptext : g.i.stdin.length ≤ msgCapBytes := send_stdin_length_le_msgCapBytes hin hc
  have hdom : W1BinarySendDom g.c g.i w1R := by
    intro pAddr hpAddr
    rw [hc] at hpAddr
    injection hpAddr with hpEq
    subst hpEq
    exact ⟨rfl, rfl, rfl, hptext, rfl⟩
  dsimp only [mkBinaryKitRealCalleeEnvs]
  rw [hc]
  exact ⟨w1R, hc ▸ hdom, hevs⟩

/-- `W1` (`send`) serialized `SignalMessage` length bound (`≤ sessionCapBytes`). -/
theorem w1_send_out_serialized_le_sessionCapBytes
    {S : RunSem} (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (peerV meV : AddrV) (f : StoresGhost) (m : SignalMessage)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .send peerV)
    (henc : S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV)
      g.i.stdin (coinsOf g.i) = some (some (f, .signalMessage m)))
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl) :
    m.serialized.length ≤ sessionCapBytes := by
  rw [hS_enc] at henc
  exact encDef_some_out_bounds ⟨W.C, W.Q⟩ (runFiles g.i) (addrValOf peerV) (addrValOf meV)
    g.i.stdin (coinsOf g.i) f (.signalMessage m) (send_stdin_length_le_msgCapBytes hin hc) henc

/-- `W1` (`send`) serialized `PreKeySignalMessage` length bound (`≤ sessionCapBytes`). -/
theorem w1_send_outPk_serialized_le_sessionCapBytes
    {S : RunSem} (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (peerV meV : AddrV) (f : StoresGhost) (m : PreKeySignalMessage)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .send peerV)
    (henc : S.encrypt (runFiles g.i) (addrValOf peerV) (addrValOf meV)
      g.i.stdin (coinsOf g.i) = some (some (f, .preKeySignalMessage m)))
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl) :
    m.serialized.length ≤ sessionCapBytes := by
  rw [hS_enc] at henc
  exact encDef_some_out_bounds ⟨W.C, W.Q⟩ (runFiles g.i) (addrValOf peerV) (addrValOf meV)
    g.i.stdin (coinsOf g.i) f (.preKeySignalMessage m) (send_stdin_length_le_msgCapBytes hin hc) henc

/-- `W2` (`recv` whisper) containment into `(mkBinaryKitRealCalleeEnvs img S X W g).decSigEnv`. -/
theorem w2_cliDecryptSignalSlotEnv_sub_binaryKit [LibsignalPlacement] {M : AllocCostModel}
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (g : RunCall) (meG : AddrGhost) (peerV : AddrV) (rest : List (BitVec 8)) (m : SignalMessage)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 2#8 :: rest)
    (htr : SignalMessage.tryFrom protoSignalCodec rest = .ok m)
    {evs : List AllocEvent}
    (hevs : CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (W2RealTdEnv W.C.F W.Q.K)
      (decBinarySessKitPlacedBudget A.repAlloc B)
      (decBinaryIdKitPlacedBudget A.repAlloc B)
      (r3aDecSigGhost0 g peerV meG m) evs) :
    (mkBinaryKitRealCalleeEnvs img S X W g).decSigEnv evs := by
  let x := r3aDecSigGhost0 g peerV meG m
  let w2R : W2BinaryWhisperParams := ⟨A.repAlloc, B, x.peer, x⟩
  have hct_rest : m.ciphertext.length ≤ rest.length :=
    (signalMessage_tryFrom_lengths_le htr).2.1
  have hrest_cap : rest.length ≤ msgCapBytes :=
    recv_rest_length_le_msgCapBytes hin hc hst
  have hct_cap : m.ciphertext.length ≤ msgCapBytes :=
    Nat.le_trans hct_rest hrest_cap
  have hdom : W2BinaryWhisperDom g.c g.i w2R := by
    intro pAddr hpAddr
    rw [hc] at hpAddr
    injection hpAddr with hpEq
    subst hpEq
    exact ⟨rfl, rfl, rfl, hct_cap, rfl⟩
  dsimp only [mkBinaryKitRealCalleeEnvs]
  rw [hc]
  exact ⟨w2R, hc ▸ hdom, hevs⟩

/-- `W4` (`recv-prekey`) containment into `(mkBinaryKitRealCalleeEnvs img S X W g).decPkEnv`. -/
theorem w4_realCliDecPkBinaryWideSlotEnv_sub_binaryKit [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (meV : AddrV) (peerV : AddrV)
    (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    (hpk : S.pksmParse rest = some pm)
    {evs : List AllocEvent}
    (hevs : realCliDecPkBinaryWideSlotEnv X W (r3bDecPkGhost g meV peerV pm) evs)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    (mkBinaryKitRealCalleeEnvs img S X W g).decPkEnv evs := by
  obtain ⟨w4, hcs, _hik, _hbk, henv⟩ := hevs
  have hparse_recv : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
    hc ▸ hparse
  have hpk' : pksmParse rest = some pm := hS_pksm ▸ hpk
  have hct_rest : pm.message.ciphertext.length ≤ rest.length :=
    (pksmParse_lengths_le hpk').2.2.1
  have hrest_cap : rest.length ≤ msgCapBytes :=
    recv_rest_length_le_msgCapBytes hin hc hst
  have hct_cap : pm.message.ciphertext.length ≤ msgCapBytes :=
    Nat.le_trans hct_rest hrest_cap
  have hdom : W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w4.base :=
    hcs.toRealDomOf hparse_recv hct_cap
  have hdom4 : W4BinaryRecvPrekeyDom g.c g.i w4 := by
    intro pAddr hpAddr
    rw [hc] at hpAddr
    injection hpAddr with hpEq
    subst hpEq
    exact ⟨hcs.eq_peerVal, hdom.outer_dom.peer_len, hcs.eq_files, hcs.eq_rd, hdom⟩
  dsimp only [mkBinaryKitRealCalleeEnvs]
  rw [hc]
  exact ⟨w4, hc ▸ hdom4, henv⟩

end LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
