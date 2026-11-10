/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecryptPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegTailPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegExitPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded CLI `SegClone` Composition and `try_decrypt_from_record` Region Assembly

Assembles sub-segments 5–9 and `segClone_placed_ok`, then composes all five budget-threaded segment
proofs into `recordDecrypt_placed_region_ok` and `recordDecrypt_full_placed_region_ok` on CLI
Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto PublicKey SessionState)
open CryptoVerification (
  LibsignalPlacement lsmpl withLsCodeLoaded
  lsRustNoAllocShimSym lsRustAllocSym lsRustDeallocSym lsHandleErrorSym
)
open CryptoVerification.RustHeap (allocHookStack vecAt vecBuf vecU8At vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (ChainGhost VecGhost chainAt vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SenderChainGhost SessionGhost UuidParser uuidTryParse
  optSenderChainAt optTailVecAt protocolAddressAt sessionStateAt signalMessageAt
)
open CryptoVerification.LibsignalTripleRatchet (
  RecordDecryptGhost SpqrModel region_ok rootStack
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (logClosurePlacedSpec lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  OptSenderChainInline bytes104OfW6Q chunks96_6QAt optSenderChainHeap
)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel errsAt regionOutcome)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (
  DstVals OptKybClone OptPendClone SpillVals dstSlotsAt spillSlotsAt
  exists_unpack32_pair_of_length_8 stackAt_chainClone_eq_alloc
  segClone_dstSlotsWrittenAt segClone_dstSlotsWrittenAt_entails_sessionStateAt
  segClone_sessionStateAt_0x138_eq segClone_setWidth_64_truncate_32
  segClone_srcSessionState_reassemble segClone_vecAt_0x180_chains_eq
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463)
open CryptoVerification.Cli.CoinsTape (cliTapeAt)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (
  LibsignalCodeRoLoaded recEntryPlaced recExitPlaced recFramePlaced
  recMPCPlaced recMetaPlaced recVPCPlaced
)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps (SepWPpCl)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget SeqEnv fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec
  growOneSpeSpec setSessionStateSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  chainCloneSpec senderChainCloneSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  FromFEnv FromMEnv FromVEnv RecordDecryptEnv SeamBudget SegCloneEnv SegTailEnv
  TryDecryptEnvArgs optTailCloneEvents recordTryDecryptEnvArgs segCloneEvents vecCloneEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget (
  MStatePlaced SegClonePlacedSpec VStatePlaced
  recordDecryptPlacedSpec recordDecrypt_placed_region_ok_of_seams tryDecryptPlacedSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  SegCloneHooks segClone_clonePostPlaced segClone_fields_10_to_11_placed
  segClone_fixedRestPlaced segClone_fixedRest_reassemble_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeysPlacedBudget (
  fields1To4Events segClone_entry_combined_placed segClone_fields_1_to_4_placed
  senderChainOptCloneEvents
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudget (
  segClone_pendingKyber_placed segClone_pendingPreKey_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChainsPlacedBudgetAux (
  receiverChainsCloneEvents segClone_receiverChains_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlacedBudgetAux (
  pqRatchetCloneEvents segClone_aliceBaseKey_placed segClone_pqRatchet_placed
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecryptPlacedBudget (segDecrypt_placed_ok)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget (segMismatch_placed_ok)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegTailPlacedBudget (segTail_placed_ok)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegExitPlacedBudget (segExit_placed_ok)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Envelope Splitting and Inhabitedness Helpers -/

/-- Events emitted by sub-segments 5–9 (`receiverChains`, `pendingPreKey`, `pendingKyber`,
    `aliceBaseKey`, `pqRatchetState`). -/
def fields5To9Events (G : SessionGhost) (st : SessionState (List (BitVec 8))) : List AllocEvent :=
  receiverChainsCloneEvents G.chains st.receiverChains ++
  (optTailCloneEvents G.pending ++
    (optTailCloneEvents G.kyber ++
      (vecCloneEvents G.alice ++ pqRatchetCloneEvents st.pqRatchetState)))

theorem segCloneEvents_eq_split (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    segCloneEvents G st = fields1To4Events G st ++ fields5To9Events G st := by
  cases hgs : G.sender <;> cases hsc : st.senderChain <;>
    by_cases hrc : st.receiverChains = [] <;> by_cases hpq : st.pqRatchetState.length = 0 <;>
      simp [segCloneEvents, fields1To4Events, senderChainOptCloneEvents, fields5To9Events,
        receiverChainsCloneEvents, pqRatchetCloneEvents, hgs, hsc, hrc, hpq, List.append_assoc]

theorem fromMEnv_inhabited : ∃ evs, FromMEnv evs := by
  have hgrow : GrowOneSpeEnv 0#64 (rustAllocEvents (4 * 48) 8) := Or.inl ⟨rfl, rfl⟩
  have htail : SegTailEnv ([] ++ rustAllocEvents 17 1) := SeqEnv.append FreeOnlyEvs.nil rfl
  have hfromF : FromFEnv (([] ++ rustAllocEvents 17 1) ++ []) :=
    SeqEnv.append htail FreeOnlyEvs.nil
  exact ⟨_, SeqEnv.append hgrow hfromF⟩

/-- Concrete `try_decrypt_with_state` envelopes (`TryDecryptEnv`, etc.) are inhabited on every
    version-matching `RecordDecryptGhost` input (needed to extract `FitsEvents` for `segCloneEvents`
    from `FitsEnv M lim st_init (RecordDecryptEnv tdEnv x)`). -/
def TdEnvInhabited (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  ∀ x : RecordDecryptGhost,
    x.st.version.toNat = x.msg.messageVersion.toNat →
    ∃ G₁ evs, CloneRel x.G G₁ ∧ tdEnv (recordTryDecryptEnvArgs x G₁) evs

theorem fitsEvents_segClone_of_recordDecryptEnv {M : AllocCostModel} {lim : BudgetLimits}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {st_init : M.σ}
    (htd_ne : TdEnvInhabited tdEnv)
    (hfit : FitsEnv M lim st_init (RecordDecryptEnv tdEnv x)) :
    FitsEvents M lim st_init (segCloneEvents x.G x.st) := by
  by_cases hver : x.st.version.toNat = x.msg.messageVersion.toNat
  · obtain ⟨G₀, evs_td, hcl0, htd0⟩ := htd_ne x hver
    have hfv : FromVEnv tdEnv x G₀ (evs_td ++ []) :=
      SeqEnv.append htd0 (Or.inl FreeOnlyEvs.nil)
    have hrec : RecordDecryptEnv tdEnv x (segCloneEvents x.G x.st ++ (evs_td ++ [])) := by
      unfold RecordDecryptEnv
      simp only [hver, ↓reduceIte]
      exact ⟨G₀, hcl0, SeqEnv.append rfl hfv⟩
    exact ((fitsEvents_append M lim (segCloneEvents x.G x.st) (evs_td ++ []) st_init).mp
      (hfit _ hrec)).1
  · obtain ⟨evs_m, hm_env⟩ := fromMEnv_inhabited
    have hrec : RecordDecryptEnv tdEnv x (segCloneEvents x.G x.st ++ evs_m) := by
      unfold RecordDecryptEnv
      simp only [hver, ↓reduceIte]
      exact SeqEnv.append rfl hm_env
    exact ((fitsEvents_append M lim (segCloneEvents x.G x.st) evs_m st_init).mp
      (hfit _ hrec)).1

/-! ## Sub-Segments 5–9 and `segClone_wp_placed` -/

/-- Combined sub-segments 5–9 (`+0x544 / +0x300 → +0x594`):
    clones `receiver_chains`, `pending_pre_key`, `pending_kyber_pre_key`, `alice_base_key`,
    and `pq_ratchet_state`, threading `A.pool` across `fields5To9Events x.G x.st`. -/
theorem segClone_fields_5_to_9_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : String → Option (State → State)}
    (hA : SegCloneHooks A lim H)
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H)
      (lsmpl.base 468) (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    {x : RecordDecryptGhost} {s0 s : State}
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (hQp_false : ∀ sf P_p, sf.status = .Panicked → Qp sf ((⌜False⌝ : SepProp) ∗ P_p))
    {v00 v08 v18 v30 : BitVec 64} {v14 v24 v28 v2c v3c : BitVec 32}
    {w288 w28c : BitVec 32} {F : SepProp}
    (hfits : FitsEvents M lim st (fields5To9Events x.G x.st))
    (hpc : s.pc = (if x.st.receiverChains = []
      then (blkPl_463).base + 1348#64
      else (blkPl_463).base + 768#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = x.st.sessionVersion.setWidth 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.st.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
      (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32)
      (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32)
      (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (blkPl_463).base + 1428#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' →
      s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = w288.setWidth 64 →
      s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = w28c.setWidth 64 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = pendCap' →
      s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = chainsPtr' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      chains'.length = x.st.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.st.receiverChains.length →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool lim (M.stepEvents (fields5To9Events x.G x.st) st) s1 ∗
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
            (x.G.chains.zip x.st.receiverChains) ∗
          vecGhostAt A.repAlloc x.G.alice (s.sp + 0x198#64) ∗
          vecU8At A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          optTailVecAt A.repAlloc 48 (s.sp + 0x230#64) x.G.pending ∗
          optTailVecAt A.repAlloc 32 (s.sp + 0x260#64) x.G.kyber ∗
          ((s.sp + 0x288#64) ↦₃₂ w288) ∗
          ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
            (chains'.zip x.st.receiverChains) ∗
          vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
          vecU8Buf A.repAlloc pqCap' pqPtr' x.st.pqRatchetState ∗
          OptPendClone A.repAlloc x.G.pending pendCap' pendPtr' ∗
          OptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' ∗
          (s.sp ↦₆₄ kybPtr') ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗
          ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          ((s.sp + 0x30#64) ↦₆₄ chainsCap') ∗
          ((s.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q Qp) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool lim st s ∗
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A.repAlloc x.G.alice (s.sp + 0x198#64) ∗
        vecU8At A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optTailVecAt A.repAlloc 48 (s.sp + 0x230#64) x.G.pending ∗
        optTailVecAt A.repAlloc 32 (s.sp + 0x260#64) x.G.kyber ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗
        ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        (s.sp ↦₆₄ v00) ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗
        ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗
        ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q Qp := by
  obtain ⟨hfit_rc, hfit_69⟩ := (fitsEvents_append M lim _ _ st).mp hfits
  obtain ⟨hfit_pend, hfit_79⟩ := (fitsEvents_append M lim _ _ _).mp hfit_69
  obtain ⟨hfit_kyb, hfit_89⟩ := (fitsEvents_append M lim _ _ _).mp hfit_79
  obtain ⟨hfit_alice, hfit_pq⟩ := (fitsEvents_append M lim _ _ _).mp hfit_89
  rw [segClone_vecAt_0x180_chains_eq A.repAlloc s.sp x.G.chainsCap x.G.chainsPtr
      x.G.chains x.st.receiverChains hchains_len]
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim st s ∗
            ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            memRegion (s.sp + 0x5f0#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            (((s.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗
              ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              vecGhostAt A.repAlloc x.G.alice (s.sp + 0x198#64) ∗
              vecU8At A.repAlloc (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A.repAlloc 48 (s.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A.repAlloc 32 (s.sp + 0x260#64) x.G.kyber ∗
              ((s.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s.sp ↦₆₄ v00) ∗
              ((s.sp + 0x08#64) ↦₆₄ v08) ∗
              ((s.sp + 0x14#64) ↦₃₂ v14) ∗
              ((s.sp + 0x18#64) ↦₆₄ v18) ∗
              ((s.sp + 0x24#64) ↦₃₂ v24) ∗
              ((s.sp + 0x28#64) ↦₃₂ v28) ∗
              ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
              ((s.sp + 0x30#64) ↦₆₄ v30) ∗
              ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine segClone_receiverChains_placed hA hchainClone x s0 s ret hQp_false _
    hfit_rc hpc hrun hsp hx26 htr hchains_len
    fun s1 chainsCap' chainsPtr' chains' hchains_l hchains_c hpc1 hrun1 hsp1 hspA1
      hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
  rw [← hsp1]
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim (M.stepEvents (receiverChainsCloneEvents x.G.chains x.st.receiverChains) st) s1 ∗
            optTailVecAt A.repAlloc 48 (s1.sp + 0x230#64) x.G.pending ∗
            ((s1.sp + 0x08#64) ↦₆₄ v08) ∗
            ((s1.sp + 0x18#64) ↦₆₄ v18) ∗
            ((s1.sp + 0x24#64) ↦₃₂ v24) ∗
            ((s1.sp + 0x28#64) ↦₃₂ v28) ∗
            ((s1.sp + 0x2c#64) ↦₃₂ v2c) ∗
            stackAt s1.sp allocHookStack ∗
            (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s1.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
                (chains'.zip x.st.receiverChains) ∗
              vecGhostAt A.repAlloc x.G.alice (s1.sp + 0x198#64) ∗
              vecU8At A.repAlloc (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A.repAlloc 32 (s1.sp + 0x260#64) x.G.kyber ∗
              ((s1.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s1.sp ↦₆₄ v00) ∗
              ((s1.sp + 0x14#64) ↦₃₂ v14) ∗
              ((s1.sp + 0x30#64) ↦₆₄ v30) ∗
              ((s1.sp + 0x3c#64) ↦₃₂ v3c) ∗
              memRegion (s1.sp + 0x5f0#64) 104 ∗
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by
      rw [segClone_vecAt_0x180_chains_eq A.repAlloc s1.sp x.G.chainsCap x.G.chainsPtr
            x.G.chains x.st.receiverChains hchains_len,
          stackAt_chainClone_eq_alloc s1.sp]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine segClone_pendingPreKey_placed hA hfit_pend hpc1 hrun1 hspA1 htr1
    fun s2 pendCap' pendPtr' v08' v24' v28' v2c' hpc2 hrun2 hsp2 hspA2
      hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
  rw [← hsp2]
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim
            (M.stepEvents (optTailCloneEvents x.G.pending)
              (M.stepEvents (receiverChainsCloneEvents x.G.chains x.st.receiverChains) st)) s2 ∗
            optTailVecAt A.repAlloc 32 (s2.sp + 0x260#64) x.G.kyber ∗
            (s2.sp ↦₆₄ v00) ∗
            ((s2.sp + 0x14#64) ↦₃₂ v14) ∗
            ((s2.sp + 0x3c#64) ↦₃₂ v3c) ∗
            stackAt s2.sp allocHookStack ∗
            (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
                (chains'.zip x.st.receiverChains) ∗
              optTailVecAt A.repAlloc 48 (s2.sp + 0x230#64) x.G.pending ∗
              OptPendClone A.repAlloc x.G.pending pendCap' pendPtr' ∗
              vecGhostAt A.repAlloc x.G.alice (s2.sp + 0x198#64) ∗
              vecU8At A.repAlloc (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              ((s2.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
              ((s2.sp + 0x08#64) ↦₆₄ v08') ∗
              ((s2.sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((s2.sp + 0x24#64) ↦₃₂ v24') ∗
              ((s2.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s2.sp + 0x2c#64) ↦₃₂ v2c') ∗
              ((s2.sp + 0x30#64) ↦₆₄ v30) ∗
              memRegion (s2.sp + 0x5f0#64) 104 ∗
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine segClone_pendingKyber_placed hA hfit_kyb hpc2 hrun2 hspA2 htr2
    fun s3 kybCap' kybPtr' v14' hpc3 hrun3 hsp3 hspA3
      hx19_3 hx22_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 htr3 => ?_
  have hx25_2' : (s2.readReg64 .x25).truncate 32 = x.st.sessionVersion := by
    rw [hx25_2, hx25_1, hx25, segClone_setWidth_64_truncate_32]
  rw [hx25_2', ← hsp3]
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim
            (M.stepEvents (optTailCloneEvents x.G.kyber)
              (M.stepEvents (optTailCloneEvents x.G.pending)
                (M.stepEvents (receiverChainsCloneEvents x.G.chains x.st.receiverChains) st))) s3 ∗
            vecGhostAt A.repAlloc x.G.alice (s3.sp + 0x198#64) ∗
            ((s3.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗
            ((s3.sp + 0x30#64) ↦₆₄ v30) ∗
            stackAt s3.sp allocHookStack ∗
            (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
                (chains'.zip x.st.receiverChains) ∗
              optTailVecAt A.repAlloc 48 (s3.sp + 0x230#64) x.G.pending ∗
              OptPendClone A.repAlloc x.G.pending pendCap' pendPtr' ∗
              optTailVecAt A.repAlloc 32 (s3.sp + 0x260#64) x.G.kyber ∗
              OptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' ∗
              vecU8At A.repAlloc (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              (s3.sp ↦₆₄ kybPtr') ∗ ((s3.sp + 0x08#64) ↦₆₄ v08') ∗
              ((s3.sp + 0x14#64) ↦₃₂ v14') ∗ ((s3.sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((s3.sp + 0x24#64) ↦₃₂ v24') ∗ ((s3.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s3.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s3.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
              memRegion (s3.sp + 0x5f0#64) 104 ∗
              memRegion (s3.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine segClone_aliceBaseKey_placed hA hfit_alice hpc3 hrun3 hspA3 htr3
    fun s4 alice' hpc4 hrun4 hsp4 hspA4
      hx19_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4 halice_b halice_c => ?_
  have hx26_3' : s3.readReg64 .x26 = chainsCap' := by
    rw [hx26_3, hx26_2, hx26_1, ← hchains_c]
  rw [hx26_3', ← hsp4]
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim
            (M.stepEvents (vecCloneEvents x.G.alice)
              (M.stepEvents (optTailCloneEvents x.G.kyber)
                (M.stepEvents (optTailCloneEvents x.G.pending)
                  (M.stepEvents (receiverChainsCloneEvents x.G.chains x.st.receiverChains) st)))) s4 ∗
            vecU8At A.repAlloc (s4.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            stackAt s4.sp allocHookStack ∗
            (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s4.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A.repAlloc x.G.alice (s4.sp + 0x198#64) ∗
              optTailVecAt A.repAlloc 48 (s4.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A.repAlloc 32 (s4.sp + 0x260#64) x.G.kyber ∗
              ((s4.sp + 0x288#64) ↦₃₂ w288) ∗ ((s4.sp + 0x28c#64) ↦₃₂ w28c) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
                (chains'.zip x.st.receiverChains) ∗
              vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
              OptPendClone A.repAlloc x.G.pending pendCap' pendPtr' ∗
              OptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' ∗
              (s4.sp ↦₆₄ kybPtr') ∗ ((s4.sp + 0x08#64) ↦₆₄ v08') ∗
              ((s4.sp + 0x14#64) ↦₃₂ v14') ∗ ((s4.sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((s4.sp + 0x24#64) ↦₃₂ v24') ∗ ((s4.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s4.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s4.sp + 0x30#64) ↦₆₄ chainsCap') ∗
              ((s4.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
              memRegion (s4.sp + 0x5f0#64) 104 ∗
              memRegion (s4.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  have hx24_4' : s4.readReg64 .x24 = s4.sp + 0xca0#64 := by reg_chain
  refine segClone_pqRatchet_placed hA hfit_pq hpc4 hrun4 hspA4 hx24_4' htr4
    fun s5 pqCap' pqPtr' hpc5 hrun5 hsp5 hspA5
      hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5 htr5 hpq_c => ?_
  have hsp_eq : s4.sp = s.sp := by reg_chain
  have hst_fold :
      M.stepEvents (pqRatchetCloneEvents x.st.pqRatchetState)
        (M.stepEvents (vecCloneEvents x.G.alice)
          (M.stepEvents (optTailCloneEvents x.G.kyber)
            (M.stepEvents (optTailCloneEvents x.G.pending)
              (M.stepEvents (receiverChainsCloneEvents x.G.chains x.st.receiverChains) st)))) =
      M.stepEvents (fields5To9Events x.G x.st) st := by
    simp only [fields5To9Events, M.stepEvents_append]
  rw [hsp_eq] at hx24_5 ⊢
  rw [hst_fold]
  refine SepWPpCl.weaken_pre
    (by rw [stackAt_chainClone_eq_alloc s.sp]; exact Entails.of_eq (by sep_ac_rfl))
    (hnext s5 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr'
      hpc5 hrun5 (by reg_chain) hspA5
      (by reg_chain) hx20_5 (by reg_chain) hx22_5 (by reg_chain) hx24_5
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
      htr5 hchains_l hchains_c halice_b halice_c hpq_c)

/-- Full budget-threaded relocatable CLI `SepWPpCl` for `SegClone` (`+0x1a8 → +0x69c / +0x7e4`),
    advancing `A.pool` from `st` to `M.stepEvents (segCloneEvents x.G x.st) st` with `onOom = ⌜False⌝`
    and `onPanic = ⌜False⌝`. -/
theorem segClone_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    (hA : SegCloneHooks A lim H)
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H)
      (lsmpl.base 468) (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (hsenderClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H)
      (lsmpl.base 468) (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)))
    (x : RecordDecryptGhost) (s0 : State)
    (hfits : FitsEvents M lim st (segCloneEvents x.G x.st))
    (hpc : s0.pc = (blkPl_463).base + 424#64)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (h27 : s0.readReg64 .x27 = x.sret) (h19 : s0.readReg64 .x19 = x.remA)
    (h23 : s0.readReg64 .x23 = s0.sp + 0x5f0#64) (h24 : s0.readReg64 .x24 = s0.sp + 0xca0#64)
    (hrc32 : x.st.receiverChains.length < 2 ^ 32) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H)
      (if x.st.version.toNat = x.msg.messageVersion.toNat then
         (blkPl_463).base + 1692#64
       else
         (blkPl_463).base + 2020#64)
      s0
      (memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A.repAlloc (s0.sp + 0x138#64) x.G x.st ∗
        memRegion (s0.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        cliTapeAt ctl x.cur x.rest ∗ lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool lim st s0)
      (segClone_clonePostPlaced A lim st ctl x s0)
      (fun _ P_p => P_p ⊢ (⌜False⌝ : SepProp)) := by
  have hQp_false : ∀ (sf : State) (P_p : SepProp), sf.status = .Panicked →
      ((⌜False⌝ : SepProp) ∗ P_p ⊢ (⌜False⌝ : SepProp)) :=
    fun _ _ _ => Entails.pure_left False.elim
  have hfits_split :
      FitsEvents M lim st (fields1To4Events x.G x.st ++ fields5To9Events x.G x.st) :=
    segCloneEvents_eq_split x.G x.st ▸ hfits
  obtain ⟨hfit_14, hfit_59⟩ := (fitsEvents_append M lim _ _ st).mp hfits_split
  have hrc_lt : x.st.receiverChains.length < 2 ^ 63 := by omega
  rw [segClone_sessionStateAt_0x138_eq A.repAlloc s0.sp x.G x.st]
  refine SepWPpCl.weaken_pre
    (P' := ⌜PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey ∧
            (match x.st.remoteIdentity with
             | none => x.G.remoteIk.bytes = []
             | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey) ∧
            x.G.chains.length = x.st.receiverChains.length ∧
            x.G.pending.isSome = x.st.pendingPreKey ∧ x.G.regIds.length = 8 ∧
            x.G.localIk.bytes.length = 33 ∧
            (x.st.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)⌝ ∗
          (memRegion s0.sp 0xa0 ∗
            ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
            vecGhostAt A.repAlloc x.G.localIk (s0.sp + 0x138#64) ∗
            vecGhostAt A.repAlloc x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A.repAlloc (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A.repAlloc x.G.alice (s0.sp + 0x198#64) ∗
            vecU8At A.repAlloc (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A.repAlloc (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A.repAlloc 48 (s0.sp + 0x230#64) x.G.pending ∗
            optTailVecAt A.repAlloc 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦ₛ x.G.regIds) ∗
            memRegion (s0.sp + 0x4b0#64) 0x950 ∗
            protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
            signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
            cliTapeAt ctl x.cur x.rest ∗ lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool lim st s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine SepWPpCl.pure_elim fun
      ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  obtain ⟨w288, w28c, _, h_reg_pts⟩ := exists_unpack32_pair_of_length_8 h_reg_len
  have h28c : s0.sp + 0x288#64 + 4#64 = s0.sp + 0x28c#64 := by bv_arith
  rw [h_reg_pts (s0.sp + 0x288#64), h28c]
  refine SepWPpCl.weaken_pre
    (P' := memRegion s0.sp 0xa0 ∗
            ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
            vecGhostAt A.repAlloc x.G.localIk (s0.sp + 0x138#64) ∗
            memRegion (s0.sp + 0x4b0#64) 0x950 ∗
            protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
            signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
            cliTapeAt ctl x.cur x.rest ∗ lsLogOff ∗ stackAt s0.sp rootStack ∗
            (A.pool lim st s0 ∗
              vecGhostAt A.repAlloc x.G.remoteIk (s0.sp + 0x150#64) ∗
              vecU8At A.repAlloc (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr
                (keyToBytes32 x.st.rootKey) ∗
              vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A.repAlloc x.G.alice (s0.sp + 0x198#64) ∗
              vecU8At A.repAlloc (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optSenderChainAt A.repAlloc (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              optTailVecAt A.repAlloc 48 (s0.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A.repAlloc 32 (s0.sp + 0x260#64) x.G.kyber ∗
              ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              ((s0.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s0.sp + 0x28c#64) ↦₃₂ w28c)))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine segClone_entry_combined_placed (A := A) (ctl := ctl)
    hpc hrun hsp h19 h27 h23 h24 ⟨rfl, rfl⟩
    fun s1 sv dv bq0 bq1 bq2 bq3 bq4 bq5 hvm1 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1 => ?_
  have hpool1 := A.pool_transport lim st s0 s1 hvm1
  rw [← hsp1] at hx23_1 hx24_1 ⊢
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim st s1 ∗
            vecGhostAt A.repAlloc x.G.localIk (s1.sp + 0x138#64) ∗
            vecGhostAt A.repAlloc x.G.remoteIk (s1.sp + 0x150#64) ∗
            vecU8At A.repAlloc (s1.sp + 0x168#64) x.G.root.cap x.G.root.ptr
              (keyToBytes32 x.st.rootKey) ∗
            optSenderChainAt A.repAlloc (s1.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            chunks96_6QAt (s1.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s1.sp + 0x5f0#64) 104 ∗
            ((s1.sp + 0x40#64) ↦₆₄ sv.v40) ∗
            ((s1.sp + 0x48#64) ↦₆₄ sv.v48) ∗
            ((s1.sp + 0x54#64) ↦₃₂ sv.v54) ∗
            ((s1.sp + 0x58#64) ↦₆₄ sv.v58) ∗
            ((s1.sp + 0x60#64) ↦₆₄ sv.v60) ∗
            ((s1.sp + 0x68#64) ↦₆₄ sv.v68) ∗
            ((s1.sp + 0x70#64) ↦₆₄ sv.v70) ∗
            ((s1.sp + 0x78#64) ↦₆₄ sv.v78) ∗
            ((s1.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s1.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            ((s1.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            stackAt s1.sp chainCloneStack ∗
            (((s1.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗
              ((s1.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A.repAlloc x.G.alice (s1.sp + 0x198#64) ∗
              vecU8At A.repAlloc (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A.repAlloc 48 (s1.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A.repAlloc 32 (s1.sp + 0x260#64) x.G.kyber ∗
              ((s1.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s1.sp ↦₆₄ sv.v00) ∗
              ((s1.sp + 0x08#64) ↦₆₄ sv.v08) ∗
              ((s1.sp + 0x14#64) ↦₃₂ sv.v14) ∗
              ((s1.sp + 0x18#64) ↦₆₄ sv.v18) ∗
              ((s1.sp + 0x24#64) ↦₃₂ sv.v24) ∗
              ((s1.sp + 0x28#64) ↦₃₂ sv.v28) ∗
              ((s1.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
              ((s1.sp + 0x30#64) ↦₆₄ sv.v30) ∗
              ((s1.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
              memRegion (s1.sp + 0x10#64) 4 ∗
              memRegion (s1.sp + 0x20#64) 4 ∗
              memRegion (s1.sp + 0x38#64) 4 ∗
              memRegion (s1.sp + 0x50#64) 4 ∗
              dstSlotsAt s1.sp dv ∗
              ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
              segClone_fixedRestPlaced A ctl x s1.sp))
    (by
      unfold spillSlotsAt
      rw [hpool1,
          segClone_vecAt_0x180_chains_eq A.repAlloc s1.sp x.G.chainsCap x.G.chainsPtr
            x.G.chains x.st.receiverChains h_chains_len,
          stackAt_chainClone_eq_alloc s1.sp]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine segClone_fields_1_to_4_placed hA hsenderClone hQp_false hfit_14
    hpc1 hrun1 hspA1 hx23_1 htr1 hrc_lt
    fun s2 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc2 hrun2 hsp2 hspA2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 htr2
      hloc_b hloc_c hrem_b hrem_c hinl => ?_
  rw [← hsp2] at hx23_2 ⊢
  have hx24_2' : s2.readReg64 .x24 = s2.sp + 0xca0#64 := by reg_chain
  refine SepWPpCl.weaken_pre
    (P' := A.pool lim (M.stepEvents (fields1To4Events x.G x.st) st) s2 ∗
            vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A.repAlloc x.G.alice (s2.sp + 0x198#64) ∗
            vecU8At A.repAlloc (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optTailVecAt A.repAlloc 48 (s2.sp + 0x230#64) x.G.pending ∗
            optTailVecAt A.repAlloc 32 (s2.sp + 0x260#64) x.G.kyber ∗
            ((s2.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
            (s2.sp ↦₆₄ sv.v00) ∗
            ((s2.sp + 0x08#64) ↦₆₄ sv.v08) ∗
            ((s2.sp + 0x14#64) ↦₃₂ sv.v14) ∗
            ((s2.sp + 0x18#64) ↦₆₄ sv.v18) ∗
            ((s2.sp + 0x24#64) ↦₃₂ sv.v24) ∗
            ((s2.sp + 0x28#64) ↦₃₂ sv.v28) ∗
            ((s2.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
            ((s2.sp + 0x30#64) ↦₆₄ sv.v30) ∗
            ((s2.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
            memRegion (s2.sp + 0x5f0#64) 104 ∗
            stackAt s2.sp chainCloneStack ∗
            (vecGhostAt A.repAlloc x.G.localIk (s2.sp + 0x138#64) ∗
              vecGhostAt A.repAlloc x.G.remoteIk (s2.sp + 0x150#64) ∗
              vecU8At A.repAlloc (s2.sp + 0x168#64) x.G.root.cap x.G.root.ptr
                (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A.repAlloc (s2.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              optSenderChainHeap A.repAlloc sender' x.st.senderChain ∗
              chunks96_6QAt (s2.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((s2.sp + 0x40#64) ↦₆₄ scCap') ∗
              ((s2.sp + 0x48#64) ↦₆₄ rootPtr') ∗
              ((s2.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
              ((s2.sp + 0x58#64) ↦₆₄ 32#64) ∗
              ((s2.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
              ((s2.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
              ((s2.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗
              ((s2.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
              ((s2.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s2.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s2.sp + 0x10#64) 4 ∗
              memRegion (s2.sp + 0x20#64) 4 ∗
              memRegion (s2.sp + 0x38#64) 4 ∗
              memRegion (s2.sp + 0x50#64) 4 ∗
              dstSlotsAt s2.sp dv ∗
              ((s2.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
              segClone_fixedRestPlaced A ctl x s2.sp))
    (by
      rw [segClone_vecAt_0x180_chains_eq A.repAlloc s2.sp x.G.chainsCap x.G.chainsPtr
            x.G.chains x.st.receiverChains h_chains_len]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine segClone_fields_5_to_9_placed hA hchainClone hQp_false hfit_59
    hpc2 hrun2 hspA2 hx24_2' hx25_2 hx26_2 htr2 h_chains_len
    fun s3 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr'
      hpc3 hrun3 hsp3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3
      hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 htr3
      hchains_l hchains_c halice_b halice_c hpq_c => ?_
  have hst_all :
      M.stepEvents (fields5To9Events x.G x.st) (M.stepEvents (fields1To4Events x.G x.st) st) =
      M.stepEvents (segCloneEvents x.G x.st) st := by
    rw [← M.stepEvents_append, ← segCloneEvents_eq_split]
  rw [hst_all]
  let st' := M.stepEvents (segCloneEvents x.G x.st) st
  rw [← hsp3] at hx24_3 ⊢
  refine SepWPpCl.weaken_pre
    (P' := dstSlotsAt s3.sp dv ∗
            chunks96_6QAt (s3.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            spillSlotsAt s3.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap'
              x.st.sessionVersion scCap' rootPtr' x.st.previousCounter 32#64
              remoteIk'.ptr remoteIk'.cap localIk'.ptr localIk'.cap ∗
            ((s3.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            (A.pool lim st' s3 ∗
              vecGhostAt A.repAlloc x.G.localIk (s3.sp + 0x138#64) ∗
              vecGhostAt A.repAlloc x.G.remoteIk (s3.sp + 0x150#64) ∗
              vecU8At A.repAlloc (s3.sp + 0x168#64) x.G.root.cap x.G.root.ptr
                (keyToBytes32 x.st.rootKey) ∗
              vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A.repAlloc x.G.alice (s3.sp + 0x198#64) ∗
              vecU8At A.repAlloc (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optSenderChainAt A.repAlloc (s3.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              optTailVecAt A.repAlloc 48 (s3.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A.repAlloc 32 (s3.sp + 0x260#64) x.G.kyber ∗
              ((s3.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s3.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              ((s3.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗
              vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
                (chains'.zip x.st.receiverChains) ∗
              vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
              vecU8Buf A.repAlloc pqCap' pqPtr' x.st.pqRatchetState ∗
              optSenderChainHeap A.repAlloc sender' x.st.senderChain ∗
              OptPendClone A.repAlloc x.G.pending pendCap' pendPtr' ∗
              OptKybClone A.repAlloc x.G.kyber kybCap' kybPtr' ∗
              memRegion (s3.sp + 0x5f0#64) 104 ∗
              stackAt s3.sp chainCloneStack ∗
              segClone_fixedRestPlaced A ctl x s3.sp))
    (by unfold spillSlotsAt; exact Entails.of_eq (by sep_ac_rfl)) ?_
  apply SepWPpCl.of_sepWPp
  refine segClone_fields_10_to_11_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08' v14' pendCap' pendPtr'
    v24' v28' v2c' w288 w28c _
    hpc3 hrun3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3
    fun s4 hvm4 hpc4 hrun4 hsp4 hspA4 hx9_4 hx29_4 htr4 => ?_
  have hsp_eq : s3.sp = s0.sp := by reg_chain
  have hpool4 := A.pool_transport lim st' s3 s4 hvm4
  rw [hsp_eq, ← hpool4]
  refine SepWPp.done hpc4 hrun4
    ⟨by reg_chain, hspA4, by reg_chain, htr4, hx9_4, ?_⟩
  have hdst :=
    segClone_dstSlotsWrittenAt_entails_sessionStateAt A.repAlloc s0.sp x localIk' remoteIk' rootPtr'
      chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap'
      sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24'
      kybCap' kybPtr' v14' w288 w28c
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
      hloc_b hloc_c hrem_b hrem_c hchains_l hchains_c halice_b halice_c hpq_c hinl
  have hsrc :=
    segClone_srcSessionState_reassemble A.repAlloc s0.sp x w288 w28c
      h_loc_deser h_rem_deser h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
  have hrest :=
    segClone_fixedRest_reassemble_placed A lim st' s4 ctl x s0.sp sq0 sq1 sq2 sq3 sq4 sq5
      kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
      scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
      localIk'.ptr localIk'.cap
  rw [stackAt_chainClone_eq_alloc s0.sp]
  refine Entails.trans
    (Q := (segClone_dstSlotsWrittenAt s0.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
              pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24'
              kybCap' kybPtr' v14' x.st.sessionVersion x.st.previousCounter w288 w28c ∗
            vecU8Buf A.repAlloc localIk'.cap localIk'.ptr localIk'.bytes ∗
            vecU8Buf A.repAlloc remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A.repAlloc 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap' chainsPtr'
              (chains'.zip x.st.receiverChains) ∗
            vecU8Buf A.repAlloc alice'.cap alice'.ptr alice'.bytes ∗
            vecU8Buf A.repAlloc pqCap' pqPtr' x.st.pqRatchetState ∗
            optSenderChainHeap A.repAlloc sender' x.st.senderChain ∗
            OptPendClone A.repAlloc x.G.pending pendCap' pendPtr' ∗
            OptKybClone A.repAlloc x.G.kyber kybCap' kybPtr') ∗
          (vecGhostAt A.repAlloc x.G.localIk (s0.sp + 0x138#64) ∗
            vecGhostAt A.repAlloc x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A.repAlloc (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr
              (keyToBytes32 x.st.rootKey) ∗
            vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A.repAlloc x.G.alice (s0.sp + 0x198#64) ∗
            vecU8At A.repAlloc (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A.repAlloc (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A.repAlloc 48 (s0.sp + 0x230#64) x.G.pending ∗
            optTailVecAt A.repAlloc 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s0.sp + 0x28c#64) ↦₃₂ w28c)) ∗
          (spillSlotsAt s0.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap'
              x.st.sessionVersion scCap' rootPtr' x.st.previousCounter 32#64
              remoteIk'.ptr remoteIk'.cap localIk'.ptr localIk'.cap ∗
            chunks96_6QAt (s0.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            memRegion (s0.sp + 0x5f0#64) 104 ∗
            ((s0.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            memRegion (s0.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
            stackAt s0.sp allocHookStack ∗ A.pool lim st' s4 ∗
            segClone_fixedRestPlaced A ctl x s0.sp))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hdst (sepConj_mono hsrc hrest)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G₁
  refine Entails.sepExists_right G₁ ?_
  change _ ⊢ _ ∗
    recFramePlaced (A.atState lim st' s4) x s0.sp ∗
    sessionStateAt (A.atState lim st' s4) (s0.sp + 0x138#64) x.G x.st ∗
    sessionStateAt (A.atState lim st' s4) (s0.sp + 0xca0#64) G₁ x.st ∗ _
  rw [sessionStateAt_atState A lim st' s4 (s0.sp + 0x138#64) x.G x.st,
      sessionStateAt_atState A lim st' s4 (s0.sp + 0xca0#64) G₁ x.st]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Segment Theorem and Region Assembly -/

theorem segClone_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)}
    (htd_ne : TdEnvInhabited tdEnv) :
    SegClonePlacedSpec C A lim ctl parse S tdEnv H := by
  intro hshim halloc _hdealloc hmemcpy _hpanic hchainClone hsenderClone _hdrop1
    x st_init R s0 hpc hrun hpre hL
  have hA : SegCloneHooks A lim H := ⟨hshim, halloc, hmemcpy⟩
  dsimp only [recEntryPlaced] at hpc
  dsimp only [recordDecryptPlacedSpec,
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfit_full, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfl, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hsp, h27, h19, h23, h24, hrem_ne, hseeds, hrc32, _⟩, hm⟩ := hpre
  rw [sessionStateAt_atState, protocolAddressAt_atState, protocolAddressAt_atState,
      signalMessageAt_atState, RustCliAllocBudget.atState_pool] at hm
  simp only [← sepConj_assoc] at hm
  have hfits_clone : FitsEvents M lim st_init (segCloneEvents x.G x.st) :=
    fitsEvents_segClone_of_recordDecryptEnv htd_ne hfit_full
  have hwp :=
    segClone_wp_placed (ctl := ctl) hA hchainClone hsenderClone x s0 hfits_clone
      hpc hrun hsp h27 h19 h23 h24 hrc32
  have hm_assoc : s0.mem ⊨
      (memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A.repAlloc (s0.sp + 0x138#64) x.G x.st ∗
        memRegion (s0.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
        cliTapeAt ctl x.cur x.rest ∗ lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool lim st_init s0) ∗ R :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  obtain ⟨sf, hsteps, hout⟩ := hwp hfl.1 R hm_assoc hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hspf, hspAf, hx29f, ⟨htrf, hvrf⟩, hx9f, hent⟩ |
      ⟨_, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · have hmeta : recMetaPlaced s0 sf :=
      ⟨hrunf, hspf, hspAf, hx29f, htrf,
       LibsignalCodeRoLoaded.of_keepsFrozen hfl hsteps.keepsFrozen, hvrf⟩
    have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf'
    obtain ⟨G₁, hmf'⟩ := hmf'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf'
    obtain ⟨hclone, hmf'⟩ := hmf'
    let st' := M.stepEvents (segCloneEvents x.G x.st) st_init
    by_cases hver : x.st.version.toNat = x.msg.messageVersion.toNat
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcV : sf.pc = recVPCPlaced := by simpa [recVPCPlaced] using hpcf
      have hseqV : ∀ e1 e2, SegCloneEnv x.G x.st e1 → FromVEnv tdEnv x G₁ e2 →
          RecordDecryptEnv tdEnv x (e1 ++ e2) := by
        intro e1 e2 he1 he2
        unfold RecordDecryptEnv
        simp only [hver, ↓reduceIte]
        exact ⟨G₁, hclone, SeqEnv.append he1 he2⟩
      have hsbV : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st' (FromVEnv tdEnv x G₁) :=
        (SeamBudget.init hfit_full).step hseqV rfl
      refine ⟨sf, hsteps, Or.inl ⟨G₁, st', hsbV, hpcV, hmeta, ⟨hrem_ne, hseeds, hrc32⟩,
        hclone, hver, ?_⟩⟩
      simpa only [sepConj_assoc] using hmf'
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcM : sf.pc = recMPCPlaced := by simpa [recMPCPlaced] using hpcf
      have hseqM : ∀ e1 e2, SegCloneEnv x.G x.st e1 → FromMEnv e2 →
          RecordDecryptEnv tdEnv x (e1 ++ e2) := by
        intro e1 e2 he1 he2
        unfold RecordDecryptEnv
        simp only [hver, ↓reduceIte]
        exact SeqEnv.append he1 he2
      have hsbM : SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st' FromMEnv :=
        (SeamBudget.init hfit_full).step hseqM rfl
      refine ⟨sf, hsteps, Or.inr (Or.inl ⟨G₁, st', hsbM, hpcM, hmeta, hver, hx9f, ?_⟩)⟩
      simpa only [sepConj_assoc] using hmf'
  · have hfalse := Satisfies.mono (sepConj_mono_left hqp) hmf
    rw [satisfies_pure_sepConj] at hfalse
    exact False.elim hfalse.1
  · exact (not_satisfies_false_sepConj hoom).elim

alias segClone_placed_ok_of_inhabited := segClone_placed_ok

/-- Complete budget-threaded `[LibsignalPlacement]` `region_ok` proof for the CLI record-loop body
    on Block `463`, composing all 5 budget segment proofs (`segClone_placed_ok`,
    `segDecrypt_placed_ok`, `segMismatch_placed_ok`, `segTail_placed_ok`, `segExit_placed_ok`)
    under `TdEnvInhabited tdEnv`. -/
theorem recordDecrypt_placed_region_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (htd_ne : TdEnvInhabited tdEnv)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hcc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (hsc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)))
    (hdrop1 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)))
    (htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv)))
    (hset : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)))
    (hdrop2 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hgrow : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec))) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv) :=
  recordDecrypt_placed_region_ok_of_seams C A lim ctl uuidTryParse S tdEnv H
    hshim halloc hdealloc hmemcpy hpanic hcc hsc hdrop1 htd hset hdrop2 hgrow hclosure
    (segClone_placed_ok htd_ne) segDecrypt_placed_ok segMismatch_placed_ok
    segTail_placed_ok segExit_placed_ok

alias recordDecrypt_placed_region_ok_of_inhabited := recordDecrypt_placed_region_ok

/-- Complete budget-threaded `[LibsignalFullPlacement]` `region_ok` proof for
`withLsFrozen lsmpl (recordDecryptPlacedSpec ...)` on Block `463` (`0` `hclosure` premise). -/
theorem recordDecrypt_full_placed_region_ok [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (htd_ne : TdEnvInhabited tdEnv)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hcc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (hsc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)))
    (hdrop1 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)))
    (htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv)))
    (hset : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)))
    (hdrop2 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hgrow : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim))) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv)) :=
  LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.recordDecrypt_full_placed_region_ok_of_seams
    C A lim ctl uuidTryParse S tdEnv H
    hshim halloc hdealloc hmemcpy hpanic hcc hsc hdrop1 htd hset hdrop2 hgrow
    (segClone_placed_ok htd_ne)
    LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecryptPlacedBudget.segDecrypt_full_placed_ok
    LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget.segMismatch_full_placed_ok
    segTail_placed_ok segExit_placed_ok

alias recordDecrypt_full_placed_region_ok_of_inhabited := recordDecrypt_full_placed_region_ok

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlacedBudget
