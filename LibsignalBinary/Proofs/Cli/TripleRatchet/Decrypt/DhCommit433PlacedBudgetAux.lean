/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep5
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Pinned-Capacity Budget-Threaded DH Commit Composition

Tracks exact post-commit ghost buffer capacities (`trGhostCaps trG' = s3AfterCaps ...`) across the
`receiver_chains` push, optional `grow_one`, and oldest-chain eviction loop (`+0x8ac → +0x3e4`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudgetAux

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open scoped CryptoVerification.RustHeap
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (ChainKey KeyPair PublicKey RatchetState ReceiverChain RootKey SenderChain SessionState TripleRatchet macLength)
open CryptoVerification (LibsignalPlacement lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsmpl)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecAt vecBuf vecU8At)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt chainKeyBytes msgTypeByte optSenderChainBytes ratchetAt)
open CryptoVerification.LibsignalTripleRatchetRepr (boxU8At optBoxU8At protocolAddressAt sessionStateAt signalMessageAt)
open CryptoVerification.LibsignalTripleRatchet (TrGhost TryDecryptGhost trAt)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (
  add_assoc_const cell_to_memRegion_8 cells_4_to_memRegion_32 chainAt_newChain_of_cells
  chainHeaps chainKeyBytes_pointsTo elim_memRegion_104 evictList newChainGhost
  newReceiverChain optChainKeyHeap optChainKeyTailBytes optChainKeyTailBytes_length
  optSenderChainBytes_some_pointsTo pack64 pointsToBytes_32_eq_pointsTo64
  publicKey_serialize_length setWidth8_zeroExtend64_shared_lb stackAt_split_from
  vecBuf_chainAt_expose_bytes vecBuf_chainAt_of_bytes vecBuf_chainAt_push_reassemble
  vecBuf_expose_for_grow vecBuf_expose_for_push)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit.DhCommitFacts (
  evictGcs le_of_eq_succ_lt map_snd_evictGcs map_snd_zip_append
  sckWord0 sckWord16 sckWord20 sckWord28 sckWord8 vecAt_chains_eq zip_map_fst_snd)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (GrowOne104Env fitsEnv_growOne104_iff growOne104Events)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (chainKeyToPbSpecWithStack framelessMemcpyBudgetSpec noAllocShimBudgetSpec publicKeySerializeSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore (DhCommitBlockVmWp DhCommitEnv dhCommitAllocEvents fitsEvents_of_fitsEnv_dhCommitEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetStep4 (dhCommit_evict_one_of_wp dhCommit_step4_of_wp dropChainSpecWithStack evictActiveWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetStep5 (dhCommit_step5_of_wp)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget (dhCommitStep12Events dhCommitStep12Pre dhCommit_step1_2_withStack_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget (CommitStep3bVmWp DhCommitStep3BlockWp dhCommitStep3Events dhCommitStep3aEvents growOneSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (TrGhostCaps dhStepNewChainsCap s3AfterCaps trGhostCaps)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemmoveBudgetSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Post-Commit `TrGhostCaps` Equality Helpers -/

theorem map_fst_zip_eq_of_length_eq {α β : Type} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length → (xs.zip ys).map Prod.fst = xs
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zip_cons_cons, List.map_cons, map_fst_zip_eq_of_length_eq h]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem evictList_map {α β : Type} (f : α → β) (xs : List α) :
    (evictList xs).map f = evictList (xs.map f) := by
  simp only [evictList, List.map_drop, List.length_map]

theorem trGhostCaps_after_commit (trG : TrGhost) (rc : List ReceiverChain) (ptr' srkPtr ckPtr : BitVec 64)
    (srk : PublicKey) (newChain : ReceiverChain) (hchains_len : trG.ratchet.chains.length = rc.length) :
    let gcs1 := trG.ratchet.chains.zip rc ++ [(newChainGhost srkPtr ckPtr srk, newChain)]
    let cap' := dhStepNewChainsCap trG.ratchet.chainsCap rc.length
    let trG' : TrGhost := { trG with ratchet := { trG.ratchet with
      chainsCap := cap', chainsPtr := ptr', chains := (evictGcs gcs1).map Prod.fst } }
    trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) rc.length := by
  intro gcs1 cap' trG'; dsimp only [trG', gcs1]; unfold trGhostCaps s3AfterCaps evictGcs
  refine congrArg (fun m => TrGhostCaps.mk cap' m trG.pq.cap) ?_
  rw [evictList_map, evictList_map]; refine congrArg evictList ?_
  simp only [List.map_append, List.map_cons, List.map_nil, map_fst_zip_eq_of_length_eq hchains_len, newChainGhost]

/-! ## Pinned-Capacity Step 3 (`+0xa84 → +0xaf0`) -/

private theorem steps_of_sepWP {prog : Program} {s : State}
    {target : BitVec 64} {Pre Rest : SepProp}
    {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP)
    (hmem : s.mem ⊨ Pre ∗ Rest)
    (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out, s1.pc = target → s1.status = .Running → prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ Rest) →
      PostWP s1 P_out →
      ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, hoom⟩⟩ := hwp.elim hmem hL
  · obtain ⟨sf, hsteps2, hQ⟩ :=
      hcont s1 P_out hpc1 hrun1 (hL.of_keepsFrozen hsteps1.keepsFrozen) hm1 hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem steps_of_call_no_panic {α : Type} {prog : Program} {s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Rest : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : s.mem ⊨ spec.pre arg s ∗ Rest)
    (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl)
    (hcont : ∀ s1, s1.pc = ret_pc → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ Rest) →
      ∃ sf, Steps prog s1 sf ∧ Q sf) :
    ∃ sf, Steps prog s sf ∧ Q sf := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    hcall.no_fault_before_outcome arg Rest s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨_, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hsp_align1 : s1.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨sf, hsteps2, hQ⟩ :=
      hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 (hL.of_keepsFrozen hsteps1.keepsFrozen) hpost1
    exact ⟨sf, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1

/-- Pinned-capacity Step 3a (`+0xa84 → +0xa9c`), preserving the exact capacity formula
`dhStepNewChainsCap chainsCap gcs.length`. -/
theorem dhCommit_step3a_pinned_of_wp {prog : Program} {entry growEntry deallocEntry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry growEntry deallocEntry)
    {stk : Nat} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog growEntry (growOneSpecWithStack stk M A lim))
    (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨ (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Frame ∗ R)) :
    let st1 := M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0
    let chainsCap1 := dhStepNewChainsCap chainsCap gcs.length
    ∃ sf, Steps prog s sf ∧ ∃ chainsPtr1 : BitVec 64,
        gcs.length < chainsCap1.toNat ∧ sf.pc = entry + 0xa9c#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = BitVec.ofNat 64 gcs.length ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        prog.CodeLoaded sf.mem ∧ (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 gcs ∗
           A.pool lim st1 sf ∗ stackAt sp stk) ∗ (Frame ∗ R)) := by
  intro st1 chainsCap1
  have hexp0 : s.mem ⊨
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       A.pool lim st0 s ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl
  by_cases hgrow : BitVec.ofNat 64 gcs.length = chainsCap
  · have hst1_eq : st1 = M.stepEvents (growOne104Events chainsCap) st0 := by
      dsimp only [st1, dhCommitStep3aEvents]; simp only [hgrow, ↓reduceIte]
    have hfits_grow : FitsEnv M lim st0 (GrowOne104Env chainsCap) := by
      rw [fitsEnv_growOne104_iff]
      dsimp only [dhCommitStep3aEvents] at hfits3a
      simpa only [hgrow, ↓reduceIte] using hfits3a
    have hexp := Satisfies.mono
      (sepConj_mono_left (vecBuf_chainAt_expose_bytes A.repAlloc chainsCap chainsPtr gcs)) hexp0
    rw [sepExists_sepConj_left, satisfies_sepExists] at hexp
    rcases hexp with ⟨bs, hexp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hexp
    rcases hexp with ⟨⟨hbs, hlen_bs, _hle_cap, _hcap_lt, hptr⟩, hexp⟩
    have hlen_eq_cap : gcs.length = chainsCap.toNat := by
      rw [← hgrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [vecBuf_expose_for_grow A.repAlloc chainsCap chainsPtr gcs bs hlen_bs hlen_eq_cap] at hexp
    have h38_grow : ((sp + 0x38#64) ↦₆₄ chainsCap) = ((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) := by
      rw [hgrow]
    have hm_grow_wp : s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗ ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          (if chainsCap = 0 then emp else A.live chainsPtr bs.length 8 ∗ (chainsPtr ↦ₛ bs)) ∗
          chainHeaps A.repAlloc gcs ∗ A.pool lim st0 s ∗ stackAt sp stk ∗ Frame) ∗ R) := by
      rw [h38_grow] at hexp
      change _ at hexp
      refine Satisfies.mono (Entails.of_eq ?_) hexp; sep_ac_rfl
    refine steps_of_sepWP
      (hwp.step3a_grow sp (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align)
      hm_grow_wp hL ?_
    intro s1 P1 hpc1 hrun1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    rw [← A.pool_transport lim st0 s s1 hvm1] at hm1'
    have hmax_lt : max (2 * chainsCap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
    have hm_call : s1.mem ⊨
        (growOneSpecWithStack stk M A lim).pre ((sp + 0x38#64, chainsCap, chainsPtr, bs), st0) s1 ∗
        ((((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
          chainHeaps A.repAlloc gcs ∗ Frame) ∗ R) := by
      dsimp only [growOneSpecWithStack]
      rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, by omega, hptr, hmax_lt, hfits_grow⟩, ?_⟩
      have h38_8 := add_assoc_const sp 0x38#64 8#64 0x40#64
      rw [h38_8]
      rw [← h38_grow] at hm1'
      refine Satisfies.mono (Entails.of_eq ?_) hm1'; sep_ac_rfl
    refine steps_of_call_no_panic hGrow hpc1 hrun1 hsp_align1 hx30_1 hm_call hL1
      (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
    intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 hL2 hm2
    dsimp only [growOneSpecWithStack] at hm2
    rw [hsp1, sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨htr2, hm2⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
    rcases hm2 with ⟨p', hm2⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨hp', hm2⟩
    set cap1 := BitVec.ofNat 64 (max (2 * chainsCap.toNat) 4)
    have hcap1_pin : chainsCap1 = cap1 := by
      dsimp only [chainsCap1, dhStepNewChainsCap, cap1]
      simp only [hgrow, ↓reduceIte]
    have hcap1_toNat : cap1.toNat = max (2 * chainsCap.toNat) 4 := by
      dsimp only [cap1]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_cap1 : gcs.length < chainsCap1.toNat := by
      rw [hcap1_pin]; omega
    have hcap1_ne : cap1 ≠ 0 := by
      intro h0; rw [h0] at hcap1_toNat; change 0 = max (2 * chainsCap.toNat) 4 at hcap1_toNat; omega
    have h38_8 := add_assoc_const sp 0x38#64 8#64 0x40#64
    rw [h38_8, ← hst1_eq] at hm2
    have hlive_eq : A.live p' (max (2 * chainsCap.toNat) 4 * 104) 8 = A.repAlloc.live p' (cap1.toNat * 104) 8 := by
      rw [hcap1_toNat]; rfl
    have hmr_eq :
        memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * chainsCap.toNat) 4 - chainsCap.toNat) * 104) =
          memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) := by
      rw [hlen_bs, hcap1_toNat, ← hlen_eq_cap]
    have hpull2 : s2.mem ⊨
        (A.repAlloc.live p' (cap1.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
         memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) ∗
         chainHeaps A.repAlloc gcs) ∗ (((sp + 0x38#64) ↦₆₄ cap1) ∗ ((sp + 0x40#64) ↦₆₄ p') ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         A.pool lim st1 s2 ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
      rw [hlive_eq, hmr_eq] at hm2
      refine Satisfies.mono (Entails.of_eq ?_) hm2; sep_ac_rfl
    have hreasm := vecBuf_chainAt_of_bytes A.repAlloc cap1 p' hcap1_ne hbs (by omega) (by omega) hp'
    have hm2_vec := Satisfies.mono (sepConj_mono_left hreasm) hpull2
    have hm2_final : s2.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ p') ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 p' gcs ∗
         A.pool lim st1 s2 ∗ stackAt sp stk) ∗ (Frame ∗ R) := by
      rw [hcap1_pin]
      refine Satisfies.mono (Entails.of_eq ?_) hm2_vec; sep_ac_rfl
    exact ⟨s2, .refl s2, p', hlt_cap1, hpc2, hrun2, by reg_chain, hsp_align2,
      htr2.trans (htr1.trans htrace), by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, hL2, hm2_final⟩
  · have hcap1_pin : chainsCap1 = chainsCap := by
      dsimp only [chainsCap1, dhStepNewChainsCap]
      simp only [hgrow, ↓reduceIte]
    have hst1_eq : st1 = st0 := by
      dsimp only [st1, dhCommitStep3aEvents]; simp only [hgrow, ↓reduceIte]; exact M.stepEvents_nil st0
    have hle_cap : gcs.length ≤ chainsCap.toNat := by
      unfold vecBuf at hexp0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hexp0
      exact hexp0.1.1
    have hlt_cap : gcs.length < chainsCap1.toNat := by
      rw [hcap1_pin]
      rcases Nat.lt_or_eq_of_le hle_cap with hlt | heq
      · exact hlt
      · exfalso; apply hgrow; rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hm_nogrow : s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
          A.pool lim st0 s ∗ stackAt sp stk ∗ Frame) ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl
    refine steps_of_sepWP
      (hwp.step3a_nogrow sp chainsCap (BitVec.ofNat 64 gcs.length) s hpc hrun hsp hsp_align hgrow)
      hm_nogrow hL ?_
    intro s1 P1 hpc1 hrun1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hvm1, hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    rw [← A.pool_transport lim st0 s s1 hvm1, ← hst1_eq] at hm1'
    have hm1_final : s1.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr gcs ∗
         A.pool lim st1 s1 ∗ stackAt sp stk) ∗ (Frame ∗ R) := by
      rw [hcap1_pin]
      refine Satisfies.mono (Entails.of_eq ?_) hm1'; sep_ac_rfl
    exact ⟨s1, .refl s1, chainsPtr, hlt_cap, hpc1, hrun1, hsp1, hsp_align1,
      htr1.trans htrace, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hL1, hm1_final⟩

/-- Pinned-capacity Step 3b (`+0xa9c → +0xaf0`), preserving `chainsCap1` and `chainsPtr1`
directly without existential binder shadowing. -/
theorem dhCommit_step3b_pinned_of_wp [LibsignalPlacement] {prog : Program} {entry deallocEntry : BitVec 64}
    (hwp3b : CommitStep3bVmWp prog entry deallocEntry)
    {stk : Nat} (hstk_lo : allocHookStack ≤ stk) (hstk_hi : stk < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st1 : M.σ)
    (hDealloc : subroutine_ok prog deallocEntry (rustCliDeallocBudgetSpec M A lim))
    (R Frame : SepProp) (s0 s s1 : State) (sp chainsCap1 chainsPtr1 boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlt_cap1 : gcs.length < chainsCap1.toNat) (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0)
    (hpc1 : s1.pc = entry + 0xa9c#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = sp) (hsp_align1 : s1.spAligned = true) (htr1 : s1.trace = s0.trace)
    (hx19_1 : s1.readReg64 .x19 = s.readReg64 .x19) (hx20_1 : s1.readReg64 .x20 = s.readReg64 .x20)
    (hx21_1 : s1.readReg64 .x21 = s.readReg64 .x21) (hx22_1 : s1.readReg64 .x22 = s.readReg64 .x22)
    (hx23_1 : s1.readReg64 .x23 = s.readReg64 .x23) (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 gcs.length)
    (hx25_1 : s1.readReg64 .x25 = s.readReg64 .x25) (hx26_1 : s1.readReg64 .x26 = s.readReg64 .x26)
    (hx27_1 : s1.readReg64 .x27 = s.readReg64 .x27) (hx28_1 : s1.readReg64 .x28 = s.readReg64 .x28)
    (hx29_1 : s1.readReg64 .x29 = s.readReg64 .x29) (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64) (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr) (hx28 : s.readReg64 .x28 = srkPtr) (hL1 : prog.CodeLoaded s1.mem)
    (hm1 : s1.mem ⊨ (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 gcs ∗
       A.pool lim st1 s1 ∗ stackAt sp stk) ∗
      ((((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
        memRegion (sp + 0x1b0#64) 72 ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗ Frame) ∗ R))
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    let st2 := M.stepEvents (rustDeallocEvents 33 1) st1
    ∃ sf, Steps prog s1 sf ∧ sf.pc = entry + 0xaf0#64 ∧ sf.status = .Running ∧
      sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
      sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
      sf.readReg64 .x23 = s.readReg64 .x23 ∧
      sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
      calleeSavedVRegs sf = calleeSavedVRegs s ∧ prog.CodeLoaded sf.mem ∧ (sf.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
         vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
         memRegion (sp + 0x190#64) 104 ∗ A.pool lim st2 sf ∗ stackAt sp stk) ∗ (Frame ∗ R)) := by
  intro newGC st2
  have hm1_push : s1.mem ⊨
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 gcs ∗
      (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st1 s1 ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1; sep_ac_rfl
  have hm1_exp := Satisfies.mono
    (sepConj_mono_left (vecBuf_expose_for_push A.repAlloc chainsCap1 chainsPtr1 gcs hlt_cap1)) hm1_push
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_exp
  rcases hm1_exp with ⟨⟨hcap1_lt, hptr1_ne⟩, hm1_exp⟩
  set rcLen := BitVec.ofNat 64 gcs.length
  set slot := chainsPtr1 + rcLen * 104#64
  have hm1_slot : s1.mem ⊨
      memRegion slot 104 ∗ (A.repAlloc.live chainsPtr1 (chainsCap1.toNat * 104) 8 ∗
       arrayAt (chainAt A.repAlloc) 104 chainsPtr1 gcs ∗
       memRegion (chainsPtr1 + BitVec.ofNat 64 ((gcs.length + 1) * 104))
         ((chainsCap1.toNat - (gcs.length + 1)) * 104) ∗
       ((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ rcLen) ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st1 s1 ∗ stackAt sp stk ∗ (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1_exp; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, hm1_w⟩ :=
    elim_memRegion_104 hm1_slot
  set tail := optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad
  have htail_len : tail.length = 32 := optChainKeyTailBytes_length ⟨32#64, ckPtr⟩ (some rck) hpad
  have h190_cells : ((sp + 0x190#64) ↦ₛ tail) =
      ((sp + 0x190#64) ↦₆₄ pack64 (tail.take 8)) ∗
      ((sp + 0x198#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
      ((sp + 0x1a0#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗
      ((sp + 0x1a8#64) ↦₆₄ pack64 (tail.drop 24)) := by
    rw [pointsToBytes_32_eq_pointsTo64 (sp + 0x190#64) htail_len,
      add_assoc_const sp 0x190#64 8#64 0x198#64,
      add_assoc_const sp 0x190#64 16#64 0x1a0#64,
      add_assoc_const sp 0x190#64 24#64 0x1a8#64]
  set ck0 := pack64 (tail.take 8)
  set ck1 := pack64 ((tail.drop 8).take 8)
  set ck2 := pack64 ((tail.drop 16).take 8)
  set ck3 := pack64 (tail.drop 24)
  have hm_step3b : s1.mem ⊨
      (((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗ ((sp + 0x48#64) ↦₆₄ rcLen) ∗
       ((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
       ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
       ((chainsPtr1 + rcLen * 104#64) ↦₆₄ w0) ∗ ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ w1) ∗
       ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ w2) ∗ ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ w3) ∗
       ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ w4) ∗ ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ w5) ∗
       ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ w6) ∗ ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ w7) ∗
       ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ w8) ∗ ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ w9) ∗
       ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ w10) ∗ ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ w11) ∗
       ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ w12)) ∗
      ((A.repAlloc.live chainsPtr1 (chainsCap1.toNat * 104) 8 ∗
        arrayAt (chainAt A.repAlloc) 104 chainsPtr1 gcs ∗
        memRegion (chainsPtr1 + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((chainsCap1.toNat - (gcs.length + 1)) * 104) ∗
        ((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ memRegion (sp + 0x1b0#64) 72 ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
        A.pool lim st1 s1 ∗ stackAt sp stk ∗ Frame) ∗ R) := by
    rw [h190_cells] at hm1_w
    dsimp only [slot] at hm1_w
    refine Satisfies.mono (Entails.of_eq ?_) hm1_w; sep_ac_rfl
  refine steps_of_sepWP
    (hwp3b sp chainsPtr1 rcLen boxPtr srkPtr ck0 ck1 ck2 ck3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12
      s1 hpc1 hrun1 hsp1 hsp_align1 hx24_1
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain))
    hm_step3b hL1 ?_
  intro s2 P2 hpc2 hrun2 hL2 hm2 hpost2
  rcases hpost2 with ⟨hvm2, hsp2, hsp_align2, htr2, hx0_2, hx1_2, hx2_2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _hx24_2, hx25_2, _hx26_2, _hx27_2, _hx28_2,
    hx29_2, hx30_2, hvregs_2, hP2⟩
  have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
  rw [← A.pool_transport lim st1 s1 s2 hvm2] at hm2'
  have h190_reg :
      (((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
       ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3)) ∗
      memRegion (sp + 0x1b0#64) 72 ⊢ memRegion (sp + 0x190#64) 104 := by
    have hsplit104 := memRegion_split (sp + 0x190#64) 32 72 (by decide)
    rw [show (32 + 72 : Nat) = 104 from rfl] at hsplit104
    rw [hsplit104, add_assoc_const sp 0x190#64 (BitVec.ofNat 64 32) 0x1b0#64]
    have h32 := cells_4_to_memRegion_32 (sp + 0x190#64) ck0 ck1 ck2 ck3
    rw [add_assoc_const sp 0x190#64 8#64 0x198#64,
      add_assoc_const sp 0x190#64 16#64 0x1a0#64,
      add_assoc_const sp 0x190#64 24#64 0x1a8#64] at h32
    exact sepConj_mono_left h32
  have hslot_eq : chainsPtr1 + BitVec.ofNat 64 (gcs.length * 104) = slot := by
    dsimp only [slot, rcLen]; rw [BitVec.ofNat_mul]
  have hnew_chain :
      (((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
        ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
        ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
        ((slot + 72#64) ↦₆₄ ck0) ∗ ((slot + 80#64) ↦₆₄ ck1) ∗ ((slot + 88#64) ↦₆₄ ck2) ∗
        ((slot + 96#64) ↦₆₄ ck3) ∗ (A.repAlloc.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck))) ⊢
      chainAt A.repAlloc newGC (chainsPtr1 + BitVec.ofNat 64 (gcs.length * 104)) := by
    rw [hslot_eq]
    exact chainAt_newChain_of_cells A.repAlloc slot srkPtr ckPtr srk rck hpad hsrk_ne
  have hpush_vec := vecBuf_chainAt_push_reassemble A.repAlloc chainsCap1 chainsPtr1 gcs newGC
    hlt_cap1 hcap1_lt hptr1_ne
  have hlen_append : rcLen + 1#64 = BitVec.ofNat 64 (gcs ++ [newGC]).length := by
    dsimp only [rcLen]; rw [List.length_append, List.length_singleton, BitVec.ofNat_add]
  have hser_len : srk.serialize.length = 33 := publicKey_serialize_length srk
  have hm2_grouped : s2.mem ⊨
      (A.repAlloc.live chainsPtr1 (chainsCap1.toNat * 104) 8 ∗
       arrayAt (chainAt A.repAlloc) 104 chainsPtr1 gcs ∗
       (((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
         ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
         ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
         ((slot + 72#64) ↦₆₄ ck0) ∗ ((slot + 80#64) ↦₆₄ ck1) ∗ ((slot + 88#64) ↦₆₄ ck2) ∗
         ((slot + 96#64) ↦₆₄ ck3) ∗ (A.repAlloc.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
         optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck))) ∗
       memRegion (chainsPtr1 + BitVec.ofNat 64 ((gcs.length + 1) * 104))
         ((chainsCap1.toNat - (gcs.length + 1)) * 104)) ∗
      ((((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
        ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3)) ∗ memRegion (sp + 0x1b0#64) 72) ∗
      ((boxPtr ↦ₛ srk.serialize) ∗ (A.live boxPtr 33 1 ∗ A.pool lim st1 s2 ∗
        ((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
        stackAt sp stk ∗ Frame ∗ R)) := by
    rw [← hlen_append]
    dsimp only [slot]
    refine Satisfies.mono (Entails.of_eq ?_) hm2'; sep_ac_rfl
  have hm2_chain := Satisfies.mono
    (sepConj_mono
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hnew_chain)))
        hpush_vec)
      (sepConj_mono_left h190_reg))
    hm2_grouped
  have hbox_reg : (boxPtr ↦ₛ srk.serialize) ⊢ memRegion boxPtr 33 := by
    have h := pointsToBytes_entails_memRegion boxPtr srk.serialize
    rwa [hser_len] at h
  have hm2_box := Satisfies.mono
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hbox_reg)))
    hm2_chain
  have hstk_dealloc := stackAt_split_from sp stk allocHookStack hstk_lo hstk_hi
  have hm_dealloc : s2.mem ⊨
      (rustCliDeallocBudgetSpec M A lim).pre (boxPtr, 33, 1, st1) s2 ∗
      ((((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
        vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
        memRegion (sp + 0x190#64) 104 ∗ memRegion (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗
        Frame) ∗ R) := by
    dsimp only [rustCliDeallocBudgetSpec]
    rw [hstk_dealloc] at hm2_box
    rw [hsp2, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_2, by rw [hx1_2]; rfl, by rw [hx2_2]; rfl, hx30_2.symm ▸ hlr_dealloc⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm2_box; sep_ac_rfl
  refine steps_of_call_no_panic hDealloc
    hpc2 hrun2 hsp_align2 hx30_2 hm_dealloc hL2
    (by intro _; rfl) (by intros; rfl) (by intro _; rfl) ?_
  intro s3 hpc3 hrun3 hsp3 hsp_align3 hcs3 hL3 hm3
  dsimp only [rustCliDeallocBudgetSpec] at hm3
  rw [hsp2, sepConj_assoc, satisfies_pure_sepConj] at hm3
  rcases hm3 with ⟨⟨hacp3, _hlive3⟩, hm3⟩
  have htr3 : s3.trace = s2.trace := hacp3.2.1
  have hm3_final : s3.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
       memRegion (sp + 0x190#64) 104 ∗ A.pool lim st2 s3 ∗ stackAt sp stk) ∗ (Frame ∗ R) := by
    rw [hstk_dealloc]
    refine Satisfies.mono (Entails.of_eq ?_) hm3; sep_ac_rfl
  exact ⟨s3, .refl s3, hpc3, hrun3, by reg_chain, hsp_align3,
    htr3.trans (htr2.trans htr1), by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, hL3, hm3_final⟩

theorem dhCommit_step3_pinned_of_wp [LibsignalPlacement] {prog : Program} {entry growEntry deallocEntry : BitVec 64}
    (hwp : DhCommitStep3BlockWp prog entry growEntry deallocEntry)
    {stk : Nat} (hstk_lo : allocHookStack ≤ stk) (hstk_hi : stk < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ)
    (hGrow : subroutine_ok prog growEntry (growOneSpecWithStack stk M A lim))
    (hDealloc : subroutine_ok prog deallocEntry (rustCliDeallocBudgetSpec M A lim))
    (R Frame : SepProp) (s0 s : State) (sp chainsCap chainsPtr boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlen_lt : gcs.length < 2 ^ 32) (hpad : pad.length = 4) (hsrk_ne : srkPtr ≠ 0)
    (hfits3a : FitsEvents M lim st0 (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)))
    (hpc : s.pc = entry + 0xa84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_align : s.spAligned = true) (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64) (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr) (hx28 : s.readReg64 .x28 = srkPtr) (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨ (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Frame ∗ R))
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    let st2 := M.stepEvents (dhCommitStep3Events chainsCap (BitVec.ofNat 64 gcs.length)) st0
    let chainsCap1 := dhStepNewChainsCap chainsCap gcs.length
    ∃ sf, Steps prog s sf ∧ ∃ chainsPtr1 : BitVec 64,
        sf.pc = entry + 0xaf0#64 ∧ sf.status = .Running ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧ prog.CodeLoaded sf.mem ∧ (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
           vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
           memRegion (sp + 0x190#64) 104 ∗ A.pool lim st2 sf ∗ stackAt sp stk) ∗ (Frame ∗ R)) := by
  intro newGC st2 chainsCap1
  set Step3Rest : SepProp :=
    ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
    memRegion (sp + 0x1b0#64) 72 ∗ (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
    (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
    optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some rck) ∗ Frame
  have hm3a : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) chainsCap chainsPtr gcs ∗
       A.pool lim st0 s ∗ stackAt sp stk) ∗ (Step3Rest ∗ R) := by
    dsimp only [Step3Rest]
    refine Satisfies.mono (Entails.of_eq ?_) hmem; sep_ac_rfl
  obtain ⟨s1, hsteps3a, chainsPtr1, hlt_cap1, hpc1, hrun1, hsp1, hsp_align1, htr1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1,
      hvregs_1, hL1, hm1⟩ :=
    dhCommit_step3a_pinned_of_wp hwp A lim st0 hGrow R Step3Rest s0 s sp chainsCap chainsPtr gcs
      hlen_lt hfits3a hpc hrun hsp hsp_align htrace hL hm3a
  obtain ⟨sf, hsteps3b, hpost⟩ :=
    dhCommit_step3b_pinned_of_wp (hlr_dealloc := hlr_dealloc) hwp.step3b hstk_lo hstk_hi A lim
      (M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0)
      hDealloc R Frame s0 s s1 sp chainsCap1 chainsPtr1 boxPtr srkPtr ckPtr gcs srk rck pad
      hlt_cap1 hpad hsrk_ne hpc1 hrun1 hsp1 hsp_align1 htr1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
      hx25 hx26 hx27 hx28 hL1 hm1
  have hst2_eq :
      M.stepEvents (rustDeallocEvents 33 1)
        (M.stepEvents (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length)) st0) = st2 := by
    dsimp only [st2, dhCommitStep3Events]
    exact (M.stepEvents_append (dhCommitStep3aEvents chainsCap (BitVec.ofNat 64 gcs.length))
      (rustDeallocEvents 33 1) st0).symm
  rw [hst2_eq] at hpost
  exact ⟨sf, hsteps3a.trans hsteps3b, chainsPtr1, hpost⟩

/-! ## Pinned-Capacity `dhCommit` Composition -/

/-- Pinned-capacity total-correctness `Steps` composition for S3 Commit (`+0x8ac → +0x3e4`),
recording `trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length`. -/
theorem dhCommit_pinned_withStack_env_of_wp [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockVmWp prog entry dropChainEntry)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st0 : M.σ) (hookStack growStk dropStk : Nat)
    (hhook_lo : allocHookStack ≤ hookStack) (hhook_hi : hookStack + 48 < 2 ^ 64)
    (hpb_le : hookStack + 48 ≤ tryDecryptSubStack) (_hpb_align : (hookStack + 48) % 16 = 0)
    (hgrow_lo : allocHookStack ≤ growStk) (hgrow_hi : growStk < 2 ^ 64)
    (hgrow_le : growStk ≤ tryDecryptSubStack) (_hgrow_align : growStk % 16 = 0)
    (hdrop_le : dropStk ≤ tryDecryptSubStack) (_hdrop_align : dropStk % 16 = 0)
    (hPkSer : subroutine_ok prog (lsmpl.base 205) (publicKeySerializeSpecWithStack M A lim hookStack))
    (hToPb : subroutine_ok prog (lsmpl.base 22) (chainKeyToPbSpecWithStack M A lim hookStack))
    (hGrowOne : subroutine_ok prog (lsmpl.base 43) (growOneSpecWithStack growStk M A lim))
    (hDropChain : subroutine_ok prog dropChainEntry (dropChainSpecWithStack dropStk M A lim))
    (hShim : subroutine_ok prog (lsmpl.ρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (hAlloc : subroutine_ok prog (lsmpl.ρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false))
    (hDealloc : subroutine_ok prog (lsmpl.ρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : subroutine_ok prog (lsmpl.ρ "memcpy") framelessMemcpyBudgetSpec)
    (hMemmove : subroutine_ok prog (lsmpl.ρ "memmove") (sessionMemmoveBudgetSpec dropStk))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain) (receiverChainKey : ChainKey)
    (newSenderKey : KeyPair) (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (envHeap R : SepProp) (s0 s : State) (hsc : tr.ratchet.senderChain = some sc)
    (hrc_len : tr.ratchet.receiverChains.length < 2 ^ 32)
    (hclamp : clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes)
    (hfits : FitsEnv M lim st0 (DhCommitEnv trG.ratchet.chainsCap (BitVec.ofNat 64 tr.ratchet.receiverChains.length)))
    (hpc_s : s.pc = entry + 0x8ac#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1504#64)
    (hsp0_align : s0.spAligned = true) (hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64) (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA) (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64) (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 0x3d0#64) (msgW : BitVec 32)
    (hmsgW : msgW.setWidth 8 = msgTypeByte x.msgType)
    (hm : s.mem ⊨ sessionStateAt (A.atState lim st0 s) x.ss x.G.afterTrFrom st1 ∗
      trAt (A.atState lim st0 s) ((s0.sp - 1504#64) + 0x38#64) trG
        { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗ memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x10 ∗
      (((s0.sp - 1504#64) + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion ((s0.sp - 1504#64) + 0x14#64) 8 ∗ (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
      (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗ (((s0.sp - 1504#64) + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 0x2c#64) 4 ∗ (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x140#64) 0x50 ∗ (((s0.sp - 1504#64) + 0x190#64) ↦₃₂ 0#32) ∗
      (((s0.sp - 1504#64) + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      (((s0.sp - 1504#64) + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion ((s0.sp - 1504#64) + 0x1d8#64) 0xd8 ∗ memRegion ((s0.sp - 1504#64) + 0x2b0#64) 0x10 ∗
      memRegion ((s0.sp - 1504#64) + 0x2c0#64) 0x110 ∗
      (((s0.sp - 1504#64) + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion ((s0.sp - 1504#64) + 0x3f4#64) 12 ∗
      (((s0.sp - 1504#64) + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      (((s0.sp - 1504#64) + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 0x440#64) 0x80 ∗
      (((s0.sp - 1504#64) + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      (((s0.sp - 1504#64) + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      memRegion ((s0.sp - 1504#64) + 0x4e0#64) 0xa0 ∗
      (protocolAddressAt (A.atState lim st0 s) x.rem x.remA ∗
       protocolAddressAt (A.atState lim st0 s) x.loc x.locA ∗
       signalMessageAt (A.atState lim st0 s) x.msgG x.msgA x.msg ∗ envHeap ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗
       A.pool lim st0 s) ∗ R)
    (hL : prog.CodeLoaded s.mem)
    (hlr_alloc : LsRetAddr624 (entry + 0xa00#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_dealloc : LsRetAddr624 (entry + 0xaf0#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *])
    (hlr_ls : LsRetAddr624 (entry + 0xb8c#64) := by
      first
      | assumption
      | simp (config := { decide := true }) [wp_norm, arm64_norm, lsLen, *]) :
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey, chainKey := some receiverChainKey, messageKeys := [] }
    let r1 : RatchetState := { tr.ratchet with
      senderChain := some ⟨newSenderKey, senderChainKey⟩, rootKey := finalRootKey
      previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
      receiverChains := RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    let sp := s0.sp - 1504#64
    ∃ sf evs trG',
      Steps prog s sf ∧
      DhCommitEnv trG.ratchet.chainsCap (BitVec.ofNat 64 tr.ratchet.receiverChains.length) evs ∧
      trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
      sf.pc = entry + 0x3e4#64 ∧ (sf.status = .Running ∧ sf.sp = sp ∧ s0.spAligned = true ∧
       sf.spAligned = true ∧ sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.trace = s0.trace ∧
       calleeSavedVRegs sf = calleeSavedVRegs s0) ∧ sf.readReg64 .x12 = sp + 0x2c0#64 ∧
      sf.readReg64 .x19 = x.ret ∧ sf.readReg64 .x20 = sp + 0x140#64 ∧ sf.readReg64 .x21 = x.ss ∧
      sf.readReg64 .x22 = x.msgA ∧ sf.readReg64 .x23 = sp + 0x500#64 ∧
      (sf.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
      (sf.mem ⊨
        sessionStateAt (A.atState lim (M.stepEvents evs st0) sf) x.ss x.G.afterTrFrom st1 ∗
        trAt (A.atState lim (M.stepEvents evs st0) sf) (sp + 0x38#64) trG' { tr with ratchet := r1 } ∗
        memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
        ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
        ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x140#64) 0x170 ∗
        ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
        ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗
        memRegion (sp + 0x2d4#64) 0x2ac ∗
        (protocolAddressAt (A.atState lim (M.stepEvents evs st0) sf) x.rem x.remA ∗
         protocolAddressAt (A.atState lim (M.stepEvents evs st0) sf) x.loc x.locA ∗
         signalMessageAt (A.atState lim (M.stepEvents evs st0) sf) x.msgG x.msgA x.msg ∗ envHeap ∗
         stackAt sp tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗
         A.pool lim (M.stepEvents evs st0) sf) ∗ R) := by
  let newChain : ReceiverChain :=
    { senderRatchetKey := x.msg.senderRatchetKey, chainKey := some receiverChainKey, messageKeys := [] }
  let r1 : RatchetState := { tr.ratchet with
    senderChain := some ⟨newSenderKey, senderChainKey⟩, rootKey := finalRootKey
    previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
    receiverChains := RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
  let sp := s0.sp - 1504#64
  have ⟨hfits12, hfits3a_rc⟩ := fitsEvents_of_fitsEnv_dhCommitEnv hfits
  dsimp only [trAt, ratchetAt, signalMessageAt] at hm
  rw [hsc] at hm
  have h_sc_50_eq :
      ∀ (pad : List (BitVec 8)), pad.length = 100 →
        ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) pad) =
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗ ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
         ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
         ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗
         ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) := by
    intro pad _hpad
    rw [show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
        optSenderChainBytes_some_pointsTo (sp + 0x50#64) sc pad,
        show sp + 0x50#64 + 4#64 = sp + 0x54#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 36#64 = sp + 0x74#64 from add_assoc_const _ _ _ _,
        show sp + 0x50#64 + 68#64 = sp + 0x94#64 from add_assoc_const _ _ _ _,
        chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey,
        show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _]
  have hm_pures : s.mem ⊨
      ⌜∀ sc', some sc = some sc' →
        clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
        trG.ratchet.senderPad.length = 100 ∧ tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜macLength + 1 ≤ x.msg.serialized.length ∧ x.msg.serialized.length < 2 ^ 40 ∧
        x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
       vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr
         (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
       ((sp + 0x38#64 + 24#64) ↦ₛ optSenderChainBytes (some sc) trG.ratchet.senderPad) ∗
       ((sp + 0x38#64 + 128#64) ↦ₛ keyToBytes32 0) ∗
       ((sp + 0x38#64 + 160#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
       ((sp + 0x38#64 + 168#64) ↦₃₂ tr.ratchet.previousCounter) ∗
       memRegion (sp + 0x38#64 + 172#64) 4 ∗
       vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
       ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
       ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
       memRegion x.ret 48 ∗ memRegion sp 0x10 ∗
       ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
       memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₃₂ 0#32) ∗
       ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
       ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗ memRegion (sp + 0x1d8#64) 0xd8 ∗
       memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x110 ∗
       ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗ memRegion (sp + 0x3f4#64) 12 ∗
       ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
       ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x440#64) 0x80 ∗
       ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
       memRegion (sp + 0x4e0#64) 0xa0 ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗
       vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
       boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
       boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
       ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
       optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
       ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ memRegion (x.msgA + 0x71#64) 7 ∗ envHeap ∗
       stackAt sp tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗ A.pool lim st0 s ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [sp]
    rw [show sessionStateAt (A.atState lim st0 s) = sessionStateAt A.repAlloc from rfl,
        show protocolAddressAt (A.atState lim st0 s) = protocolAddressAt A.repAlloc from rfl,
        show vecAt (A.atState lim st0 s) 104 8 (chainAt (A.atState lim st0 s)) =
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) from rfl,
        show vecU8At (A.atState lim st0 s) = vecU8At A.repAlloc from rfl,
        show boxU8At (A.atState lim st0 s) = boxU8At A.repAlloc from rfl,
        show optBoxU8At (A.atState lim st0 s) = optBoxU8At A.repAlloc from rfl]
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hm_pures
  rcases hm_pures with ⟨_hclamp_old, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures
  rcases hm_pures with ⟨⟨hchains_len, hpad_len, hmfj⟩, hm_pures⟩
  rw [satisfies_pure_sepConj] at hm_pures
  rcases hm_pures with ⟨hmsg_pure, hm_body⟩
  rw [h_sc_50_eq trG.ratchet.senderPad hpad_len,
      show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 160#64 = sp + 0xd8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 172#64 = sp + 0xe4#64 from add_assoc_const _ _ _ _] at hm_body
  have hsplit_1d8 := memRegion_split (sp + 0x1d8#64) 0x60 0x78 (by decide)
  rw [show (0x60 + 0x78 : Nat) = 0xd8 from rfl,
      show sp + 0x1d8#64 + 96#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hsplit_1d8
  have hsplit_2c0 := memRegion_split (sp + 0x2c0#64) 0x14 0xfc (by decide)
  rw [show (0x14 + 0xfc : Nat) = 0x110 from rfl,
      show sp + 0x2c0#64 + 20#64 = sp + 0x2d4#64 from add_assoc_const _ _ _ _] at hsplit_2c0
  have hsplit_440 := memRegion_split (sp + 0x440#64) 0x10 0x70 (by decide)
  rw [show (0x10 + 0x70 : Nat) = 0x80 from rfl,
      show sp + 0x440#64 + 16#64 = sp + 0x450#64 from add_assoc_const _ _ _ _] at hsplit_440
  have hsplit_450 := memRegion_split (sp + 0x450#64) 0x50 0x20 (by decide)
  rw [show (0x50 + 0x20 : Nat) = 0x70 from rfl,
      show sp + 0x450#64 + 80#64 = sp + 0x4a0#64 from add_assoc_const _ _ _ _] at hsplit_450
  have hsplit_4e0 := memRegion_split (sp + 0x4e0#64) 0x20 0x80 (by decide)
  rw [show (0x20 + 0x80 : Nat) = 0xa0 from rfl,
      show sp + 0x4e0#64 + 32#64 = sp + 0x500#64 from add_assoc_const _ _ _ _] at hsplit_4e0
  have hsplit_500 := memRegion_split (sp + 0x500#64) 0x60 0x20 (by decide)
  rw [show (0x60 + 0x20 : Nat) = 0x80 from rfl,
      show sp + 0x500#64 + 96#64 = sp + 0x560#64 from add_assoc_const _ _ _ _] at hsplit_500
  have hstk_pb := stackAt_split_from sp tryDecryptSubStack (hookStack + 48) hpb_le (by decide)
  rw [hsplit_1d8, hsplit_2c0, hsplit_440, hsplit_450, hsplit_4e0, hsplit_500, hstk_pb] at hm_body
  let BaseFrame : SepProp :=
    sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ ((sp + 0x50#64) ↦₃₂ 1#32) ∗
    ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
    ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
    ((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗
    ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗ memRegion (sp + 0xe4#64) 4 ∗
    vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
    ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗ memRegion x.ret 48 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
    memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
    ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x238#64) 0x78 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗
    memRegion (sp + 0x2c0#64) 0x14 ∗ memRegion (sp + 0x2d4#64) 0xfc ∗ memRegion (sp + 0x3f4#64) 12 ∗
    ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x450#64) 0x50 ∗
    memRegion (sp + 0x4a0#64) 0x20 ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗ memRegion (sp + 0x560#64) 0x20 ∗
    protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
    vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
    boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
    boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
    optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
    ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
    ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ memRegion (x.msgA + 0x71#64) 7 ∗ envHeap ∗
    tryDecryptSavedRegs s0.sp s0
  let gcs0 := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hsplit_sp16 := memRegion_split sp 12 4 (by decide)
  rw [show (12 + 4 : Nat) = 0x10 from rfl,
      show sp + 12#64 = sp + 0xc#64 from rfl] at hsplit_sp16
  rw [hsplit_sp16] at hm_body
  let Frame12 : SepProp :=
    vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
    memRegion (sp + 0xc#64) 4 ∗ memRegion (sp + 0x1d8#64) 0x60 ∗ memRegion (sp + 0x500#64) 0x60 ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
      (tryDecryptSubStack - (hookStack + 48)) ∗ BaseFrame
  have hm_step12 : s.mem ⊨
      dhCommitStep12Pre A lim st0 (hookStack + 48) s sp x.msgA sc.chainKey.index
        tr.ratchet.previousCounter finalRootKey senderChainKey receiverChainKey
        x.msg.senderRatchetKey ∗ (Frame12 ∗ R) := by
    dsimp only [dhCommitStep12Pre, Frame12, BaseFrame]
    refine Satisfies.mono (Entails.of_eq ?_) hm_body
    sep_ac_rfl
  obtain ⟨s1, hsteps12, boxPtr, srkPtr, ckPtr, pad, hsrk0, hpad, hpc1, hrun1, hsp1, hsp_align1,
      htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1,
      hvregs_1, hL1, hm1⟩ :=
    dhCommit_step1_2_withStack_placed (hlr_alloc := hlr_alloc) hwp.step12 A lim st0 hookStack hhook_lo hhook_hi
      hPkSer hShim hAlloc hMemcpy hToPb hfits12
      R Frame12 s0 s sp x.msgA sc.chainKey.index tr.ratchet.previousCounter
      finalRootKey senderChainKey receiverChainKey x.msg.senderRatchetKey
      hpc_s hrun hsp hsp_align htr hx22 hx25 hx27 hx28 hL hm_step12
  let st_12 := M.stepEvents dhCommitStep12Events st0
  have hstk_grow := stackAt_split_from sp tryDecryptSubStack growStk hgrow_le (by decide)
  have hsplit_1d8_32 := memRegion_split (sp + 0x1d8#64) 32 0x40 (by decide)
  rw [show (32 + 0x40 : Nat) = 0x60 from rfl,
      show sp + 0x1d8#64 + 32#64 = sp + 0x1f8#64 from add_assoc_const _ _ _ _] at hsplit_1d8_32
  have hjoin_1b0_72 := (memRegion_split (sp + 0x1b0#64) 40 32 (by decide)).symm
  rw [show (40 + 32 : Nat) = 72 from rfl,
      show sp + 0x1b0#64 + 40#64 = sp + 0x1d8#64 from add_assoc_const _ _ _ _] at hjoin_1b0_72
  have hm1_sp8 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (cell_to_memRegion_8 sp boxPtr))) hm1
  have hm1_prep : s1.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
          (tryDecryptSubStack - (hookStack + 48)) ∗ stackAt sp (hookStack + 48)) ∗
      (memRegion (sp + 0x1b0#64) 40 ∗ memRegion (sp + 0x1d8#64) 32) ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
      memRegion sp 8 ∗ ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
      ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
      memRegion (sp + 0x1f8#64) 0x40 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗ ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗ memRegion (sp + 0x500#64) 0x60 ∗
      ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
      (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
      optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗ A.pool lim st_12 s1 ∗
      BaseFrame ∗ R := by
    dsimp only [Frame12, st_12] at hm1_sp8 ⊢
    rw [hsplit_1d8_32] at hm1_sp8
    refine Satisfies.mono (Entails.of_eq ?_) hm1_sp8
    sep_ac_rfl
  rw [← hstk_pb, hstk_grow, hjoin_1b0_72, vecAt_chains_eq] at hm1_prep
  let Frame3 : SepProp :=
    memRegion sp 8 ∗ ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
    ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index) ∗ ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
    memRegion (sp + 0x1f8#64) 0x40 ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
    ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗ ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
    ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x500#64) 0x60 ∗ ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
      (tryDecryptSubStack - growStk) ∗ BaseFrame
  have hm_step3 : s1.mem ⊨
      (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs0.length) ∗
       vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) trG.ratchet.chainsCap trG.ratchet.chainsPtr gcs0 ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some receiverChainKey) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ x.msg.senderRatchetKey.serialize)) ∗
       optChainKeyHeap A.repAlloc ⟨32#64, ckPtr⟩ (some receiverChainKey) ∗ A.pool lim st_12 s1 ∗
       stackAt sp growStk) ∗ (Frame3 ∗ R) := by
    dsimp only [Frame3]
    refine Satisfies.mono (Entails.of_eq ?_) hm1_prep
    sep_ac_rfl
  have hgcs0_len_eq : gcs0.length = tr.ratchet.receiverChains.length := by
    dsimp only [gcs0]
    rw [List.length_zip, hchains_len, Nat.min_self]
  have hgcs0_len : gcs0.length < 2 ^ 32 := hgcs0_len_eq ▸ hrc_len
  have hfits3a : FitsEvents M lim st_12
      (dhCommitStep3aEvents trG.ratchet.chainsCap (BitVec.ofNat 64 gcs0.length)) := by
    rw [hgcs0_len_eq]
    exact hfits3a_rc
  let cap' := dhStepNewChainsCap trG.ratchet.chainsCap tr.ratchet.receiverChains.length
  obtain ⟨s2, hsteps3, ptr', hpc2, hrun2, hsp2, hsp_align2, htr2,
      hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx25_2, hx29_2, hvregs_2, hL2, hm2⟩ :=
    dhCommit_step3_pinned_of_wp (hlr_dealloc := hlr_dealloc) hwp.step3 hgrow_lo hgrow_hi A lim st_12 hGrowOne hDealloc
      R Frame3 s0 s1 sp trG.ratchet.chainsCap trG.ratchet.chainsPtr boxPtr srkPtr ckPtr gcs0
      x.msg.senderRatchetKey receiverChainKey pad hgcs0_len hpad hsrk0 hfits3a
      hpc1 hrun1 hsp1 hsp_align1 htr1 hx25_1 hx26_1 hx27_1 hx28_1 hL1 hm_step3
  let st_123 := M.stepEvents (dhCommitAllocEvents trG.ratchet.chainsCap
    (BitVec.ofNat 64 tr.ratchet.receiverChains.length)) st0
  have hcap'_eq : dhStepNewChainsCap trG.ratchet.chainsCap gcs0.length = cap' := by
    dsimp only [cap']
    rw [hgcs0_len_eq]
  have hst_123_eq :
      M.stepEvents (dhCommitStep3Events trG.ratchet.chainsCap (BitVec.ofNat 64 gcs0.length)) st_12 =
        st_123 := by
    dsimp only [st_123, st_12, dhCommitAllocEvents]
    rw [hgcs0_len_eq, ← M.stepEvents_append]
  rw [hcap'_eq, hst_123_eq] at hm2
  let gcs1 := gcs0 ++ [(newChainGhost srkPtr ckPtr x.msg.senderRatchetKey, newChain)]
  have hstk_drop := stackAt_split_from sp tryDecryptSubStack dropStk hdrop_le (by decide)
  have hjoin_1f8 := (memRegion_split (sp + 0x1f8#64) 0x40 0x78 (by decide)).symm
  rw [show (0x40 + 0x78 : Nat) = 0xb8 from rfl,
      show sp + 0x1f8#64 + 64#64 = sp + 0x238#64 from add_assoc_const _ _ _ _] at hjoin_1f8
  have hck_94 := (chainKeyBytes_pointsTo (sp + 0x94#64) sc.chainKey).symm
  rw [show sp + 0x94#64 + 32#64 = sp + 0xb4#64 from add_assoc_const _ _ _ _] at hck_94
  have hm2_prep : s2.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
          (tryDecryptSubStack - growStk) ∗ stackAt sp growStk) ∗
      (memRegion (sp + 0x1f8#64) 0x40 ∗ memRegion (sp + 0x238#64) 0x78) ∗
      (((sp + 0x94#64) ↦ₛ keyToBytes32 sc.chainKey.key) ∗ ((sp + 0xb4#64) ↦₃₂ sc.chainKey.index)) ∗
      ((sp + 0x38#64) ↦₆₄ cap') ∗ ((sp + 0x40#64) ↦₆₄ ptr') ∗
      ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs1.length) ∗
      vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) cap' ptr' gcs1 ∗ memRegion (sp + 0x190#64) 104 ∗
      memRegion (sp + 0x500#64) 96 ∗ memRegion sp 8 ∗ A.pool lim st_123 s2 ∗
      ((sp + 8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗ ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
      ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
      sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗ ((sp + 0x50#64) ↦₃₂ 1#32) ∗
      ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗ memRegion (sp + 0xe4#64) 4 ∗
      vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
      ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
      ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗ memRegion x.ret 48 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x50 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x14 ∗ memRegion (sp + 0x2d4#64) 0xfc ∗ memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗ memRegion (sp + 0x450#64) 0x50 ∗
      memRegion (sp + 0x4a0#64) 0x20 ∗ ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗ memRegion (sp + 0x560#64) 0x20 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
      vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
      boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
      boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
      optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
      ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
      ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ memRegion (x.msgA + 0x71#64) 7 ∗ envHeap ∗
      tryDecryptSavedRegs s0.sp s0 ∗ R := by
    dsimp only [Frame3, BaseFrame, gcs1, newReceiverChain, newChain] at hm2 ⊢
    refine Satisfies.mono (Entails.of_eq ?_) hm2
    sep_ac_rfl
  rw [← hstk_grow, hstk_drop, hjoin_1f8, hck_94] at hm2_prep
  let TailFrame : SepProp :=
    sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
    ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
    ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
    ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗ memRegion (sp + 0xe4#64) 4 ∗
    vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
    ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
    ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗ memRegion x.ret 48 ∗
    ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗
    vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
    boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
    boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
    ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
    ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
    ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ memRegion (x.msgA + 0x71#64) 7 ∗ envHeap ∗
    tryDecryptSavedRegs s0.sp s0
  let Step5Cells : SepProp :=
    memRegion sp 8 ∗ ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
    ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
    memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x50#64) ↦₃₂ 1#32) ∗
    ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
    ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
    ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x1f8#64) 0xb8 ∗ memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x14 ∗
    memRegion (sp + 0x2d4#64) 0xfc ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
    memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
    ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
    ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x450#64) 0x50 ∗ memRegion (sp + 0x4a0#64) 0x20 ∗
    ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
    ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
    ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗ ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗
    ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗
    memRegion (sp + 0x560#64) 0x20
  let Frame4 : SepProp :=
    ((sp + 0x38#64) ↦₆₄ cap') ∗ Step5Cells ∗ memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
      (tryDecryptSubStack - dropStk) ∗ TailFrame
  have hm_step4 : s2.mem ⊨
      evictActiveWithStack dropStk A lim st_123 s2 sp cap' ptr' gcs1 ∗ (Frame4 ∗ R) := by
    dsimp only [evictActiveWithStack, Frame4, Step5Cells, TailFrame]
    refine Satisfies.mono (Entails.of_eq ?_) hm2_prep
    sep_ac_rfl
  have hgcs1_len : gcs1.length = tr.ratchet.receiverChains.length + 1 := by
    dsimp only [gcs1, gcs0]
    rw [List.length_append, List.length_zip, hchains_len, Nat.min_self]
    rfl
  have hle4 : gcs1.length ≤ 2 ^ 32 := le_of_eq_succ_lt hgcs1_len hrc_len
  obtain ⟨s3, hsteps4, evs_free, hfree, hpc3, hrun3, hsp3, hsp_align3, htr3,
      hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx29_3, hvregs_3, hL3, hm3⟩ :=
    dhCommit_step4_of_wp A lim st_123 R Frame4 s0 s2 sp cap' ptr'
      hwp.step45.step4a_lo hwp.step45.step4a_ge
      (fun s' st' gc₀ gcs' hlen' hpc' hrun' hsp' hal' htr' hx23' hx24' hx25' hx27' hx28' hL' hm' =>
        dhCommit_evict_one_of_wp A lim st' hwp.step45.step4b_pre_memmove
          hwp.step45.step4b_post_memmove hMemmove hDropChain R Frame4 s0 s' sp cap' ptr' gc₀ gcs'
          hlen' hpc' hrun' hsp' hal' htr' hx23' hx24' hx25' hx27' hx28' hL' hm' hlr_ls)
      hwp.step45.step4c_hi hwp.step45.step4c_le
      gcs1 hle4 hpc2 hrun2 hsp2 hsp_align2 htr2
      (hx23_2.trans (hx23_1.trans hx23)) hx25_2 hL2 hm_step4
  let evs_all := dhCommitAllocEvents trG.ratchet.chainsCap
    (BitVec.ofNat 64 tr.ratchet.receiverChains.length) ++ evs_free
  let st_f := M.stepEvents evs_all st0
  have hst_f_eq : M.stepEvents evs_free st_123 = st_f := by
    dsimp only [st_f, evs_all, st_123]
    exact (M.stepEvents_append _ _ _).symm
  rw [hst_f_eq] at hm3
  let Frame5 : SepProp :=
    vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) cap' ptr' (evictGcs gcs1) ∗
    A.pool lim st_f s3 ∗ stackAt sp tryDecryptSubStack ∗ TailFrame
  have hm_step5 : s3.mem ⊨
      memRegion sp 8 ∗ ((sp + 0x8#64) ↦₃₂ sckWord16 senderChainKey) ∗ memRegion (sp + 0xc#64) 4 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗ ((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x50#64) ↦₃₂ 1#32) ∗
      ((sp + 0x54#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
      ((sp + 0x74#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
      ((sp + 0x94#64) ↦ₛ chainKeyBytes sc.chainKey) ∗ memRegion (sp + 0x140#64) 0x50 ∗
      memRegion (sp + 0x190#64) 104 ∗ memRegion (sp + 0x1f8#64) 0xb8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗ memRegion (sp + 0x2c0#64) 0x14 ∗
      memRegion (sp + 0x2d4#64) 0xfc ∗ ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗ ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      ((sp + 0x440#64) ↦₆₄ sckWord0 senderChainKey) ∗ ((sp + 0x448#64) ↦₆₄ sckWord8 senderChainKey) ∗
      memRegion (sp + 0x450#64) 0x50 ∗ memRegion (sp + 0x4a0#64) 0x20 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      ((sp + 0x4e0#64) ↦₆₄ sckWord20 senderChainKey) ∗
      ((sp + 0x4e8#64) ↦₆₄ sckWord28 senderChainKey) ∗ ((sp + 0x4f0#64) ↦₆₄ sckWord0 senderChainKey) ∗
      ((sp + 0x4f8#64) ↦₆₄ sckWord8 senderChainKey) ∗ memRegion (sp + 0x500#64) 96 ∗
      memRegion (sp + 0x560#64) 0x20 ∗ (Frame5 ∗ R) := by
    dsimp only [evictActiveWithStack, Frame4, Step5Cells, Frame5, evictGcs] at hm3 ⊢
    rw [vecAt_chains_eq, hstk_drop]
    refine Satisfies.mono (Entails.of_eq ?_) hm3
    sep_ac_rfl
  obtain ⟨sf, hsteps5, hvm5, hpcf, hrunf, hspf, hsp_alignf, htrf,
      hx12f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx29f, _hx30f, hvregsf, _hLf, hmf⟩ :=
    dhCommit_step5_of_wp trG.ratchet.senderPad sc receiverChainKey newSenderKey senderChainKey
      msgW Frame5 R s3 sp hwp.step45.step5 hpc3 hrun3 hsp3 hsp_align3 hx25_3 hL3 hm_step5
  let trG' : TrGhost := { trG with ratchet := { trG.ratchet with
    chainsCap := cap', chainsPtr := ptr', chains := (evictGcs gcs1).map Prod.fst } }
  have henv_all :
      DhCommitEnv trG.ratchet.chainsCap (BitVec.ofNat 64 tr.ratchet.receiverChains.length) evs_all :=
    Or.inr ⟨_, _, rfl, rfl, hfree⟩
  have hcaps_trG' :
      trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length :=
    trGhostCaps_after_commit trG tr.ratchet.receiverChains ptr' srkPtr ckPtr
      x.msg.senderRatchetKey newChain hchains_len
  have hsteps_all : Steps prog s sf := ((hsteps12.trans hsteps3).trans hsteps4).trans hsteps5
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hx29f.trans (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29)))
  have hx19_f : sf.readReg64 .x19 = x.ret := hx19f.trans (hx19_3.trans (hx19_2.trans (hx19_1.trans hx19)))
  have hx20_f : sf.readReg64 .x20 = sp + 0x140#64 := hx20f.trans (hx20_3.trans (hx20_2.trans (hx20_1.trans hx20)))
  have hx21_f : sf.readReg64 .x21 = x.ss := hx21f.trans (hx21_3.trans (hx21_2.trans (hx21_1.trans hx21)))
  have hx22_f : sf.readReg64 .x22 = x.msgA := hx22f.trans (hx22_3.trans (hx22_2.trans hx22_1))
  have hx23_f : sf.readReg64 .x23 = sp + 0x500#64 := hx23f.trans hx23_3
  have hx24_f : (sf.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType := by
    rw [hx24f, setWidth8_zeroExtend64_shared_lb, hmsgW]
  have hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    hvregsf.trans (hvregs_3.trans (hvregs_2.trans (hvregs_1.trans hvregs)))
  refine ⟨sf, evs_all, trG', hsteps_all, henv_all, hcaps_trG', hpcf,
    ⟨hrunf, hspf, hsp0_align, hsp_alignf, hx29_f, htrf.trans htr3, hvregs_f⟩,
    hx12f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25f, ?_⟩
  have h_map_snd_gcs1 : gcs1.map Prod.snd = tr.ratchet.receiverChains ++ [newChain] :=
    map_snd_zip_append trG.ratchet.chains tr.ratchet.receiverChains
      (newChainGhost srkPtr ckPtr x.msg.senderRatchetKey) newChain hchains_len
  have h_evict_snd : (evictGcs gcs1).map Prod.snd = r1.receiverChains := by
    rw [map_snd_evictGcs, h_map_snd_gcs1]
  have h_zip_trG' : trG'.ratchet.chains.zip r1.receiverChains = evictGcs gcs1 := by
    dsimp only [trG']; rw [← h_evict_snd, zip_map_fst_snd]
  have h_len_trG' : trG'.ratchet.chains.length = r1.receiverChains.length := by
    dsimp only [trG']; rw [← h_evict_snd, List.length_map, List.length_map]
  have h_clamp_r1 : ∀ sc', r1.senderChain = some sc' →
      clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes := by
    intro sc' hsc'; injection hsc' with hsc'_eq; subst hsc'_eq; exact hclamp
  dsimp only [trAt, ratchetAt, signalMessageAt, Frame5, TailFrame, st_f] at hmf ⊢
  rw [← A.pool_transport lim (M.stepEvents evs_all st0) s3 sf hvm5] at hmf
  rw [h_zip_trG',
      show sp + 0x38#64 + 24#64 = sp + 0x50#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 128#64 = sp + 0xb8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 160#64 = sp + 0xd8#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 168#64 = sp + 0xe0#64 from add_assoc_const _ _ _ _,
      show sp + 0x38#64 + 172#64 = sp + 0xe4#64 from add_assoc_const _ _ _ _]
  have hmf_pures : sf.mem ⊨
      ⌜∀ sc', r1.senderChain = some sc' →
        clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes⌝ ∗
      ⌜trG'.ratchet.chains.length = r1.receiverChains.length ∧ trG'.ratchet.senderPad.length = 100 ∧
        r1.maxForwardJumps < 2 ^ 64⌝ ∗ ⌜macLength + 1 ≤ x.msg.serialized.length ∧
        x.msg.serialized.length < 2 ^ 40 ∧
        x.msg.ciphertext.length < 2 ^ 40 ∧ x.msg.pqRatchet.length < 2 ^ 40 ∧
        (∀ ad, x.msg.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
      (((sp + 0x50#64) ↦ₛ optSenderChainBytes (some ⟨newSenderKey, senderChainKey⟩) trG.ratchet.senderPad) ∗
       memRegion sp 0x20 ∗ memRegion (sp + 0x140#64) 0x170 ∗
       ((sp + 0x2b0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
       ((sp + 0x2c0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 20) ∗
       memRegion (sp + 0x2d4#64) 0x2ac ∗
       ((vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (sp + 0x38#64) cap' ptr' (evictGcs gcs1) ∗
         A.pool lim (M.stepEvents evs_all st0) sf ∗ stackAt sp tryDecryptSubStack ∗
         (sessionStateAt A.repAlloc x.ss x.G.afterTrFrom st1 ∗
          ((sp + 0xb8#64) ↦ₛ keyToBytes32 finalRootKey) ∗
          ((sp + 0xd8#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
          ((sp + 0xe0#64) ↦₃₂ BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)) ∗
          memRegion (sp + 0xe4#64) 4 ∗
          vecU8At A.repAlloc (sp + 0x38#64 + 0xb0#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
          ((sp + 0x38#64 + 0xc8#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
          ((sp + 0x38#64 + 0xe8#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList) ∗
          memRegion x.ret 48 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗ ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          vecU8At A.repAlloc x.msgA x.msgG.pqCap x.msgG.pqPtr x.msg.pqRatchet ∗
          boxU8At A.repAlloc (x.msgA + 0x18#64) x.msgG.ctPtr x.msg.ciphertext ∗
          boxU8At A.repAlloc (x.msgA + 0x28#64) x.msgG.serPtr x.msg.serialized ∗
          ((x.msgA + 0x38#64) ↦ₛ x.msg.senderRatchetKey.bytes.toList) ∗
          optBoxU8At A.repAlloc (x.msgA + 0x58#64) x.msgG.addrPtr x.msg.addresses ∗
          ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ ((x.msgA + 0x6c#64) ↦₃₂ x.msg.previousCounter) ∗
          ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ memRegion (x.msgA + 0x71#64) 7 ∗ envHeap ∗
          tryDecryptSavedRegs s0.sp s0)) ∗ R)) := by
    rw [satisfies_pure_sepConj]
    refine ⟨h_clamp_r1, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨h_len_trG', hpad_len, hmfj⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    exact ⟨hmsg_pure, hmf⟩
  refine Satisfies.mono (Entails.of_eq ?_) hmf_pures
  dsimp only [sp, r1, newChain, trG']
  rw [show sessionStateAt (A.atState lim (M.stepEvents evs_all st0) sf) = sessionStateAt A.repAlloc from rfl,
      show protocolAddressAt (A.atState lim (M.stepEvents evs_all st0) sf) = protocolAddressAt A.repAlloc from rfl,
      show vecAt (A.atState lim (M.stepEvents evs_all st0) sf) 104 8
          (chainAt (A.atState lim (M.stepEvents evs_all st0) sf)) =
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) from rfl,
      show vecU8At (A.atState lim (M.stepEvents evs_all st0) sf) = vecU8At A.repAlloc from rfl,
      show boxU8At (A.atState lim (M.stepEvents evs_all st0) sf) = boxU8At A.repAlloc from rfl,
      show optBoxU8At (A.atState lim (M.stepEvents evs_all st0) sf) = optBoxU8At A.repAlloc from rfl]
  sep_ac_rfl

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommit433PlacedBudgetAux
