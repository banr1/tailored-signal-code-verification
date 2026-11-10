/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePend
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Entry Prefix and Pending-Key Clearing

Relocatable `[LibsignalPlacement]` counterparts of `archive_clear_to_shim_cps`,
`archive_shim_to_raw_cps`, and `archive_head_to_raw_cps` on Block `51` (`lsProg_51 H`), along with
`ArchiveOverGenPlacedOk` and `PromoteStateOverGenPlacedOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] Program.fetch Program.externAt?

/-- Relocatable `[LibsignalPlacement]` counterpart of `ArchiveOverGenOk` on `lsProg_51 H`. -/
def ArchiveOverGenPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_51 H) (blkPl_51).base (withLsCodeLoaded lsmpl (archiveOverGenSpec A))

/-- Relocatable `[LibsignalPlacement]` counterpart of `PromoteStateOverGenOk` on `lsProg_47 H`. -/
def PromoteStateOverGenPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_47 H) (blkPl_47).base (withLsCodeLoaded lsmpl (promoteOverGenSpec A))

/-- Relocatable `[LibsignalPlacement]` counterpart of `ArchiveOverOkX` on `lsProg_51 H`. -/
def ArchiveOverPlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_51 H) (blkPl_51).base (withLsCodeLoaded lsmpl (archiveOverSpecX A))

/-- Relocatable `[LibsignalPlacement]` counterpart of `PromoteStateOverOkX` on `lsProg_47 H`. -/
def PromoteStateOverPlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_47 H) (blkPl_47).base (withLsCodeLoaded lsmpl (promoteOverSpecX A))

private abbrev lhsOfNe_arch {α : Type} {x y : α} (_ : x ≠ y) : α := x

private theorem sepWPpLsCl_split_x0_arch {pl : MultiPlacement} {prog : Program}
    {ret_pc : BitVec 64} {s : State}
    {P : SepProp} {Qp Q : State → SepProp → Prop}
    (h0 : s.readReg64 .x0 = 0#64 → SepWPpLsCl pl prog ret_pc s P Qp Q)
    (hn : s.readReg64 .x0 ≠ 0#64 → SepWPpLsCl pl prog ret_pc s P Qp Q) :
    SepWPpLsCl pl prog ret_pc s P Qp Q := by
  by_cases h : s.readReg64 .x0 = 0#64
  · exact h0 h
  · exact hn h

/-! ## Entry to Allocator-Shim Return -/

set_option maxHeartbeats 800000 in
theorem archive_clear_to_shim_placed_cps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (Fprev R : SepProp)
    (s0 : State)
    (Q : State → SepProp → Prop)
    (hpc : s0.pc = (blkPl_51).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 : BitVec 64) (v112 : BitVec 128)
    (hcont : ∀ (sf : State) (bs336 : List (BitVec 8)),
      bs336.length = 336 →
      sf.pc = (blkPl_51).base + (archiveShimCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) sf
        (archiveMidShimPre A s0 recPtr prevCap prevPtr G sess bs336 c0 c1 c2 c3 v464 v112 Fprev)
        Q (archiveQp s0 R)) :
    SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) s0
      ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
        sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
        stackAt (s0.sp - 464#64) serializeSubStackX ∗
        ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
        memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ Fprev)
      Q (archiveQp s0 R) := by
  have hmemcpy := memcpy_placed_sub_okX (callerProg := lsProg_51 H) hC
  have hdealloc := dealloc_arch_placed_okX (callerProg := lsProg_51 H) hC
  have hshim := shim_placed_sub_okX (callerProg := lsProg_51 H) hC
  have hlen : subroutine_ok (lsProg_51 H) (lsmpl.base 86)
      (withLsCodeLoaded lsmpl (sessionLenSubSpecX A)) :=
    sessionLen_placed_sub_okX (callerProg := lsProg_51 H) (A := A)
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
  refine SepWP.fold (sessionAt_unpack_rec_genX A recPtr G sess) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro bs336
  apply sepWP_pure_left_sepX; rintro ⟨hbs336, hcap, hinl⟩
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hbs336]
  wpplscl_callc hmemcpy (withLsCodeLoaded lsmpl memcpySubSpecX) (s0.sp - 448#64, recPtr + 32#64, bs336)
  obtain ⟨a, pPtr, pRest, kPtr, kTail, ha, hpRest, hkTail, hbs_eq, hinl', hheap⟩ :=
    bs336_split_gen A hinl
  have hsplit448 : ((s0.sp - 448#64) ↦ₛ bs336) ⊢
      (((s0.sp - 448#64) ↦ₛ a) ∗
        ((s0.sp - 208#64) ↦₆₄ optTailCap G.pending) ∗ ((s0.sp - 200#64) ↦₆₄ pPtr) ∗
        ((s0.sp - 192#64) ↦ₛ pRest) ∗
        ((s0.sp - 160#64) ↦₆₄ optTailCap G.kyber) ∗ ((s0.sp - 152#64) ↦₆₄ kPtr) ∗
        ((s0.sp - 144#64) ↦ₛ kTail)) := by
    rw [hbs_eq, bytes448_split_genX s0.sp a pRest kTail _ _ _ _ ha hpRest]
    exact Entails.refl _
  have hpack_clear := sessionAt_pack_456_clearX A s0.sp G sess ha hpRest hinl'
  have hn_pos : 0 < (encSessionMem (clearPendingGhost G) (clearPending sess)).length :=
    encSessionMem_length_pos _ _
  have hlen_enc' : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 4294967296 :=
    hlen_enc
  have hn_toNat : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat =
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hn_b63 : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).getLsbD 63 = false := by
    rw [BitVec.getLsbD_ofNat]
    simp only [Nat.reduceLT, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (by omega)
  have hn_ne0 : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length == 0#64) = false := by
    apply beq_false_of_ne; intro heq
    have h1 : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat = 0 :=
      congrArg BitVec.toNat heq
    rw [hn_toNat] at h1; omega
  by_cases hps : (optTailCap G.pending).slt 1#64 = true
  · obtain ⟨hps_gt0, hps_le0, hps_ge1⟩ := cap_slt_conds_of_true hps
    by_cases hks : (optTailCap G.kyber).slt 1#64 = true
    · obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_true hks
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 86)
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold (heap_split_tt A hheap hps hks) (by sep_focus) ?_
      wp_steps
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wpplscl_callc hlen (withLsCodeLoaded lsmpl (sessionLenSubSpecX A))
        ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wpplscl_callc hshim (withLsCodeLoaded lsmpl shimSubSpecX) ()
      refine SepWPpLsCl.weaken_pre (Entails.of_eq (by unfold archiveMidShimPre; ac_rfl))
        (hcont _ bs336 hbs336 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*]))
    · have hks' : (optTailCap G.kyber).slt 1#64 = false := Bool.eq_false_iff.mpr hks
      obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_false hks'
      apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustDeallocSym)
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold (heap_split_tf A hheap hps hks') (by sep_focus) ?_
      apply sepWP_pure_left_sepX; rintro ⟨hk_pos, hk_lt⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hex_k : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_k : (optTailCap G.kyber).toNat + 1 ≤ 2 ^ 63 := by omega
      wpplscl_callc hdealloc (withLsCodeLoaded lsmpl (rustDeallocSubSpecX A)) (kPtr, (optTailCap G.kyber).toNat, 1)
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 86)
      wp_steps
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wpplscl_callc hlen (withLsCodeLoaded lsmpl (sessionLenSubSpecX A))
        ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wpplscl_callc hshim (withLsCodeLoaded lsmpl shimSubSpecX) ()
      refine SepWPpLsCl.weaken_pre (Entails.of_eq (by unfold archiveMidShimPre; ac_rfl))
        (hcont _ bs336 hbs336 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*]))
  · have hps' : (optTailCap G.pending).slt 1#64 = false := Bool.eq_false_iff.mpr hps
    obtain ⟨hps_gt0, hps_le0, hps_ge1⟩ := cap_slt_conds_of_false hps'
    by_cases hks : (optTailCap G.kyber).slt 1#64 = true
    · obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_true hks
      apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustDeallocSym)
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold (heap_split_ft A hheap hps' hks) (by sep_focus) ?_
      apply sepWP_pure_left_sepX; rintro ⟨hp_pos, hp_lt⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hex_p : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_p : (optTailCap G.pending).toNat + 1 ≤ 2 ^ 63 := by omega
      wpplscl_callc hdealloc (withLsCodeLoaded lsmpl (rustDeallocSubSpecX A)) (pPtr, (optTailCap G.pending).toNat, 1)
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 86)
      wp_steps
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wpplscl_callc hlen (withLsCodeLoaded lsmpl (sessionLenSubSpecX A))
        ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wpplscl_callc hshim (withLsCodeLoaded lsmpl shimSubSpecX) ()
      refine SepWPpLsCl.weaken_pre (Entails.of_eq (by unfold archiveMidShimPre; ac_rfl))
        (hcont _ bs336 hbs336 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*]))
    · have hks' : (optTailCap G.kyber).slt 1#64 = false := Bool.eq_false_iff.mpr hks
      obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_false hks'
      apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustDeallocSym)
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold (heap_split_ff A hheap hps' hks') (by sep_focus) ?_
      apply sepWP_pure_left_sepX; rintro ⟨⟨hp_pos, hp_lt⟩, ⟨hk_pos, hk_lt⟩⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hex_p : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_p : (optTailCap G.pending).toNat + 1 ≤ 2 ^ 63 := by omega
      wpplscl_callc hdealloc (withLsCodeLoaded lsmpl (rustDeallocSubSpecX A)) (pPtr, (optTailCap G.pending).toNat, 1)
      apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hex_k : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_k : (optTailCap G.kyber).toNat + 1 ≤ 2 ^ 63 := by omega
      wpplscl_callc hdealloc (withLsCodeLoaded lsmpl (rustDeallocSubSpecX A)) (kPtr, (optTailCap G.kyber).toNat, 1)
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 86)
      wp_steps
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wpplscl_callc hlen (withLsCodeLoaded lsmpl (sessionLenSubSpecX A))
        ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wpplscl_callc hshim (withLsCodeLoaded lsmpl shimSubSpecX) ()
      refine SepWPpLsCl.weaken_pre (Entails.of_eq (by unfold archiveMidShimPre; ac_rfl))
        (hcont _ bs336 hbs336 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*]))

/-! ## Allocator-Shim Return to `encode_raw` Return -/

set_option maxHeartbeats 800000 in
theorem archive_shim_to_raw_placed_cps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hRaw : EncodeRawPlacedOkX A H)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8))
    (Fprev R : SepProp)
    (s0 s2 : State)
    (Q : State → SepProp → Prop)
    (hsp_align : s0.spAligned = true)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (c0 c1 c2 c3 v464 : BitVec 64) (v112 : BitVec 128)
    (hpc2 : s2.pc = (blkPl_51).base + (archiveShimCutOff + 4#64))
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 464#64)
    (htr2 : s2.trace = s0.trace)
    (hx19 : s2.readReg64 .x19 = recPtr)
    (hx20 : s2.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx23 : s2.readReg64 .x23 = 0#64)
    (hx24 : s2.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s2.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s2.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s2.readReg64 .x29 = s0.sp - 64#64)
    (hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (capEnc ptrEnc : BitVec 64),
      sf.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x21 = s0.sp - 112#64 →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) sf
        (archiveMidRawPre A s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 Fprev)
        Q (archiveQp s0 R)) :
    SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) s2
      (archiveMidShimPre A s0 recPtr prevCap prevPtr G sess bs336 c0 c1 c2 c3 v464 v112 Fprev)
      Q (archiveQp s0 R) := by
  have halloc := alloc_placed_sub_okX (callerProg := lsProg_51 H) hC
  have hpanic := hC.alloc.externAt_handle_error (callerProg := lsProg_51 H)
  have hraw : subroutine_ok (lsProg_51 H) (lsmpl.base 14)
      (withLsCodeLoaded lsmpl (encodeRawSubSpecX A)) :=
    encodeRaw_placed_sub_okX (callerProg := lsProg_51 H) hRaw
  simp only [archiveShimCutOff, arm64_norm] at hpc2
  unfold archiveMidShimPre
  have hn_pos : 0 < (encSessionMem (clearPendingGhost G) (clearPending sess)).length :=
    encSessionMem_length_pos _ _
  have hn_toNat : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat =
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply SepWPpLsCl.of_sepWP (mid := lsρ lsRustAllocSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsz_le : (encSessionMem (clearPendingGhost G) (clearPending sess)).length + 1 ≤ 2 ^ 63 := by
    omega
  have hsz_le' :
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length ≤ 9223372036854775807 := by
    omega
  wpplscl_callc halloc (withLsCodeLoaded lsmpl (rustAllocSubSpecX A))
    ((encSessionMem (clearPendingGhost G) (clearPending sess)).length, 1)
  refine sepWPpLsCl_split_x0_arch (fun hp0 => ?_) (fun hp0 => ?_)
  · conv => arg 5; simp only [hp0, ↓reduceIte, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htr_fail => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPpLsCl.panic (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_eq
          (by simp only [Rust.panicked, htr_fail, htr2, wp_norm, arm64_norm])) hm
  · have hp0' : lhsOfNe_arch hp0 ≠ 0 := hp0
    have hp0_beq : (lhsOfNe_arch hp0 == 0#64) = false := beq_false_of_ne hp0
    conv => arg 5; simp only [hp0', ↓reduceIte, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨halign, htr_alloc⟩ => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 14)
    wp_steps
    refine SepWP.fold
      (vecU8At_nil_88X A s0.sp (lhsOfNe_arch hp0)
        (encSessionMem (clearPendingGhost G) (clearPending sess)).length
        hn_pos (by omega) hp0')
      (by dsimp only [lhsOfNe_arch, Reg.x0]; sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hraw_lt : ([] : List (BitVec 8)).length +
        (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
      simp only [List.length_nil, Nat.zero_add]; exact hlen_enc
    wpplscl_callc hraw (withLsCodeLoaded lsmpl (encodeRawSubSpecX A))
      ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess, s0.sp - 88#64,
        BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length,
        lhsOfNe_arch hp0, []⟩
    refine SepWPpLsCl.weaken_pre (Entails.of_eq (by unfold archiveMidRawPre; ac_rfl))
      (hcont _ _ _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [*]))

/-- Combined relocatable prefix from `archive_current_state_inner` entry through `encode_raw` return. -/
theorem archive_head_to_raw_placed_cps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hRaw : EncodeRawPlacedOkX A H)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (Fprev R : SepProp)
    (s0 : State)
    (Q : State → SepProp → Prop)
    (hpc : s0.pc = (blkPl_51).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 : BitVec 64) (v112 : BitVec 128)
    (hcont : ∀ (sf : State) (bs336 : List (BitVec 8)) (capEnc ptrEnc : BitVec 64),
      bs336.length = 336 →
      sf.pc = (blkPl_51).base + (archiveEncodeRawCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x21 = s0.sp - 112#64 →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) sf
        (archiveMidRawPre A s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 Fprev)
        Q (archiveQp s0 R)) :
    SepWPpLsCl lsmpl (lsProg_51 H) (s0.readReg64 .lr) s0
      ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
        sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
        stackAt (s0.sp - 464#64) serializeSubStackX ∗
        ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
        memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ Fprev)
      Q (archiveQp s0 R) :=
  archive_clear_to_shim_placed_cps hC recPtr prevCap prevPtr G sess Fprev R s0 Q
    hpc hrun hsp_align hx0 hlen_enc c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
    fun s2 bs336 hbs336 hpc2 hrun2 hsp2 htr2 hx19 hx20 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs2 =>
      archive_shim_to_raw_placed_cps hC hRaw recPtr prevCap prevPtr G sess bs336 Fprev R s0 s2 Q
        hsp_align hlen_enc c0 c1 c2 c3 v464 v112
        hpc2 hrun2 hsp2 htr2 hx19 hx20 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs2
        fun sf capEnc ptrEnc => hcont sf bs336 capEnc ptrEnc hbs336

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
