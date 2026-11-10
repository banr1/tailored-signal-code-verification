/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandBlock1
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandLoop
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt

/-!
# Verification of `<GenericHkdf<Hmac<Sha256>>>::expand_multi_info`

Assembles the Block 1, loop-iteration, and `finalize_fixed` segment proofs to establish
`expandMultiInfoSpec` on `tripleRatchetProgAt`, `tripleRatchetProgAtExt`, and under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)

namespace Expand

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

section Assembly

variable {b : BitVec 64} {C : Crypto} {ext : String → Option (State → State)} [HkdfHooks C.F ext]
  {ctl : BitVec 64} {abs : String → Option (State → State)}

/-- Full `RunsTo` contract of `expand_multi_info` (`b + 0x1a874` → `s₀.readReg64 .lr`) on
`tripleRatchetProgAtExt b ext` for both `okmLen = 64` (2 blocks) and `okmLen = 80` (3 blocks), parameterized by
`(hFin : Fin.FinalizeFixedRunsToExt b C ext)`. -/
theorem expand_multi_info_runsTo_ext (hFin : Fin.FinalizeFixedRunsToExt b C ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀) :
    RunsTo (tripleRatchetProgAtExt b ext) s₀ (ExpandPost C.F prk info okmLen s₀) := by
  refine (seg0_runsTo hpre).trans fun s1 hs1 => ?_
  refine (seg1_runsTo hpre hs1).trans fun s2 hs2 => ?_
  refine (seg2a_runsTo hpre hs2).trans fun s3 hs3 => ?_
  refine (seg2b_runsTo hpre hs3).trans fun s4 hs4 => ?_
  refine (fin1_runsTo hFin hpre hs4).trans fun s5 hs5 => ?_
  refine (seg3_runsTo hpre hs5).trans fun s6 hs6 => ?_
  rcases hpre.okm_len with rfl | rfl
  · -- Case `okmLen = 64`: 1 loop iteration (`i = 1, rem = 32, dstOff = 32`)
    refine (iter_to_fin_runsTo hFin hpre (t1_length C.F prk info) (Or.inl rfl) (Or.inl rfl) (by decide) hs6).trans
      fun s7 hs7 => ?_
    have hokm64 : t1 C.F prk info ++ (hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8])).take 32 =
        hkdfExpand C.F prk info 64 := by
      rw [show hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8]) = t2 C.F prk info from rfl,
          List.take_of_length_le (by simp), hkdfExpand_64_eq]
    refine (iter_d_done_runsTo hpre (Or.inl rfl) (Or.inl rfl) rfl hokm64 hs7).trans fun s8 hs8 => ?_
    exact epilogue_runsTo hpre hs8
  · -- Case `okmLen = 80`: 2 loop iterations (`i = 1, rem = 48, dstOff = 32` then `i = 2, rem = 16, dstOff = 64`)
    refine (iter_to_fin_runsTo hFin hpre (t1_length C.F prk info) (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide) hs6).trans
      fun s7 hs7 => ?_
    refine (iter_d_continue_runsTo (tNext := t2 C.F prk info) hpre rfl (by decide) rfl hs7).trans
      fun s8 hs8 => ?_
    refine (iter_to_fin_runsTo hFin hpre (t2_length C.F prk info) (Or.inr rfl) (Or.inr (Or.inr rfl)) (by decide) hs8).trans
      fun s9 hs9 => ?_
    have hokm80 : (t1 C.F prk info ++ t2 C.F prk info) ++
        (hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8])).take 16 =
        hkdfExpand C.F prk info 80 := by
      rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
          hkdfExpand_80_eq]
    refine (iter_d_done_runsTo hpre (Or.inr rfl) (Or.inr rfl) rfl hokm80 hs9).trans fun s10 hs10 => ?_
    exact epilogue_runsTo hpre hs10

theorem expand_multi_info_runsTo (hFin : FinalizeFixedProof.FinalizeFixedRunsTo b C ctl abs)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ : State}
    (hpre : ExpandPre b C.F prk info infoPtr okmLen s₀) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s₀ (ExpandPost C.F prk info okmLen s₀) :=
  expand_multi_info_runsTo_ext (ext := tripleRatchetExterns C ctl abs) hFin hpre

end Assembly

/-! ## Relocatable `[LibsignalPlacement]` Assembly -/

section AssemblyPlaced

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]

theorem ExpandFrame.keepsFrozen {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State} {m : Memory}
    (hpre : ExpandPre b F prk info infoPtr okmLen s₀)
    (hf : ExpandFrame okmLen s₀ m) :
    KeepsFrozenNoAnon s₀.mem m := by
  refine KeepsFrozenNoAnon.of_perm_eq hf.2.1 hf.2.2.2.1 fun a hperm => ?_
  refine hf.1 a (fun r hr => ?_)
  rw [outsideRegion_iff_not_inRegion]
  intro hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have hrw := (Memory.permNoLazy_eq_some_rw_iff.mp (hpre.rw_x2 a hin)).1
    unfold Memory.Frozen at hperm; rw [hrw] at hperm; cases hperm
  · have hrw := (Memory.permNoLazy_eq_some_rw_iff.mp (hpre.rw_stack a hin)).1
    unfold Memory.Frozen at hperm; rw [hrw] at hperm; cases hperm

theorem expand_multi_info_placed_runsTo_of_fin
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ : State}
    (hFin : ∀ {key msg : List (BitVec 8)} {s : State},
      ExpandFrame okmLen s₀ s.mem →
      FinalizeFixedProof.FinPre finPlacedFakeB C.F key msg s →
      RunsTo ((blkPC_53).rebase (blkPl_53).base H) s (FinalizeFixedProof.FinPost C.F key msg s))
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (ExpandPost C.F prk info okmLen s₀) := by
  refine (seg0_placed_runsTo hpre).trans fun s1 hs1 => ?_
  refine (seg1_placed_runsTo hpre hs1).trans fun s2 hs2 => ?_
  refine (seg2a_placed_runsTo hpre hs2).trans fun s3 hs3 => ?_
  refine (seg2b_placed_runsTo hpre hs3).trans fun s4 hs4 => ?_
  refine (fin1_placed_runsTo hFin hpre hs4).trans fun s5 hs5 => ?_
  refine (seg3_placed_runsTo hpre hs5).trans fun s6 hs6 => ?_
  rcases hpre.okm_len with rfl | rfl
  · refine (iter_to_fin_placed_runsTo hFin hpre (t1_length C.F prk info) (Or.inl rfl) (Or.inl rfl) (by decide) hs6).trans
      fun s7 hs7 => ?_
    have hokm64 : t1 C.F prk info ++ (hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8])).take 32 =
        hkdfExpand C.F prk info 64 := by
      rw [show hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8]) = t2 C.F prk info from rfl,
          List.take_of_length_le (by simp), hkdfExpand_64_eq]
    refine (iter_d_done_placed_runsTo hpre (Or.inl rfl) (Or.inl rfl) rfl hokm64 hs7).trans fun s8 hs8 => ?_
    exact epilogue_placed_runsTo hpre hs8
  · refine (iter_to_fin_placed_runsTo hFin hpre (t1_length C.F prk info) (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide) hs6).trans
      fun s7 hs7 => ?_
    refine (iter_d_continue_placed_runsTo (tNext := t2 C.F prk info) hpre rfl (by decide) rfl hs7).trans
      fun s8 hs8 => ?_
    refine (iter_to_fin_placed_runsTo hFin hpre (t2_length C.F prk info) (Or.inr rfl) (Or.inr (Or.inr rfl)) (by decide) hs8).trans
      fun s9 hs9 => ?_
    have hokm80 : (t1 C.F prk info ++ t2 C.F prk info) ++
        (hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8])).take 16 =
        hkdfExpand C.F prk info 80 := by
      rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
          hkdfExpand_80_eq]
    refine (iter_d_done_placed_runsTo hpre (Or.inr rfl) (Or.inr rfl) rfl hokm80 hs9).trans fun s10 hs10 => ?_
    exact epilogue_placed_runsTo hpre hs10

theorem expand_multi_info_placed_runsTo
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ : State}
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem)
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (ExpandPost C.F prk info okmLen s₀) := by
  refine expand_multi_info_placed_runsTo_of_fin (fun hf hfin_pre => ?_) hpre
  have hkf : KeepsFrozenNoAnon s₀.mem _ := ExpandFrame.keepsFrozen hpre hf
  have hcl_s : LibsignalCodeLoaded lsmpl _ :=
    fun i hi hunmut ext panics svc => Program.CodeLoaded.of_keepsFrozenNoAnon (hcl i hi hunmut ext panics svc) hkf
  exact FinalizeFixedProof.finalize_fixed_placed_runsTo_of_other_block hcl_s hfin_pre

end AssemblyPlaced
end Expand

/-! ## Separation Logic Bridge and Top-Level `expand_multi_info_ok` -/

open Expand in
theorem ro_outside_rw_shared_lb {P Q R : SepProp} {b_ro b_rw : BitVec 64} {n_ro n_rw : ℕ}
    {Φ_ro Φ_rw : Memory → Prop} {m : Memory}
    (hro : IsBlockRO P b_ro n_ro Φ_ro)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ P ∗ (Q ∗ R)) :
    ∀ a, InRegion b_ro n_ro a → OutsideRegion b_rw n_rw a := by
  intro a ha_ro
  rw [outsideRegion_iff_not_inRegion]
  intro ha_rw
  have hQPR : m ⊨ Q ∗ (P ∗ R) := by rwa [sepConj_left_comm]
  have hperm : m.perm a = some Perm.rw := hrw.perm_rw hQPR ha_rw
  have hm_reg : m ⊨ memRegion b_rw n_rw ∗ (P ∗ R) :=
    hrw.update (IsBlock.memRegion b_rw n_rw) (Nat.le_refl _) hQPR
      (AgreesOutside.rfl' m b_rw n_rw) trivial
  have hm_lf := Satisfies.madvFreeNonFrozen hm_reg
  rw [sepConj_left_comm] at hm_lf
  have hfalse := hro.isLazyFree_false hm_lf ha_ro
  rw [Memory.isLazyFree_madvFreeNonFrozen] at hfalse
  have hin : (a - b_rw).toNat < n_rw := ha_rw
  have hcond : ((some Perm.rw).mapped && !(some Perm.rw).frozen) = true := rfl
  simp only [hin, hperm, decide_true, Bool.true_and, hcond, ↓reduceIte] at hfalse
  cases hfalse

open Expand in
theorem expand_multi_info_ok_ext (b : BitVec 64) (C : Crypto)
    (ext : String → Option (State → State)) [HkdfHooks C.F ext] :
    ExpandMultiInfoOkExt b C ext := by
  unfold ExpandMultiInfoOkExt
  have hfn : (tripleRatchetProgAtExt b ext).fnAddr expandMultiInfoName = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info") := by
    unfold tripleRatchetProgAtExt expandMultiInfoName
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info")]
  rw [hfn]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [expandMultiInfoSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, hokm_len⟩, hsep⟩
  change s0.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      memRegion (s0.sp - 640#64) 640) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt C.F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) (BitVec.ofNat 64 x.info.length)
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = BitVec.ofNat 64 x.info.length) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (s0.sp - 640#64) 640
  let R_inv : SepProp :=
    hmacCoreAt C.F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (x.infoA ↦ᵣ x.info) ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗ (memRegion (s0.sp - 640#64) 640 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 640#64) 640 ∗ (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion x.okmA x.okmLen ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hokm_pos : 0 < x.okmLen := by omega
  have h_exp_pre : ExpandPre b C.F x.prk x.info x.infoA x.okmLen s0 :=
    { pc_eq := hpc
      status := hrun
      x3_eq := hx3
      prk_le := hprk_le
      info_lt := hinfo_lt
      okm_len := hokm_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := hro_info.read hsep_info_stk
      read_x0 := by rw [hx0]; exact Memory.RW.readable (fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha)
      read_x1 := by rw [hx1]; exact Memory.RW.readable (fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha)
      rw_x2 := by rw [hx2]; exact fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
      rw_stack := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
      disj_x2_stack := by rw [hx2]; exact hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) hokm_pos hsep_hm_okm
      disj_x1_stack := by rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) hokm_pos hsep_hdr_okm
      out_info_stk := ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by rw [hx2]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  have hFin : Fin.FinalizeFixedRunsToExt b C ext :=
    fun hpre => FinalizeFixedProof.finalize_fixed_runsTo_ext hpre
  refine (expand_multi_info_runsTo_ext hFin h_exp_pre).to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [expandMultiInfoSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrame at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info x.okmLen).length = x.okmLen := by
    rcases hokm_len with h64 | h80
    · rw [h64, Expand.hkdfExpand_64_eq]
      simp [Expand.t1_length, Expand.t2_length]
    · rw [h80, Expand.hkdfExpand_80_eq]
      simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      (memRegion (s0.sp - 640#64) 640 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      memRegion (s0.sp - 640#64) 640) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

open Expand in
theorem expand_multi_info_ok_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    ExpandMultiInfoOk_trap b C abs :=
  expand_multi_info_ok_ext b C (trTrapExterns C abs)

open Expand in
theorem expand_multi_info_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    ExpandMultiInfoOk b C ctl abs := by
  unfold ExpandMultiInfoOk
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr expandMultiInfoName]
  exact subroutine_ok_kit_of_trTrap (expand_multi_info_ok_trap b C abs)

/-! ## Contract-Backed `ExpandMultiInfoOkExt'` at `expandMultiInfoStackExt` (`17024` B) -/

namespace HkdfExt.ExpandExt

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

open Expand
open Extract (RunsToE S2Frame)

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  sp_sub_496_eq_esp sp_add_neg496_eq_esp esp_add_496_sub_496
  read8_write64_120_127 CryptoVerification.LibsignalTripleRatchet.Expand.truncate8_ofNat64
  bv32_zero_add bv8_zero_add
  t1_length t2_length t3_length

section AssemblyX

variable {img : Obj.Image} {C : Crypto} {F : ShaState → List (BitVec 8) → ShaState}
  {ext : String → Option (State → State)}

theorem fin1_x_runsTo (hFin : FinalizeFixedOkExt' img C ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img C.F prk info infoPtr okmLen s₀)
    (hkf : s₀.mem.KeepsFrozen s.mem)
    (hsym : s.symtab = s₀.symtab)
    (hx : StateX2X img.base C.F prk info infoPtr okmLen s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateX2rX img.base C.F prk info infoPtr okmLen s₀) := by
  rcases fin_side_conditions_x (C := C) hpre hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin := finalize_fixed_runsTo_ext_x hFin
    (hpre.frozen.of_keepsFrozen hkf)
    (hsym.trans hpre.symtab_eq)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq
    hpre.prk_le (by have := hpre.info_lt; simp; omega)
    hx.hmac_240 hrw_x0 hrw_x1
    (by rw [hx.common.sp_eq]; exact hrw_sp)
    hd_x0_x1
    (by rw [hx.common.sp_eq]; exact hd_x0_sp)
    (by rw [hx.common.sp_eq]; exact hd_x1_sp)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)
  refine hfin.mono fun s' ⟨hpc', hstat', hcc, ht1, hfr⟩ => ?_
  rw [hx.common.sp_eq] at hfr
  exact ⟨hpc'.trans hx.lr_eq,
    ExpandCommonX.of_fin_frame_x hpre hx.common hstat' hcc hfr,
    (Extract.CallingConventionPreserved.x22 hcc).trans hx.x22_eq,
    (CallingConventionPreserved.x23 hcc).trans hx.x23_eq,
    (CallingConventionPreserved.x26 hcc).trans hx.x26_eq,
    ht1⟩

theorem iter_c_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopBX img.base F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s
      (StateLoopCX img.base F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hx.common.frame
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommonX.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx19, ?_, hx22, hx23, hx24, ?_, hx28, ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hrem with rfl | rfl | rfl <;> rfl
  · simp only [mem_setMem]
    exact HmacSt.of_copy_esp_64_240 hx.hmac_64
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 240#64) 0x90 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 240#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 240#64 0x90 hd (by prove_agrees_esp)
        (by have := hpre.okm_len; omega) hx.okm_pre

theorem iter_fin_x_runsTo (hFin : FinalizeFixedOkExt' img C ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hkf : s₀.mem.KeepsFrozen s.mem)
    (hsym : s.symtab = s₀.symtab)
    (hx : StateLoopCX img.base C.F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateLoopFinX img.base C.F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀) := by
  rcases fin_side_conditions_x (C := C) hpre hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen := ExpandFrameX.rw_x2 hpre hx.common.frame
  have hfin := finalize_fixed_runsTo_ext_x hFin
    (hpre.frozen.of_keepsFrozen hkf)
    (hsym.trans hpre.symtab_eq)
    hx.pc_eq hx.common.status hx.x0_eq hx.x1_eq
    hpre.prk_le (by have := hpre.info_lt; simp [ht_len]; omega)
    hx.hmac_240 hrw_x0 hrw_x1
    (by rw [hx.common.sp_eq]; exact hrw_sp)
    hd_x0_x1
    (by rw [hx.common.sp_eq]; exact hd_x0_sp)
    (by rw [hx.common.sp_eq]; exact hd_x1_sp)
    (by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned)
  refine hfin.mono fun s' ⟨hpc', hstat', hcc, ht, hfr⟩ => ?_
  rw [hx.common.sp_eq] at hfr
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (hfr.readBytes_eq (hrw_x2.sub (by have := hpre.okm_len; bv_omega)) (fun r hr => ?_)
        (by have := hpre.okm_len; omega)).trans hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 17024#64) 17024 (s₀.readReg64 .x2) dstOff :=
        hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hd_stk.sub_left _ ⟨by simp, by unfold esp; bv_omega⟩
  exact ⟨hpc'.trans hx.lr_eq,
    ExpandCommonX.of_fin_frame_x hpre hx.common hstat' hcc hfr,
    (Extract.CallingConventionPreserved.x19 hcc).trans hx.x19_eq,
    (Extract.CallingConventionPreserved.x21 hcc).trans hx.x21_eq,
    (Extract.CallingConventionPreserved.x22 hcc).trans hx.x22_eq,
    (CallingConventionPreserved.x23 hcc).trans hx.x23_eq,
    (CallingConventionPreserved.x24 hcc).trans hx.x24_eq,
    (CallingConventionPreserved.x26 hcc).trans hx.x26_eq,
    (CallingConventionPreserved.x28 hcc).trans hx.x28_eq,
    ht, hokm'⟩

theorem iter_d_head_x_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hx : StateLoopFinX img.base F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s_mc =>
      s_mc.pc = img.base + bv% (ls_off% "memcpy") ∧
      s_mc.status = .Running ∧
      s_mc.sp = esp s₀ ∧
      s_mc.readReg64 .lr = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 688) ∧
      s_mc.readReg64 .x0 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff ∧
      s_mc.readReg64 .x1 = esp s₀ + 208#64 ∧
      s_mc.readReg64 .x2 = BitVec.ofNat 64 (min rem 32) ∧
      s_mc.readReg64 .x19 = BitVec.ofNat 64 i ∧
      s_mc.readReg64 .x20 = s₀.readReg64 .x0 ∧
      s_mc.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + min rem 32) ∧
      s_mc.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff ∧
      s_mc.readReg64 .x23 = BitVec.ofNat 64 (min rem 32) ∧
      s_mc.readReg64 .x24 = 64#64 ∧
      s_mc.readReg64 .x26 = BitVec.ofNat 64 (rem - min rem 32) ∧
      s_mc.readReg64 .x27 = esp s₀ + 64#64 ∧
      s_mc.readReg64 .x28 = esp s₀ + 64#64 ∧
      s_mc.readReg64 .x29 = esp s₀ + 400#64 ∧
      s_mc.mem = s.mem) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  iterate 4 s2_step
  refine RunsTo.refl ?_
  exact ⟨rfl, hrun, hsp, rfl, rfl, rfl, rfl,
    hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hx29, rfl⟩

theorem iter_d_continue_tail_x_runsTo
    {prk info okmSoFar tNext : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen dstOff : ℕ} {s₀ s₁ : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hdst : dstOff + 32 ≤ okmLen)
    (hpc₁ : s₁.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 688))
    (hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = 1#64)
    (hx21 : s₁.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + 32))
    (hx24 : s₁.readReg64 .x24 = 64#64)
    (hx26 : s₁.readReg64 .x26 = 16#64)
    (hx28 : s₁.readReg64 .x28 = esp s₀ + 64#64)
    (ht_208 : s₁.mem.readBytes (esp s₀ + 208#64) 32 = tNext)
    (hokm_next : s₁.mem.readBytes (s₀.readReg64 .x2) (dstOff + 32) = okmSoFar ++ tNext) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s₁
      (StateLoopX img.base infoPtr info.length okmLen tNext (okmSoFar ++ tNext) 2 16 (dstOff + 32) s₀) := by
  have hrun := hc1.status
  have hsp := hc1.sp_eq
  have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq
  have hx20 := hc1.x20_eq
  have hm16_1 : s₁.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw1_esp : s₁.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hc1.frame
  iterate 6 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc₁],
    ExpandCommonX.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx21],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · simp only [mem_setMem]
    exact readBytes_32_esp_32_of_208 ht_208
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) (dstOff + 32) :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by omega, by have := hpre.okm_len; bv_omega⟩
    dsimp only [mem_setMem]
    exact readBytes_eq_of_agreesOutside_esp s₀ s₁.mem 32#64 32 hd2 (by prove_agrees_esp)
      (by have := hpre.okm_len; omega) hokm_next

theorem iter_d_continue_x_runsTo
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    {prk info tPrev okmSoFar tNext : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hi : i = 1)
    (hdst : dstOff + 32 ≤ okmLen)
    (htNext : tNext = hmacWith F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]))
    (hkf : s₀.mem.KeepsFrozen s.mem)
    (hsym : s.symtab = s₀.symtab)
    (hx : StateLoopFinX img.base F prk info tPrev okmSoFar infoPtr okmLen i 48 dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateLoopX img.base infoPtr info.length okmLen tNext (okmSoFar ++ tNext) (i + 1) 16 (dstOff + 32) s₀) := by
  subst hi
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [htNext, length_hmacWith]
  clear htNext
  refine RunsToE.trans_full (Extract.RunsTo.toE (iter_d_head_x_runsTo hx))
    fun s_mc h_mc hkf_mc hsym_mc => ?_
  rcases h_mc with ⟨hpc_mc, hstat_mc, hsp_mc, hlr_mc, hx0_mc, hx1_mc, hx2_mc,
    hx19_mc, hx20_mc, hx21_mc, hx22_mc, hx23_mc, hx24_mc, hx26_mc, hx27_mc, hx28_mc, hx29_mc, hmem_mc⟩
  have hrw_stk : s_mc.mem.RW (s₀.sp - 17024#64) 17024 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_stkX hpre hx.common.frame
  have hrw_esp : s_mc.mem.RW (esp s₀) 496 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_esp hpre hx.common.frame
  have hrw_x2 : s_mc.mem.RW (s₀.readReg64 .x2) okmLen := by
    rw [hmem_mc]; exact ExpandFrameX.rw_x2 hpre hx.common.frame
  have hrw_dst : s_mc.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hrw_src : s_mc.mem.RW (esp s₀ + 208#64) 32 := hrw_esp.sub (by bv_omega)
  have hrw_ext : s_mc.mem.RW (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change s_mc.mem.RW (esp s₀ - 16384#64) 16384
    exact hrw_stk.sub (by unfold esp; bv_omega)
  have hd_dst_src : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (esp s₀ + 208#64) 32 :=
    (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
      ⟨by decide, by unfold esp; bv_omega⟩
  have hd_dst_ext : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) 32 (esp s₀ - 16384#64) 16384
    exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ - 16384#64)
      ⟨by decide, by unfold esp; bv_omega⟩
  have hd_src_ext : DisjointRegions (esp s₀ + 208#64) 32
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ - 16384#64) 16384
    unfold DisjointRegions; bv_omega
  have hc_mc : ExpandCommonX infoPtr info.length okmLen s₀ s_mc :=
    ⟨hstat_mc, hsp_mc, hx29_mc, hx27_mc, hx20_mc,
     by rw [hmem_mc]; exact hx.common.m8_eq,
     by rw [hmem_mc]; exact hx.common.m16_eq,
     by rw [hmem_mc]; exact hx.common.saved,
     by rw [hmem_mc]; exact hx.common.frame⟩
  have hmc := memcpy_subroutine_runsTo hMemcpy
    (bs := tNext)
    ((hpre.frozen.of_keepsFrozen hkf).of_keepsFrozen hkf_mc)
    (hsym_mc.trans (hsym.trans hpre.symtab_eq))
    hpc_mc hstat_mc hx0_mc hx1_mc
    (by rw [hx2_mc, ht_len]; rfl)
    (by rw [ht_len, hmem_mc]; exact ht_208)
    (by rw [ht_len]; exact hrw_dst)
    (by rw [ht_len]; exact hrw_src)
    hrw_ext
    (by rw [ht_len]; exact hd_dst_src)
    (by rw [ht_len]; exact hd_dst_ext)
    (by rw [ht_len]; exact hd_src_ext)
    (by rw [hsp_mc]; exact esp_aligned hpre.sp_aligned)
  refine hmc.trans fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, hsrc₁, hfr_mc⟩
  rw [hsp_mc, ht_len] at hfr_mc
  rw [ht_len] at hdst₁ hsrc₁
  have hoff_lt : dstOff < 2 ^ 64 := by have := hpre.okm_len; omega
  have hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁ :=
    ExpandCommonX.of_memcpy_x2_frame hpre hc_mc
      ⟨by decide, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]; exact hdst⟩
      hstat₁ hcc₁ hfr_mc
  have hleft : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (hfr_mc.readBytes_eq (hrw_x2.sub (by have := hpre.okm_len; bv_omega)) (fun r hr => ?_)
        (by have := hpre.okm_len; omega)).trans (by rw [hmem_mc]; exact hx.okm_pre)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold DisjointRegions; have := hpre.okm_len; bv_omega
      · change DisjointRegions (esp s₀ - 16384#64) 16384 (s₀.readReg64 .x2) dstOff
        exact (hpre.disj_x2_stack.symm.sub_left (esp s₀ - 16384#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
  have hokm_next : s₁.mem.readBytes (s₀.readReg64 .x2) (dstOff + 32) = okmSoFar ++ tNext := by
    rw [Bytes.readBytes_add s₁.mem (s₀.readReg64 .x2) dstOff 32, hleft, hdst₁]
  exact Extract.RunsTo.toE (iter_d_continue_tail_x_runsTo hpre hdst (hpc₁.trans hlr_mc) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx19_mc)
    ((Extract.CallingConventionPreserved.x21 hcc₁).trans hx21_mc)
    ((CallingConventionPreserved.x24 hcc₁).trans hx24_mc)
    ((CallingConventionPreserved.x26 hcc₁).trans hx26_mc)
    ((CallingConventionPreserved.x28 hcc₁).trans hx28_mc)
    hsrc₁ hokm_next)

theorem iter_d_done_tail_x_runsTo
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i dstOff rem : ℕ} {s₀ s₁ : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hpc₁ : s₁.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" + 688))
    (hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁)
    (hx19 : s₁.readReg64 .x19 = BitVec.ofNat 64 i)
    (hx21 : s₁.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + rem))
    (hx26 : s₁.readReg64 .x26 = 0#64)
    (hokm_done : s₁.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand F prk info okmLen) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s₁
      (StateDoneX img.base F prk info infoPtr okmLen s₀) := by
  have hrun := hc1.status
  have hsp := hc1.sp_eq
  have hx29 := hc1.x29_eq
  have hx27 := hc1.x27_eq
  have hx20 := hc1.x20_eq
  have hm16_1 : s₁.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw1_esp : s₁.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hc1.frame
  iterate 6 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc₁],
    ExpandCommonX.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    ?_⟩
  have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) okmLen :=
    hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64) ⟨by decide, by unfold esp; bv_omega⟩
  dsimp only [mem_setMem]
  exact readBytes_eq_of_agreesOutside_esp s₀ s₁.mem 32#64 32 hd2 (by prove_agrees_esp)
    (by have := hpre.okm_len; omega) hokm_done

theorem iter_d_done_x_runsTo
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 16)
    (hdst : dstOff + rem = okmLen)
    (hokm : okmSoFar ++ (hmacWith F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).take rem =
              hkdfExpand F prk info okmLen)
    (hkf : s₀.mem.KeepsFrozen s.mem)
    (hsym : s.symtab = s₀.symtab)
    (hx : StateLoopFinX img.base F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s
      (StateDoneX img.base F prk info infoPtr okmLen s₀) := by
  let tNext := hmacWith F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])
  have hmin : min rem 32 = rem := by rcases hrem with rfl | rfl <;> rfl
  have hrem_pos : 0 < rem := by rcases hrem with rfl | rfl <;> decide
  have htake_len : (tNext.take rem).length = rem := by
    rw [List.length_take, length_hmacWith]; omega
  have hread_rem : s.mem.readBytes (esp s₀ + 208#64) rem = tNext.take rem := by
    have hslice := Bytes.readBytes_slice_of_readBytes_eq s.mem (esp s₀ + 208#64) tNext
      (by rw [length_hmacWith]; exact hx.t_208) 0 rem (by rw [length_hmacWith]; omega)
    simpa using hslice
  refine RunsToE.trans_full (Extract.RunsTo.toE (iter_d_head_x_runsTo hx))
    fun s_mc h_mc hkf_mc hsym_mc => ?_
  rcases h_mc with ⟨hpc_mc, hstat_mc, hsp_mc, hlr_mc, hx0_mc, hx1_mc, hx2_mc,
    hx19_mc, hx20_mc, hx21_mc, _, _, _, hx26_mc, hx27_mc, _, hx29_mc, hmem_mc⟩
  rw [hmin] at hx2_mc hx21_mc
  rw [hmin, Nat.sub_self] at hx26_mc
  have hrw_stk : s_mc.mem.RW (s₀.sp - 17024#64) 17024 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_stkX hpre hx.common.frame
  have hrw_esp : s_mc.mem.RW (esp s₀) 496 := by
    rw [hmem_mc]; exact ExpandFrameX.rw_esp hpre hx.common.frame
  have hrw_x2 : s_mc.mem.RW (s₀.readReg64 .x2) okmLen := by
    rw [hmem_mc]; exact ExpandFrameX.rw_x2 hpre hx.common.frame
  have hrw_dst : s_mc.mem.RW (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem :=
    hrw_x2.sub (by have := hpre.okm_len; bv_omega)
  have hrw_src : s_mc.mem.RW (esp s₀ + 208#64) rem := hrw_esp.sub (by bv_omega)
  have hrw_ext : s_mc.mem.RW (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change s_mc.mem.RW (esp s₀ - 16384#64) 16384
    exact hrw_stk.sub (by unfold esp; bv_omega)
  have hd_dst_src : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem (esp s₀ + 208#64) rem :=
    (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨hrem_pos, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ + 208#64)
      ⟨hrem_pos, by unfold esp; bv_omega⟩
  have hd_dst_ext : DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff) rem (esp s₀ - 16384#64) 16384
    exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff)
      ⟨hrem_pos, by have := hpre.okm_len; bv_omega⟩).sub_right (esp s₀ - 16384#64)
      ⟨by decide, by unfold esp; bv_omega⟩
  have hd_src_ext : DisjointRegions (esp s₀ + 208#64) rem
      (s_mc.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_mc]
    change DisjointRegions (esp s₀ + 208#64) rem (esp s₀ - 16384#64) 16384
    unfold DisjointRegions; bv_omega
  have hc_mc : ExpandCommonX infoPtr info.length okmLen s₀ s_mc :=
    ⟨hstat_mc, hsp_mc, hx29_mc, hx27_mc, hx20_mc,
     by rw [hmem_mc]; exact hx.common.m8_eq,
     by rw [hmem_mc]; exact hx.common.m16_eq,
     by rw [hmem_mc]; exact hx.common.saved,
     by rw [hmem_mc]; exact hx.common.frame⟩
  have hmc := memcpy_subroutine_runsTo hMemcpy
    (bs := tNext.take rem)
    ((hpre.frozen.of_keepsFrozen hkf).of_keepsFrozen hkf_mc)
    (hsym_mc.trans (hsym.trans hpre.symtab_eq))
    hpc_mc hstat_mc hx0_mc hx1_mc
    (by rw [hx2_mc, htake_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    (by rw [htake_len, hmem_mc]; exact hread_rem)
    (by rw [htake_len]; exact hrw_dst)
    (by rw [htake_len]; exact hrw_src)
    hrw_ext
    (by rw [htake_len]; exact hd_dst_src)
    (by rw [htake_len]; exact hd_dst_ext)
    (by rw [htake_len]; exact hd_src_ext)
    (by rw [hsp_mc]; exact esp_aligned hpre.sp_aligned)
  refine hmc.trans fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, _, hfr_mc⟩
  rw [hsp_mc, htake_len] at hfr_mc
  rw [htake_len] at hdst₁
  have hoff_lt : dstOff < 2 ^ 64 := by have := hpre.okm_len; omega
  have hc1 : ExpandCommonX infoPtr info.length okmLen s₀ s₁ :=
    ExpandCommonX.of_memcpy_x2_frame hpre hc_mc
      ⟨hrem_pos, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]; omega⟩
      hstat₁ hcc₁ hfr_mc
  have hleft : s₁.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (hfr_mc.readBytes_eq (hrw_x2.sub (by have := hpre.okm_len; bv_omega)) (fun r hr => ?_)
        (by have := hpre.okm_len; omega)).trans (by rw [hmem_mc]; exact hx.okm_pre)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold DisjointRegions; have := hpre.okm_len; bv_omega
      · change DisjointRegions (esp s₀ - 16384#64) 16384 (s₀.readReg64 .x2) dstOff
        exact (hpre.disj_x2_stack.symm.sub_left (esp s₀ - 16384#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by have := hpre.okm_len; bv_omega⟩
  have hokm_done : s₁.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand F prk info okmLen := by
    rw [← hdst, Bytes.readBytes_add s₁.mem (s₀.readReg64 .x2) dstOff rem, hleft, hdst₁, hokm, hdst]
  exact Extract.RunsTo.toE (iter_d_done_tail_x_runsTo hpre (hpc₁.trans hlr_mc) hc1
    ((Extract.CallingConventionPreserved.x19 hcc₁).trans hx19_mc)
    ((Extract.CallingConventionPreserved.x21 hcc₁).trans hx21_mc)
    ((CallingConventionPreserved.x26 hcc₁).trans hx26_mc)
    hokm_done)

theorem iter_to_fin_from_s0_x_runsTo
    (hRO : MemcpyROContract img ext)
    (hFin : FinalizeFixedOkExt' img C ext)
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ : State}
    (hpre : ExpandPreX img C.F prk info infoPtr okmLen s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hloop : RunsToE (tripleRatchetProgAtExt img.base ext) s₀
      (StateLoopX img.base infoPtr info.length okmLen tPrev okmSoFar i rem dstOff s₀)) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀
      (StateLoopFinX img.base C.F prk info tPrev okmSoFar infoPtr okmLen i rem dstOff s₀) := by
  have h1 := hloop.trans fun s hs => Extract.RunsTo.toE (iter_a1_x_runsTo hpre hrem hdst hs)
  have h2 := h1.trans fun s hs => Extract.RunsTo.toE (iter_a2_x_runsTo hpre ht_len hdst hs)
  have h3 := RunsToE.trans_full h2 fun s hs hkf hsym => iter_b_x_runsTo hRO hpre ht_len hi hdst hkf hsym hs
  have h4 := h3.trans fun s hs => Extract.RunsTo.toE (iter_c_x_runsTo hpre hrem hdst hs)
  exact RunsToE.trans_full h4 fun s hs hkf hsym => iter_fin_x_runsTo hFin hpre ht_len hdst hkf hsym hs

theorem epilogue_x_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State}
    (hpre : ExpandPreX img F prk info infoPtr okmLen s₀)
    (hx : StateDoneX img.base F prk info infoPtr okmLen s₀ s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s
      (ExpandPostX F prk info infoPtr okmLen s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := ExpandFrameX.rw_esp hpre hx.common.frame
  rcases hx.common.saved with ⟨m400, m408, m416, m424, m432, m440, m448, m456, m464, m472, m480, m488⟩
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl, hrun, ⟨(esp_eq_add s₀).symm, ?_⟩, hx.okm_all, hx.common.frame⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Full `RunsToE` contract of `expand_multi_info` on `tripleRatchetProgAtExt img.base ext`
for both `okmLen = 64` (2 blocks) and `okmLen = 80` (3 blocks) at `17024` B stack. -/
theorem expand_multi_info_runsTo_ext_x
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    (hRO : MemcpyROContract img ext)
    (hFin : FinalizeFixedOkExt' img C ext)
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ}
    {s₀ : State}
    (hpre : ExpandPreX img C.F prk info infoPtr okmLen s₀) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀
      (ExpandPostX C.F prk info infoPtr okmLen s₀) := by
  have h0 := Extract.RunsTo.toE (seg0_x_runsTo (ext := ext) hpre)
  have h1 := h0.trans fun s hs => Extract.RunsTo.toE (seg1_x_runsTo hpre hs)
  have h2a := RunsToE.trans_full h1 fun s hs hkf hsym => seg2a_x_runsTo hRO hpre hkf hsym hs
  have h2b := h2a.trans fun s hs => Extract.RunsTo.toE (seg2b_x_runsTo hpre hs)
  have hfin1 := RunsToE.trans_full h2b fun s hs hkf hsym => fin1_x_runsTo hFin hpre hkf hsym hs
  have hloop1 := RunsToE.trans_full hfin1 fun s hs hkf hsym => seg3_x_runsTo hMemcpy hpre hkf hsym hs
  rcases hpre.okm_len with rfl | rfl
  · -- Case `okmLen = 64`: 1 loop iteration (`i = 1, rem = 32, dstOff = 32`)
    have hlf1 := iter_to_fin_from_s0_x_runsTo hRO hFin hpre
      (t1_length C.F prk info) (Or.inl rfl) (Or.inl rfl) (by decide) hloop1
    have hokm64 : t1 C.F prk info ++ (hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8])).take 32 =
        hkdfExpand C.F prk info 64 := by
      rw [show hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8]) = t2 C.F prk info from rfl,
          List.take_of_length_le (by simp), hkdfExpand_64_eq]
    have hdone := RunsToE.trans_full hlf1 fun s hs hkf hsym =>
      iter_d_done_x_runsTo hMemcpy hpre (Or.inl rfl) (Or.inl rfl) rfl hokm64 hkf hsym hs
    exact hdone.trans fun s hs => Extract.RunsTo.toE (epilogue_x_runsTo hpre hs)
  · -- Case `okmLen = 80`: 2 loop iterations (`i = 1, rem = 48, dstOff = 32` then `i = 2, rem = 16, dstOff = 64`)
    have hlf1 := iter_to_fin_from_s0_x_runsTo hRO hFin hpre
      (t1_length C.F prk info) (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide) hloop1
    have hloop2 := RunsToE.trans_full hlf1 fun s hs hkf hsym =>
      iter_d_continue_x_runsTo (tNext := t2 C.F prk info) hMemcpy hpre rfl (by decide) rfl hkf hsym hs
    have hlf2 := iter_to_fin_from_s0_x_runsTo hRO hFin hpre
      (t2_length C.F prk info) (Or.inr rfl) (Or.inr (Or.inr rfl)) (by decide) hloop2
    have hokm80 : (t1 C.F prk info ++ t2 C.F prk info) ++
        (hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8])).take 16 =
        hkdfExpand C.F prk info 80 := by
      rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
          hkdfExpand_80_eq]
    have hdone := RunsToE.trans_full hlf2 fun s hs hkf hsym =>
      iter_d_done_x_runsTo hMemcpy hpre (Or.inr rfl) (Or.inr rfl) rfl hokm80 hkf hsym hs
    exact hdone.trans fun s hs => Extract.RunsTo.toE (epilogue_x_runsTo hpre hs)

end AssemblyX

end HkdfExt.ExpandExt

open Expand HkdfExt.ExpandExt in
theorem expand_multi_info_ok_ext'_of_memcpy {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    (hRO : HkdfExt.ExpandExt.MemcpyROContract img ext)
    (hFin : FinalizeFixedOkExt' img C ext) :
    ExpandMultiInfoOkExt' img C ext := by
  unfold ExpandMultiInfoOkExt'
  rw [trExt_fnAddr_expandMultiInfo]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, expandMultiInfoSpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrz0, hsym0⟩, ⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, hokm_len⟩, hsep⟩
  change s0.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      memRegion (s0.sp - 17024#64) 17024) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt C.F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) (BitVec.ofNat 64 x.info.length)
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = BitVec.ofNat 64 x.info.length) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (s0.sp - 17024#64) 17024
  let R_inv : SepProp :=
    hmacCoreAt C.F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗ R
  have hsep_okm_stk_ro : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗ ((x.infoA ↦ᵣ x.info) ∗ R_inv)) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 17024#64) 17024 ∗
      (memRegion x.okmA x.okmLen ∗ ((x.infoA ↦ᵣ x.info) ∗ R_inv)) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion x.okmA x.okmLen ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 17024#64) 17024 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 17024#64) 17024 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion (s0.sp - 17024#64) 17024 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hokm_pos : 0 < x.okmLen := by omega
  have h_exp_pre : ExpandPreX img C.F x.prk x.info x.infoA x.okmLen s0 :=
    { pc_eq := hpc
      status := hrun
      frozen := hfrz0
      symtab_eq := hsym0
      x3_eq := hx3
      prk_le := hprk_le
      info_lt := hinfo_lt
      okm_len := hokm_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := hro_info.read hsep_info_stk
      read_info := fun a ha => ⟨hro_info.perm_r hsep_info_stk ha, hro_info.isLazyFree_false hsep_info_stk ha⟩
      read_x0 := by rw [hx0]; exact Memory.RW.readable (fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha)
      read_x1 := by rw [hx1]; exact Memory.RW.readable (fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha)
      rw_x2 := by rw [hx2]; exact fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk_ro ha
      rw_stack := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
      disj_x2_stack := by rw [hx2]; exact hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk_ro
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) hokm_pos hsep_hm_okm
      disj_x1_stack := by rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) hokm_pos hsep_hdr_okm
      out_info_stk := ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by rw [hx2]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  refine (expand_multi_info_runsTo_ext_x hMemcpy hRO hFin h_exp_pre).to_reaches_pc
    fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [Spec.inImage, expandMultiInfoSpecExt]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrameX at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info x.okmLen).length = x.okmLen := by
    rcases hokm_len with h64 | h80
    · rw [h64, Expand.hkdfExpand_64_eq]
      simp [Expand.t1_length, Expand.t2_length]
    · rw [h80, Expand.hkdfExpand_80_eq]
      simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      (memRegion (s0.sp - 17024#64) 17024 ∗ ((x.infoA ↦ᵣ x.info) ∗ R_inv)) :=
    S2FrameRO.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hro_info hsep_okm_stk_ro hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      memRegion (s0.sp - 17024#64) 17024) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

theorem expand_multi_info_ok_ext' (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State))
    (hHkdf : HkdfContractsExt img C.F ext) :
    ExpandMultiInfoOkExt' img C ext :=
  expand_multi_info_ok_ext'_of_memcpy hHkdf.memcpy hHkdf.memcpyRO
    (finalize_fixed_ok_ext' img C ext hHkdf)

/-- Relocatable `[LibsignalPlacement]` contract predicate for `expand_multi_info`. -/
def ExpandMultiInfoPlacedOk [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (blkPl_53).base
    (withLsCodeLoaded lsmpl (expandMultiInfoSpec C.F))

open Expand in
theorem expand_multi_info_placed_ok [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    ExpandMultiInfoPlacedOk C H := by
  unfold ExpandMultiInfoPlacedOk
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cl hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre_cl
  dsimp only [expandMultiInfoSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, hokm_len⟩, hsep⟩
  change s0.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      memRegion (s0.sp - 640#64) 640) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt C.F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) (BitVec.ofNat 64 x.info.length)
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = BitVec.ofNat 64 x.info.length) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (s0.sp - 640#64) 640
  let R_inv : SepProp :=
    hmacCoreAt C.F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (x.infoA ↦ᵣ x.info) ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗ (memRegion (s0.sp - 640#64) 640 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 640#64) 640 ∗ (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion x.okmA x.okmLen ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hokm_pos : 0 < x.okmLen := by omega
  have h_exp_pre : ExpandPre expPlacedFakeB C.F x.prk x.info x.infoA x.okmLen s0 :=
    { pc_eq := by rw [expPlacedFakeB_off_0]; exact hpc
      status := hrun
      x3_eq := hx3
      prk_le := hprk_le
      info_lt := hinfo_lt
      okm_len := hokm_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := hro_info.read hsep_info_stk
      read_x0 := by rw [hx0]; exact Memory.RW.readable (fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha)
      read_x1 := by rw [hx1]; exact Memory.RW.readable (fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha)
      rw_x2 := by rw [hx2]; exact fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
      rw_stack := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
      disj_x2_stack := by rw [hx2]; exact hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) hokm_pos hsep_hm_okm
      disj_x1_stack := by rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) hokm_pos hsep_hdr_okm
      out_info_stk := ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by rw [hx2]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  refine (expand_multi_info_placed_runsTo (H := H) hcl h_exp_pre).to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [withLsCodeLoaded, expandMultiInfoSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrame at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info x.okmLen).length = x.okmLen := by
    rcases hokm_len with h64 | h80
    · rw [h64, Expand.hkdfExpand_64_eq]
      simp [Expand.t1_length, Expand.t2_length]
    · rw [h80, Expand.hkdfExpand_80_eq]
      simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      (memRegion (s0.sp - 640#64) 640 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      memRegion (s0.sp - 640#64) 640) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

end CryptoVerification.LibsignalTripleRatchet
