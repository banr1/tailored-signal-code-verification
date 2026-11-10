/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymA
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchSome
public meta import Lean
public meta import LibsignalBinary.Proofs.Common.InImageKit
public import LibsignalBinary.Proofs.RecordCodecs.Deps
import all Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable Branch & Callee Helpers for `save_identity::{closure#0}`

Provides `SepWPp` callee combinators, relocatable `PublicKey::serialize` (Block 205) transfer, and
shared epilogue and branch lemmas on Block `565` (`lsProg_565 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] calleeSavedVRegs_writeVReg128_0
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496

/-! ## 1. `SepWPp` Callee Combinators under `StoreKit.LibsignalCodeRoLoaded` -/

theorem ispoll_call_panicking_raw_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (x : α) (F : SepProp) {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hinv : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic x s sm ∗ R') → allocFailedIn s sm ∧ s.trace <+: sm.trace)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_conseq hpre ?_
  intro R hm hL
  have hm_pre : s.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) :=
    satisfies_lscro_pre hinv (by rwa [sepConj_assoc] at hm)
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm_pre hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpans, hpost⟩ |
    ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpcm hrunm hspm hcsm
      (hinv.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using hpan_imp sm (F ∗ R) hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpans, _, hpost, hpan sm _ halloc0⟩)⟩
  · exact (hexit_imp code sm (F ∗ R) hpost).elim
  · exact (hoom_imp sm (F ∗ R) hpost).elim

private theorem memRegion_33_cells_p (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ b0 : BitVec 8,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u3) ∗ ((a + 9#64) ↦₆₄ u2) ∗
        ((a + 17#64) ↦₆₄ u1) ∗ ((a + 25#64) ↦₆₄ u0)) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 32) (b' := a + 1#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 1#64) (n := 8) (k := 24) (b' := a + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 9#64) (n := 8) (k := 16) (b' := a + 17#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 17#64) (n := 8) (k := 8) (b' := a + 25#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_one a,
    ProofLib.memRegion_eight (a + 1#64),
    ProofLib.memRegion_eight (a + 9#64),
    ProofLib.memRegion_eight (a + 17#64),
    ProofLib.memRegion_eight (a + 25#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem sepWPp_pure_mid_p {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

/-- Relocatable `<PublicKey>::serialize` (Block `205`) under `AllocContractsXCliPlaced` and
`CliPanicHooksPlaced`, transferred to any caller block `i < 619`. -/
theorem publicKeySerialize_lscro_of_cli [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H]
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (StoreKit.withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX A)) := by
  have h205 : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (StoreKit.withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX A)) := by
    have hshim := shim_lscro_of_cli (callerProg := (blkPC_205).rebase (blkPl_205).base H)
      hC (stk := extHookStack) (by decide) (by decide) (by decide)
    have halloc := alloc_lscro_of_cli (callerProg := (blkPC_205).rebase (blkPl_205).base H)
      hC (by decide)
    have hpanic : ((blkPC_205).rebase (blkPl_205).base H).externAt? (lsρ lsHandleErrorSym) =
        some Rust.panicked :=
      ls_panicAt_of_cliPanic hpan
    have hshim_sym : lsRustNoAllocShimSym = lsRustNoAllocShimSymCli := rfl
    have halloc_sym : lsRustAllocSym = lsRustAllocSymCli := rfl
    rw [← hshim_sym] at hshim
    rw [← halloc_sym] at halloc
    simp only [StoreKit.withLsCodeRoLoaded, publicKeySerializeSpecX,
      PublicKey.serialize, boxU8Buf, ProofLib.stackAt_split_cells _ extHookStack 4 (by decide)]
    cells_unfold
    wpp_init x s0
    obtain ⟨self, pk⟩ := x
    have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
    dsimp only at *
    obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
      exists_unpack64_of_length_32 (List.Vector.toList_length pk.bytes)
    rw [hpk_cells self]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
    apply StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustNoAllocShimSym) hcrl0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    refine ispoll_call_panicking_raw_placed (spec := withStack sessionShimSpec extHookStack)
      (ret_pc := (blkPl_205).base + bv% (20))
      hshim () ?_
      (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_goal)
      hcrl1
      (fun sf _ hp hm => allowPanic_panicked hp hm)
      (by
        dsimp only [withStack, sessionShimSpec]
        simp only [wp_norm, arm64_norm, emp_sepConj]
        ispoll_close_frame)
      (fun _ _ h => (not_satisfies_false_sepConj h).elim)
      (fun _ _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ h => (not_satisfies_false_sepConj h)) ?_
    intro sf hpc_s hrun_s hsp_s hcs_s hcrl2
    simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm]
      at hpc_s hsp_s hcs_s
    rcases hcs_s with ⟨hx19_s, _, _, _, _, _, _, _, _, _, _, hvregs_s⟩
    have hsp_al_s : sf.spAligned = true := by
      simp only [State.spAligned, hsp_s]; wp_norm_lhs
    dsimp only [withStack, sessionShimSpec]
    conv => arg 4; simp only [hsp_s, emp_sepConj, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_s => ?_
    apply StoreKit.sepWPp_seq_lscro (mid := lsρ lsRustAllocSym) hcrl2
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl3
    refine ispoll_call_panicking_raw_placed (spec := rustAllocSpecWithStack A extHookStack)
      (ret_pc := (blkPl_205).base + bv% (32))
      halloc (33, 1)
      ((self ↦₆₄ w0) ∗ ((self + 8#64) ↦₆₄ w1) ∗ ((self + 16#64) ↦₆₄ w2) ∗
        ((self + 24#64) ↦₆₄ w3) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ v_stk_3))
      (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, htr_s])
      hcrl3
      (fun sf_p _ hp hm => allowPanic_panicked hp hm)
      (by
        dsimp only [rustAllocSpecWithStack]
        simp only [wp_norm, arm64_norm, hsp_s, sepConj_assoc]
        exact Entails.pure_right hlay (Entails.of_eq (by ac_rfl)))
      (fun _ _ h => (not_satisfies_false_sepConj h).elim)
      (fun _ _ _ h => not_satisfies_false_sepConj h)
      (fun _ _ h => not_satisfies_false_sepConj h) ?_
    intro sf1 hpc1 hrun1 hsp1 hcs1 _hcrl4
    simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
      hsp_s, hx19_s, hvregs_s] at hpc1 hsp1 hcs1
    rcases hcs1 with ⟨hx19_1, _, _, _, _, _, _, _, _, _, _, hvregs_1⟩
    have hsp_al1 : sf1.spAligned = true := by
      simp only [State.spAligned, hsp1, ← hsp_s]; exact hsp_al_s
    dsimp only [rustAllocSpecWithStack]
    by_cases hoom : sf1.readReg64 (Reg.gpr 0#5) = 0
    · simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_mid_p fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm, wp_norm] using hpanic) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, htrace, htr_s])) hm
    · simp only [hoom, ite_false, memRegion_33_cells_p, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
        SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
        SepWPp.exists_elim fun b0 => ?_
      refine sepWPp_pure_mid_p fun ⟨hmod, htrace⟩ => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      simp only [List.length_cons, List.Vector.toList_length,
        List.cons_ne_nil, ite_false, djbType,
        pointsToBytes_cons, hpk_cells,
        BitVec.add_assoc, BitVec.reduceAdd]
      wp_done
  exact ls_transfer_lscro (callerProg := callerProg) (j := 205) h205 hi (by decide) (by decide)

theorem ispoll_call_dirGet_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirGetSpecPlaced rd pathOk A getStk))
    (xg : DirGetGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace) →
      SepWPp prog ret sm
        ((getResultAt A xg.ret gr ∗ dirAt A xg.self xg.dir ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun gr => SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr hpcm hrunm hspm hcsm hinvm hgr)

theorem ispoll_call_decode_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (StoreKit.withLsCodeRoLoaded lsmpl (RecordCodecsBinary.identityKeyDecodeRawSpec A)))
    (xg : DecodeGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.bytesA)
    (hx1 : (s.readReg64 .x1).toNat = xg.bytes.length)
    (hx8 : s.readReg64 .x8 = xg.ret)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((xg.bytesA ↦ₛ xg.bytes) ∗ memRegion xg.ret 48 ∗ FromRecordCallees.lsLogOff ∗
      stackAt s.sp 0x60) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((identityKeyResultAt A xg.ret (decodeIdentityKey xg.bytes) ∗
          (xg.bytesA ↦ₛ xg.bytes) ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp 0x60) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hlog : FromRecordCallees.lsLogOff = lsLogOff := rfl
  refine ispoll_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    rw [hlog]
    simp only [identityKeyDecodeRawSpec, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx8⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [identityKeyDecodeRawSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [identityKeyDecodeRawSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [identityKeyDecodeRawSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [identityKeyDecodeRawSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [← hlog]
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

theorem ispoll_call_publicKeyEq_placed [LibsignalPlacement] {prog : Program}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (StoreKit.withLsCodeRoLoaded lsmpl Getters.publicKeyEqSpec))
    (p1 : BitVec 64) (pk1 : PublicKey) (p2 : BitVec 64) (pk2 : PublicKey) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = p1) (hx1 : s.readReg64 .x1 = p2)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗ stackAt s.sp 64) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) → sm.trace = s.trace →
      SepWPp prog ret sm
        (((p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗ stackAt s.sp 64) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw_placed hcall (p1, pk1, p2, pk2, s.sp) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [Getters.publicKeyEqSpec, ← stackAt_64_eq_publicKeyEq_frames s.sp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, trivial⟩ (Entails.refl _)
  · intro sm R' hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [Getters.publicKeyEqSpec, ← stackAt_64_eq_publicKeyEq_frames s.sp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hx0m htrm)

theorem ispoll_call_serialize_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (StoreKit.withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX A)))
    (keyA : BitVec 64) (pk : PublicKey) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = keyA)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((keyA ↦ₛ pk.bytes.toList) ∗ A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = 33#64 → sm.trace = s.trace →
      SepWPp prog ret sm
        ((boxU8Buf A (sm.readReg64 .x0) pk.serialize ∗
          (keyA ↦ₛ pk.bytes.toList) ∗ A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw_placed hcall ⟨keyA, pk⟩ F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [publicKeySerializeSpecX, sepConj_assoc]
    exact Entails.pure_right hx0 (Entails.refl _)
  · intro sm R' hpost
    simp only [publicKeySerializeSpecX, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [publicKeySerializeSpecX] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [publicKeySerializeSpecX] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [publicKeySerializeSpecX, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1m, htrm⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hx1m htrm)

theorem ispoll_call_dirPutStr_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc} {putStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirPutStrSpecPlaced A putStk))
    (xg : DirPutStrGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.self) (hx1 : s.readReg64 .x1 = xg.nameA)
    (hx2 : (s.readReg64 .x2).toNat = xg.name.length) (hx3 : s.readReg64 .x3 = xg.bytesV)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.changed.length < 2 ^ 32)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      vecU8 A xg.bytesV xg.bytes ∗ stackAt s.sp putStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((dirAt A xg.self (xg.dir.put xg.name xg.bytes) ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          memRegion xg.bytesV 24 ∗ stackAt s.sp putStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

theorem ispoll_call_dealloc_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (StoreKit.withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack)))
    (ptr : BitVec 64) (size : Nat) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = 1) (hlay : LayoutOk size 1)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ A.live ptr size 1 ∗ memRegion ptr size ∗ stackAt s.sp extHookStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      SepWPp prog ret sm ((A.pool ∗ stackAt s.sp extHookStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ispoll_call_panicking_raw_placed hcall (ptr, size, 1) F
    hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [rustDeallocExternSpecWithStack, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [rustDeallocExternSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [rustDeallocExternSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [rustDeallocExternSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [rustDeallocExternSpecWithStack, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm htrm)

private theorem ispoll_onPanic_placed [LibsignalPlacement] {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    {x : IdPollGhost} {s0 sf : State} {P_f : SepProp}
    (hp : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    P_f ⊢ (idSavePollSpecPlaced rd pathOk A stk).onPanic x s0 sf := by
  dsimp only [idSavePollSpecPlaced, StoreKit.withLsCodeRoLoaded]
  exact Entails.pure_right hp (Entails.top_right fun _ => trivial)

/-! ## 2. Epilogue & Branch Helpers on Block `565` -/

theorem ispoll_epilogue_1bc_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} (x : IdPollGhost)
    (c1 c2 c3 c4 c5 c6 c7 : BitVec 8) (s16 : BitVec 64) (s24 : BitVec 8)
    (Rest : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_565).base + offEpilogue)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hq : ∀ sf : State,
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s.trace →
      Q sf (epilogueOut s0 x (s.readReg64 .x25)
        ((s.readReg64 .x26).truncate 32) ((s.readReg64 .x8).truncate 32)
        (s.readReg64 .x21) (s.readReg64 .x22)
        c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗ Rest)) :
    SepWP ((blkPC_565).rebase (blkPl_565).base H) (s0.readReg64 .lr) s
      (epiloguePre s0 x c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗ Rest) Q := by
  dsimp only [offEpilogue] at hpc
  conv =>
    arg 4
    unfold epiloguePre overlap7View1 idSaveBoxAt savedCalleeSlots
    rw [sret48_epilogue_split x.call.out]
    unfold overlap7View1
    simp only [wp_norm, arm64_norm, ispoll_sp_eqs, out_add_eqs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro o0; apply SepWP.exists_elim; intro o8
  apply SepWP.exists_elim; intro o12; apply SepWP.exists_elim; intro o16
  apply SepWP.exists_elim; intro o24; apply SepWP.exists_elim; intro o32
  apply SepWP.exists_elim; intro o40
  apply SepWP.exists_elim; intro b1; apply SepWP.exists_elim; intro b2
  apply SepWP.exists_elim; intro b3; apply SepWP.exists_elim; intro b4
  apply SepWP.exists_elim; intro b5; apply SepWP.exists_elim; intro b6
  apply SepWP.exists_elim; intro b7
  apply sepWP_step_to (mid := (blkPl_565).base + offEpiLdur11)
  dsimp only [offEpiLdur11]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have h7_sp :
      ((s0.sp - 0xc8#64) ↦₃₂ (c4 ++ c3 ++ c2 ++ c1)) ∗
        ((s0.sp - 0xc4#64) ↦₈ c5) ∗ ((s0.sp - 0xc3#64) ↦₁₆ (c7 ++ c6)) =
      ((s0.sp - 0xc8#64) ↦₁₆ (c2 ++ c1)) ∗
        ((s0.sp - 0xc6#64) ↦₈ c3) ∗ ((s0.sp - 0xc5#64) ↦₃₂ (c7 ++ c6 ++ c5 ++ c4)) := by
    have h7 := overlap7_realign (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7
    unfold overlap7View1 overlap7View2 at h7
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_sp
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWP_step_to (mid := (blkPl_565).base + offEpiStr44)
  dsimp only [offEpiStr44]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have h7_out :
      ((x.call.out + 41#64) ↦₃₂ (c4 ++ c3 ++ c2 ++ c1)) ∗
        ((x.call.out + 45#64) ↦₈ b5) ∗ ((x.call.out + 46#64) ↦₁₆ (b7 ++ b6)) =
      ((x.call.out + 41#64) ↦₁₆ (c2 ++ c1)) ∗
        ((x.call.out + 43#64) ↦₈ c3) ∗ ((x.call.out + 44#64) ↦₃₂ (b7 ++ b6 ++ b5 ++ c4)) := by
    have h7 := overlap7_realign (x.call.out + 41#64) c1 c2 c3 c4 b5 b6 b7
    unfold overlap7View1 overlap7View2 at h7
    simpa only [out_add_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_out
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine Eq.mpr (congrArg (Q _) ?_)
    (hq _ (by wp_norm_goal)
      (by simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs])
      (by wp_norm_goal))
  unfold epilogueOut overlap7View2 idSaveBoxAt savedCalleeSlots
  simp only [wp_norm, arm64_norm, ispoll_sp_eqs]
  ac_rfl

theorem ispoll_ok_tail_190_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hSer : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 205)
      (StoreKit.withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX A)))
    (hPut : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A putStk))
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost)
    (gr : Except Unit (List (BitVec 8))) (o : Option IdentityKey) (c : IdentityChange)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (hpc : s.pc = (blkPl_565).base + offOkTail)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx26 : (s.readReg64 .x26).truncate 32 = (if c == .replacedExisting then 1#32 else 0#32))
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hc : idSaveOf (.ok o) x.call.call.key = .ok c)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hgr : gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name)
    (hans : IdPeerAns gr (.ok o)) :
    SepWPp ((blkPC_565).rebase (blkPl_565).base H) (s0.readReg64 .lr) s
      (dirAt A (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        FromRecordCallees.lsLogOff ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        memRegion (s0.sp - 0xa0#64) 16 ∗
        memRegion (s0.sp - 0x90#64) 48 ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpecPlaced rd pathOk A stk).post x s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpecPlaced rd pathOk A stk).onPanic x s0 sf) := by
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    have : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
    unfold saveMinStk at this; omega
  have hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) →
      (P_f ⊢ (idSavePollSpecPlaced rd pathOk A stk).onPanic x s0 sf) :=
    fun _ _ hp => ispoll_onPanic_placed hp
  dsimp only [offOkTail] at hpc
  conv =>
    arg 4
    rw [protocolAddressAt_borrow A x.call.call.addr x.call.call.addrA]
    unfold idSaveBoxAt
    simp only [sepConj_assoc]
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 205) hinv
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_ser
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (serStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  refine ispoll_call_serialize_placed (ret_pc := (blkPl_565).base + offAfterSer) hSer
    x.call.call.keyA x.call.call.key.publicKey ?ispollF1
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_goal)
    hinv_ser
    (by wp_norm_goal) hpan ?ispollPre1 ?_
  case ispollPre1 => ispoll_close_frame
  intro sm1 hpc1 hrun1 hsp1 hcs1 hinv1 hx1_1 htr1
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp, htr, hx19, hx20, hx24, hx29, hvregs] at hpc1 hsp1 htr1 hx1_1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, _, hx26_1, _, _, hx29_1, hvregs_1⟩
  have hsp_al1 : sm1.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp1, ← hsp]
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp, hsp1]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (serStk_le_saveSubMax getStk putStk) hsub_hi).symm
  ispoll_rw_pre (slot90_split_vec24 s0.sp)
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v1
  apply SepWPp.exists_elim; intro v2
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 543) hinv1
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_put
  ispoll_fold_pre (boxU8Buf_to_vecU8_33 A s0.sp (sm1.readReg64 .x0) x.call.call.key)
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (putStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  have hx2_len : (BitVec.ofNat 64 x.call.call.addr.name.bytes.length).toNat =
      x.call.call.addr.name.bytes.length := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ispoll_call_dirPutStr_placed (ret_pc := (blkPl_565).base + offAfterPut) hPut
    { self := x.self + 0x28#64
      dir := x.peers
      nameRo := false
      nameA := x.call.call.addr.name.ptr
      name := x.call.call.addr.name.bytes
      bytesV := s0.sp - 0x90#64
      bytes := x.call.call.key.serialize } ?ispollF2
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_goal)
    hinv_put
    (by simp only [wp_norm, arm64_norm])
    (by wp_norm_goal)
    (by simp only [wp_norm, arm64_norm, hx2_len])
    (by wp_norm_goal) hnlen hclen hpan
    ?ispollPre2 ?_
  case ispollPre2 => ispoll_close_frame
  intro sm2 hpc2 hrun2 hsp2 hcs2 _hinv2 htr2
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx24_1, hx29_1, hvregs_1] at hpc2 hsp2 htr2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, _, _, hx26_2, _, _, _, hvregs_2⟩
  have hsp_al2 : sm2.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp2, ← hsp]
  have hmerge48 :
      (memRegion (s0.sp - 0x90#64) 24 ∗ memRegion (s0.sp - 0x78#64) 24) =
        memRegion (s0.sp - 0x90#64) 48 :=
    (ProofLib.memRegion_split' (b := s0.sp - 0x90#64) (n := 24) (k := 24)
      (b' := s0.sp - 0x78#64) rfl (by bv_omega) (by decide)).symm
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp, hsp1, hsp2]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (putStk_le_saveSubMax getStk putStk) hsub_hi).symm
  ispoll_rw_pre hmerge48
  let restPut : SepProp :=
    dirAt A (x.self + 0x28#64)
      (x.peers.put x.call.call.addr.name.bytes x.call.call.key.serialize) ∗
    protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
    (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
    FromRecordCallees.lsLogOff ∗ A.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
    stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
    memRegion (s0.sp - 0xd0#64) 8 ∗
    ((s0.sp - 0xc1#64) ↦₈ c15) ∗
    memRegion (s0.sp - 0xb7#64) 7 ∗
    ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
    ((s0.sp - 0xa8#64) ↦₈ s40) ∗
    memRegion (s0.sp - 0xa7#64) 7 ∗
    memRegion (s0.sp - 0xa0#64) 16 ∗
    memRegion (s0.sp - 0x90#64) 48
  refine sepWPp_conseq (P' := epiloguePre s0 x c1 c2 c3 c4 c5 c6 c7 s16 s24 ∗ restPut)
    (Entails.of_eq ?_) ?_
  · dsimp only [restPut]
    rw [protocolAddressAt_borrow A x.call.call.addr x.call.call.addrA]
    unfold epiloguePre idSaveBoxAt
    ac_rfl
  apply sepWPp_of_sepWP_final
  apply sepWP_step_to (mid := (blkPl_565).base + offEpilogue)
  dsimp only [offEpilogue]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ispoll_epilogue_1bc_placed (H := H) x
    c1 c2 c3 c4 c5 c6 c7 s16 s24 restPut
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, hvregs_2])
    (by wp_norm_goal) (by wp_norm_goal) ?_
  intro sf hspf hcsf htrf
  refine ⟨hspf, hcsf, ?_⟩
  have htr_eq : sf.trace = s0.trace := by simp only [wp_norm, arm64_norm, htr2] at htrf; exact htrf
  simp only [wp_norm, arm64_norm] at hx26
  conv =>
    lhs; arg 1
    simp only [wp_norm, arm64_norm, hx26_2, hx26_1, hx26]
  unfold epilogueOut
  refine Entails.trans (Entails.of_eq (by dsimp only [restPut]; ac_rfl :
    _ = ((x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((x.call.out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
          ((x.call.out + 12#64) ↦₃₂ (sm2.readReg64 (Reg.gpr 8#5)).truncate 32) ∗
          ((x.call.out + 16#64) ↦₆₄ sm2.readReg64 (Reg.gpr 21#5)) ∗
          ((x.call.out + 24#64) ↦₆₄ sm2.readReg64 (Reg.gpr 22#5)) ∗
          ((x.call.out + 32#64) ↦₆₄ s16) ∗
          ((x.call.out + 40#64) ↦₈ s24) ∗
          overlap7View2 (x.call.out + 41#64) c1 c2 c3 c4 c5 c6 c7) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
          stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
          memRegion (s0.sp - 0xd0#64) 8 ∗
          overlap7View2 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
          ((s0.sp - 0xc1#64) ↦₈ c15) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
          ((s0.sp - 0xb8#64) ↦₈ s24) ∗
          memRegion (s0.sp - 0xb7#64) 7 ∗
          ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
          ((s0.sp - 0xa8#64) ↦₈ s40) ∗
          memRegion (s0.sp - 0xa7#64) 7 ∗
          memRegion (s0.sp - 0xa0#64) 16 ∗
          memRegion (s0.sp - 0x90#64) 48 ∗
          savedCalleeSlots s0) ∗
        (dirAt A (x.self + 0x28#64)
          (x.peers.put x.call.call.addr.name.bytes x.call.call.key.serialize) ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          FromRecordCallees.lsLogOff ∗ A.pool))) ?_
  refine Entails.trans
    (sepConj_mono (epilogueOut_ok_reassemble A x.call.out c _ _ _ s16 s24 c1 c2 c3 c4 c5 c6 c7)
      (sepConj_mono_left (restore_savePollStack s0 hstk hhi c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40))) ?_
  dsimp only [idSavePollSpecPlaced, StoreKit.withLsCodeRoLoaded]
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_right gr (Entails.sepExists_right (.ok o) ?_)
  have hprop_ok :
      (gr = x.peers.get rd s0.fs.files x.call.call.addr.val.name ∧ sf.trace = s0.trace) ∧
      IdPeerAns gr (.ok o) :=
    ⟨⟨hgr, htr_eq⟩, hans⟩
  simp only [hc, idSavePeers, sepConj_assoc]
  exact Entails.pure_right hprop_ok (Entails.of_eq (by ac_rfl))

theorem ispoll_branch_err_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s48 s56w : BitVec 64)
    (hpc : s.pc = (blkPl_565).base + offAfterGet)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (herr_case : x.peers.get rd s0.fs.files x.call.call.addr.val.name = .error () ∧ s.trace = s0.trace) :
    SepWPp ((blkPC_565).rebase (blkPl_565).base H) (s0.readReg64 .lr) s
      (getResultAt A (s0.sp - 0x90#64) (.error ()) ∗
        dirAt A (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        FromRecordCallees.lsLogOff ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        ((s0.sp - 0xa0#64) ↦₆₄ s48) ∗
        ((s0.sp - 0x98#64) ↦₆₄ s56w) ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpecPlaced rd pathOk A stk).post x s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpecPlaced rd pathOk A stk).onPanic x s0 sf) := by
  dsimp only [offAfterGet] at hpc
  dsimp only [getResultAt, vecResultAt]
  conv =>
    arg 4
    rw [speAt_read_invalidState_unpack A s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.exists_elim; intro fnPtr
  apply sepWPp_of_sepWP_final
  let w5 : BitVec 64 := BitVec.ofNat 64 (utf8 "read").length
  apply sepWP_step_to (mid := (blkPl_565).base + offErrShuffle)
  dsimp only [offErrShuffle]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  ispoll_rw_pre (s48_split_byte7 s0.sp fnPtr w5)
  conv =>
    arg 4
    unfold overlap7View1
    simp only [ispoll_sp_eqs, sepConj_assoc]
  apply sepWP_step_to (mid := (blkPl_565).base + offErrLdr60)
  dsimp only [offErrLdr60]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have h7_97 :
      ((s0.sp - 0x97#64) ↦₃₂ (w5.extractLsb' 32 8 ++ w5.extractLsb' 24 8 ++ w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 0x93#64) ↦₈ w5.extractLsb' 40 8) ∗
        ((s0.sp - 0x92#64) ↦₁₆ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8)) =
      ((s0.sp - 0x97#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 0x95#64) ↦₈ w5.extractLsb' 24 8) ∗
        ((s0.sp - 0x94#64) ↦₃₂ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8 ++ w5.extractLsb' 40 8 ++ w5.extractLsb' 32 8)) := by
    have h7 := overlap7_realign (s0.sp - 0x97#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
    unfold overlap7View1 overlap7View2 at h7
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_97
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWP_step_to (mid := (blkPl_565).base + offErrStur11)
  dsimp only [offErrStur11]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have h7_c8 :
      ((s0.sp - 0xc8#64) ↦₃₂ (w5.extractLsb' 32 8 ++ w5.extractLsb' 24 8 ++ w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 0xc4#64) ↦₈ c5) ∗ ((s0.sp - 0xc3#64) ↦₁₆ (c7 ++ c6)) =
      ((s0.sp - 0xc8#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
        ((s0.sp - 0xc6#64) ↦₈ w5.extractLsb' 24 8) ∗
        ((s0.sp - 0xc5#64) ↦₃₂ (c7 ++ c6 ++ c5 ++ w5.extractLsb' 32 8)) := by
    have h7 := overlap7_realign (s0.sp - 0xc8#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) c5 c6 c7
    unfold overlap7View1 overlap7View2 at h7
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h7
  ispoll_rw_pre h7_c8
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWP_step_to (mid := (blkPl_565).base + offEpilogue)
  dsimp only [offEpilogue]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  let restErr : SepProp :=
    ((s0.sp - 0x90#64) ↦₆₄ speWord 1) ∗
    ((s0.sp - 0x88#64) ↦₆₄ cap) ∗
    ((s0.sp - 0x80#64) ↦₆₄ ptr) ∗
    ((s0.sp - 0x78#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ((s0.sp - 0x70#64) ↦₆₄ fnPtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
    (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
    (fnPtr ↦ᵣ utf8 "read") ∗
    dirAt A (x.self + 0x28#64) x.peers ∗
    protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
    (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
    FromRecordCallees.lsLogOff ∗ A.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
    stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
    memRegion (s0.sp - 0xd0#64) 8 ∗
    ((s0.sp - 0xc1#64) ↦₈ c15) ∗
    memRegion (s0.sp - 0xb7#64) 7 ∗
    ((s0.sp - 0xb0#64) ↦₆₄ fnPtr) ∗
    ((s0.sp - 0xa8#64) ↦₈ w5.extractLsb' 0 8) ∗
    memRegion (s0.sp - 0xa7#64) 7
  refine sepWP_conseq (P' :=
      memRegion (s0.sp - 0xa0#64) 16 ∗
      (epiloguePre s0 x
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
        fnPtr (w5.extractLsb' 0 8) ∗ restErr)) ?_ ?_
  · have hback_c8 := (overlap7_realign (s0.sp - 0xc8#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)).symm
    have hback_97 := (overlap7_realign (s0.sp - 0x97#64)
      (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
      (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)).symm
    unfold overlap7View2 at hback_c8 hback_97
    simp only [ispoll_sp_eqs] at hback_c8 hback_97
    refine Entails.trans (Entails.of_eq ?_)
      (sepConj_mono_left (s48_byte7_entails_memRegion16 s0.sp fnPtr (w5.extractLsb' 0 8)
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)))
    · refine Eq.trans (by dsimp only [restErr]; ac_rfl :
        _ = (((s0.sp - 0x97#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
              ((s0.sp - 0x95#64) ↦₈ w5.extractLsb' 24 8) ∗
              ((s0.sp - 0x94#64) ↦₃₂ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8 ++ w5.extractLsb' 40 8 ++ w5.extractLsb' 32 8))) ∗
            (((s0.sp - 0xc8#64) ↦₁₆ (w5.extractLsb' 16 8 ++ w5.extractLsb' 8 8)) ∗
              ((s0.sp - 0xc6#64) ↦₈ w5.extractLsb' 24 8) ∗
              ((s0.sp - 0xc5#64) ↦₃₂ (w5.extractLsb' 56 8 ++ w5.extractLsb' 48 8 ++ w5.extractLsb' 40 8 ++ w5.extractLsb' 32 8))) ∗
            (((s0.sp - 0xa0#64) ↦₆₄ fnPtr) ∗
              ((s0.sp - 0x98#64) ↦₈ w5.extractLsb' 0 8) ∗
              (((s0.sp - 0xc0#64) ↦₆₄ fnPtr) ∗
                ((s0.sp - 0xb8#64) ↦₈ w5.extractLsb' 0 8) ∗
                memRegion x.call.out 48 ∗
                idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
                savedCalleeSlots s0 ∗ restErr))) ?_
      rw [hback_97, hback_c8]
      unfold epiloguePre
      ac_rfl
  refine sepWP_conseq (P' :=
      epiloguePre s0 x
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
        fnPtr (w5.extractLsb' 0 8) ∗ (memRegion (s0.sp - 0xa0#64) 16 ∗ restErr))
    (Entails.of_eq (by ac_rfl)) ?_
  refine ispoll_epilogue_1bc_placed (H := H) x
    (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
    (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
    fnPtr (w5.extractLsb' 0 8) (memRegion (s0.sp - 0xa0#64) 16 ∗ restErr)
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, hvregs])
    (by wp_norm_goal) (by wp_norm_goal) ?_
  intro sf hspf hcsf htrf
  refine ⟨hspf, hcsf, ?_⟩
  have htr_s : sf.trace = s.trace := by simp only [wp_norm, arm64_norm] at htrf; exact htrf
  have hcap_lo :
      BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 cap) &&& 0xFFFFFFFF000000FF#64 |||
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (cap >>> 8)) &&& 16777215#64) <<< 8) =
      cap.extractLsb' 0 32 := by
    ext i hi; interval_cases i <;> simp
  have hcap_hi : BitVec.truncate 32 (cap >>> 32) = cap.extractLsb' 32 32 := by
    ext i hi; interval_cases i <;> simp
  unfold epilogueOut
  conv =>
    lhs; arg 1
    simp only [wp_norm, arm64_norm, hcap_lo, hcap_hi]
  refine Entails.trans (Entails.of_eq (by dsimp only [restErr]; ac_rfl :
    _ = ((x.call.out ↦₆₄ speWord 1) ∗
          ((x.call.out + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((x.call.out + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((x.call.out + 16#64) ↦₆₄ ptr) ∗
          ((x.call.out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((x.call.out + 32#64) ↦₆₄ fnPtr) ∗
          ((x.call.out + 40#64) ↦₈ w5.extractLsb' 0 8) ∗
          overlap7View2 (x.call.out + 41#64)
            (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
            (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
          (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
            if cap = 0#64 then emp
            else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          (fnPtr ↦ᵣ utf8 "read") ∗
          ((s0.sp - 0x90#64) ↦₆₄ speWord 1) ∗
          ((s0.sp - 0x88#64) ↦₆₄ cap) ∗ ((s0.sp - 0x80#64) ↦₆₄ ptr) ∗
          ((s0.sp - 0x78#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((s0.sp - 0x70#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length)) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
          stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
          memRegion (s0.sp - 0xd0#64) 8 ∗
          overlap7View2 (s0.sp - 0xc8#64)
            (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
            (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
          ((s0.sp - 0xc1#64) ↦₈ c15) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0xb8#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 0xb7#64) 7 ∗
          ((s0.sp - 0xb0#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0xa8#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 0xa7#64) 7 ∗
          memRegion (s0.sp - 0xa0#64) 16 ∗
          savedCalleeSlots s0) ∗
        (dirAt A (x.self + 0x28#64) x.peers ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          FromRecordCallees.lsLogOff ∗ A.pool))) ?_
  refine Entails.trans
    (sepConj_mono_left (epilogueOut_err_reassemble A s0.sp x.call.out bs cap ptr fnPtr)) ?_
  refine Entails.trans
    (Entails.of_eq (by ac_rfl :
      (idSaveOutAt A x.call.out (.error ()) ∗ memRegion (s0.sp - 0x90#64) 48) ∗ _ =
      idSaveOutAt A x.call.out (.error ()) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
          stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
          memRegion (s0.sp - 0xd0#64) 8 ∗
          overlap7View2 (s0.sp - 0xc8#64)
            (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
            (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8) ∗
          ((s0.sp - 0xc1#64) ↦₈ c15) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0xb8#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 0xb7#64) 7 ∗
          ((s0.sp - 0xb0#64) ↦₆₄ fnPtr) ∗
          ((s0.sp - 0xa8#64) ↦₈ w5.extractLsb' 0 8) ∗
          memRegion (s0.sp - 0xa7#64) 7 ∗
          memRegion (s0.sp - 0xa0#64) 16 ∗
          memRegion (s0.sp - 0x90#64) 48 ∗
          savedCalleeSlots s0) ∗
        (dirAt A (x.self + 0x28#64) x.peers ∗
          idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 1#8 ∗
          protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
          FromRecordCallees.lsLogOff ∗ A.pool))) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left
      (restore_savePollStack s0 hstk hhi
        (w5.extractLsb' 8 8) (w5.extractLsb' 16 8) (w5.extractLsb' 24 8)
        (w5.extractLsb' 32 8) (w5.extractLsb' 40 8) (w5.extractLsb' 48 8) (w5.extractLsb' 56 8)
        c15 fnPtr (w5.extractLsb' 0 8) fnPtr (w5.extractLsb' 0 8)))) ?_
  dsimp only [idSavePollSpecPlaced, StoreKit.withLsCodeRoLoaded]
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_right (Except.error () : Except Unit (List (BitVec 8)))
    (Entails.sepExists_right (Except.error () : Except Unit (Option IdentityKey)) ?_)
  simp only [idSaveOf, idSavePeers, sepConj_assoc]
  refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
  exact ⟨⟨herr_case.1.symm, htr_s.trans herr_case.2⟩, rfl⟩

end Placed

end CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
