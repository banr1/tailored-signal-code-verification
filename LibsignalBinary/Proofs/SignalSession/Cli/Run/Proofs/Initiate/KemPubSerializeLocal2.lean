/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# Proof of `<kem::Key<Public>>::serialize [local#1]`

Proves fixed- and variable-stack separation-logic contracts for
`<kem::Key<Public>>::serialize [local#1]` on `tripleRatchetProgAtExt img.base ext1` under
`AllocContractsX img A ext1`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.KemPubSerializeLocal2

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.E2E
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev kemPubSerLocal2Sym : String :=
  "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"

theorem kemPubSerLocal2_fnOff :
    libsignalSessionCode.fnOff kemPubSerLocal2Sym =
      num% (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]")

gen_decodes CryptoVerification.libsignalSessionCode_tree cliKemPubSerLocal2Bin
  [(ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]") →
   (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]" + 0x90)]

def kemPubSerializeValAtStkSpec (A : RustAlloc) (calleeStk : Nat) :
    Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (boxPtr, pkBytes) s =>
    ⌜s.readReg64 .x0 = boxPtr ∧ s.readReg64 .x1 = 1568#64 ∧ pkBytes.length = 1568⌝ ∗
      (boxPtr ↦ₛ pkBytes) ∗ A.pool ∗ stackAt s.sp calleeStk
  post := fun (boxPtr, pkBytes) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x1 = 1569#64 ∧ sf.trace = s0.trace⌝ ∗
      (boxPtr ↦ₛ pkBytes) ∗
      ((sf.readReg64 .x0) ↦ₛ (8#8 :: pkBytes)) ∗ A.live (sf.readReg64 .x0) 1569 1 ∗
      A.pool ∗ stackAt s0.sp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev kemPubSerFixedStk : Nat := extHookStack + 48

private theorem stackAt_kemPubSerFixed (sp : BitVec 64) :
    stackAt sp kemPubSerFixedStk =
      stackAt (sp - 48#64) extHookStack ∗ ProofLib.cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_1569_split_local (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), ProofLib.memRegion_one]

private theorem sepWPp_pure_mid_local {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem panic_mem_of_trace_eq (s0 : State) {sp : State} {Pm R : SepProp}
    (htr : sp.trace = s0.trace ++ [allocFailedEvent]) (hm : sp.mem ⊨ Pm ∗ R) :
    sp.mem ⊨ ⌜allocFailedIn s0 sp ∧ s0.trace <+: sp.trace⌝ ∗ anyHeap ∗ R := by
  rw [← sepConj_assoc]
  exact Satisfies.mono
    (sepConj_mono_left
      (Entails.pure_right
        (CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_eq htr)
        (entails_anyHeap Pm)))
    hm

private theorem sp_sub_48_add_48 (sp : BitVec 64) : (sp - 48#64) + 48#64 = sp := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sp_sub_48_add_48 BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "alloc::raw_vec::handle_error")

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1200000 in
/-- Fixed-stack contract for `<kem::Key<Public>>::serialize [local#1]` under `AllocContractsX`. -/
theorem kemPubKeySerialize_local2_fixed_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)}
    (hAlloc : AllocContractsX img A ext1) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr kemPubSerLocal2Sym)
      ((kemPubSerializeValAtStkSpec A kemPubSerFixedStk).inImage img) := by
  unfold Spec.inImage
  simp only [kemPubSerializeValAtStkSpec, stackAt_kemPubSerFixed]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff kemPubSerLocal2Sym =
      num% (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]") :=
    kemPubSerLocal2_fnOff
  have hshim := shim_ok_at2_ext_x hAlloc (name := kemPubSerLocal2Sym)
    (k := num% (ls_rel%
      "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  have halloc := alloc_ok_at_norm_ext_x hAlloc (name := kemPubSerLocal2Sym)
    (k := num% (ls_rel%
      "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"
      "__rustc::__rust_alloc"))
  have hmemcpy := hAlloc.session_memcpy_region_ok_at kemPubSerLocal2Sym
    (num% (ls_rel%
      "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"
      "memcpy"))
    (hk := by rw [hfn]; simp only [arm64_norm])
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext1)
    (name := kemPubSerLocal2Sym)
    (k := num% (ls_rel%
      "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"
      "alloc::raw_vec::handle_error"))
  clear hfn
  wpp_init g s0
  code_fetches CryptoVerification.libsignalSessionCode cliKemPubSerLocal2Bin img.base
    (Rust.withPanics ext1) kemPubSerLocal2_fnOff
    (num% (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]")) 144
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext1)).fnAddr kemPubSerLocal2Sym := by
    rw [hpc, Program.fnAddr_rebase, kemPubSerLocal2_fnOff]
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmemcpy hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext1)).fnAddr kemPubSerLocal2Sym = fnBase
  examples_hide_fetches
  obtain ⟨boxPtr, pkBytes⟩ := g
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP_inImage (mid := fnBase + bv% (72)) hinv0
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"
      "__rustc::__rust_alloc"))
    hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_call halloc (1569, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv3
  have ⟨hF3, hsym3⟩ := hinv3
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_local fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"
        "alloc::raw_vec::handle_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    exact panic_mem_of_trace_eq s0
      (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›]) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_1569_split_local, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => ?_
    refine sepWPp_pure_mid_local fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"
        "memcpy"))
      hinv3
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF4, hsym4⟩
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, pkBytes)
    wp_steps
    simp only [pointsToBytes_cons]
    wp_done

theorem kemPubKeySerialize_local2_fixed_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr kemPubSerLocal2Sym)
      ((kemPubSerializeValAtStkSpec A kemPubSerFixedStk).inImage img) :=
  kemPubKeySerialize_local2_fixed_ext_ok hh.alloc

private theorem memRegion_bound_of_pointsTo64_local {m : Memory} {b a v : BitVec 64} {n : Nat}
    {R : SepProp} (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

private theorem stackAt_sub_split_local (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

def kemPubSerializeFullAtStkSpec (A : RustAlloc) (calleeStk : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (keyRef, kpkPtr, kpk) s =>
    ⌜s.readReg64 .x0 = kpkPtr ∧ s.readReg64 .x1 = 1568#64 ∧ kpk.length = 1568⌝ ∗
      (keyRef ↦₆₄ kpkPtr) ∗ ((keyRef + 8#64) ↦₆₄ 1568#64) ∗
      (kpkPtr ↦ₛ kpk) ∗ A.pool ∗ stackAt s.sp calleeStk
  post := fun (keyRef, kpkPtr, kpk) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x1 = 1569#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) 1569 1 ∗
      ((sf.readReg64 .x0) ↦ₛ (0x08#8 :: kpk)) ∗
      (keyRef ↦₆₄ kpkPtr) ∗ ((keyRef + 8#64) ↦₆₄ 1568#64) ∗
      (kpkPtr ↦ₛ kpk) ∗ A.pool ∗ stackAt s0.sp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Variable-stack contract (`0x30 + extHookStack ≤ stk`) for `<kem::Key<Public>>::serialize [local#1]` under `AllocContractsX`. -/
theorem kemPubKeySerialize_local2_full_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)}
    (hAlloc : AllocContractsX img A ext1)
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr kemPubSerLocal2Sym)
      ((kemPubSerializeFullAtStkSpec A stk).inImage img) := by
  refine subroutine_ok.of_codeLoaded fun (keyRef, kpkPtr, kpk) R s0 hpc hrun hpre hsp _hL => ?_
  have hle : kemPubSerFixedStk ≤ stk := by
    dsimp [kemPubSerFixedStk]; omega
  have hbound_mem : s0.mem ⊨ memRegion (s0.sp - BitVec.ofNat 64 stk) stk ∗
      ((keyRef ↦₆₄ kpkPtr) ∗
       (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        ⌜s0.readReg64 .x0 = kpkPtr ∧ s0.readReg64 .x1 = 1568#64 ∧ kpk.length = 1568⌝ ∗
        ((keyRef + 8#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ kpk) ∗ A.pool ∗ R)) := by
    dsimp only [Spec.inImage, kemPubSerializeFullAtStkSpec, stackAt] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  have hhi : stk ≤ 2 ^ 64 := memRegion_bound_of_pointsTo64_local hbound_mem
  have hsplit := stackAt_sub_split_local s0.sp hle hhi
  let F : SepProp :=
    (keyRef ↦₆₄ kpkPtr) ∗ ((keyRef + 8#64) ↦₆₄ 1568#64) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kemPubSerFixedStk)
  have hpre' : s0.mem ⊨ ((kemPubSerializeValAtStkSpec A kemPubSerFixedStk).inImage img).pre
      (kpkPtr, kpk) s0 ∗ (F ∗ R) := by
    dsimp only [Spec.inImage, kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (kemPubKeySerialize_local2_fixed_ext_ok hAlloc).mono_outcome (kpkPtr, kpk) (F ∗ R) s0
    hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

theorem kemPubKeySerialize_local2_full_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (hh : RunHooks img A (cliExterns W))
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr kemPubSerLocal2Sym)
      ((kemPubSerializeFullAtStkSpec A stk).inImage img) :=
  kemPubKeySerialize_local2_full_ext_ok hh.alloc hstk

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.KemPubSerializeLocal2

end

