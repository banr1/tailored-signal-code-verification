/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoop
import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPb
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `AllocContracts4K` Specialization for `<spqr::chain::Chain>::into_pb`

Specializes the `<spqr::chain::Chain>::into_pb` allocation step and subroutine contracts from
`AllocContracts` to `AllocContracts4K` (`into_pb` invokes only `shim`, `alloc`, and `dealloc`,
with no `mem*` calls).
-/

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L36
open IntoPbDecodes

set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 800000 in
theorem intoPb_alloc_step_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (x : ChainIntoPbCall) (s0 s1 : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pos : 1 ≤ x.chain.links.length) (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hpc1 : s1.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 288#64) (htr1 : TraceCalleeSaved s1 s0)
    (hfp1 : s1.readReg64 .fp = s0.sp - 96#64) (hx19_1 : s1.readReg64 .x19 = x.chainPtr)
    (hx20_1 : s1.readReg64 .x20 = x.out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112))
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26_1 : s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = x.gChain.linksHead)
    (hx28_1 : s1.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainIntoPbName + 148#64) s1
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (fun sm Pm =>
        sm.sp = s0.sp - 288#64 ∧ sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x3 = x.gChain.linksCap ∧ sm.readReg64 .x19 = x.chainPtr ∧
        sm.readReg64 .x20 = x.out ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112) ∧
        sm.readReg64 .x24 = 8#64 ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        sm.readReg64 .x27 = x.gChain.linksHead ∧ sm.readReg64 .x28 = x.gChain.linksPtr ∧
        (if sm.readReg64 .x0 = 0 then
           sm.trace = s0.trace ++ [allocFailedEvent]
         else
           TraceCalleeSaved sm s0 ∧
           (Pm ⊢ memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
             A.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
             memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
             (if x.gChain.linksCap = 0 then emp
              else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
                vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
                  x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
             vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
             A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
             stackAt (s0.sp - 288#64) dropStack32))) := by
  rcases htr1 with ⟨htr1, hvr1⟩
  have hshim := hA.shim_ok_at chainIntoPbName
    (ls_rel% "<spqr::chain::Chain>::into_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [show libsignalSessionCode.fnOff chainIntoPbName = num% (ls_off% "<spqr::chain::Chain>::into_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb"),
            show libsignalSessionCode.fnOff shimName = num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") from (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := hA.alloc_ok_at chainIntoPbName
    (ls_rel% "<spqr::chain::Chain>::into_pb" "__rustc::__rust_alloc")
    (by rw [show libsignalSessionCode.fnOff chainIntoPbName = num% (ls_off% "<spqr::chain::Chain>::into_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb"),
            show libsignalSessionCode.fnOff allocName = num% (ls_off% "__rustc::__rust_alloc") from (ls_stub% "__rustc::__rust_alloc")])
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  have hcbz_23 : (BitVec.ofNat 64 (x.chain.links.length * 112) == 0#64) = false :=
    mul_112_beq_zero_false (by omega) hl_new_lt
  have halign8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hsplit_stack : stackAt (s0.sp - 288#64) dropStack32 =
      stackAt (s0.sp - 288#64) allocHookStack ∗ memRegion (s0.sp - 4416#64) 32 := by
    rw [stackAt_dropStack32_split_allocHook, BitVec.sub_sub]; rfl
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, tripleRatchetProgAtExt, chainIntoPbName,
    sessionShimSpec, rustAllocSpec, BitVec.ofNat_eq_ofNat] at hshim halloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  rw [hsplit_stack]; unfold intoPbScratchAt; wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (x.chain.links.length * 112, 8)
  rw [‹sf.sp = s1.sp›, hsp1]; wp_steps
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · simp only [hoom, ↓reduceIte]
    wp_focus_pure; rintro htr_a
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    simp only [Reg.x0, Reg.x3, Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
      Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm, *, ↓reduceIte, and_self]
  · simp only [hoom, ↓reduceIte]
    wp_focus_pure; rintro ⟨_, htr_a⟩
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    simp only [TraceCalleeSaved, Reg.x0, Reg.x3, Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
      Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm, *, ↓reduceIte, true_and, and_self]
    exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem chain_into_pb_pinned_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    ChainIntoPbPinnedOkExt b A ext := by
  have hdealloc : DeallocOkExt b A ext := hA.dealloc
  unfold ChainIntoPbPinnedOkExt
  refine subroutine_ok_of_sepWPp fun x R s0 hpc hrun hpre hsp_align =>
    ⟨(chainIntoPbPinnedSpec A).pre x s0, R, hpre, ?_⟩
  dsimp only [State.spAligned] at hsp_align
  refine SepWPp.of_sepWP (mid := (dropProgAtExt b ext).fnAddr chainIntoPbName + 116#64) ?_
  wp_conv_pre => dsimp only [chainIntoPbPinnedSpec]
  wp_focus_pure
  rintro ⟨hx8, hx0⟩
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (chainAt_unpack A x.chainPtr x.gChain x.chain))) ?_
  wp_focus_pure
  rintro ⟨hlen, hl_le, hl_cap_lt, hl_cap_ne, hl_head, hn1, hn2, hn3⟩
  have hl_new_lt : x.chain.links.length * 112 < 2 ^ 63 := by omega
  wp_simp_pre [sepConj_assoc]
  refine SepWP.mono (intoPb_prologue x s0 hsp_align hl_new_lt hpc hrun hx8 hx0) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hfp1, hx3_1, hx19_1, hx20_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
  refine SepWPp.weaken_pre hP1 ?_
  by_cases hnil : x.chain.links = []
  · refine SepWPp.of_sepWP_ret ?_
    refine SepWP.mono (intoPb_empty_links hdealloc x s0 s1 hsp_align hnil hlen hl_cap_lt hl_cap_ne
      hn1 hn2 hn3 hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1 hx25_1 hx26_1 hx28_1) ?_
    rintro sf P_f _ _ ⟨hP_f, hspf, htrf, hcsf⟩
    refine ⟨fun hm => ?_, hspf, hcsf⟩
    dsimp only [chainIntoPbPinnedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htrf, Satisfies.mono (sepConj_mono_left hP_f) hm⟩
  · have hlen_pos : 1 ≤ x.chain.links.length := Nat.pos_of_ne_zero (List.length_pos_iff.mpr hnil).ne'
    refine SepWPp.of_sepWP (mid := (dropProgAtExt b ext).fnAddr chainIntoPbName + 148#64) ?_
    refine SepWP.mono (intoPb_alloc_step_4k hA x s0 s1 hsp_align hlen_pos hl_new_lt
      hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1) ?_
    rintro sm Pm hpcm hrunm ⟨hspm, hfpm, hx3m, hx19m, hx20m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hbranch⟩
    by_cases hoom : sm.readReg64 .x0 = 0
    · simp only [hoom, ↓reduceIte] at hbranch
      exact intoPb_oom_panic (A := A) x s0 sm Pm R hpcm hrunm hoom hbranch
    · simp only [hoom, ↓reduceIte] at hbranch
      refine SepWPp.weaken_pre hbranch.2 ?_
      refine SepWPp.of_sepWP_ret ?_
      refine SepWP.mono (intoPb_post_alloc_ok hdealloc x s0 sm hsp_align hlen_pos hlen hl_le
        hl_cap_lt hl_cap_ne hl_head hn1 hn2 hn3 hpcm hrunm hspm hbranch.1 hfpm hoom hx3m
        hx19m hx20m hx22m hx24m hx25m hx26m hx27m hx28m) ?_
      rintro sf P_f _ _ ⟨hP_f, hspf, htrf, hcsf⟩
      refine ⟨fun hm => ?_, hspf, hcsf⟩
      dsimp only [chainIntoPbPinnedSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htrf, Satisfies.mono (sepConj_mono_left hP_f) hm⟩

theorem chain_into_pb_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    ChainIntoPbOkExt b A ext := by
  have hpinned := chain_into_pb_pinned_ok_ext_4k hA
  unfold ChainIntoPbOkExt
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    hpinned.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [chainIntoPbPinnedSpec, chainIntoPbSpec] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (chainPBIntoPinnedAt_entails_protoRepr A x.gChain x.out x.chain)))) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chain_into_pb_pinned_ok_ext_X_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainIntoPbName) (chainIntoPbPinnedSpecX A) := by
  have hpinned := chain_into_pb_pinned_ok_ext_4k hA
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (chainIntoPbPinnedSpec A).pre x s0 ∗
      (memRegion (s0.sp - 16672#64) 12256 ∗ R) := by
    dsimp only [chainIntoPbPinnedSpecX, chainIntoPbPinnedSpec] at hpre ⊢
    rw [stackAt_chainIntoPbX_split s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine hpinned.mono_outcome x (memRegion (s0.sp - 16672#64) 12256 ∗ R) s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX] at hpost ⊢
    rw [stackAt_chainIntoPbX_split s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX] at hpost ⊢
    rw [← sepConj_assoc] at hpost; exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

theorem chain_into_pb_ok_ext_X_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainIntoPbName) (chainIntoPbSpecX A) := by
  have hpinned := chain_into_pb_pinned_ok_ext_X_4k hA
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    hpinned.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [chainIntoPbPinnedSpecX, chainIntoPbSpecX] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (chainPBIntoPinnedAt_entails_protoRepr A x.gChain x.out x.chain)))) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chain_into_pb_pinned_ok_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    ChainIntoPbPinnedOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img (chain_into_pb_pinned_ok_ext_X_4k hA)

theorem chain_into_pb_ok_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    ChainIntoPbOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img (chain_into_pb_ok_ext_X_4k hA)

theorem chain_into_pb_ok_x_4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    ChainIntoPbOkX img A ext :=
  chain_into_pb_ok_4k hA

end CryptoVerification.SpqrV1.ChainProofs
