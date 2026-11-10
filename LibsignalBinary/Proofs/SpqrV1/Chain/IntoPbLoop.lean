/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoin
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Epilogue and Loop Proofs for `<spqr::chain::Chain>::into_pb`

Proves the 288-byte frame scratch invariants, shared epilogue (`chainIntoPb_epilogue`,
`0x60848 .. 0x608cc`), and both ring-buffer conversion loops (`intoPb_loop1_run`,
`intoPb_loop2_run`), together with their relocatable `[LibsignalPlacement]` counterparts for
Block `365`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
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

/-! ## Callee Offset Helpers and Normalization Lemmas -/

theorem dropChainEpochSliceLocal2_rel_intoPb (b : BitVec 64) (ext : String → Option (State → State)) :
    (dropProgAtExt b ext).fnAddr dropChainEpochSliceLocal2Name =
      (dropProgAtExt b ext).fnAddr chainIntoPbName +
        (bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]" "<spqr::chain::Chain>::into_pb")) := by
  change b + BitVec.ofNat 64 (libsignalSessionCode.fnOff dropChainEpochSliceLocal2Name) =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff chainIntoPbName) +
      (bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]" "<spqr::chain::Chain>::into_pb"))
  rw [show libsignalSessionCode.fnOff dropChainEpochSliceLocal2Name = num% (ls_off% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]") from (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]"),
      show libsignalSessionCode.fnOff chainIntoPbName = num% (ls_off% "<spqr::chain::Chain>::into_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb")]
  bv_omega

theorem rustDealloc_rel_intoPb (b : BitVec 64) (ext : String → Option (State → State)) :
    (dropProgAtExt b ext).fnAddr "__rustc::__rust_dealloc" =
      (dropProgAtExt b ext).fnAddr chainIntoPbName +
        (bv% (ls_rel% "<spqr::chain::Chain>::into_pb" "__rustc::__rust_dealloc")) := by
  change b + BitVec.ofNat 64 (libsignalSessionCode.fnOff "__rustc::__rust_dealloc") =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff chainIntoPbName) +
      (bv% (ls_rel% "<spqr::chain::Chain>::into_pb" "__rustc::__rust_dealloc"))
  rw [show libsignalSessionCode.fnOff "__rustc::__rust_dealloc" = num% (ls_off% "__rustc::__rust_dealloc") from (ls_stub% "__rustc::__rust_dealloc"),
      show libsignalSessionCode.fnOff chainIntoPbName = num% (ls_off% "<spqr::chain::Chain>::into_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb")]
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem pool_entails_empty_arrayAt_pool_intoPb {α : Type} (A : RustAlloc)
    (elem : α → BitVec 64 → SepProp) (stride : Nat) (ptr : BitVec 64) :
    A.pool ⊢ arrayAt elem stride ptr [] ∗ A.pool :=
  Entails.of_eq (emp_sepConj A.pool).symm

@[simp, arm64_norm, wp_norm]
theorem truncate32_zeroExtend64 (v : BitVec 32) :
    (v.zeroExtend 64).truncate 32 = v := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem setWidth32_setWidth64 (v : BitVec 32) :
    (v.setWidth 64).setWidth 32 = v := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem add_curPtr_112_offset (ptr : BitVec 64) (n : Nat) (off : BitVec 64) :
    ptr + BitVec.ofNat 64 (n * 112) + off + 112#64 =
      ptr + BitVec.ofNat 64 ((n + 1) * 112) + off := by
  have h1 : ptr + BitVec.ofNat 64 (n * 112) + off + 112#64 =
      (ptr + BitVec.ofNat 64 (n * 112) + 112#64) + off := by bv_omega
  rw [h1, BitVec.add_assoc ptr, ofNat_mul_112_add_112]

@[simp, arm64_norm, wp_norm]
theorem ofNat_succ_mul_112_sub_112 (n : Nat) :
    BitVec.ofNat 64 ((1 + n) * 112) - 112#64 = BitVec.ofNat 64 (n * 112) := by
  rw [Nat.add_mul, Nat.one_mul, BitVec.ofNat_add]
  bv_omega

theorem memRegion_append_112 (base : BitVec 64) (n : Nat) (hn : (n + 1) * 112 < 2 ^ 63) :
    memRegion base (n * 112) ∗ memRegion (base + BitVec.ofNat 64 (n * 112)) 112 =
      memRegion base ((n + 1) * 112) := by
  have heq : (n + 1) * 112 = n * 112 + 112 := by omega
  rw [heq]
  exact (ProofLib.memRegion_split' (b := base) (n := n * 112) (k := 112)
    (b' := base + BitVec.ofNat 64 (n * 112)) rfl rfl (by omega)).symm

/-! ## Scratch Stack Frame `[s0.sp - 288#64 .. s0.sp - 96#64)` -/

/-- The 168-byte loop scratch region `[s0.sp - 264#64 .. s0.sp - 96#64)` during `into_pb`. -/
def intoPbLoopScratchAt (s0 : State) : SepProp :=
  memRegion (s0.sp - 264#64) 4 ∗
  (∃∗ s1c : BitVec 32, (s0.sp - 260#64) ↦₃₂ s1c) ∗
  (∃∗ s20 : BitVec 64, (s0.sp - 256#64) ↦₆₄ s20) ∗
  (∃∗ s28 : BitVec 64, (s0.sp - 248#64) ↦₆₄ s28) ∗
  (∃∗ s30 : BitVec 64, (s0.sp - 240#64) ↦₆₄ s30) ∗
  (∃∗ s38 : BitVec 64, (s0.sp - 232#64) ↦₆₄ s38) ∗
  (∃∗ s40 : BitVec 64, (s0.sp - 224#64) ↦₆₄ s40) ∗
  (∃∗ s48 : BitVec 64, (s0.sp - 216#64) ↦₆₄ s48) ∗
  (∃∗ s50 : BitVec 64, (s0.sp - 208#64) ↦₆₄ s50) ∗
  (∃∗ s58 : BitVec 64, (s0.sp - 200#64) ↦₆₄ s58) ∗
  (∃∗ s60 : BitVec 64, (s0.sp - 192#64) ↦₆₄ s60) ∗
  (∃∗ s68 : BitVec 64, (s0.sp - 184#64) ↦₆₄ s68) ∗
  (∃∗ s70 : BitVec 64, (s0.sp - 176#64) ↦₆₄ s70) ∗
  (∃∗ s78 : BitVec 64, (s0.sp - 168#64) ↦₆₄ s78) ∗
  (∃∗ s80 : BitVec 64, (s0.sp - 160#64) ↦₆₄ s80) ∗
  (∃∗ s88 : BitVec 64, (s0.sp - 152#64) ↦₆₄ s88) ∗
  (∃∗ s90 : BitVec 64, (s0.sp - 144#64) ↦₆₄ s90) ∗
  (∃∗ s98 : BitVec 64, (s0.sp - 136#64) ↦₆₄ s98) ∗
  (∃∗ sa0 : BitVec 64, (s0.sp - 128#64) ↦₆₄ sa0) ∗
  (∃∗ sa8 : BitVec 64, (s0.sp - 120#64) ↦₆₄ sa8) ∗
  memRegion (s0.sp - 112#64) 16

/-- The 192-byte scratch region `[s0.sp - 288#64 .. s0.sp - 96#64)` during `into_pb`. -/
def intoPbScratchAt (s0 : State) (g : ChainGhost) (c : Chain) : SepProp :=
  ((s0.sp - 288#64) ↦₆₄ c.currentEpoch) ∗
  ((s0.sp - 280#64) ↦₆₄ c.sendEpoch) ∗
  ((s0.sp - 272#64) ↦₆₄ g.linksCap) ∗
  intoPbLoopScratchAt s0

theorem intoPbLoopScratchAt_pack (s0 : State)
    (s1c : BitVec 32)
    (s20 s28 s30 s38 s40 s48 s50 s58 s60 s68 s70 s78 s80 s88 s90 s98 sa0 sa8 : BitVec 64) :
    memRegion (s0.sp - 264#64) 4 ∗
      ((s0.sp - 260#64) ↦₃₂ s1c) ∗
      ((s0.sp - 256#64) ↦₆₄ s20) ∗
      ((s0.sp - 248#64) ↦₆₄ s28) ∗
      ((s0.sp - 240#64) ↦₆₄ s30) ∗
      ((s0.sp - 232#64) ↦₆₄ s38) ∗
      ((s0.sp - 224#64) ↦₆₄ s40) ∗
      ((s0.sp - 216#64) ↦₆₄ s48) ∗
      ((s0.sp - 208#64) ↦₆₄ s50) ∗
      ((s0.sp - 200#64) ↦₆₄ s58) ∗
      ((s0.sp - 192#64) ↦₆₄ s60) ∗
      ((s0.sp - 184#64) ↦₆₄ s68) ∗
      ((s0.sp - 176#64) ↦₆₄ s70) ∗
      ((s0.sp - 168#64) ↦₆₄ s78) ∗
      ((s0.sp - 160#64) ↦₆₄ s80) ∗
      ((s0.sp - 152#64) ↦₆₄ s88) ∗
      ((s0.sp - 144#64) ↦₆₄ s90) ∗
      ((s0.sp - 136#64) ↦₆₄ s98) ∗
      ((s0.sp - 128#64) ↦₆₄ sa0) ∗
      ((s0.sp - 120#64) ↦₆₄ sa8) ∗
      memRegion (s0.sp - 112#64) 16 ⊢
      intoPbLoopScratchAt s0 := by
  unfold intoPbLoopScratchAt
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_right s1c (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s20 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s28 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s30 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s38 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s40 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s48 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s50 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s58 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s60 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s68 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s70 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s78 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s80 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s88 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s90 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s98 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sa0 (Entails.refl _)) ?_
  exact sepConj_mono (Entails.sepExists_right sa8 (Entails.refl _)) (Entails.refl _)

theorem intoPbScratchAt_pack (s0 : State) (g : ChainGhost) (c : Chain)
    (s1c : BitVec 32)
    (s20 s28 s30 s38 s40 s48 s50 s58 s60 s68 s70 s78 s80 s88 s90 s98 sa0 sa8 : BitVec 64) :
    ((s0.sp - 288#64) ↦₆₄ c.currentEpoch) ∗
      ((s0.sp - 280#64) ↦₆₄ c.sendEpoch) ∗
      ((s0.sp - 272#64) ↦₆₄ g.linksCap) ∗
      memRegion (s0.sp - 264#64) 4 ∗
      ((s0.sp - 260#64) ↦₃₂ s1c) ∗
      ((s0.sp - 256#64) ↦₆₄ s20) ∗
      ((s0.sp - 248#64) ↦₆₄ s28) ∗
      ((s0.sp - 240#64) ↦₆₄ s30) ∗
      ((s0.sp - 232#64) ↦₆₄ s38) ∗
      ((s0.sp - 224#64) ↦₆₄ s40) ∗
      ((s0.sp - 216#64) ↦₆₄ s48) ∗
      ((s0.sp - 208#64) ↦₆₄ s50) ∗
      ((s0.sp - 200#64) ↦₆₄ s58) ∗
      ((s0.sp - 192#64) ↦₆₄ s60) ∗
      ((s0.sp - 184#64) ↦₆₄ s68) ∗
      ((s0.sp - 176#64) ↦₆₄ s70) ∗
      ((s0.sp - 168#64) ↦₆₄ s78) ∗
      ((s0.sp - 160#64) ↦₆₄ s80) ∗
      ((s0.sp - 152#64) ↦₆₄ s88) ∗
      ((s0.sp - 144#64) ↦₆₄ s90) ∗
      ((s0.sp - 136#64) ↦₆₄ s98) ∗
      ((s0.sp - 128#64) ↦₆₄ sa0) ∗
      ((s0.sp - 120#64) ↦₆₄ sa8) ∗
      memRegion (s0.sp - 112#64) 16 ⊢
      intoPbScratchAt s0 g c := by
  unfold intoPbScratchAt
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (intoPbLoopScratchAt_pack s0 s1c s20 s28 s30 s38 s40 s48 s50 s58
      s60 s68 s70 s78 s80 s88 s90 s98 sa0 sa8)))

theorem restore_stack_chainIntoPb (s0 : State) (g : ChainGhost) (c : Chain) :
    stackAt (s0.sp - 288#64) dropStack32 ∗
      intoPbScratchAt s0 g c ∗
      calleeSavedFromPbAt s0 ⊢
      stackAt s0.sp chainIntoPbStack := by
  rw [stackAt_chainIntoPb_split s0.sp]
  unfold intoPbScratchAt intoPbLoopScratchAt calleeSavedFromPbAt
  simp only [sepConj_assoc]
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_right c.currentEpoch (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right c.sendEpoch (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right g.linksCap (Entails.refl _)) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .fp) (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .lr) (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .x28) (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .x27) (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .x26) (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .x25) (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .x24) (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .x23) (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .x22) (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right (s0.readReg64 .x21) (Entails.refl _)) ?_
  exact sepConj_mono (Entails.sepExists_right (s0.readReg64 .x20) (Entails.refl _))
    (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))

/-! ## Shared Epilogue at `+820` (`0x60848 .. 0x608cc`) -/

theorem stackAt_dropStack32_split_allocHook (sp : BitVec 64) :
    stackAt sp dropStack32 = stackAt sp allocHookStack ∗ memRegion (sp - 4128#64) 32 := by
  unfold stackAt
  change memRegion (sp - 4128#64) 4128 = memRegion (sp - 4096#64) 4096 ∗ memRegion (sp - 4128#64) 32
  rw [sepConj_comm]
  exact ProofLib.memRegion_split' (b := sp - 4128#64) (n := 32) (k := 4096) (b' := sp - 4096#64)
    rfl (by bv_omega) (by decide)

/-- Pinned output `ChainPB` at `out` produced by `<spqr::chain::Chain>::into_pb`,
existentially quantifying over the newly allocated `links` vector buffer pointer `newLinksPtr`. -/
def chainPBIntoPinnedAt (A : RustAlloc) (gChain : ChainGhost) (out : BitVec 64) (cChain : Chain) :
    SepProp :=
  ∃∗ newLinksPtr : BitVec 64,
    chainPBAt A
      ⟨BitVec.ofNat 64 cChain.links.length, newLinksPtr,
        gChain.epochs.map toChainEpochPBGhost, gChain.nextRoot⟩
      out cChain.intoPb

theorem chainPBAt_entails_chainPBIntoPinnedAt (A : RustAlloc) (out newLinksPtr : BitVec 64)
    (gChain : ChainGhost) (cChain : Chain) :
    chainPBAt A
      ⟨BitVec.ofNat 64 cChain.links.length, newLinksPtr,
        gChain.epochs.map toChainEpochPBGhost, gChain.nextRoot⟩
      out cChain.intoPb ⊢
    chainPBIntoPinnedAt A gChain out cChain := by
  unfold chainPBIntoPinnedAt
  exact Entails.sepExists_right (P := chainPBAt A
      ⟨BitVec.ofNat 64 cChain.links.length, newLinksPtr,
        gChain.epochs.map toChainEpochPBGhost, gChain.nextRoot⟩
      out cChain.intoPb)
    (Q := fun newLinksPtr' => chainPBAt A
      ⟨BitVec.ofNat 64 cChain.links.length, newLinksPtr',
        gChain.epochs.map toChainEpochPBGhost, gChain.nextRoot⟩
      out cChain.intoPb)
    newLinksPtr (Entails.refl _)

/-- Return postcondition of `chainIntoPbPinnedSpec`. -/
abbrev intoPbPinnedRetPost (A : RustAlloc) (x : ChainIntoPbCall) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P' =>
    (P' ⊢
      chainPBIntoPinnedAt A x.gChain x.out x.chain ∗
      memRegion x.chainPtr 88 ∗
      A.pool ∗ stackAt s0.sp chainIntoPbStack) ∧
    sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ CalleeSavedPreserved s0 sf

set_option maxHeartbeats 800000 in
/-- Epilogue of `<spqr::chain::Chain>::into_pb` at `+820` (`0x60848 .. 0x608cc`):
calls `drop_glue::<[ChainEpoch]> [local#2]` twice on empty slices (`x1 = 0#64`),
conditionally calls `__rust_dealloc` on the old `VecDeque` buffer (`x28 = gChain.linksPtr`, `x9 = gChain.linksCap`),
writes the 80-byte `ChainPB` header at `x20 = out`, restores callee-saved registers, and returns. -/
theorem chainIntoPb_epilogue {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainIntoPbCall) (s0 s : State) (newLinksPtr : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63)
    (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hl_new_ne : newLinksPtr ≠ 0)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63)
    (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = 0#64)
    (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = newLinksPtr)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗
        chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  have hdrop : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainIntoPbName +
        (bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]" "<spqr::chain::Chain>::into_pb")))
      (dropChainEpochSliceSpec A) :=
    sub_ok_of_addr_eq (dropChainEpochSliceLocal2_rel_intoPb b ext)
      (drop_chain_epoch_slice_local2_ok_ext hdealloc)
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainIntoPbName +
        (bv% (ls_rel% "<spqr::chain::Chain>::into_pb" "__rustc::__rust_dealloc"))) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (rustDealloc_rel_intoPb b ext) hdealloc
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  have hdrop_emp1 := pool_entails_empty_arrayAt_pool_intoPb A (chainEpoch A) 112 x.gChain.linksPtr
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, chainIntoPbName, dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hdrop hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 840#64)
    (P_mid := memRegion x.out 80 ∗
      chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      arrayAt (chainEpochPBAt A) 112 newLinksPtr
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
      (if (x.gChain.linksCap == 0#64) = true then emp
       else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
         memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗
      intoPbScratchAt s0 x.gChain x.chain ∗
      calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
      sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
      sm.readReg64 .x23 = 0#64 ∧
      sm.readReg64 .x24 = newLinksPtr ∧
      sm.readReg64 .x25 = x.chain.sendEpoch ∧
      sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      sm.readReg64 .x27 = x.chain.currentEpoch ∧
      sm.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · refine SepWP.focus_weaken hdrop_emp1 (by sep_focus) ?_
    unfold intoPbScratchAt
    wp_steps
    wp_call hdrop ⟨x.gChain.linksPtr, []⟩
    rw [hsp, memRegion_zero, emp_sepConj]
    wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
    refine seq_clean (mid := entry + 852#64)
      (P_mid := memRegion x.out 80 ∗
        chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x24 = newLinksPtr ∧
        sm.readReg64 .x25 = x.chain.sendEpoch ∧
        sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        sm.readReg64 .x27 = x.chain.currentEpoch ∧
        sm.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · refine SepWP.focus_weaken hdrop_emp1 (by sep_focus) ?_
      wp_steps
      wp_call hdrop ⟨x.gChain.linksPtr, []⟩
      rw [hsp1, memRegion_zero, emp_sepConj]
      wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2⟩
      refine seq_clean (mid := entry + 880#64)
        (P_mid := memRegion x.out 80 ∗
          chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          arrayAt (chainEpochPBAt A) 112 newLinksPtr
            ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
          linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗
          intoPbScratchAt s0 x.gChain x.chain ∗
          calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32)
        (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x24 = newLinksPtr ∧
          sm.readReg64 .x25 = x.chain.sendEpoch ∧
          sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
          sm.readReg64 .x27 = x.chain.currentEpoch) ?_ ?_
      · unfold intoPbScratchAt
        by_cases hcap : x.gChain.linksCap = 0
        · have hcapb : (x.gChain.linksCap == 0#64) = true := beq_iff_eq.mpr hcap
          simp only [hcapb, ↓reduceIte, emp_sepConj, sepConj_emp]
          wp_steps
          wp_done
        · have hcapb : (x.gChain.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
          have hcap_pos : x.gChain.linksCap.toNat * 112 > 0 := by
            have hpos := BitVec.toNat_pos_of_ne_zero hcap; omega
          have hsz_bv := cap_mul_112_shift_eq x.gChain.linksCap hl_cap_lt
          have hsplit_stack := stackAt_dropStack32_split_allocHook (s0.sp - 288#64)
          simp only [hcapb, Bool.false_eq_true, ↓reduceIte]
          rw [hsplit_stack]
          wp_steps
          wp_call hdealloc_raw (x.gChain.linksPtr, x.gChain.linksCap.toNat * 112, 8)
          rw [hsp2, ← hsplit_stack]
          wp_done
      · rintro sm hpcm hrunm ⟨hspm, htrm, hfpm, hx19m, hx20m, hx21m, hx22m, hx24m, hx25m, hx26m, hx27m⟩
        rw [memRegion_80_split_out x.out]
        wp_pull_exists
        unfold chainHeaderCellsAt calleeSavedFromPbAt
        wp_steps
        refine SepWP.focus_weaken
          (restore_stack_chainIntoPb s0 x.gChain x.chain)
          (by unfold calleeSavedFromPbAt; sep_focus) ?_
        refine SepWP.focus_weaken
          (chainHeaderCellsAt_entails_memRegion_88 x.chainPtr x.gChain x.chain)
          (by unfold chainHeaderCellsAt; sep_focus) ?_
        refine SepWP.focus_weaken
          (Entails.trans
            (chainPBAt_pack_out A x.out newLinksPtr x.gChain x.chain hlen hl_new_lt hl_new_ne hn1 hn2 hn3)
            (chainPBAt_entails_chainPBIntoPinnedAt A x.out newLinksPtr x.gChain x.chain))
          (by sep_focus) ?_
        unfold intoPbPinnedRetPost
        wp_done

/-! ## Loop 1 (`0x60640 .. 0x606e0`, `+300 .. +460`) -/

set_option maxHeartbeats 800000 in
/-- Single iteration of Loop 1 (`0x60640 .. 0x606dc`, `+300 .. +456`). -/
theorem intoPb_loop1_step {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s0 s : State) (gChain : ChainGhost) (cChain : Chain)
    (srcBase dstBase : BitVec 64)
    (convG : List ChainEpochGhost) (conv : List ChainEpoch)
    (g : ChainEpochGhost) (ep : ChainEpoch)
    (restG : List ChainEpochGhost) (rest : List ChainEpoch)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hconv_len : convG.length = conv.length)
    (hrest_len : restG.length = rest.length)
    (hbound : (conv.length + 1 + rest.length) * 112 < 2 ^ 63)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 300#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
    (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 ((1 + rest.length) * 112))
    (hx13 : s.readReg64 .x13 = s0.sp - 160#64)
    (hx14 : s.readReg64 .x14 = s0.sp - 208#64)
    (hx15 : s.readReg64 .x15 = s0.sp - 260#64)
    (hx16 : s.readReg64 .x16 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
    (hx17 : s.readReg64 .x17 = srcBase + BitVec.ofNat 64 (conv.length * 112) + 56#64) :
    SepWP (dropProgAtExt b ext)
      (if rest.isEmpty then (dropProgAtExt b ext).fnAddr chainIntoPbName + 460#64
       else (dropProgAtExt b ext).fnAddr chainIntoPbName + 300#64)
      s
      (memRegion srcBase (conv.length * 112) ∗
        chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 (conv.length * 112)) ∗
        arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
          (restG.zip rest) ∗
        arrayAt (chainEpochPBAt A) 112 dstBase
          ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
        memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
        memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
        intoPbScratchAt s0 gChain cChain)
      (fun sf Pm =>
        (Pm ⊢ memRegion srcBase ((conv.length + 1) * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
            (restG.zip rest) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            (((convG ++ [g]).map toChainEpochPBGhost).zip ((conv ++ [ep]).map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
          intoPbScratchAt s0 gChain cChain) ∧
        sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x3 = s.readReg64 .x3 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x9 = s.readReg64 .x9 ∧
        sf.readReg64 .x10 = s0.sp - 160#64 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x12 = BitVec.ofNat 64 (rest.length * 112) ∧
        sf.readReg64 .x13 = s0.sp - 160#64 ∧
        sf.readReg64 .x14 = s0.sp - 208#64 ∧
        sf.readReg64 .x15 = s0.sp - 260#64 ∧
        sf.readReg64 .x16 = dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112) + 52#64 ∧
        sf.readReg64 .x17 = srcBase + BitVec.ofNat 64 ((conv.length + 1) * 112) + 56#64 ∧
        CalleeSavedPreserved s sf) := by
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, chainIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  refine SepWP.focus_rw
    (memRegion_112_split_dst (dstBase + BitVec.ofNat 64 (conv.length * 112)))
    (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.focus_rw
    (by rfl : intoPbScratchAt s0 gChain cChain =
      ((s0.sp - 288#64) ↦₆₄ cChain.currentEpoch) ∗
      ((s0.sp - 280#64) ↦₆₄ cChain.sendEpoch) ∗
      ((s0.sp - 272#64) ↦₆₄ gChain.linksCap) ∗
      intoPbLoopScratchAt s0)
    (by sep_focus) ?_
  unfold intoPbLoopScratchAt
  wp_pull_exists
  refine SepWP.focus_weaken
    (chainEpochAt_unpack_cells A g ep (srcBase + BitVec.ofNat 64 (conv.length * 112)))
    (by sep_focus) ?_
  wp_focus_pure
  rintro ⟨hs1, hs2, hs3, hs4, hs5, hs6, hr1, hr2, hr3, hr4, hr5, hr6⟩
  wp_steps
  refine SepWP.focus_weaken
    (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
      (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
      (BitVec.ofNat 64 ep.recv.prev.data.length)))
    (by sep_focus) ?_
  cases rest with
  | nil =>
    simp only [List.isEmpty_nil, List.length_nil, Nat.mul_zero, ↓reduceIte]
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 (conv.length * 112))
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
        ep.send.ctr ep.recv.ctr)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_append_112 srcBase conv.length (by omega)))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
        g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
      (by sep_focus) ?_
    wp_done
  | cons ep2 rest2 =>
    have hne : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) != 112#64) = true := by
      have hbeq : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) ==
          BitVec.ofNat 64 (1 * 112)) = false :=
        ofNat_mul_112_beq_false (by simp) (by simp at hbound ⊢; omega) (by decide)
      simpa [bne] using hbeq
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 (conv.length * 112))
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
        ep.send.ctr ep.recv.ctr)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_append_112 srcBase conv.length (by omega)))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
        g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
      (by sep_focus) ?_
    wp_done

/-- Inductive Loop 1 theorem (`0x60640 .. 0x606e0`, `+300 .. +460`) over `rem = (g, ep) :: rest`. -/
theorem intoPb_loop1_run {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (rem : List ChainEpoch) :
    ∀ (remG : List ChainEpochGhost) (convG : List ChainEpochGhost) (conv : List ChainEpoch)
      (s0 s : State) (gChain : ChainGhost) (cChain : Chain) (srcBase dstBase : BitVec 64)
      (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
      (hrem_pos : 1 ≤ rem.length)
      (hrem_len : remG.length = rem.length)
      (hconv_len : convG.length = conv.length)
      (hbound : (conv.length + rem.length) * 112 < 2 ^ 63)
      (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 300#64)
      (hrun : s.status = .Running)
      (hsp : s.sp = s0.sp - 288#64)
      (htr : TraceCalleeSaved s s0)
      (hfp : s.readReg64 .fp = s0.sp - 96#64)
      (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
      (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 (rem.length * 112))
      (hx13 : s.readReg64 .x13 = s0.sp - 160#64)
      (hx14 : s.readReg64 .x14 = s0.sp - 208#64)
      (hx15 : s.readReg64 .x15 = s0.sp - 260#64)
      (hx16 : s.readReg64 .x16 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
      (hx17 : s.readReg64 .x17 = srcBase + BitVec.ofNat 64 (conv.length * 112) + 56#64),
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr chainIntoPbName + 460#64)
        s
        (memRegion srcBase (conv.length * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 (conv.length * 112))
            (remG.zip rem) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) (rem.length * 112) ∗
          intoPbScratchAt s0 gChain cChain)
        (fun sf Pm =>
          (Pm ⊢ memRegion srcBase ((conv.length + rem.length) * 112) ∗
            arrayAt (chainEpochPBAt A) 112 dstBase
              (((convG ++ remG).map toChainEpochPBGhost).zip ((conv ++ rem).map chainEpochIntoPb)) ∗
            intoPbScratchAt s0 gChain cChain) ∧
          sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
          sf.readReg64 .fp = s0.sp - 96#64 ∧
          sf.readReg64 .x0 = s.readReg64 .x0 ∧
          sf.readReg64 .x3 = s.readReg64 .x3 ∧
          sf.readReg64 .x8 = s.readReg64 .x8 ∧
          sf.readReg64 .x9 = s.readReg64 .x9 ∧
          sf.readReg64 .x10 = s0.sp - 160#64 ∧
          sf.readReg64 .x11 = s.readReg64 .x11 ∧
          CalleeSavedPreserved s sf) := by
  induction rem with
  | nil => intro _ _ _ _ _ _ _ _ _ _ hpos; simp at hpos
  | cons ep rest ih =>
    intro remG convG conv s0 s gChain cChain srcBase dstBase hsp0_align _ hrem_len hconv_len hbound
      hpc hrun hsp htr hfp hx10 hx12 hx13 hx14 hx15 hx16 hx17
    cases remG with
    | nil => simp at hrem_len
    | cons g restG =>
      have hrest_len : restG.length = rest.length := by simpa using hrem_len
      have hlen_cons : (ep :: rest).length = 1 + rest.length := by simp [Nat.add_comm]
      have hsplit_dst :
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) =
            memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
            memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) := by
        rw [hlen_cons, Nat.add_mul, Nat.one_mul]
        exact ProofLib.memRegion_split' (b := dstBase + BitVec.ofNat 64 (conv.length * 112))
          (n := 112) (k := rest.length * 112)
          (b' := dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
          rfl (by rw [add_curPtr_112]) (by omega)
      have hstep := intoPb_loop1_step (A := A) (b := b) (ext := ext)
        s0 s gChain cChain srcBase dstBase convG conv g ep restG rest hsp0_align
        hconv_len hrest_len (by rw [hlen_cons] at hbound; omega)
        hpc hrun hsp htr hfp hx10 (by rw [hlen_cons] at hx12; exact hx12)
        hx13 hx14 hx15 hx16 hx17
      change SepWP _ _ _
        (memRegion srcBase (conv.length * 112) ∗
          (chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 (conv.length * 112)) ∗
            arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 (conv.length * 112) + 112#64)
              (restG.zip rest)) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) ∗
          intoPbScratchAt s0 gChain cChain) _
      rw [add_curPtr_112 srcBase conv.length, hsplit_dst]
      cases rest with
      | nil =>
        have hrestG_nil : restG = [] := List.eq_nil_of_length_eq_zero hrest_len
        subst hrestG_nil
        simp only [List.isEmpty_nil, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
        rintro sf Pm _ _ ⟨hPm, hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, _, _, _, _, _, _, hcs1⟩
        refine ⟨Entails.trans hPm ?_, hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, hcs1⟩
        simp only [List.zip_nil_right, arrayAt, List.length_nil, Nat.mul_zero, Nat.zero_mul,
          memRegion_zero, emp_sepConj, sepConj_emp, List.length_singleton, List.append_assoc,
          List.nil_append]
        exact Entails.of_eq (by ac_rfl)
      | cons ep2 rest2 =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep ?_)
        rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hfpm, hx0m, hx3m, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m, hx14m, hx15m, hx16m, hx17m, hcsm⟩
        have hconv1 : (conv ++ [ep]).length = conv.length + 1 := by
          rw [List.length_append, List.length_singleton]
        have hbound' : ((conv ++ [ep]).length + (ep2 :: rest2).length) * 112 < 2 ^ 63 := by
          rw [hconv1]; rw [hlen_cons] at hbound; omega
        have hih := ih restG (convG ++ [g]) (conv ++ [ep]) s0 sm gChain cChain srcBase dstBase
          hsp0_align (by simp) hrest_len (by simp [hconv_len]) hbound'
          hpcm hrunm hspm htrm hfpm hx10m hx12m hx13m hx14m hx15m
          (by rw [hconv1]; exact hx16m)
          (by rw [hconv1]; exact hx17m)
        simp only [hconv1, List.append_assoc, List.singleton_append] at hih
        refine SepWP.weaken_pre (Entails.trans hPm (Entails.of_eq (by ac_rfl))) (SepWP.mono hih ?_)
        rintro sf Pf _ _ ⟨hPf, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
        have hlen_add : conv.length + 1 + (ep2 :: rest2).length = conv.length + (ep :: ep2 :: rest2).length := by
          simp [Nat.add_assoc, Nat.add_comm 1]
        rw [hlen_add] at hPf
        exact ⟨hPf, hsp2, htr2, hfp2, hx0_2.trans hx0m, hx3_2.trans hx3m, hx8_2.trans hx8m,
          hx9_2.trans hx9m, hx10_2, hx11_2.trans hx11m,
          CalleeSavedPreserved.trans hcsm hcs2⟩

/-! ## Loop 2 (`0x60714 .. 0x607b4`, `+512 .. +672`) -/

set_option maxHeartbeats 800000 in
/-- Single iteration of Loop 2 (`0x60714 .. 0x607b0`, `+512 .. +668`). -/
theorem intoPb_loop2_step {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s0 s : State) (gChain : ChainGhost) (cChain : Chain)
    (srcBase dstBase : BitVec 64)
    (convG : List ChainEpochGhost) (conv : List ChainEpoch)
    (g : ChainEpochGhost) (ep : ChainEpoch)
    (restG : List ChainEpochGhost) (rest : List ChainEpoch)
    (m₁ : Nat)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hconv_len : convG.length = conv.length)
    (hrest_len : restG.length = rest.length)
    (hm1_le : m₁ ≤ conv.length)
    (hbound : (conv.length + 1 + rest.length) * 112 < 2 ^ 63)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 ((1 + rest.length) * 112))
    (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
    (hx12 : s.readReg64 .x12 = s0.sp - 160#64)
    (hx13 : s.readReg64 .x13 = s0.sp - 208#64)
    (hx14 : s.readReg64 .x14 = s0.sp - 260#64)
    (hx15 : s.readReg64 .x15 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
    (hx16 : s.readReg64 .x16 = srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112) + 56#64) :
    SepWP (dropProgAtExt b ext)
      (if rest.isEmpty then (dropProgAtExt b ext).fnAddr chainIntoPbName + 672#64
       else (dropProgAtExt b ext).fnAddr chainIntoPbName + 512#64)
      s
      (memRegion srcBase ((conv.length - m₁) * 112) ∗
        chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112)) ∗
        arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁ + 1) * 112))
          (restG.zip rest) ∗
        arrayAt (chainEpochPBAt A) 112 dstBase
          ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
        memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
        memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
        intoPbScratchAt s0 gChain cChain)
      (fun sf Pm =>
        (Pm ⊢ memRegion srcBase ((conv.length - m₁ + 1) * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁ + 1) * 112))
            (restG.zip rest) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            (((convG ++ [g]).map toChainEpochPBGhost).zip ((conv ++ [ep]).map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
          intoPbScratchAt s0 gChain cChain) ∧
        sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x2 = s.readReg64 .x2 ∧
        sf.readReg64 .x3 = s.readReg64 .x3 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x9 = BitVec.ofNat 64 (rest.length * 112) ∧
        sf.readReg64 .x10 = s0.sp - 160#64 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x12 = s0.sp - 160#64 ∧
        sf.readReg64 .x13 = s0.sp - 208#64 ∧
        sf.readReg64 .x14 = s0.sp - 260#64 ∧
        sf.readReg64 .x15 = dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112) + 52#64 ∧
        sf.readReg64 .x16 = srcBase + BitVec.ofNat 64 ((conv.length - m₁ + 1) * 112) + 56#64 ∧
        CalleeSavedPreserved s sf) := by
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, chainIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  refine SepWP.focus_rw
    (memRegion_112_split_dst (dstBase + BitVec.ofNat 64 (conv.length * 112)))
    (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.focus_rw
    (by rfl : intoPbScratchAt s0 gChain cChain =
      ((s0.sp - 288#64) ↦₆₄ cChain.currentEpoch) ∗
      ((s0.sp - 280#64) ↦₆₄ cChain.sendEpoch) ∗
      ((s0.sp - 272#64) ↦₆₄ gChain.linksCap) ∗
      intoPbLoopScratchAt s0)
    (by sep_focus) ?_
  unfold intoPbLoopScratchAt
  wp_pull_exists
  refine SepWP.focus_weaken
    (chainEpochAt_unpack_cells A g ep (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112)))
    (by sep_focus) ?_
  wp_focus_pure
  rintro ⟨hs1, hs2, hs3, hs4, hs5, hs6, hr1, hr2, hr3, hr4, hr5, hr6⟩
  wp_steps
  refine SepWP.focus_weaken
    (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
      (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
      (BitVec.ofNat 64 ep.recv.prev.data.length)))
    (by sep_focus) ?_
  cases rest with
  | nil =>
    simp only [List.isEmpty_nil, List.length_nil, Nat.mul_zero, ↓reduceIte]
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112))
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
        ep.send.ctr ep.recv.ctr)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_append_112 srcBase (conv.length - m₁) (by omega)))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
        g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
      (by sep_focus) ?_
    wp_done
  | cons ep2 rest2 =>
    have hne : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) != 112#64) = true := by
      have hbeq : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) ==
          BitVec.ofNat 64 (1 * 112)) = false :=
        ofNat_mul_112_beq_false (by simp) (by simp at hbound ⊢; omega) (by decide)
      simpa [bne] using hbeq
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112))
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
        ep.send.ctr ep.recv.ctr)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_append_112 srcBase (conv.length - m₁) (by omega)))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
        g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
      (by sep_focus) ?_
    wp_done

/-- Inductive Loop 2 theorem (`0x60714 .. 0x607b4`, `+512 .. +672`) over `rem = (g, ep) :: rest`. -/
theorem intoPb_loop2_run {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (rem : List ChainEpoch) :
    ∀ (remG : List ChainEpochGhost) (convG : List ChainEpochGhost) (conv : List ChainEpoch)
      (s0 s : State) (gChain : ChainGhost) (cChain : Chain) (srcBase dstBase : BitVec 64)
      (m₁ : Nat)
      (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
      (hrem_pos : 1 ≤ rem.length)
      (hrem_len : remG.length = rem.length)
      (hconv_len : convG.length = conv.length)
      (hm1_le : m₁ ≤ conv.length)
      (hbound : (conv.length + rem.length) * 112 < 2 ^ 63)
      (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 512#64)
      (hrun : s.status = .Running)
      (hsp : s.sp = s0.sp - 288#64)
      (htr : TraceCalleeSaved s s0)
      (hfp : s.readReg64 .fp = s0.sp - 96#64)
      (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (rem.length * 112))
      (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
      (hx12 : s.readReg64 .x12 = s0.sp - 160#64)
      (hx13 : s.readReg64 .x13 = s0.sp - 208#64)
      (hx14 : s.readReg64 .x14 = s0.sp - 260#64)
      (hx15 : s.readReg64 .x15 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
      (hx16 : s.readReg64 .x16 = srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112) + 56#64),
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr chainIntoPbName + 672#64)
        s
        (memRegion srcBase ((conv.length - m₁) * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112))
            (remG.zip rem) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) (rem.length * 112) ∗
          intoPbScratchAt s0 gChain cChain)
        (fun sf Pm =>
          (Pm ⊢ memRegion srcBase ((conv.length - m₁ + rem.length) * 112) ∗
            arrayAt (chainEpochPBAt A) 112 dstBase
              (((convG ++ remG).map toChainEpochPBGhost).zip ((conv ++ rem).map chainEpochIntoPb)) ∗
            intoPbScratchAt s0 gChain cChain) ∧
          sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
          sf.readReg64 .fp = s0.sp - 96#64 ∧
          sf.readReg64 .x0 = s.readReg64 .x0 ∧
          sf.readReg64 .x2 = s.readReg64 .x2 ∧
          sf.readReg64 .x3 = s.readReg64 .x3 ∧
          sf.readReg64 .x8 = s.readReg64 .x8 ∧
          sf.readReg64 .x11 = s.readReg64 .x11 ∧
          CalleeSavedPreserved s sf) := by
  induction rem with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ hpos; simp at hpos
  | cons ep rest ih =>
    intro remG convG conv s0 s gChain cChain srcBase dstBase m₁ hsp0_align _ hrem_len hconv_len hm1_le hbound
      hpc hrun hsp htr hfp hx9 hx10 hx12 hx13 hx14 hx15 hx16
    cases remG with
    | nil => simp at hrem_len
    | cons g restG =>
      have hrest_len : restG.length = rest.length := by simpa using hrem_len
      have hlen_cons : (ep :: rest).length = 1 + rest.length := by simp [Nat.add_comm]
      have hsplit_dst :
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) =
            memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
            memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) := by
        rw [hlen_cons, Nat.add_mul, Nat.one_mul]
        exact ProofLib.memRegion_split' (b := dstBase + BitVec.ofNat 64 (conv.length * 112))
          (n := 112) (k := rest.length * 112)
          (b' := dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
          rfl (by rw [add_curPtr_112]) (by omega)
      have hstep := intoPb_loop2_step (A := A) (b := b) (ext := ext)
        s0 s gChain cChain srcBase dstBase convG conv g ep restG rest m₁ hsp0_align
        hconv_len hrest_len hm1_le (by rw [hlen_cons] at hbound; omega)
        hpc hrun hsp htr hfp (by rw [hlen_cons] at hx9; exact hx9)
        hx10 hx12 hx13 hx14 hx15 hx16
      change SepWP _ _ _
        (memRegion srcBase ((conv.length - m₁) * 112) ∗
          (chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112)) ∗
            arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112) + 112#64)
              (restG.zip rest)) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) ∗
          intoPbScratchAt s0 gChain cChain) _
      rw [add_curPtr_112 srcBase (conv.length - m₁), hsplit_dst]
      cases rest with
      | nil =>
        have hrestG_nil : restG = [] := List.eq_nil_of_length_eq_zero hrest_len
        subst hrestG_nil
        simp only [List.isEmpty_nil, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
        rintro sf Pm _ _ ⟨hPm, hsp1, htr1, hfp1, hx0_1, hx2_1, hx3_1, hx8_1, _, _, hx11_1, _, _, _, _, _, hcs1⟩
        refine ⟨Entails.trans hPm ?_, hsp1, htr1, hfp1, hx0_1, hx2_1, hx3_1, hx8_1, hx11_1, hcs1⟩
        simp only [List.zip_nil_right, arrayAt, List.length_nil, Nat.mul_zero, Nat.zero_mul,
          memRegion_zero, emp_sepConj, sepConj_emp, List.length_singleton, List.append_assoc,
          List.nil_append]
        exact Entails.of_eq (by ac_rfl)
      | cons ep2 rest2 =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep ?_)
        rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hfpm, hx0m, hx2m, hx3m, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m, hx14m, hx15m, hx16m, hcsm⟩
        have hconv1 : (conv ++ [ep]).length = conv.length + 1 := by
          rw [List.length_append, List.length_singleton]
        have hsub_add : conv.length + 1 - m₁ = conv.length - m₁ + 1 := by omega
        have hbound' : ((conv ++ [ep]).length + (ep2 :: rest2).length) * 112 < 2 ^ 63 := by
          rw [hconv1]; rw [hlen_cons] at hbound; omega
        have hih := ih restG (convG ++ [g]) (conv ++ [ep]) s0 sm gChain cChain srcBase dstBase m₁
          hsp0_align (by simp) hrest_len (by simp [hconv_len])
          (by rw [hconv1]; omega) hbound'
          hpcm hrunm hspm htrm hfpm hx9m hx10m hx12m hx13m hx14m
          (by rw [hconv1]; exact hx15m)
          (by rw [hconv1, hsub_add]; exact hx16m)
        simp only [hconv1, hsub_add, List.append_assoc, List.singleton_append] at hih
        refine SepWP.weaken_pre (Entails.trans hPm (Entails.of_eq (by ac_rfl))) (SepWP.mono hih ?_)
        rintro sf Pf _ _ ⟨hPf, hsp2, htr2, hfp2, hx0_2, hx2_2, hx3_2, hx8_2, hx11_2, hcs2⟩
        have hlen_add : conv.length - m₁ + 1 + (ep2 :: rest2).length =
            conv.length - m₁ + (ep :: ep2 :: rest2).length := by
          simp [Nat.add_assoc, Nat.add_comm 1]
        rw [hlen_add] at hPf
        exact ⟨hPf, hsp2, htr2, hfp2, hx0_2.trans hx0m, hx2_2.trans hx2m, hx3_2.trans hx3m,
          hx8_2.trans hx8m, hx11_2.trans hx11m,
          CalleeSavedPreserved.trans hcsm hcs2⟩

/-! ## Relocatable `[LibsignalPlacement]` Epilogue and Loop Proofs (Block `365`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` epilogue of `<spqr::chain::Chain>::into_pb` at `+820`. -/
theorem chainIntoPb_epilogue_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (x : ChainIntoPbCall) (s0 s : State) (newLinksPtr : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63)
    (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hl_new_ne : newLinksPtr ≠ 0)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63)
    (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_365).base + 820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = 0#64)
    (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = newLinksPtr)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗
        chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  have hdrop_emp1 := pool_entails_empty_arrayAt_pool_intoPb A (chainEpoch A) 112 x.gChain.linksPtr
  dsimp only [dropChainEpochSliceSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hdrop hdealloc hpc ⊢
  refine seq_clean (mid := (blkPl_365).base + 840#64)
    (P_mid := memRegion x.out 80 ∗
      chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      arrayAt (chainEpochPBAt A) 112 newLinksPtr
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
      (if (x.gChain.linksCap == 0#64) = true then emp
       else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
         memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗
      intoPbScratchAt s0 x.gChain x.chain ∗
      calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
      sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
      sm.readReg64 .x23 = 0#64 ∧
      sm.readReg64 .x24 = newLinksPtr ∧
      sm.readReg64 .x25 = x.chain.sendEpoch ∧
      sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      sm.readReg64 .x27 = x.chain.currentEpoch ∧
      sm.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · refine SepWP.focus_weaken hdrop_emp1 (by sep_focus) ?_
    unfold intoPbScratchAt
    wp_steps
    wp_call hdrop ⟨x.gChain.linksPtr, []⟩
    rw [hsp, memRegion_zero, emp_sepConj]
    wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
    refine seq_clean (mid := (blkPl_365).base + 852#64)
      (P_mid := memRegion x.out 80 ∗
        chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x24 = newLinksPtr ∧
        sm.readReg64 .x25 = x.chain.sendEpoch ∧
        sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        sm.readReg64 .x27 = x.chain.currentEpoch ∧
        sm.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · refine SepWP.focus_weaken hdrop_emp1 (by sep_focus) ?_
      wp_steps
      wp_call hdrop ⟨x.gChain.linksPtr, []⟩
      rw [hsp1, memRegion_zero, emp_sepConj]
      wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2⟩
      refine seq_clean (mid := (blkPl_365).base + 880#64)
        (P_mid := memRegion x.out 80 ∗
          chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          arrayAt (chainEpochPBAt A) 112 newLinksPtr
            ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
          linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗
          intoPbScratchAt s0 x.gChain x.chain ∗
          calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32)
        (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x24 = newLinksPtr ∧
          sm.readReg64 .x25 = x.chain.sendEpoch ∧
          sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
          sm.readReg64 .x27 = x.chain.currentEpoch) ?_ ?_
      · unfold intoPbScratchAt
        by_cases hcap : x.gChain.linksCap = 0
        · have hcapb : (x.gChain.linksCap == 0#64) = true := beq_iff_eq.mpr hcap
          simp only [hcapb, ↓reduceIte, emp_sepConj, sepConj_emp]
          wp_steps
          wp_done
        · have hcapb : (x.gChain.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
          have hcap_pos : x.gChain.linksCap.toNat * 112 > 0 := by
            have hpos := BitVec.toNat_pos_of_ne_zero hcap; omega
          have hsz_bv := cap_mul_112_shift_eq x.gChain.linksCap hl_cap_lt
          have hsplit_stack := stackAt_dropStack32_split_allocHook (s0.sp - 288#64)
          simp only [hcapb, Bool.false_eq_true, ↓reduceIte]
          rw [hsplit_stack]
          wp_steps
          wp_call hdealloc (x.gChain.linksPtr, x.gChain.linksCap.toNat * 112, 8)
          rw [hsp2, ← hsplit_stack]
          wp_done
      · rintro sm hpcm hrunm ⟨hspm, htrm, hfpm, hx19m, hx20m, hx21m, hx22m, hx24m, hx25m, hx26m, hx27m⟩
        rw [memRegion_80_split_out x.out]
        wp_pull_exists
        unfold chainHeaderCellsAt calleeSavedFromPbAt
        wp_steps
        refine SepWP.focus_weaken
          (restore_stack_chainIntoPb s0 x.gChain x.chain)
          (by unfold calleeSavedFromPbAt; sep_focus) ?_
        refine SepWP.focus_weaken
          (chainHeaderCellsAt_entails_memRegion_88 x.chainPtr x.gChain x.chain)
          (by unfold chainHeaderCellsAt; sep_focus) ?_
        refine SepWP.focus_weaken
          (Entails.trans
            (chainPBAt_pack_out A x.out newLinksPtr x.gChain x.chain hlen hl_new_lt hl_new_ne hn1 hn2 hn3)
            (chainPBAt_entails_chainPBIntoPinnedAt A x.out newLinksPtr x.gChain x.chain))
          (by sep_focus) ?_
        unfold intoPbPinnedRetPost
        wp_done

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` single iteration of Loop 1 (`+300 .. +456`). -/
theorem intoPb_loop1_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (s0 s : State) (gChain : ChainGhost) (cChain : Chain)
    (srcBase dstBase : BitVec 64)
    (convG : List ChainEpochGhost) (conv : List ChainEpoch)
    (g : ChainEpochGhost) (ep : ChainEpoch)
    (restG : List ChainEpochGhost) (rest : List ChainEpoch)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hconv_len : convG.length = conv.length)
    (hrest_len : restG.length = rest.length)
    (hbound : (conv.length + 1 + rest.length) * 112 < 2 ^ 63)
    (hpc : s.pc = (blkPl_365).base + 300#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
    (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 ((1 + rest.length) * 112))
    (hx13 : s.readReg64 .x13 = s0.sp - 160#64)
    (hx14 : s.readReg64 .x14 = s0.sp - 208#64)
    (hx15 : s.readReg64 .x15 = s0.sp - 260#64)
    (hx16 : s.readReg64 .x16 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
    (hx17 : s.readReg64 .x17 = srcBase + BitVec.ofNat 64 (conv.length * 112) + 56#64) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H)
      (if rest.isEmpty then (blkPl_365).base + 460#64
       else (blkPl_365).base + 300#64)
      s
      (memRegion srcBase (conv.length * 112) ∗
        chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 (conv.length * 112)) ∗
        arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
          (restG.zip rest) ∗
        arrayAt (chainEpochPBAt A) 112 dstBase
          ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
        memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
        memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
        intoPbScratchAt s0 gChain cChain)
      (fun sf Pm =>
        (Pm ⊢ memRegion srcBase ((conv.length + 1) * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
            (restG.zip rest) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            (((convG ++ [g]).map toChainEpochPBGhost).zip ((conv ++ [ep]).map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
          intoPbScratchAt s0 gChain cChain) ∧
        sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x3 = s.readReg64 .x3 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x9 = s.readReg64 .x9 ∧
        sf.readReg64 .x10 = s0.sp - 160#64 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x12 = BitVec.ofNat 64 (rest.length * 112) ∧
        sf.readReg64 .x13 = s0.sp - 160#64 ∧
        sf.readReg64 .x14 = s0.sp - 208#64 ∧
        sf.readReg64 .x15 = s0.sp - 260#64 ∧
        sf.readReg64 .x16 = dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112) + 52#64 ∧
        sf.readReg64 .x17 = srcBase + BitVec.ofNat 64 ((conv.length + 1) * 112) + 56#64 ∧
        CalleeSavedPreserved s sf) := by
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  refine SepWP.focus_rw
    (memRegion_112_split_dst (dstBase + BitVec.ofNat 64 (conv.length * 112)))
    (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.focus_rw
    (by rfl : intoPbScratchAt s0 gChain cChain =
      ((s0.sp - 288#64) ↦₆₄ cChain.currentEpoch) ∗
      ((s0.sp - 280#64) ↦₆₄ cChain.sendEpoch) ∗
      ((s0.sp - 272#64) ↦₆₄ gChain.linksCap) ∗
      intoPbLoopScratchAt s0)
    (by sep_focus) ?_
  unfold intoPbLoopScratchAt
  wp_pull_exists
  refine SepWP.focus_weaken
    (chainEpochAt_unpack_cells A g ep (srcBase + BitVec.ofNat 64 (conv.length * 112)))
    (by sep_focus) ?_
  wp_focus_pure
  rintro ⟨hs1, hs2, hs3, hs4, hs5, hs6, hr1, hr2, hr3, hr4, hr5, hr6⟩
  wp_steps
  refine SepWP.focus_weaken
    (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
      (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
      (BitVec.ofNat 64 ep.recv.prev.data.length)))
    (by sep_focus) ?_
  cases rest with
  | nil =>
    simp only [List.isEmpty_nil, List.length_nil, Nat.mul_zero, ↓reduceIte]
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 (conv.length * 112))
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
        ep.send.ctr ep.recv.ctr)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_append_112 srcBase conv.length (by omega)))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
        g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
      (by sep_focus) ?_
    wp_done
  | cons ep2 rest2 =>
    have hne : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) != 112#64) = true := by
      have hbeq : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) ==
          BitVec.ofNat 64 (1 * 112)) = false :=
        ofNat_mul_112_beq_false (by simp) (by simp at hbound ⊢; omega) (by decide)
      simpa [bne] using hbeq
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 (conv.length * 112))
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
        ep.send.ctr ep.recv.ctr)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_append_112 srcBase conv.length (by omega)))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
        g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
      (by sep_focus) ?_
    wp_done

/-- Relocatable `[LibsignalPlacement]` inductive Loop 1 theorem (`+300 .. +460`) over `rem = (g, ep) :: rest`. -/
theorem intoPb_loop1_run_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (rem : List ChainEpoch) :
    ∀ (remG : List ChainEpochGhost) (convG : List ChainEpochGhost) (conv : List ChainEpoch)
      (s0 s : State) (gChain : ChainGhost) (cChain : Chain) (srcBase dstBase : BitVec 64)
      (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
      (hrem_pos : 1 ≤ rem.length)
      (hrem_len : remG.length = rem.length)
      (hconv_len : convG.length = conv.length)
      (hbound : (conv.length + rem.length) * 112 < 2 ^ 63)
      (hpc : s.pc = (blkPl_365).base + 300#64)
      (hrun : s.status = .Running)
      (hsp : s.sp = s0.sp - 288#64)
      (htr : TraceCalleeSaved s s0)
      (hfp : s.readReg64 .fp = s0.sp - 96#64)
      (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
      (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 (rem.length * 112))
      (hx13 : s.readReg64 .x13 = s0.sp - 160#64)
      (hx14 : s.readReg64 .x14 = s0.sp - 208#64)
      (hx15 : s.readReg64 .x15 = s0.sp - 260#64)
      (hx16 : s.readReg64 .x16 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
      (hx17 : s.readReg64 .x17 = srcBase + BitVec.ofNat 64 (conv.length * 112) + 56#64),
      SepWP ((blkPC_365).rebase (blkPl_365).base H)
        ((blkPl_365).base + 460#64)
        s
        (memRegion srcBase (conv.length * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 (conv.length * 112))
            (remG.zip rem) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) (rem.length * 112) ∗
          intoPbScratchAt s0 gChain cChain)
        (fun sf Pm =>
          (Pm ⊢ memRegion srcBase ((conv.length + rem.length) * 112) ∗
            arrayAt (chainEpochPBAt A) 112 dstBase
              (((convG ++ remG).map toChainEpochPBGhost).zip ((conv ++ rem).map chainEpochIntoPb)) ∗
            intoPbScratchAt s0 gChain cChain) ∧
          sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
          sf.readReg64 .fp = s0.sp - 96#64 ∧
          sf.readReg64 .x0 = s.readReg64 .x0 ∧
          sf.readReg64 .x3 = s.readReg64 .x3 ∧
          sf.readReg64 .x8 = s.readReg64 .x8 ∧
          sf.readReg64 .x9 = s.readReg64 .x9 ∧
          sf.readReg64 .x10 = s0.sp - 160#64 ∧
          sf.readReg64 .x11 = s.readReg64 .x11 ∧
          CalleeSavedPreserved s sf) := by
  induction rem with
  | nil => intro _ _ _ _ _ _ _ _ _ _ hpos; simp at hpos
  | cons ep rest ih =>
    intro remG convG conv s0 s gChain cChain srcBase dstBase hsp0_align _ hrem_len hconv_len hbound
      hpc hrun hsp htr hfp hx10 hx12 hx13 hx14 hx15 hx16 hx17
    cases remG with
    | nil => simp at hrem_len
    | cons g restG =>
      have hrest_len : restG.length = rest.length := by simpa using hrem_len
      have hlen_cons : (ep :: rest).length = 1 + rest.length := by simp [Nat.add_comm]
      have hsplit_dst :
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) =
            memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
            memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) := by
        rw [hlen_cons, Nat.add_mul, Nat.one_mul]
        exact ProofLib.memRegion_split' (b := dstBase + BitVec.ofNat 64 (conv.length * 112))
          (n := 112) (k := rest.length * 112)
          (b' := dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
          rfl (by rw [add_curPtr_112]) (by omega)
      have hstep := intoPb_loop1_step_placed (A := A) (H := H)
        s0 s gChain cChain srcBase dstBase convG conv g ep restG rest hsp0_align
        hconv_len hrest_len (by rw [hlen_cons] at hbound; omega)
        hpc hrun hsp htr hfp hx10 (by rw [hlen_cons] at hx12; exact hx12)
        hx13 hx14 hx15 hx16 hx17
      change SepWP _ _ _
        (memRegion srcBase (conv.length * 112) ∗
          (chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 (conv.length * 112)) ∗
            arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 (conv.length * 112) + 112#64)
              (restG.zip rest)) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) ∗
          intoPbScratchAt s0 gChain cChain) _
      rw [add_curPtr_112 srcBase conv.length, hsplit_dst]
      cases rest with
      | nil =>
        have hrestG_nil : restG = [] := List.eq_nil_of_length_eq_zero hrest_len
        subst hrestG_nil
        simp only [List.isEmpty_nil, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
        rintro sf Pm _ _ ⟨hPm, hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, _, _, _, _, _, _, hcs1⟩
        refine ⟨Entails.trans hPm ?_, hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, hcs1⟩
        simp only [List.zip_nil_right, arrayAt, List.length_nil, Nat.mul_zero, Nat.zero_mul,
          memRegion_zero, emp_sepConj, sepConj_emp, List.length_singleton, List.append_assoc,
          List.nil_append]
        exact Entails.of_eq (by ac_rfl)
      | cons ep2 rest2 =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep ?_)
        rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hfpm, hx0m, hx3m, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m, hx14m, hx15m, hx16m, hx17m, hcsm⟩
        have hconv1 : (conv ++ [ep]).length = conv.length + 1 := by
          rw [List.length_append, List.length_singleton]
        have hbound' : ((conv ++ [ep]).length + (ep2 :: rest2).length) * 112 < 2 ^ 63 := by
          rw [hconv1]; rw [hlen_cons] at hbound; omega
        have hih := ih restG (convG ++ [g]) (conv ++ [ep]) s0 sm gChain cChain srcBase dstBase
          hsp0_align (by simp) hrest_len (by simp [hconv_len]) hbound'
          hpcm hrunm hspm htrm hfpm hx10m hx12m hx13m hx14m hx15m
          (by rw [hconv1]; exact hx16m)
          (by rw [hconv1]; exact hx17m)
        simp only [hconv1, List.append_assoc, List.singleton_append] at hih
        refine SepWP.weaken_pre (Entails.trans hPm (Entails.of_eq (by ac_rfl))) (SepWP.mono hih ?_)
        rintro sf Pf _ _ ⟨hPf, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
        have hlen_add : conv.length + 1 + (ep2 :: rest2).length = conv.length + (ep :: ep2 :: rest2).length := by
          simp [Nat.add_assoc, Nat.add_comm 1]
        rw [hlen_add] at hPf
        exact ⟨hPf, hsp2, htr2, hfp2, hx0_2.trans hx0m, hx3_2.trans hx3m, hx8_2.trans hx8m,
          hx9_2.trans hx9m, hx10_2, hx11_2.trans hx11m,
          CalleeSavedPreserved.trans hcsm hcs2⟩

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` single iteration of Loop 2 (`+512 .. +668`). -/
theorem intoPb_loop2_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (s0 s : State) (gChain : ChainGhost) (cChain : Chain)
    (srcBase dstBase : BitVec 64)
    (convG : List ChainEpochGhost) (conv : List ChainEpoch)
    (g : ChainEpochGhost) (ep : ChainEpoch)
    (restG : List ChainEpochGhost) (rest : List ChainEpoch)
    (m₁ : Nat)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hconv_len : convG.length = conv.length)
    (hrest_len : restG.length = rest.length)
    (hm1_le : m₁ ≤ conv.length)
    (hbound : (conv.length + 1 + rest.length) * 112 < 2 ^ 63)
    (hpc : s.pc = (blkPl_365).base + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 ((1 + rest.length) * 112))
    (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
    (hx12 : s.readReg64 .x12 = s0.sp - 160#64)
    (hx13 : s.readReg64 .x13 = s0.sp - 208#64)
    (hx14 : s.readReg64 .x14 = s0.sp - 260#64)
    (hx15 : s.readReg64 .x15 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
    (hx16 : s.readReg64 .x16 = srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112) + 56#64) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H)
      (if rest.isEmpty then (blkPl_365).base + 672#64
       else (blkPl_365).base + 512#64)
      s
      (memRegion srcBase ((conv.length - m₁) * 112) ∗
        chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112)) ∗
        arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁ + 1) * 112))
          (restG.zip rest) ∗
        arrayAt (chainEpochPBAt A) 112 dstBase
          ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
        memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
        memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
        intoPbScratchAt s0 gChain cChain)
      (fun sf Pm =>
        (Pm ⊢ memRegion srcBase ((conv.length - m₁ + 1) * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁ + 1) * 112))
            (restG.zip rest) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            (((convG ++ [g]).map toChainEpochPBGhost).zip ((conv ++ [ep]).map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
          intoPbScratchAt s0 gChain cChain) ∧
        sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x2 = s.readReg64 .x2 ∧
        sf.readReg64 .x3 = s.readReg64 .x3 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x9 = BitVec.ofNat 64 (rest.length * 112) ∧
        sf.readReg64 .x10 = s0.sp - 160#64 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x12 = s0.sp - 160#64 ∧
        sf.readReg64 .x13 = s0.sp - 208#64 ∧
        sf.readReg64 .x14 = s0.sp - 260#64 ∧
        sf.readReg64 .x15 = dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112) + 52#64 ∧
        sf.readReg64 .x16 = srcBase + BitVec.ofNat 64 ((conv.length - m₁ + 1) * 112) + 56#64 ∧
        CalleeSavedPreserved s sf) := by
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  refine SepWP.focus_rw
    (memRegion_112_split_dst (dstBase + BitVec.ofNat 64 (conv.length * 112)))
    (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.focus_rw
    (by rfl : intoPbScratchAt s0 gChain cChain =
      ((s0.sp - 288#64) ↦₆₄ cChain.currentEpoch) ∗
      ((s0.sp - 280#64) ↦₆₄ cChain.sendEpoch) ∗
      ((s0.sp - 272#64) ↦₆₄ gChain.linksCap) ∗
      intoPbLoopScratchAt s0)
    (by sep_focus) ?_
  unfold intoPbLoopScratchAt
  wp_pull_exists
  refine SepWP.focus_weaken
    (chainEpochAt_unpack_cells A g ep (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112)))
    (by sep_focus) ?_
  wp_focus_pure
  rintro ⟨hs1, hs2, hs3, hs4, hs5, hs6, hr1, hr2, hr3, hr4, hr5, hr6⟩
  wp_steps
  refine SepWP.focus_weaken
    (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
      (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
      (BitVec.ofNat 64 ep.recv.prev.data.length)))
    (by sep_focus) ?_
  cases rest with
  | nil =>
    simp only [List.isEmpty_nil, List.length_nil, Nat.mul_zero, ↓reduceIte]
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112))
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
        ep.send.ctr ep.recv.ctr)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_append_112 srcBase (conv.length - m₁) (by omega)))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
        g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
      (by sep_focus) ?_
    wp_done
  | cons ep2 rest2 =>
    have hne : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) != 112#64) = true := by
      have hbeq : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) ==
          BitVec.ofNat 64 (1 * 112)) = false :=
        ofNat_mul_112_beq_false (by simp) (by simp at hbound ⊢; omega) (by decide)
      simpa [bne] using hbeq
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112))
        g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
        g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
        g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
        g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
        ep.send.ctr ep.recv.ctr)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_append_112 srcBase (conv.length - m₁) (by omega)))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
        g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
      (by sep_focus) ?_
    wp_done

/-- Relocatable `[LibsignalPlacement]` inductive Loop 2 theorem (`+512 .. +672`) over `rem = (g, ep) :: rest`. -/
theorem intoPb_loop2_run_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (rem : List ChainEpoch) :
    ∀ (remG : List ChainEpochGhost) (convG : List ChainEpochGhost) (conv : List ChainEpoch)
      (s0 s : State) (gChain : ChainGhost) (cChain : Chain) (srcBase dstBase : BitVec 64)
      (m₁ : Nat)
      (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
      (hrem_pos : 1 ≤ rem.length)
      (hrem_len : remG.length = rem.length)
      (hconv_len : convG.length = conv.length)
      (hm1_le : m₁ ≤ conv.length)
      (hbound : (conv.length + rem.length) * 112 < 2 ^ 63)
      (hpc : s.pc = (blkPl_365).base + 512#64)
      (hrun : s.status = .Running)
      (hsp : s.sp = s0.sp - 288#64)
      (htr : TraceCalleeSaved s s0)
      (hfp : s.readReg64 .fp = s0.sp - 96#64)
      (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (rem.length * 112))
      (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
      (hx12 : s.readReg64 .x12 = s0.sp - 160#64)
      (hx13 : s.readReg64 .x13 = s0.sp - 208#64)
      (hx14 : s.readReg64 .x14 = s0.sp - 260#64)
      (hx15 : s.readReg64 .x15 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
      (hx16 : s.readReg64 .x16 = srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112) + 56#64),
      SepWP ((blkPC_365).rebase (blkPl_365).base H)
        ((blkPl_365).base + 672#64)
        s
        (memRegion srcBase ((conv.length - m₁) * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112))
            (remG.zip rem) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) (rem.length * 112) ∗
          intoPbScratchAt s0 gChain cChain)
        (fun sf Pm =>
          (Pm ⊢ memRegion srcBase ((conv.length - m₁ + rem.length) * 112) ∗
            arrayAt (chainEpochPBAt A) 112 dstBase
              (((convG ++ remG).map toChainEpochPBGhost).zip ((conv ++ rem).map chainEpochIntoPb)) ∗
            intoPbScratchAt s0 gChain cChain) ∧
          sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
          sf.readReg64 .fp = s0.sp - 96#64 ∧
          sf.readReg64 .x0 = s.readReg64 .x0 ∧
          sf.readReg64 .x2 = s.readReg64 .x2 ∧
          sf.readReg64 .x3 = s.readReg64 .x3 ∧
          sf.readReg64 .x8 = s.readReg64 .x8 ∧
          sf.readReg64 .x11 = s.readReg64 .x11 ∧
          CalleeSavedPreserved s sf) := by
  induction rem with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ hpos; simp at hpos
  | cons ep rest ih =>
    intro remG convG conv s0 s gChain cChain srcBase dstBase m₁ hsp0_align _ hrem_len hconv_len hm1_le hbound
      hpc hrun hsp htr hfp hx9 hx10 hx12 hx13 hx14 hx15 hx16
    cases remG with
    | nil => simp at hrem_len
    | cons g restG =>
      have hrest_len : restG.length = rest.length := by simpa using hrem_len
      have hlen_cons : (ep :: rest).length = 1 + rest.length := by simp [Nat.add_comm]
      have hsplit_dst :
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) =
            memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
            memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) := by
        rw [hlen_cons, Nat.add_mul, Nat.one_mul]
        exact ProofLib.memRegion_split' (b := dstBase + BitVec.ofNat 64 (conv.length * 112))
          (n := 112) (k := rest.length * 112)
          (b' := dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
          rfl (by rw [add_curPtr_112]) (by omega)
      have hstep := intoPb_loop2_step_placed (A := A) (H := H)
        s0 s gChain cChain srcBase dstBase convG conv g ep restG rest m₁ hsp0_align
        hconv_len hrest_len hm1_le (by rw [hlen_cons] at hbound; omega)
        hpc hrun hsp htr hfp (by rw [hlen_cons] at hx9; exact hx9)
        hx10 hx12 hx13 hx14 hx15 hx16
      change SepWP _ _ _
        (memRegion srcBase ((conv.length - m₁) * 112) ∗
          (chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112)) ∗
            arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112) + 112#64)
              (restG.zip rest)) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) ∗
          intoPbScratchAt s0 gChain cChain) _
      rw [add_curPtr_112 srcBase (conv.length - m₁), hsplit_dst]
      cases rest with
      | nil =>
        have hrestG_nil : restG = [] := List.eq_nil_of_length_eq_zero hrest_len
        subst hrestG_nil
        simp only [List.isEmpty_nil, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
        rintro sf Pm _ _ ⟨hPm, hsp1, htr1, hfp1, hx0_1, hx2_1, hx3_1, hx8_1, _, _, hx11_1, _, _, _, _, _, hcs1⟩
        refine ⟨Entails.trans hPm ?_, hsp1, htr1, hfp1, hx0_1, hx2_1, hx3_1, hx8_1, hx11_1, hcs1⟩
        simp only [List.zip_nil_right, arrayAt, List.length_nil, Nat.mul_zero, Nat.zero_mul,
          memRegion_zero, emp_sepConj, sepConj_emp, List.length_singleton, List.append_assoc,
          List.nil_append]
        exact Entails.of_eq (by ac_rfl)
      | cons ep2 rest2 =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep ?_)
        rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hfpm, hx0m, hx2m, hx3m, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m, hx14m, hx15m, hx16m, hcsm⟩
        have hconv1 : (conv ++ [ep]).length = conv.length + 1 := by
          rw [List.length_append, List.length_singleton]
        have hsub_add : conv.length + 1 - m₁ = conv.length - m₁ + 1 := by omega
        have hbound' : ((conv ++ [ep]).length + (ep2 :: rest2).length) * 112 < 2 ^ 63 := by
          rw [hconv1]; rw [hlen_cons] at hbound; omega
        have hih := ih restG (convG ++ [g]) (conv ++ [ep]) s0 sm gChain cChain srcBase dstBase m₁
          hsp0_align (by simp) hrest_len (by simp [hconv_len])
          (by rw [hconv1]; omega) hbound'
          hpcm hrunm hspm htrm hfpm hx9m hx10m hx12m hx13m hx14m
          (by rw [hconv1]; exact hx15m)
          (by rw [hconv1, hsub_add]; exact hx16m)
        simp only [hconv1, hsub_add, List.append_assoc, List.singleton_append] at hih
        refine SepWP.weaken_pre (Entails.trans hPm (Entails.of_eq (by ac_rfl))) (SepWP.mono hih ?_)
        rintro sf Pf _ _ ⟨hPf, hsp2, htr2, hfp2, hx0_2, hx2_2, hx3_2, hx8_2, hx11_2, hcs2⟩
        have hlen_add : conv.length - m₁ + 1 + (ep2 :: rest2).length =
            conv.length - m₁ + (ep :: ep2 :: rest2).length := by
          simp [Nat.add_assoc, Nat.add_comm 1]
        rw [hlen_add] at hPf
        exact ⟨hPf, hsp2, htr2, hfp2, hx0_2.trans hx0m, hx2_2.trans hx2m, hx3_2.trans hx3m,
          hx8_2.trans hx8m, hx11_2.trans hx11m,
          CalleeSavedPreserved.trans hcsm hcs2⟩

end CryptoVerification.SpqrV1.ChainProofs
