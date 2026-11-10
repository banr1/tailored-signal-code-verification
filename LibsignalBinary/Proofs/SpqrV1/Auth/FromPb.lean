/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Auth.Repr
public import LibsignalBinary.Proofs.SpqrV1.Auth.SpqrAuthCodeSym
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::authenticator::Authenticator>::from_pb`

Verifies `<spqr::authenticator::Authenticator>::from_pb` (`0x55208`, block 330) against
`Authenticator.fromPb` on `tripleRatchetProgAtExt` and under `[LibsignalPlacement]`,
together with `Option<ProtoAuthenticator>` niche-tag bridge lemmas and stack-frame
helpers for `Authenticator::update`.
-/

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

private gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x4fe10 → 0x4fed4]

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::from_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-- Instruction-fetch tactic for `[k0, k0 + len)` inside `Authenticator::from_pb` (`0x55208`). -/
macro "from_pb_fetches_range " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalSessionBin $b $H $hfn 0x4fe10 $k0 $len)

/-- Stack budget of `Authenticator::from_pb` (`allocHookStack + 64`). -/
abbrev authFromPbStack : Nat := allocHookStack + 64

private theorem stackAt_authFromPb (sp : BitVec 64) :
    stackAt sp authFromPbStack =
      stackAt (sp - 64#64) allocHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗
        ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4096 8 (by decide)
  change stackAt sp authFromPbStack =
    stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗
        ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

private theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        (a ↦₆₄ w5) ∗ ((a + 8#64) ↦₆₄ w4) ∗ ((a + 16#64) ↦₆₄ w3) ∗
        ((a + 24#64) ↦₆₄ w2) ∗ ((a + 32#64) ↦₆₄ w1) ∗ ((a + 40#64) ↦₆₄ w0)) := by
  rw [ProofLib.memRegion_split a 24 24 (by decide), memRegion_24, memRegion_24]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem cap_ne_zero_of_pos {cap : BitVec 64} {n : Nat} (hpos : 0 < n) (hle : n ≤ cap.toNat) :
    cap ≠ 0#64 := by
  intro h
  subst h
  change n ≤ 0 at hle
  omega

private theorem pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

private theorem vecU8_of_zero (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A v [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) by ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

private theorem vecU8_of_pos (A : RustAlloc) (v p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      vecU8 A v bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht
    omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 bs.length))
  refine Entails.trans ?_ (Entails.sepExists_intro p')
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

private theorem out_add24_add8 (out : BitVec 64) :
    (out + 24#64) + 8#64 = out + 32#64 := by bv_omega

private theorem out_add24_add16 (out : BitVec 64) :
    (out + 24#64) + 16#64 = out + 40#64 := by bv_omega

/-! ## Specifications -/

/-- Pinned ghost arguments for `Authenticator::from_pb`. -/
structure AuthFromPbPinnedGhost where
  /-- Sret pointer (`x0`, 48-byte `Authenticator` output). -/
  out : BitVec 64
  /-- Pointer to `&spqr::proto::pq_ratchet::Authenticator` (`x1`, 48 bytes). -/
  pbA : BitVec 64
  /-- Ghost `(cap, ptr)` pins of `pb`. -/
  g : AuthenticatorPBGhost
  pb : ProtoAuthenticator

/-- Unpinned ghost arguments for `Authenticator::from_pb`. -/
structure AuthFromPbGhost where
  /-- Sret pointer (`x0`, 48-byte `Authenticator` output). -/
  out : BitVec 64
  /-- Pointer to `&spqr::proto::pq_ratchet::Authenticator` (`x1`, 48 bytes). -/
  pbA : BitVec 64
  pb : ProtoAuthenticator

/-- Pinned specification of `<spqr::authenticator::Authenticator>::from_pb` (`0x55208`):
clones `pb.root_key` and `pb.mac_key` into `authenticatorAt A x.out (Authenticator.fromPb x.pb)`
while preserving `authenticatorPBPinnedAt A x.g x.pbA x.pb` (or panicking on OOM). -/
def authFromPbPinnedSpec (A : RustAlloc) : Spec AuthFromPbPinnedGhost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA⌝ ∗
      memRegion x.out 48 ∗
      authenticatorPBPinnedAt A x.g x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp authFromPbStack
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorAt A x.out (Authenticator.fromPb x.pb) ∗
      authenticatorPBPinnedAt A x.g x.pbA x.pb ∗
      A.pool ∗ stackAt s0.sp authFromPbStack
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned specification of `Authenticator::from_pb`. -/
def authFromPbSpec (A : RustAlloc) : Spec AuthFromPbGhost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA⌝ ∗
      memRegion x.out 48 ∗
      authenticatorPBAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp authFromPbStack
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorAt A x.out (Authenticator.fromPb x.pb) ∗
      authenticatorPBAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s0.sp authFromPbStack
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `.inImage img` contract proposition for `authFromPbSpec A`. -/
def AuthFromPbOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authFromPbName)
    ((authFromPbSpec A).inImage img)

set_option maxHeartbeats 1600000 in
private theorem auth_from_pb_pinned_ok_core {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x4fe10)))
      sessionShimSpec)
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - 0x4fe10)))
      (rustAllocSpec A))
    (hmc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - 0x4fe10)))
      (withStack sessionMemcpyRegionSpec allocHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName)
      (authFromPbPinnedSpec A) := by
  simp only [authFromPbPinnedSpec, authenticatorPBPinnedAt, authenticatorAt, Authenticator.fromPb,
    vecU8At, vecHeader, memRegion_48_cells, stackAt_authFromPb,
    out_add24_add8, out_add24_add16, BitVec.ofNat_eq_ofNat,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  have hfn : libsignalSessionCode.fnOff authFromPbName = 0x4fe10 :=
    libsignalSessionCode_fnOff_0x4fe10
  simp only [withStack] at hmc
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := authFromPbName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x4fe10))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  from_pb_fetches_range b (Rust.withPanics ext) hfn 0 200
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr authFromPbName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨out, pbA, ⟨⟨cap0, ptr0⟩, ⟨cap1, ptr1⟩⟩, ⟨rootKey, macKey⟩⟩ := x
  dsimp only at *
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hr_le : rootKey.length ≤ cap0.toNat := ‹_›
  have hr_cap : cap0.toNat < 2 ^ 63 := ‹_›
  have hm_le : macKey.length ≤ cap1.toNat := ‹_›
  have hm_cap : cap1.toNat < 2 ^ 63 := ‹_›
  have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
  have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
  have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
  have hm_lt64 : macKey.length < 2 ^ 64 := by omega
  have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
  have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hr_cases with rfl | hr_pos <;>
    rcases hm_cases with rfl | hm_pos
  · -- Case 1: rootKey = [] ∧ macKey = []
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at *
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply SepWP.fold (vecU8_of_zero A out) (by sep_focus)
    have h2 : ((out + 24#64) ↦₆₄ 0#64) ∗ ((out + 32#64) ↦₆₄ 1#64) ∗ ((out + 40#64) ↦₆₄ 0#64) ⊢
        vecU8 A (out + 24#64) [] := by
      simpa only [out_add24_add8, out_add24_add16] using vecU8_of_zero A (out + 24#64)
    apply SepWP.fold h2 (by sep_focus)
    wp_done
  · -- Case 2: rootKey = [] ∧ 0 < macKey.length
    have hcap1_ne : cap1 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hlay1 : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, hcap1_ne, ↓reduceIte, sepConj_assoc] at *
    apply SepWPp.of_sepWP (mid := entry + 104#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom1, ite_true]
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x4fe10))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom1, ite_false, sepConj_assoc]
      have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_apply
      wp_steps
      apply SepWP.fold (vecU8_of_zero A out) (by sep_focus)
      have h2 : ((out + 24#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          ((out + 32#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          ((out + 40#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          A.live (sf_1.readReg64 Reg.x0) macKey.length 1 ∗
          (sf_1.readReg64 Reg.x0 ↦ₛ macKey) ⊢
          vecU8 A (out + 24#64) macKey := by
        simpa only [out_add24_add8, out_add24_add16] using
          vecU8_of_pos A (out + 24#64) (sf_1.readReg64 Reg.x0) macKey hm_pos hm_lt63 hoom1
      apply SepWP.fold h2 (by sep_focus)
      wp_done
  · -- Case 3: 0 < rootKey.length ∧ macKey = []
    have hcap0_ne : cap0 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hlay0 : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, hcap0_ne, ↓reduceIte, sepConj_assoc] at *
    apply SepWPp.of_sepWP (mid := entry + 56#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, ite_true]
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x4fe10))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, ite_false, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_apply
      wp_steps
      apply SepWP.fold (vecU8_of_pos A out (sf_1.readReg64 Reg.x0) rootKey hr_pos hr_lt63 hoom0) (by sep_focus)
      have h2 : ((out + 24#64) ↦₆₄ 0#64) ∗ ((out + 32#64) ↦₆₄ 1#64) ∗ ((out + 40#64) ↦₆₄ 0#64) ⊢
          vecU8 A (out + 24#64) [] := by
        simpa only [out_add24_add8, out_add24_add16] using vecU8_of_zero A (out + 24#64)
      apply SepWP.fold h2 (by sep_focus)
      wp_done
  · -- Case 4: 0 < rootKey.length ∧ 0 < macKey.length
    have hcap0_ne : cap0 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hcap1_ne : cap1 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hlay0 : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    have hlay1 : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    simp only [hcap0_ne, hcap1_ne, ↓reduceIte, sepConj_assoc] at *
    apply SepWPp.of_sepWP (mid := entry + 56#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ite_true]
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x4fe10))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP (mid := entry + 104#64)
      wp_steps
      wp_apply
      wp_steps
      wp_apply
      wp_steps
      wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom1 : sf_4.readReg64 Reg.x0 = 0#64
      · simp only [hoom1, BitVec.ofNat_eq_ofNat, ite_true]
        rw [pull_alloc_pure]
        refine SepWPp.pure_elim fun htrace => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x4fe10))
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
      · simp only [hoom1, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
        have hoom1_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
        rw [pull_alloc_pure]
        refine SepWPp.pure_elim fun ⟨_, htr4⟩ => ?_
        have htr_sf4 : sf_4.trace = s0.trace := by
          rw [htr4]; simp only [wp_norm, arm64_norm, *]
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_apply
        wp_steps
        apply SepWP.fold (vecU8_of_pos A out (sf_1.readReg64 Reg.x0) rootKey hr_pos hr_lt63 hoom0) (by sep_focus)
        have h2 : ((out + 24#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            ((out + 32#64) ↦₆₄ sf_4.readReg64 Reg.x0) ∗
            ((out + 40#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            A.live (sf_4.readReg64 Reg.x0) macKey.length 1 ∗
            (sf_4.readReg64 Reg.x0 ↦ₛ macKey) ⊢
            vecU8 A (out + 24#64) macKey := by
          simpa only [out_add24_add8, out_add24_add16] using
            vecU8_of_pos A (out + 24#64) (sf_4.readReg64 Reg.x0) macKey hm_pos hm_lt63 hoom1
        apply SepWP.fold h2 (by sep_focus)
        wp_done

/-- `Authenticator::from_pb` meets `authFromPbPinnedSpec A` on `tripleRatchetProgAtExt`. -/
theorem auth_from_pb_pinned_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName)
      (authFromPbPinnedSpec A) :=
  auth_from_pb_pinned_ok_core
    (hA.shim_ok_at authFromPbName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x4fe10)))
    (hA.alloc_ok_at authFromPbName (num% (ls_off% "__rustc::__rust_alloc" - 0x4fe10)))
    (subroutine_ok_withStack_of_subroutine_ok
      (hA.session_memcpy_region_ok_at authFromPbName (num% (ls_off% "memcpy" - 0x4fe10)))
      allocHookStack)

private theorem auth_from_pb_ok_of_pinned {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hpinned : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName) (authFromPbPinnedSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName)
      (authFromPbSpec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [authFromPbSpec, authenticatorPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.out, x.pbA, g, x.pb⟩ R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [authFromPbSpec, authenticatorPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hex)

/-- `Authenticator::from_pb` meets `authFromPbSpec A` on `tripleRatchetProgAtExt`. -/
theorem auth_from_pb_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName)
      (authFromPbSpec A) :=
  auth_from_pb_ok_of_pinned (auth_from_pb_pinned_ok_ext hA)

/-- `.inImage img` contract proposition for `authFromPbPinnedSpec A`. -/
def AuthFromPbPinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authFromPbName)
    ((authFromPbPinnedSpec A).inImage img)

theorem auth_from_pb_pinned_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    AuthFromPbPinnedOkX img A ext := by
  unfold AuthFromPbPinnedOkX
  refine subroutine_ok_mono (auth_from_pb_pinned_ok_ext hA) (fun x R s0 hpre => ?_)
    (fun _ _ _ _ hpost => hpost)
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem auth_from_pb_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    AuthFromPbOkX img A ext := by
  unfold AuthFromPbOkX
  refine subroutine_ok_mono (auth_from_pb_ok_ext hA) (fun x R s0 hpre => ?_)
    (fun _ _ _ _ hpost => hpost)
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem auth_from_pb_ok_x_tripleRatchetExterns {img : Obj.Image} (C : Crypto) {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    AuthFromPbOkX img A (tripleRatchetExterns C ctl abs) :=
  auth_from_pb_ok_x (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA)

namespace Ext4K

theorem auth_from_pb_pinned_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.SpqrV1.Alloc.AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName)
      (authFromPbPinnedSpec A) :=
  auth_from_pb_pinned_ok_core
    (hA.shim_ok_at authFromPbName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x4fe10)))
    (hA.alloc_ok_at authFromPbName (num% (ls_off% "__rustc::__rust_alloc" - 0x4fe10)))
    (hA.session_memcpy_region_ok_at authFromPbName (num% (ls_off% "memcpy" - 0x4fe10)) allocHookStack)

theorem auth_from_pb_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.SpqrV1.Alloc.AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authFromPbName)
      (authFromPbSpec A) :=
  auth_from_pb_ok_of_pinned (auth_from_pb_pinned_ok_ext hA)

theorem auth_from_pb_pinned_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.SpqrV1.Alloc.AllocContracts4K img.base A ext) :
    AuthFromPbPinnedOkX img A ext := by
  unfold AuthFromPbPinnedOkX
  refine subroutine_ok_mono (auth_from_pb_pinned_ok_ext hA) (fun x R s0 hpre => ?_)
    (fun _ _ _ _ hpost => hpost)
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem auth_from_pb_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.SpqrV1.Alloc.AllocContracts4K img.base A ext) :
    AuthFromPbOkX img A ext := by
  unfold AuthFromPbOkX
  refine subroutine_ok_mono (auth_from_pb_ok_ext hA) (fun x R s0 hpre => ?_)
    (fun _ _ _ _ hpost => hpost)
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

end Ext4K

/-! ## `optAuthenticatorPBAt` Niche-Tag Bridge Lemmas -/

/-- Exposes the niche/capacity word `(a ↦₆₄ optAuthCap g opt)` from `optAuthenticatorPBPinnedAt`. -/
theorem optAuthenticatorPBPinnedAt_expose_cap (A : RustAlloc) (g : AuthenticatorPBGhost)
    (a : BitVec 64) (opt : Option AuthenticatorPB) :
    optAuthenticatorPBPinnedAt A g a opt =
      (a ↦₆₄ optAuthCap g opt) ∗ optAuthPayload A g a opt :=
  optAuthenticatorPBPinnedAt_eq A g a opt

theorem optAuthenticatorPBAt_expose_cap (A : RustAlloc) (a : BitVec 64)
    (opt : Option AuthenticatorPB) :
    optAuthenticatorPBAt A a opt =
      ∃∗ g : AuthenticatorPBGhost,
        (a ↦₆₄ optAuthCap g opt) ∗ optAuthPayload A g a opt := by
  rw [optAuthenticatorPBAt_eq_exists_pinned]
  simp only [optAuthenticatorPBPinnedAt_eq]

@[simp]
theorem optAuthCap_none (g : AuthenticatorPBGhost) :
    optAuthCap g none = noneCap := rfl

@[simp]
theorem optAuthCap_some (g : AuthenticatorPBGhost) (pb : AuthenticatorPB) :
    optAuthCap g (some pb) = g.rootKey.cap := rfl

@[simp]
theorem optAuthCap_none_add_one_beq_zero (g : AuthenticatorPBGhost) :
    (optAuthCap g none + 1#64 == 0#64) = true := by dsimp only [optAuthCap]; decide

@[simp]
theorem optAuthCap_none_add_one_bne_zero (g : AuthenticatorPBGhost) :
    (optAuthCap g none + 1#64 != 0#64) = false := by dsimp only [optAuthCap]; decide

@[simp]
theorem optAuthenticatorPBPinnedAt_none_eq (A : RustAlloc) (g : AuthenticatorPBGhost)
    (a : BitVec 64) :
    optAuthenticatorPBPinnedAt A g a none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40 := rfl

@[simp]
theorem optAuthenticatorPBPinnedAt_some_eq (A : RustAlloc) (g : AuthenticatorPBGhost)
    (a : BitVec 64) (pb : AuthenticatorPB) :
    optAuthenticatorPBPinnedAt A g a (some pb) = authenticatorPBPinnedAt A g a pb := rfl

@[simp]
theorem optAuthenticatorPBAt_none_eq (A : RustAlloc) (a : BitVec 64) :
    optAuthenticatorPBAt A a none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40 := rfl

@[simp]
theorem optAuthenticatorPBAt_some_eq (A : RustAlloc) (a : BitVec 64) (pb : AuthenticatorPB) :
    optAuthenticatorPBAt A a (some pb) = authenticatorPBAt A a pb := rfl

/-- Refolds `(a ↦₆₄ optAuthCap g none) ∗ optAuthPayload A g a none` into `optAuthenticatorPBPinnedAt A g a none`. -/
theorem optAuthenticatorPBPinnedAt_fold_none (A : RustAlloc) (g : AuthenticatorPBGhost)
    (a : BitVec 64) :
    (a ↦₆₄ optAuthCap g none) ∗ optAuthPayload A g a none =
      optAuthenticatorPBPinnedAt A g a none := rfl

theorem optAuthenticatorPBAt_fold_none (A : RustAlloc) (g : AuthenticatorPBGhost)
    (a : BitVec 64) :
    (a ↦₆₄ optAuthCap g none) ∗ optAuthPayload A g a none =
      optAuthenticatorPBAt A a none := rfl

/-- Refolds `(a ↦₆₄ optAuthCap g (some pb)) ∗ optAuthPayload A g a (some pb)` into `authenticatorPBPinnedAt A g a pb`. -/
theorem optAuthenticatorPBPinnedAt_fold_some (A : RustAlloc) (g : AuthenticatorPBGhost)
    (a : BitVec 64) (pb : AuthenticatorPB) :
    (a ↦₆₄ optAuthCap g (some pb)) ∗ optAuthPayload A g a (some pb) =
      authenticatorPBPinnedAt A g a pb :=
  (optAuthenticatorPBPinnedAt_eq A g a (some pb)).symm

theorem authenticatorPBPinnedAt_entails_optAuthenticatorPBAt_some (A : RustAlloc)
    (g : AuthenticatorPBGhost) (a : BitVec 64) (pb : AuthenticatorPB) :
    authenticatorPBPinnedAt A g a pb ⊢ optAuthenticatorPBAt A a (some pb) :=
  authenticatorPinAt_entails_authenticatorAt A g a (Authenticator.fromPb pb)

/-! ## Relocatable Contracts (Block 330) and `update` Frame Helpers -/

set_option maxHeartbeats 1600000 in
/-- Block 330 (`Authenticator::from_pb`) meets `authFromPbPinnedSpec A`. -/
theorem auth_from_pb_pinned_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "memcpy") framelessMemcpySpec)
    (hpanic : ((blkPC_330).rebase (blkPl_330).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_330).rebase (blkPl_330).base H) (blkPl_330).base
      (authFromPbPinnedSpec A) := by
  simp only [authFromPbPinnedSpec, authenticatorPBPinnedAt, authenticatorAt, Authenticator.fromPb,
    vecU8At, vecHeader, memRegion_48_cells, stackAt_authFromPb,
    out_add24_add8, out_add24_add16, BitVec.ofNat_eq_ofNat,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wpp_init x s0
  obtain ⟨out, pbA, ⟨⟨cap0, ptr0⟩, ⟨cap1, ptr1⟩⟩, ⟨rootKey, macKey⟩⟩ := x
  dsimp only at *
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hr_le : rootKey.length ≤ cap0.toNat := ‹_›
  have hr_cap : cap0.toNat < 2 ^ 63 := ‹_›
  have hm_le : macKey.length ≤ cap1.toNat := ‹_›
  have hm_cap : cap1.toNat < 2 ^ 63 := ‹_›
  have hr_lt63 : rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
  have hm_lt63 : macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
  have hr_lt64 : rootKey.length < 2 ^ 64 := by omega
  have hm_lt64 : macKey.length < 2 ^ 64 := by omega
  have hr_toNat : (BitVec.ofNat 64 rootKey.length).toNat = rootKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
  have hm_toNat : (BitVec.ofNat 64 macKey.length).toNat = macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
  have hr_cases : rootKey = [] ∨ 0 < rootKey.length := by cases rootKey <;> simp
  have hm_cases : macKey = [] ∨ 0 < macKey.length := by cases macKey <;> simp
  rcases hr_cases with rfl | hr_pos <;>
    rcases hm_cases with rfl | hm_pos
  · simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at *
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply SepWP.fold (vecU8_of_zero A out) (by sep_focus)
    have h2 : ((out + 24#64) ↦₆₄ 0#64) ∗ ((out + 32#64) ↦₆₄ 1#64) ∗ ((out + 40#64) ↦₆₄ 0#64) ⊢
        vecU8 A (out + 24#64) [] := by
      simpa only [out_add24_add8, out_add24_add16] using vecU8_of_zero A (out + 24#64)
    apply SepWP.fold h2 (by sep_focus)
    wp_done
  · have hcap1_ne : cap1 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hlay1 : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, hcap1_ne, ↓reduceIte, sepConj_assoc] at *
    apply SepWPp.of_sepWP (mid := (blkPl_330).base + 104#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom1, ite_true]
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom1, ite_false, sepConj_assoc]
      have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_apply
      wp_steps
      apply SepWP.fold (vecU8_of_zero A out) (by sep_focus)
      have h2 : ((out + 24#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          ((out + 32#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          ((out + 40#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
          A.live (sf_1.readReg64 Reg.x0) macKey.length 1 ∗
          (sf_1.readReg64 Reg.x0 ↦ₛ macKey) ⊢
          vecU8 A (out + 24#64) macKey := by
        simpa only [out_add24_add8, out_add24_add16] using
          vecU8_of_pos A (out + 24#64) (sf_1.readReg64 Reg.x0) macKey hm_pos hm_lt63 hoom1
      apply SepWP.fold h2 (by sep_focus)
      wp_done
  · have hcap0_ne : cap0 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hlay0 : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, hcap0_ne, ↓reduceIte, sepConj_assoc] at *
    apply SepWPp.of_sepWP (mid := (blkPl_330).base + 56#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, ite_true]
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, ite_false, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_apply
      wp_steps
      apply SepWP.fold (vecU8_of_pos A out (sf_1.readReg64 Reg.x0) rootKey hr_pos hr_lt63 hoom0) (by sep_focus)
      have h2 : ((out + 24#64) ↦₆₄ 0#64) ∗ ((out + 32#64) ↦₆₄ 1#64) ∗ ((out + 40#64) ↦₆₄ 0#64) ⊢
          vecU8 A (out + 24#64) [] := by
        simpa only [out_add24_add8, out_add24_add16] using vecU8_of_zero A (out + 24#64)
      apply SepWP.fold h2 (by sep_focus)
      wp_done
  · have hcap0_ne : cap0 ≠ 0#64 := cap_ne_zero_of_pos hr_pos hr_le
    have hcap1_ne : cap1 ≠ 0#64 := cap_ne_zero_of_pos hm_pos hm_le
    have hr_ne0 : (BitVec.ofNat 64 rootKey.length == 0#64) = false :=
      ofNat_beq_zero_false hr_pos hr_lt64
    have hm_ne0 : (BitVec.ofNat 64 macKey.length == 0#64) = false :=
      ofNat_beq_zero_false hm_pos hm_lt64
    have hlay0 : LayoutOk rootKey.length 1 := ⟨hr_pos, hpow1, by omega⟩
    have hlay1 : LayoutOk macKey.length 1 := ⟨hm_pos, hpow1, by omega⟩
    simp only [hcap0_ne, hcap1_ne, ↓reduceIte, sepConj_assoc] at *
    apply SepWPp.of_sepWP (mid := (blkPl_330).base + 56#64)
    wp_steps
    wp_apply
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ite_true]
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP (mid := (blkPl_330).base + 104#64)
      wp_steps
      wp_apply
      wp_steps
      wp_apply
      wp_steps
      wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom1 : sf_4.readReg64 Reg.x0 = 0#64
      · simp only [hoom1, BitVec.ofNat_eq_ofNat, ite_true]
        rw [pull_alloc_pure]
        refine SepWPp.pure_elim fun htrace => ?_
        apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
      · simp only [hoom1, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
        have hoom1_beq : (sf_4.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
        rw [pull_alloc_pure]
        refine SepWPp.pure_elim fun ⟨_, htr4⟩ => ?_
        have htr_sf4 : sf_4.trace = s0.trace := by
          rw [htr4]; simp only [wp_norm, arm64_norm, *]
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_apply
        wp_steps
        apply SepWP.fold (vecU8_of_pos A out (sf_1.readReg64 Reg.x0) rootKey hr_pos hr_lt63 hoom0) (by sep_focus)
        have h2 : ((out + 24#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            ((out + 32#64) ↦₆₄ sf_4.readReg64 Reg.x0) ∗
            ((out + 40#64) ↦₆₄ BitVec.ofNat 64 macKey.length) ∗
            A.live (sf_4.readReg64 Reg.x0) macKey.length 1 ∗
            (sf_4.readReg64 Reg.x0 ↦ₛ macKey) ⊢
            vecU8 A (out + 24#64) macKey := by
          simpa only [out_add24_add8, out_add24_add16] using
            vecU8_of_pos A (out + 24#64) (sf_4.readReg64 Reg.x0) macKey hm_pos hm_lt63 hoom1
        apply SepWP.fold h2 (by sep_focus)
        wp_done

/-- Block 330 (`Authenticator::from_pb`) meets `authFromPbSpec A`. -/
theorem auth_from_pb_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hmc : subroutine_ok ((blkPC_330).rebase (blkPl_330).base H)
      (lsρ "memcpy") framelessMemcpySpec)
    (hpanic : ((blkPC_330).rebase (blkPl_330).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_330).rebase (blkPl_330).base H) (blkPl_330).base
      (authFromPbSpec A) := by
  have hpinned := auth_from_pb_pinned_placed_ok hshim halloc hmc hpanic
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [authFromPbSpec, authenticatorPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.out, x.pbA, g, x.pb⟩ R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [authFromPbSpec, authenticatorPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hex)

/-- Stack budget of `Authenticator::update` (`160 + extHookStack`). -/
abbrev authUpdateStackX : Nat := 160 + extHookStack

namespace UpdateFacts

@[simp] theorem updateLabel_length :
    Authenticator.updateLabel.length = 45 := by decide

@[simp] theorem replicate_32_zero_length :
    (List.replicate 32 (0#8 : BitVec 8)).length = 32 := by decide

/-- Splits `stackAt sp authUpdateStackX` into the `ikm` (`[sp - 160, sp - 136)`) and `info`
(`[sp - 136, sp - 112)`) `Vec<u8>` sret slots, the `[&[u8]; 2]` array (`[sp - 112, sp - 80)`),
and the ten saved register/epoch cells (`[sp - 80, sp)`). -/
theorem stackAt_authUpdateX_split (sp : BitVec 64) :
    stackAt sp authUpdateStackX = stackAt (sp - 160#64) extHookStack ∗
      memRegion (sp - 160#64) 24 ∗ memRegion (sp - 136#64) 24 ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
        ((sp - 112#64) ↦₆₄ s0) ∗ ((sp - 104#64) ↦₆₄ s1) ∗ ((sp - 96#64) ↦₆₄ s2) ∗ ((sp - 88#64) ↦₆₄ s3)) ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗ ((sp - 56#64) ↦₆₄ c3) ∗
        ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗ ((sp - 32#64) ↦₆₄ c6) ∗ ((sp - 24#64) ↦₆₄ c7) ∗
        ((sp - 16#64) ↦₆₄ c8) ∗ ((sp - 8#64) ↦₆₄ c9)) := by
  change memRegion (sp - BitVec.ofNat 64 16544) 16544 = memRegion (sp - 160#64 - BitVec.ofNat 64 16384) 16384 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16544) (n := 16384) (k := 160) (b' := sp - 160#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 160#64) (n := 24) (k := 136) (b' := sp - 136#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 136#64) (n := 24) (k := 112) (b' := sp - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 112#64) (n := 32) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16544) 16384 ∗ (memRegion (sp - 160#64) 24 ∗
    (memRegion (sp - 136#64) 24 ∗ (memRegion (sp - 112#64) (8 * 4) ∗ memRegion (sp - 80#64) (8 * 10)))) = _
  rw [ProofLib.memRegion_cells (sp - 112#64) 4 (by decide), ProofLib.memRegion_cells (sp - 80#64) 10 (by decide)]
  have hsub : sp - 160#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16544 := by bv_kernel
  rw [hsub]; cells_unfold

/-- Reassembles the `Authenticator::update` frame back into `stackAt sp authUpdateStackX`. -/
theorem rejoin_stack_authUpdateX (sp : BitVec 64)
    (v0 v1 v2 w0 w1 w2 s0 s1 s2 s3 c0 c1 c2 : BitVec 64)
    {beBytes : List (BitVec 8)} (hbe : beBytes.length = 8) (c4 c5 c6 c7 c8 c9 : BitVec 64) :
    stackAt (sp - 160#64) extHookStack ∗
      ((sp - 160#64) ↦₆₄ v0) ∗ ((sp - 152#64) ↦₆₄ v1) ∗ ((sp - 144#64) ↦₆₄ v2) ∗
      ((sp - 136#64) ↦₆₄ w0) ∗ ((sp - 128#64) ↦₆₄ w1) ∗ ((sp - 120#64) ↦₆₄ w2) ∗
      ((sp - 112#64) ↦₆₄ s0) ∗ ((sp - 104#64) ↦₆₄ s1) ∗ ((sp - 96#64) ↦₆₄ s2) ∗ ((sp - 88#64) ↦₆₄ s3) ∗
      ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗ ((sp - 56#64) ↦ₛ beBytes) ∗
      ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗ ((sp - 32#64) ↦₆₄ c6) ∗
      ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗ ((sp - 8#64) ↦₆₄ c9) ⊢ stackAt sp authUpdateStackX := by
  have heq : stackAt sp authUpdateStackX =
      stackAt (sp - 160#64) extHookStack ∗ cells (sp - 160#64) 13 ∗ memRegion (sp - 56#64) 8 ∗ cells (sp - 48#64) 6 := by
    change memRegion (sp - BitVec.ofNat 64 16544) 16544 = memRegion (sp - 160#64 - BitVec.ofNat 64 16384) 16384 ∗ _
    rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16544) (n := 16384) (k := 160) (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 104) (k := 56) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 8) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide)]
    change memRegion (sp - BitVec.ofNat 64 16544) 16384 ∗ (memRegion (sp - 160#64) (8 * 13) ∗
      (memRegion (sp - 56#64) 8 ∗ memRegion (sp - 48#64) (8 * 6))) = _
    rw [ProofLib.memRegion_cells (sp - 160#64) 13 (by decide), ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]
    have hsub : sp - 160#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16544 := by bv_kernel
    rw [hsub]
  rw [heq]
  have hc13 : (((sp - 160#64) ↦₆₄ v0) ∗ ((sp - 152#64) ↦₆₄ v1) ∗ ((sp - 144#64) ↦₆₄ v2) ∗
      ((sp - 136#64) ↦₆₄ w0) ∗ ((sp - 128#64) ↦₆₄ w1) ∗ ((sp - 120#64) ↦₆₄ w2) ∗
      ((sp - 112#64) ↦₆₄ s0) ∗ ((sp - 104#64) ↦₆₄ s1) ∗ ((sp - 96#64) ↦₆₄ s2) ∗ ((sp - 88#64) ↦₆₄ s3) ∗
      ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2)) ⊢ cells (sp - 160#64) 13 := by
    cells_unfold
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
        (Entails.sepExists_right s0 (Entails.sepExists_right s1 (Entails.sepExists_right s2
          (Entails.sepExists_right s3 (Entails.sepExists_right c0 (Entails.sepExists_right c1
            (Entails.sepExists_right c2 (Entails.refl _)))))))))))))
  have hmbe : ((sp - 56#64) ↦ₛ beBytes) ⊢ memRegion (sp - 56#64) 8 :=
    hbe ▸ pointsToBytes_entails_memRegion (sp - 56#64) beBytes
  have hc6 : (((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗ ((sp - 32#64) ↦₆₄ c6) ∗
      ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗ ((sp - 8#64) ↦₆₄ c9)) ⊢ cells (sp - 48#64) 6 := by
    cells_unfold
    exact Entails.sepExists_right c4 (Entails.sepExists_right c5 (Entails.sepExists_right c6
      (Entails.sepExists_right c7 (Entails.sepExists_right c8 (Entails.sepExists_right c9 (Entails.refl _))))))
  have hgroup : stackAt (sp - 160#64) extHookStack ∗
      ((sp - 160#64) ↦₆₄ v0) ∗ ((sp - 152#64) ↦₆₄ v1) ∗ ((sp - 144#64) ↦₆₄ v2) ∗
      ((sp - 136#64) ↦₆₄ w0) ∗ ((sp - 128#64) ↦₆₄ w1) ∗ ((sp - 120#64) ↦₆₄ w2) ∗
      ((sp - 112#64) ↦₆₄ s0) ∗ ((sp - 104#64) ↦₆₄ s1) ∗ ((sp - 96#64) ↦₆₄ s2) ∗ ((sp - 88#64) ↦₆₄ s3) ∗
      ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗ ((sp - 56#64) ↦ₛ beBytes) ∗
      ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗ ((sp - 32#64) ↦₆₄ c6) ∗
      ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗ ((sp - 8#64) ↦₆₄ c9) =
      stackAt (sp - 160#64) extHookStack ∗
        (((sp - 160#64) ↦₆₄ v0) ∗ ((sp - 152#64) ↦₆₄ v1) ∗ ((sp - 144#64) ↦₆₄ v2) ∗
         ((sp - 136#64) ↦₆₄ w0) ∗ ((sp - 128#64) ↦₆₄ w1) ∗ ((sp - 120#64) ↦₆₄ w2) ∗
         ((sp - 112#64) ↦₆₄ s0) ∗ ((sp - 104#64) ↦₆₄ s1) ∗ ((sp - 96#64) ↦₆₄ s2) ∗ ((sp - 88#64) ↦₆₄ s3) ∗
         ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2)) ∗
        ((sp - 56#64) ↦ₛ beBytes) ∗
        (((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗ ((sp - 32#64) ↦₆₄ c6) ∗
         ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗ ((sp - 8#64) ↦₆₄ c9)) := by ac_rfl
  rw [hgroup]; exact sepConj_mono_right (sepConj_mono hc13 (sepConj_mono hmbe hc6))

theorem vecU8_expose_entails (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs ⊢ ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans (vecU8At_expose_entails A v cap ptr bs) ?_
  exact Entails.of_eq (by ac_rfl)

theorem authenticatorAt_of_32_32 (A : RustAlloc) (selfA p_rk p_mk : BitVec 64)
    (rk mk : List (BitVec 8))
    (hrk_len : rk.length = 32) (hmk_len : mk.length = 32)
    (hp_rk : p_rk ≠ 0#64) (hp_mk : p_mk ≠ 0#64) :
    (selfA ↦₆₄ 32#64) ∗ ((selfA + 8#64) ↦₆₄ p_rk) ∗ ((selfA + 16#64) ↦₆₄ 32#64) ∗
      ((selfA + 24#64) ↦₆₄ 32#64) ∗ ((selfA + 32#64) ↦₆₄ p_mk) ∗ ((selfA + 40#64) ↦₆₄ 32#64) ∗
      A.live p_rk 32 1 ∗ (p_rk ↦ₛ rk) ∗ A.live p_mk 32 1 ∗ (p_mk ↦ₛ mk) ⊢
      authenticatorAt A selfA { rootKey := rk, macKey := mk } := by
  refine Entails.trans ?_
    (authenticatorPinAt_entails_authenticatorAt A
      ⟨⟨32#64, p_rk⟩, ⟨32#64, p_mk⟩⟩ selfA { rootKey := rk, macKey := mk })
  dsimp only [authenticatorPinAt, vecU8At, vecHeader]
  have h32_ne : (32#64 : BitVec 64) ≠ 0#64 := by decide
  have h32_toNat : (32#64 : BitVec 64).toNat = 32 := by decide
  have h24_8 : (selfA + 24#64) + 8#64 = selfA + 32#64 := by bv_omega
  have h24_16 : (selfA + 24#64) + 16#64 = selfA + 40#64 := by bv_omega
  simp only [hrk_len, hmk_len, BitVec.ofNat_eq_ofNat, h32_ne, h32_toNat,
    Nat.le_refl, ↓reduceIte, Nat.sub_self, memRegion_zero, sepConj_emp, h24_8, h24_16, sepConj_assoc]
  rw [show (selfA ↦₆₄ 32#64) ∗ ((selfA + 8#64) ↦₆₄ p_rk) ∗ ((selfA + 16#64) ↦₆₄ 32#64) ∗
        ⌜True ∧ (32 : Nat) < 2 ^ 63 ∧ p_rk ≠ 0#64⌝ ∗ A.live p_rk 32 1 ∗ (p_rk ↦ₛ rk) ∗
        ((selfA + 24#64) ↦₆₄ 32#64) ∗ ((selfA + 32#64) ↦₆₄ p_mk) ∗ ((selfA + 40#64) ↦₆₄ 32#64) ∗
        ⌜True ∧ (32 : Nat) < 2 ^ 63 ∧ p_mk ≠ 0#64⌝ ∗ A.live p_mk 32 1 ∗ (p_mk ↦ₛ mk) =
      ⌜True ∧ (32 : Nat) < 2 ^ 63 ∧ p_rk ≠ 0#64⌝ ∗ ⌜True ∧ (32 : Nat) < 2 ^ 63 ∧ p_mk ≠ 0#64⌝ ∗
        ((selfA ↦₆₄ 32#64) ∗ ((selfA + 8#64) ↦₆₄ p_rk) ∗ ((selfA + 16#64) ↦₆₄ 32#64) ∗
         ((selfA + 24#64) ↦₆₄ 32#64) ∗ ((selfA + 32#64) ↦₆₄ p_mk) ∗ ((selfA + 40#64) ↦₆₄ 32#64) ∗
         A.live p_rk 32 1 ∗ (p_rk ↦ₛ rk) ∗ A.live p_mk 32 1 ∗ (p_mk ↦ₛ mk)) by ac_rfl]
  exact Entails.pure_right ⟨trivial, by decide, hp_rk⟩
    (Entails.pure_right ⟨trivial, by decide, hp_mk⟩ (Entails.refl _))

end UpdateFacts

theorem drop_32_take_32_eq_drop_32_of_length_64 {bs : List (BitVec 8)} (h : bs.length = 64) :
    (bs.drop 32).take 32 = bs.drop 32 := List.take_of_length_le (by simp [h])

theorem authenticatorPinAt_expose_entails (A : RustAlloc) (g : AuthenticatorGhost)
    (selfA : BitVec 64) (auth : Authenticator) :
    authenticatorPinAt A g selfA auth ⊢
      ⌜(auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0) ∧
        (auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0)⌝ ∗
        (selfA ↦₆₄ g.rootKey.cap) ∗ ((selfA + 8#64) ↦₆₄ g.rootKey.ptr) ∗
        ((selfA + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ((selfA + 24#64) ↦₆₄ g.macKey.cap) ∗ ((selfA + 32#64) ↦₆₄ g.macKey.ptr) ∗
        ((selfA + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
        (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
        (if g.rootKey.cap = 0 then emp
         else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗
           memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length)
             (g.rootKey.cap.toNat - auth.rootKey.length)) ∗
        (g.macKey.ptr ↦ₛ auth.macKey) ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length)
             (g.macKey.cap.toNat - auth.macKey.length)) := by
  unfold authenticatorPinAt
  refine Entails.trans (sepConj_mono
    (vecU8At_expose_entails A selfA g.rootKey.cap g.rootKey.ptr auth.rootKey)
    (vecU8At_expose_entails A (selfA + 24#64) g.macKey.cap g.macKey.ptr auth.macKey)) ?_
  have h24_8 : (selfA + 24#64) + 8#64 = selfA + 32#64 := by bv_omega
  have h24_16 : (selfA + 24#64) + 16#64 = selfA + 40#64 := by bv_omega
  rw [h24_8, h24_16, show
      ((selfA ↦₆₄ g.rootKey.cap) ∗ ((selfA + 8#64) ↦₆₄ g.rootKey.ptr) ∗
        ((selfA + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
        (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
        (if g.rootKey.cap = 0 then emp else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗
          memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length))) ∗
      ((selfA + 24#64) ↦₆₄ g.macKey.cap) ∗ ((selfA + 32#64) ↦₆₄ g.macKey.ptr) ∗
        ((selfA + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
        ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        (g.macKey.ptr ↦ₛ auth.macKey) ∗
        (if g.macKey.cap = 0 then emp else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
          memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) =
      ⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
        ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        ((selfA ↦₆₄ g.rootKey.cap) ∗ ((selfA + 8#64) ↦₆₄ g.rootKey.ptr) ∗
         ((selfA + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((selfA + 24#64) ↦₆₄ g.macKey.cap) ∗ ((selfA + 32#64) ↦₆₄ g.macKey.ptr) ∗
         ((selfA + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
         (if g.rootKey.cap = 0 then emp else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗
           memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)) ∗
         (g.macKey.ptr ↦ₛ auth.macKey) ∗
         (if g.macKey.cap = 0 then emp else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length))) by ac_rfl]
  refine Entails.pure_left fun hrk => Entails.pure_left fun hmk => ?_
  exact Entails.pure_right ⟨hrk, hmk⟩ (Entails.refl _)

def rustAllocZeroedSpecWithStack (A : RustAlloc) (hookStack : Nat := extHookStack) :
    Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 Reg.x0).toNat = size ∧ (s.readReg64 Reg.x1).toNat = align ∧
      LayoutOk size align⌝ ∗
      A.pool ∗ stackAt s.sp hookStack
  post := fun (size, align) s0 sf =>
    A.pool ∗ stackAt s0.sp hookStack ∗
      (if sf.readReg64 Reg.x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
         ⌜(sf.readReg64 Reg.x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
           A.live (sf.readReg64 Reg.x0) size align ∗
           (sf.readReg64 Reg.x0 ↦ₛ List.replicate size 0#8))

theorem rustAllocZeroedWithStack_of_rustAllocZeroed {P : Program} {addr : BitVec 64}
    {A : RustAlloc} {hookStack : Nat} (h : subroutine_ok P addr (rustAllocZeroedSpec A))
    (hle : allocHookStack ≤ hookStack := by decide) (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (rustAllocZeroedSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨size, align⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗ stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (hookStack - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustAllocZeroedSpec A).pre (size, align) s0 ∗ R' := by
    dsimp only [rustAllocZeroedSpecWithStack, rustAllocZeroedSpec, R'] at hpre ⊢
    rw [hsplit] at hpre; ac_nf at hpre ⊢
  refine h.mono_outcome (size, align) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocZeroedSpecWithStack, rustAllocZeroedSpec, R'] at hpost ⊢
    rw [hsplit]; ac_nf at hpost ⊢
  · dsimp only [rustAllocZeroedSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [rustAllocZeroedSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [rustAllocZeroedSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

def vecBufAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (ptr ↦ₛ bs) ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecBufAt_fold (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
      vecBufAt A cap ptr bs :=
  Entails.refl _

theorem vecBufAt_of_cap_zero (A : RustAlloc) {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hcap : cap = 0#64) (hle : bs.length ≤ cap.toNat) : vecBufAt A cap ptr bs ⊢ emp := by
  unfold vecBufAt
  have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by subst hcap; simpa using hle)
  subst hcap hnil; simp only [pointsToBytes_nil, emp_sepConj]; exact Entails.refl _

theorem pointsToBytes_replicate_64_entails_memRegion (p : BitVec 64) :
    (p ↦ₛ List.replicate 64 (0#8 : BitVec 8)) ⊢ memRegion p 64 :=
  (by decide : (List.replicate 64 (0#8 : BitVec 8)).length = 64) ▸
    pointsToBytes_entails_memRegion p (List.replicate 64 0#8)

theorem pointsToBytes_64_entails_memRegion (p : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 64) :
    (p ↦ₛ bs) ⊢ memRegion p 64 :=
  h ▸ pointsToBytes_entails_memRegion p bs

theorem SepWPp.seq_frame_inImage {prog : Program} {img : Obj.Image}
    {mid_pc ret_pc : BitVec 64} {s : State} {P P_local Q_local F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hF : ImgCallInv img s)
    (hframe : P = P_local ∗ F)
    (h1 : SepWP prog mid_pc s P_local
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s.trace ∧ (Pm ⊢ Q_local)))
    (h2 : ∀ sm : State, sm.pc = mid_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → sm.trace = s.trace → ImgCallInv img sm →
      SepWPp prog ret_pc sm (Q_local ∗ F) Q Qp) :
    SepWPp prog ret_pc s P Q Qp := by
  intro R hm hL
  rw [hframe, sepConj_assoc] at hm
  rcases h1.elim (R := F ∗ R) hm hL with
    ⟨sm, hsteps1, ⟨hpc, hrun, Pm, hPm, hsp, hcs, htr, hent⟩ | ⟨_, hoom⟩⟩
  · have hPm' : sm.mem ⊨ (Q_local ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hent) hPm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      h2 sm hpc hrun hsp hcs htr (hF.of_steps hsteps1) R hPm' (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem dealloc_vecBuf_cases {cap : BitVec 64} {n : Nat}
    (_hle : n ≤ cap.toNat) : cap = 0#64 ∨ cap ≠ 0#64 := Decidable.em (cap = 0#64)

def ikmDeallocLocal (A : RustAlloc) {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (_hle : bs.length ≤ cap.toNat) (_hptr : ptr ≠ 0#64) (sp : BitVec 64) : SepProp :=
  vecBufAt A cap ptr bs ∗ A.pool ∗ stackAt sp extHookStack

theorem ikmVecBuf_fold (A : RustAlloc) {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (_hle : bs.length ≤ cap.toNat) (_hptr : ptr ≠ 0#64) :
    (ptr ↦ₛ bs) ∗ (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢ vecBufAt A cap ptr bs :=
  Entails.refl _

theorem allowPanic_panicked_update {s0 sf : State} {P R : SepProp}
    (haf : allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace)
    (hm : (Rust.panicked sf).mem ⊨ P ∗ R) :
    (Rust.panicked sf).mem ⊨
      (⌜allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace⌝ ∗ anyHeap) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨haf, Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) hm⟩

end CryptoVerification.SpqrV1.Auth
