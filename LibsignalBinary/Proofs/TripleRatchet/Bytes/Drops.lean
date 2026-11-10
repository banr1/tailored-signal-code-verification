/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.BytesCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.OptImageHelper
public import LibsignalBinary.Proofs.CodeLayout -- shake: keep
public import ProofLib.SepLogic.WP.Apply -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `bytes::Bytes` Drop Functions and Vtable Dispatch

Verifies `bytes::bytes::static_drop` (`0x40950`), `bytes::bytes::promotable_even_drop` (`0x41098`),
`bytes::bytes::promotable_odd_drop` (`0x40fac`), unified vtable `drop` dispatch
(`bytesDropFnAddr`), and relocated `.rodata` vtable `+0x20` slot lookup (`bytesVtableSlotLoaded`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Decoded Instructions for Drop Functions -/

/-! ### `bytes::bytes::static_drop` (`0x40950`, 4 bytes) -/
gen_decodes libsignalSessionCode_tree libsignalTripleRatchetBin [(ls_off% "bytes::bytes::static_drop")]

/-! ### `bytes::bytes::promotable_odd_drop` (`0x40fac..0x41094`, 236 bytes) -/
gen_decodes libsignalSessionCode_tree libsignalTripleRatchetBin [(ls_off% "bytes::bytes::promotable_odd_drop") → (ls_off% "bytes::bytes::promotable_odd_drop" + 232)]

/-! ### `bytes::bytes::promotable_even_drop` (`0x41098..0x41184`, 240 bytes) -/
gen_decodes libsignalSessionCode_tree libsignalTripleRatchetBin [(ls_off% "bytes::bytes::promotable_even_drop") → (ls_off% "bytes::bytes::promotable_even_drop" + 236)]

/-! ## 2. Verification of `bytes::bytes::static_drop` (`0x40950`) -/

theorem bytesStaticDrop_base_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr bytesStaticDropName)
      bytesStaticDropSpec := by
  unfold bytesStaticDropSpec
  have hfn := (ls_lemma% fnOff "bytes::bytes::static_drop")
  tripleRatchet_fetches b (Rust.withPanics ext) hfn (num% (ls_off% "bytes::bytes::static_drop")) 4
  clear hfn
  dsimp only [tripleRatchetProgAtExt, bytesStaticDropName] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr "bytes::bytes::static_drop" = entry
  wp_init x s0
  examples_hide_fetches
  wp_steps
  wp_done

theorem bytesStaticDrop_base_ok {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr bytesStaticDropName)
      bytesStaticDropSpec :=
  bytesStaticDrop_base_ok_ext

theorem bytesStaticDropOk_ext {img : Obj.Image} {b : BitVec 64}
    {ext : String → Option (State → State)} :
    BytesStaticDropOkExt img b ext := by
  intro _ hb
  subst hb
  exact subroutine_ok_inImage img bytesStaticDrop_base_ok_ext

/-- `bytes::bytes::static_drop` meets `bytesStaticDropSpec` on `tripleRatchetProgAt b C ctl abs`
    under the triple-ratchet hypotheses (`BytesStaticDropOk`). -/
theorem bytesStaticDropOk {img : Obj.Image} {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)} :
    BytesStaticDropOk img b C A ctl S abs :=
  fun _ himg hb => bytesStaticDropOk_ext himg hb

/-! ## 3. Tail-Call `__rust_dealloc` Helper and Arithmetic Lemmas -/

private theorem stackAt_add_48_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

private theorem stackAt_add_48_comm_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt sp hookStack := by
  unfold stackAt
  have h0 : hookStack + 48 = 48 + hookStack := Nat.add_comm hookStack 48
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 (48 + hookStack)) 48 hookStack (by omega)
  have h1 : sp - BitVec.ofNat 64 (48 + hookStack) =
      sp - BitVec.ofNat 64 hookStack - 48#64 := by
    rw [BitVec.ofNat_add]
    bv_lin
  have h2 : sp - BitVec.ofNat 64 (48 + hookStack) + 48#64 =
      sp - BitVec.ofNat 64 hookStack := by
    rw [BitVec.ofNat_add]
    bv_lin
  rw [h0, hsplit, h2, h1]

private theorem pointsTo64_entails_exists (a v : BitVec 64) {R Q : SepProp}
    (h : R ⊢ Q) : ((a ↦₆₄ v) ∗ R) ⊢ ∃∗ x, (a ↦₆₄ x) ∗ Q :=
  Entails.trans (sepConj_mono_right h) (Entails.sepExists_intro (P := fun x => (a ↦₆₄ x) ∗ Q) v)

private theorem pointsTo64_entails_exists_single (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ x, (a ↦₆₄ x) :=
  Entails.sepExists_intro (P := fun x => a ↦₆₄ x) v

private theorem pointsTo64_6_entails_cells (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5)) ⊢ cells base 6 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_exists _ v0
    (pointsTo64_entails_exists _ v1
      (pointsTo64_entails_exists _ v2
        (pointsTo64_entails_exists _ v3
          (pointsTo64_entails_exists _ v4
            (pointsTo64_entails_exists_single _ v5)))))

private abbrev DeallocTailGhost :=
  BitVec 64 × List (BitVec 8) × Nat ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def rustDeallocTailSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec DeallocTailGhost where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align ∧
      LayoutOk bs.length align⌝ ∗
      A.pool ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) hookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp (hookStack + 48)

private theorem dealloc_tail_ok_of_dealloc {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64)
    (hdealloc : subroutine_ok P addr (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok P addr (rustDeallocTailSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cells (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre' : s0.mem ⊨
      (rustDeallocExternSpecWithStack A hookStack).pre (p, bs.length, align) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) := by
    unfold rustDeallocTailSpecWithStack at hpre
    unfold rustDeallocExternSpecWithStack
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
          A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 48#64) hookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_48_opt hstack, stackAt_add_48_comm_opt hstack] at h1
    exact (by ac_rfl :
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt s0.sp hookStack)) ∗ R) =
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗ stackAt s0.sp hookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R))) ▸ h1
  refine hdealloc.mono_outcome (p, bs.length, align)
    (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTailSpecWithStack
    unfold rustDeallocExternSpecWithStack at hpost
    dsimp only at hpost ⊢
    rw [stackAt_add_48_comm_opt hstack]
    exact (by ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp hookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt s0.sp hookStack)) ∗ R)) ▸ hpost
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

private theorem dealloc_tail_ok_of_dealloc_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64)
    (hdealloc : subroutine_ok P addr
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack))) :
    subroutine_ok P addr
      (specWithOptInv oimg (rustDeallocTailSpecWithStack A hookStack)) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cells (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre' : s0.mem ⊨
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack)).pre
        (p, bs.length, align) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) := by
    unfold specWithOptInv rustDeallocTailSpecWithStack at hpre
    unfold specWithOptInv rustDeallocExternSpecWithStack
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜OptCallInv oimg s0⌝ ∗
          ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
            (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
          A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 48#64) hookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells)))))
    rw [← stackAt_add_48_opt hstack, stackAt_add_48_comm_opt hstack] at h1
    exact (by ac_rfl :
      ((⌜OptCallInv oimg s0⌝ ∗
        ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt s0.sp hookStack)) ∗ R) =
      ((⌜OptCallInv oimg s0⌝ ∗
        ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗ stackAt s0.sp hookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R))) ▸ h1
  refine hdealloc.mono_outcome (p, bs.length, align)
    (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold specWithOptInv rustDeallocTailSpecWithStack
    unfold specWithOptInv rustDeallocExternSpecWithStack at hpost
    dsimp only at hpost ⊢
    rw [stackAt_add_48_comm_opt hstack]
    exact (by ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp hookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt s0.sp hookStack)) ∗ R)) ▸ hpost
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

@[simp, arm64_norm]
private theorem getLsbD_or_one (ptr : BitVec 64) : (ptr ||| 1#64).getLsbD 0 = true := by
  bv_bits

private theorem or_one_and_not_one {ptr : BitVec 64} (h : (ptr &&& 1#64) = 0#64) :
    (ptr ||| 1#64) &&& (-2#64) = ptr := by
  bv_bits

private theorem odd_drop_add {off len : Nat} (hoff : off ≤ len) :
    BitVec.ofNat 64 off + BitVec.ofNat 64 (len - off) = BitVec.ofNat 64 len := by
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le hoff]

private theorem ult_ofNat_false {off len : Nat} (hoff : off ≤ len) (hlen : len < 2 ^ 63) :
    (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 off) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : off < 2 ^ 64)]
  omega

private theorem getLsbD_63_ofNat_eq_false {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit_lt_two_pow hn, Bool.and_false]

/-! ## 4. Relocated `.rodata` Vtable Slot Helper (`hasReloc8At`) -/

private def afterRelocDisjoint (rs : List Obj.DataReloc) (off : Nat) : Bool :=
  rs.all (fun r => decide (r.off + r.width ≤ off ∨ off + 8 ≤ r.off))

private def hasReloc8At (N : Nat) : List Obj.DataReloc → Nat → Nat → Bool
  | [], _, _ => false
  | r :: rs, off, target =>
    decide (r.off + r.width ≤ N) &&
      ((decide (r.off = off ∧ r.width = 8 ∧ r.target = target) && afterRelocDisjoint rs off) ||
       hasReloc8At N rs off target)

private theorem dataReloc_apply_getElem?_self {base : BitVec 64} {d out : List (BitVec 8)}
    {r : Obj.DataReloc} (h : Obj.DataReloc.apply base d r = .ok out)
    (hb : r.off + r.width ≤ d.length)
    {j : Nat} (hj : j < r.width) :
    out[r.off + j]? = (Obj.bytesLE r.width (base + BitVec.ofNat 64 r.target))[j]? := by
  unfold Obj.DataReloc.apply at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  simp only [Except.ok.injEq] at h
  subst h
  have htk : (d.take r.off).length = r.off := by
    simp only [List.length_take]; omega
  have hpre : (d.take r.off ++ Obj.bytesLE r.width (base + BitVec.ofNat 64 r.target)).length =
      r.off + r.width := by
    rw [List.length_append, htk, ProofLib.ObjectLoad.RoDataFactsAux.bytesLE_length]
  rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega), htk,
    Nat.add_sub_cancel_left]

private theorem foldlM_dataReloc_of_hasReloc8At {base : BitVec 64} {N off target : Nat} :
    ∀ (rs : List Obj.DataReloc) (d out : List (BitVec 8)),
      rs.foldlM (Obj.DataReloc.apply base) d = .ok out →
      hasReloc8At N rs off target = true →
      N ≤ d.length →
      ∀ {j : Nat}, j < 8 →
        out[off + j]? = (Obj.bytesLE 8 (base + BitVec.ofNat 64 target))[j]?
  | [], _, _, _, hrel, _, _, _ => by simp [hasReloc8At] at hrel
  | r :: rs, d, out, hfold, hrel, hN, j, hj => by
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    simp only [hasReloc8At, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hrel
    rcases hrel with ⟨hrN, ⟨⟨hroff, hrw, hrtgt⟩, hafter⟩ | htail⟩
    · cases hr : Obj.DataReloc.apply base d r with
      | error e => rw [hr] at hfold; cases hfold
      | ok d' =>
        rw [hr] at hfold
        have hd' := dataReloc_apply_getElem?_self hr (by omega) (j := j) (by omega)
        rw [hroff, hrw, hrtgt] at hd'
        have hlen8 : (Obj.bytesLE 8 (base + BitVec.ofNat 64 target)).length = 8 :=
          ProofLib.ObjectLoad.RoDataFactsAux.bytesLE_length 8 _
        obtain ⟨x, hx⟩ : ∃ x, (Obj.bytesLE 8 (base + BitVec.ofNat 64 target))[j]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        rw [hx] at hd' ⊢
        exact ProofLib.ObjectLoad.RoDataFactsAux.foldlM_dataReloc_getElem?_of_disjoint
          rs d' out hfold hafter (k := off + j) (by omega) (by omega) hd'
    · cases hr : Obj.DataReloc.apply base d r with
      | error e => rw [hr] at hfold; cases hfold
      | ok d' =>
        rw [hr] at hfold
        have hdlen := ProofLib.ObjectLoad.RoDataFactsAux.dataReloc_apply_length hr (by omega)
        exact foldlM_dataReloc_of_hasReloc8At rs d' out hfold htail (by omega) hj

private theorem read64_of_read8_extractLsb' (m : Memory) (a v : BitVec 64)
    (h0 : m.read8 (a + 0#64) = v.extractLsb' 0 8)
    (h1 : m.read8 (a + 1#64) = v.extractLsb' 8 8)
    (h2 : m.read8 (a + 2#64) = v.extractLsb' 16 8)
    (h3 : m.read8 (a + 3#64) = v.extractLsb' 24 8)
    (h4 : m.read8 (a + 4#64) = v.extractLsb' 32 8)
    (h5 : m.read8 (a + 5#64) = v.extractLsb' 40 8)
    (h6 : m.read8 (a + 6#64) = v.extractLsb' 48 8)
    (h7 : m.read8 (a + 7#64) = v.extractLsb' 56 8) :
    m.read64 a = v := by
  simp only [Memory.read64, h0, h1, h2, h3, h4, h5, h6, h7]
  bv_bits

namespace ImageDataOffFacts

theorem img_dataOff : libsignalSessionImage.dataOff = num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) := rfl

end ImageDataOffFacts

private theorem rodata_reloc64_byte {img : Obj.Image} {m : Memory}
    (himg : Obj.Loads libsignalSessionImage img)
    (hro : img.RoDataLoaded m)
    {secOff target : Nat}
    (hsec : (secOff, 40) ∈ libsignalSessionImage.roData)
    (hoff : num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) ≤ secOff) (hlen : secOff < 2 ^ 32)
    (hrel : hasReloc8At libsignalSessionImage.data.length libsignalSessionImage.relocs
      (secOff - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 32) target = true)
    (j : Nat) (hj : j < 8) :
    some (m.read8 (img.base + BitVec.ofNat 64 secOff + 0x20#64 + BitVec.ofNat 64 j)) =
      (Obj.bytesLE 8 (img.base + BitVec.ofNat 64 target))[j]? := by
  have hdo : libsignalSessionImage.dataOff = num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) := ImageDataOffFacts.img_dataOff
  generalize_entry libsignalSessionImage = li reverting [libsignalSessionImage]
  obtain ⟨data, hfold, -, _, _, himg_eq⟩ := ProofLib.ObjectLoad.load_eq_ok himg
  have hd0 : li.data.length ≤
      (li.data ++ List.replicate li.bss 0).length := by
    rw [List.length_append]
    exact Nat.le_add_right _ _
  have hout := foldlM_dataReloc_of_hasReloc8At li.relocs _ data hfold hrel hd0 hj
  have hda : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff := by
    conv => lhs; rw [himg_eq]
  have hdata_eq : img.data = data := by
    conv => lhs; rw [himg_eq]
  have hroD : (img.base + BitVec.ofNat 64 secOff, 40) ∈ img.roData := by
    rw [show img.roData = li.roData.map (fun (o, n) => (img.base + BitVec.ofNat 64 o, n)) by
      conv => lhs; rw [himg_eq]]
    exact List.mem_map.mpr ⟨(secOff, 40), hsec, rfl⟩
  have hlen8 : (Obj.bytesLE 8 (img.base + BitVec.ofNat 64 target)).length = 8 :=
    ProofLib.ObjectLoad.RoDataFactsAux.bytesLE_length 8 _
  obtain ⟨x, hx⟩ : ∃ x, (Obj.bytesLE 8 (img.base + BitVec.ofNat 64 target))[j]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [← hdata_eq, hx] at hout
  have hi : secOff - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 32 + j < img.data.length := (List.getElem?_eq_some_iff.mp hout).1
  have haddr : img.dataAddr + BitVec.ofNat 64 (secOff - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 32 + j) =
      img.base + BitVec.ofNat 64 secOff + 0x20#64 + BitVec.ofNat 64 j := by
    have hsub : BitVec.ofNat 64 (num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44))) + BitVec.ofNat 64 (secOff - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 32 + j) =
        BitVec.ofNat 64 secOff + BitVec.ofNat 64 32 + BitVec.ofNat 64 j := by
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    rw [hda, hdo, BitVec.add_assoc img.base, hsub]
    bv_lin
  have hisro : img.isRoData (img.dataAddr + BitVec.ofNat 64 (secOff - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 32 + j)) = true := by
    unfold Obj.Image.isRoData
    rw [List.any_eq_true]
    refine ⟨_, hroD, ?_⟩
    have e : img.base + BitVec.ofNat 64 secOff + 0x20#64 + BitVec.ofNat 64 j -
        (img.base + BitVec.ofNat 64 secOff) = BitVec.ofNat 64 (32 + j) := by
      rw [BitVec.ofNat_add]; bv_lin
    rw [haddr, e]
    simp only [decide_eq_true_eq, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨h8, _⟩ := hro _ hi hisro
  rw [haddr] at h8
  rw [h8, hx, ← List.getElem?_eq_getElem hi, hout]

private theorem rodata_reloc64_slot {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hF : img.FrozenLoaded s)
    {secOff target : Nat}
    (hsec : (secOff, 40) ∈ libsignalSessionImage.roData)
    (hoff : num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) ≤ secOff) (hlen : secOff < 2 ^ 32)
    (hrel : hasReloc8At libsignalSessionImage.data.length libsignalSessionImage.relocs
      (secOff - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 32) target = true) :
    s.mem.canRead (img.base + BitVec.ofNat 64 secOff + 0x20#64) 8 = true ∧
    s.mem.read64 (img.base + BitVec.ofNat 64 secOff + 0x20#64) =
      img.base + BitVec.ofNat 64 target ∧
    ∀ {P : SepProp}, (s.mem ⊨ P) →
      s.mem ⊨ ((img.base + BitVec.ofNat 64 secOff + 0x20#64) ↦₆₄ᵣ
        (img.base + BitVec.ofNat 64 target)) ∗ P := by
  have hro : img.RoDataLoaded s.mem := hF.roData
  have hro40 : s.mem.RO (img.base + BitVec.ofNat 64 secOff) 40 :=
    ProofLib.rodata_ro himg ImageDataOffFacts.img_dataOff hsec (by decide) s.mem hro
  have hro8 : s.mem.RO (img.base + BitVec.ofNat 64 secOff + 0x20#64) 8 := by
    intro a ha
    apply hro40 a
    unfold InRegion at ha ⊢
    bv_omega
  have hb := fun j hj => rodata_reloc64_byte himg hro hsec hoff hlen hrel j hj
  have hread64 : s.mem.read64 (img.base + BitVec.ofNat 64 secOff + 0x20#64) =
      img.base + BitVec.ofNat 64 target :=
    read64_of_read8_extractLsb' s.mem
      (img.base + BitVec.ofNat 64 secOff + 0x20#64)
      (img.base + BitVec.ofNat 64 target)
      (Option.some.inj (hb 0 (by decide)))
      (Option.some.inj (hb 1 (by decide)))
      (Option.some.inj (hb 2 (by decide)))
      (Option.some.inj (hb 3 (by decide)))
      (Option.some.inj (hb 4 (by decide)))
      (Option.some.inj (hb 5 (by decide)))
      (Option.some.inj (hb 6 (by decide)))
      (Option.some.inj (hb 7 (by decide)))
  have hintro : ∀ {P : SepProp}, (s.mem ⊨ P) →
      s.mem ⊨ ((img.base + BitVec.ofNat 64 secOff + 0x20#64) ↦₆₄ᵣ
        (img.base + BitVec.ofNat 64 target)) ∗ P :=
    fun hP => (IsBlockRO.pointsTo64RO _ _).intro_of_ro hro8 hread64 hP
  have hemp : s.mem ⊨ emp := satisfies_emp s.mem
  have hcan : s.mem.canRead (img.base + BitVec.ofNat 64 secOff + 0x20#64) 8 = true :=
    (IsBlockRO.pointsTo64RO _ _).canRead (by decide) (hintro hemp)
  exact ⟨hcan, hread64, hintro⟩

set_option maxRecDepth 2000000 in
private theorem promotableOddVtable_in_roData :
    (num% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE"), 40) ∈ libsignalSessionImage.roData :=
  List.mem_of_elem_eq_true (by rfl_kernel)

set_option maxRecDepth 2000000 in
private theorem promotableEvenVtable_in_roData :
    (num% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE"), 40) ∈ libsignalSessionImage.roData :=
  List.mem_of_elem_eq_true (by rfl_kernel)

set_option maxRecDepth 2000000 in
private theorem staticVtable_hasReloc8At :
    hasReloc8At libsignalSessionImage.data.length libsignalSessionImage.relocs
      (num% (ls_reloc% (ls_off% "bytes::bytes::static_clone")) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 32) (num% (ls_off% "bytes::bytes::static_drop")) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
private theorem promotableOddVtable_hasReloc8At :
    hasReloc8At libsignalSessionImage.data.length libsignalSessionImage.relocs
      (num% (ls_sym% "bytes::bytes::PROMOTABLE_ODD_VTABLE") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 32) (num% (ls_off% "bytes::bytes::promotable_odd_drop")) = true := by
  rfl_kernel

set_option maxRecDepth 2000000 in
private theorem promotableEvenVtable_hasReloc8At :
    hasReloc8At libsignalSessionImage.data.length libsignalSessionImage.relocs
      (num% (ls_sym% "bytes::bytes::PROMOTABLE_EVEN_VTABLE") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) + 32) (num% (ls_off% "bytes::bytes::promotable_even_drop")) = true := by
  rfl_kernel

/-- Relocated `.rodata` vtable `+0x20` slot lookup for `STATIC_VTABLE`, `PROMOTABLE_ODD_VTABLE`,
    and `PROMOTABLE_EVEN_VTABLE` (`BytesVtableSlotLoadedStmt`). -/
theorem bytesVtableSlotLoaded : BytesVtableSlotLoadedStmt := by
  intro img s ptr len himg hF
  rw [bytesVtable_eq_off, bytesDropFnAddr_eq_off]
  split_ifs with hlen0 heven
  · exact rodata_reloc64_slot himg hF staticVtable_in_roData
      (by decide) (by decide) staticVtable_hasReloc8At
  · exact rodata_reloc64_slot himg hF promotableEvenVtable_in_roData
      (by decide) (by decide) promotableEvenVtable_hasReloc8At
  · exact rodata_reloc64_slot himg hF promotableOddVtable_in_roData
      (by decide) (by decide) promotableOddVtable_hasReloc8At

/-! ## 5. Unified Parameterized `promotable_even_drop`, `promotable_odd_drop`, and Vtable Dispatch -/

def promotableEvenDropSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp (hookStack + 48)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp (hookStack + 48)

def promotableOddDropSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp (hookStack + 48)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp (hookStack + 48)

def bytesVtableDropSpecWithStack (A : RustAlloc) (hookStack : Nat)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) : Spec Unit where
  pre := fun _ s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp (hookStack + 48)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp (hookStack + 48)

theorem promotableEvenDrop_base_ok_of_dealloc_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableEvenDropName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "bytes::bytes::promotable_even_drop"))
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableEvenDropName)
      (specWithOptInv oimg (promotableEvenDropSpecWithStack A hookStack)) := by
  unfold specWithOptInv promotableEvenDropSpecWithStack bytesBoxU8Buf
  have hfn := (ls_lemma% fnOff "bytes::bytes::promotable_even_drop")
  have hdealloc := dealloc_tail_ok_of_dealloc_opt hstack hdealloc_ext
  tripleRatchet_fetches b (Rust.withPanics ext) hfn (num% (ls_off% "bytes::bytes::promotable_even_drop")) 240
  clear hfn hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  dsimp only [tripleRatchetProgAtExt, promotableEvenDropName] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr "bytes::bytes::promotable_even_drop" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have heven : (ptr &&& 1#64) = 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hand : (ptr ||| 1#64) &&& (-2#64) = ptr := or_one_and_not_one heven
  apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "bytes::bytes::promotable_even_drop")) hinv0
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    have hadd_even' : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

theorem promotableOddDrop_base_ok_of_dealloc_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableOddDropName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "bytes::bytes::promotable_odd_drop"))
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableOddDropName)
      (specWithOptInv oimg (promotableOddDropSpecWithStack A hookStack)) := by
  unfold specWithOptInv promotableOddDropSpecWithStack bytesBoxU8Buf
  have hfn := (ls_lemma% fnOff "bytes::bytes::promotable_odd_drop")
  have hdealloc := dealloc_tail_ok_of_dealloc_opt hstack hdealloc_ext
  tripleRatchet_fetches b (Rust.withPanics ext) hfn (num% (ls_off% "bytes::bytes::promotable_odd_drop")) 236
  clear hfn hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  dsimp only [tripleRatchetProgAtExt, promotableOddDropName] at *
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr "bytes::bytes::promotable_odd_drop" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have hodd : (ptr &&& 1#64) ≠ 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hlsb0 : ptr.getLsbD 0 = true := getLsbD_zero_iff.mpr hodd
  apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "bytes::bytes::promotable_odd_drop")) hinv0
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    have hadd_odd : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

theorem bytesVtableDrop_base_ok_of_drops_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (heven_ok : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableEvenDropName)
      (specWithOptInv oimg (promotableEvenDropSpecWithStack A hookStack)))
    (hodd_ok : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableOddDropName)
      (specWithOptInv oimg (promotableOddDropSpecWithStack A hookStack)))
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (bytesDropFnAddr b ptr bs.length)
      (specWithOptInv oimg (bytesVtableDropSpecWithStack A hookStack ptr bs off)) := by
  refine subroutine_ok_outcome_intro ?_
  intro _ R s0 hpc hrun hpre hsp
  by_cases hbs : bs = []
  · subst hbs
    have haddr : bytesDropFnAddr b ptr ([] : List (BitVec 8)).length =
        (tripleRatchetProgAtExt b ext).fnAddr bytesStaticDropName := by
      unfold bytesDropFnAddr tripleRatchetProgAtExt
      simp only [List.length_nil, ↓reduceIte, Program.fnAddr_rebase]
    rw [haddr] at hpc
    unfold specWithOptInv bytesVtableDropSpecWithStack bytesBoxU8Buf at hpre
    simp only [↓reduceIte, sepConj_emp, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_hinv, _, _, hmem⟩
    have hpre_static : s0.mem ⊨ bytesStaticDropSpec.pre () s0 ∗
        (A.pool ∗ (stackAt s0.sp (hookStack + 48) ∗ R)) := by
      unfold bytesStaticDropSpec
      simpa only [emp_sepConj] using hmem
    refine (bytesStaticDrop_base_ok_ext (b := b) (ext := ext)).mono_outcome ()
      (A.pool ∗ (stackAt s0.sp (hookStack + 48) ∗ R)) s0 hpc hrun hpre_static hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      unfold specWithOptInv bytesVtableDropSpecWithStack
      unfold bytesStaticDropSpec at hpost
      simpa only [sepConj_assoc] using hpost
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_ne : bs.length ≠ 0 := by omega
    by_cases heven : (ptr &&& 1#64) = 0#64
    · have haddr : bytesDropFnAddr b ptr bs.length =
          (tripleRatchetProgAtExt b ext).fnAddr promotableEvenDropName := by
        unfold bytesDropFnAddr tripleRatchetProgAtExt
        simp only [hlen_ne, heven, ↓reduceIte, Program.fnAddr_rebase]
      rw [haddr] at hpc
      have hpre_even :
          s0.mem ⊨ (specWithOptInv oimg (promotableEvenDropSpecWithStack A hookStack)).pre
            (ptr, bs, off) s0 ∗ R := by
        unfold specWithOptInv bytesVtableDropSpecWithStack bytesData bytesPtr at hpre
        unfold specWithOptInv promotableEvenDropSpecWithStack
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc,
          satisfies_pure_sepConj] at hpre
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre with ⟨hinv, ⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨hinv, ⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact heven_ok.mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_even hsp fun _ hout => hout
    · have haddr : bytesDropFnAddr b ptr bs.length =
          (tripleRatchetProgAtExt b ext).fnAddr promotableOddDropName := by
        unfold bytesDropFnAddr tripleRatchetProgAtExt
        simp only [hlen_ne, heven, ↓reduceIte, Program.fnAddr_rebase]
      rw [haddr] at hpc
      have hpre_odd :
          s0.mem ⊨ (specWithOptInv oimg (promotableOddDropSpecWithStack A hookStack)).pre
            (ptr, bs, off) s0 ∗ R := by
        unfold specWithOptInv bytesVtableDropSpecWithStack bytesData bytesPtr at hpre
        unfold specWithOptInv promotableOddDropSpecWithStack
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc,
          satisfies_pure_sepConj] at hpre
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre with ⟨hinv, ⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨hinv, ⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact hodd_ok.mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_odd hsp fun _ hout => hout

/-! ## 6. Base (`AllocContracts`) and Refinement (`AllocContractsX`) Specializations -/

theorem promotableEvenDrop_base_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableEvenDropName)
      (promotableEvenDropSpec A) :=
  subroutine_ok_of_optNone
    (promotableEvenDrop_base_ok_of_dealloc_opt (by decide)
      (dealloc_opt_of_base hA (by fnoff_eq)))

theorem promotableEvenDrop_base_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr promotableEvenDropName)
      (promotableEvenDropSpec A) :=
  promotableEvenDrop_base_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

theorem promotableEvenDropOk_ext {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} :
    PromotableEvenDropOkExt img b A ext := by
  intro hA _ hb
  subst hb
  exact subroutine_ok_inImage img (promotableEvenDrop_base_ok_ext hA)

/-- `bytes::bytes::promotable_even_drop` meets `promotableEvenDropSpec` on `tripleRatchetProgAt b C ctl abs`
    under the triple-ratchet hypotheses (`PromotableEvenDropOk`). -/
theorem promotableEvenDropOk {img : Obj.Image} {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)} :
    PromotableEvenDropOk img b C A ctl S abs :=
  fun hH himg hb => promotableEvenDropOk_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hH.alloc) himg hb

theorem promotableOddDrop_base_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promotableOddDropName)
      (promotableOddDropSpec A) :=
  subroutine_ok_of_optNone
    (promotableOddDrop_base_ok_of_dealloc_opt (by decide)
      (dealloc_opt_of_base hA (by fnoff_eq)))

theorem promotableOddDrop_base_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr promotableOddDropName)
      (promotableOddDropSpec A) :=
  promotableOddDrop_base_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

theorem promotableOddDropOk_ext {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} :
    PromotableOddDropOkExt img b A ext := by
  intro hA _ hb
  subst hb
  exact subroutine_ok_inImage img (promotableOddDrop_base_ok_ext hA)

/-- `bytes::bytes::promotable_odd_drop` meets `promotableOddDropSpec` on `tripleRatchetProgAt b C ctl abs`
    under the triple-ratchet hypotheses (`PromotableOddDropOk`). -/
theorem promotableOddDropOk {img : Obj.Image} {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)} :
    PromotableOddDropOk img b C A ctl S abs :=
  fun hH himg hb => promotableOddDropOk_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hH.alloc) himg hb

theorem bytesVtableDrop_base_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      (bytesDropFnAddr b ptr bs.length)
      (bytesVtableDropSpec A ptr bs off) :=
  subroutine_ok_of_optNone
    (bytesVtableDrop_base_ok_of_drops_opt
      (subroutine_ok_to_optNone (promotableEvenDrop_base_ok_ext hA))
      (subroutine_ok_to_optNone (promotableOddDrop_base_ok_ext hA))
      ptr bs off)

theorem bytesVtableDrop_base_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      (bytesDropFnAddr b ptr bs.length)
      (bytesVtableDropSpec A ptr bs off) :=
  bytesVtableDrop_base_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) ptr bs off

theorem bytesVtableDropOk_ext {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    BytesVtableDropOkExt img b A ext ptr bs off := by
  intro hA _ hb
  subst hb
  exact subroutine_ok_inImage img (bytesVtableDrop_base_ok_ext hA ptr bs off)

/-- Unified vtable `drop` dispatch (`bytesDropFnAddr b ptr bs.length`) meets `bytesVtableDropSpec`
    on `tripleRatchetProgAt b C ctl abs` under the triple-ratchet hypotheses (`BytesVtableDropOk`). -/
theorem bytesVtableDropOk {img : Obj.Image} {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    BytesVtableDropOk img b C A ctl S abs ptr bs off :=
  fun hH himg hb => bytesVtableDropOk_ext ptr bs off (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hH.alloc) himg hb

theorem promotableEvenDrop_base_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr promotableEvenDropName)
      ((promotableEvenDropSpecX A).inImage img) :=
  promotableEvenDrop_base_ok_of_dealloc_opt (oimg := some img) (by decide)
    (dealloc_opt_of_x hA (by fnoff_eq))

theorem promotableEvenDropOk_ext_x {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} :
    PromotableEvenDropOkExtX img b A ext := by
  intro hA _ hb
  subst hb
  exact promotableEvenDrop_base_ok_ext_x hA

theorem promotableOddDrop_base_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr promotableOddDropName)
      ((promotableOddDropSpecX A).inImage img) :=
  promotableOddDrop_base_ok_of_dealloc_opt (oimg := some img) (by decide)
    (dealloc_opt_of_x hA (by fnoff_eq))

theorem promotableOddDropOk_ext_x {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} :
    PromotableOddDropOkExtX img b A ext := by
  intro hA _ hb
  subst hb
  exact promotableOddDrop_base_ok_ext_x hA

theorem bytesVtableDrop_base_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (bytesDropFnAddr img.base ptr bs.length)
      ((bytesVtableDropSpecX A ptr bs off).inImage img) :=
  bytesVtableDrop_base_ok_of_drops_opt (oimg := some img)
    (promotableEvenDrop_base_ok_ext_x hA)
    (promotableOddDrop_base_ok_ext_x hA)
    ptr bs off

theorem bytesVtableDropOk_ext_x {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    BytesVtableDropOkExtX img b A ext ptr bs off := by
  intro hA _ hb
  subst hb
  exact bytesVtableDrop_base_ok_ext_x hA ptr bs off

/-! ## 7. Relocatable `[LibsignalPlacement]` Contracts (Blocks `224`, `267`, `268`) -/

abbrev lsBytesRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

theorem ls_externAt?_rustDealloc [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ lsBytesRustDeallocSym) = H lsBytesRustDeallocSym := by
  have hmem : lsBytesRustDeallocSym ∈ libsignalSessionExterns := by decide
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by simp [hk, hget]) hi hunmut

theorem ls_hook_ok_rustDealloc [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {spec : Spec α} (hsat : HookSat H lsBytesRustDeallocSym spec)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsBytesRustDeallocSym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((ls_externAt?_rustDealloc hi hunmut).trans hf) hok

/-- Block `224`: `bytes::bytes::static_drop` meets `bytesStaticDropSpec` under `[LibsignalPlacement]`. -/
theorem bytesStaticDrop_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_224).rebase (blkPl_224).base H) (blkPl_224).base
      bytesStaticDropSpec := by
  unfold bytesStaticDropSpec
  wp_init x s0
  wp_steps
  wp_done

theorem promotableEvenDrop_placed_ok_of_dealloc_opt [LibsignalPlacement]
    {oimg : Option Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_237).rebase (blkPl_237).base H)
      (lsρ lsBytesRustDeallocSym)
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack))) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (specWithOptInv oimg (promotableEvenDropSpecWithStack A hookStack)) := by
  unfold specWithOptInv promotableEvenDropSpecWithStack bytesBoxU8Buf
  have hdealloc := dealloc_tail_ok_of_dealloc_opt hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have heven : (ptr &&& 1#64) = 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hand : (ptr ||| 1#64) &&& (-2#64) = ptr := or_one_and_not_one heven
  apply SepWP.seq_optImage (mid := lsρ lsBytesRustDeallocSym) hinv0
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    have hadd_even' : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

theorem promotableEvenDrop_placed_ok_of_dealloc [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_237).rebase (blkPl_237).base H)
      (lsρ lsBytesRustDeallocSym)
      (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpecWithStack A hookStack) := by
  unfold promotableEvenDropSpecWithStack bytesBoxU8Buf
  have hdealloc := dealloc_tail_ok_of_dealloc hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have heven : (ptr &&& 1#64) = 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hand : (ptr ||| 1#64) &&& (-2#64) = ptr := or_one_and_not_one heven
  apply SepWP.cut (mid := lsρ lsBytesRustDeallocSym)
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have hadd_even' : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

/-- Block `237`: `bytes::bytes::promotable_even_drop` meets `promotableEvenDropSpec`
    under `[LibsignalPlacement]`. -/
theorem promotableEvenDrop_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpec A) :=
  promotableEvenDrop_placed_ok_of_dealloc (by decide)
    (rustDeallocExternWithStack_of_rustDealloc
      (ls_hook_ok_rustDealloc hdealloc) (by decide) (by decide))

theorem promotableOddDrop_placed_ok_of_dealloc_opt [LibsignalPlacement]
    {oimg : Option Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_236).rebase (blkPl_236).base H)
      (lsρ lsBytesRustDeallocSym)
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack))) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (specWithOptInv oimg (promotableOddDropSpecWithStack A hookStack)) := by
  unfold specWithOptInv promotableOddDropSpecWithStack bytesBoxU8Buf
  have hdealloc := dealloc_tail_ok_of_dealloc_opt hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have hodd : (ptr &&& 1#64) ≠ 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hlsb0 : ptr.getLsbD 0 = true := getLsbD_zero_iff.mpr hodd
  apply SepWP.seq_optImage (mid := lsρ lsBytesRustDeallocSym) hinv0
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    have hadd_odd : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

theorem promotableOddDrop_placed_ok_of_dealloc [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_236).rebase (blkPl_236).base H)
      (lsρ lsBytesRustDeallocSym)
      (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpecWithStack A hookStack) := by
  unfold promotableOddDropSpecWithStack bytesBoxU8Buf
  have hdealloc := dealloc_tail_ok_of_dealloc hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have hodd : (ptr &&& 1#64) ≠ 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hlsb0 : ptr.getLsbD 0 = true := getLsbD_zero_iff.mpr hodd
  apply SepWP.cut (mid := lsρ lsBytesRustDeallocSym)
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have hadd_odd : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

/-- Block `236`: `bytes::bytes::promotable_odd_drop` meets `promotableOddDropSpec`
    under `[LibsignalPlacement]`. -/
theorem promotableOddDrop_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpec A) :=
  promotableOddDrop_placed_ok_of_dealloc (by decide)
    (rustDeallocExternWithStack_of_rustDealloc
      (ls_hook_ok_rustDealloc hdealloc) (by decide) (by decide))

/-- Relocatable `.rodata` vtable `+0x20` slot lookup under `[LibsignalPlacement]`:
    for any `m` satisfying `LibsignalRoLoaded lsmpl m`, the 8-byte word at
    `bytesPlacedVtable ptr len + 0x20#64` holds `bytesPlacedDropFnAddr ptr len` read-only. -/
theorem bytesVtableSlotLoaded_placed_intro [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) (ptr : BitVec 64) (len : Nat)
    {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((bytesPlacedVtable ptr len + 0x20#64) ↦₆₄ᵣ bytesPlacedDropFnAddr ptr len) ∗ P := by
  unfold bytesPlacedVtable bytesPlacedDropFnAddr staticVtablePlacedAddr
    promotableEvenVtablePlacedAddr promotableOddVtablePlacedAddr
  by_cases hlen : len = 0
  · simp only [hlen, ↓reduceIte]
    exact lsro_reloc64_intro hro (sym := staticVtableSym) (off := 32)
      (tgt := bytesStaticDropName) rfl (by simp) (by decide +kernel) hP
  · by_cases heven : (ptr &&& 1#64) = 0#64
    · simp only [hlen, heven, ↓reduceIte]
      exact lsro_reloc64_intro hro (sym := promotableEvenVtableName) (off := 32)
        (tgt := promotableEvenDropName) rfl (by simp) (by decide +kernel) hP
    · simp only [hlen, heven, ↓reduceIte]
      exact lsro_reloc64_intro hro (sym := promotableOddVtableName) (off := 32)
        (tgt := promotableOddDropName) rfl (by simp) (by decide +kernel) hP

theorem bytesVtableDrop_placed_ok_of_drops [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {hookStack : Nat}
    (heven_ok : subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpecWithStack A hookStack))
    (hodd_ok : subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpecWithStack A hookStack))
    (hi : i < 619 := by decide)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCodeLoaded lsmpl (bytesVtableDropSpecWithStack A hookStack ptr bs off)) := by
  refine subroutine_ok_outcome_intro ?_
  intro _ R s0 hpc hrun hpre hsp
  by_cases hbs : bs = []
  · subst hbs
    have haddr : bytesPlacedDropFnAddr ptr ([] : List (BitVec 8)).length = (blkPl_224).base := rfl
    rw [haddr] at hpc
    have hstatic := ls_subroutine_ok_of_block (callerProg := callerProg)
      (subroutine_ok_withLsCodeLoaded_of_plain (bytesStaticDrop_placed_ok H)) hi
    have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
    unfold bytesVtableDropSpecWithStack bytesBoxU8Buf at hpre0
    simp only [↓reduceIte, sepConj_emp, sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨_, _, hmem⟩
    have hpre_static : s0.mem ⊨ (withLsCodeLoaded lsmpl bytesStaticDropSpec).pre () s0 ∗
        (A.pool ∗ (stackAt s0.sp (hookStack + 48) ∗ R)) := by
      dsimp only [withLsCodeLoaded, bytesStaticDropSpec]
      rw [emp_sepConj, satisfies_pure_sepConj]
      exact ⟨hcl, hmem⟩
    refine hstatic.mono_outcome () (A.pool ∗ (stackAt s0.sp (hookStack + 48) ∗ R)) s0 hpc hrun hpre_static hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack]
      dsimp only [withLsCodeLoaded, bytesStaticDropSpec] at hpost
      simpa only [sepConj_assoc] using hpost
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_ne : bs.length ≠ 0 := by omega
    by_cases heven : (ptr &&& 1#64) = 0#64
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = (blkPl_237).base := by
        unfold bytesPlacedDropFnAddr
        simp only [hlen_ne, heven, ↓reduceIte]
        rfl
      rw [haddr] at hpc
      have heven_cl := ls_subroutine_ok_of_block (callerProg := callerProg)
        (subroutine_ok_withLsCodeLoaded_of_plain heven_ok) hi
      have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
      have hpre_even :
          s0.mem ⊨ (withLsCodeLoaded lsmpl (promotableEvenDropSpecWithStack A hookStack)).pre
            (ptr, bs, off) s0 ∗ R := by
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack, bytesData, bytesPtr] at hpre0
        dsimp only [withLsCodeLoaded, promotableEvenDropSpecWithStack]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        refine ⟨hcl, ?_⟩
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpre0
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre0 with ⟨⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact heven_cl.mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_even hsp fun _ hout => hout
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = (blkPl_236).base := by
        unfold bytesPlacedDropFnAddr
        simp only [hlen_ne, heven, ↓reduceIte]
        rfl
      rw [haddr] at hpc
      have hodd_cl := ls_subroutine_ok_of_block (callerProg := callerProg)
        (subroutine_ok_withLsCodeLoaded_of_plain hodd_ok) hi
      have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
      have hpre_odd :
          s0.mem ⊨ (withLsCodeLoaded lsmpl (promotableOddDropSpecWithStack A hookStack)).pre
            (ptr, bs, off) s0 ∗ R := by
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack, bytesData, bytesPtr] at hpre0
        dsimp only [withLsCodeLoaded, promotableOddDropSpecWithStack]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        refine ⟨hcl, ?_⟩
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpre0
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre0 with ⟨⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact hodd_cl.mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_odd hsp fun _ hout => hout

/-- Unified relocatable vtable `drop` dispatch (`entry_pc = bytesPlacedDropFnAddr ptr bs.length`)
    meets `bytesVtableDropSpec` for any caller block `i` under `[LibsignalPlacement]`. -/
theorem bytesVtableDrop_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCodeLoaded lsmpl (bytesVtableDropSpec A ptr bs off)) :=
  bytesVtableDrop_placed_ok_of_drops
    (promotableEvenDrop_placed_ok hdealloc)
    (promotableOddDrop_placed_ok hdealloc)
    hi ptr bs off

end CryptoVerification.LibsignalTripleRatchet
