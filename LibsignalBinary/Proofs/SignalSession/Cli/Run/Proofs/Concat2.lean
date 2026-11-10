/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

/-!
# Two-Slice Byte Concatenation (`<[&[u8]] as alloc::slice::Concat<u8>>::concat`)

Proves `cliConcat2_ok`, showing that the specialized 2-slice `Concat<u8>::concat` instance in
`signal-session` meets `cliConcat2Spec` across all four empty/non-empty slice combinations when
`bs0.length + bs1.length < 2 ^ 63`.
-/

abbrev cliConcatName : String := "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"

def cliConcat2Spec (A : RustAlloc) (stk : Nat) : Spec SpqrV1.ChainProofs.SliceConcat2Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      x.bs0.length + x.bs1.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      SpqrV1.ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗ SpqrV1.ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (x.bs0 ++ x.bs1) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      SpqrV1.ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗ SpqrV1.ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s0.sp stk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

section Helpers

open ProofLib.ProgramReflection CryptoVerification.LibsignalSessionRepr
  CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes CryptoVerification.libsignalSessionCode_tree cliConcatBin
  [(ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") →
   (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" + 364)]

private theorem cliConcat_fnOff :
    libsignalSessionCode.fnOff cliConcatName =
      ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" :=
  ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"

private abbrev cliConcatStack : Nat := 96 + extHookStack

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_cliConcat (sp : BitVec 64) :
    stackAt sp cliConcatStack =
      stackAt (sp - 96#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16384 12 (by decide)
  have hsum : 16384 + 8 * 12 = cliConcatStack := by decide
  rw [hsum] at h1
  change stackAt sp cliConcatStack =
    stackAt (sp - 96#64) extHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

private theorem stackAt_split_ge (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

private theorem subroutine_ok_frame_weaken {α : Type} {prog : Program} {entry : BitVec 64}
    {spec spec' : Spec α} (F : α → State → SepProp)
    (h : subroutine_ok prog entry spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf ∗ F x s0 ⊢ spec'.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp => ?_
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  refine h.mono_outcome x (F x s0 ∗ R) s0 hpc hrun hp' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan_st, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) hq
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem ofNat_getLsbD_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_getElem_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false h

private theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_ult_of_le {a b : Nat} (hle : a ≤ b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

private theorem pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

private def cliMemcpyBytesAtSpecX (ro : Bool) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack

private theorem cliMemcpy_bytesAt_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliConcatName +
        BitVec.ofNat 64
          (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" "memcpy"))
      ((cliMemcpyBytesAtSpecX ro).inImage img) := by
  cases ro
  · have hmc := memcpy_ok_at2_ext_x hA (name := cliConcatName)
      (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" "memcpy")
      (by rw [cliConcat_fnOff, (ls_stub% "memcpy")])
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ (session2MemcpySpecX.inImage img).pre (dst, src, bs) s0 ∗ R := by
      simp only [Spec.inImage, cliMemcpyBytesAtSpecX, session2MemcpySpecX,
        SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact ⟨hpre.1, ⟨hpre.2.1.1, hpre.2.1.2.1, hpre.2.1.2.2.1⟩, hpre.2.2⟩
    refine hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [Spec.inImage, cliMemcpyBytesAtSpecX, session2MemcpySpecX,
        SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)
  · have hmc_ro := SpqrV1.Alloc.session_memcpy_region_ro_ok_at (b := img.base) hRO cliConcatName
      (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" "memcpy")
      (by rw [cliConcat_fnOff, (ls_stub% "memcpy")])
    apply SpqrV1.Alloc.subroutine_ok_inImage img
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ SpqrV1.Alloc.sessionMemcpyRegionROSpec.pre (dst, src, bs) s0 ∗
        (stackAt s0.sp extHookStack ∗ R) := by
      simp only [cliMemcpyBytesAtSpecX, SpqrV1.Alloc.sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] at hpre ⊢
      exact hpre
    refine hmc_ro.mono_outcome (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal
      fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simp only [cliMemcpyBytesAtSpecX, SpqrV1.Alloc.sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] at hpost ⊢
      exact hpost
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1

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

private theorem vecU8_of_append_pos (A : RustAlloc) (v p' : BitVec 64)
    (bs0 bs1 : List (BitVec 8))
    (hpos : 0 < bs0.length + bs1.length) (hlt : bs0.length + bs1.length < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗
      A.live p' (bs0.length + bs1.length) 1 ∗ (p' ↦ₛ (bs0 ++ bs1)) ⊢
      vecU8 A v (bs0 ++ bs1) := by
  rw [← List.length_append]
  exact vecU8_of_pos A v p' (bs0 ++ bs1) (by rw [List.length_append]; exact hpos)
    (by rw [List.length_append]; exact hlt) hp'

set_option maxHeartbeats 1600000 in
private theorem cliConcat2_exact_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliConcatName)
      ((cliConcat2Spec A cliConcatStack).inImage img) := by
  unfold Spec.inImage cliConcat2Spec
  simp only [memRegion_24_cells, stackAt_cliConcat, sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff cliConcatName =
      ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" :=
    cliConcat_fnOff
  have hshim := shim_ok_at2_ext_x hA (name := cliConcatName)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_ext_x hA (name := cliConcatName)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "__rustc::__rust_alloc")
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hmc_any := cliMemcpy_bytesAt_ok_at hA hRO
  clear hRO
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext)
    (name := cliConcatName)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "alloc::raw_vec::handle_error")
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  code_fetches_range CryptoVerification.libsignalSessionCode cliConcatBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]")) 0 364
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmc_any hpanic ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr cliConcatName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨‹_›, ‹_›⟩
  have hmax : bs0.length + bs1.length < 2 ^ 63 := ‹_›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have htot_lt63 : bs1.length + bs0.length < 2 ^ 63 := by omega
  have htot_lt64 : bs1.length + bs0.length < 2 ^ 64 := by omega
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have hadd_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add]
  have hsub_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
      omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]
      omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length))[63] = false :=
    ofNat_getElem_63_false (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi1 : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have h0_eq : bs0 = [] ∨ 0 < bs0.length := by cases bs0 <;> simp
  have h1_eq : bs1 = [] ∨ 0 < bs1.length := by cases bs1 <;> simp
  rcases h0_eq with rfl | hpos0 <;>
    rcases h1_eq with rfl | hpos1
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.nil_append] at *
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply SepWP.fold (vecU8_of_zero A outVec) (by sep_focus)
    wp_done
  ·
    simp only [List.length_nil, Nat.zero_add, BitVec.ofNat_eq_ofNat, List.nil_append] at *
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false :=
      ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk bs1.length 1 := ⟨hpos1, hpow1, by omega⟩
    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (108)) hinv0
    apply SepWP.seq_inImage
      (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv1
    have ⟨hF1, hsym1⟩ := hinv1
    apply SepWP.seq_inImage
      (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
        "__rustc::__rust_alloc")) hinv1
    wp_apply
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hF2, hsym2⟩
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_sf1
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
          "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_inImage
        (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
          "memcpy")) hinv_sf1
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hF3, hsym3⟩
      wp_apply using (hmc_any ro1)
      wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs1 hpos1 hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false :=
      ofNat_beq_zero_false hpos0 h0_lt64
    have hlay : LayoutOk bs0.length 1 := ⟨hpos0, hpow1, by omega⟩
    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (108)) hinv0
    apply SepWP.seq_inImage
      (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv1
    have ⟨hF1, hsym1⟩ := hinv1
    apply SepWP.seq_inImage
      (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
        "__rustc::__rust_alloc")) hinv1
    wp_apply
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hF2, hsym2⟩
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_sf1
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
          "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_inImage
        (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
          "memcpy")) hinv_sf1
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hF3, hsym3⟩
      wp_apply using (hmc_any ro0)
      wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs0 hpos0 hmax hoom) (by sep_focus)
      wp_done
  ·
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false :=
      ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false :=
      ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk (bs0.length + bs1.length) 1 := ⟨by omega, hpow1, by omega⟩
    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (108)) hinv0
    apply SepWP.seq_inImage
      (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv1
    have ⟨hF1, hsym1⟩ := hinv1
    apply SepWP.seq_inImage
      (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
        "__rustc::__rust_alloc")) hinv1
    wp_apply
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hF2, hsym2⟩
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_sf1
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true, sepConj_assoc]
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
          "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by
        rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_inImage
        (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
          "memcpy")) hinv_sf1
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hinv3
      have ⟨hF3, hsym3⟩ := hinv3
      apply SepWP.seq_inImage (mid := entry + bv% (172)) hinv3
      wp_apply using (hmc_any ro0)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hinv3'
      apply SepWP.seq_inImage
        (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
          "memcpy")) hinv3'
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      rintro ⟨hF4, hsym4⟩
      wp_apply using (hmc_any ro1)
      wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs1).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs1
        (by omega) hmax hoom) (by sep_focus)
      wp_done

end Helpers

theorem cliConcat2_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliConcatName)
      ((cliConcat2Spec A stk).inImage img) := by
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliConcatStack))
    (cliConcat2_exact_ok hA hRO) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
  · intro x s0
    dsimp only [Spec.inImage, cliConcat2Spec]
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro x s0 sf
    dsimp only [Spec.inImage, cliConcat2Spec]
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro _ s0 sf
    dsimp only [Spec.inImage, cliConcat2Spec]
    rw [sepConj_assoc]
    exact sepConj_mono_right (entails_anyHeap _)

example : libsignalSessionCode.fnOff cliConcatName =
    num% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]") :=
  ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"

end CryptoVerification.SignalSession.Cli.RunProofs
