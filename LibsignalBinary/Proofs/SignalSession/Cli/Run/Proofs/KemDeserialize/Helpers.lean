/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.Spec
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Exact-Stack Helpers and Proof for `kem::Key<Public>::deserialize`

Stack/result-slot decompositions, `key_length` and `memcpy` callee wrappers, and the exact-stack
symbolic execution proof `cliKemDeserialize_exact_ok`.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.KemDeserializeHelpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev kemKeyLengthName : String :=
  "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length"

abbrev cliKemDeserStack : Nat := 48 + extHookStack

gen_decodes CryptoVerification.libsignalSessionCode_tree kemDeserBin
  [(ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length") →
   (ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length" + 8),
   (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize") →
   (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize" + 252)]

theorem cliKemDeserialize_fnOff :
    libsignalSessionCode.fnOff cliKemDeserializeName =
      ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize" :=
  ls_lemma% fnOff "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"

private theorem kemKeyLength_fnOff :
    libsignalSessionCode.fnOff kemKeyLengthName =
      ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length" :=
  ls_lemma% fnOff "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length"

/-! ## Stack & Result Slot Decompositions -/

theorem stackAt_split_ge (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

theorem subroutine_ok_frame_weaken {α : Type} {prog : Program} {entry : BitVec 64}
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

private theorem stackAt_kemDeser (sp : BitVec 64) :
    stackAt sp cliKemDeserStack =
      stackAt (sp - 48#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗
        ((sp - 32#64) ↦₆₄ v2) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
        ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16384 6 (by decide)
  have hsum : 16384 + 8 * 6 = cliKemDeserStack := by decide
  rw [hsum] at h1
  change stackAt sp cliKemDeserStack =
    stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 at h1
  have hc6 : cells (sp - 48#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗
        ((sp - 32#64) ↦₆₄ v2) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
        ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
    cells_unfold
  rw [h1, hc6]

private theorem memRegion_24_split_8_16 (r : BitVec 64) :
    memRegion r 24 = (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ memRegion (r + 8#64) 16 := by
  rw [show (24 : Nat) = 8 + 16 by rfl, ProofLib.memRegion_split r 8 16 (by decide),
    ProofLib.memRegion_eight]

private theorem memRegion_24_split_badType (r : BitVec 64) :
    memRegion r 24 =
      (∃∗ b1 : BitVec 8, ∃∗ w0 : BitVec 64,
        (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₈ b1) ∗ memRegion (r + 9#64) 15) := by
  rw [memRegion_24_split_8_16 r,
    show (16 : Nat) = 1 + 15 by rfl,
    ProofLib.memRegion_split (r + 8#64) 1 15 (by decide),
    ProofLib.memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_24_split_badLen (r : BitVec 64) :
    memRegion r 24 =
      (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (r ↦₆₄ w0) ∗ ((r + 8#64) ↦₆₄ w1) ∗ memRegion (r + 16#64) 8) := by
  rw [memRegion_24_split_8_16 r,
    show (16 : Nat) = 8 + 8 by rfl,
    ProofLib.memRegion_split (r + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

/-! ## Arithmetic & Postcondition Helpers -/

private theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_ne_1569 {n : Nat} (hne : n ≠ 1569) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 1569#64 := by
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 1569 at ht
  omega

private theorem byte_zext32_ne8 {t : BitVec 8} (ht : t ≠ 0x08#8) :
    t.zeroExtend 32 ≠ 8#32 := by
  intro h
  apply ht
  apply BitVec.eq_of_toNat_eq
  have hlt : t.toNat < 256 := t.isLt
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : t.toNat < 2 ^ 32)] at hn
  exact hn

private theorem byte_zext64_ne8 {t : BitVec 8} (ht : t ≠ 0x08#8) :
    t.zeroExtend 64 ≠ 8#64 := by
  intro h
  apply ht
  apply BitVec.eq_of_toNat_eq
  have hlt : t.toNat < 256 := t.isLt
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : t.toNat < 2 ^ 64)] at hn
  exact hn

private theorem ok_post_entails (A : RustAlloc) (r buf : BitVec 64) (key : List (BitVec 8))
    (hlen : key.length = kemPkLen) (hbuf : buf ≠ 0#64) :
    (r ↦₆₄ 0xfffffffffffffffe#64) ∗ ((r + 8#64) ↦₆₄ buf) ∗ ((r + 16#64) ↦₆₄ 1568#64) ∗
      A.live buf 1568 1 ∗ (buf ↦ₛ key) ⊢
      kemDeserResAt A r (.ok key) := by
  have hne : key ≠ [] := by
    intro h; rw [h] at hlen; simp [kemPkLen] at hlen
  unfold kemDeserResAt
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right buf ?_
  unfold boxU8At
  have hoff : (r + 8#64 + asm64% boxSliceLenOff) = r + 16#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hpure : (buf ≠ 0 ∧ 1568 < 2 ^ 63) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hbuf, by decide⟩⟩
  rw [hoff, hlen]
  dsimp only [kemPkLen]
  simp only [hne, ↓reduceIte, hpure, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

private theorem sepExists_mono_bv64 {P Q : BitVec 64 → SepProp}
    (h : ∀ v, P v ⊢ Q v) : (∃∗ v, P v) ⊢ (∃∗ v, Q v) :=
  Entails.sepExists_mono h

private theorem sepWPp_ok_ret {prog : Program} {s s0 : State} {P R : SepProp}
    {Tail : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {Qp : State → SepProp → Prop} {A : RustAlloc} {r : BitVec 64} (buf : BitVec 64)
    {key : List (BitVec 8)} (hlen : key.length = kemPkLen) (hbuf : buf ≠ 0#64)
    (h : SepWP prog (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ∃∗ x0, ∃∗ x1, ∃∗ x2, ∃∗ x3, ∃∗ x4, ∃∗ x5,
            ⌜sf.trace = s0.trace⌝ ∗
              ((r ↦₆₄ 0xfffffffffffffffe#64) ∗ ((r + 8#64) ↦₆₄ buf) ∗
                ((r + 16#64) ↦₆₄ 1568#64) ∗ A.live buf 1568 1 ∗ (buf ↦ₛ key)) ∗
              Tail x0 x1 x2 x3 x4 x5)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWPp prog (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ∃∗ x0, ∃∗ x1, ∃∗ x2, ∃∗ x3, ∃∗ x4, ∃∗ x5,
            ⌜sf.trace = s0.trace⌝ ∗
              kemDeserResAt A r (.ok key) ∗
              Tail x0 x1 x2 x3 x4 x5)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  have h1 := SepWPp.of_sepWP_ret (Qp := Qp) h
  intro R' hm hL
  rcases h1 R' hm hL with ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq, hsp, hcs⟩ | hpan | hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, ?_, hsp, hcs⟩⟩
    intro hm_pf
    refine Satisfies.mono ?_ (hq hm_pf)
    exact sepExists_mono_bv64 fun x0 => sepExists_mono_bv64 fun x1 =>
      sepExists_mono_bv64 fun x2 => sepExists_mono_bv64 fun x3 =>
        sepExists_mono_bv64 fun x4 => sepExists_mono_bv64 fun x5 =>
          sepConj_mono_right (sepConj_mono_left (ok_post_entails A r buf key hlen hbuf))
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## Callee Specs (`key_length` and `memcpy` over `bytesAt`) -/

def kemKeyLengthSpec : Spec Unit where
  pre := fun () _ => emp
  post := fun () s0 sf => ⌜sf.readReg64 .x0 = 1568#64 ∧ sf.trace = s0.trace⌝

private theorem kemKeyLength_ok {img : Obj.Image}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kemKeyLengthName)
      (kemKeyLengthSpec.inImage img) := by
  apply SpqrV1.Alloc.subroutine_ok_inImage img
  have hfn : libsignalSessionCode.fnOff kemKeyLengthName =
      ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length" :=
    kemKeyLength_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode kemDeserBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length")) 0 8
  dsimp only [tripleRatchetProgAtExt]
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr kemKeyLengthName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init u s0
  cases u
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

private theorem kemKeyLength_ok_at {img : Obj.Image}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliKemDeserializeName +
        bv% (2 ^ 64 +
          (ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length") -
          (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize")))
      (kemKeyLengthSpec.inImage img) := by
  rw [Wire.fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize")
    (ls_lemma% fnOff "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length")
    (by decide)]
  exact kemKeyLength_ok

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
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliKemDeserializeName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
            "memcpy"))
      ((cliMemcpyBytesAtSpecX ro).inImage img) := by
  cases ro
  · have hmc := memcpy_ok_at2_ext_x hA (name := cliKemDeserializeName)
      (k := ls_rel% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
        "memcpy")
      (by rw [cliKemDeserialize_fnOff, (ls_stub% "memcpy")])
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
  · have hmc_ro := SpqrV1.Alloc.session_memcpy_region_ro_ok_at (b := img.base) hRO
      cliKemDeserializeName
      (ls_rel% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
        "memcpy")
      (by rw [cliKemDeserialize_fnOff, (ls_stub% "memcpy")])
    apply SpqrV1.Alloc.subroutine_ok_inImage img
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ SpqrV1.Alloc.sessionMemcpyRegionROSpec.pre (dst, src, bs) s0 ∗
        (stackAt s0.sp extHookStack ∗ R) := by
      simp only [cliMemcpyBytesAtSpecX, SpqrV1.Alloc.sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc] at hpre ⊢
      exact hpre
    refine hmc_ro.mono_outcome (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal fun sf hout => ?_
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

private def cliMemcpy1568SpecX (ro : Bool) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     s0.readReg64 .x2 = 1568#64 ∧
     bs.length = 1568⌝ ∗
    memRegion dst 1568 ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    SpqrV1.ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp extHookStack

private theorem cliMemcpy1568_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliKemDeserializeName +
        BitVec.ofNat 64
          (ls_rel% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
            "memcpy"))
      ((cliMemcpy1568SpecX ro).inImage img) := by
  have hmc := cliMemcpy_bytesAt_ok_at hA hRO ro
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((cliMemcpyBytesAtSpecX ro).inImage img).pre (dst, src, bs) s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hpre
    simp only [Spec.inImage, cliMemcpy1568SpecX, cliMemcpyBytesAtSpecX]
    refine sepConj_mono_right ?_
    apply Entails.pure_left
    rintro ⟨hx0, hx1, hx2, hlen⟩
    rw [hx2, hlen]
    exact Entails.pure_right ⟨hx0, hx1, rfl, by decide⟩ (Entails.refl _)
  refine hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [Spec.inImage, cliMemcpy1568SpecX, cliMemcpyBytesAtSpecX, sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ## Exact-Stack Main Proof -/

set_option maxHeartbeats 1600000 in
theorem cliKemDeserialize_exact_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliKemDeserializeName)
      ((cliKemDeserializeSpec A cliKemDeserStack).inImage img) := by
  unfold Spec.inImage cliKemDeserializeSpec
  simp only [stackAt_kemDeser, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff cliKemDeserializeName =
      ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize" :=
    cliKemDeserialize_fnOff
  have hkeylen := kemKeyLength_ok_at (img := img) (ext := ext)
  have hshim := shim_ok_at2_ext_x hA (name := cliKemDeserializeName)
    (k := ls_rel% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_ext_x hA (name := cliKemDeserializeName)
    (k := ls_rel% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
      "__rustc::__rust_alloc")
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hmc_any := cliMemcpy1568_ok_at hA hRO
  clear hRO
  have hpanic : (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliKemDeserializeName +
        bv% (ls_rel% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
          "alloc::alloc::handle_alloc_error")) = some Rust.panicked :=
    panic_at_handle_alloc_error_ext img.base ext cliKemDeserializeName
      (ls_rel% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
        "alloc::alloc::handle_alloc_error")
      (by rw [hfn, (ls_stub% "alloc::alloc::handle_alloc_error")])
  code_fetches_range CryptoVerification.libsignalSessionCode kemDeserBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"))
    0 252
  dsimp only [tripleRatchetProgAtExt] at hkeylen hshim halloc hmc_any hpanic ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr cliKemDeserializeName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨r, ro, p, bs⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨‹_›, ‹_›⟩
  cases bs with
  | nil =>
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, kemPkDeserialize, kemDeserResAt,
      memRegion_24_split_8_16 r, sepExists_sepConj_left, sepConj_assoc] at *
    refine SepWPp.exists_elim fun w0 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  | cons t rest =>
    have hlen_lt63 : (t :: rest).length < 2 ^ 63 := ‹_›
    have hlen_lt64 : rest.length + 1 < 2 ^ 64 := by simp at hlen_lt63; omega
    have hne0 : (BitVec.ofNat 64 (rest.length + 1) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) hlen_lt64
    by_cases ht : t = 0x08#8
    · subst ht
      simp only [kemPkDeserialize, ne_eq, not_true_eq_false, ↓reduceIte]
      by_cases hrlen : rest.length = kemPkLen
      · -- Valid 1569-byte Kyber1024 public key (`0x08 :: rest`, `rest.length = 1568`)
        have hrlen_keep : rest.length = kemPkLen := hrlen
        have hrlen1568 : rest.length = 1568 := hrlen
        have hx2_eq : BitVec.ofNat 64 (rest.length + 1) = 1569#64 := by rw [hrlen1568]
        rw [List.length_cons] at *
        try rw [hx2_eq] at *
        simp only [hrlen, not_true_eq_false, ↓reduceIte,
          memRegion_24_cells r, sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
          SepWPp.exists_elim fun w2 => ?_
        have hlay : LayoutOk 1568 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
        have hpow : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
        have hmcall := hmc_any ro
        cases ro
        · simp only [SpqrV1.ChainProofs.bytesAt_false, ProofLib.pointsToBytes_cons,
            sepConj_assoc] at hmcall ⊢
          apply SepWPp.of_sepWP_inImage (mid := entry + bv% (92)) hinv0
          apply SepWP.seq_inImage
            (mid := entry + bv% (ls_rel%
              "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
              "__rustc::__rust_alloc")) hinv0
          apply SepWP.seq_inImage
            (mid := entry + bv% (ls_rel%
              "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
              "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
          apply SepWP.seq_inImage
            (mid := entry + bv% (2 ^ 64 +
              (ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length") -
              (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"))) hinv0
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨_, _⟩
          wp_apply
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨_, _⟩
          wp_apply
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨_, _⟩
          wp_apply
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hinv_sf2
          by_cases hoom : sf_2.readReg64 Reg.x0 = 0
          · have hoom64 : sf_2.readReg64 Reg.x0 = 0#64 := hoom
            simp only [hoom, ite_true]
            rw [pull_alloc_pure]
            refine SepWPp.pure_elim fun htrace => ?_
            apply SepWPp.of_sepWP
              (mid := entry + bv% (ls_rel%
                "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
                "alloc::alloc::handle_alloc_error"))
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) hpanic fun hm => ?_
            simpa only [sepConj_assoc] using
              allowPanic_panicked
                (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
          · simp only [hoom, ite_false, sepConj_assoc]
            have hoom_beq : (sf_2.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
            rw [pull_alloc_pure]
            refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
            have htr_sf2 : sf_2.trace = s0.trace := by
              rw [htr2]; simp only [wp_norm, arm64_norm, *]
            apply sepWPp_ok_ret (sf_2.readReg64 Reg.x0) hrlen_keep hoom
            apply SepWP.seq_inImage
              (mid := entry + bv% (ls_rel%
                "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
                "memcpy")) hinv_sf2
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            rintro ⟨_, _⟩
            wp_apply using hmcall
            wp_steps
            wp_done
        · simp only [SpqrV1.ChainProofs.bytesAt_true, ProofLib.pointsToBytesRO_cons,
            sepConj_assoc] at hmcall ⊢
          apply SepWPp.of_sepWP_inImage (mid := entry + bv% (92)) hinv0
          apply SepWP.seq_inImage
            (mid := entry + bv% (ls_rel%
              "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
              "__rustc::__rust_alloc")) hinv0
          apply SepWP.seq_inImage
            (mid := entry + bv% (ls_rel%
              "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
              "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
          apply SepWP.seq_inImage
            (mid := entry + bv% (2 ^ 64 +
              (ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length") -
              (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"))) hinv0
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨_, _⟩
          wp_apply
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨_, _⟩
          wp_apply
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨_, _⟩
          wp_apply
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hinv_sf2
          by_cases hoom : sf_2.readReg64 Reg.x0 = 0
          · have hoom64 : sf_2.readReg64 Reg.x0 = 0#64 := hoom
            simp only [hoom, ite_true]
            rw [pull_alloc_pure]
            refine SepWPp.pure_elim fun htrace => ?_
            apply SepWPp.of_sepWP
              (mid := entry + bv% (ls_rel%
                "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
                "alloc::alloc::handle_alloc_error"))
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) hpanic fun hm => ?_
            simpa only [sepConj_assoc] using
              allowPanic_panicked
                (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
          · simp only [hoom, ite_false, sepConj_assoc]
            have hoom_beq : (sf_2.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
            rw [pull_alloc_pure]
            refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
            have htr_sf2 : sf_2.trace = s0.trace := by
              rw [htr2]; simp only [wp_norm, arm64_norm, *]
            apply sepWPp_ok_ret (sf_2.readReg64 Reg.x0) hrlen_keep hoom
            apply SepWP.seq_inImage
              (mid := entry + bv% (ls_rel%
                "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"
                "memcpy")) hinv_sf2
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            rintro ⟨_, _⟩
            wp_apply using hmcall
            wp_steps
            wp_done
      · -- Wrong key length (`0x08 :: rest`, `rest.length ≠ 1568`)
        have hne1569 : BitVec.ofNat 64 (rest.length + 1) ≠ 1569#64 :=
          ofNat_ne_1569 (by simp [kemPkLen] at hrlen; omega) hlen_lt64
        have hbeq1569 : (BitVec.ofNat 64 (rest.length + 1) == 1569#64) = false :=
          beq_false_of_ne hne1569
        rw [List.length_cons] at *
        simp only [hrlen, not_false_eq_true, ↓reduceIte, kemDeserResAt,
          memRegion_24_split_badLen r, sepExists_sepConj_left, sepConj_assoc]
        refine SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w0 => ?_
        apply SepWPp.of_sepWP_ret
        cases ro
        · simp only [SpqrV1.ChainProofs.bytesAt_false, ProofLib.pointsToBytes_cons, sepConj_assoc]
          apply SepWP.seq_inImage
            (mid := entry + bv% (2 ^ 64 +
              (ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length") -
              (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"))) hinv0
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨_, _⟩
          wp_apply
          wp_steps
          wp_done
        · simp only [SpqrV1.ChainProofs.bytesAt_true, ProofLib.pointsToBytesRO_cons, sepConj_assoc]
          apply SepWP.seq_inImage
            (mid := entry + bv% (2 ^ 64 +
              (ls_off% "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length") -
              (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"))) hinv0
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          rintro ⟨_, _⟩
          wp_apply
          wp_steps
          wp_done
    · -- Wrong key type byte (`t ≠ 0x08#8`)
      have hne32 := byte_zext32_ne8 ht
      have hne64 := byte_zext64_ne8 ht
      have hsub32 : t.zeroExtend 32 - 8#32 ≠ 0#32 := by bv_omega
      have hsub64 : t.zeroExtend 64 - 8#64 ≠ 0#64 := by bv_omega
      have hbeq_sub32 : (t.zeroExtend 32 - 8#32 == 0#32) = false := beq_false_of_ne hsub32
      have hbeq8_32 : (t.zeroExtend 32 == 8#32) = false := beq_false_of_ne hne32
      have hbeq8_64 : (t.zeroExtend 64 == 8#64) = false := beq_false_of_ne hne64
      rw [List.length_cons] at *
      simp only [kemPkDeserialize, ne_eq, ht, not_false_eq_true, ↓reduceIte,
        kemDeserResAt, memRegion_24_split_badType r, sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun b1 => SepWPp.exists_elim fun w0 => ?_
      apply SepWPp.of_sepWP_ret
      cases ro
      · simp only [SpqrV1.ChainProofs.bytesAt_false, ProofLib.pointsToBytes_cons, sepConj_assoc]
        wp_steps
        wp_done
      · simp only [SpqrV1.ChainProofs.bytesAt_true, ProofLib.pointsToBytesRO_cons, sepConj_assoc]
        wp_steps
        wp_done

end CryptoVerification.SignalSession.Cli.RunProofs.KemDeserializeHelpers
