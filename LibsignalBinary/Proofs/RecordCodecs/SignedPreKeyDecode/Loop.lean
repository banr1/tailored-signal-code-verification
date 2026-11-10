/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkip
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DecodeKey
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.KeyAndScalar
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# `SignedPreKeyRecordStructure::decode` Tag Dispatch, Loop Induction, and Prologue

Verifies tag dispatch (`+144 .. +172`, `+220 .. +232`), loop induction over `fuel` (`+92`), and
prologue unpacking (`+0 .. +72` → `+656`) across all inputs (`[]` and `b0 :: bs1`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
attribute [local arm64_norm] BitVec.toNat_zero

namespace CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Dispatch (`+144..+172`, `+220..+232`), loop induction (`+92` / `+104`), and prologue (`+0..+72`) -/

theorem spk_decodeKey_bounds {bs rest : List (BitVec 8)} {tag : ℕ} {wt : WireType}
    (hdk : decodeKey bs = some ((tag, wt), rest)) :
    (∃ k, 1 ≤ k ∧ k ≤ bs.length ∧ rest = bs.drop k) ∧ 1 ≤ tag ∧ tag < 2 ^ 29 := by
  obtain ⟨k, hk1, hkle, hr, _, hge1⟩ := Wire.decodeKey_suffix hdk
  refine ⟨⟨k, hk1, hkle, hr⟩, hge1, ?_⟩
  unfold decodeKey at hdk
  cases hdv : decodeVarint bs with
  | none => simp [hdv] at hdk
  | some kv =>
    rcases kv with ⟨key, rest'⟩
    simp only [hdv] at hdk
    split at hdk
    · nomatch hdk
    · cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none => rw [hwt] at hdk; nomatch hdk
      | some wt' =>
        rw [hwt] at hdk
        dsimp only at hdk
        split at hdk
        · nomatch hdk
        · injection hdk with hdk
          injection hdk with hdk _
          injection hdk with htag_eq _
          omega

private theorem spk_tag_ge6_conds (tag : ℕ) (hge : 6 ≤ tag) (hlt29 : tag < 2 ^ 29) :
    let w := (BitVec.ofNat 64 tag).setWidth 32
    (BitVec.sle w 2#32 = false) ∧
    (BitVec.slt 2#32 w = true) ∧
    (BitVec.slt w 2#32 = false) ∧
    ((w == 3#32) = false) ∧ ((w != 3#32) = true) ∧
    ((w == 4#32) = false) ∧ ((w != 4#32) = true) ∧
    ((w == 5#32) = false) ∧ ((w != 5#32) = true) ∧
    ((w - 2#32 == 0#32) = false) ∧ ((w - 2#32 != 0#32) = true) ∧
    ((w - 3#32 == 0#32) = false) ∧ ((w - 3#32 != 0#32) = true) ∧
    ((w - 4#32 == 0#32) = false) ∧ ((w - 4#32 != 0#32) = true) ∧
    ((w - 5#32 == 0#32) = false) ∧ ((w - 5#32 != 0#32) = true) := by
  dsimp only
  have hmod : tag % 2 ^ 32 = tag := Nat.mod_eq_of_lt (by omega)
  have hw : (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (by omega : tag < 2 ^ 64), hmod]
  rw [hw]
  have hn3 : BitVec.ofNat 32 tag ≠ 3#32 := by bv_omega
  have hn4 : BitVec.ofNat 32 tag ≠ 4#32 := by bv_omega
  have hn5 : BitVec.ofNat 32 tag ≠ 5#32 := by bv_omega
  have hs2 : BitVec.ofNat 32 tag - 2#32 ≠ 0#32 := by bv_omega
  have hs3 : BitVec.ofNat 32 tag - 3#32 ≠ 0#32 := by bv_omega
  have hs4 : BitVec.ofNat 32 tag - 4#32 ≠ 0#32 := by bv_omega
  have hs5 : BitVec.ofNat 32 tag - 5#32 ≠ 0#32 := by bv_omega
  have htn : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, hmod]
  have hti : (BitVec.ofNat 32 tag).toInt = (tag : Int) := by
    unfold BitVec.toInt
    rw [htn]
    split <;> omega
  have hti2 : (2#32).toInt = (2 : Int) := rfl
  have hsle : BitVec.sle (BitVec.ofNat 32 tag) 2#32 = false := by
    unfold BitVec.sle; rw [hti, hti2]; exact decide_eq_false (by omega)
  have hslt1 : BitVec.slt 2#32 (BitVec.ofNat 32 tag) = true := by
    unfold BitVec.slt; rw [hti, hti2]; exact decide_eq_true (by omega)
  have hslt2 : BitVec.slt (BitVec.ofNat 32 tag) 2#32 = false := by
    unfold BitVec.slt; rw [hti, hti2]; exact decide_eq_false (by omega)
  refine ⟨hsle, hslt1, hslt2,
    beq_eq_false_iff_ne.mpr hn3, bne_iff_ne.mpr hn3,
    beq_eq_false_iff_ne.mpr hn4, bne_iff_ne.mpr hn4,
    beq_eq_false_iff_ne.mpr hn5, bne_iff_ne.mpr hn5,
    beq_eq_false_iff_ne.mpr hs2, bne_iff_ne.mpr hs2,
    beq_eq_false_iff_ne.mpr hs3, bne_iff_ne.mpr hs3,
    beq_eq_false_iff_ne.mpr hs4, bne_iff_ne.mpr hs4,
    beq_eq_false_iff_ne.mpr hs5, bne_iff_ne.mpr hs5⟩

/-- Dispatch CPS (`+144..+172`, `+220..+232`) routing tags `1..5` and unknown `tag ≥ 6` (`< 2^29`). -/
theorem dispatch_144_cps {img : Obj.Image}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 : BitVec 64} {tag : ℕ}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_dispatch)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 29)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag1 →
      s1.status = .Running → SpkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s1 P Q Qp)
    (h2 : tag = 2 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag2 →
      s1.status = .Running → SpkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s1 P Q Qp)
    (h3 : tag = 3 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag3 →
      s1.status = .Running → SpkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s1 P Q Qp)
    (h4 : tag = 4 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag4 →
      s1.status = .Running → SpkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s1 P Q Qp)
    (h5 : tag = 5 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag5 →
      s1.status = .Running → SpkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s1 P Q Qp)
    (h6 : 6 ≤ tag → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_skip →
      s1.status = .Running → SpkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s1 P Q Qp) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s P Q Qp := by
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 144 32
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 220 16
  dsimp only [tripleRatchetProgAtExt] at h1 h2 h3 h4 h5 h6 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  rcases tag with _ | _ | _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag1) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h1 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag2) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h2 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag3) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h3 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 4#64 := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag4) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h4 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 5#64 := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h5 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 6) := hx1
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12,
      hc13, hc14, hc15, hc16, hc17⟩ := spk_tag_ge6_conds (n + 6) (by omega) htag_lt
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_skip) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h6 (by omega) _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simpa [arm64_norm] using hx1')
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr

/-- Unified field merge CPS (`+144` → `+92` on `some (m', rest2)`, `+656` on `none`). -/
theorem mergeField_144_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {tag : ℕ} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (hlen : bs.length < 2 ^ 63)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 29)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_dispatch)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlatch : ∀ (m' : SignedPreKeyRecordStructure) (rest2 : List (BitVec 8)) (s3 : State),
      SignedPreKeyRecordStructure.mergeField m tag wt rest = some (m', rest2) →
      s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_latch →
      s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s3
        (spkLoopMemAt cfg.subStack A sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 m')
        (spkConvergePostAt cfg.subStack img A s0 sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 out)
        (tryFromQp s0))
    (hnone : SignedPreKeyRecordStructure.mergeField m tag wt rest = none → out = none) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (spkAfterVarintMemAt cfg.subStack A sp' x19 ptr bs rest bs.length m)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  refine dispatch_144_cps hpc hrun hregs hx1 htag_ge htag_lt hsp hF hsym htr
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hF1 hsym1 htr1 => ?_)
  · subst htag
    exact tag1_276_wp B hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1
      (fun v rest2 s3 hm => hlatch { m with id := v } rest2 s3
        (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact bytesField_merge_wp B .pub hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1
      (fun v rest2 s3 hm => hlatch { m with publicKey := v } rest2 s3
        (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact bytesField_merge_wp B .priv hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1
      (fun v rest2 s3 hm => hlatch { m with privateKey := v } rest2 s3
        (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact bytesField_merge_wp B .sig hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1
      (fun v rest2 s3 hm => hlatch { m with signature := v } rest2 s3
        (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact tag5_176_wp B hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1
      (fun v rest2 s3 hm => hlatch { m with timestamp := v } rest2 s3
        (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact skip_300_wp B hsuf hlen (by omega) hpc1 hrun1 hregs1 (hx0_1.trans hx0) hx1_1
      hsp1 hF1 hsym1 htr1
      (fun rest2 s3 hsu => hlatch m rest2 s3
        (by simpa [SignedPreKeyRecordStructure.mergeField] using hsu))
      (fun hsu => hnone (by simpa [SignedPreKeyRecordStructure.mergeField] using hsu))

/-! ## Loop latch (`+92..+100`) and loop induction over `fuel` -/

theorem latch_92_empty_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {m : SignedPreKeyRecordStructure} {out : Option SignedPreKeyRecordStructure}
    (hok : out = some m)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_latch)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (spkLoopMemAt cfg.subStack A sp' x19 ptr [] m)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr [] out)
      (tryFromQp s0) := by
  have hexit := @okEmpty_392_wp cfg img A ext s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 92 12
  dsimp only [tripleRatchetProgAtExt] at hexit hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  unfold spkLoopMemAt sliceCursorAt
  simp only [sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_okEmpty) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hexit (sp' := sp') (x19 := x19) (ptr := ptr) (m := m) (bs := []) (out := out) hok
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simp [htr, arm64_norm]))
  have h16 := Wire.pointsTo64_pair_entails_memRegion16 sp' ptr (BitVec.ofNat 64 ([] : List (BitVec 8)).length)
  have hof := spkStructLoopOf_entails_of A sp' ([] : List (BitVec 8)).length m
  rw [← sepConj_assoc (sp' ↦₆₄ ptr) ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length)]
  refine Entails.trans
    (sepConj_mono h16
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hof))))) ?_
  apply entails_of_eq; ac_rfl

theorem latch_92_cons_cps {img : Obj.Image}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_latch)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_key →
      s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s1
        (sliceCursorAt sp' ptr (b0 :: bs1) ∗ ((sp' + 104#64) ↦₆₄ sp') ∗ F) Q Qp) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (sliceCursorAt sp' ptr (b0 :: bs1) ∗ ((sp' + 104#64) ↦₆₄ sp') ∗ F) Q Qp := by
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 92 12
  dsimp only [tripleRatchetProgAtExt] at hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
  have hc_eq' : (BitVec.ofNat 64 (bs1.length + 1) == 0#64) = false := by
    simpa only [List.length_cons] using hc_eq
  have hc_ne' : (BitVec.ofNat 64 (bs1.length + 1) != 0#64) = true := by
    simpa only [List.length_cons] using hc_ne
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_key) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hcont _
      (by simp [arm64_norm])
      (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simp [htr, arm64_norm]))
  unfold sliceCursorAt
  apply entails_of_eq; ac_rfl

theorem decodeIter_104_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : SignedPreKeyRecordStructure}
    (ih : ∀ {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : SignedPreKeyRecordStructure},
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_latch →
      s.status = .Running →
      SpkLoopRegs s0 sp' x19 s →
      s.spAligned = true → img.FrozenLoaded s → s.symtab = img.symtab →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
        (spkLoopMemAt cfg.subStack A sp' x19 ptr bs m)
        (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs
          (decodeFieldsLoop SignedPreKeyRecordStructure.mergeField fuel m bs))
        (tryFromQp s0))
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_key)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1)
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (spkLoopMemAt cfg.subStack A sp' x19 ptr (b0 :: bs1) m)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr (b0 :: bs1)
        (decodeFieldsLoop SignedPreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1)))
      (tryFromQp s0) := by
  refine decodeKey_104_cps B hlen hpc hrun hregs hsp hF hsym htr
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun hdk_none => by simp [decodeFieldsLoop, hdk_none])
  obtain ⟨⟨k1, hk1_pos, hk1_le, hrest1_eq⟩, htag_ge, htag_lt⟩ := spk_decodeKey_bounds hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  refine mergeField_144_wp B ⟨k1, hk1_le, hrest1_eq⟩ hlen htag_ge htag_lt
    hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hF1 hsym1 htr1
    (fun m' rest2 s2 hmf hpc2 hrun2 hregs2 hsp2 hF2 hsym2 htr2 => ?_)
    (fun hmf_none => by simp [decodeFieldsLoop, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := spkMergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  have hloop_eq : decodeFieldsLoop SignedPreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1) =
      decodeFieldsLoop SignedPreKeyRecordStructure.mergeField fuel m' rest2 := by
    simp [decodeFieldsLoop, hdk, hmf]
  rw [hloop_eq]
  exact ih hpc2 hrun2 hregs2 hsp2 hF2 hsym2 htr2 (by omega) (by omega)

theorem decodeLoop_92_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 : State} {sp' x19 : BitVec 64} :
    ∀ (fuel : ℕ) {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)}
        {m : SignedPreKeyRecordStructure},
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_latch →
      s.status = .Running →
      SpkLoopRegs s0 sp' x19 s →
      s.spAligned = true → img.FrozenLoaded s → s.symtab = img.symtab →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
        (spkLoopMemAt cfg.subStack A sp' x19 ptr bs m)
        (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs
          (decodeFieldsLoop SignedPreKeyRecordStructure.mergeField fuel m bs))
        (tryFromQp s0)
  | 0, s, ptr, bs, m, hpc, hrun, hregs, hsp, hF, hsym, htr, hfuel, _ => by
    cases bs with
    | nil => exact latch_92_empty_wp rfl hpc hrun hregs hsp hF hsym htr
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, s, ptr, bs, m, hpc, hrun, hregs, hsp, hF, hsym, htr, hfuel, hlen => by
    cases bs with
    | nil => exact latch_92_empty_wp rfl hpc hrun hregs hsp hF hsym htr
    | cons b0 bs1 =>
      unfold spkLoopMemAt
      refine latch_92_cons_cps hpc hrun hregs hsp hF hsym htr hlen ?_
      intro s1 hpc1 hrun1 hregs1 hsp1 hF1 hsym1 htr1
      exact decodeIter_104_wp B (decodeLoop_92_wp B fuel)
        hpc1 hrun1 hregs1 hsp1 hF1 hsym1 htr1 hfuel hlen

/-! ## Prologue memory unpacking (`+0..+72` → `+104` → `+656`) -/

private theorem spkMemRegion64_unpack (a : BitVec 64) :
    memRegion a 64 ⊢
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
        (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗ ((a + 24#64) ↦₆₄ c3) ∗
        ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗ ((a + 48#64) ↦₆₄ c6) ∗ ((a + 56#64) ↦₆₄ c7) := by
  rw [ProofLib.memRegion_split a 8 56 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 48 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun c7 => Entails.sepExists_elim fun c6 =>
    Entails.sepExists_elim fun c5 => Entails.sepExists_elim fun c4 =>
    Entails.sepExists_elim fun c3 => Entails.sepExists_elim fun c2 =>
    Entails.sepExists_elim fun c1 => Entails.sepExists_elim fun c0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro c0)
  refine Entails.trans ?_ (Entails.sepExists_intro c1)
  refine Entails.trans ?_ (Entails.sepExists_intro c2)
  refine Entails.trans ?_ (Entails.sepExists_intro c3)
  refine Entails.trans ?_ (Entails.sepExists_intro c4)
  refine Entails.trans ?_ (Entails.sepExists_intro c5)
  refine Entails.trans ?_ (Entails.sepExists_intro c6)
  refine Entails.trans ?_ (Entails.sepExists_intro c7)
  exact Entails.refl _

private theorem spkStruct88_unpack_init (a : BitVec 64) :
    memRegion a 88 ⊢
      ∃∗ s0w : BitVec 64, ∃∗ s1w : BitVec 64, ∃∗ s2w : BitVec 64,
      ∃∗ s3w : BitVec 64, ∃∗ s4w : BitVec 64, ∃∗ s5w : BitVec 64,
      ∃∗ s6w : BitVec 64, ∃∗ s7w : BitVec 64, ∃∗ s8w : BitVec 64,
      ∃∗ s9w : BitVec 64, ∃∗ s10w : BitVec 32,
        (a ↦₆₄ s0w) ∗ ((a + 8#64) ↦₆₄ s1w) ∗ ((a + 16#64) ↦₆₄ s2w) ∗
        ((a + 24#64) ↦₆₄ s3w) ∗ ((a + 32#64) ↦₆₄ s4w) ∗ ((a + 40#64) ↦₆₄ s5w) ∗
        ((a + 48#64) ↦₆₄ s6w) ∗ ((a + 56#64) ↦₆₄ s7w) ∗ ((a + 64#64) ↦₆₄ s8w) ∗
        ((a + 72#64) ↦₆₄ s9w) ∗ ((a + 80#64) ↦₃₂ s10w) ∗ memRegion (a + 84#64) 4 := by
  rw [ProofLib.memRegion_split a 8 80 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 72 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 64 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 56 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 4 4 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun s10w => Entails.sepExists_elim fun s9w =>
    Entails.sepExists_elim fun s8w => Entails.sepExists_elim fun s7w =>
    Entails.sepExists_elim fun s6w => Entails.sepExists_elim fun s5w =>
    Entails.sepExists_elim fun s4w => Entails.sepExists_elim fun s3w =>
    Entails.sepExists_elim fun s2w => Entails.sepExists_elim fun s1w =>
    Entails.sepExists_elim fun s0w => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro s0w)
  refine Entails.trans ?_ (Entails.sepExists_intro s1w)
  refine Entails.trans ?_ (Entails.sepExists_intro s2w)
  refine Entails.trans ?_ (Entails.sepExists_intro s3w)
  refine Entails.trans ?_ (Entails.sepExists_intro s4w)
  refine Entails.trans ?_ (Entails.sepExists_intro s5w)
  refine Entails.trans ?_ (Entails.sepExists_intro s6w)
  refine Entails.trans ?_ (Entails.sepExists_intro s7w)
  refine Entails.trans ?_ (Entails.sepExists_intro s8w)
  refine Entails.trans ?_ (Entails.sepExists_intro s9w)
  refine Entails.trans ?_ (Entails.sepExists_intro s10w)
  exact Entails.refl _

private theorem spkEmptyHeaders_entails_loopOf (A : RustAlloc) (sp' : BitVec 64) (n : ℕ) :
    ((sp' + 16#64) ↦₆₄ 0#64) ∗ ((sp' + 24#64) ↦₆₄ 1#64) ∗ ((sp' + 32#64) ↦₆₄ 0#64) ∗
      ((sp' + 40#64) ↦₆₄ 0#64) ∗ ((sp' + 48#64) ↦₆₄ 1#64) ∗ ((sp' + 56#64) ↦₆₄ 0#64) ∗
      ((sp' + 64#64) ↦₆₄ 0#64) ∗ ((sp' + 72#64) ↦₆₄ 1#64) ∗ ((sp' + 80#64) ↦₆₄ 0#64) ∗
      ((sp' + 88#64) ↦₆₄ 0#64) ∗ ((sp' + 96#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 100#64) 4 ⊢
      spkStructLoopOf A sp' n SignedPreKeyRecordStructure.empty := by
  have hz3 := spk_emp_entails_three_vecU8Buf_zero A
  refine Entails.trans ?_
    (spkStructAt_entails_loopOf A ⟨⟨0#64, 1#64⟩, ⟨0#64, 1#64⟩, ⟨0#64, 1#64⟩⟩ sp' n
      SignedPreKeyRecordStructure.empty
      ⟨Or.inl (by decide), Or.inl (by decide), Or.inl (by decide)⟩)
  unfold spkStructAt
  dsimp only [SignedPreKeyRecordStructure.empty]
  rw [vecU8At_eq_header_buf A (sp' + 16#64) 0#64 1#64 [],
    vecU8At_eq_header_buf A (sp' + 40#64) 0#64 1#64 [],
    vecU8At_eq_header_buf A (sp' + 64#64) 0#64 1#64 []]
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [← emp_sepConj (((sp' + 16#64) ↦₆₄ 0#64) ∗ ((sp' + 24#64) ↦₆₄ 1#64) ∗
    ((sp' + 32#64) ↦₆₄ 0#64) ∗ ((sp' + 40#64) ↦₆₄ 0#64) ∗ ((sp' + 48#64) ↦₆₄ 1#64) ∗
    ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ 0#64) ∗ ((sp' + 72#64) ↦₆₄ 1#64) ∗
    ((sp' + 80#64) ↦₆₄ 0#64) ∗ ((sp' + 88#64) ↦₆₄ 0#64) ∗ ((sp' + 96#64) ↦₃₂ 0#32) ∗
    memRegion (sp' + 100#64) 4)]
  refine Entails.trans (sepConj_mono_left hz3) ?_
  apply entails_of_eq; ac_rfl

/-- Full prologue + decode loop (`+0..+656`) for ALL `x.bytes` (`[]` and `b0 :: bs1`), producing
`spkActualDecode x.bytes` at `+656` (`spkOff_converge`). -/
theorem prologue_0_to_converge_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {x : DecodeGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.ret)
    (hx1 : s0.readReg64 .x1 = x.bytesA)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s0.sp (224 + cfg.subStack) ∗ A.pool)
      (fun sm Pm =>
        SpkConvergeState img s0 (s0.sp - 224#64) x.ret sm ∧
        (Pm ⊢ spkConvergeMemAt cfg.subStack A (s0.sp - 224#64) x.ret x.bytesA x.bytes
            (spkActualDecode x.bytes) (sm.readReg64 .x1) ∗
          spkCalleeSavedAt (s0.sp - 224#64) s0))
      (tryFromQp s0) := by
  set sp' := s0.sp - 224#64
  have hstk := spkStack_split cfg s0.sp
  have h160 : memRegion sp' 160 =
      memRegion sp' 16 ∗ memRegion (sp' + 16#64) 88 ∗
      memRegion (sp' + 104#64) 8 ∗ memRegion (sp' + 112#64) 48 := by
    rw [show (160 : Nat) = 16 + (88 + (8 + 48)) by decide,
      ProofLib.memRegion_split sp' 16 144 (by decide),
      ProofLib.memRegion_split (sp' + 16#64) 88 56 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 88#64) 8 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h16 : memRegion sp' 16 =
      (∃∗ u0 : BitVec 64, sp' ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (sp' + 8#64) ↦₆₄ u1) := by
    rw [ProofLib.memRegion_split sp' 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  refine Wire.SepWPp.mono_pre
    (P' := memRegion (sp' + 160#64) 64 ∗
      memRegion (sp' + 16#64) 88 ∗
      memRegion sp' 16 ∗
      memRegion (sp' + 104#64) 8 ∗
      (memRegion (sp' + 112#64) 48 ∗
        memRegion x.ret 88 ∗ (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗
        stackAt sp' cfg.subStack))
    (by
      rw [hstk]
      dsimp only [sp'] at h160 ⊢
      rw [h160]
      apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (spkMemRegion64_unpack (sp' + 160#64))
      (sepConj_mono (spkStruct88_unpack_init (sp' + 16#64)) (Entails.refl _))) ?_
  rw [h16, ProofLib.memRegion_eight (sp' + 104#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun u104 =>
    Wire.SepWPp.exists_pre fun u1 => Wire.SepWPp.exists_pre fun u0 =>
    Wire.SepWPp.exists_pre fun s10w => Wire.SepWPp.exists_pre fun s9w =>
    Wire.SepWPp.exists_pre fun s8w => Wire.SepWPp.exists_pre fun s7w =>
    Wire.SepWPp.exists_pre fun s6w => Wire.SepWPp.exists_pre fun s5w =>
    Wire.SepWPp.exists_pre fun s4w => Wire.SepWPp.exists_pre fun s3w =>
    Wire.SepWPp.exists_pre fun s2w => Wire.SepWPp.exists_pre fun s1w =>
    Wire.SepWPp.exists_pre fun s0w =>
    Wire.SepWPp.exists_pre fun c7 => Wire.SepWPp.exists_pre fun c6 =>
    Wire.SepWPp.exists_pre fun c5 => Wire.SepWPp.exists_pre fun c4 =>
    Wire.SepWPp.exists_pre fun c3 => Wire.SepWPp.exists_pre fun c2 =>
    Wire.SepWPp.exists_pre fun c1 => Wire.SepWPp.exists_pre fun c0 => ?_
  have hdk0 := @decodeKey_104_cps cfg img A ext B s0
  have hiter := @decodeIter_104_wp cfg img A ext B s0
  have hih := @decodeLoop_92_wp cfg img A ext B s0 sp' x.ret
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 0 76
  dsimp only [tripleRatchetProgAtExt] at hdk0 hiter hih hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  dsimp only [sp']
  have h0 : s0.readReg64 (Reg.gpr 0#5) = x.ret := hx0
  have h1 : s0.readReg64 (Reg.gpr 1#5) = x.bytesA := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 x.bytes.length := hx2
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_key) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  have hoff104 : s0.sp - 224#64 + 160#64 + (-56#64) = s0.sp - 224#64 + 104#64 := by bv_omega
  have hoff104' : s0.sp - 120#64 = s0.sp - 224#64 + 104#64 := by bv_omega
  have hloop0 := spkEmptyHeaders_entails_loopOf A sp' x.bytes.length
  refine Wire.SepWPp.mono_pre
    (P' := spkLoopMemAt cfg.subStack A sp' x.ret x.bytesA x.bytes SignedPreKeyRecordStructure.empty ∗
      spkCalleeSavedAt sp' s0)
    (by
      unfold spkLoopMemAt sliceCursorAt spkCalleeSavedAt
      dsimp only [sp'] at hloop0 ⊢
      simp only [arm64_norm]
      try rw [hoff104]
      try rw [hoff104']
      have hp :
          ((s0.sp - 224#64 + 160#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 224#64 + 168#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 224#64 + 176#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
            ((s0.sp - 224#64 + 184#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
            ((s0.sp - 224#64 + 192#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 224#64 + 200#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 224#64 + 208#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 224#64 + 216#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
            ((s0.sp - 224#64 + 16#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 24#64) ↦₆₄ 1#64) ∗
            ((s0.sp - 224#64 + 32#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 40#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 224#64 + 48#64) ↦₆₄ 1#64) ∗ ((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 224#64 + 64#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 72#64) ↦₆₄ 1#64) ∗
            ((s0.sp - 224#64 + 80#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 88#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 224#64 + 96#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 224#64 + 100#64) 4 ∗
            ((s0.sp - 224#64) ↦₆₄ x.bytesA) ∗
            ((s0.sp - 224#64 + 8#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
            memRegion (s0.sp - 224#64 + 112#64) 48 ∗
            memRegion x.ret 88 ∗ (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗
            stackAt (s0.sp - 224#64) cfg.subStack =
          (((s0.sp - 224#64 + 16#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 24#64) ↦₆₄ 1#64) ∗
              ((s0.sp - 224#64 + 32#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 40#64) ↦₆₄ 0#64) ∗
              ((s0.sp - 224#64 + 48#64) ↦₆₄ 1#64) ∗ ((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64) ∗
              ((s0.sp - 224#64 + 64#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 72#64) ↦₆₄ 1#64) ∗
              ((s0.sp - 224#64 + 80#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 88#64) ↦₆₄ 0#64) ∗
              ((s0.sp - 224#64 + 96#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 224#64 + 100#64) 4) ∗
            (((s0.sp - 224#64) ↦₆₄ x.bytesA) ∗
              ((s0.sp - 224#64 + 8#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
              (x.bytesA ↦ₛ x.bytes)) ∗
            ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
            memRegion (s0.sp - 224#64 + 112#64) 48 ∗
            memRegion x.ret 88 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) cfg.subStack ∗
            (((s0.sp - 224#64 + 160#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
              ((s0.sp - 224#64 + 168#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 224#64 + 176#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
              ((s0.sp - 224#64 + 184#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
              ((s0.sp - 224#64 + 192#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
              ((s0.sp - 224#64 + 200#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 224#64 + 208#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
              ((s0.sp - 224#64 + 216#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) := by
        ac_rfl
      rw [hp]
      refine Entails.trans (sepConj_mono_left hloop0) ?_
      apply entails_of_eq; ac_rfl) ?_
  cases hbs : x.bytes with
  | nil =>
    have hact : spkActualDecode ([] : List (BitVec 8)) = none := rfl
    rw [hact]
    exact Wire.SepWPp.frame_tryFrom
      (hdk0 (sp' := sp') (x19 := x.ret) (ptr := x.bytesA)
        (bs := []) (m := SignedPreKeyRecordStructure.empty) (out := none)
        (by decide)
        (by simp [arm64_norm])
        (by simp [hrun, arm64_norm])
        ⟨by simp [sp', arm64_norm],
         by simp [sp', arm64_norm]; bv_omega,
         by simp [sp', arm64_norm]; bv_omega,
         by simp [arm64_norm],
         ⟨by simp [arm64_norm], by simp [arm64_norm],
          by simp [arm64_norm], by simp [arm64_norm]⟩⟩
        (by simpa [State.spAligned, arm64_norm] using spkSpAligned_sub224 hsp)
        hF1 hsym1
        (by simp [arm64_norm])
        (fun _ _ _ _ hdk => nomatch hdk)
        (fun _ => rfl))
      (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, sepConj_mono_left hentf⟩)
  | cons b0 bs1 =>
    have hlen63 : (b0 :: bs1).length < 2 ^ 63 := by
      simp [hbs, List.length_cons] at hlt ⊢; omega
    have hact : spkActualDecode (b0 :: bs1) =
        decodeFieldsLoop SignedPreKeyRecordStructure.mergeField (bs1.length + 1)
          SignedPreKeyRecordStructure.empty (b0 :: bs1) := rfl
    rw [hact]
    exact Wire.SepWPp.frame_tryFrom
      (hiter (sp' := sp') (x19 := x.ret) (ptr := x.bytesA)
        (fuel := bs1.length) (b0 := b0) (bs1 := bs1) (m := SignedPreKeyRecordStructure.empty)
        (hih bs1.length)
        (by simp [arm64_norm])
        (by simp [hrun, arm64_norm])
        ⟨by simp [sp', arm64_norm],
         by simp [sp', arm64_norm]; bv_omega,
         by simp [sp', arm64_norm]; bv_omega,
         by simp [arm64_norm],
         ⟨by simp [arm64_norm], by simp [arm64_norm],
          by simp [arm64_norm], by simp [arm64_norm]⟩⟩
        (by simpa [State.spAligned, arm64_norm] using spkSpAligned_sub224 hsp)
        hF1 hsym1
        (by simp [arm64_norm])
        (by simp)
        hlen63)
      (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, sepConj_mono_left hentf⟩)

/-! ## Relocatable `[LibsignalPlacement]` Dispatch, Loop, & Prologue Proofs (Block `562`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

attribute [local irreducible] Program.fetch Program.externAt?

theorem dispatch_144_placed_cps [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 : BitVec 64} {tag : ℕ} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_562).base + spkOff_dispatch) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 29) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State, s1.pc = (blkPl_562).base + spkOff_tag1 → s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s1 P Q Qp)
    (h2 : tag = 2 → ∀ s1 : State, s1.pc = (blkPl_562).base + spkOff_tag2 → s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s1 P Q Qp)
    (h3 : tag = 3 → ∀ s1 : State, s1.pc = (blkPl_562).base + spkOff_tag3 → s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s1 P Q Qp)
    (h4 : tag = 4 → ∀ s1 : State, s1.pc = (blkPl_562).base + spkOff_tag4 → s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s1 P Q Qp)
    (h5 : tag = 5 → ∀ s1 : State, s1.pc = (blkPl_562).base + spkOff_tag5 → s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s1 P Q Qp)
    (h6 : 6 ≤ tag → ∀ s1 : State, s1.pc = (blkPl_562).base + spkOff_skip → s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s1 P Q Qp) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s P Q Qp := by
  rcases tag with _ | _ | _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag1) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 =>
      h1 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
        (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm])
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag2) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 =>
      h2 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
        (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm])
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag3) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 =>
      h3 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
        (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm])
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 4#64 := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag4) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 =>
      h4 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
        (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm])
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 5#64 := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag5) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 =>
      h5 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
        (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm])
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 6) := hx1
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17⟩ :=
      spk_tag_ge6_conds (n + 6) (by omega) htag_lt
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_skip) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 =>
      h6 (by omega) _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
        (by simp [arm64_norm]) (by simpa [arm64_norm] using hx1')
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm])

theorem mergeField_144_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {tag : ℕ} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure} (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (hlen : bs.length < 2 ^ 63) (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 29)
    (hpc : s.pc = (blkPl_562).base + spkOff_dispatch) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlatch : ∀ (m' : SignedPreKeyRecordStructure) (rest2 : List (BitVec 8)) (s3 : State),
      SignedPreKeyRecordStructure.mergeField m tag wt rest = some (m', rest2) →
      s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running → SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem → s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkLoopMem A sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) rest2 m')
        (spkConvergePostPlaced A s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) rest2 out)
        (tryFromQp s0))
    (hnone : SignedPreKeyRecordStructure.mergeField m tag wt rest = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  refine dispatch_144_placed_cps hpc hrun hregs hx1 htag_ge htag_lt hsp hcrl htr
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcrl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcrl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcrl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcrl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcrl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hcrl1 htr1 => ?_)
  · subst htag
    exact tag1_276_placed_wp hH d hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcrl1 htr1
      (fun v rest2 s3 hm => hlatch { m with id := v } rest2 s3 (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact bytesField_merge_placed_wp hH d .pub hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcrl1 htr1
      (fun v rest2 s3 hm => hlatch { m with publicKey := v } rest2 s3 (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact bytesField_merge_placed_wp hH d .priv hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcrl1 htr1
      (fun v rest2 s3 hm => hlatch { m with privateKey := v } rest2 s3 (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact bytesField_merge_placed_wp hH d .sig hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcrl1 htr1
      (fun v rest2 s3 hm => hlatch { m with signature := v } rest2 s3 (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact tag5_176_placed_wp hH hsuf hlen hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcrl1 htr1
      (fun v rest2 s3 hm => hlatch { m with timestamp := v } rest2 s3 (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [SignedPreKeyRecordStructure.mergeField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact skip_300_placed_wp d hsuf hlen (by omega) hpc1 hrun1 hregs1 (hx0_1.trans hx0) hx1_1 hsp1 hcrl1 htr1
      (fun rest2 s3 hsu => hlatch m rest2 s3 (by simpa [SignedPreKeyRecordStructure.mergeField] using hsu))
      (fun hsu => hnone (by simpa [SignedPreKeyRecordStructure.mergeField] using hsu))

theorem latch_92_empty_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure} (hok : out = some m)
    (hpc : s.pc = (blkPl_562).base + spkOff_latch) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkLoopMem A sp' x19 ptr [] m) (spkConvergePostPlaced A s0 sp' x19 ptr [] out) (tryFromQp s0) := by
  have hexit := @okEmpty_392_placed_wp _ A H s0
  have hsp_eq : s.sp = sp' := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  unfold spkLoopMem sliceCursorAt; simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_okEmpty) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre ?_
    (hexit (sp' := sp') (x19 := x19) (ptr := ptr) (m := m) (bs := []) (out := out) hok
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]))
  have h16 := Wire.pointsTo64_pair_entails_memRegion16 sp' ptr (BitVec.ofNat 64 ([] : List (BitVec 8)).length)
  have hof := spkStructLoopOf_entails_of A sp' ([] : List (BitVec 8)).length m
  rw [← sepConj_assoc (sp' ↦₆₄ ptr) ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length)]
  refine Entails.trans (sepConj_mono h16 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof))))) ?_
  apply entails_of_eq; ac_rfl

theorem latch_92_cons_placed_cps [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_562).base + spkOff_latch) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State, s1.pc = (blkPl_562).base + spkOff_key → s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s1
        (sliceCursorAt sp' ptr (b0 :: bs1) ∗ ((sp' + 104#64) ↦₆₄ sp') ∗ F) Q Qp) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (sliceCursorAt sp' ptr (b0 :: bs1) ∗ ((sp' + 104#64) ↦₆₄ sp') ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
  have hc_eq' : (BitVec.ofNat 64 (bs1.length + 1) == 0#64) = false := by simpa only [List.length_cons] using hc_eq
  have hc_ne' : (BitVec.ofNat 64 (bs1.length + 1) != 0#64) = true := by simpa only [List.length_cons] using hc_ne
  unfold sliceCursorAt; simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_key) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre ?_
    (hcont _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]))
  unfold sliceCursorAt; apply entails_of_eq; ac_rfl

theorem decodeIter_104_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)}
    {m : SignedPreKeyRecordStructure}
    (ih : ∀ {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : SignedPreKeyRecordStructure},
      s.pc = (blkPl_562).base + spkOff_latch → s.status = .Running → SpkLoopRegs s0 sp' x19 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length < 2 ^ 63 →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s (spkLoopMem A sp' x19 ptr bs m)
        (spkConvergePostPlaced A s0 sp' x19 ptr bs (decodeFieldsLoop SignedPreKeyRecordStructure.mergeField fuel m bs))
        (tryFromQp s0))
    (hpc : s.pc = (blkPl_562).base + spkOff_key) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1) (hlen : (b0 :: bs1).length < 2 ^ 63) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s (spkLoopMem A sp' x19 ptr (b0 :: bs1) m)
      (spkConvergePostPlaced A s0 sp' x19 ptr (b0 :: bs1)
        (decodeFieldsLoop SignedPreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1))) (tryFromQp s0) := by
  refine decodeKey_104_placed_cps hH d hlen hpc hrun hregs hsp hcrl htr
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hcrl1 htr1 => ?_)
    (fun hdk_none => by simp [decodeFieldsLoop, hdk_none])
  obtain ⟨⟨k1, hk1_pos, hk1_le, hrest1_eq⟩, htag_ge, htag_lt⟩ := spk_decodeKey_bounds hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  refine mergeField_144_placed_wp hH d ⟨k1, hk1_le, hrest1_eq⟩ hlen htag_ge htag_lt
    hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hcrl1 htr1
    (fun m' rest2 s2 hmf hpc2 hrun2 hregs2 hsp2 hcrl2 htr2 => ?_)
    (fun hmf_none => by simp [decodeFieldsLoop, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := spkMergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  rw [show decodeFieldsLoop SignedPreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1) =
    decodeFieldsLoop SignedPreKeyRecordStructure.mergeField fuel m' rest2 by simp [decodeFieldsLoop, hdk, hmf]]
  exact ih hpc2 hrun2 hregs2 hsp2 hcrl2 htr2 (by omega) (by omega)

theorem decodeLoop_92_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) {s0 : State} {sp' x19 : BitVec 64} :
    ∀ (fuel : ℕ) {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : SignedPreKeyRecordStructure},
      s.pc = (blkPl_562).base + spkOff_latch → s.status = .Running → SpkLoopRegs s0 sp' x19 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length < 2 ^ 63 →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s (spkLoopMem A sp' x19 ptr bs m)
        (spkConvergePostPlaced A s0 sp' x19 ptr bs (decodeFieldsLoop SignedPreKeyRecordStructure.mergeField fuel m bs))
        (tryFromQp s0)
  | 0, s, ptr, bs, m, hpc, hrun, hregs, hsp, hcrl, htr, hfuel, _ => by
    cases bs with
    | nil => exact latch_92_empty_placed_wp rfl hpc hrun hregs hsp hcrl htr
    | cons _ _ => simp at hfuel
  | fuel + 1, s, ptr, bs, m, hpc, hrun, hregs, hsp, hcrl, htr, hfuel, hlen => by
    cases bs with
    | nil => exact latch_92_empty_placed_wp rfl hpc hrun hregs hsp hcrl htr
    | cons b0 bs1 =>
      unfold spkLoopMem
      refine latch_92_cons_placed_cps hpc hrun hregs hsp hcrl htr hlen fun s1 hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 =>
        decodeIter_104_placed_wp hH d (decodeLoop_92_placed_wp hH d fuel) hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 hfuel hlen

theorem prologue_0_to_converge_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) {x : DecodeGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32) (hpc : s0.pc = (blkPl_562).base) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ret) (hx1 : s0.readReg64 .x1 = x.bytesA)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 x.bytes.length) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗ stackAt s0.sp signedDecodeStack ∗ A.pool)
      (fun sm Pm =>
        SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret sm ∧
        (Pm ⊢ spkConvergeMem A (s0.sp - 224#64) x.ret x.bytesA x.bytes
            (spkActualDecode x.bytes) (sm.readReg64 .x1) ∗
          spkCalleeSavedAt (s0.sp - 224#64) s0))
      (tryFromQp s0) := by
  set sp' := s0.sp - 224#64
  have hstk : stackAt s0.sp signedDecodeStack =
      stackAt sp' (SpqrV1.Varint.skipField3Stack 100) ∗
        memRegion sp' 160 ∗ memRegion (sp' + 160#64) 64 :=
    spkStack_split spkCfgLegacy s0.sp
  have h160 : memRegion sp' 160 =
      memRegion sp' 16 ∗ memRegion (sp' + 16#64) 88 ∗ memRegion (sp' + 104#64) 8 ∗ memRegion (sp' + 112#64) 48 := by
    rw [show (160 : Nat) = 16 + (88 + (8 + 48)) by decide,
      ProofLib.memRegion_split sp' 16 144 (by decide), ProofLib.memRegion_split (sp' + 16#64) 88 56 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 88#64) 8 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h16 : memRegion sp' 16 = (∃∗ u0 : BitVec 64, sp' ↦₆₄ u0) ∗ (∃∗ u1 : BitVec 64, (sp' + 8#64) ↦₆₄ u1) := by
    rw [ProofLib.memRegion_split sp' 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  refine Wire.SepWPp.mono_pre
    (P' := memRegion (sp' + 160#64) 64 ∗ memRegion (sp' + 16#64) 88 ∗ memRegion sp' 16 ∗ memRegion (sp' + 104#64) 8 ∗
      (memRegion (sp' + 112#64) 48 ∗ memRegion x.ret 88 ∗ (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100)))
    (by rw [hstk]; dsimp only [sp'] at h160 ⊢; rw [h160]; apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (spkMemRegion64_unpack (sp' + 160#64)) (sepConj_mono (spkStruct88_unpack_init (sp' + 16#64)) (Entails.refl _))) ?_
  rw [h16, ProofLib.memRegion_eight (sp' + 104#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun u104 => Wire.SepWPp.exists_pre fun u1 => Wire.SepWPp.exists_pre fun u0 =>
    Wire.SepWPp.exists_pre fun s10w => Wire.SepWPp.exists_pre fun s9w => Wire.SepWPp.exists_pre fun s8w =>
    Wire.SepWPp.exists_pre fun s7w => Wire.SepWPp.exists_pre fun s6w => Wire.SepWPp.exists_pre fun s5w =>
    Wire.SepWPp.exists_pre fun s4w => Wire.SepWPp.exists_pre fun s3w => Wire.SepWPp.exists_pre fun s2w =>
    Wire.SepWPp.exists_pre fun s1w => Wire.SepWPp.exists_pre fun s0w =>
    Wire.SepWPp.exists_pre fun c7 => Wire.SepWPp.exists_pre fun c6 => Wire.SepWPp.exists_pre fun c5 =>
    Wire.SepWPp.exists_pre fun c4 => Wire.SepWPp.exists_pre fun c3 => Wire.SepWPp.exists_pre fun c2 =>
    Wire.SepWPp.exists_pre fun c1 => Wire.SepWPp.exists_pre fun c0 => ?_
  have hdk0 := @decodeKey_104_placed_cps _ A H hH d s0
  have hiter := @decodeIter_104_placed_wp _ A H hH d s0
  have hih := @decodeLoop_92_placed_wp _ A H hH d s0 sp' x.ret
  dsimp only [sp']
  have h0 : s0.readReg64 (Reg.gpr 0#5) = x.ret := hx0
  have h1 : s0.readReg64 (Reg.gpr 1#5) = x.bytesA := hx1
  have h2 : s0.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 x.bytes.length := hx2
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_key) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  have hloop0 := spkEmptyHeaders_entails_loopOf A sp' x.bytes.length
  refine Wire.SepWPp.mono_pre
    (P' := spkLoopMem A sp' x.ret x.bytesA x.bytes SignedPreKeyRecordStructure.empty ∗ spkCalleeSavedAt sp' s0)
    (by
      unfold spkLoopMem sliceCursorAt spkCalleeSavedAt; dsimp only [sp'] at hloop0 ⊢
      simp only [arm64_norm]
      refine Entails.trans (Q := (((s0.sp - 224#64 + 16#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 24#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 32#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 40#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 48#64) ↦₆₄ 1#64) ∗ ((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 64#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 72#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 224#64 + 80#64) ↦₆₄ 0#64) ∗ ((s0.sp - 224#64 + 88#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 224#64 + 96#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 224#64 + 100#64) 4) ∗
        (((s0.sp - 224#64) ↦₆₄ x.bytesA) ∗ ((s0.sp - 224#64 + 8#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗ (x.bytesA ↦ₛ x.bytes)) ∗
        ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗ memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        memRegion x.ret 88 ∗ A.pool ∗ stackAt (s0.sp - 224#64) (SpqrV1.Varint.skipField3Stack 100) ∗
        (((s0.sp - 224#64 + 160#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 224#64 + 168#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 224#64 + 176#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 224#64 + 184#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
          ((s0.sp - 224#64 + 192#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 224#64 + 200#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 224#64 + 208#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 224#64 + 216#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
        (by apply entails_of_eq; ac_rfl)
        (Entails.trans (sepConj_mono_left hloop0) (by apply entails_of_eq; ac_rfl))) ?_
  cases hbs : x.bytes with
  | nil =>
    rw [show spkActualDecode ([] : List (BitVec 8)) = none from rfl]
    exact Wire.SepWPp.frame_tryFrom
      (hdk0 (sp' := sp') (x19 := x.ret) (ptr := x.bytesA) (bs := []) (m := SignedPreKeyRecordStructure.empty) (out := none)
        (by decide) (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simp [sp', arm64_norm], by simp [sp', arm64_norm]; bv_omega, by simp [sp', arm64_norm]; bv_omega,
         by simp [arm64_norm], ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩⟩
        (by simpa [State.spAligned, arm64_norm] using spkSpAligned_sub224 hsp) hcrl1 (by simp [arm64_norm])
        (fun _ _ _ _ hdk => nomatch hdk) (fun _ => rfl))
      (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, sepConj_mono_left hentf⟩)
  | cons b0 bs1 =>
    have hlen63 : (b0 :: bs1).length < 2 ^ 63 := by simp [hbs, List.length_cons] at hlt ⊢; omega
    rw [show spkActualDecode (b0 :: bs1) =
      decodeFieldsLoop SignedPreKeyRecordStructure.mergeField (bs1.length + 1) SignedPreKeyRecordStructure.empty (b0 :: bs1) from rfl]
    exact Wire.SepWPp.frame_tryFrom
      (hiter (sp' := sp') (x19 := x.ret) (ptr := x.bytesA) (fuel := bs1.length) (b0 := b0) (bs1 := bs1)
        (m := SignedPreKeyRecordStructure.empty) (hih bs1.length) (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simp [sp', arm64_norm], by simp [sp', arm64_norm]; bv_omega, by simp [sp', arm64_norm]; bv_omega,
         by simp [arm64_norm], ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩⟩
        (by simpa [State.spAligned, arm64_norm] using spkSpAligned_sub224 hsp) hcrl1 (by simp [arm64_norm]) (by simp) hlen63)
      (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, sepConj_mono_left hentf⟩)

end Placed

end CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers
