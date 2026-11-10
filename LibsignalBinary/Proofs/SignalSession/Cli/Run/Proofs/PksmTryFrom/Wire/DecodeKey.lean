/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas -- shake: keep

/-!
# `PreKeySignalMessage::try_from`: Inlined `decode_key` and 8-Way Tag Dispatch

Symbolic execution of inlined `decode_varint` / `decode_key` (`+0x0f4..+0x16c`, `+0x308..+0x33c`)
and the 8-way protobuf field-tag dispatch (`+0x170..+0x234`) on `contractProg img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  memRegion_split decodeVarint_suffix pointsTo64_pair_entails_memRegion16
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_IS5Wire_DecodeKey : True := trivial

/-! ## 3b. Inlined `decode_varint` and `decodeKeyPK_cpsX` (`+0x0f4..+0x16c`) -/

set_option maxHeartbeats 800000 in
theorem decodeVarintMultiPK_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hSlow : PksmDecodeVarintSlowOk img A ext) (hvarint : Prost.DecodeVarintSliceOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x10c#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hne : bs ≠ []) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x154#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace → s1.readReg64 .x24 = key →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hslice := @decodeVarintSlicePK_tail_cpsX img A ext hvarint s0
  have hslow := @decodeVarintSlowPK_tail_cpsX img A ext hSlow s0
  preKeyTryFrom_fetches img.base H 268 20
  dsimp only [contractProg] at hslice hslow hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 268#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hlen_pos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hlen64 : bs.length < 2 ^ 64 := by omega
  by_cases hlen11 : 11 ≤ bs.length
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_true_eq]; omega
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (288)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact hslice (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simpa [arm64_norm] using hx28) (by simpa [arm64_norm] using hx26)
      (by simpa [arm64_norm] using hx1) (by simpa [arm64_norm] using hx2)
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simpa [arm64_norm] using htr) hlen (Or.inl hlen11) hcont hnone
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_false_iff_not]; omega
    have hlast_addr : ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) = ptr + BitVec.ofNat 64 (bs.length - 1) := by
      have heq : bs.length = (bs.length - 1) + 1 := by omega
      have h1_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (bs.length - 1) + 1#64 := by
        conv_lhs => rw [heq]; exact BitVec.ofNat_add (bs.length - 1) 1
      rw [h1_eq]; bv_omega
    by_cases hlast : (bs.getLast hne).toNat ≤ 0x7F
    · have hbit31 := (signExtend32_bit31_eq_false_iff (bs.getLast hne)).mpr hlast
      unfold sliceCursorAt; rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [sepConj_assoc]
      refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (288)) ?_; wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
      refine SepWPp.mono_pre ?_
        (hslice (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
           by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
          (by simpa [arm64_norm] using hx28) (by simpa [arm64_norm] using hx26)
          (by simpa [arm64_norm] using hx1) (by simpa [arm64_norm] using hx2)
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simpa [arm64_norm] using htr) hlen (Or.inr ⟨hne, hlast⟩) hcont hnone)
      apply entails_of_eq; unfold sliceCursorAt; rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [arm64_norm]
    · have hbit31 := (signExtend32_bit31_eq_true_iff (bs.getLast hne)).mpr (by omega)
      unfold sliceCursorAt; rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [sepConj_assoc]
      refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (748)) ?_; wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
      refine SepWPp.mono_pre ?_
        (hslow (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
           by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simpa [arm64_norm] using htr) hlen hcont hnone)
      apply entails_of_eq; unfold sliceCursorAt; rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [arm64_norm]

set_option maxHeartbeats 800000 in
theorem decodeVarintPK_inlined_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hSlow : PksmDecodeVarintSlowOk img A ext) (hvarint : Prost.DecodeVarintSliceOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0f4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : (b0 :: bs1).length < 2 ^ 32)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint (b0 :: bs1) = some (key, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x154#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace → s1.readReg64 .x24 = key →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr (b0 :: bs1) rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res) (tryFromQp s0))
    (hnone : decodeVarint (b0 :: bs1) = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res) (tryFromQp s0) := by
  let H := Rust.withPanics ext; have hmulti := @decodeVarintMultiPK_cpsX img A ext hSlow hvarint s0
  preKeyTryFrom_fetches img.base H 244 24; preKeyTryFrom_fetches img.base H 332 8
  dsimp only [contractProg] at hmulti hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 244#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h28 : s.readReg64 (Reg.gpr 28#5) = sp' + 296#64 := hx28
  have h26 : s.readReg64 (Reg.gpr 26#5) = sp' + 304#64 := hx26
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (b0 :: bs1).length := hx2
  by_cases hb0 : b0.toNat ≤ 0x7F
  · have hbit63 := (signExtend64_bit63_eq_false_iff b0).mpr hb0
    have hd := decodeVarint_cons_of_le b0 bs1 hb0
    have hsub1 : BitVec.ofNat 64 (bs1.length + 1) - 1#64 = BitVec.ofNat 64 bs1.length := by
      have h1_eq : BitVec.ofNat 64 (bs1.length + 1) = BitVec.ofNat 64 bs1.length + 1#64 := BitVec.ofNat_add bs1.length 1
      rw [h1_eq]; bv_omega
    unfold sliceCursorAt; rw [pointsToBytes_cons ptr b0 bs1]; simp only [sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (340)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    have hse := signExtend64_eq_zeroExtend64_of_le b0 hb0
    refine SepWPp.mono_pre ?_
      (hcont (b0.zeroExtend 64) bs1 _ hd (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr) (by simp only [hse, arm64_norm]))
    apply entails_of_eq; unfold sliceCursorAfter; rw [pointsToBytes_cons ptr b0 bs1]
    simp only [List.length_cons, Nat.add_sub_cancel_left, hsub1, arm64_norm]
  · have hbit63 := (signExtend64_bit63_eq_true_iff b0).mpr (by omega)
    unfold sliceCursorAt; rw [pointsToBytes_cons ptr b0 bs1]; simp only [sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (268)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre ?_
      (hmulti (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simpa [arm64_norm] using hx28) (by simpa [arm64_norm] using hx26)
        (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr) (List.cons_ne_nil b0 bs1) hlen hcont hnone)
    apply entails_of_eq; unfold sliceCursorAt; rw [pointsToBytes_cons ptr b0 bs1]; simp only [arm64_norm]

set_option maxHeartbeats 800000 in
theorem decodeKeyPK_tail_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hFrom : PksmDecodeErrorFromOk img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr key : BitVec 64}
    {bs rest : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x154#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = key)
    (hcont : ∀ (tag : Nat) (wt : WireType) (s1 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x170#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace → s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : decodeKey bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  let H := Rust.withPanics ext; have herr := @decodeErrorFromPK_tail_wpX img A ext hFrom s0
  preKeyTryFrom_fetches img.base H 340 28; preKeyTryFrom_fetches img.base H 776 28
  dsimp only [contractProg] at herr hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 340#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h24 : s.readReg64 (Reg.gpr 24#5) = key := hx24
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h27 : s.readReg64 (Reg.gpr 27#5) = 0x8000000000000002#64 := hregs.x27
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte]
    have hres := hnone hdk; subst hres; have hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    rw [memRegion64_split_448_456_464 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w1 => SepWPp.exists_pre (fun w0 => ?_))
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (804)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    refine SepWPp.mono_pre ?_
      (herr (w0 := w0) (mErr := m) (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr) (by simp only [KindNoHeap, arm64_norm]))
    refine Entails.trans ?_ (decodeKeyPK_err_entailsX A sp' ptr w0 key bs rest m); apply entails_of_eq; ac_rfl
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt]
      have hres := hnone hdk; subst hres
      have hge6 : 6 ≤ key.toNat % 8 := (WireType.ofNat?_eq_none_iff (key.toNat % 8) (by omega)).mp hwt
      have hbcs := key_and7_ule6_of_ge key hge6
      rw [memRegion64_split_448_456_464 sp']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre (fun w1 => SepWPp.exists_pre (fun w0 => ?_))
      refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (804)) ?_; wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
      refine SepWPp.mono_pre ?_
        (herr (w0 := w0) (mErr := m) (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
           by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simpa [arm64_norm] using htr) (by simp only [KindNoHeap, arm64_norm]))
      refine Entails.trans ?_ (decodeKeyPK_err_entailsX A sp' ptr w0 (key &&& 7#64) bs rest m); apply entails_of_eq; ac_rfl
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := WireType.lt_six_of_ofNat?_eq_some hwt
      have hbcs := key_and7_ule6_of_lt key hlt6
      by_cases htag0 : key.toNat / 8 < 1
      · have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hres := hnone hdk; subst hres; have hcbz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
        rw [memRegion64_split8 sp', ProofLib.memRegion_eight (sp' + 448#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_pre (fun w0 => ?_)
        refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (804)) ?_; wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
        refine SepWPp.mono_pre ?_
          (herr (w0 := w0) (mErr := m) (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
             by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
             by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
            hF1 hsym1 (by simpa [arm64_norm] using htr) (by simp only [KindNoHeap, arm64_norm]))
        refine Entails.trans (sepConj_mono_left (sliceCursorAfter_entails_memRegion (sp' + 296#64) ptr bs rest)) ?_
        apply entails_of_eq; simp only [arm64_norm]
      · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
        refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (368)) ?_; wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
        have htag_eq := key_tag32_zeroExtend64_eq key hkey_lt
        have hand7_eq := key_and7_eq_wt key hwt
        exact hcont (key.toNat / 8) wt _ hdk (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
           by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simpa [arm64_norm] using htr)
          (by simp only [arm64_norm]; exact hand7_eq) (by simp only [arm64_norm]; exact htag_eq)

theorem decodeKeyPK_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    (hSlow : PksmDecodeVarintSlowOk img A ext)
    (hvarint : Prost.DecodeVarintSliceOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0f4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : (b0 :: bs1).length < 2 ^ 32)
    (hcont : ∀ (tag : Nat) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x170#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace → s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr (b0 :: bs1) rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res) (tryFromQp s0))
    (hnone : decodeKey (b0 :: bs1) = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res) (tryFromQp s0) :=
  decodeVarintPK_inlined_cpsX hSlow hvarint hpc hrun hregs hx28 hx26 hx2 hsp hF hsym htr hlen
    (fun key rest s1 hdv hpc1 hrun1 hregs1 hsp1 hF1 hsym1 htr1 hx24_1 =>
      decodeKeyPK_tail_cpsX hFrom hdv hpc1 hrun1 hregs1 hsp1 hF1 hsym1 htr1 hx24_1
        (fun tag wt s2 hdk => hcont tag wt rest s2 hdk) hnone)
    (fun hdv_none => hnone (by simp [decodeKey, hdv_none]))

theorem decodeKeyPK_of_callees_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0f4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : (b0 :: bs1).length < 2 ^ 32)
    (hcont : ∀ (tag : Nat) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x170#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace → s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr (b0 :: bs1) rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res) (tryFromQp s0))
    (hnone : decodeKey (b0 :: bs1) = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr (b0 :: bs1) res) (tryFromQp s0) :=
  decodeKeyPK_cpsX hC.decodeErrorFrom hC.decodeVarintSlow hC.varintSlice
    hpc hrun hregs hx28 hx26 hx2 hsp hF hsym htr hlen hcont hnone

/-! ## 4. 8-Way Tag Dispatch (`+0x170..+0x234`) -/

theorem tag_ge9_conds (tag : Nat) (hge : 9 ≤ tag) (hlt : tag < 2 ^ 32) :
    let w1 := (BitVec.ofNat 64 tag).setWidth 32
    ((w1 == 1#32) = false) ∧ ((w1 == 2#32) = false) ∧ ((w1 != 2#32) = true) ∧
    ((w1 == 3#32) = false) ∧ ((w1 != 3#32) = true) ∧
    ((w1 == 4#32) = false) ∧ ((w1 != 4#32) = true) ∧ ((w1 == 5#32) = false) ∧
    ((w1 == 6#32) = false) ∧ ((w1 != 6#32) = true) ∧
    ((w1 == 7#32) = false) ∧ ((w1 != 7#32) = true) ∧
    ((w1 == 8#32) = false) ∧ ((w1 != 8#32) = true) := by
  dsimp only; rw [setWidth32_ofNat64]
  have h1 : BitVec.ofNat 32 tag ≠ 1#32 := by bv_omega
  have h2 : BitVec.ofNat 32 tag ≠ 2#32 := by bv_omega
  have h3 : BitVec.ofNat 32 tag ≠ 3#32 := by bv_omega
  have h4 : BitVec.ofNat 32 tag ≠ 4#32 := by bv_omega
  have h5 : BitVec.ofNat 32 tag ≠ 5#32 := by bv_omega
  have h6 : BitVec.ofNat 32 tag ≠ 6#32 := by bv_omega
  have h7 : BitVec.ofNat 32 tag ≠ 7#32 := by bv_omega
  have h8 : BitVec.ofNat 32 tag ≠ 8#32 := by bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2, bne_iff_ne.mpr h2,
    beq_eq_false_iff_ne.mpr h3, bne_iff_ne.mpr h3,
    beq_eq_false_iff_ne.mpr h4, bne_iff_ne.mpr h4, beq_eq_false_iff_ne.mpr h5,
    beq_eq_false_iff_ne.mpr h6, bne_iff_ne.mpr h6,
    beq_eq_false_iff_ne.mpr h7, bne_iff_ne.mpr h7,
    beq_eq_false_iff_ne.mpr h8, bne_iff_ne.mpr h8⟩

set_option maxHeartbeats 800000 in
theorem dispatchPK_cps {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {tag : Nat}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x170#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag) (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x260#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1 P Q Qp)
    (h2 : tag = 2 → ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x190#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1 P Q Qp)
    (h3 : tag = 3 → ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2a0#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1 P Q Qp)
    (h4 : tag = 4 → ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x200#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1 P Q Qp)
    (h5 : tag = 5 → ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x280#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1 P Q Qp)
    (h6 : tag = 6 → ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x1d0#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1 P Q Qp)
    (h7 : tag = 7 → ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2c8#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1 P Q Qp)
    (h8 : tag = 8 → ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x238#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true → img.FrozenLoaded s1 →
      s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1 P Q Qp)
    (h9 : 9 ≤ tag → ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2d8#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1 P Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s P Q Qp := by
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 368 32; preKeyTryFrom_fetches img.base H 440 24
  preKeyTryFrom_fetches img.base H 496 16; preKeyTryFrom_fetches img.base H 552 16
  dsimp only [contractProg] at h1 h2 h3 h4 h5 h6 h7 h8 h9 hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 368#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (608)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact h1 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (400)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact h2 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (672)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact h3 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 4#64 := hx1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (512)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact h4 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 5#64 := hx1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (640)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact h5 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 6#64 := hx1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (464)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact h6 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 7#64 := hx1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (712)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact h7 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 8#64 := hx1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (568)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
    exact h8 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 9) := hx1
    obtain ⟨hc1, hc2, hc2_ne, hc3, hc3_ne, hc4, hc4_ne, hc5, hc6, hc6_ne, hc7, hc7_ne, hc8, hc8_ne⟩ :=
      tag_ge9_conds (n + 9) (by omega) htag_lt
    cases hgt4 : BitVec.slt 4#32 ((BitVec.ofNat 64 (n + 9)).setWidth 32)
    · cases hgt2 : BitVec.slt 2#32 ((BitVec.ofNat 64 (n + 9)).setWidth 32)
      · refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (728)) ?_; wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
        exact h9 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
           by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
      · refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (728)) ?_; wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
        exact h9 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
           by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
    · cases hgt6 : BitVec.slt 6#32 ((BitVec.ofNat 64 (n + 9)).setWidth 32)
      · refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (728)) ?_; wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
        exact h9 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
           by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
      · refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (728)) ?_; wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
        exact h9 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
           by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
