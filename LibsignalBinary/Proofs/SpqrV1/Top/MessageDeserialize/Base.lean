/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Base Step Lemmas for `<Message>::deserialize`

Symbolic execution of the varint loop, post-varint 32-byte chunk copy, and shared `Ok` / `Err`
epilogues for `<spqr::v1::chunked::states::Message>::deserialize` (`0x5f434..0x5f780`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.MessageDeserialize

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  msgDeserialize_fnOff
  libsignalSessionCode_fnOff_0x5a03c

theorem sp_sub_144_aligned (s0 : State) (h : s0.spAligned = true) :
    ((s0.sp - 144#64) &&& 15#64 == 0#64) = true := by
  simp only [State.spAligned, beq_iff_eq] at h ⊢
  generalize s0.sp = sp at h ⊢
  revert sp h; bv_kernel

/-- High callee-saved registers `x23..x28` and `calleeSavedVRegs` untouched by
    `<Message>::deserialize`. -/
def DeserHighCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

set_option maxHeartbeats 800000 in
/-- Shared `Err(.msgDecode)` epilogue (`0x5f6cc..0x5f6ec`, `+664..+696`, 9 instructions). -/
theorem step_err_tail (P_poly : PolyApi) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode)
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName + 664#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hcs : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  have hfn : libsignalSessionCode.fnOff messageDeserializeName = 0x5a03c := msgDeserialize_fnOff
  code_fetches_range libsignalSessionCode libsignalSessionBin base hooks hfn 0x5a03c 664 36
  clear hfn
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_144_aligned s0 hs0A
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  subst hP hpost
  dsimp only [messageDeserializeName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase base hooks).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  refine SepWP.fold (rawOutBufAt_entails_err_split call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a)
    (by sep_focus) ?_
  unfold msgDeserSavedAt
  wp_steps
  dsimp only [messageDeserializeSpecX]
  rw [herr]
  dsimp only [messageResultAt]
  refine SepWP.fold (fold_messageErrorAt_region call.out) (by sep_focus) ?_
  refine SepWP.fold (msgDeser_stack_restore s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
    unfold msgDeserSavedAt
    sep_focus) ?_
  wp_done

set_option maxHeartbeats 1200000 in
/-- Shared `Ok` epilogue (`0x5f680..0x5f6c8`, `+588..+660`, 19 instructions). -/
theorem step_ok_tail (P_poly : PolyApi) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall)
    (tag : BitVec 8) (idxReg : BitVec 64) (c2 : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hok : rawOkOutAt call.out call.epoch tag st0 st1 c2 st3 st4 st5 st6 (idxReg.truncate 16) ⊢
      messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes))
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx1 : s.readReg64 .x1 = call.epoch)
    (hx8 : s.readReg64 .x8 = tag.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = idxReg)
    (hx10 : s.readReg64 .x10 = c2.zeroExtend 64)
    (hx29 : s.readReg64 .fp = s0.sp - 48#64)
    (hcs : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  have hfn : libsignalSessionCode.fnOff messageDeserializeName = 0x5a03c := msgDeserialize_fnOff
  code_fetches_range libsignalSessionCode libsignalSessionBin base hooks hfn 0x5a03c 588 76
  clear hfn
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_144_aligned s0 hs0A
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  subst hP hpost
  dsimp only [messageDeserializeName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase base hooks).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  unfold rawOutBufAt chunk32AtomsAt msgDeserScratchAt msgDeserSavedAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 5
  -- Swap `(s0.sp - 104 ↦₈ st4) ∗ (s0.sp - 103 ↦₆₄ st5)` for unaligned `ldr q0, [sp, #0x20]`.
  have hswap_st : (((s0.sp - 104#64) ↦₈ st4) ∗ ((s0.sp - 103#64) ↦₆₄ st5)) ⊢
      ((s0.sp - 104#64) ↦₆₄ shiftWord st4 st5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5) := by
    have h1 := byte_word64_swap (s0.sp - 104#64) st4 st5
    have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
    have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
    rw [ha1, ha8] at h1
    exact Entails.of_eq h1
  have hunswap_st : (((s0.sp - 104#64) ↦₆₄ shiftWord st4 st5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5)) ⊢
      ((s0.sp - 104#64) ↦₈ st4) ∗ ((s0.sp - 103#64) ↦₆₄ st5) := by
    have h1 := (byte_word64_swap (s0.sp - 104#64) st4 st5).symm
    have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
    have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
    rw [ha1, ha8] at h1
    exact Entails.of_eq h1
  refine SepWP.fold hswap_st (by sep_focus) ?_
  wp_steps 1
  -- Restore `[s0.sp - 104]` and `[s0.sp - 103]` for `ldur q1, [sp, #0x29]`.
  refine SepWP.fold hunswap_st (by sep_focus) ?_
  wp_steps 5
  -- Swap `[call.out + 25]` and `[call.out + 26]` for unaligned `stur q0, [x0, #0x11]`.
  have hswap_out : (((call.out + 25#64) ↦₈ oc4) ∗ ((call.out + 26#64) ↦₆₄ oc5)) ⊢
      ((call.out + 25#64) ↦₆₄ shiftWord oc4 oc5) ∗ ((call.out + 33#64) ↦₈ hiByte oc5) := by
    have h1 := byte_word64_swap (call.out + 25#64) oc4 oc5
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
    exact Entails.of_eq h1
  refine SepWP.fold hswap_out (by sep_focus) ?_
  wp_steps 1
  -- Restore `[call.out + 25 ↦₈ st4]` and `[call.out + 26 ↦₆₄ ...]` before `stur q1`.
  have hunswap_out : (((call.out + 25#64) ↦₆₄ shiftWord st4 st5) ∗ ((call.out + 33#64) ↦₈ hiByte oc5)) ⊢
      ((call.out + 25#64) ↦₈ st4) ∗ ((call.out + 26#64) ↦₆₄ unshiftWord (shiftWord st4 st5) (hiByte oc5)) := by
    have h1 := shiftWord_byte_swap (call.out + 25#64) st4 st5 (hiByte oc5)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
    exact Entails.of_eq h1
  refine SepWP.fold hunswap_out (by sep_focus) ?_
  wp_steps
  dsimp only [messageDeserializeSpecX]
  have hfold_ok :
      ((call.out ↦₆₄ call.epoch) ∗ ((call.out + 8#64) ↦₈ tag) ∗ ((call.out + 9#64) ↦₈ 1#8) ∗
        ((call.out + 10#64) ↦₃₂ st0) ∗ ((call.out + 14#64) ↦₁₆ st1) ∗ ((call.out + 16#64) ↦₈ c2) ∗
        ((call.out + 17#64) ↦₆₄ st3) ∗ ((call.out + 25#64) ↦₈ st4) ∗
        ((call.out + 26#64) ↦₆₄ st5) ∗ ((call.out + 34#64) ↦₆₄ st6) ∗
        ((call.out + 42#64) ↦₁₆ BitVec.truncate 16 (BitVec.truncate 32 idxReg)) ∗
        memRegion (call.out + 44#64) 4) ⊢
      messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes) := by
    have htr16 : BitVec.truncate 16 (BitVec.truncate 32 idxReg) = idxReg.truncate 16 :=
      BitVec.setWidth_setWidth_of_le (x := idxReg) (by decide)
    rw [htr16]
    refine Entails.trans ?_ hok
    unfold rawOkOutAt chunk32AtomsAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.fold hfold_ok (by sep_focus) ?_
  refine SepWP.fold (msgDeser_stack_restore s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
    unfold msgDeserScratchAt msgDeserSavedAt
    sep_focus) ?_
  wp_done

theorem rest2_lt32_of_ult {tag : BitVec 8} {pre₁ rest2 : List (BitVec 8)}
    (hlt : (tag :: (pre₁ ++ rest2)).length < 2 ^ 63)
    (hult : (BitVec.ofNat 64 (tag :: (pre₁ ++ rest2)).length).ult (BitVec.ofNat 64 pre₁.length + 33#64) = true) :
    rest2.length < 32 := by
  simp [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat] at hlt hult
  omega

theorem rest2_ge32_of_not_ult {tag : BitVec 8} {pre₁ rest2 : List (BitVec 8)}
    (hlt : (tag :: (pre₁ ++ rest2)).length < 2 ^ 63)
    (hult : ¬(BitVec.ofNat 64 (tag :: (pre₁ ++ rest2)).length).ult (BitVec.ofNat 64 pre₁.length + 33#64) = true) :
    ¬ rest2.length < 32 := by
  simp [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat] at hlt hult
  omega

theorem index_gt65535_of_lsr16 {index : BitVec 64}
    (hne : ¬index >>> 16 = 0#64) :
    index.toNat > 65535 := by
  bv_omega

theorem index_le65535_of_lsr16 {index : BitVec 64}
    (heq : index >>> 16 = 0#64) :
    ¬(index.toNat > 65535) := by
  bv_omega

set_option maxHeartbeats 1600000 in
/-- Post-varint length & `u16` range check plus 32-byte chunk copy (`0x5f640..0x5f67c`,
    `+524..+588`). -/
theorem step_after_varint (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall)
    (tag : BitVec 8) (pre₁ rest2 : List (BitVec 8)) (index : BitVec 64)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (htag : tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8)
    (hsplit : call.fromBytes = (tag :: pre₁) ++ rest2)
    (hlen_lt : call.fromBytes.length < 2 ^ 63)
    (hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
      deserAfterVarint P_poly call.epoch tag (some (index, rest2)))
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName + 524#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx1 : s.readReg64 .x1 = call.epoch)
    (hx2 : s.readReg64 .x2 = call.fromPtr)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hx8 : s.readReg64 .x8 = tag.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = index)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 pre₁.length)
    (hx29 : s.readReg64 .fp = s0.sp - 48#64)
    (hcs : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  have hfn : libsignalSessionCode.fnOff messageDeserializeName = 0x5a03c := msgDeserialize_fnOff
  have herr_tail := step_err_tail P_poly base hooks A call o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
  code_fetches_range libsignalSessionCode libsignalSessionBin base hooks hfn 0x5a03c 524 64
  clear hfn
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_144_aligned s0 hs0A
  have hfrom_len : call.fromBytes.length = 1 + pre₁.length + rest2.length := by
    rw [hsplit, List.length_append, List.length_cons]; omega
  have hlen_lt' : (tag :: (pre₁ ++ rest2)).length < 2 ^ 63 := by
    have : call.fromBytes = tag :: (pre₁ ++ rest2) := by simpa using hsplit
    rwa [← this]
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  dsimp only [messageDeserializeName] at hpc herr_tail ⊢
  generalize_entry hentry : (libsignalSessionCode.rebase base hooks).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  wp_steps 3
  wp_if hhi
  · have hlt32 : rest2.length < 32 := rest2_lt32_of_ult hlen_lt' hhi
    have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
      rw [hdeser]; unfold deserAfterVarint; simp [hlt32]
    exact herr_tail _ P R post hpost herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩ hP
  · have hge32 : ¬ rest2.length < 32 := rest2_ge32_of_not_ult hlen_lt' hhi
    clear hhi
    wp_steps 2
    wp_if hcbnz
    · have hgt16 : index.toNat > 65535 := index_gt65535_of_lsr16 hcbnz
      have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
        rw [hdeser]; unfold deserAfterVarint; simp [hge32, hgt16]
      exact herr_tail _ P R post hpost herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hsp, arm64_norm]) hs0A (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm])
        ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
         by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩ hP
    · have hle16 : ¬ index.toNat > 65535 := index_le65535_of_lsr16 hcbnz
      clear hcbnz herr_tail
      have hlen32 : (rest2.take 32).length = 32 := by rw [List.length_take]; omega
      obtain ⟨c0, c1, c2, c3, c4, c5, c6, htake⟩ :=
        exists_chunk32Bytes_of_length_32 hlen32
      have hok : rawOkOutAt call.out call.epoch tag c0 c1 c2 c3 c4 c5 c6 (index.truncate 16) ⊢
          messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes) := by
        rw [hdeser]
        unfold deserAfterVarint
        simp only [hge32, ↓reduceDIte, hle16, ↓reduceIte]
        exact rawOkOutAt_entails_mkChunkMsg P_poly hPoly call.out call.epoch tag (index.truncate 16)
          c0 c1 c2 c3 c4 c5 c6 ⟨rest2.take 32, hlen32⟩ htake htag
      have hok_tail := step_ok_tail P_poly base hooks A call tag index c2
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 c3 c4 c5 c6 c0 c1 fb0 f50 f58 s0
      dsimp only [messageDeserializeName] at hok_tail
      rw [hentry] at hok_tail
      have hexp := fromBytes_expose_chunk32 call.fromPtr call.fromBytes pre₁ rest2
        tag c0 c1 c2 c3 c4 c5 c6 hsplit htake
      have hunexp := fromBytes_unexpose_chunk32 call.fromPtr call.fromBytes pre₁ rest2
        tag c0 c1 c2 c3 c4 c5 c6 hsplit htake
      let x10_ptr := call.fromPtr + (BitVec.ofNat 64 pre₁.length - 1#64)
      have hswap_in : (((x10_ptr + 17#64) ↦₈ c4) ∗ ((x10_ptr + 18#64) ↦₆₄ c5)) ⊢
          ((x10_ptr + 17#64) ↦₆₄ shiftWord c4 c5) ∗ ((x10_ptr + 25#64) ↦₈ hiByte c5) := by
        have h1 := byte_word64_swap (x10_ptr + 17#64) c4 c5
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
        exact Entails.of_eq h1
      have hunswap_in : (((x10_ptr + 17#64) ↦₆₄ shiftWord c4 c5) ∗ ((x10_ptr + 25#64) ↦₈ hiByte c5)) ⊢
          ((x10_ptr + 17#64) ↦₈ c4) ∗ ((x10_ptr + 18#64) ↦₆₄ c5) := by
        have h1 := (byte_word64_swap (x10_ptr + 17#64) c4 c5).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
        exact Entails.of_eq h1
      have hswap_st : (((s0.sp - 104#64) ↦₈ st4) ∗ ((s0.sp - 103#64) ↦₆₄ st5)) ⊢
          ((s0.sp - 104#64) ↦₆₄ shiftWord st4 st5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5) := by
        have h1 := byte_word64_swap (s0.sp - 104#64) st4 st5
        have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
        have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
        rw [ha1, ha8] at h1
        exact Entails.of_eq h1
      have hunswap_st : (((s0.sp - 104#64) ↦₆₄ shiftWord c4 c5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5)) ⊢
          ((s0.sp - 104#64) ↦₈ c4) ∗ ((s0.sp - 103#64) ↦₆₄ unshiftWord (shiftWord c4 c5) (hiByte st5)) := by
        have h1 := shiftWord_byte_swap (s0.sp - 104#64) c4 c5 (hiByte st5)
        have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
        have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
        rw [ha1, ha8] at h1
        exact Entails.of_eq h1
      subst hP
      wp_steps 2
      refine SepWP.fold hexp (by sep_focus) ?_
      unfold chunk32AtX10
      wp_steps 2
      refine SepWP.fold hswap_in (by sep_focus) ?_
      wp_steps 1
      refine SepWP.fold hunswap_in (by sep_focus) ?_
      wp_steps 2
      refine SepWP.fold hunexp (by
        unfold chunk32AtX10
        sep_focus) ?_
      unfold msgDeserScratchAt
      wp_steps 2
      refine SepWP.fold hswap_st (by sep_focus) ?_
      wp_steps 1
      refine SepWP.fold hunswap_st (by sep_focus) ?_
      wp_steps 1
      exact hok_tail _ _ R post hpost hok
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
        (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
        (by simp [hx8, arm64_norm]) (by simp [hx9, arm64_norm]) (by simp [arm64_norm])
        (by simp [hx29, arm64_norm])
        ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
         by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩
        (by unfold msgDeserScratchAt; ac_rfl)

/-! ## Varint Loop & Pre-Loop Stepping (`0x5f474..0x5f63c`) -/

theorem decodeVarintLoop_stop (j : Nat) (out : BitVec 64) (b : BitVec 8) (rest2 : List (BitVec 8))
    (hb : b &&& 0x80#8 = 0#8) :
    decodeVarintLoop j out (b :: rest2) =
      some (out ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * j)), rest2) := by
  simp [decodeVarintLoop, hb]

theorem decodeVarintLoop_cont_end (j : Nat) (out : BitVec 64) (b : BitVec 8) (rest2 : List (BitVec 8))
    (hj : j < 10) (hb : b &&& 0x80#8 ≠ 0#8) (hend : min (j + 1 + rest2.length) 10 ≤ j + 1) :
    decodeVarintLoop j out (b :: rest2) = none := by
  unfold decodeVarintLoop
  simp only [hb, ↓reduceIte, MAX_VARINT_BYTES_LEN]
  by_cases h10 : j + 1 = 10
  · simp [h10]
  · simp only [h10, ↓reduceIte]
    cases rest2 with
    | nil => rfl
    | cons b2 tl =>
      simp only [List.length_cons] at hend
      omega

theorem decodeVarintLoop_cont_step (j : Nat) (out : BitVec 64) (b : BitVec 8) (rest2 : List (BitVec 8))
    (hj : j + 1 < 10) (hb : b &&& 0x80#8 ≠ 0#8) :
    decodeVarintLoop j out (b :: rest2) =
      decodeVarintLoop (j + 1) (out ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * j))) rest2 := by
  have hne : j + 1 ≠ MAX_VARINT_BYTES_LEN := by unfold MAX_VARINT_BYTES_LEN; omega
  simp [decodeVarintLoop, hb, hne]

abbrev sbfm8Val (b : BitVec 8) : BitVec 64 :=
  BitVec.zeroExtend 64
    (BitVec.truncate 32
      (BitVec.zeroExtend 64 b >>> 0 &&& 255#64 |||
        (if b.getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551360#64))

theorem sbfm8_bit31_nz {b : BitVec 8}
    (h : (sbfm8Val b).getLsbD 31 = true) :
    b &&& 0x80#8 ≠ 0#8 := by
  unfold sbfm8Val at h
  bv_bits

theorem sbfm8_bit31_z {b : BitVec 8}
    (h : ¬(sbfm8Val b).getLsbD 31 = true) :
    b &&& 0x80#8 = 0#8 := by
  unfold sbfm8Val at h
  bv_bits

theorem varint_orr_lsl_eq (j : Nat) (hj : j < 10) (out : BitVec 64) (b : BitVec 8) :
    ((b.zeroExtend 64 &&& 127#64) <<< ((BitVec.ofNat 64 (7 * j)).toNat % 64)) ||| out =
      out ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * j)) := by
  have hmod : (BitVec.ofNat 64 (7 * j)).toNat % 64 = 7 * j := by
    rw [BitVec.toNat_ofNat]
    omega
  have hand : b.zeroExtend 64 &&& 127#64 = (b &&& 0x7f#8).zeroExtend 64 := by bv_bits
  rw [hmod, hand, BitVec.or_comm]

theorem varint_cs_true {j n : Nat} (hj : j < 10)
    (h : (BitVec.ofNat 64 (min (j + 1 + n) 10)).ule (BitVec.ofNat 64 (j + 1)) = true) :
    min (j + 1 + n) 10 ≤ j + 1 := by
  simp [BitVec.ule, BitVec.toNat_ofNat] at h
  omega

theorem varint_cs_false {j n : Nat} (hj : j < 10)
    (h : ¬(BitVec.ofNat 64 (min (j + 1 + n) 10)).ule (BitVec.ofNat 64 (j + 1)) = true) :
    j + 1 < min (j + 1 + n) 10 := by
  simp [BitVec.ule, BitVec.toNat_ofNat] at h
  omega

theorem varint_pre_eq_zero {tag : BitVec 8} {rest : List (BitVec 8)}
    (hlt : (tag :: rest).length < 2 ^ 63)
    (heq : BitVec.ofNat 64 (tag :: rest).length = 1#64) :
    rest = [] := by
  have hlen : rest.length = 0 := by
    have h1 : (BitVec.ofNat 64 (tag :: rest).length).toNat = 1 := by rw [heq]; rfl
    simp [BitVec.toNat_ofNat] at hlt h1
    omega
  exact List.eq_nil_of_length_eq_zero hlen

theorem varint_pre_ne_zero {tag : BitVec 8} {rest : List (BitVec 8)}
    (hne : ¬BitVec.ofNat 64 (tag :: rest).length = 1#64) :
    rest ≠ [] := by
  intro hnil
  subst hnil
  exact hne rfl

theorem varint_pre_csel_eq {tag : BitVec 8} {rest : List (BitVec 8)}
    (hlt : (tag :: rest).length < 2 ^ 63) :
    (if (BitVec.ofNat 64 (tag :: rest).length - 1#64).ult 10#64 = true then
      BitVec.ofNat 64 (tag :: rest).length - 1#64
    else 10#64) = BitVec.ofNat 64 (min rest.length 10) := by
  have hsub : BitVec.ofNat 64 (tag :: rest).length - 1#64 = BitVec.ofNat 64 rest.length := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat] at hlt ⊢
    omega
  rw [hsub]
  have hlt' : rest.length < 2 ^ 63 := by simp at hlt; omega
  by_cases h10 : rest.length < 10
  · have hult : (BitVec.ofNat 64 rest.length).ult 10#64 = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    simp [hult, Nat.min_eq_left (by omega : rest.length ≤ 10)]
  · have hult : ¬(BitVec.ofNat 64 rest.length).ult 10#64 = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    simp [hult, Nat.min_eq_right (by omega : 10 ≤ rest.length)]

theorem step_at_520 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall)
    (tag b : BitVec 8) (pre₁' rest2 : List (BitVec 8)) (index : BitVec 64)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (htag : tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8)
    (hsplit : call.fromBytes = (tag :: pre₁') ++ rest2)
    (hlen_lt : call.fromBytes.length < 2 ^ 63)
    (herr_case : b &&& 0x80#8 ≠ 0#8 →
      Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode)
    (hok_case : b &&& 0x80#8 = 0#8 →
      Message.deserialize P_poly call.epoch call.fromBytes =
        deserAfterVarint P_poly call.epoch tag (some (index, rest2)))
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName + 520#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx1 : s.readReg64 .x1 = call.epoch)
    (hx2 : s.readReg64 .x2 = call.fromPtr)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hx8 : s.readReg64 .x8 = tag.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = index)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 pre₁'.length)
    (hx14 : s.readReg64 .x14 = sbfm8Val b)
    (hx29 : s.readReg64 .fp = s0.sp - 48#64)
    (hcs : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  have hfn : libsignalSessionCode.fnOff messageDeserializeName = 0x5a03c := msgDeserialize_fnOff
  have herr_tail := step_err_tail P_poly base hooks A call o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
  have hafter := step_after_varint P_poly hPoly base hooks A call tag pre₁' rest2 index
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
  code_fetches_range libsignalSessionCode libsignalSessionBin base hooks hfn 0x5a03c 520 4
  clear hfn
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  dsimp only [messageDeserializeName] at hpc herr_tail hafter ⊢
  generalize_entry (libsignalSessionCode.rebase base hooks).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  wp_steps 1
  wp_if htb
  · have hb : b &&& 0x80#8 ≠ 0#8 := sbfm8_bit31_nz htb
    exact herr_tail _ P R post hpost (herr_case hb)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩ hP
  · have hb : b &&& 0x80#8 = 0#8 := sbfm8_bit31_z htb
    exact hafter _ P R post hpost htag hsplit hlen_lt (hok_case hb)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
      (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
      (by simp [hx9, arm64_norm]) (by simp [hx10, arm64_norm]) (by simp [hx29, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩ hP

abbrev VarintLoopStmt (loopOff : BitVec 64)
    (P_poly : PolyApi) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) : Prop :=
  (post = fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) →
  (tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8) →
  call.fromBytes.length < 2 ^ 63 →
  s0.spAligned = true →
  ∀ (rest1 pre₁ : List (BitVec 8)) (out : BitVec 64) (s : State) (P : SepProp),
    rest1 ≠ [] →
    pre₁.length < 10 →
    call.fromBytes = (tag :: pre₁) ++ rest1 →
    Message.deserialize P_poly call.epoch call.fromBytes =
      deserAfterVarint P_poly call.epoch tag (decodeVarintLoop pre₁.length out rest1) →
    s.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName + loopOff →
    s.status = .Running →
    s.sp = s0.sp - 144#64 →
    s.trace = s0.trace →
    s.readReg64 .x0 = call.out →
    s.readReg64 .x1 = call.epoch →
    s.readReg64 .x2 = call.fromPtr →
    s.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length →
    s.readReg64 .x8 = tag.zeroExtend 64 →
    s.readReg64 .x9 = out →
    s.readReg64 .x10 = BitVec.ofNat 64 pre₁.length →
    s.readReg64 .x11 = BitVec.ofNat 64 (7 * pre₁.length) →
    s.readReg64 .x12 = BitVec.ofNat 64 (min (pre₁.length + rest1.length) 10) →
    s.readReg64 .x13 = call.fromPtr + 1#64 →
    s.readReg64 .fp = s0.sp - 48#64 →
    DeserHighCalleeSaved s0 s →
    P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) →
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post

set_option hygiene false in
macro "prove_varint_loop" off:num len:num tail_step:tactic : tactic => `(tactic| (
  intro hpost htag hlen_lt hs0A rest1 pre₁ out s P hne hj hsplit hdeser
    hpc hrun hsp htr hx0 hx1 hx2 hx3 hx8 hx9 hx10 hx11 hx12 hx13 hx29 hcs hP
  induction rest1 generalizing pre₁ out s P with
  | nil => exact absurd rfl hne
  | cons b rest2 ih =>
    have hfn : libsignalSessionCode.fnOff messageDeserializeName = 0x5a03c := msgDeserialize_fnOff
    code_fetches_range libsignalSessionCode libsignalSessionBin base hooks hfn 0x5a03c $off $len
    clear hfn hne
    have hlen_rest : pre₁.length + (b :: rest2).length = pre₁.length + 1 + rest2.length := by
      simp only [List.length_cons]; omega
    rw [hlen_rest] at hx12
    have hsplit' : call.fromBytes = (tag :: (pre₁ ++ [b])) ++ rest2 := by
      simp [hsplit]
    have hlen_pre1' : (pre₁ ++ [b]).length = pre₁.length + 1 := by simp
    have h10_add : BitVec.ofNat 64 pre₁.length + 1#64 = BitVec.ofNat 64 (pre₁ ++ [b]).length := by
      rw [hlen_pre1']; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h11_add : BitVec.ofNat 64 (7 * pre₁.length) + 7#64 = BitVec.ofNat 64 (7 * (pre₁ ++ [b]).length) := by
      rw [hlen_pre1']; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    let out' := out ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * pre₁.length))
    have horr := varint_orr_lsl_eq pre₁.length hj out b
    have h520 := step_at_520 P_poly hPoly base hooks A call tag b (pre₁ ++ [b]) rest2 out'
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
    have haddr_b : call.fromPtr + (1#64 + BitVec.ofNat 64 pre₁.length) =
        call.fromPtr + BitVec.ofNat 64 (tag :: pre₁).length := by
      simp only [List.length_cons]; bv_omega
    have hexp := fromBytes_expose_byte call.fromPtr call.fromBytes (tag :: pre₁) rest2 b
      (call.fromPtr + (1#64 + BitVec.ofNat 64 pre₁.length)) hsplit haddr_b
    have hunexp := fromBytes_unexpose_byte call.fromPtr call.fromBytes (tag :: pre₁) rest2 b
      (call.fromPtr + (1#64 + BitVec.ofNat 64 pre₁.length)) hsplit haddr_b
    rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
    dsimp only [messageDeserializeName] at hpc h520 ih ⊢
    generalize_entry (libsignalSessionCode.rebase base hooks).fnAddr
      "<spqr::v1::chunked::states::Message>::deserialize" = entry
    examples_hide_fetches
    subst hP
    refine SepWP.fold hexp (by sep_focus) ?_
    wp_steps 1
    refine SepWP.fold hunexp (by sep_focus) ?_
    wp_steps 7
    wp_if hcs_br
    · have hend : min (pre₁.length + 1 + rest2.length) 10 ≤ pre₁.length + 1 :=
        varint_cs_true hj hcs_br
      have herr_case : b &&& 0x80#8 ≠ 0#8 →
          Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
        intro hb; rw [hdeser, decodeVarintLoop_cont_end pre₁.length out b rest2 hj hb hend]; rfl
      have hok_case : b &&& 0x80#8 = 0#8 →
          Message.deserialize P_poly call.epoch call.fromBytes =
            deserAfterVarint P_poly call.epoch tag (some (out', rest2)) := by
        intro hb; rw [hdeser, decodeVarintLoop_stop pre₁.length out b rest2 hb]
      exact h520 _ _ R post hpost htag hsplit' hlen_lt herr_case hok_case
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
        (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
        (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
        (by simp [out', arm64_norm]) (by simp [arm64_norm])
        (by simp [sbfm8Val, arm64_norm]) (by simp [hx29, arm64_norm])
        ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
         by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩ rfl
    · have hmore : pre₁.length + 1 < min (pre₁.length + 1 + rest2.length) 10 :=
        varint_cs_false hj hcs_br
      clear hcs_br
      have hj1 : pre₁.length + 1 < 10 := by omega
      have hne2 : rest2 ≠ [] := by
        intro hnil; subst hnil; simp at hmore
      wp_steps 2
      wp_if htb
      · have hb : b &&& 0x80#8 ≠ 0#8 := sbfm8_bit31_nz htb
        have hdeser' : Message.deserialize P_poly call.epoch call.fromBytes =
            deserAfterVarint P_poly call.epoch tag (decodeVarintLoop (pre₁ ++ [b]).length out' rest2) := by
          rw [hdeser, hlen_pre1', decodeVarintLoop_cont_step pre₁.length out b rest2 hj1 hb]
        exact ih (pre₁ ++ [b]) out' _ _ hne2 (by rw [hlen_pre1']; exact hj1) hsplit' hdeser'
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
          (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [out', arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by rw [hlen_pre1']; simp [hx12, arm64_norm])
          (by simp [hx13, arm64_norm]) (by simp [hx29, arm64_norm])
          ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
           by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩ rfl
      · have hb : b &&& 0x80#8 = 0#8 := sbfm8_bit31_z htb
        $tail_step
        have herr_case : b &&& 0x80#8 ≠ 0#8 →
            Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode :=
          fun h => absurd hb h
        have hok_case : b &&& 0x80#8 = 0#8 →
            Message.deserialize P_poly call.epoch call.fromBytes =
              deserAfterVarint P_poly call.epoch tag (some (out', rest2)) := by
          intro _; rw [hdeser, decodeVarintLoop_stop pre₁.length out b rest2 hb]
        exact h520 _ _ R post hpost htag hsplit' hlen_lt herr_case hok_case
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
          (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
          (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
          (by simp [out', arm64_norm]) (by simp [arm64_norm])
          (by simp [sbfm8Val, arm64_norm]) (by simp [hx29, arm64_norm])
          ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
           by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩ rfl
))

set_option maxHeartbeats 1600000 in
theorem step_varint_loop_3 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmt 100#64 P_poly base hooks A call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop 100 44 (wp_steps 1)

set_option maxHeartbeats 1600000 in
theorem step_varint_loop_1 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmt 232#64 P_poly base hooks A call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop 232 44 (wp_steps 1)

set_option maxHeartbeats 1600000 in
theorem step_varint_loop_5 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmt 320#64 P_poly base hooks A call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop 320 44 (wp_steps 1)

set_option maxHeartbeats 1600000 in
theorem step_varint_loop_2 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmt 400#64 P_poly base hooks A call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop 400 44 (wp_steps 1)

set_option linter.unusedTactic false in
set_option maxHeartbeats 1600000 in
theorem step_varint_loop_6 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 : State) (R : SepProp) (post : State → SepProp → Prop) :
    VarintLoopStmt 480#64 P_poly base hooks A call tag
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post := by
  prove_varint_loop 480 40 (skip)

abbrev VarintPreStmt (preOff : BitVec 64)
    (P_poly : PolyApi) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) : Prop :=
  (post = fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) →
  (tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨ tag = 5#8 ∨ tag = 6#8) →
  call.fromBytes = tag :: rest →
  call.fromBytes.length < 2 ^ 63 →
  Message.deserialize P_poly call.epoch call.fromBytes =
    deserAfterVarint P_poly call.epoch tag (decodeVarintLoop 0 0#64 rest) →
  s.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName + preOff →
  s.status = .Running →
  s.sp = s0.sp - 144#64 →
  s0.spAligned = true →
  s.trace = s0.trace →
  s.readReg64 .x0 = call.out →
  s.readReg64 .x1 = call.epoch →
  s.readReg64 .x2 = call.fromPtr →
  s.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length →
  s.readReg64 .x8 = tag.zeroExtend 64 →
  s.readReg64 .fp = s0.sp - 48#64 →
  DeserHighCalleeSaved s0 s →
  P =
    (call.fromPtr ↦ₛ call.fromBytes) ∗
    rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
    A.pool ∗
    msgDeserFramePad s0.sp ∗
    msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
    msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) →
  SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post

set_option hygiene false in
macro "prove_varint_pre" off:num loop_thm:ident : tactic => `(tactic| (
  intro hpost htag hsplit0 hlen_lt hdeser0 hpc hrun hsp hs0A htr hx0 hx1 hx2 hx3 hx8 hx29 hcs hP
  have hfn : libsignalSessionCode.fnOff messageDeserializeName = 0x5a03c := msgDeserialize_fnOff
  have herr_tail := step_err_tail P_poly base hooks A call o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0
  have hloop := $loop_thm P_poly hPoly base hooks A call tag
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 R post hpost htag hlen_lt hs0A
  code_fetches_range libsignalSessionCode libsignalSessionBin base hooks hfn 0x5a03c $off 36
  clear hfn
  have hlen_lt' : (tag :: rest).length < 2 ^ 63 := by rwa [← hsplit0]
  have hcsel := varint_pre_csel_eq hlen_lt'
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  dsimp only [messageDeserializeName] at hpc herr_tail hloop ⊢
  generalize_entry (libsignalSessionCode.rebase base hooks).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  wp_steps 2
  wp_if heq
  · have hnil : rest = [] := varint_pre_eq_zero hlen_lt' heq
    have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
      rw [hdeser0, hnil]; rfl
    exact herr_tail _ P R post hpost herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm]) hs0A
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩ hP
  · have hne : rest ≠ [] := varint_pre_ne_zero heq
    clear heq herr_tail
    wp_steps 7
    exact hloop rest [] 0#64 _ P hne (by decide) (by simp [hsplit0]) (by simpa using hdeser0)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
      (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx1, arm64_norm])
      (by simp [hx2, arm64_norm]) (by simp [hx3, arm64_norm]) (by simp [hx8, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [hcsel, arm64_norm]) (by simp [hx2, arm64_norm]) (by simp [hx29, arm64_norm])
      ⟨by simp [hx23, arm64_norm], by simp [hx24, arm64_norm], by simp [hx25, arm64_norm],
       by simp [hx26, arm64_norm], by simp [hx27, arm64_norm], by simp [hx28, arm64_norm], by simp [hvregs, arm64_norm]⟩ hP
))

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_3 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmt 64#64 P_poly base hooks A call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre 64 step_varint_loop_3

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_1 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmt 196#64 P_poly base hooks A call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre 196 step_varint_loop_1

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_5 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmt 284#64 P_poly base hooks A call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre 284 step_varint_loop_5

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_2 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmt 364#64 P_poly base hooks A call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre 364 step_varint_loop_2

set_option maxHeartbeats 1600000 in
theorem step_varint_pre_6 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop) :
    VarintPreStmt 444#64 P_poly base hooks A call tag rest
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
      f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 s0 s P R post := by
  prove_varint_pre 444 step_varint_loop_6

/-- Empty-slice (`from.is_empty()`, `+0: cbz x3, +144`) error return (`0x5f4c4..0x5f4d4`,
    `+144..+160`, 5 insns). -/
theorem step_err_empty (P_poly : PolyApi) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode)
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hcs : CalleeSavedPreserved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      stackAt s0.sp messageDeserializeStackX) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  have hfn : libsignalSessionCode.fnOff messageDeserializeName = 0x5a03c := msgDeserialize_fnOff
  code_fetches_range libsignalSessionCode libsignalSessionBin base hooks hfn 0x5a03c 144 20
  clear hfn
  rcases hcs with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, hvregs⟩
  subst hP hpost
  dsimp only [messageDeserializeName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase base hooks).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  refine SepWP.fold (rawOutBufAt_entails_err_split call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a)
    (by sep_focus) ?_
  wp_steps
  dsimp only [messageDeserializeSpecX]
  rw [herr]
  dsimp only [messageResultAt]
  refine SepWP.fold (fold_messageErrorAt_region call.out) (by sep_focus) ?_
  wp_done

end CryptoVerification.SpqrV1.Top.MessageDeserialize

