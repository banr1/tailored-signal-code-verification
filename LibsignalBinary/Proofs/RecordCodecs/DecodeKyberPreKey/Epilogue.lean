/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Layout
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymD
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Fetches
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `decode_kyber_pre_key` `Ok` and `Err` Epilogue Proofs

Verifies the post-call `Ok` (`+0x01c..+0x05c`) and `Err` (`+0x01c..+0x024`, `+0x060..+0x080`)
branches of `signal_session::stores::decode_kyber_pre_key`, plus relocatable `[LibsignalPlacement]`
variants on Block `595`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

attribute [local irreducible] Program.fetch Program.externAt?

def kpkPost (img : Obj.Image) (A : RustAlloc) (x : DecodeGhost) (s0 : State) :
    State → SepProp → Prop :=
  fun sf Pf =>
    sf.sp = s0.sp ∧
    (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
    (Pf ⊢ (decodeKyberPreKeySpec A img).post x s0 sf)

theorem kpkSpAligned_sub128 {s0 : State} (hsp0 : s0.spAligned = true) :
    ((s0.sp - 128#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned] at hsp0
  revert hsp0
  generalize s0.sp = sp
  intro hsp0
  bv_kernel

/-- `Ok` branch (`+0x01c..+0x05c`): reads word 0 (`pubCap < 2^63`, so `cmn x20, #1` is false),
copies all 88 bytes of `signedPreKeyStructAt A (sp' + 8) m` to `x.ret`, restores the frame and
callee-saved registers, and returns to `s0.readReg64 .x30`. -/
theorem epilogue_ok_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : DecodeGhost} {s0 s : State} {m : SignedPreKeyRecordStructure}
    (hdec : SignedPreKeyRecordStructure.decode x.bytes = some m)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + bv% (28))
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 128#64)
    (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hsaved : KpkSavedRegs s0 s) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (signedPreKeyStructAt A (s0.sp - 128#64 + 8#64) m ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 128#64 + 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 128#64 + 104#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 128#64 + 112#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 128#64 + 120#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        stackAt (s0.sp - 128#64) signedDecodeStack ∗
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ∗
        A.pool)
      (kpkPost img A x s0)
      (tryFromQp s0) := by
  set sp' := s0.sp - 128#64
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (signedPreKeyStructAt_sp8_unpack A sp' m)
      (sepConj_mono_left (memRegion88_unpack x.ret))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
    Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 =>
    Wire.SepWPp.exists_pre fun r6 => Wire.SepWPp.exists_pre fun r7 =>
    Wire.SepWPp.exists_pre fun r8 => Wire.SepWPp.exists_pre fun r9 =>
    Wire.SepWPp.exists_pre fun r10 =>
    Wire.SepWPp.exists_pre fun pubCap => Wire.SepWPp.exists_pre fun pubPtr =>
    Wire.SepWPp.exists_pre fun privCap => Wire.SepWPp.exists_pre fun privPtr =>
    Wire.SepWPp.exists_pre fun sigCap => Wire.SepWPp.exists_pre fun sigPtr =>
    Wire.SepWPp.exists_pre fun pad32 => ?_
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hpub_lt => ?_
  have hc := cap_add1_eq_of_lt hpub_lt
  unfold words88Sp words88Ret
  simp only [sepConj_assoc]
  code_fetches_from CryptoVerification.libsignalSessionCode kpkDec
    img.base (Rust.withPanics ext) kpkDec_fnOff kpkDecOff 28 68
  dsimp only [tripleRatchetProgAtExt, decodeKyberPreKeyName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "libsignal_cli::stores::decode_kyber_pre_key" = entry
  examples_hide_fetches
  have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
  refine Wire.SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _ _
  have hsp_ret : s0.sp - 128#64 + 128#64 = s0.sp := by bv_omega
  refine ⟨by simp [sp', hsp_ret, arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm],
      by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x21,
      by simpa [arm64_norm] using hsaved.x22,
      by simpa [arm64_norm] using hsaved.x23,
      by simpa [arm64_norm] using hsaved.x24,
      by simpa [arm64_norm] using hsaved.x25,
      by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27,
      by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm],
      hv⟩
  · dsimp only [decodeKyberPreKeySpec, Spec.inImage]
    rw [kyberDeserialize_of_some hdec, pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hpack := okExit_pack A s0.sp x.ret x.bytesA x.bytes
      pubCap pubPtr privCap privPtr sigCap sigPtr
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19)
      pad32 m
    refine Entails.trans ?_ hpack
    unfold words88Sp words88Ret
    simp only [sp', arm64_norm]
    apply entails_of_eq; ac_rfl

/-- `Err` branch (`+0x01c..+0x024`, `+0x060..+0x080`): reads `errTag` at `sp' + 8`, branches to
`+0x060`, drops `decodeErrorAt A e` via `dropDecodeError3`, writes `(errTag, speWord 2)` at `x.ret`,
restores the frame and callee-saved registers, and returns to `s0.readReg64 .x30`. -/
theorem epilogue_err_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name)
      (Prost.dropDecodeErrorSpec A))
    {x : DecodeGhost} {s0 s : State} {e : BitVec 64}
    (hdec : SignedPreKeyRecordStructure.decode x.bytes = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + bv% (28))
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 128#64)
    (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hsaved : KpkSavedRegs s0 s) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (((s0.sp - 128#64 + 8#64) ↦₆₄ errTag) ∗
        ((s0.sp - 128#64 + 16#64) ↦₆₄ e) ∗
        decodeErrorAt A e ∗
        memRegion (s0.sp - 128#64 + 24#64) 72 ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 128#64 + 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 128#64 + 104#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 128#64 + 112#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 128#64 + 120#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        stackAt (s0.sp - 128#64) signedDecodeStack ∗
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ∗
        A.pool)
      (kpkPost img A x s0)
      (tryFromQp s0) := by
  set sp' := s0.sp - 128#64
  have hcall := dropDecodeError3_call_ok hDrop
  clear hDrop
  have hstack := kpkDecodeStack_drop_split sp'
  let retDropOff : BitVec 64 := bv% (104)
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion88_err_unpack x.ret)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 => ?_
  code_fetches_from CryptoVerification.libsignalSessionCode kpkDec
    img.base (Rust.withPanics ext) kpkDec_fnOff kpkDecOff 28 12
  code_fetches_from CryptoVerification.libsignalSessionCode kpkDec
    img.base (Rust.withPanics ext) kpkDec_fnOff kpkDecOff 96 36
  dsimp only [tripleRatchetProgAtExt, decodeKyberPreKeyName] at hcall hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "libsignal_cli::stores::decode_kyber_pre_key" = entry
  examples_hide_fetches
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + dropDecodeError3RelOff) ?_
  wp_steps
  refine Wire.SepWP.done (by dsimp only [dropDecodeError3RelOff]; simp [arm64_norm])
    (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_noPanic_tryFrom e hcall
    (by dsimp only [dropDecodeError3RelOff]; simp [arm64_norm])
    (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + retDropOff) (by dsimp only [retDropOff]; simp [arm64_norm])
    (T := decodeErrorAt A e ∗ A.pool ∗ stackAt sp' dropDecodeErrorStack)
    (φ := e = e)
    (by simp [dropDecodeErrorSpec, sp', hsp_eq, arm64_norm])
    rfl
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [dropDecodeErrorSpec]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [sp', hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
  have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = errTag := by simpa [arm64_norm] using hcs2.2.1
  have hsaved2 : KpkSavedRegs s0 s2 := KpkSavedRegs.of_calleeSaved
    ⟨by simpa [arm64_norm] using hsaved.x21,
     by simpa [arm64_norm] using hsaved.x22,
     by simpa [arm64_norm] using hsaved.x23,
     by simpa [arm64_norm] using hsaved.x24,
     by simpa [arm64_norm] using hsaved.x25,
     by simpa [arm64_norm] using hsaved.x26,
     by simpa [arm64_norm] using hsaved.x27,
     by simpa [arm64_norm] using hsaved.x28⟩ hcs2
  dsimp only [retDropOff] at hpc2
  refine Wire.SepWPp.of_sepWP_end hF2 hsym2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro _ _
  have hsp_ret : s0.sp - 128#64 + 128#64 = s0.sp := by bv_omega
  refine ⟨by simp [sp', hsp_ret, arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm],
      by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved2.x21,
      by simpa [arm64_norm] using hsaved2.x22,
      by simpa [arm64_norm] using hsaved2.x23,
      by simpa [arm64_norm] using hsaved2.x24,
      by simpa [arm64_norm] using hsaved2.x25,
      by simpa [arm64_norm] using hsaved2.x26,
      by simpa [arm64_norm] using hsaved2.x27,
      by simpa [arm64_norm] using hsaved2.x28,
      by simp [arm64_norm],
      hv⟩
  · dsimp only [decodeKyberPreKeySpec, Spec.inImage]
    rw [kyberDeserialize_of_none hdec, pure_true_emp (by simp [htr2, htr, arm64_norm]), emp_sepConj]
    have hpack := errExit_pack A s0.sp x.ret x.bytesA e
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19) x.bytes
    refine Entails.trans ?_ hpack
    simp only [sp', hstack, hsp_eq, arm64_norm]
    apply entails_of_eq; ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Epilogue Proofs (Block `595`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

@[arm64_norm] def kpkOff_retDec : BitVec 64 := 28#64
@[arm64_norm] def kpkOff_retDrop : BitVec 64 := 104#64

def kpkPostPlaced (A : RustAlloc) (x : DecodeGhost) (s0 : State) :
    State → SepProp → Prop :=
  fun sf Pf =>
    sf.sp = s0.sp ∧
    (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
    (Pf ⊢ (decodeKyberPreKeyRawSpec A).post x s0 sf)

/-- Relocatable `Ok` branch (`+0x01c..+0x05c`) in block `595`. -/
theorem epilogue_ok_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : DecodeGhost} {s0 s : State} {m : SignedPreKeyRecordStructure}
    (hdec : SignedPreKeyRecordStructure.decode x.bytes = some m)
    (hpc : s.pc = (blkPl_595).base + kpkOff_retDec)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 128#64)
    (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hsaved : KpkSavedRegs s0 s) :
    Wire.SepWPp (lsProg_595 H)
      (s0.readReg64 .x30) s
      (signedPreKeyStructAt A (s0.sp - 128#64 + 8#64) m ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 128#64 + 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 128#64 + 104#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 128#64 + 112#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 128#64 + 120#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        stackAt (s0.sp - 128#64) signedDecodeStack ∗
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ∗
        A.pool)
      (kpkPostPlaced A x s0)
      (tryFromQp s0) := by
  let _ := hsp
  set sp' := s0.sp - 128#64
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (signedPreKeyStructAt_sp8_unpack A sp' m)
      (sepConj_mono_left (memRegion88_unpack x.ret))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
    Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 =>
    Wire.SepWPp.exists_pre fun r6 => Wire.SepWPp.exists_pre fun r7 =>
    Wire.SepWPp.exists_pre fun r8 => Wire.SepWPp.exists_pre fun r9 =>
    Wire.SepWPp.exists_pre fun r10 =>
    Wire.SepWPp.exists_pre fun pubCap => Wire.SepWPp.exists_pre fun pubPtr =>
    Wire.SepWPp.exists_pre fun privCap => Wire.SepWPp.exists_pre fun privPtr =>
    Wire.SepWPp.exists_pre fun sigCap => Wire.SepWPp.exists_pre fun sigPtr =>
    Wire.SepWPp.exists_pre fun pad32 => ?_
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hpub_lt => ?_
  have hc := cap_add1_eq_of_lt hpub_lt
  unfold words88Sp words88Ret
  simp only [sepConj_assoc]
  have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
  refine sepWPp_of_sepWP_end_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _
  have hsp_ret : s0.sp - 128#64 + 128#64 = s0.sp := by bv_omega
  refine ⟨by simp [sp', hsp_ret, arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm],
      by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x21,
      by simpa [arm64_norm] using hsaved.x22,
      by simpa [arm64_norm] using hsaved.x23,
      by simpa [arm64_norm] using hsaved.x24,
      by simpa [arm64_norm] using hsaved.x25,
      by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27,
      by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm],
      hv⟩
  · dsimp only [decodeKyberPreKeyRawSpec]
    rw [kyberDeserialize_of_some hdec, pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hpack := okExit_pack A s0.sp x.ret x.bytesA x.bytes
      pubCap pubPtr privCap privPtr sigCap sigPtr
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19)
      pad32 m
    refine Entails.trans ?_ hpack
    unfold words88Sp words88Ret
    simp only [sp', arm64_norm]
    apply entails_of_eq; ac_rfl

/-- Relocatable `Err` branch (`+0x01c..+0x024`, `+0x060..+0x080`) in block `595`. -/
theorem epilogue_err_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hDrop : subroutine_ok (lsProg_551 H) (blkPl_551).base (Prost.dropDecodeErrorSpec A))
    {x : DecodeGhost} {s0 s : State} {e : BitVec 64}
    (hdec : SignedPreKeyRecordStructure.decode x.bytes = none)
    (hpc : s.pc = (blkPl_595).base + kpkOff_retDec)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 128#64)
    (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hsaved : KpkSavedRegs s0 s) :
    Wire.SepWPp (lsProg_595 H)
      (s0.readReg64 .x30) s
      (((s0.sp - 128#64 + 8#64) ↦₆₄ errTag) ∗
        ((s0.sp - 128#64 + 16#64) ↦₆₄ e) ∗
        decodeErrorAt A e ∗
        memRegion (s0.sp - 128#64 + 24#64) 72 ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 128#64 + 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 128#64 + 104#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 128#64 + 112#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 128#64 + 120#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        stackAt (s0.sp - 128#64) signedDecodeStack ∗
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ∗
        A.pool)
      (kpkPostPlaced A x s0)
      (tryFromQp s0) := by
  set sp' := s0.sp - 128#64
  have hcall := dropDecodeError3_placed_call_ok hDrop
  clear hDrop
  have hstack := kpkDecodeStack_drop_split sp'
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion88_err_unpack x.ret)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 => ?_
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_551).base) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]; rfl) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine sepWPp_call_noPanic_lscro e hcall
    (by simp [arm64_norm]; rfl)
    (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_595).base + kpkOff_retDrop) (by simp [arm64_norm])
    (T := decodeErrorAt A e ∗ A.pool ∗ stackAt sp' dropDecodeErrorStack)
    (φ := e = e)
    (by simp [dropDecodeErrorSpec, sp', hsp_eq, arm64_norm])
    rfl
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [dropDecodeErrorSpec]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [sp', hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
  have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = errTag := by simpa [arm64_norm] using hcs2.2.1
  have hsaved2 : KpkSavedRegs s0 s2 := KpkSavedRegs.of_calleeSaved
    ⟨by simpa [arm64_norm] using hsaved.x21,
     by simpa [arm64_norm] using hsaved.x22,
     by simpa [arm64_norm] using hsaved.x23,
     by simpa [arm64_norm] using hsaved.x24,
     by simpa [arm64_norm] using hsaved.x25,
     by simpa [arm64_norm] using hsaved.x26,
     by simpa [arm64_norm] using hsaved.x27,
     by simpa [arm64_norm] using hsaved.x28⟩ hcs2
  refine sepWPp_of_sepWP_end_lscro hcrl2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro _
  have hsp_ret : s0.sp - 128#64 + 128#64 = s0.sp := by bv_omega
  refine ⟨by simp [sp', hsp_ret, arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm],
      by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved2.x21,
      by simpa [arm64_norm] using hsaved2.x22,
      by simpa [arm64_norm] using hsaved2.x23,
      by simpa [arm64_norm] using hsaved2.x24,
      by simpa [arm64_norm] using hsaved2.x25,
      by simpa [arm64_norm] using hsaved2.x26,
      by simpa [arm64_norm] using hsaved2.x27,
      by simpa [arm64_norm] using hsaved2.x28,
      by simp [arm64_norm],
      hv⟩
  · dsimp only [decodeKyberPreKeyRawSpec]
    rw [kyberDeserialize_of_none hdec, pure_true_emp (by simp [htr2, htr, arm64_norm]), emp_sepConj]
    have hpack := errExit_pack A s0.sp x.ret x.bytesA e
      (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19) x.bytes
    refine Entails.trans ?_ hpack
    simp only [sp', hstack, hsp_eq, arm64_norm]
    apply entails_of_eq; ac_rfl

end Placed

end CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers
