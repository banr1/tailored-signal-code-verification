/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.HookTrace
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym -- shake: keep

/-!
# Shared Definitions & Helpers for Back Segments (`S7`–`S9`) of `try_decrypt_with_state`

Instruction fetch tactics, callee/stub resolution lemmas, and `SepWPp` / `onPanic` bridges shared
across `VerifyMac`, `AesDecrypt`, and `ApplyRatchet`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection
open CryptoVerification.HookTrace

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

@[simp, wp_norm] theorem calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    calleeSavedVRegs (s.writeReg32 r v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setPC (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setPState (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_0 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_1 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 1#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_2 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 2#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_3 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 3#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_4 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 4#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_5 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 5#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_6 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 6#5 v) = calleeSavedVRegs s := rfl
@[simp, wp_norm] theorem calleeSavedVRegs_writeVReg128_7 (s : State) (v : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 7#5 v) = calleeSavedVRegs s := rfl

namespace AuthDecryptFacts

theorem spAligned_of_sp_eq {s1 s2 : State} (heq : s2.sp = s1.sp) (hal : s1.spAligned = true) :
    s2.spAligned = true := by
  unfold State.spAligned at hal ⊢
  rw [heq]
  exact hal

end AuthDecryptFacts

open Lean Elab Tactic in
/-- `code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-- Fetch hypotheses for `try_decrypt_with_state::<HookRng>` (`hfn : fnOff tryDecryptName = 0x3439c`),
    from fn-relative offset `k0`, `len` bytes. -/
macro "decrypt_fetches " b:term:max C:term:max ctl:term:max abs:term:max
    hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode libsignalTripleRatchetBin $b
    (Rust.withPanics (tripleRatchetExterns $C $ctl $abs)) $hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) $k0 $len)

/-- Fetch hypotheses for `try_decrypt_with_state::<HookRng>` on `tripleRatchetProgAtExt b ext`. -/
macro "decrypt_fetches_ext " b:term:max ext:term:max
    hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode libsignalTripleRatchetBin $b
    (Rust.withPanics $ext) $hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) $k0 $len)

theorem hfn_tryDecrypt : libsignalSessionCode.fnOff tryDecryptName = num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") :=
  (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")

/-! ## 1. Entry / PC Rewriting and Callee / Hook Wrappers -/

theorem tryDecryptEntry_eq_fnAddr_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName :=
  entryOf_eq_tripleRatchetProgAtExt ext himg tryDecryptName

theorem tryDecryptEntry_eq_fnAddr {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    tryDecryptEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName :=
  entryOf_eq_tripleRatchetProgAt himg tryDecryptName

theorem segS7PC_eq_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    segVerifyMacPC img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 0x63c := by
  rw [segVerifyMacPC, tryDecryptEntry_eq_fnAddr_ext himg]

theorem segS7PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    segVerifyMacPC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 0x63c := by
  rw [segVerifyMacPC, tryDecryptEntry_eq_fnAddr himg]

theorem segS8PC_eq_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    segAesDecryptPC img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 0x678 := by
  rw [segAesDecryptPC, tryDecryptEntry_eq_fnAddr_ext himg]

theorem segS8PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    segAesDecryptPC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 0x678 := by
  rw [segAesDecryptPC, tryDecryptEntry_eq_fnAddr himg]

theorem segS9PC_eq_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    segApplyRatchetPC img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 0x6a4 := by
  rw [segApplyRatchetPC, tryDecryptEntry_eq_fnAddr_ext himg]

theorem segS9PC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    segApplyRatchetPC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 0x6a4 := by
  rw [segApplyRatchetPC, tryDecryptEntry_eq_fnAddr himg]

theorem errTailPC_eq_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    errTailPC img = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 0x30c := by
  rw [errTailPC, tryDecryptEntry_eq_fnAddr_ext himg]

theorem errTailPC_eq {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    errTailPC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 0x30c := by
  rw [errTailPC, tryDecryptEntry_eq_fnAddr himg]

theorem bl_verifyMac_target_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"), (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")]
  bv_omega

theorem bl_verifyMac_target (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr verifyMacWithAddressesName :=
  bl_verifyMac_target_ext img (tripleRatchetExterns C ctl abs)

theorem bl_trApply_target_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr trApplyName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"), (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state")]
  bv_omega

theorem bl_trApply_target (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr trApplyName :=
  bl_trApply_target_ext img (tripleRatchetExterns C ctl abs)

theorem bl_clearUpk_target_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr clearUpkName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"), (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message")]
  bv_omega

theorem bl_clearUpk_target (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr clearUpkName :=
  bl_clearUpk_target_ext img (tripleRatchetExterns C ctl abs)

theorem sessionShim_hookOk : HookOk hookNoop sessionShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [sessionShimSpec, hookNoop, retHook, id_eq, State.trace_setPC,
    satisfies_pure_sepConj, true_and, emp_sepConj] at hpre ⊢
  exact hpre

theorem sessionMemcpyRegion_hookOk : HookOk hookMemcpy sessionMemcpyRegionSpec := by
  refine HookOk.of_trace hookMemcpy_region_ok fun _ _ _ ht hpost => ?_
  simp only [memcpyRegionSpec, sessionMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

theorem shim_ok_at_ext (img : Obj.Image) {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      sessionShimSpec :=
  hC.shim_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem shim_ok_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      sessionShimSpec :=
  hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") (by decide) (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, sessionShim_hookOk⟩

theorem memcpy_ok_at_ext (img : Obj.Image) {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      sessionMemcpyRegionSpec :=
  hC.session_memcpy_region_ok_at tryDecryptName (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem memcpy_ok_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      sessionMemcpyRegionSpec :=
  hook_ok_at (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") (by decide) (by decide)
    (ls_hook% "memcpy") (by simp [Rust.isPanicSymbol])
    ⟨hookMemcpy, rfl, sessionMemcpyRegion_hookOk⟩

theorem alloc_ok_at_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      (rustAllocSpec A) :=
  hC.alloc_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem alloc_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      (rustAllocSpec A) :=
  alloc_ok_at_ext img C A ctl S _ (Stage2Contracts.of_tripleRatchetProgAt' hS)

theorem dealloc_ok_at_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      (rustDeallocSpec A) :=
  hC.dealloc_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem dealloc_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      (rustDeallocSpec A) :=
  dealloc_ok_at_ext img C A ctl S _ (Stage2Contracts.of_tripleRatchetProgAt' hS)

theorem formatInner_ok_at_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      (formatInnerSpec A) :=
  hC.format_inner_ok_at tryDecryptName (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem formatInner_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      (formatInnerSpec A) :=
  formatInner_ok_at_ext img C A ctl S _ (Stage2Contracts.of_tripleRatchetProgAt' hS)

theorem aesDec_ok_at_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      (aesDecSpec C.D A) :=
  hC.aes_dec_ok_at tryDecryptName (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem aesDec_ok_at (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      (aesDecSpec C.D A) :=
  aesDec_ok_at_ext img C A ctl S _ (Stage2Contracts.of_tripleRatchetProgAt' hS)

theorem externAt_handle_error_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))) =
      some Rust.panicked :=
  panic_at_handle_error_ext img.base ext tryDecryptName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem externAt_handle_error (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).externAt?
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))) =
      some Rust.panicked :=
  externAt_handle_error_ext img (tripleRatchetExterns C ctl abs)

/-! ## 2. `SepWPp` Segment, Representation & Panic Bridge Lemmas -/

theorem sepWPp_to_reaches_outcome {α : Type} {prog : Program} {spec : Spec α}
    {x : α} {P R : SepProp} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp prog (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    reaches_outcome prog spec x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ := hwp R hm hL
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hq hmf⟩))
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hqp hmf⟩)))
  · exact (not_satisfies_false_sepConj hoom).elim

theorem allocFailedIn_trans {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace) (hmf : allocFailedIn sm sf) :
    allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := h0m
  unfold allocFailedIn at hmf ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at hmf
  exact List.mem_of_mem_drop hmf

theorem tryDecrypt_onPanic_of_callee (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold tryDecryptSpec Spec.inImage
  exact allowPanic_frame
    (fun ⟨haf, hmf⟩ => ⟨Or.inr (Or.inr (allocFailedIn_trans h0m haf)), h0m.trans hmf⟩) hm

theorem tryDecrypt_onPanic_of_direct (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sf : State) (P R : SepProp)
    (haf : allocFailedIn s0 sf) (htr : s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold tryDecryptSpec Spec.inImage
  exact allowPanic_panicked ⟨Or.inr (Or.inr haf), htr⟩ hm

theorem SepWPp.panic_at {prog : Program} {ret panic_pc : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : prog.externAt? panic_pc = some Rust.panicked)
    (hqp : Qp (Rust.panicked s) P) : SepWPp prog ret s P Q Qp := by
  rw [← hpc] at hext
  exact SepWPp.panic hrun hext hqp

theorem SepWPp.panic_direct_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (ext : String → Option (State → State))
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : (tripleRatchetProgAtExt img.base ext).externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  refine SepWPp.panic_at hpc hrun hext fun _ hm_pan => ?_
  have htr_f : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent] := htr
  have haf : allocFailedIn s0 (Rust.panicked s) := by
    unfold allocFailedIn
    rw [htr_f, List.drop_left]
    exact List.Mem.head _
  have hpre : s0.trace <+: (Rust.panicked s).trace := by
    rw [htr_f]
    exact ⟨[allocFailedEvent], rfl⟩
  exact tryDecrypt_onPanic_of_direct C A ctl S img x s0 (Rust.panicked s) P R haf hpre hm_pan

theorem SepWPp.panic_direct (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (abs : String → Option (State → State))
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : (tripleRatchetProgAt img.base C ctl abs).externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt img.base C ctl abs) ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) :=
  SepWPp.panic_direct_ext C A ctl S img (tripleRatchetExterns C ctl abs)
    x s0 s ret panic_pc P R hpc hrun hext htr

def boxU8Rest (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜p ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗ (if bs = [] then emp else A.live p bs.length 1)

theorem boxU8At_eq_rest (A : RustAlloc) (b p : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A b p bs =
      ((b ↦₆₄ p) ∗ ((b + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
       (p ↦ₛ bs) ∗ boxU8Rest A p bs) := by
  unfold boxU8At boxU8Rest
  by_cases h : bs = []
  · subst h
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, pointsToBytes_nil, sepConj_emp]
    ac_rfl
  · simp only [h, ↓reduceIte]
    ac_rfl

theorem bytesToKey32_keyToBytes32 (k : BitVec 256) : bytesToKey32 (keyToBytes32 k) = k := by
  change bytesToKey32
    [k.extractLsb' 0 8, k.extractLsb' 8 8, k.extractLsb' 16 8, k.extractLsb' 24 8,
     k.extractLsb' 32 8, k.extractLsb' 40 8, k.extractLsb' 48 8, k.extractLsb' 56 8,
     k.extractLsb' 64 8, k.extractLsb' 72 8, k.extractLsb' 80 8, k.extractLsb' 88 8,
     k.extractLsb' 96 8, k.extractLsb' 104 8, k.extractLsb' 112 8, k.extractLsb' 120 8,
     k.extractLsb' 128 8, k.extractLsb' 136 8, k.extractLsb' 144 8, k.extractLsb' 152 8,
     k.extractLsb' 160 8, k.extractLsb' 168 8, k.extractLsb' 176 8, k.extractLsb' 184 8,
     k.extractLsb' 192 8, k.extractLsb' 200 8, k.extractLsb' 208 8, k.extractLsb' 216 8,
     k.extractLsb' 224 8, k.extractLsb' 232 8, k.extractLsb' 240 8, k.extractLsb' 248 8] = k
  have h0 (x : BitVec 8) : ((0 : BitVec 256) <<< 8) ||| x.setWidth 256 = x.setWidth 256 := by simp
  have hs {w : Nat} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 256) <<< 8) ||| y.setWidth 256 = (x ++ y).setWidth 256 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  have hext (s₂ s₁ n₂ n₁ : Nat) (h : s₂ = s₁ + n₁) :
      k.extractLsb' s₂ n₂ ++ k.extractLsb' s₁ n₁ = k.extractLsb' s₁ (n₂ + n₁) := by
    subst h
    ext i hi
    simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
    split
    · rfl
    · congr 1; omega
  dsimp only [bytesToKey32, List.foldr, BitVec.zeroExtend]
  rw [h0]
  repeat rw [hs]
  rw [BitVec.setWidth_eq]
  rw [hext 248 240 _ 8 rfl, hext 240 232 _ 8 rfl, hext 232 224 _ 8 rfl, hext 224 216 _ 8 rfl,
      hext 216 208 _ 8 rfl, hext 208 200 _ 8 rfl, hext 200 192 _ 8 rfl, hext 192 184 _ 8 rfl,
      hext 184 176 _ 8 rfl, hext 176 168 _ 8 rfl, hext 168 160 _ 8 rfl, hext 160 152 _ 8 rfl,
      hext 152 144 _ 8 rfl, hext 144 136 _ 8 rfl, hext 136 128 _ 8 rfl, hext 128 120 _ 8 rfl,
      hext 120 112 _ 8 rfl, hext 112 104 _ 8 rfl, hext 104 96 _ 8 rfl, hext 96 88 _ 8 rfl,
      hext 88 80 _ 8 rfl, hext 80 72 _ 8 rfl, hext 72 64 _ 8 rfl, hext 64 56 _ 8 rfl,
      hext 56 48 _ 8 rfl, hext 48 40 _ 8 rfl, hext 40 32 _ 8 rfl, hext 32 24 _ 8 rfl,
      hext 24 16 _ 8 rfl, hext 16 8 _ 8 rfl, hext 8 0 _ 8 rfl]
  ext i hi; simp

theorem bytesToBlock_blockToBytesLE (iv : CBC.Block) :
    CBC.bytesToBlock (CBC.blockToBytesLE iv) = iv := by
  change CBC.bytesToBlock
    [iv.extractLsb' 0 8, iv.extractLsb' 8 8, iv.extractLsb' 16 8, iv.extractLsb' 24 8,
     iv.extractLsb' 32 8, iv.extractLsb' 40 8, iv.extractLsb' 48 8, iv.extractLsb' 56 8,
     iv.extractLsb' 64 8, iv.extractLsb' 72 8, iv.extractLsb' 80 8, iv.extractLsb' 88 8,
     iv.extractLsb' 96 8, iv.extractLsb' 104 8, iv.extractLsb' 112 8, iv.extractLsb' 120 8] = iv
  have h0 (x : BitVec 8) : ((0 : BitVec 128) <<< 8) ||| x.setWidth 128 = x.setWidth 128 := by simp
  have hs {w : Nat} (x : BitVec w) (y : BitVec 8) :
      ((x.setWidth 128) <<< 8) ||| y.setWidth 128 = (x ++ y).setWidth 128 := by
    ext i hi
    simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_append]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge y i (by omega)]
  have hext (s₂ s₁ n₂ n₁ : Nat) (h : s₂ = s₁ + n₁) :
      iv.extractLsb' s₂ n₂ ++ iv.extractLsb' s₁ n₁ = iv.extractLsb' s₁ (n₂ + n₁) := by
    subst h
    ext i hi
    simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
    split
    · rfl
    · congr 1; omega
  dsimp only [CBC.bytesToBlock, List.foldr, BitVec.zeroExtend]
  rw [h0]
  repeat rw [hs]
  rw [BitVec.setWidth_eq]
  rw [hext 120 112 _ 8 rfl, hext 112 104 _ 8 rfl, hext 104 96 _ 8 rfl, hext 96 88 _ 8 rfl,
      hext 88 80 _ 8 rfl, hext 80 72 _ 8 rfl, hext 72 64 _ 8 rfl, hext 64 56 _ 8 rfl,
      hext 56 48 _ 8 rfl, hext 48 40 _ 8 rfl, hext 40 32 _ 8 rfl, hext 32 24 _ 8 rfl,
      hext 24 16 _ 8 rfl, hext 16 8 _ 8 rfl, hext 8 0 _ 8 rfl]
  ext i hi; simp

theorem length_keyToBytes32 (k : BitVec 256) : (keyToBytes32 k).length = 32 := by
  simp [keyToBytes32]

theorem length_blockToBytesLE (iv : CBC.Block) : (CBC.blockToBytesLE iv).length = 16 := by
  simp [CBC.blockToBytesLE]

theorem add_one_ne_zero_of_lt_2_63 {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_omega

theorem stackAt_sub_split (sp : BitVec 64) (n : Nat) (hn : n ≤ tryDecryptSubStack) :
    stackAt sp tryDecryptSubStack =
      memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - n) ∗
      stackAt sp n := by
  have h := stackAt_split_bottom sp n (tryDecryptSubStack - n)
    (by unfold tryDecryptSubStack rootStack tryDecryptFrameSize at hn ⊢; omega)
  have hsum : n + (tryDecryptSubStack - n) = tryDecryptSubStack := Nat.add_sub_of_le hn
  rwa [hsum] at h

theorem messageKeysAt_eq (sp : BitVec 64) (mks : MessageKeys) :
    messageKeysAt (sp + 0x500#64) mks =
      (((sp + 0x500#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
       ((sp + 0x520#64) ↦ₛ keyToBytes32 mks.macKey) ∗
       ((sp + 0x540#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
       ((sp + 0x550#64) ↦₃₂ mks.counter)) := by
  unfold messageKeysAt
  have h1 : sp + 0x500#64 + 0x20#64 = sp + 0x520#64 := by bv_omega
  have h2 : sp + 0x500#64 + 0x40#64 = sp + 0x540#64 := by bv_omega
  have h3 : sp + 0x500#64 + 0x50#64 = sp + 0x550#64 := by bv_omega
  rw [h1, h2, h3]

theorem messageKeysAt_entails_memRegion (p : BitVec 64) (mks : MessageKeys) :
    messageKeysAt p mks ⊢ memRegion p 0x54 := by
  unfold messageKeysAt
  have h1 := pointsToBytes_entails_memRegion p (keyToBytes32 mks.cipherKey)
  rw [length_keyToBytes32] at h1
  have h2 := pointsToBytes_entails_memRegion (p + 0x20#64) (keyToBytes32 mks.macKey)
  rw [length_keyToBytes32] at h2
  have h3 := pointsToBytes_entails_memRegion (p + 0x40#64) (CBC.blockToBytesLE mks.iv)
  rw [length_blockToBytesLE] at h3
  have h4 := pointsTo32_entails_memRegion (p + 0x50#64) mks.counter
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 h4))) ?_
  rw [show (0x54 : Nat) = 32 + (32 + (16 + 4)) by decide,
      memRegion_split p 32 (32 + (16 + 4)) (by decide),
      memRegion_split (p + 32#64) 32 (16 + 4) (by decide),
      show p + 32#64 + 32#64 = p + 0x40#64 by bv_omega,
      memRegion_split (p + 0x40#64) 16 4 (by decide),
      show p + 0x40#64 + 16#64 = p + 0x50#64 by bv_omega]
  exact Entails.refl _

theorem newPqr_dealloc_prep (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap ≠ 0) (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
    A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  simp only [hcap, ↓reduceIte]
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)) ?_
  rw [← memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega),
      Nat.add_sub_of_le hle]
  exact Entails.refl _

theorem sepWPp_to_steps_or_panic {prog : Program} (ret : BitVec 64) {s : State}
    {P R : SepProp} {Goal : State → Prop} {OnPanic : State → SepProp}
    (hm : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hwp : SepWPp prog ret s P
      (fun sf P_f => sf.pc = ret → sf.status = .Running → (sf.mem ⊨ P_f ∗ R) → Goal sf)
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ OnPanic sf ∗ R))) :
    ∃ s', Steps prog s s' ∧
      (Goal s' ∨ (s'.status = .Panicked ∧ (s'.mem ⊨ OnPanic s' ∗ R))) := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, Or.inl (hq hpc hrun hmf)⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, hqp hpan hmf⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.call_frame_frozen {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.call_frame_frozen hcall hF hsym hpc hrun hsp hlr hspec hφ hP hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hFm hsymm =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hFm hsymm)
    hoom

theorem SepWPp.call_inImage_frame {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.call_inImage_frame hcall hF hsym hpc hrun hsp hlr hspec hφ hP hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hFm hsymm =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hFm hsymm)
    hoom

theorem SepWPp.mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  exact SepWPp.weaken_pre h hwp

theorem SepWPp.elim_pure {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem SepWPp.elim_exists {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (Φ a ∗ P) Q Qp) :
    SepWPp prog ret s ((∃∗ a, Φ a) ∗ P) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

theorem SepWPp.elim_pure_focus {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = (⌜φ⌝ ∗ Rest))
    (h : φ → SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc]
  exact SepWPp.elim_pure h

theorem SepWPp.elim_exists_focus {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Φ : α → SepProp} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = ((∃∗ p, Φ p) ∗ Rest))
    (h : ∀ p, SepWPp prog ret s (Φ p ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc]
  exact SepWPp.elim_exists h

theorem SepWPp.elim_vecU8_focus {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {a : BitVec 64} {bs : List (BitVec 8)} {P Rest : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfoc : P = (vecU8 A a bs ∗ Rest))
    (h : ∀ cap ptr : BitVec 64,
      bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 →
      SepWPp prog ret s
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc]
  unfold vecU8
  apply SepWPp.elim_exists; intro cap
  apply SepWPp.elim_exists; intro ptr
  unfold vecU8At vecHeader
  rw [← sepConj_assoc,
      sepConj_comm ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)),
      sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply SepWPp.elim_pure; rintro ⟨hle, hlt, hnz⟩
  simp only [sepConj_assoc]
  exact h cap ptr hle hlt hnz

/-! ## 3. Segment 8 (`+0x678 → +0x6a4 / +0x30c`) -/

theorem signalMessageAt_ct_lt {A : RustAlloc} {g : SignalMessageGhost} {a : BitVec 64}
    {msg : SignalMessage} {R : SepProp} {m : Memory}
    (h : m ⊨ signalMessageAt A g a msg ∗ R) : msg.ciphertext.length < 2 ^ 40 := by
  unfold signalMessageAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.2.1

elab "sep_close" : tactic => do
  SepSolver.closeSat (SepSolver.tacDisch (← `(tactic| first | rfl | assumption | (bv_omega_fast; done))))

theorem aesDecrypt_scr_split (sp : BitVec 64) :
    memRegion (sp + 0x140#64) 0x3c0 =
      (memRegion (sp + 0x140#64) 0x290 ∗ memRegion (sp + 0x3d0#64) 24 ∗
       memRegion (sp + 0x3e8#64) 0x118) := by
  rw [show (0x3c0 : Nat) = 0x290 + (24 + 0x118) by decide,
      memRegion_split (sp + 0x140#64) 0x290 (24 + 0x118) (by decide),
      show sp + 0x140#64 + BitVec.ofNat 64 0x290 = sp + 0x3d0#64 by bv_omega,
      memRegion_split (sp + 0x3d0#64) 24 0x118 (by decide),
      show sp + 0x3d0#64 + BitVec.ofNat 64 24 = sp + 0x3e8#64 by bv_omega]

theorem applyRatchet_reg10_split (sp : BitVec 64) :
    memRegion (sp + 0x10#64) 0x18 =
      (memRegion (sp + 0x10#64) 0xc ∗ memRegion (sp + 0x1c#64) 4 ∗ memRegion (sp + 0x20#64) 8) := by
  rw [show (0x18 : Nat) = 0xc + (4 + 8) by decide,
      memRegion_split (sp + 0x10#64) 0xc (4 + 8) (by decide),
      show sp + 0x10#64 + BitVec.ofNat 64 0xc = sp + 0x1c#64 by bv_omega,
      memRegion_split (sp + 0x1c#64) 4 8 (by decide),
      show sp + 0x1c#64 + BitVec.ofNat 64 4 = sp + 0x20#64 by bv_omega]

theorem applyRatchet_reg3e8_split (sp : BitVec 64) :
    memRegion (sp + 0x3e8#64) 0x198 =
      (memRegion (sp + 0x3e8#64) 0x118 ∗ memRegion (sp + 0x500#64) 0x54 ∗ memRegion (sp + 0x554#64) 0x2c) := by
  rw [show (0x198 : Nat) = 0x118 + (0x54 + 0x2c) by decide,
      memRegion_split (sp + 0x3e8#64) 0x118 (0x54 + 0x2c) (by decide),
      show sp + 0x3e8#64 + BitVec.ofNat 64 0x118 = sp + 0x500#64 by bv_omega,
      memRegion_split (sp + 0x500#64) 0x54 0x2c (by decide),
      show sp + 0x500#64 + BitVec.ofNat 64 0x54 = sp + 0x554#64 by bv_omega]

theorem Satisfies.mono_focus {A B P Rest : SepProp} {m : Memory}
    (hAB : A ⊢ B) (hfoc : P = A ∗ Rest) (hm : m ⊨ P) :
    m ⊨ B ∗ Rest := by
  rw [hfoc] at hm
  exact Satisfies.mono (sepConj_mono_left hAB) hm

theorem SepWPp.mono_focus {prog : Program} {ret : BitVec 64} {s : State}
    {A B P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hAB : A ⊢ B) (hfoc : P = A ∗ Rest)
    (hwp : SepWPp prog ret s (B ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc]
  exact SepWPp.mono_pre (sepConj_mono_left hAB) hwp

theorem vecU8At_parts_entails_vecU8 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hnz : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
    vecU8 A a bs := by
  unfold vecU8
  refine Entails.trans ?_ (Entails.sepExists_intro cap)
  refine Entails.trans ?_ (Entails.sepExists_intro ptr)
  unfold vecU8At vecHeader
  rw [← sepConj_assoc,
      sepConj_comm ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)),
      sepConj_assoc, sepConj_assoc]
  exact Entails.pure_right
    (⟨hle, hlt, hnz⟩ : bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0)
    (Entails.of_eq (by ac_rfl))

theorem mks_parts_entails_memRegion (sp : BitVec 64) (mks : MessageKeys) :
    ((sp - 224#64) ↦ₛ keyToBytes32 mks.cipherKey) ∗
    ((sp - 192#64) ↦ₛ keyToBytes32 mks.macKey) ∗
    ((sp - 160#64) ↦ₛ CBC.blockToBytesLE mks.iv) ∗
    ((sp - 144#64) ↦₃₂ mks.counter) ⊢
    memRegion (sp - 1504#64 + 0x500#64) 0x54 := by
  rw [show sp - 224#64 = sp - 1504#64 + 0x500#64 by bv_omega,
      show sp - 192#64 = sp - 1504#64 + 0x520#64 by bv_omega,
      show sp - 160#64 = sp - 1504#64 + 0x540#64 by bv_omega,
      show sp - 144#64 = sp - 1504#64 + 0x550#64 by bv_omega,
      ← messageKeysAt_eq]
  exact messageKeysAt_entails_memRegion _ _

theorem applyRatchet_sp_entails_memRegion (sp : BitVec 64) (msgW : BitVec 32) (locA remA : BitVec 64) :
    ((sp - 1476#64) ↦₃₂ msgW) ∗
    ((sp - 1472#64) ↦₆₄ locA) ∗
    ((sp - 1456#64) ↦₆₄ remA) ⊢
    memRegion (sp - 1476#64) 4 ∗
    memRegion (sp - 1472#64) 8 ∗
    memRegion (sp - 1456#64) 8 :=
  sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem errTail_sp_entails_memRegion (sp : BitVec 64)
    (newPqrCap locA newPqrPtr remA v1104 v1096 v528 v520 v512 v480 v472 : BitVec 64)
    (msgW : BitVec 32) :
    ((sp - 1496#64) ↦₆₄ newPqrCap) ∗
    ((sp - 1476#64) ↦₃₂ msgW) ∗
    ((sp - 1472#64) ↦₆₄ locA) ∗
    ((sp - 1464#64) ↦₆₄ newPqrPtr) ∗
    ((sp - 1456#64) ↦₆₄ remA) ∗
    ((sp - 1104#64) ↦₆₄ v1104) ∗
    ((sp - 1096#64) ↦₆₄ v1096) ∗
    ((sp - 528#64) ↦₆₄ v528) ∗
    ((sp - 520#64) ↦₆₄ v520) ∗
    ((sp - 512#64) ↦₆₄ v512) ∗
    ((sp - 480#64) ↦₆₄ v480) ∗
    ((sp - 472#64) ↦₆₄ v472) ⊢
    memRegion (sp - 1496#64) 8 ∗
    memRegion (sp - 1476#64) 4 ∗
    memRegion (sp - 1472#64) 8 ∗
    memRegion (sp - 1464#64) 8 ∗
    memRegion (sp - 1456#64) 8 ∗
    memRegion (sp - 1104#64) 8 ∗
    memRegion (sp - 1096#64) 8 ∗
    memRegion (sp - 528#64) 8 ∗
    memRegion (sp - 520#64) 8 ∗
    memRegion (sp - 512#64) 8 ∗
    memRegion (sp - 480#64) 8 ∗
    memRegion (sp - 472#64) 8 :=
  sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (sepConj_mono (pointsTo64_entails_memRegion _ _)
                        (pointsTo64_entails_memRegion _ _)))))))))))

theorem aesDecrypt_none_scr_split (sp : BitVec 64) :
    memRegion (sp - 1184#64) 656 =
      (memRegion (sp - 1184#64) 40 ∗ memRegion (sp - 1144#64) 24 ∗
       memRegion (sp - 1120#64) 1 ∗ memRegion (sp - 1119#64) 15 ∗
       memRegion (sp - 1104#64) 8 ∗ memRegion (sp - 1096#64) 8 ∗
       memRegion (sp - 1088#64) 560) := by
  rw [show (656 : Nat) = 40 + (24 + (1 + (15 + (8 + (8 + 560))))) by decide,
      memRegion_split (sp - 1184#64) 40 _ (by decide),
      show sp - 1184#64 + BitVec.ofNat 64 40 = sp - 1144#64 by bv_omega,
      memRegion_split (sp - 1144#64) 24 _ (by decide),
      show sp - 1144#64 + BitVec.ofNat 64 24 = sp - 1120#64 by bv_omega,
      memRegion_split (sp - 1120#64) 1 _ (by decide),
      show sp - 1120#64 + BitVec.ofNat 64 1 = sp - 1119#64 by bv_omega,
      memRegion_split (sp - 1119#64) 15 _ (by decide),
      show sp - 1119#64 + BitVec.ofNat 64 15 = sp - 1104#64 by bv_omega,
      memRegion_split (sp - 1104#64) 8 _ (by decide),
      show sp - 1104#64 + BitVec.ofNat 64 8 = sp - 1096#64 by bv_omega,
      memRegion_split (sp - 1096#64) 8 560 (by decide),
      show sp - 1096#64 + BitVec.ofNat 64 8 = sp - 1088#64 by bv_omega]

theorem aesDecrypt_none_reg504_split (sp : BitVec 64) :
    memRegion (sp - 504#64) 280 =
      (memRegion (sp - 504#64) 24 ∗ memRegion (sp - 480#64) 8 ∗
       memRegion (sp - 472#64) 8 ∗ memRegion (sp - 464#64) 240) := by
  rw [show (280 : Nat) = 24 + (8 + (8 + 240)) by decide,
      memRegion_split (sp - 504#64) 24 _ (by decide),
      show sp - 504#64 + BitVec.ofNat 64 24 = sp - 480#64 by bv_omega,
      memRegion_split (sp - 480#64) 8 _ (by decide),
      show sp - 480#64 + BitVec.ofNat 64 8 = sp - 472#64 by bv_omega,
      memRegion_split (sp - 472#64) 8 240 (by decide),
      show sp - 472#64 + BitVec.ofNat 64 8 = sp - 464#64 by bv_omega]

theorem aesDecrypt_none_prep (sp : BitVec 64) :
    memRegion (sp - 1184#64) 656 ∗ memRegion (sp - 504#64) 280 ⊢
      (memRegion (sp - 1184#64) 40 ∗ memRegion (sp - 1144#64) 24 ∗
       memRegion (sp - 1120#64) 1 ∗ memRegion (sp - 1119#64) 15 ∗
       memRegion (sp - 1104#64) 8 ∗ memRegion (sp - 1096#64) 8 ∗
       memRegion (sp - 1088#64) 560) ∗
      (memRegion (sp - 504#64) 24 ∗ memRegion (sp - 480#64) 8 ∗
       memRegion (sp - 472#64) 8 ∗ memRegion (sp - 464#64) 240) := by
  rw [← aesDecrypt_none_scr_split sp, ← aesDecrypt_none_reg504_split sp]
  exact Entails.refl _

theorem SepWPp.elim_memRegion8_focus {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = (memRegion a 8 ∗ Rest))
    (h : ∀ v : BitVec 64, SepWPp prog ret s ((a ↦₆₄ v) ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc, memRegion_eight]
  exact SepWPp.elim_exists h

theorem SepWPp.elim_memRegion1_focus {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = (memRegion a 1 ∗ Rest))
    (h : ∀ v : BitVec 8, SepWPp prog ret s ((a ↦₈ v) ∗ Rest) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  rw [hfoc, memRegion_one]
  exact SepWPp.elim_exists h

theorem SepWP.setPC_ite_false {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {c : Prop} [inst : Decidable c] {pc1 pc2 : BitVec 64} (hnc : ¬ c)
    (helse : SepWP prog target_pc (s.setPC pc2) P post) :
    SepWP prog target_pc (s.setPC (@ite _ c inst pc1 pc2)) P post := by
  rw [ite_eq_right_iff.mpr fun hc => (hnc hc).elim]; exact helse

theorem SepWP.setPC_ite_true {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {c : Prop} [inst : Decidable c] {pc1 pc2 : BitVec 64} (hc : c)
    (hthen : SepWP prog target_pc (s.setPC pc1) P post) :
    SepWP prog target_pc (s.setPC (@ite _ c inst pc1 pc2)) P post := by
  rw [ite_eq_left_iff.mpr fun hnc => (hnc hc).elim]; exact hthen

theorem errTail_sp_split (sp : BitVec 64) :
    memRegion (sp - 1504#64) 0x38 =
      (memRegion (sp - 1504#64) 8 ∗ memRegion (sp - 1496#64) 8 ∗
       memRegion (sp - 1488#64) 12 ∗ memRegion (sp - 1476#64) 4 ∗
       memRegion (sp - 1472#64) 8 ∗ memRegion (sp - 1464#64) 8 ∗
       memRegion (sp - 1456#64) 8) := by
  rw [show (0x38 : Nat) = 8 + (8 + (12 + (4 + (8 + (8 + 8))))) by decide,
      memRegion_split (sp - 1504#64) 8 _ (by decide),
      show sp - 1504#64 + BitVec.ofNat 64 8 = sp - 1496#64 by bv_omega,
      memRegion_split (sp - 1496#64) 8 _ (by decide),
      show sp - 1496#64 + BitVec.ofNat 64 8 = sp - 1488#64 by bv_omega,
      memRegion_split (sp - 1488#64) 12 _ (by decide),
      show sp - 1488#64 + BitVec.ofNat 64 12 = sp - 1476#64 by bv_omega,
      memRegion_split (sp - 1476#64) 4 _ (by decide),
      show sp - 1476#64 + BitVec.ofNat 64 4 = sp - 1472#64 by bv_omega,
      memRegion_split (sp - 1472#64) 8 _ (by decide),
      show sp - 1472#64 + BitVec.ofNat 64 8 = sp - 1464#64 by bv_omega,
      memRegion_split (sp - 1464#64) 8 8 (by decide),
      show sp - 1464#64 + BitVec.ofNat 64 8 = sp - 1456#64 by bv_omega]

theorem errTail_reg190_split (sp : BitVec 64) :
    memRegion (sp - 1504#64 + 0x190#64) 0x3f0 =
      (memRegion (sp - 1104#64) 8 ∗ memRegion (sp - 1096#64) 8 ∗
       memRegion (sp - 1088#64) 560 ∗ memRegion (sp - 528#64) 8 ∗
       memRegion (sp - 520#64) 8 ∗ memRegion (sp - 512#64) 8 ∗
       memRegion (sp - 504#64) 24 ∗ memRegion (sp - 480#64) 8 ∗
       memRegion (sp - 472#64) 8 ∗ memRegion (sp - 464#64) 240 ∗
       memRegion (sp - 1504#64 + 0x500#64) 0x54 ∗
       memRegion (sp - 1504#64 + 0x554#64) 0x2c) := by
  rw [show sp - 1504#64 + 0x190#64 = sp - 1104#64 by bv_omega,
      show (0x3f0 : Nat) = 8 + (8 + (560 + (8 + (8 + (8 + (24 + (8 + (8 + (240 + (0x54 + 0x2c)))))))))) by decide,
      memRegion_split (sp - 1104#64) 8 _ (by decide),
      show sp - 1104#64 + BitVec.ofNat 64 8 = sp - 1096#64 by bv_omega,
      memRegion_split (sp - 1096#64) 8 _ (by decide),
      show sp - 1096#64 + BitVec.ofNat 64 8 = sp - 1088#64 by bv_omega,
      memRegion_split (sp - 1088#64) 560 _ (by decide),
      show sp - 1088#64 + BitVec.ofNat 64 560 = sp - 528#64 by bv_omega,
      memRegion_split (sp - 528#64) 8 _ (by decide),
      show sp - 528#64 + BitVec.ofNat 64 8 = sp - 520#64 by bv_omega,
      memRegion_split (sp - 520#64) 8 _ (by decide),
      show sp - 520#64 + BitVec.ofNat 64 8 = sp - 512#64 by bv_omega,
      memRegion_split (sp - 512#64) 8 _ (by decide),
      show sp - 512#64 + BitVec.ofNat 64 8 = sp - 504#64 by bv_omega,
      memRegion_split (sp - 504#64) 24 _ (by decide),
      show sp - 504#64 + BitVec.ofNat 64 24 = sp - 480#64 by bv_omega,
      memRegion_split (sp - 480#64) 8 _ (by decide),
      show sp - 480#64 + BitVec.ofNat 64 8 = sp - 472#64 by bv_omega,
      memRegion_split (sp - 472#64) 8 _ (by decide),
      show sp - 472#64 + BitVec.ofNat 64 8 = sp - 464#64 by bv_omega,
      memRegion_split (sp - 464#64) 240 _ (by decide),
      show sp - 464#64 + BitVec.ofNat 64 240 = sp - 1504#64 + 0x500#64 by bv_omega,
      memRegion_split (sp - 1504#64 + 0x500#64) 0x54 0x2c (by decide),
      show sp - 1504#64 + 0x500#64 + BitVec.ofNat 64 0x54 = sp - 1504#64 + 0x554#64 by bv_omega]

theorem formatInner_post_eq_badCiphertext (A : RustAlloc) (sp : BitVec 64) :
    (∃∗ bs : List (BitVec 8), vecU8 A (sp - 1144#64) bs) =
      invalidMessageStrAt A (sp - 1504#64 + 0x168#64) .badCiphertext := by
  unfold invalidMessageStrAt
  rw [show sp - 1504#64 + 0x168#64 = sp - 1144#64 by bv_omega]

theorem newPqr_zero_prep (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap = 0) :
    (if cap = 0 then emp else (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs)) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢ emp := by
  simp only [hcap, ↓reduceIte]; exact Entails.refl _

theorem newPqr_dealloc_prep' (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap ≠ 0) (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    (if cap = 0 then emp else (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs)) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
    A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  simp only [sepConj_assoc]
  exact newPqr_dealloc_prep A cap ptr bs hcap hle hlt

theorem vecU8At_parts_entails_vecU8' (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hnz : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (if cap = 0 then emp else (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs)) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
    vecU8 A a bs := by
  simp only [sepConj_assoc]
  exact vecU8At_parts_entails_vecU8 A a cap ptr bs hle hlt hnz

theorem stackAt_ext_split_alloc (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12288 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp 4096 12288 (by decide)

theorem noPanic_callee {F R Q : SepProp} {m : Memory}
    (hm : m ⊨ (⌜False⌝ ∗ F) ∗ R) : m ⊨ Q := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1.elim

theorem noExit_callee {F R : SepProp} {m : Memory}
    (hm : m ⊨ ⌜False⌝ ∗ F ∗ R) : False := by
  rw [satisfies_pure_sepConj] at hm
  exact hm.1

theorem writeReg64_trace (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := rfl
theorem writeReg32_trace (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := rfl
theorem setPC_trace (s : State) (pc : BitVec 64) :
    (s.setPC pc).trace = s.trace := rfl
theorem setPState_trace (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := rfl
theorem setMem_trace (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := rfl

theorem boxU8At_msg_ct (A : RustAlloc) (a p : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A (a + 0x18#64) p bs =
      (((a + 0x18#64) ↦₆₄ p) ∗ ((a + 0x20#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
       (p ↦ₛ bs) ∗ boxU8Rest A p bs) := by
  rw [boxU8At_eq_rest, show a + 0x18#64 + 8#64 = a + 0x20#64 by bv_omega]

theorem pointsTo8_msgType_eq (sp : BitVec 64) (msgW : BitVec 32) (t : MessageType)
    (hmsgW : msgW.setWidth 8 = msgTypeByte t) :
    ((sp - 1120#64) ↦₈ msgW.setWidth 8) =
      ((sp - 1504#64 + 0x168#64 + 24#64) ↦₈ msgTypeByte t) := by
  rw [hmsgW, show sp - 1504#64 + 0x168#64 + 24#64 = sp - 1120#64 by bv_omega]

/-! ## 4. `Stage2ContractsX` (`_x`) Helpers for Back Segments -/

theorem shim_ok_at_x (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      ((withStack sessionShimSpec extHookStack).inImage img) :=
  hC.shim_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem memcpy_ok_at_x (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      ((withStack sessionMemcpyRegionSpec extHookStack).inImage img) :=
  hC.session_memcpy_region_ok_at tryDecryptName (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem alloc_ok_at_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  hC.alloc_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem dealloc_ok_at_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  hC.dealloc_ok_at tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem formatInner_ok_at_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      ((formatInnerSpec A).inImage img) :=
  hC.format_inner_ok_at tryDecryptName (num% (ls_off% "alloc::fmt::format::format_inner" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem aesDec_ok_at_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + BitVec.ofNat 64 (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")))
      ((aesDecFnSpec decFn A).inImage img) :=
  hC.aes_dec_ok_at tryDecryptName (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>"))

theorem tryDecryptFn_onPanic_of_callee (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold tryDecryptFnSpec Spec.inImage
  exact allowPanic_frame
    (fun ⟨haf, hmf⟩ => ⟨Or.inr (Or.inr (allocFailedIn_trans h0m haf)), h0m.trans hmf⟩) hm

theorem tryDecryptFn_onPanic_of_direct (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (s0 sf : State) (P R : SepProp)
    (haf : allocFailedIn s0 sf) (htr : s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  unfold tryDecryptFnSpec Spec.inImage
  exact allowPanic_panicked ⟨Or.inr (Or.inr haf), htr⟩ hm

theorem SepWPp.panic_direct_fn_ext (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (ext : String → Option (State → State))
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : (tripleRatchetProgAtExt img.base ext).externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (tryDecryptFnSpec C decFn A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  refine SepWPp.panic_at hpc hrun hext fun _ hm_pan => ?_
  have htr_f : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent] := htr
  have haf : allocFailedIn s0 (Rust.panicked s) := by
    unfold allocFailedIn
    rw [htr_f, List.drop_left]
    exact List.Mem.head _
  have hpre : s0.trace <+: (Rust.panicked s).trace := by
    rw [htr_f]
    exact ⟨[allocFailedEvent], rfl⟩
  exact tryDecryptFn_onPanic_of_direct C decFn A ctl S img x s0 (Rust.panicked s) P R haf hpre hm_pan

theorem layoutOk_of_cap_ne_zero {cap : BitVec 64} (hcap : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 :=
  ⟨by bv_omega, ⟨0, rfl⟩, by omega⟩

theorem aesDecrypt_none_prep_x (sp : BitVec 64) :
    memRegion (sp - 520#64) 16 ∗ memRegion (sp - 1184#64) 656 ∗ memRegion (sp - 504#64) 280 ⊢
      (memRegion (sp - 520#64) 8 ∗ memRegion (sp - 512#64) 8) ∗
      (memRegion (sp - 1184#64) 40 ∗ memRegion (sp - 1144#64) 24 ∗
       memRegion (sp - 1120#64) 1 ∗ memRegion (sp - 1119#64) 15 ∗
       memRegion (sp - 1104#64) 8 ∗ memRegion (sp - 1096#64) 8 ∗
       memRegion (sp - 1088#64) 560) ∗
      (memRegion (sp - 504#64) 24 ∗ memRegion (sp - 480#64) 8 ∗
       memRegion (sp - 472#64) 8 ∗ memRegion (sp - 464#64) 240) := by
  rw [show (16 : Nat) = 8 + 8 by decide,
      memRegion_split (sp - 520#64) 8 8 (by decide),
      show sp - 520#64 + BitVec.ofNat 64 8 = sp - 512#64 by bv_omega,
      ← aesDecrypt_none_scr_split sp, ← aesDecrypt_none_reg504_split sp]
  exact Entails.refl _

theorem logFilterAddr_eq_at_c00_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.LibsignalSession.logFilterAddr img =
      ((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr tryDecryptName + 3072#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 3072))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) := by
  have halign := ProofLib.ObjectLoad.base_aligned_of_loads himg
  unfold CryptoVerification.LibsignalSession.logFilterAddr
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")]
  revert halign; bv_kernel

theorem logOff_eq_at_c00_ext {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    logOff img =
      (((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr tryDecryptName + 3072#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>" + 3072))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) ↦₆₄ 0#64) := by
  unfold logOff
  rw [logFilterAddr_eq_at_c00_ext himg ext]

theorem aesDecrypt_none_reg1144_split (sp : BitVec 64) :
    memRegion (sp - 1144#64) 24 =
      (memRegion (sp - 1144#64) 8 ∗ memRegion (sp - 1136#64) 8 ∗ memRegion (sp - 1128#64) 8) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by decide,
      memRegion_split (sp - 1144#64) 8 (8 + 8) (by decide),
      show sp - 1144#64 + BitVec.ofNat 64 8 = sp - 1136#64 by bv_omega,
      memRegion_split (sp - 1136#64) 8 8 (by decide),
      show sp - 1136#64 + BitVec.ofNat 64 8 = sp - 1128#64 by bv_omega]

theorem aesDecrypt_none_p0_spe_entails_memRegion (sp : BitVec 64)
    (w1144 w1136 : BitVec 64) (b1120 : BitVec 8) :
    ((sp - 1144#64) ↦₆₄ w1144) ∗
    ((sp - 1136#64) ↦₆₄ w1136) ∗
    memRegion (sp - 1128#64) 8 ∗
    ((sp - 1120#64) ↦₈ b1120) ∗
    memRegion (sp - 1119#64) 15 ⊢
    memRegion (sp - 1504#64 + 0x168#64) 40 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))))) ?_
  rw [show sp - 1504#64 + 0x168#64 = sp - 1144#64 by bv_omega,
      show (40 : Nat) = 8 + (8 + (8 + (1 + 15))) by decide,
      memRegion_split (sp - 1144#64) 8 _ (by decide),
      show sp - 1144#64 + BitVec.ofNat 64 8 = sp - 1136#64 by bv_omega,
      memRegion_split (sp - 1136#64) 8 _ (by decide),
      show sp - 1136#64 + BitVec.ofNat 64 8 = sp - 1128#64 by bv_omega,
      memRegion_split (sp - 1128#64) 8 _ (by decide),
      show sp - 1128#64 + BitVec.ofNat 64 8 = sp - 1120#64 by bv_omega,
      memRegion_split (sp - 1120#64) 1 15 (by decide),
      show sp - 1120#64 + BitVec.ofNat 64 1 = sp - 1119#64 by bv_omega]
  exact Entails.refl _

/-! ## 5. Relocatable `[LibsignalPlacement]` Helpers for Back Segments -/

section Placed

theorem SepWPp.of_sepWP_placed [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩
  · have hcl_m := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout⟩ := hnext hcl_m R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.call_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_sm, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hcl.of_keepsFrozen hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_sm, hoom sm R hoom_sm hpost⟩)⟩

theorem SepWPp.call_cro_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_sm, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hcl.of_keepsFrozen hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_sm, hoom sm R hoom_sm hpost⟩)⟩

theorem tryDecrypt_onPanic_of_callee_placed [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (x : TryDecryptGhost) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  unfold tryDecryptSpecPlaced withLsCodeRoLoaded tryDecryptRawSpecPlaced tryDecryptSpec Spec.inImage
  exact allowPanic_frame
    (fun ⟨haf, hmf⟩ => ⟨Or.inr (Or.inr (allocFailedIn_trans h0m haf)), h0m.trans hmf⟩) hm

theorem tryDecrypt_onPanic_of_direct_placed [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (x : TryDecryptGhost) (s0 sf : State) (P R : SepProp)
    (haf : allocFailedIn s0 sf) (htr : s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  unfold tryDecryptSpecPlaced withLsCodeRoLoaded tryDecryptRawSpecPlaced tryDecryptSpec Spec.inImage
  exact allowPanic_panicked ⟨Or.inr (Or.inr haf), htr⟩ hm

theorem SepWPp.panic_direct_placed [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    {prog : Program}
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : prog.externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp prog ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 sf ∗ R)) := by
  refine SepWPp.panic_at hpc hrun hext fun _ hm_pan => ?_
  have htr_f : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent] := htr
  have haf : allocFailedIn s0 (Rust.panicked s) := by
    unfold allocFailedIn
    rw [htr_f, List.drop_left]
    exact List.Mem.head _
  have hpre : s0.trace <+: (Rust.panicked s).trace := by
    rw [htr_f]
    exact ⟨[allocFailedEvent], rfl⟩
  exact tryDecrypt_onPanic_of_direct_placed C A ctl S x s0 (Rust.panicked s) P R haf hpre hm_pan

theorem tryDecryptFn_onPanic_of_callee_placed [LibsignalPlacement]
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (x : TryDecryptGhost) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  unfold tryDecryptFnSpecPlaced withLsCodeRoLoaded tryDecryptFnRawSpecPlaced tryDecryptFnSpec Spec.inImage
  exact allowPanic_frame
    (fun ⟨haf, hmf⟩ => ⟨Or.inr (Or.inr (allocFailedIn_trans h0m haf)), h0m.trans hmf⟩) hm

theorem tryDecryptFn_onPanic_of_direct_placed [LibsignalPlacement]
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (x : TryDecryptGhost) (s0 sf : State) (P R : SepProp)
    (haf : allocFailedIn s0 sf) (htr : s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 sf ∗ R := by
  unfold tryDecryptFnSpecPlaced withLsCodeRoLoaded tryDecryptFnRawSpecPlaced tryDecryptFnSpec Spec.inImage
  exact allowPanic_panicked ⟨Or.inr (Or.inr haf), htr⟩ hm

theorem SepWPp.panic_direct_fn_placed [LibsignalPlacement]
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    {prog : Program}
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : prog.externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp prog ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A ctl uuidTryParse S).onPanic x s0 sf ∗ R)) := by
  refine SepWPp.panic_at hpc hrun hext fun _ hm_pan => ?_
  have htr_f : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent] := htr
  have haf : allocFailedIn s0 (Rust.panicked s) := by
    unfold allocFailedIn
    rw [htr_f, List.drop_left]
    exact List.Mem.head _
  have hpre : s0.trace <+: (Rust.panicked s).trace := by
    rw [htr_f]
    exact ⟨[allocFailedEvent], rfl⟩
  exact tryDecryptFn_onPanic_of_direct_placed C decFn A ctl S x s0 (Rust.panicked s) P R haf hpre hm_pan

theorem logFilterAddr_eq_placed [LibsignalPlacement] :
    CryptoVerification.LibsignalSession.logFilterAddr tryDecryptPlacedImg =
      lsρ lsLogFilterSym :=
  logFilterAddr_tryDecryptPlacedImg

theorem logOff_eq_placed [LibsignalPlacement] :
    logOff tryDecryptPlacedImg = (lsρ lsLogFilterSym ↦₆₄ 0#64) :=
  logOff_tryDecryptPlacedImg

private theorem exec_bind_panic_eq_auth {σ α β : Type} (m : Mut σ α) (f₁ f₂ : α → Mut σ β) (s : σ)
    (h : ∀ a s', ((Mut.exec (f₁ a) s').1 = .error .panic) = ((Mut.exec (f₂ a) s').1 = .error .panic)) :
    ((Mut.exec (m >>= f₁) s).1 = .error .panic) = ((Mut.exec (m >>= f₂) s).1 = .error .panic) := by
  dsimp only [Bind.bind, ExceptT.bind, StateT.bind, Mut.exec, ExceptT.run, StateT.run, ExceptT.mk, ExceptT.bindCont]
  cases m s with
  | mk res s' =>
    cases res with
    | error e => rfl
    | ok a => exact h a s'

private theorem decryptFn_error_panic_eq_auth {PQ PQC : Type} (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (s : TripleRatchet PQ) :
    ((Mut.exec (TripleRatchet.decryptFn C decFn spqr expected ciphertext msgType coins) s).1 = .error .panic) =
      ((Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType coins) s).1 = .error .panic) := by
  unfold TripleRatchet.decryptFn TripleRatchet.decrypt
  refine exec_bind_panic_eq_auth _ _ _ s fun chainKey s1 => ?_
  refine exec_bind_panic_eq_auth _ _ _ s1 fun messageKeyGen s2 => ?_
  refine exec_bind_panic_eq_auth _ _ _ s2 fun t s3 => ?_
  dsimp only
  cases spqr.recvPanics t.pqrState ciphertext.pqRatchet with
  | true => rfl
  | false =>
    cases spqr.recv t.pqrState ciphertext.pqRatchet with
    | error sd => cases sd <;> rfl
    | ok r =>
      rcases r with ⟨newPqrState, pqrKey⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [Bind.bind, ExceptT.bind, StateT.bind, Mut.exec, ExceptT.run, StateT.run,
        pure, ExceptT.pure, StateT.pure, ExceptT.mk, ExceptT.bindCont]
      cases SignalMessage.verifyMacWithAddresses C.F ciphertext expected
          t.remoteIdentityKey t.localIdentityKey
          (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).macKey with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases decFn ciphertext.ciphertext
            (keyToBytes32 (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).cipherKey)
            (CBC.blockToBytesLE (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).iv) <;>
          cases aesCbcDecrypt C.D
            (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).cipherKey
            (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).iv
            ciphertext.ciphertext <;>
          exact propext ⟨nofun, nofun⟩

private theorem exec_liftE_tail_panic_eq_auth {PQ : Type} [Inhabited PQ]
    (r : Except SignalProtocolError (List (BitVec 8))) (session : TripleRatchet PQ)
    (s : SessionState PQ) :
    ((Mut.exec (do
      let ptext ← liftE r
      modify fun st => (session.applyToSessionState st).clearUnacknowledgedPreKeyMessage
      return ptext) s).1 = .error .panic) = (r = .error .panic) := by
  cases r with
  | error e => rfl
  | ok ptext => rfl

private theorem tryDecryptWithStateFn_error_panic_eq_auth {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (s : SessionState PQ) :
    ((Mut.exec (SessionState.tryDecryptWithStateFn C decFn spqr expected ciphertext msgType coins) s).1 = .error .panic) =
      ((Mut.exec (SessionState.tryDecryptWithState C spqr expected ciphertext msgType coins) s).1 = .error .panic) := by
  unfold SessionState.tryDecryptWithStateFn SessionState.tryDecryptWithState
  refine exec_bind_panic_eq_auth _ _ _ s fun session s1 => ?_
  dsimp only
  rw [exec_liftE_tail_panic_eq_auth, exec_liftE_tail_panic_eq_auth]
  exact decryptFn_error_panic_eq_auth C decFn spqr expected ciphertext msgType coins session

theorem tryDecryptFnSpec_onPanic_eq_auth (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    (tryDecryptFnSpec C decFn A ctl parse S img).onPanic =
      (tryDecryptSpec C A ctl parse S img).onPanic := by
  funext x s0 sf
  unfold tryDecryptFnSpec tryDecryptSpec Spec.inImage
  dsimp only
  rw [show ((x.modelFn C decFn S parse).1 = .error .panic) = ((x.model C S parse).1 = .error .panic) from
    tryDecryptWithStateFn_error_panic_eq_auth C decFn S.spqr
      (serializeAddresses (serviceIdParse parse) x.rem x.loc) x.msg x.msgType (coinsOf x.rest) x.st]

theorem tryDecryptFnSpecPlaced_onPanic_eq_auth [LibsignalPlacement] (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) :
    (tryDecryptFnSpecPlaced C decFn A ctl parse S).onPanic =
      (tryDecryptSpecPlaced C A ctl parse S).onPanic :=
  tryDecryptFnSpec_onPanic_eq_auth C decFn A ctl parse S tryDecryptPlacedImg

end Placed

end CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt
