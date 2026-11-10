/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Previous-Session Loop Head (`+0x1e78 → +0x1ee8`)

Proves `overPrevLoop_head_cli_wp` on `tripleRatchetProgAtExt` for `previous_sessions.len = 1`,
writing `-1` to `[sp + 0x3e0]` and `prevPtr + 24` to `[sp + 0xd0]`, initializing loop registers
(`x21 = sp + 0x930`, `x24 = 1`, `x25 = -1`, `x26 = 0`, `x27 = prevPtr`), and preserving
`calleeSavedVRegs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")

private gen_decodes libsignalSessionCode_tree verNeLoopSegsCliDec [
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x1e78) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x1ea4)]

local macro "loopSegs_fetches_range " b:term:max H:term:max lo:num hi:num : tactic => do
  let s := lo.getNat
  let l := Lean.Syntax.mkNumLit (toString (hi.getNat - s + 4))
  `(tactic| code_fetches_range libsignalSessionCode verNeLoopSegsCliDec $b $H
    (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") $lo $l)

set_option maxHeartbeats 800000 in
/-- Loop head (`+0x1e78 → +0x1ee8`) on `tripleRatchetProgAtExt img.base ext` when `len = 1#64`. -/
theorem overPrevLoop_head_cli_wp (img : Obj.Image) (ext : String → Option (State → State))
    (s : State) (coroPtr prevCap prevPtr u3e0 wd0 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e78#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1ee8#64) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64))) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.sp + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = 0#64 ∧
        s1.readReg64 .x27 = prevPtr ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  loopSegs_fetches_range img.base (Rust.withPanics ext) 0x1e78 0x1ea4
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨Entails.refl _, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
