/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewFetch
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<SignalMessage>::new` Segment 1 (`+0x000 .. +0x100`)

Prologue (`+0x000..+0x054`), optional `serialize_addresses` and `PublicKey::serialize`
(`+0x054..+0x07c / +0x0f0`), and temporary `ciphertext` and `pq_ratchet` slice copies
(`+0x07c..+0x100`) for `<libsignal_protocol::protocol::SignalMessage>::new` (`0x1d918`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost
open ProofLib.ProgramReflection
open CryptoVerification.InImageLift

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[simp, wp_norm, arm64_norm]
abbrev TraceVRegsEq (sm s : State) : Prop :=
  sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s

theorem _root_.And.trans {α β : Type _} {a1 a2 a3 : α} {b1 b2 b3 : β}
    (h1 : a1 = a2 ∧ b1 = b2) (h2 : a2 = a3 ∧ b2 = b3) :
    a1 = a3 ∧ b1 = b3 :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

@[local simp, local arm64_norm]
theorem sp_sub_96_add_96 (a : BitVec 64) : a - 96#64 + 96#64 = a := by bv_lin
@[local simp, local arm64_norm]
theorem sp_sub_96_add_112 (a : BitVec 64) : a - 96#64 + 112#64 = a + 16#64 := by bv_lin
@[local simp, local arm64_norm]
theorem sp_sub_96_add_120 (a : BitVec 64) : a - 96#64 + 120#64 = a + 24#64 := by bv_lin
@[local simp, local arm64_norm]
theorem sp_sub_96_add_128 (a : BitVec 64) : a - 96#64 + 128#64 = a + 32#64 := by bv_lin
@[local simp, local arm64_norm]
theorem sp_add_32_add_8 (a : BitVec 64) : a + 32#64 + 8#64 = a + 40#64 := by bv_lin

namespace NewPrologueCallees

theorem entails_of_sep_focus {P Q : SepProp} (h : P = Q ∗ emp) : P ⊢ Q :=
  Entails.of_eq (by rw [h, sepConj_emp])

theorem satisfies_of_sep_focus {m : Memory} {P Q : SepProp} (hm : m ⊨ P)
    (h : P = Q ∗ emp) : m ⊨ Q := by
  rwa [h, sepConj_emp] at hm

theorem new_shim_ok_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) noAllocShimSpec :=
  hA.shim_ok_at signalMessageNewName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_shim_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) noAllocShimSpec :=
  noAllocShim_ok_at (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_alloc_ok_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) (rustAllocSpec A) :=
  hA.alloc_ok_at signalMessageNewName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_alloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) (rustAllocSpec A) :=
  alloc_ok_at_norm hA (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_memcpy_ok_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) framelessMemcpySpec :=
  memcpy_ok_at2_ext hA (name := signalMessageNewName) (k := num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) framelessMemcpySpec :=
  framelessMemcpy_ok_at (name := signalMessageNewName) (k := num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

end NewPrologueCallees

/-! ## Prologue (`+0x000..+0x054`) -/

theorem pointsTo32_sub_332_eq (a : BitVec 64) (v : BitVec 32) :
    ((a - 332#64) ↦₃₂ v) =
      ((a - 332#64) ↦₈ v.setWidth 8) ∗
      ((a - 331#64) ↦₈ v.extractLsb' 8 8) ∗
      ((a - 330#64) ↦₈ v.extractLsb' 16 8) ∗
      ((a - 329#64) ↦₈ v.extractLsb' 24 8) := by
  rw [pointsTo32_split8]
  have h0 : v.extractLsb' 0 8 = v.setWidth 8 := by bv_bits
  rw [h0, bv_sub_add_lit a 332 1, bv_sub_add_lit a 332 2, bv_sub_add_lit a 332 3]

theorem new_prologue_wp_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (x : SignalMessageNewGhost) (sp0 w368 w360 w352 w344 w328 : BitVec 64) (w332 : BitVec 32)
    (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : s0.spAligned = true)
    (hx1 : s0.readReg64 .x1 = x.macKeyA)
    (hx2 : s0.readReg64 .x2 = 32#64)
    (hx4 : s0.readReg64 .x4 = x.remA)
    (hx5 : s0.readReg64 .x5 = x.senderRatchetKeyA)
    (hx6 : (s0.readReg64 .x6).setWidth 32 = x.counter)
    (hx7 : (s0.readReg64 .x7).setWidth 32 = x.previousCounter)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 84#64) s0
      ((sp0 ↦₆₄ x.ciphertextA) ∗
       ((sp0 + 0x08#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
       ((sp0 + 0x10#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 + 0x18#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 + 0x20#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
       ((sp0 - 368#64) ↦₆₄ w368) ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗
       ((sp0 - 352#64) ↦₆₄ w352) ∗
       ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗
       ((sp0 - 328#64) ↦₆₄ w328) ∗
       cells (sp0 - 96#64) 12)
      (fun s1 P1 =>
        (s1.sp = sp0 - 416#64 ∧
         s1.spAligned = true ∧
         s1.readReg64 .x3 = s0.readReg64 .x3 ∧
         s1.readReg64 .x4 = x.remA ∧
         s1.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         s1.readReg64 .x20 = x.senderRatchetKeyA ∧
         s1.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         s1.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         s1.readReg64 .x24 = x.ret ∧
         s1.readReg64 .x25 = x.ciphertextA ∧
         s1.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         s1.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq s1 s0) ∧
        (P1 ⊢
          (sp0 ↦₆₄ x.ciphertextA) ∗
          ((sp0 + 0x08#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
          ((sp0 + 0x10#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 + 0x18#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 + 0x20#64) ↦₆₄ x.pqRatchetA) ∗
          ((sp0 + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          ((sp0 - 344#64) ↦₆₄ 32#64) ∗
          ((sp0 - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          newSavedRegs sp0 s0)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp] using hsp_align
  subst hsp
  simp only [arm64_norm] at hx1 hx2 hx4 hx5 hx6 hx7 hx8
  unfold newSavedRegs
  cells_unfold
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  new_fetches_range b (Rust.withPanics ext) 0x00 0x50
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · rw [← hx6, ← hx7]
    simp only [State.spAligned, wp_norm, arm64_norm, *]
  · exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

theorem new_prologue_wp {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (x : SignalMessageNewGhost) (sp0 w368 w360 w352 w344 w328 : BitVec 64) (w332 : BitVec 32)
    (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : s0.spAligned = true)
    (hx1 : s0.readReg64 .x1 = x.macKeyA)
    (hx2 : s0.readReg64 .x2 = 32#64)
    (hx4 : s0.readReg64 .x4 = x.remA)
    (hx5 : s0.readReg64 .x5 = x.senderRatchetKeyA)
    (hx6 : (s0.readReg64 .x6).setWidth 32 = x.counter)
    (hx7 : (s0.readReg64 .x7).setWidth 32 = x.previousCounter)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 84#64) s0
      ((sp0 ↦₆₄ x.ciphertextA) ∗
       ((sp0 + 0x08#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
       ((sp0 + 0x10#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 + 0x18#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 + 0x20#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
       ((sp0 - 368#64) ↦₆₄ w368) ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗
       ((sp0 - 352#64) ↦₆₄ w352) ∗
       ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗
       ((sp0 - 328#64) ↦₆₄ w328) ∗
       cells (sp0 - 96#64) 12)
      (fun s1 P1 =>
        (s1.sp = sp0 - 416#64 ∧
         s1.spAligned = true ∧
         s1.readReg64 .x3 = s0.readReg64 .x3 ∧
         s1.readReg64 .x4 = x.remA ∧
         s1.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         s1.readReg64 .x20 = x.senderRatchetKeyA ∧
         s1.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         s1.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         s1.readReg64 .x24 = x.ret ∧
         s1.readReg64 .x25 = x.ciphertextA ∧
         s1.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         s1.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq s1 s0) ∧
        (P1 ⊢
          (sp0 ↦₆₄ x.ciphertextA) ∗
          ((sp0 + 0x08#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
          ((sp0 + 0x10#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 + 0x18#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 + 0x20#64) ↦₆₄ x.pqRatchetA) ∗
          ((sp0 + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          ((sp0 - 344#64) ↦₆₄ 32#64) ∗
          ((sp0 - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          newSavedRegs sp0 s0)) :=
  new_prologue_wp_ext x sp0 w368 w360 w352 w344 w328 w332 s0 hpc hrun hsp hsp_align
    hx1 hx2 hx4 hx5 hx6 hx7 hx8

/-! ## `addresses` and `PublicKey::serialize` (`+0x054..+0x07c / +0x0f0`) -/

def not_satisfies_false_sepConj2 {α : Sort*} {m : Memory} {P Q : SepProp}
    (h : m ⊨ (⌜False⌝ ∗ P) ∗ Q) : α :=
  (not_satisfies_false_sepConj (show m ⊨ ⌜False⌝ ∗ (P ∗ Q) by rwa [sepConj_assoc] at h)).elim

theorem pull_pure_alloc_oom (P1 P2 F : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ ⌜φ⌝) ∗ F = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ F) := by ac_rfl

theorem pull_pure_alloc_ok (P1 P2 P3 F : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ (⌜φ⌝ ∗ P3)) ∗ F = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ F) := by ac_rfl

theorem stackAt_serializeAddresses_to_publicKeySerialize (sp : BitVec 64) :
    stackAt sp serializeAddressesStack =
      stackAt sp publicKeySerializeStack ∗ memRegion (sp - 4224#64) 96 := by
  unfold stackAt serializeAddressesStack publicKeySerializeStack
  rw [memRegion_split' (b := sp - 4224#64) (b' := sp - 4128#64) (n := 96) (k := 4128)
    (by decide) (bv_sub_add_lit sp 4224 96).symm (by decide), sepConj_comm]

theorem memRegion_24_split_8_16 (a : BitVec 64) :
    memRegion a 24 = (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) 16 := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) rfl rfl (by decide),
    memRegion_eight a]

theorem new_addr_and_rk_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPk : PublicKeySerializeOkExt b A ext)
    (hSerAddr : SerializeAddressesOkExt b A uuidTryParse ext)
    (x : SignalMessageNewGhost) (sp0 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx3 : s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64))
    (hloc_ne : x.loc.isSome → x.locA ≠ 0#64)
    (hx4 : s.readReg64 .x4 = x.remA)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 240#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 124#64)
      s
      (optAddrAt A x.locA x.loc ∗
       protocolAddressAt A x.rem x.remA ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       memRegion (sp0 - 312#64) 24 ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          optAddrAt A x.locA x.loc ∗
          protocolAddressAt A x.rem x.remA ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          optSerializeAddressesAt A (sp0 - 312#64) (x.addresses uuidTryParse) ∗
          boxU8Buf A (sm.readReg64 .x28) x.senderRatchetKey.serialize ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hpk := publicKeySerialize_ok_at_new_ext hPk
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx3 hx4 hx19 hx20 hx22 hx23 hx24 hx25 hx27 hx29
  cases hloc : x.loc with
  | none =>
    simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hx3
    simp only [hloc, optAddrAt, SignalMessageNewGhost.addresses, Option.bind_none, emp_sepConj,
      memRegion_24_split_8_16 (sp0 - 312#64), bv_sub_add_lit sp0 312 8,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun w312 => ?_
    new_fetches_range b (Rust.withPanics ext) 0x54 0x54
    new_fetches_range b (Rust.withPanics ext) 0xd4 0xec
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call
      (x := ⟨x.senderRatchetKeyA, x.senderRatchetKey⟩)
      (F := protocolAddressAt A x.rem x.remA ∗
            ((sp0 - 312#64) ↦₆₄ noneCap) ∗
            memRegion (sp0 - 304#64) 16 ∗
            memRegion (sp0 - 416#64 - 4624#64) 496)
      hpk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ R' hm => by
        simpa only [publicKeySerializeSpec, allocFailedIn, State.trace_setPC, State.trace_writeReg64,
          State.trace_setMem, arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_publicKeySerialize (sp0 - 416#64)] at hm
      simp only [publicKeySerializeSpec, noneCap, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [publicKeySerializeSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1_1, htr1⟩ => ?_
    simp only [wp_norm, arm64_norm] at hx1_1 htr1
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hc : BitVec.ofNat 64 x.ciphertext.length = 0#64 <;>
        simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · rw [stackAt_computeMac_to_publicKeySerialize (sp0 - 416#64)]
      simp only [optSerializeAddressesAt, noneCap, hsp, bv_sub_add_lit sp0 312 8, arm64_norm]
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)
  | some l =>
    have hloc_ne' : x.locA ≠ 0#64 := hloc_ne (by simp [hloc])
    have hloc_beq : (x.locA == 0#64) = false := beq_eq_false_iff_ne.mpr hloc_ne'
    simp only [hloc, ↓reduceIte] at hx3
    simp only [hloc, optAddrAt, SignalMessageNewGhost.addresses, Option.bind_some]
    have hser := serializeAddresses_ok_at_new_ext hSerAddr
    new_fetches_range b (Rust.withPanics ext) 0x54 0x78
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call
      (x := ⟨sp0 - 312#64, x.locA, l, x.remA, x.rem⟩)
      (F := (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
            memRegion (sp0 - 416#64 - 4624#64) 400)
      hser (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ R' hm => by
        simpa only [serializeAddressesSpec, allocFailedIn, State.trace_setPC, State.trace_writeReg64,
          arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_serializeAddresses (sp0 - 416#64)] at hm
      simp only [serializeAddressesSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [serializeAddressesSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call
      (x := ⟨x.senderRatchetKeyA, x.senderRatchetKey⟩)
      (F := protocolAddressAt A l x.locA ∗
            protocolAddressAt A x.rem x.remA ∗
            optSerializeAddressesAt A (sp0 - 312#64) (serializeAddresses (serviceIdParse uuidTryParse) l x.rem) ∗
            memRegion (sp0 - 416#64 - 4224#64) 96 ∗
            memRegion (sp0 - 416#64 - 4624#64) 400)
      hpk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ R' hm => by
        simpa only [publicKeySerializeSpec, htr1, allocFailedIn, State.trace_setPC,
          State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_serializeAddresses_to_publicKeySerialize] at hm
      simp only [publicKeySerializeSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [publicKeySerializeSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
    simp only [wp_norm, arm64_norm, htr1] at hx1_2 htr2
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hc : BitVec.ofNat 64 x.ciphertext.length = 0#64 <;>
        simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · rw [stackAt_computeMac_to_serializeAddresses (sp0 - 416#64),
        stackAt_serializeAddresses_to_publicKeySerialize (sp0 - 416#64)]
      simp only [hsp1, arm64_norm]
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

theorem new_addr_and_rk_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hPk : PublicKeySerializeOk b C A ctl abs)
    (hSerAddr : SerializeAddressesOk b C A ctl uuidTryParse abs)
    (x : SignalMessageNewGhost) (sp0 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx3 : s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64))
    (hloc_ne : x.loc.isSome → x.locA ≠ 0#64)
    (hx4 : s.readReg64 .x4 = x.remA)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 240#64
       else
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 124#64)
      s
      (optAddrAt A x.locA x.loc ∗
       protocolAddressAt A x.rem x.remA ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       memRegion (sp0 - 312#64) 24 ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          optAddrAt A x.locA x.loc ∗
          protocolAddressAt A x.rem x.remA ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          optSerializeAddressesAt A (sp0 - 312#64) (x.addresses uuidTryParse) ∗
          boxU8Buf A (sm.readReg64 .x28) x.senderRatchetKey.serialize ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_addr_and_rk_wpp_ext hPk hSerAddr x sp0 s hpc hrun hsp hsp_align hx3 hloc_ne hx4
    hx19 hx20 hx22 hx23 hx24 hx25 hx27 hx29

/-! ## `ciphertext` copy (`+0x07c / +0x0f0 → +0x0a8 / +0x0fc`) -/

/-- Heap part of an exact-capacity `Vec<u8>` buffer before its 24-byte header is stored on stack. -/
def signalMessageNew_vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜cap = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    if cap = 0#64 then emp
    else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)

theorem vecU8At_of_vecU8Buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ cap) ∗ signalMessageNew_vecU8Buf A cap ptr bs ⊢
    vecU8At A v cap ptr bs := by
  unfold signalMessageNew_vecU8Buf vecU8At vecHeader
  simp only [arm64_norm]
  refine Entails.pure_left fun ⟨hcap, hlt, hne⟩ => ?_
  have hcap_nat : cap.toNat = bs.length := by
    rw [hcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [← hcap]
  by_cases hc : cap = 0#64
  · have hbs0 : bs.length = 0 := by rw [← hcap_nat, hc, BitVec.toNat_zero]
    simp only [hc, show (0#64 : BitVec 64) = 0 from rfl, ↓reduceIte, hbs0, arm64_norm]
    refine Entails.pure_right hne ?_
    exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)
  · have hc0 : cap ≠ 0 := hc
    simp only [hc, hc0, ↓reduceIte, hcap_nat, Nat.sub_self, memRegion_zero, sepConj_emp, arm64_norm]
    refine Entails.pure_right ⟨Nat.le_refl _, hlt, hne⟩ ?_
    exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

theorem vecU8Buf_eq_boxU8Buf (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length < 2 ^ 63) :
    signalMessageNew_vecU8Buf A (BitVec.ofNat 64 bs.length) ptr bs = boxU8Buf A ptr bs := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hbs : bs = []
  · subst hbs
    simp [signalMessageNew_vecU8Buf, boxU8Buf]
  · have hcap0 : BitVec.ofNat 64 bs.length ≠ 0#64 := by
      intro h
      have ht := congrArg BitVec.toNat h
      rw [htoNat, BitVec.toNat_zero] at ht
      exact hbs (List.eq_nil_of_length_eq_zero ht)
    have hpure : (bs.length < 2 ^ 63 ∧ ptr ≠ 0#64) = (ptr ≠ 0#64 ∧ bs.length < 2 ^ 63) :=
      propext ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h1, h2⟩⟩
    simp only [signalMessageNew_vecU8Buf, boxU8Buf, hcap0, hbs, ↓reduceIte, true_and, hpure]

theorem new_ct_copy_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : SignalMessageNewGhost) (sp0 rkPtr w400 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 240#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 124#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 252#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 168#64)
      s
      (((sp0 - 400#64) ↦₆₄ w400) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          signalMessageNew_vecU8Buf A (BitVec.ofNat 64 x.ciphertext.length) (sm.readReg64 .x26) x.ciphertext ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hx29
  by_cases hct0 : BitVec.ofNat 64 x.ciphertext.length = 0#64
  · simp only [hct0, ↓reduceIte] at hpc
    new_fetches_range b (Rust.withPanics ext) 0xf0 0xf8
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;>
        simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · unfold signalMessageNew_vecU8Buf
      simp only [hct0, ↓reduceIte, sepConj_emp, arm64_norm]
      refine Entails.pure_right (by omega) ?_
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)
  · simp only [hct0, ↓reduceIte] at hpc
    have hct_pos : 0 < x.ciphertext.length := by
      by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hct0
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hct_msb : (BitVec.ofNat 64 x.ciphertext.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hct_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hshim := NewPrologueCallees.new_shim_ok_ext hA
    have halloc := NewPrologueCallees.new_alloc_ok_ext hA
    have hmemcpy := NewPrologueCallees.new_memcpy_ok_ext hA
    have ho864 := @oom_at_864_ext b ext
    new_fetches_range b (Rust.withPanics ext) 0x7c 0xa4
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ()) (F := ((sp0 - 400#64) ↦₆₄ w400) ∗
        (x.ciphertextA ↦ₛ x.ciphertext) ∗ A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp only [noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [noAllocShimSpec]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := (x.ciphertext.length, 1))
      (F := ((sp0 - 400#64) ↦₆₄ w400) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
            memRegion (sp0 - 416#64 - 4624#64) 528)
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)] at hm
      simp only [rustAllocSpec, LayoutOk,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    by_cases hoom : sf2.readReg64 .x0 = 0#64
    · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
      refine SepWPp.pure_elim fun htr2 => ?_
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom
      apply SepWPp.of_sepWP (mid := entry + bv% (2148))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      exact ho864 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
    · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
      refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.ciphertextA, x.ciphertext⟩)
        (F := ((sp0 - 400#64) ↦₆₄ w400) ∗
              A.live (sf2.readReg64 .x0) x.ciphertext.length 1 ∗
              A.pool ∗ stackAt sf2.sp allocHookStack ∗
              memRegion (sp0 - 416#64 - 4624#64) 528)
        hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp only [framelessMemcpySpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
      simp only [framelessMemcpySpec, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
      simp only [wp_norm, arm64_norm, htr2] at hx0_3 htr3
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;>
          simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
      · simp only [State.spAligned, wp_norm, arm64_norm, *]
      · unfold signalMessageNew_vecU8Buf
        have h26_eq : sf3.readReg64 (Reg.gpr 26#5) = sf2.readReg64 (Reg.gpr 0#5) := by
          simp only [wp_norm, arm64_norm, *]
        rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)]
        simp only [hct0, ↓reduceIte, h26_eq, hsp2, arm64_norm]
        refine Entails.pure_right ⟨by omega, hoom⟩ ?_
        exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

theorem new_ct_copy_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : SignalMessageNewGhost) (sp0 rkPtr w400 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 240#64
       else
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 124#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 252#64
       else
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 168#64)
      s
      (((sp0 - 400#64) ↦₆₄ w400) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          signalMessageNew_vecU8Buf A (BitVec.ofNat 64 x.ciphertext.length) (sm.readReg64 .x26) x.ciphertext ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_ct_copy_wpp_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) x sp0 rkPtr w400
    hct_bound s hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hx29

/-! ## `pq_ratchet` copy (`+0x0a8 / +0x0fc → +0x100`) -/

/-- Heap part of `pq_ratchet: Option<Vec<u8>>` before its 24-byte header `(cap, ptr, len)` is
stored on stack at `sp0 - 240#64`:
* when `pq = []`, `cap = noneCap` (`-1`);
* when `pq ≠ []`, `cap = BitVec.ofNat 64 pq.length > 0`, `ptr ≠ 0`, and `ptr` owns a live
  `pq.length`-byte heap buffer containing `pq`. -/
def optPqBuf (A : RustAlloc) (cap ptr : BitVec 64) (pq : List (BitVec 8)) : SepProp :=
  if pq.isEmpty then
    ⌜cap = noneCap⌝ ∗ emp
  else
    ⌜cap = BitVec.ofNat 64 pq.length ∧ 0 < pq.length ∧ pq.length < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      A.live ptr pq.length 1 ∗ (ptr ↦ₛ pq)

theorem optVecU8At_of_optPqBuf (A : RustAlloc) (v cap ptr : BitVec 64) (pq : List (BitVec 8)) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 pq.length) ∗
      optPqBuf A cap ptr pq ⊢
    optVecU8At A ⟨cap, ptr⟩ v (if pq.isEmpty then none else some pq) := by
  unfold optPqBuf
  by_cases hpq : pq.isEmpty
  · simp only [hpq, ↓reduceIte, optVecU8At, sepConj_emp, arm64_norm]
    refine Entails.pure_left fun hcap => ?_
    subst hcap
    refine sepConj_mono_right ?_
    rw [memRegion_16_eq_cells2 (v + 8#64), BitVec.add_assoc, show 8#64 + 8#64 = 16#64 by rfl]
    exact sepConj_mono (Entails.sepExists_intro ptr)
      (Entails.sepExists_intro (BitVec.ofNat 64 pq.length))
  · simp only [hpq, Bool.false_eq_true, ↓reduceIte, optVecU8At, arm64_norm]
    refine Entails.pure_left fun ⟨hcap, hpos, hlt, hne⟩ => ?_
    have hcap_nat : cap.toNat = pq.length := by
      rw [hcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hcap_ne0 : cap ≠ 0 := by
      intro hc; rw [show cap = 0#64 from hc, BitVec.toNat_zero] at hcap_nat; omega
    unfold vecU8At vecHeader
    simp only [hcap_ne0, ↓reduceIte, hcap_nat, Nat.sub_self, memRegion_zero, sepConj_emp, arm64_norm]
    refine Entails.pure_right ⟨Nat.le_refl _, hlt, hne⟩ ?_
    exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)


theorem signalMessageNew_call_opt {α : Type} {prog : Program} {ret : BitVec 64}
    {oimg : Option Obj.Image} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hinv : OptCallInv oimg s)
    (hcall : subroutine_ok prog entry (specWithOptInv oimg spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, OptCallInv oimg sf →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  cases oimg with
  | none =>
    exact SepWPp.call_wpp hcall hpc hrun hsp hlr (x := x) (F := F)
      (fun R hm => by
        dsimp only [specWithOptInv, OptCallInv]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨trivial, hpre R hm⟩)
      (fun sf code R' hex hpost => hexit sf code R' hex hpost)
      (fun sf hpan _ => hpanic sf hpan)
      (fun sf hpcm hrunm hspm hcsm => hnext sf trivial hpcm hrunm hspm hcsm)
      (fun sf R' hoom_s hpost => (hoom sf _ hoom_s hpost).elim)
  | some img =>
    exact SepWPp.call_wpp_frozen hcall hinv.1 hinv.2 hpc hrun hsp hlr (x := x) (F := F)
      (fun R hm => by
        dsimp only [specWithOptInv, OptCallInv]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hinv, hpre R hm⟩)
      (fun sf code R' hex hpost => hexit sf code R' hex hpost)
      (fun sf hpan _ => hpanic sf hpan)
      (fun sf hpcm hrunm hspm hcsm hfz hsym => hnext sf ⟨hfz, hsym⟩ hpcm hrunm hspm hcsm)
      (fun sf R' hoom_s hpost => (hoom sf _ hoom_s hpost).elim)

section FnOffShield
attribute [local irreducible] _root_.Arm64.Program.fnOff

theorem new_pq_copy_wpp_opt {oimg : Option Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {hookStack : Nat}
    (hbnd : hookStack + 528 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (specWithOptInv oimg (rustAllocSpecWithStack A hookStack)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
      (specWithOptInv oimg (memcpySpecWithStack hookStack)))
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hinv : OptCallInv oimg s)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 252#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 168#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 256#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) (hookStack + 528))
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          optPqBuf A (sm.readReg64 .x9) (sm.readReg64 .x25) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) (hookStack + 528)))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29
  by_cases hpq0 : BitVec.ofNat 64 x.pqRatchet.length = 0#64
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_empty : x.pqRatchet.isEmpty = true := by
      have h := congrArg BitVec.toNat hpq0
      simp only [BitVec.toNat_ofNat] at h
      exact List.isEmpty_iff.mpr (List.eq_nil_of_length_eq_zero (by omega))
    new_fetches_range b (Rust.withPanics ext) 0xfc 0xfc
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · unfold optPqBuf
      simp only [hpq_empty, ↓reduceIte, sepConj_emp, arm64_norm]
      refine Entails.pure_right rfl ?_
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_pos : 0 < x.pqRatchet.length := by
      by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hpq0
    have hpq_nonempty : x.pqRatchet.isEmpty = false := by
      cases h : x.pqRatchet <;> simp_all
    have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpq_msb : (BitVec.ofNat 64 x.pqRatchet.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hpq_toNat]
      exact Nat.testBit_lt_two_pow (by omega)

    have ho858 := @oom_at_858_ext b ext
    new_fetches_range b (Rust.withPanics ext) 0xa8 0xd0
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv0
    refine signalMessageNew_call_opt (x := ())
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
            (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ A.pool ∗
            memRegion (sp0 - 416#64 - (BitVec.ofNat 64 (hookStack + 528))) 528)
      hinv0 hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [signalMessageNew_stackAt_split_bottom (sp0 - 416#64) hookStack 528 hbnd] at hm
      simp only [shimSpecWithStack, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hinv1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [shimSpecWithStack, sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv1'
    refine signalMessageNew_call_opt (x := (x.pqRatchet.length, 1))
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗ (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
            memRegion (sp0 - 416#64 - (BitVec.ofNat 64 (hookStack + 528))) 528)
      hinv1' halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp only [rustAllocSpecWithStack, LayoutOk,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hinv2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    by_cases hoom : sf2.readReg64 .x0 = 0#64
    · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpecWithStack, hoom0, ↓reduceIte, pull_pure_alloc_oom]
      refine SepWPp.pure_elim fun htr2 => ?_
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom
      apply SepWPp.of_sepWP (mid := entry + bv% (2136))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      exact ho858 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
    · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpecWithStack, hoom0, ↓reduceIte, pull_pure_alloc_ok]
      refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
      apply SepWPp.of_sepWP_optImage (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) hinv2
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hinv2'
      refine signalMessageNew_call_opt (x := ⟨sf2.readReg64 .x0, x.pqRatchetA, x.pqRatchet⟩)
        (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
              A.live (sf2.readReg64 .x0) x.pqRatchet.length 1 ∗
              A.pool ∗
              memRegion (sp0 - 416#64 - (BitVec.ofNat 64 (hookStack + 528))) 528)
        hinv2' hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp only [memcpySpecWithStack, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 _ hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
      simp only [memcpySpecWithStack, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
      simp only [wp_norm, arm64_norm, htr2] at hx0_3 htr3
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · simp only [State.spAligned, wp_norm, arm64_norm, *]
      · unfold optPqBuf
        have h25_eq : sf3.readReg64 (Reg.gpr 25#5) = sf2.readReg64 (Reg.gpr 0#5) := by
          simp only [wp_norm, arm64_norm, *]
        rw [signalMessageNew_stackAt_split_bottom (sp0 - 416#64) hookStack 528 hbnd]
        simp only [hpq_nonempty, Bool.false_eq_true, ↓reduceIte, hsp2,
          h25_eq, arm64_norm]
        refine Entails.pure_right ⟨hpq_pos, by omega, hoom⟩ ?_
        exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)


end FnOffShield

theorem new_pq_copy_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 252#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 168#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 256#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          optPqBuf A (sm.readReg64 .x9) (sm.readReg64 .x25) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_pq_copy_wpp_opt (oimg := none) (hookStack := allocHookStack) (by decide)
    (shim_opt_of_base hA (by fnoff_eq))
    (alloc_opt_of_base hA (by fnoff_eq))
    (memcpy_opt_of_base hA (by fnoff_eq))
    x sp0 rkPtr ctCopyPtr hpq_bound s trivial
    hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29

theorem new_pq_copy_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 252#64
       else
        (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 168#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 256#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          optPqBuf A (sm.readReg64 .x9) (sm.readReg64 .x25) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_pq_copy_wpp_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) x sp0 rkPtr ctCopyPtr
    hpq_bound s hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29

/-! ## Extended-hook (`extHookStack`) segment lemmas -/

theorem stackAt_serializeAddressesX_to_publicKeySerializeX (sp : BitVec 64) :
    stackAt sp serializeAddressesStackX =
      stackAt sp publicKeySerializeStackX ∗ memRegion (sp - 16784#64) 368 := by
  rw [signalMessageNew_stackAt_split_bottom' sp serializeAddressesStackX publicKeySerializeStackX 368, sepConj_comm]
  rfl


theorem new_pq_copy_wpp_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 252#64
       else
        (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 168#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 256#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          optPqBuf A (sm.readReg64 .x9) (sm.readReg64 .x25) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStackX))
      (PanicAllocPost s) :=
  new_pq_copy_wpp_opt (oimg := some img) (hookStack := extHookStack) (by decide)
    (shim_opt_of_x hA (by fnoff_eq))
    (alloc_opt_of_x hA (by fnoff_eq))
    (memcpy_opt_of_x hA (by fnoff_eq))
    x sp0 rkPtr ctCopyPtr hpq_bound s ⟨hF, hsym⟩
    hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29

/-! ## Relocatable `[LibsignalPlacement]` segment lemmas (Block `63`) -/

theorem new_prologue_wp_placed [LibsignalPlacement] {H : LibsignalHooks}
    (x : SignalMessageNewGhost) (sp0 w368 w360 w352 w344 w328 : BitVec 64) (w332 : BitVec 32)
    (s0 : State)
    (hpc : s0.pc = (blkPl_63).base)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : s0.spAligned = true)
    (hx1 : s0.readReg64 .x1 = x.macKeyA)
    (hx2 : s0.readReg64 .x2 = 32#64)
    (hx4 : s0.readReg64 .x4 = x.remA)
    (hx5 : s0.readReg64 .x5 = x.senderRatchetKeyA)
    (hx6 : (s0.readReg64 .x6).setWidth 32 = x.counter)
    (hx7 : (s0.readReg64 .x7).setWidth 32 = x.previousCounter)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP ((blkPC_63).rebase (blkPl_63).base H) ((blkPl_63).base + 84#64) s0
      ((sp0 ↦₆₄ x.ciphertextA) ∗
       ((sp0 + 0x08#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
       ((sp0 + 0x10#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 + 0x18#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 + 0x20#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
       ((sp0 - 368#64) ↦₆₄ w368) ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗
       ((sp0 - 352#64) ↦₆₄ w352) ∗
       ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗
       ((sp0 - 328#64) ↦₆₄ w328) ∗
       cells (sp0 - 96#64) 12)
      (fun s1 P1 =>
        (s1.sp = sp0 - 416#64 ∧
         s1.spAligned = true ∧
         s1.readReg64 .x3 = s0.readReg64 .x3 ∧
         s1.readReg64 .x4 = x.remA ∧
         s1.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         s1.readReg64 .x20 = x.senderRatchetKeyA ∧
         s1.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         s1.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         s1.readReg64 .x24 = x.ret ∧
         s1.readReg64 .x25 = x.ciphertextA ∧
         s1.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         s1.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq s1 s0) ∧
        (P1 ⊢
          (sp0 ↦₆₄ x.ciphertextA) ∗
          ((sp0 + 0x08#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
          ((sp0 + 0x10#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 + 0x18#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 + 0x20#64) ↦₆₄ x.pqRatchetA) ∗
          ((sp0 + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          ((sp0 - 344#64) ↦₆₄ 32#64) ∗
          ((sp0 - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          newSavedRegs sp0 s0)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp] using hsp_align
  subst hsp
  simp only [arm64_norm] at hx1 hx2 hx4 hx5 hx6 hx7 hx8
  unfold newSavedRegs
  cells_unfold
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · rw [← hx6, ← hx7]
    simp only [State.spAligned, wp_norm, arm64_norm, *]
  · exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

theorem new_addr_and_rk_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpec A uuidTryParse)))
    (x : SignalMessageNewGhost) (sp0 : BitVec 64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx3 : s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64))
    (hloc_ne : x.loc.isSome → x.locA ≠ 0#64)
    (hx4 : s.readReg64 .x4 = x.remA)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64)
      s
      (optAddrAt A x.locA x.loc ∗
       protocolAddressAt A x.rem x.remA ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       memRegion (sp0 - 312#64) 24 ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          optAddrAt A x.locA x.loc ∗
          protocolAddressAt A x.rem x.remA ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          optSerializeAddressesAt A (sp0 - 312#64) (x.addresses uuidTryParse) ∗
          boxU8Buf A (sm.readReg64 .x28) x.senderRatchetKey.serialize ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx3 hx4 hx19 hx20 hx22 hx23 hx24 hx25 hx27 hx29
  cases hloc : x.loc with
  | none =>
    simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hx3
    simp only [hloc, optAddrAt, SignalMessageNewGhost.addresses, Option.bind_none, emp_sepConj,
      memRegion_24_split_8_16 (sp0 - 312#64), bv_sub_add_lit sp0 312 8,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun w312 => ?_
    apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 205) hcl
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl0
    refine signalMessageNew_call_placed
      (x := ⟨x.senderRatchetKeyA, x.senderRatchetKey⟩)
      (F := protocolAddressAt A x.rem x.remA ∗
            ((sp0 - 312#64) ↦₆₄ noneCap) ∗
            memRegion (sp0 - 304#64) 16 ∗
            memRegion (sp0 - 416#64 - 4624#64) 496)
      hcl0 hPk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ R' hm => by
        simpa only [publicKeySerializeSpec, allocFailedIn, State.trace_setPC, State.trace_writeReg64,
          State.trace_setMem, arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_publicKeySerialize (sp0 - 416#64)] at hm
      simp only [publicKeySerializeSpec, noneCap, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 _ hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [publicKeySerializeSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1_1, htr1⟩ => ?_
    simp only [wp_norm, arm64_norm] at hx1_1 htr1
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hc : BitVec.ofNat 64 x.ciphertext.length = 0#64 <;>
        simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · rw [stackAt_computeMac_to_publicKeySerialize (sp0 - 416#64)]
      simp only [optSerializeAddressesAt, noneCap, hsp, bv_sub_add_lit sp0 312 8, arm64_norm]
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)
  | some l =>
    have hloc_ne' : x.locA ≠ 0#64 := hloc_ne (by simp [hloc])
    have hloc_beq : (x.locA == 0#64) = false := beq_eq_false_iff_ne.mpr hloc_ne'
    simp only [hloc, ↓reduceIte] at hx3
    simp only [hloc, optAddrAt, SignalMessageNewGhost.addresses, Option.bind_some]
    apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 61) hcl
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl0
    refine signalMessageNew_call_placed
      (x := ⟨sp0 - 312#64, x.locA, l, x.remA, x.rem⟩)
      (F := (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
            memRegion (sp0 - 416#64 - 4624#64) 400)
      hcl0 hSerAddr (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ R' hm => by
        simpa only [serializeAddressesSpec, allocFailedIn, State.trace_setPC, State.trace_writeReg64,
          arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_serializeAddresses (sp0 - 416#64)] at hm
      simp only [serializeAddressesSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hcl1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [serializeAddressesSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 205) hcl1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl1'
    refine signalMessageNew_call_placed
      (x := ⟨x.senderRatchetKeyA, x.senderRatchetKey⟩)
      (F := protocolAddressAt A l x.locA ∗
            protocolAddressAt A x.rem x.remA ∗
            optSerializeAddressesAt A (sp0 - 312#64) (serializeAddresses (serviceIdParse uuidTryParse) l x.rem) ∗
            memRegion (sp0 - 416#64 - 4224#64) 96 ∗
            memRegion (sp0 - 416#64 - 4624#64) 400)
      hcl1' hPk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ R' hm => by
        simpa only [publicKeySerializeSpec, htr1, allocFailedIn, State.trace_setPC,
          State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_serializeAddresses_to_publicKeySerialize] at hm
      simp only [publicKeySerializeSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 _ hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [publicKeySerializeSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
    simp only [wp_norm, arm64_norm, htr1] at hx1_2 htr2
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hc : BitVec.ofNat 64 x.ciphertext.length = 0#64 <;>
        simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · rw [stackAt_computeMac_to_serializeAddresses (sp0 - 416#64),
        stackAt_serializeAddresses_to_publicKeySerialize (sp0 - 416#64)]
      simp only [hsp1, arm64_norm]
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

theorem new_ct_copy_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    (x : SignalMessageNewGhost) (sp0 rkPtr w400 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64)
      s
      (((sp0 - 400#64) ↦₆₄ w400) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          signalMessageNew_vecU8Buf A (BitVec.ofNat 64 x.ciphertext.length) (sm.readReg64 .x26) x.ciphertext ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hx29
  by_cases hct0 : BitVec.ofNat 64 x.ciphertext.length = 0#64
  · simp only [hct0, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;>
        simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · unfold signalMessageNew_vecU8Buf
      simp only [hct0, ↓reduceIte, sepConj_emp, arm64_norm]
      refine Entails.pure_right (by omega) ?_
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)
  · simp only [hct0, ↓reduceIte] at hpc
    have hct_pos : 0 < x.ciphertext.length := by
      by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hct0
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hct_msb : (BitVec.ofNat 64 x.ciphertext.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hct_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have halloc := new_alloc_placed_ok h_alloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have ho864 := @oom_at_864_placed _ H h_panic
    apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ()) (F := ((sp0 - 400#64) ↦₆₄ w400) ∗
        (x.ciphertextA ↦ₛ x.ciphertext) ∗ A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp only [noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [noAllocShimSpec]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := (x.ciphertext.length, 1))
      (F := ((sp0 - 400#64) ↦₆₄ w400) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
            memRegion (sp0 - 416#64 - 4624#64) 528)
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)] at hm
      simp only [rustAllocSpec, LayoutOk,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    by_cases hoom : sf2.readReg64 .x0 = 0#64
    · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
      refine SepWPp.pure_elim fun htr2 => ?_
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom
      apply SepWPp.of_sepWP (mid := (blkPl_63).base + 2148#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      exact ho864 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
    · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
      refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
      apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.ciphertextA, x.ciphertext⟩)
        (F := ((sp0 - 400#64) ↦₆₄ w400) ∗
              A.live (sf2.readReg64 .x0) x.ciphertext.length 1 ∗
              A.pool ∗ stackAt sf2.sp allocHookStack ∗
              memRegion (sp0 - 416#64 - 4624#64) 528)
        hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp only [framelessMemcpySpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
      simp only [framelessMemcpySpec, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
      simp only [wp_norm, arm64_norm, htr2] at hx0_3 htr3
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done ?_ (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · by_cases hpq : BitVec.ofNat 64 x.pqRatchet.length = 0#64 <;>
          simp only [beq_iff_eq, ↓reduceIte, wp_norm, arm64_norm, *]
      · simp only [State.spAligned, wp_norm, arm64_norm, *]
      · unfold signalMessageNew_vecU8Buf
        have h26_eq : sf3.readReg64 (Reg.gpr 26#5) = sf2.readReg64 (Reg.gpr 0#5) := by
          simp only [wp_norm, arm64_norm, *]
        rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)]
        simp only [hct0, ↓reduceIte, h26_eq, hsp2, arm64_norm]
        refine Entails.pure_right ⟨by omega, hoom⟩ ?_
        exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

theorem new_pq_copy_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 256#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          optPqBuf A (sm.readReg64 .x9) (sm.readReg64 .x25) x.pqRatchet ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29
  by_cases hpq0 : BitVec.ofNat 64 x.pqRatchet.length = 0#64
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_empty : x.pqRatchet.isEmpty = true := by
      have h := congrArg BitVec.toNat hpq0
      simp only [BitVec.toNat_ofNat] at h
      exact List.isEmpty_iff.mpr (List.eq_nil_of_length_eq_zero (by omega))
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · unfold optPqBuf
      simp only [hpq_empty, ↓reduceIte, sepConj_emp, arm64_norm]
      refine Entails.pure_right rfl ?_
      exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_pos : 0 < x.pqRatchet.length := by
      by_contra hle; simp [Nat.le_zero.mp (Nat.not_lt.mp hle)] at hpq0
    have hpq_nonempty : x.pqRatchet.isEmpty = false := by
      cases h : x.pqRatchet <;> simp_all
    have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpq_msb : (BitVec.ofNat 64 x.pqRatchet.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hpq_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have halloc := new_alloc_placed_ok h_alloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have ho858 := @oom_at_858_placed _ H h_panic
    apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := ())
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
            (x.pqRatchetA ↦ₛ x.pqRatchet) ∗ A.pool ∗
            stackAt (sp0 - 416#64) computeMacStack)
      hshim (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      simp only [noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [noAllocShimSpec]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.call (x := (x.pqRatchet.length, 1))
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗ (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
            memRegion (sp0 - 416#64 - 4624#64) 528)
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)] at hm
      simp only [rustAllocSpec, LayoutOk,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      refine ⟨⟨⟨0, rfl⟩, by omega⟩, ?_⟩
      exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    by_cases hoom : sf2.readReg64 .x0 = 0#64
    · have hoom0 : (sf2.readReg64 .x0 = 0) = True := eq_true hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]
      refine SepWPp.pure_elim fun htr2 => ?_
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom
      apply SepWPp.of_sepWP (mid := (blkPl_63).base + 2136#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      exact ho858 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
    · have hoom0 : (sf2.readReg64 .x0 = 0) = False := eq_false hoom
      simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]
      refine SepWPp.pure_elim fun ⟨halign_ptr, htr2⟩ => ?_
      have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
      apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := ⟨sf2.readReg64 .x0, x.pqRatchetA, x.pqRatchet⟩)
        (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
              A.live (sf2.readReg64 .x0) x.pqRatchet.length 1 ∗
              A.pool ∗ stackAt sf2.sp allocHookStack ∗
              memRegion (sp0 - 416#64 - 4624#64) 528)
        hmemcpy (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        simp only [framelessMemcpySpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        exact NewPrologueCallees.satisfies_of_sep_focus hm (by sep_focus)
      intro sf3 hpc3 hrun3 hsp3 hcs3
      rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
      simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
      simp only [framelessMemcpySpec, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
      simp only [wp_norm, arm64_norm, htr2] at hx0_3 htr3
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
      · simp only [State.spAligned, wp_norm, arm64_norm, *]
      · unfold optPqBuf
        have h25_eq : sf3.readReg64 (Reg.gpr 25#5) = sf2.readReg64 (Reg.gpr 0#5) := by
          simp only [wp_norm, arm64_norm, *]
        rw [stackAt_computeMac_to_allocHook (sp0 - 416#64)]
        simp only [hpq_nonempty, Bool.false_eq_true, ↓reduceIte, hsp2,
          h25_eq, arm64_norm]
        refine Entails.pure_right ⟨hpq_pos, by omega, hoom⟩ ?_
        exact NewPrologueCallees.entails_of_sep_focus (by sep_focus)

end CryptoVerification.LibsignalTripleRatchet
