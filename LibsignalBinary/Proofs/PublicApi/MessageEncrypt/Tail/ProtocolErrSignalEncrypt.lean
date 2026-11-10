/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `MessageEncrypt` `T5` Signal Error Tail (`tailSignalEncryptErr_ok`)

Steps `+0xc14..+0xc1c` and `+0xc6c..+0xc78`: copies staged error words `w3..w5` from `sp + 0xb00`
to `sp + 0x9d0` and branches to `tailDropRecord_ok` at `+0x46c`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

/-- Steps `+0xc14 → +0xc6c → +0x46c`, copying three 64-bit words from `sp + 0xb00` to
`sp + 0x9d0`. -/
theorem signal_run {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (w0 w1 w2 w3 w4 w5 sp : BitVec 64) (s : State)
    (hpc : s.pc = encEntry img + 0xc14#64) (hrun : s.status = .Running)
    (hssp : s.sp = sp) (hal : (sp &&& 15#64 == 0#64) = true)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64)
    (hregs : tailRegs w0 w1 w2 sp s) :
    SepWP (tripleRatchetProgAt img.base C ctl abs) (encEntry img + 0x46c#64) s
      (memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + 0xb00#64) [w3, w4, w5])
      (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ tailRegs w0 w1 w2 sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (sp + 0xb00#64) 24) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  dsimp only [encEntry] at hpc ⊢
  rw [entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg] at hpc ⊢
  have hfn : libsignalSessionCode.fnOff encryptWithStoresName = num% (ls_off% "session_message_encrypt") :=
    (ls_lemma% fnOff "session_message_encrypt")
  code_fetches_range CryptoVerification.libsignalSessionCode protocolErrBin img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_encrypt")) 3092 12
  code_fetches_range CryptoVerification.libsignalSessionCode protocolErrBin img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_encrypt")) 3180 12
  rw [memRegion_24_eq]
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [tripleRatchetProgAt] at *
  clear himg hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
  · unfold tailRegs
    simp only [wp_norm, arm64_norm, *]
  · intro m F hm
    have h := words64At_three_entails (sp + 0xb00#64) w3 w4 w5
    simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at h
    have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right h)))) hm
    simpa only [sepConj_assoc] using h2

open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Specializes `tailSignalEncryptErr_ok` given the `+0x46c` continuation `hT1`. -/
theorem tailSignalEncryptErr {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {H : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0xc14#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0xb00 [w3, w4, w5]) ∗ H) R s0 s)
    (hT1 : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s' →
      EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
        R s0 s' →
      SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s' (fun _ => False)) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  refine segExit_of_run hm (fun hL => ?_) hT1
  refine encTail_run (C := C) (abs := abs)
    (Act := fun sp => memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + 0xb00#64) [w3, w4, w5])
    (Fr := fun sp => (memRegion (sp + 0x46a#64) 0x566 ∗ memRegion (sp + 0x9e8#64) 0x118 ∗
      memRegion (sp + 0xb18#64) 0x68) ∗ dropRecordBase A sp scratch g rec ot ∗ cmSlotAt A sp none ∗ H)
    (Act' := fun sp => words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (sp + 0xb00#64) 24)
    hs ?_ ?_ ?_ hL
  · intro sp
    refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, pollWith_b00_eq]
    ac_rfl
  · intro sp
    refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, pollWith_9d0_eq]
    ac_rfl
  · intro sp hpc hmeta hregs hsp
    obtain ⟨hrun, hssp, _, hspal, hx29, -⟩ := hmeta
    have hal : (sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned, hssp, hsp] using hspal
    exact signal_run himg w0 w1 w2 w3 w4 w5 sp s hpc hrun (hssp.trans hsp.symm) hal
      (by rw [hx29, hsp]; bv_omega) hregs

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
