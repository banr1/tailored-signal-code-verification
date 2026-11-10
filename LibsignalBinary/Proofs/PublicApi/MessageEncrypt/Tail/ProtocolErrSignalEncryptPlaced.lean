/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommon
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlaced
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable (`[LibsignalPlacement]`) T5 Signal Tail (`tailSignalEncryptErr`)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

theorem signal_placed_run [LibsignalPlacement] {Hk : LibsignalHooks}
    (w0 w1 w2 w3 w4 w5 sp : BitVec 64) (s : State)
    (hpc : s.pc = encEntryPlaced + 0xc14#64) (hrun : s.status = .Running)
    (hssp : s.sp = sp) (hal : (sp &&& 15#64 == 0#64) = true)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64)
    (hregs : tailRegs w0 w1 w2 sp s) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x46c#64) s
      (memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + 0xb00#64) [w3, w4, w5])
      (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ tailRegs w0 w1 w2 sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (sp + 0xb00#64) 24) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  unfold encEntryPlaced at hpc ⊢
  rw [memRegion_24_eq]
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [lsProg_198, ite_true]
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

theorem tailSignalEncryptErrPlaced [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {H : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0xc14#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0xb00 [w3, w4, w5]) ∗ H) R s0 s)
    (hT1 : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s' →
      EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
        (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
        R s0 s' →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s' (fun _ => False)) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) := by
  refine segExit_placed_of_run hm (fun hL => ?_) hT1
  refine encTail_placed_run (C := C) (Hk := Hk)
    (Act := fun sp => memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + 0xb00#64) [w3, w4, w5])
    (Fr := fun sp => (memRegion (sp + 0x46a#64) 0x566 ∗ memRegion (sp + 0x9e8#64) 0x118 ∗
      memRegion (sp + 0xb18#64) 0x68) ∗ dropRecordBase A sp scratch g rec ot ∗ cmSlotAt A sp none ∗ H)
    (Act' := fun sp => words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ memRegion (sp + 0xb00#64) 24)
    hs ?_ ?_ ?_ hL
  · intro sp
    refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, pollWith_b00_eq]
    sep_ac_rfl
  · intro sp
    refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, pollWith_9d0_eq]
    sep_ac_rfl
  · intro sp hpc hmeta hregs hsp
    obtain ⟨hrun, hssp, _, hspal, hx29, -⟩ := hmeta
    have hal : (sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned, hssp, hsp] using hspal
    exact signal_placed_run w0 w1 w2 w3 w4 w5 sp s hpc hrun (hssp.trans hsp.symm) hal
      (by rw [hx29, hsp]; bv_omega) hregs

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
