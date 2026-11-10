/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrStoreHook
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable (`[LibsignalPlacement]`) T5 Store Hook Error Tail (`tailStoreHookErr`)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon hiding words64At pollWith otrSlotAt cmSlotAt dropRecordSlots tailRegs EncTailV EncTail TailModel

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

theorem store_placed_run [LibsignalPlacement] {Hk : LibsignalHooks}
    (w0 w1 w2 w3 w4 w5 sp : BitVec 64) (s : State) (pcOff src : Nat)
    (hsel : (pcOff, src) = (0xc20, 0x970) ∨ (pcOff, src) = (0xe28, 0x990) ∨
      (pcOff, src) = (0xf2c, 0x9b0))
    (hpc : s.pc = encEntryPlaced + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hssp : s.sp = sp) (hal : (sp &&& 15#64 == 0#64) = true)
    (hregs : tailRegs w0 w1 w2 sp s) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xd40#64) s
      (memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + BitVec.ofNat 64 src) [w3, w4, w5])
      (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ tailRegs w0 w1 w2 sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
            memRegion (sp + BitVec.ofNat 64 src) 24) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  unfold encEntryPlaced at hpc ⊢
  rw [memRegion_24_eq]
  simp only [sepExists_sepConj_left]
  refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  dsimp only [lsProg_464, ite_true]
  rcases hsel with h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
  · simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
    · unfold tailRegs
      simp only [wp_norm, arm64_norm, *]
    · intro m F hm
      rw [memRegion_24_eq]
      simp only [words64At, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists, BitVec.add_assoc, BitVec.reduceAdd]
      exact ⟨w5, w4, w3, by simpa only [sepConj_assoc] using hm⟩

theorem tailStoreHookErrPlaced [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
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
    {m : CiphertextMessage} {pcOff src : Nat}
    (hsel : (pcOff, src) = (0xc20, 0x970) ∨ (pcOff, src) = (0xe28, 0x990) ∨
      (pcOff, src) = (0xf2c, 0x9b0))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + BitVec.ofNat 64 pcOff) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot (some m) (pollWith sp src [w3, w4, w5]) ∗ H) R s0 s)
    (hCm : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s' →
      EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
        (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A sp scratch g rec ot (some m) (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
        R s0 s' →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s' (fun _ => False)) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) := by
  have hsrc : 0x46a ≤ src ∧ src + 24 ≤ 0x9d0 := by
    rcases hsel with h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  refine segExit_placed_of_run hm (fun hL => ?_) hCm
  refine encTail_placed_run (C := C) (Hk := Hk)
    (Act := fun sp => memRegion (sp + 0x9d0#64) 24 ∗ words64At (sp + BitVec.ofNat 64 src) [w3, w4, w5])
    (Fr := fun sp => (memRegion (sp + 0x46a#64) (src - 0x46a) ∗
        memRegion (sp + BitVec.ofNat 64 (src + 24)) (0x9d0 - (src + 24)) ∗
        memRegion (sp + 0x9e8#64) 0x198) ∗ dropRecordBase A sp scratch g rec ot ∗ cmSlotAt A sp (some m) ∗ H)
    (Act' := fun sp => words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
      memRegion (sp + BitVec.ofNat 64 src) 24)
    hs ?_ ?_ ?_ hL
  · intro sp
    refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, pollWith_src_eq sp w3 w4 w5 src hsrc.2]
    sep_ac_rfl
  · intro sp
    refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, pollWith_9d0_eq', memRegion_46a_src sp src hsrc.1 hsrc.2]
    sep_ac_rfl
  · intro sp hpc hmeta hregs hsp
    obtain ⟨hrun, hssp, _, hspal, -⟩ := hmeta
    have hal : (sp &&& 15#64 == 0#64) = true := by
      simpa [State.spAligned, hssp, hsp] using hspal
    exact store_placed_run w0 w1 w2 w3 w4 w5 sp s pcOff src hsel hpc hrun (hssp.trans hsp.symm) hal
      hregs

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
