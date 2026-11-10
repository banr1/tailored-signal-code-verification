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
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlaced
import ProofLib.SepLogic.WP.Apply

/-!
# Relocatable (`[LibsignalPlacement]`) CM Drop Tail (`tailCmDrop`)
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

theorem cmDrop_placed_run [LibsignalPlacement] {A : RustAlloc} {Hk : LibsignalHooks}
    (hdrop : subroutine_ok (lsProg_198 Hk) (lsmpl.base 135)
      (StoreKit.withLsRoCl lsmpl (cmDropSpec A)))
    (w0 w1 w2 : BitVec 64) (m : CiphertextMessage) (s : State)
    (hpc : s.pc = encEntryPlaced + 0xd40#64) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hregs : tailRegs w0 w1 w2 s.sp s) :
    SepWP (lsProg_198 Hk) (encEntryPlaced + 0x46c#64) s
      (apiEncResultAt A (s.sp + 0x370#64) (.ok m) ∗ A.pool ∗ stackAt s.sp (allocHookStack + 0x40))
      (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ tailRegs w0 w1 w2 s.sp s' ∧
        ∀ m F, (m ⊨ P ∗ F) →
          (m ⊨ (memRegion (s.sp + 0x370#64) 248 ∗ A.pool ∗
            stackAt s.sp (allocHookStack + 0x40)) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  obtain ⟨hro, hcl⟩ := hcrl
  have hcall : subroutine_ok ((blkPC_198).rebase (blkPl_198).base Hk) (lsmpl.base 135)
      (StoreKit.withLsRoCl lsmpl (cmDropSpec A)) := by
    simpa only [lsProg_198, ite_true] using hdrop
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_198, ite_true]
  wp_steps
  wp_apply
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], ?_,
      fun _ _ hm => hm⟩
  unfold tailRegs
  simp only [wp_norm, arm64_norm, *]

theorem tailCmDropPlaced [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hdrop : subroutine_ok (lsProg_198 Hk) (lsmpl.base 135)
      (StoreKit.withLsRoCl lsmpl (cmDropSpec A)))
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {H : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {m : CiphertextMessage}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot (some m) (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
      R s0 s)
    (hT1 : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s' →
      EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
        (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
        R s0 s' →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s' (fun _ => False)) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) := by
  have hn : allocHookStack + 0x40 ≤ encSubStack := by decide
  refine segExit_placed_of_run hm (fun hL => ?_) hT1
  refine encTail_placed_run_withEncCommon (C := C) (Hk := Hk)
    (Act := apiEncResultAt A (s0.sp - 0xbe0#64 + 0x370#64) (.ok m) ∗ A.pool ∗
      stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
    (Act' := memRegion (s0.sp - 0xbe0#64 + 0x370#64) 248 ∗ A.pool ∗
      stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
    (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x350#64) 0x20 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x468#64) 1) ∗
      dropRecordBase A (s0.sp - 0xbe0#64) scratch g rec ot ∗ pollWith (s0.sp - 0xbe0#64) 0x9d0 [w3, w4, w5] ∗
      H ∗ encCommonPlacedFr A ctl x (x.draws S answers) s0 (allocHookStack + 0x40))
    hs ?_ ?_ ?_ hL
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, encCommonPlaced_eq A ctl x (x.draws S answers) s0 _ hn]
    simp only [cmSlotAt]
    sep_ac_rfl
  · refine Entails.of_eq ?_
    rw [dropRecordSlots_eq, encCommonPlaced_eq A ctl x (x.draws S answers) s0 _ hn, cmSlot_none_eq]
    sep_ac_rfl
  · intro hpc hmeta hregs
    obtain ⟨hrun, hssp, _, hspal, _, _, hcrl, _⟩ := hmeta
    rw [← hssp] at hregs ⊢
    exact cmDrop_placed_run hdrop w0 w1 w2 m s hpc hrun hspal hcrl hregs

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
