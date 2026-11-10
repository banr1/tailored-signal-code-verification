/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApiRepr
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsg.Helpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Drop Glue Contract for `PreKeySignalMessage`

Defines `dropPreKeyMsgSpec` and lifts the exact-stack proof `dropPreKeyMsgExact_ok` to arbitrary
stack budgets `32 + extHookStack ≤ stk ≤ 2 ^ 64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli

abbrev cliDropPreKeyMsgName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>"

structure DropPreKeyMsgGhost where
  a : BitVec 64
  g : PreKeyMsgGhost
  m : PreKeySignalMessage

def dropPreKeyMsgSpec (A : RustAlloc) (stk : Nat) : Spec DropPreKeyMsgGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ preKeyMsgAt A x.g x.a x.m ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 248 ∗ A.pool ∗ stackAt s0.sp stk

theorem cliDropPreKeyMsg_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropPreKeyMsgName)
      ((dropPreKeyMsgSpec A stk).inImage img) := by
  refine DropPreKeyMsgHelpers.subroutine_ok_map_frame_weaken
    (fun x : DropPreKeyMsgGhost => (x.a, x.g, x.m))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (32 + extHookStack)))
    (DropPreKeyMsgHelpers.dropPreKeyMsgExact_ok hA) ?_ ?_ ?_ ?_
  · intro x s0
    dsimp only [Spec.inImage, dropPreKeyMsgSpec, DropPreKeyMsgHelpers.dropPreKeyMsgExactSpec]
    have hsplit : stackAt s0.sp stk =
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (32 + extHookStack)) ∗
          stackAt s0.sp (32 + extHookStack) := by
      have h := ProofLib.stackAt_split_bottom s0.sp (32 + extHookStack) (stk - (32 + extHookStack)) (by omega)
      rwa [Nat.add_sub_of_le hstk] at h
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)
  · intro x s0 sf
    dsimp only [Spec.inImage, dropPreKeyMsgSpec, DropPreKeyMsgHelpers.dropPreKeyMsgExactSpec]
    have hsplit : stackAt s0.sp stk =
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (32 + extHookStack)) ∗
          stackAt s0.sp (32 + extHookStack) := by
      have h := ProofLib.stackAt_split_bottom s0.sp (32 + extHookStack) (stk - (32 + extHookStack)) (by omega)
      rwa [Nat.add_sub_of_le hstk] at h
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)
  · intro _ _ _
    dsimp only [Spec.inImage]
    exact Entails.pure_left False.elim
  · intros; rfl

example : libsignalSessionCode.fnOff cliDropPreKeyMsgName =
    num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::PreKeySignalMessage>"

end CryptoVerification.SignalSession.Cli.RunProofs
