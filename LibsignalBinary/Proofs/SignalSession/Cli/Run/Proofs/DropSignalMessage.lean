/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessage.Helpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Drop Glue Contract for `SignalMessage`

Defines `dropSignalMessageSpec` and lifts the exact-stack proof `dropSignalMessageRaw_ok` to
arbitrary stack budgets `32 + extHookStack ≤ stk ≤ 2 ^ 64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

abbrev cliDropSignalMessageName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>"

structure DropSignalMessageGhost where
  a : BitVec 64
  g : SignalMessageGhost
  m : SignalMessage

def dropSignalMessageSpec (A : RustAlloc) (stk : Nat) : Spec DropSignalMessageGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ signalMessageAt A x.g x.a x.m ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 120 ∗ A.pool ∗ stackAt s0.sp stk

private theorem cliDropSignalMessage_exact_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSignalMessageName)
      ((dropSignalMessageSpec A (32 + extHookStack)).inImage img) := by
  have hraw := DropSignalMessageHelpers.smDropRaw_exact_ok hA
  exact subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal =>
    hraw.mono_outcome (x.a, x.g, x.m) R s0 hpc hrun hpre hal fun _ hout => hout

theorem cliDropSignalMessage_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSignalMessageName)
      ((dropSignalMessageSpec A stk).inImage img) := by
  refine DropSignalMessageHelpers.subroutine_ok_frame_weaken
    (F := fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (32 + extHookStack)))
    (cliDropSignalMessage_exact_ok hA) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
  · intro x s0
    dsimp only [Spec.inImage, dropSignalMessageSpec]
    rw [DropSignalMessageHelpers.stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro x s0 sf
    dsimp only [Spec.inImage, dropSignalMessageSpec]
    rw [DropSignalMessageHelpers.stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro x s0 sf
    dsimp only [Spec.inImage, dropSignalMessageSpec]
    exact Entails.pure_left False.elim

example : libsignalSessionCode.fnOff cliDropSignalMessageName =
    num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>"

end CryptoVerification.SignalSession.Cli.RunProofs
