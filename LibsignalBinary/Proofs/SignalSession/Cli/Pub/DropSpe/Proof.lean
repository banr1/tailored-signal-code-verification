/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.Proof.Helpers

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.DropSpeProof

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters

theorem cliDropSpe_ok_x_proof {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img) :=
  Helpers.cliDropSpe_ok_x_proof_core himg hA

def dropSpeSpecStk (A : RustAlloc) (stk : Nat) : Spec DropSpeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ speAt A x.fnName x.a x.e ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 48 ∗ A.pool ∗ stackAt s0.sp stk

example : dropSpeStackX = 32 + extHookStack := rfl

theorem cliDropSpe_ok_stk {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecStk A stk).inImage img) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine Helpers.subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (cliDropSpe_ok_x_proof himg hA)
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · simp only [Spec.inImage, dropSpeSpecStk, dropSpeSpecX, Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · simp only [Spec.inImage, dropSpeSpecStk, dropSpeSpecX, Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · simp only [Spec.inImage]
    exact Entails.pure_left nofun

end CryptoVerification.SignalSession.Cli.DropSpeProof
