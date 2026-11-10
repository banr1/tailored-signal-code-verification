/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwned.Plain
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwned.WithStr
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwned.SessionNotFound

/-!
# Drop Glue Contract for Owned `SignalProtocolError`

Proves `RunDrop.DropSpeOwnedOk` for `core::ptr::drop_glue::<SignalProtocolError>` over plain,
string-carrying, `SessionNotFound`, and `.proto` error variants.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunDrop

section

set_option maxRecDepth 200000

private theorem cliDropSpeOwned_plain_ok_stk {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    {i : Nat} (hi : PlainSpeTag i) (a : BitVec 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (DropSpeOwnedHelpers.SpecAt ((dropSpeOwnedSpec A stk).inImage img) ⟨a, .plain i hi⟩) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine DropSpeProof.Helpers.subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (DropSpeOwnedHelpers.cliDropSpeOwned_plain_ok_x (A := A) himg hi a)
    (fun _ s0 => ?_)
    (fun _ s0 _ => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · simp only [Spec.inImage, dropSpeOwnedSpec, speOwnedAt,
      DropSpeOwnedHelpers.dropSpePlainSpecX,
      DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · simp only [Spec.inImage, dropSpeOwnedSpec,
      DropSpeOwnedHelpers.dropSpePlainSpecX,
      DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · simp only [Spec.inImage]
    exact Entails.pure_left nofun

private theorem cliDropSpeOwned_withStr_ok_stk {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    {i : Nat} (hi : StrSpeTag i) (a : BitVec 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (DropSpeOwnedHelpers.SpecAt ((dropSpeOwnedSpec A stk).inImage img)
        ⟨a, .withString i hi⟩) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine DropSpeProof.Helpers.subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (DropSpeOwnedHelpers.subroutine_ok_specialize
      (DropSpeOwnedHelpers.cliDropSpeOwned_withStr_ok_x himg hA) ⟨a, ⟨i, hi⟩⟩)
    (fun _ s0 => ?_)
    (fun _ s0 _ => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · simp only [Spec.inImage, dropSpeOwnedSpec,
      DropSpeOwnedHelpers.dropSpeWithStrSpecX,
      DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · simp only [Spec.inImage, dropSpeOwnedSpec,
      DropSpeOwnedHelpers.dropSpeWithStrSpecX,
      DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · simp only [Spec.inImage]
    exact Entails.pure_left nofun

private theorem cliDropSpeOwned_snf_ok_stk {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext)
    (stk : Nat) (hstk : 32 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (addr : AddrVal) (op : String) (a : BitVec 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (DropSpeOwnedHelpers.SpecAt ((dropSpeOwnedSpec A stk).inImage img)
        ⟨a, .sessionNotFound addr op⟩) := by
  have hstkX : dropSpeStackX ≤ stk := hstk
  refine DropSpeProof.Helpers.subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - dropSpeStackX))
    (DropSpeOwnedHelpers.subroutine_ok_specialize
      (DropSpeOwnedHelpers.cliDropSpeOwned_snf_ok_x himg hA) ⟨a, addr, op⟩)
    (fun _ s0 => ?_)
    (fun _ s0 _ => ?_)
    (fun _ _ _ => ?_)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)
  · simp only [Spec.inImage, dropSpeOwnedSpec,
      DropSpeOwnedHelpers.dropSpeSnfSpecX,
      DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · simp only [Spec.inImage, dropSpeOwnedSpec,
      DropSpeOwnedHelpers.dropSpeSnfSpecX,
      DropSpeProof.Helpers.stackAt_split_ge s0.sp hstkX hstk64]
    exact Entails.of_eq (by ac_rfl)
  · simp only [Spec.inImage]
    exact Entails.pure_left nofun

/-- Proves `RunDrop.DropSpeOwnedOk` for `core::ptr::drop_glue::<SignalProtocolError>` across all `SpeOwned` variants. -/
theorem cliDropSpeOwned_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    RunDrop.DropSpeOwnedOk img A ext := by
  intro stk hstk hstk64
  refine DropSpeOwnedHelpers.subroutine_ok_pointwise fun ⟨a, k⟩ => ?_
  cases k with
  | proto fnName e =>
    exact DropSpeOwnedHelpers.subroutine_ok_specialize
      (DropSpeProof.cliDropSpe_ok_stk himg hA stk hstk hstk64) ⟨a, fnName, e⟩
  | sessionNotFound addr op =>
    exact cliDropSpeOwned_snf_ok_stk himg hA stk hstk hstk64 addr op a
  | untrustedIdentity addr =>
    refine DropSpeProof.Helpers.subroutine_ok_frame_weaken
      (fun _ _ => emp)
      (cliDropSpeOwned_withStr_ok_stk himg hA stk hstk hstk64 (i := 12) (by decide) a)
      (fun _ _ => ?_)
      (fun _ _ _ => ?_)
      (fun _ _ _ => ?_)
      (fun _ _ _ _ => rfl)
      (fun _ _ _ => rfl)
    · simp only [Spec.inImage, dropSpeOwnedSpec, sepConj_emp]
      exact sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_left
            (DropSpeOwnedHelpers.untrustedIdentity_entails_withString12 A a addr)))
    · simp only [Spec.inImage, dropSpeOwnedSpec, sepConj_emp]
      exact Entails.refl _
    · simp only [Spec.inImage]
      exact Entails.pure_left nofun
  | badKemKeyType =>
    exact cliDropSpeOwned_plain_ok_stk (A := A) himg stk hstk hstk64 (i := 31) (by decide) a
  | badKemKeyLength =>
    exact cliDropSpeOwned_plain_ok_stk (A := A) himg stk hstk hstk64 (i := 33) (by decide) a
  | plain i hi =>
    exact cliDropSpeOwned_plain_ok_stk (A := A) himg stk hstk hstk64 hi a
  | withString i hi =>
    exact cliDropSpeOwned_withStr_ok_stk himg hA stk hstk hstk64 hi a

end

end CryptoVerification.SignalSession.Cli.RunProofs

namespace CryptoVerification.SignalSession.Cli.RunDrop

open Arm64 ProofLib CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000 in
theorem cliDropSpeOwned_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContractsX img A ext) :
    RunDrop.DropSpeOwnedOk img A ext :=
  RunProofs.cliDropSpeOwned_ok himg hA

end CryptoVerification.SignalSession.Cli.RunDrop
