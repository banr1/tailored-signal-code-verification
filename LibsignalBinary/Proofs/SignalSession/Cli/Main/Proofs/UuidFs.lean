/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsParserTryParse

/-!
# In-Image `<uuid::Uuid>::try_parse` with `.keepsFs` and Stack Framing

Lifts `<uuid::Uuid>::try_parse` to `.keepsFs` with stack framing (`uuidTryParseStack ≤ hookStack ≤ 2 ^ 64`)
and `.inImage img` on `libsignalSessionCode`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops.UuidFs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

theorem uuidTryParse_okFs_F (b : BitVec 64) (hooks : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr uuidTryParseName)
      (uuidTryParseCodeSpec uuidTryParse).keepsFs :=
  uuidTryParse_okFs_impl b hooks

/-- Frames `(uuidTryParseCodeSpec uuidTryParse).keepsFs` (`0xC0` B) to any `uuidTryParseStack ≤ hookStack ≤ 2 ^ 64`. -/
theorem uuidTryParseWithStack_keepsFs_of_code {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h : subroutine_ok P addr (uuidTryParseCodeSpec uuidTryParse).keepsFs)
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (uuidTryParseStackSpec hookStack).keepsFs := by
  apply subroutine_ok_outcome_intro
  intro ⟨p, bs, out⟩ R s0 hpc hrun hpre hal
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗
        stackAt s0.sp uuidTryParseStack := by
    have h1 := stackAt_split_bottom s0.sp uuidTryParseStack (hookStack - uuidTryParseStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R
  have hpre' : s0.mem ⊨ (uuidTryParseCodeSpec uuidTryParse).keepsFs.pre (p, bs, out) s0 ∗ R' := by
    dsimp only [Spec.keepsFs, uuidTryParseStackSpec, uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine subroutine_ok.mono_outcome h (p, bs, out) R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.keepsFs, uuidTryParseStackSpec, uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · rcases hpan with ⟨_, hpan_sat⟩
    have h0 : (uuidTryParseCodeSpec uuidTryParse).keepsFs.onPanic (p, bs, out) s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · rcases hex with ⟨code, _, hex_sat⟩
    have h0 : (uuidTryParseCodeSpec uuidTryParse).keepsFs.onExit (p, bs, out) code s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hex_sat
    exact False.elim hex_sat.1
  · rcases hoom with ⟨_, hoom_sat⟩
    have h0 : (uuidTryParseCodeSpec uuidTryParse).keepsFs.onOom (p, bs, out) s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hoom_sat
    exact False.elim hoom_sat.1

theorem uuidTryParse_stack_keepsFs_inImage (img : Obj.Image)
    (hooks : String → Option (State → State))
    {hookStack : Nat}
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (libsignalSessionCode.rebase img.base hooks)
      ((libsignalSessionCode.rebase img.base hooks).fnAddr uuidTryParseName)
      ((uuidTryParseStackSpec hookStack).keepsFs.inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (uuidTryParseWithStack_keepsFs_of_code (uuidTryParse_okFs_F img.base hooks) hle hmax)

end CryptoVerification.SignalSession.Cli.MainHops.UuidFs
