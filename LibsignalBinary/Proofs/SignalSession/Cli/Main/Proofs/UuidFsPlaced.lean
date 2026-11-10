/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsParserTryParsePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFs
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `<uuid::Uuid>::try_parse` with `.keepsFs` and Stack Framing

Relocatable (`[LibsignalPlacement]`, Block `252`) `.keepsFs` contract and stack-frame lifting
(`uuidTryParseStack ≤ hookStack ≤ 2 ^ 64`) for `<uuid::Uuid>::try_parse`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops.UuidFs

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

theorem uuidTryParse_placed_okFs_F [LibsignalPlacement] (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base hooks)
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs) :=
  uuidTryParse_placed_okFs_impl hooks

/-- Frames `withLsCodeLoaded pl (uuidTryParseCodeSpec uuidTryParse).keepsFs` (`0xC0` B) to any `uuidTryParseStack ≤ hookStack ≤ 2 ^ 64`. -/
theorem uuidTryParseWithStack_keepsFs_of_withLsCodeLoaded {pl : Obj.MultiPlacement}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h : subroutine_ok P addr (withLsCodeLoaded pl (uuidTryParseCodeSpec uuidTryParse).keepsFs))
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (withLsCodeLoaded pl (uuidTryParseStackSpec hookStack).keepsFs) := by
  intro ⟨p, bs, out⟩ R s0 hpc hrun hpre hal hL
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗
        stackAt s0.sp uuidTryParseStack := by
    have h1 := stackAt_split_bottom s0.sp uuidTryParseStack (hookStack - uuidTryParseStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded pl (uuidTryParseCodeSpec uuidTryParse).keepsFs).pre (p, bs, out) s0 ∗ R' := by
    dsimp only [withLsCodeLoaded, Spec.keepsFs, uuidTryParseStackSpec, uuidTryParseCodeSpec,
      uuidTryParseSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨sf, hs, hout⟩ := h (p, bs, out) R' s0 hpc hrun hpre' hal hL
  refine ⟨sf, hs, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, Spec.keepsFs, uuidTryParseStackSpec, uuidTryParseCodeSpec,
      uuidTryParseSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · rcases hpan with ⟨_, hpan_sat⟩
    have h0 :
        (withLsCodeLoaded pl (uuidTryParseCodeSpec uuidTryParse).keepsFs).onPanic (p, bs, out) s0 sf =
          ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · rcases hex with ⟨code, _, hex_sat⟩
    have h0 :
        (withLsCodeLoaded pl (uuidTryParseCodeSpec uuidTryParse).keepsFs).onExit (p, bs, out) code s0 sf =
          ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hex_sat
    exact False.elim hex_sat.1
  · rcases hoom with ⟨_, hoom_sat⟩
    have h0 :
        (withLsCodeLoaded pl (uuidTryParseCodeSpec uuidTryParse).keepsFs).onOom (p, bs, out) s0 sf =
          ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hoom_sat
    exact False.elim hoom_sat.1

theorem uuidTryParse_stack_keepsFs_placed [LibsignalPlacement]
    (hooks : LibsignalHooks)
    {hookStack : Nat}
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base hooks)
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseStackSpec hookStack).keepsFs) :=
  uuidTryParseWithStack_keepsFs_of_withLsCodeLoaded
    (uuidTryParse_placed_okFs_F hooks) hle hmax

end CryptoVerification.SignalSession.Cli.MainHops.UuidFs
