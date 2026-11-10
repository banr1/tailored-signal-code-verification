/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.CBadG2.Skipped
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Ghost Invariance of MAC Tag Forgery and Collision Predicates

Proves that `MacTagForgeryOrCollision` on `whisperTrials` is invariant across ghosts satisfying
`CBadGammaAgree` and `CBadStamps` whenever the message or wire term is stamped below `n`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg trMsgKeys computeMac)
open Symbolic.Swarm.CREF.TR.FreshSigma (StampsLt TRSignalMsgStampsLt stampsLt_parseTrSignalMsg
  stampsLt_trMsgKeys stampsLt_computeMac stampsLt_trunc_pack stampsLt_kdf_pack stampsLt_concat_pack)

theorem stampsLt_wire_of_computeMac {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {n : Nat} {mk sik rik w : DY.Bytes}
    (h : StampsLt interpretation S g n (computeMac mk sik rik w)) :
    StampsLt interpretation S g n w := by
  have h1 := (stampsLt_trunc_pack interpretation S g n ⟨_⟩).mp h
  have h2 := ((stampsLt_kdf_pack interpretation S g n ⟨mk, _⟩).mp h1).2
  have h3 := ((stampsLt_concat_pack interpretation S g n ⟨sik, _⟩).mp h2).2
  exact ((stampsLt_concat_pack interpretation S g n ⟨rik, w⟩).mp h3).2

/-- `MacTagForgeryOrCollision` on `whisperTrials` is invariant across `CBadGammaAgree` and
`CBadStamps` for any `msg` stamped below `n`. -/
theorem cbadG2_ownSaltMacCollision_iff_of_msg {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g g₁ : Ghost} {ms : List Move} {n : Nat} {msg : TRSignalMsg}
    (hga : CBadGammaAgree interpretation S g g₁ n)
    (hst : CBadStamps interpretation r S g ms n)
    (hmsg : TRSignalMsgStampsLt interpretation S g n msg) :
    MacTagForgeryOrCollision interpretation S g₁ (fun u => u.AttackerKnows (runTraceMoves r ms))
        (honestSalts r ms) msg (whisperTrials interpretation r S g₁ (runTraceMoves r ms) msg) ↔
      MacTagForgeryOrCollision interpretation S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (honestSalts r ms) msg (whisperTrials interpretation r S g (runTraceMoves r ms) msg) := by
  rw [cbadG2_whisperTrials_eq_of_msg hga hst hmsg]
  have hseed_lt : ∀ ctx ∈ whisperTrials interpretation r S g (runTraceMoves r ms) msg,
      ∀ seed, ctx.seed? = some seed → StampsLt interpretation S g n seed :=
    fun ctx hctx seed hseed => (hst.trials msg hmsg ctx hctx).2.2.2.2 seed hseed
  have hkeys_lt : ∀ ctx ∈ whisperTrials interpretation r S g (runTraceMoves r ms) msg,
      ∀ seed, ctx.seed? = some seed → ∀ s ∈ ctx.ownSalts ++ honestSalts r ms,
        let mk := trMsgKeys s seed
        StampsLt interpretation S g n mk.cipherKey ∧
        StampsLt interpretation S g n mk.macKey ∧
        StampsLt interpretation S g n mk.iv ∧
        StampsLt interpretation S g n (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) := by
    intro ctx hctx seed hseed s hs
    have htr := hst.trials msg hmsg ctx hctx
    have hs_lt : StampsLt interpretation S g n s := by
      rcases List.mem_append.mp hs with hs_own | hs_hon
      · exact htr.2.2.2.1 s hs_own
      · exact hst.salts s hs_hon
    obtain ⟨hc_lt, hm_lt, hi_lt⟩ := stampsLt_trMsgKeys hs_lt (htr.2.2.2.2 seed hseed)
    exact ⟨hc_lt, hm_lt, hi_lt, stampsLt_computeMac hm_lt htr.1 htr.2.1 hmsg.1⟩
  have hwire_lt : ∀ peerIk₀ myIk₀ salt₀ seed₀ w,
      msg.mac = computeMac (trMsgKeys salt₀ seed₀).macKey peerIk₀ myIk₀ w →
      StampsLt interpretation S g n w := by
    intro peerIk₀ myIk₀ salt₀ seed₀ w hterm
    have hmac_lt := hmsg.2.1
    rw [hterm] at hmac_lt
    exact stampsLt_wire_of_computeMac hmac_lt
  constructor
  · exact Stage1Trials.MacTagForgeryOrCollision.congr_gamma
      (cbadG2_gamma_eq hga hmsg.2.1)
      (cbadG2_gamma_eq hga hmsg.1)
      (fun ctx hctx seed hseed => cbadG2_gamma_eq hga (hseed_lt ctx hctx seed hseed))
      (fun ctx hctx seed hseed s hs =>
        let ⟨hc, hm, hi, hcm⟩ := hkeys_lt ctx hctx seed hseed s hs
        ⟨cbadG2_gamma_eq hga hc, cbadG2_gamma_eq hga hm, cbadG2_gamma_eq hga hi,
         cbadG2_gamma_eq hga hcm⟩)
      (fun peerIk₀ myIk₀ salt₀ seed₀ w hterm =>
        cbadG2_gamma_eq hga (hwire_lt peerIk₀ myIk₀ salt₀ seed₀ w hterm))
  · exact Stage1Trials.MacTagForgeryOrCollision.congr_gamma
      (cbadG2_gamma_eq hga hmsg.2.1).symm
      (cbadG2_gamma_eq hga hmsg.1).symm
      (fun ctx hctx seed hseed => (cbadG2_gamma_eq hga (hseed_lt ctx hctx seed hseed)).symm)
      (fun ctx hctx seed hseed s hs =>
        let ⟨hc, hm, hi, hcm⟩ := hkeys_lt ctx hctx seed hseed s hs
        ⟨(cbadG2_gamma_eq hga hc).symm, (cbadG2_gamma_eq hga hm).symm,
         (cbadG2_gamma_eq hga hi).symm, (cbadG2_gamma_eq hga hcm).symm⟩)
      (fun peerIk₀ myIk₀ salt₀ seed₀ w hterm =>
        (cbadG2_gamma_eq hga (hwire_lt peerIk₀ myIk₀ salt₀ seed₀ w hterm)).symm)

theorem cbadG2_ownSaltMacCollision_iff {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g g₁ : Ghost} {ms : List Move} {n : Nat} {t : DY.Bytes} {msg : TRSignalMsg}
    (hga : CBadGammaAgree interpretation S g g₁ n)
    (hst : CBadStamps interpretation r S g ms n)
    (ht : StampsLt interpretation S g n t)
    (hp : parseTrSignalMsg t = some msg) :
    MacTagForgeryOrCollision interpretation S g₁ (fun u => u.AttackerKnows (runTraceMoves r ms))
        (honestSalts r ms) msg (whisperTrials interpretation r S g₁ (runTraceMoves r ms) msg) ↔
      MacTagForgeryOrCollision interpretation S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (honestSalts r ms) msg (whisperTrials interpretation r S g (runTraceMoves r ms) msg) :=
  cbadG2_ownSaltMacCollision_iff_of_msg hga hst (stampsLt_parseTrSignalMsg ht hp)

end Symbolic.Swarm.CREF
