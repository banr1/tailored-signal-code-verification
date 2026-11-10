/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.BaseAttackerKnowledge
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Comparse.Basic
import Comparse.Formats.Basic
import Comparse.Formats.Derived
import DY.Comparse
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Init.Data.String.Defs
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
public import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSendBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.RatchetDHRkSwapPeelTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
public import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.Comparse.Basic
import Symbolic.DYBridge.DY.Comparse
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Ratchet-Key Replacement Witnesses for Non-`TermShapeId` Ratchet Keys

Defines `rkWrapVariant` and constructs replacement peer ratchet keys `theirPk_c` satisfying
`TermShapeId` and preserving concrete `gamma` semantics for DH and `createChain` seeds when a
received message carries a non-`TermShapeId` ratchet key without a memo collision
(`recv_mac_authentic_or_rkSwap_seed_known_of_not_collision'`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
abbrev SpqrSem := OpaqueSymbolSemantics

open DY DY.Comparse DY.DiffieHellman DY.Literal DY.X25519
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg trMsgKeys)
open DY.Libsignal.TripleRatchet (createChain consumeMessageKey computeMac findRecvChain chainKeyAt
  kdfRk hmac hkdfBlock1 hkdfBlock2 kdfCk lit litByte)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.RecvRep

unseal DY.Bytes in
private instance subLit0RKS (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subConcat0RKS (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhPkRKS (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhRKS (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKdf0RKS (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant0RKS (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

/-! ## `rkWrapVariant` and `gamma` preservation -/

/-- Wraps a replacement inner key `k_c` with the outer `X25519.Variant.SubF` wrapper of `rk₀`, if any. -/
def rkWrapVariant (rk₀ k_c : DY.Bytes) : DY.Bytes :=
  match rk₀.view? DY.X25519.Variant.SubF with
  | none => k_c
  | some v => DY.X25519.x25519TorsionVariant k_c v.variation v.torsion

private theorem x25519Key_of_view_variant_none_rks {pk : DY.Bytes}
    (h : pk.view? DY.X25519.Variant.SubF = none) :
    DY.X25519.normalizeX25519Key pk = pk := by
  unfold DY.X25519.normalizeX25519Key; rw [h]

private theorem gamma_variant_pack_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (v : DY.X25519.Variant.SubF DY.Bytes) :
    gamma i S g v.pack =
      variantBytes (DY.Libsignal.Refinement.torsionShift i (gamma i S g v.key) v.torsion)
        v.variation := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeVariant i) (concretizeAll i S g)]
  rfl

private theorem gamma_variant_eq_of_x25519Key_gamma_eq_rks
    (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (rk₀ k_c : DY.Bytes)
    (hvar : ∀ v : DY.X25519.Variant.SubF DY.Bytes, rk₀.view? DY.X25519.Variant.SubF = some v → ¬(v.variation = 0 ∧ v.torsion = 0))
    (hk_view : k_c.view? DY.X25519.Variant.SubF = none)
    (hk_gam : gamma i S g k_c = gamma i S g (DY.X25519.normalizeX25519Key rk₀)) :
    gamma i S g (rkWrapVariant rk₀ k_c) = gamma i S g rk₀ := by
  have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF rk₀
  unfold rkWrapVariant
  cases hview : rk₀.view? DY.X25519.Variant.SubF with
  | none =>
    have hx0 : DY.X25519.normalizeX25519Key rk₀ = rk₀ := x25519Key_of_view_variant_none_rks hview
    rw [hx0] at hk_gam
    exact hk_gam
  | some v =>
    dsimp only
    rw [hview] at hv; dsimp only at hv
    have hv_ne : ¬(v.variation = 0 ∧ v.torsion = 0) := hvar v hview
    have hx0 : DY.X25519.normalizeX25519Key rk₀ = v.key := by unfold DY.X25519.normalizeX25519Key; rw [hview]
    change gamma i S g
      (if v.variation = 0 ∧ v.torsion = 0 then DY.X25519.normalizeX25519Key k_c
       else ({ key := DY.X25519.normalizeX25519Key k_c, variation := v.variation, torsion := v.torsion } : DY.X25519.Variant.SubF DY.Bytes).pack) =
      gamma i S g rk₀
    split
    · contradiction
    · rw [← hv, gamma_variant_pack_rks, gamma_variant_pack_rks,
          x25519Key_of_view_variant_none_rks hk_view, hk_gam, hx0]

private theorem gamma_dhPk_raw_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) (sk : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dhPk sk) =
      (i DY.Libsignal.Refinement.x25519PublicKeySymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk)]).getD [] := by
  unfold gamma gamma'
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g)]
  rfl

private theorem gamma_dh_raw_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (pk sk : DY.Bytes) :
    gamma i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
      (i DY.Libsignal.Refinement.x25519AgreementSymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk), gamma i S g pk]).getD [] := by
  unfold gamma gamma'; rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; rfl

private theorem gamma_dh_eq_rks (i : ExternInterpretation) (hEq : ExternCryptoLawsHold i)
    (S : SpqrSem) (g : Ghost) (pk sk : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dh pk sk) =
      (i DY.Libsignal.Refinement.x25519AgreementSymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk), gamma i S g pk]).getD [] := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 heq
    rw [heq] at hv; simp only at hv; subst hv
    split
    · rw [gamma_dh_raw_rks]
    · rw [gamma_dh_raw_rks]
      show (i DY.Libsignal.Refinement.x25519AgreementSymbol
          [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk2),
           gamma i S g (DY.DiffieHellman.dhPk sk)]).getD [] =
        (i DY.Libsignal.Refinement.x25519AgreementSymbol
          [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk),
           gamma i S g (DY.DiffieHellman.dhPk sk2)]).getD []
      rw [gamma_dhPk_raw_rks, gamma_dhPk_raw_rks,
        hEq.x25519_agreement_commutes
          (DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk2))
          (DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk))]
  · rw [gamma_dh_raw_rks]

private theorem gamma_kdfExtract_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (salt ikm : DY.Bytes) :
    gamma i S g (KdfExtract.kdfExtract salt ikm) =
      CryptoGames.HMAC.hmacWith
        (DY.Libsignal.Refinement.sha256CompressFunction i)
        (gamma i S g salt) (gamma i S g ikm) := by
  unfold KdfExtract.kdfExtract gamma gamma'
  show ((({salt := salt, ikm := ikm} : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec
    (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
  rfl

private theorem gamma_concat_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (l r : DY.Bytes) :
    gamma i S g (Concat.concat l r) = gamma i S g l ++ gamma i S g r := by
  unfold Concat.concat gamma gamma'
  show ((({lhs := l, rhs := r} : DY.Concat.Concat.SubF DY.Bytes).pack).rec
    (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g)]
  rfl

private theorem gamma_concat_congr_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {l₁ l₂ r₁ r₂ : DY.Bytes}
    (hl : gamma i S g l₁ = gamma i S g l₂)
    (hr : gamma i S g r₁ = gamma i S g r₂) :
    gamma i S g (Concat.concat l₁ r₁) = gamma i S g (Concat.concat l₂ r₂) := by
  rw [gamma_concat_rks, gamma_concat_rks, hl, hr]

private theorem gamma_hmac_congr_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {k₁ k₂ m₁ m₂ : DY.Bytes}
    (hk : gamma i S g k₁ = gamma i S g k₂)
    (hm : gamma i S g m₁ = gamma i S g m₂) :
    gamma i S g (hmac k₁ m₁) = gamma i S g (hmac k₂ m₂) := by
  unfold hmac
  rw [gamma_kdfExtract_rks, gamma_kdfExtract_rks, hk, hm]

private theorem gamma_createChain_snd_congr_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (rk pk₁ pk₂ dhs : DY.Bytes)
    (hdh : gamma i S g (DiffieHellman.dh (DY.X25519.normalizeX25519Key pk₁) dhs) =
      gamma i S g (DiffieHellman.dh (DY.X25519.normalizeX25519Key pk₂) dhs)) :
    gamma i S g (createChain rk pk₁ dhs).2 = gamma i S g (createChain rk pk₂ dhs).2 := by
  dsimp only [createChain, DY.X25519.agree, kdfRk, hkdfBlock2, hkdfBlock1]
  have hprk : gamma i S g (hmac rk (DiffieHellman.dh (DY.X25519.normalizeX25519Key pk₁) dhs)) =
      gamma i S g (hmac rk (DiffieHellman.dh (DY.X25519.normalizeX25519Key pk₂) dhs)) :=
    gamma_hmac_congr_rks i S g rfl hdh
  have hb1 : gamma i S g (hmac (hmac rk (DiffieHellman.dh (DY.X25519.normalizeX25519Key pk₁) dhs))
        (Concat.concat (lit "WhisperRatchet") (litByte 1))) =
      gamma i S g (hmac (hmac rk (DiffieHellman.dh (DY.X25519.normalizeX25519Key pk₂) dhs))
        (Concat.concat (lit "WhisperRatchet") (litByte 1))) :=
    gamma_hmac_congr_rks i S g hprk rfl
  exact gamma_hmac_congr_rks i S g hprk (gamma_concat_congr_rks i S g hb1 rfl)

private theorem gamma_chainKeyAt_congr_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    ∀ (n : Nat) {ck₁ ck₂ : DY.Bytes},
      gamma i S g ck₁ = gamma i S g ck₂ →
      gamma i S g (chainKeyAt ck₁ n) = gamma i S g (chainKeyAt ck₂ n)
  | 0, _, _, hck => hck
  | n + 1, _, _, hck =>
    gamma_chainKeyAt_congr_rks i S g n (gamma_hmac_congr_rks i S g hck rfl)

/-- On any reachable trace `tr`, every attacker-known `X25519.Variant.SubF` term has
`¬(v.variation = 0 ∧ v.torsion = 0)`. -/
theorem variant_variation_ne_zero_of_attackerKnows_reachable
    {tr : ExecTrace} (hreach : ReachableTrace tr)
    {u : DY.Bytes} (hu : u.AttackerKnows tr)
    (v : DY.X25519.Variant.SubF DY.Bytes)
    (hview : u.view? DY.X25519.Variant.SubF = some v) :
    ¬(v.variation = 0 ∧ v.torsion = 0) :=
  (variant_variation_ne_zero_of_attackerKnows_reachable_peel hreach hu v hview).1

/-- Under `ExternCryptoLawsHold interpretation` and normalised outer `Variant.SubF` wrappers, if
`k_c` has no outer `Variant.SubF` wrapper and matches `gamma` of `normalizeX25519Key rk₀`, then
`rkWrapVariant rk₀ k_c` normalises to `k_c` and preserves `gamma` on the key, DH output, and
`createChain` message seeds. -/
theorem gamma_rkWrapVariant_and_dh_eq
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (S : SpqrSem) (g : Ghost)
    (rk₀ k_c rk dhs : DY.Bytes) (n : Nat)
    (hvar : ∀ v : DY.X25519.Variant.SubF DY.Bytes,
      rk₀.view? DY.X25519.Variant.SubF = some v → ¬(v.variation = 0 ∧ v.torsion = 0))
    (hk_view : k_c.view? DY.X25519.Variant.SubF = none)
    (hk_gam : gamma interpretation S g k_c = gamma interpretation S g (DY.X25519.normalizeX25519Key rk₀)) :
    let theirPk_c := rkWrapVariant rk₀ k_c
    DY.X25519.normalizeX25519Key theirPk_c = k_c ∧
    gamma interpretation S g theirPk_c = gamma interpretation S g rk₀ ∧
    ((gamma interpretation S g rk₀).length = 32 → (gamma interpretation S g theirPk_c).length = 32) ∧
    gamma interpretation S g (DiffieHellman.dh (DY.X25519.normalizeX25519Key theirPk_c) dhs) =
      gamma interpretation S g (DiffieHellman.dh (DY.X25519.normalizeX25519Key rk₀) dhs) ∧
    gamma interpretation S g (kdfCk (chainKeyAt (createChain rk theirPk_c dhs).2 n)).2 =
      gamma interpretation S g (kdfCk (chainKeyAt (createChain rk rk₀ dhs).2 n)).2 := by
  intro theirPk_c
  have hxkey : DY.X25519.normalizeX25519Key theirPk_c = k_c := by
    dsimp only [theirPk_c, rkWrapVariant]
    cases rk₀.view? DY.X25519.Variant.SubF with
    | none => exact x25519Key_of_view_variant_none_rks hk_view
    | some v =>
      dsimp only
      change DY.X25519.normalizeX25519Key
        (if v.variation = 0 ∧ v.torsion = 0 then DY.X25519.normalizeX25519Key k_c
         else ({ key := DY.X25519.normalizeX25519Key k_c, variation := v.variation, torsion := v.torsion } : DY.X25519.Variant.SubF DY.Bytes).pack) = k_c
      split
      · rw [x25519Key_of_view_variant_none_rks hk_view, x25519Key_of_view_variant_none_rks hk_view]
      · unfold DY.X25519.normalizeX25519Key
        rw [DY.BytesView.view_pack (SubF := DY.X25519.Variant.SubF)]
        exact x25519Key_of_view_variant_none_rks hk_view
  have hgam_rk : gamma interpretation S g theirPk_c = gamma interpretation S g rk₀ :=
    gamma_variant_eq_of_x25519Key_gamma_eq_rks interpretation S g rk₀ k_c hvar hk_view hk_gam
  have hdh_gam : gamma interpretation S g (DiffieHellman.dh (DY.X25519.normalizeX25519Key theirPk_c) dhs) =
      gamma interpretation S g (DiffieHellman.dh (DY.X25519.normalizeX25519Key rk₀) dhs) := by
    rw [gamma_dh_eq_rks interpretation hEq S g,
        gamma_dh_eq_rks interpretation hEq S g,
        hxkey, hk_gam]
  have hseed_gam : gamma interpretation S g (kdfCk (chainKeyAt (createChain rk theirPk_c dhs).2 n)).2 =
      gamma interpretation S g (kdfCk (chainKeyAt (createChain rk rk₀ dhs).2 n)).2 :=
    gamma_hmac_congr_rks interpretation S g
      (gamma_chainKeyAt_congr_rks interpretation S g n
        (gamma_createChain_snd_congr_rks interpretation S g rk theirPk_c rk₀ dhs hdh_gam)) rfl
  exact ⟨hxkey, hgam_rk, fun hlen => hgam_rk ▸ hlen, hdh_gam, hseed_gam⟩

/-! ## `TermShapeId` and `AttackerKnows` closure under `rkWrapVariant` -/

theorem termShapeId_x25519TorsionVariant {k : DY.Bytes} (v : Fin 4) (t : Fin 8) (hk : TermShapeId k) :
    TermShapeId (DY.X25519.x25519TorsionVariant k v t) := by
  change TermShapeId
    (if v = 0 ∧ t = 0 then DY.X25519.normalizeX25519Key k
     else ({ key := DY.X25519.normalizeX25519Key k, variation := v, torsion := t } : DY.X25519.Variant.SubF DY.Bytes).pack)
  split
  · exact termShapeId_x25519Key hk
  · intro i S g
    rw [shape_variant_pack_sid, termShapeId_x25519Key hk i S g]

theorem termShapeId_rkWrapVariant (rk₀ : DY.Bytes) {k_c : DY.Bytes} (hk : TermShapeId k_c) :
    TermShapeId (rkWrapVariant rk₀ k_c) := by
  unfold rkWrapVariant
  cases rk₀.view? DY.X25519.Variant.SubF with
  | none => exact hk
  | some v => exact termShapeId_x25519TorsionVariant v.variation v.torsion hk

theorem attackerKnows_rkWrapVariant (rk₀ : DY.Bytes) {k_c : DY.Bytes} {tr : ExecTrace}
    (hk : k_c.AttackerKnows tr) :
    (rkWrapVariant rk₀ k_c).AttackerKnows tr := by
  unfold rkWrapVariant
  cases rk₀.view? DY.X25519.Variant.SubF with
  | none => exact hk
  | some v =>
    exact DY.Bytes.AttackerKnows.prove X25519.x25519Variant.attackerKnowledge _ tr ⟨k_c, v.variation, v.torsion, rfl, hk⟩

/-! ## Replacement key and seed construction -/

unseal DY.Bytes in
private theorem view_variant_litOf_none (bs : HwBytes) :
    (litOf bs).view? DY.X25519.Variant.SubF = none :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none
    (F1 := DY.Literal.Literal.SubF) DY.X25519.Variant.SubF { lit := _ }

unseal DY.Bytes in
private theorem view_variant_dhPk_none (sk : DY.Bytes) :
    (dhPk sk).view? DY.X25519.Variant.SubF = none :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none
    (F1 := DY.DiffieHellman.DhPk.SubF) DY.X25519.Variant.SubF { sk := sk }

private theorem gamma_litOf_rks (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) (bs : HwBytes) :
    gamma i S g (litOf bs) = bs :=
  DY.Libsignal.Composed.Refinement.gamma_litOf i S g bs

private theorem attackerKnows_chainKeyAt_rks {tr : ExecTrace} :
    ∀ (k : Nat) {ck : DY.Bytes}, ck.AttackerKnows tr → (chainKeyAt ck k).AttackerKnows tr
  | 0, _, hck => hck
  | k + 1, ck, hck =>
    attackerKnows_chainKeyAt_rks k
      (KdfExtract.attacker_knows_kdfExtract ck (litByte 0x02) tr hck
        (Literal.attacker_knows_literalToBytes _ tr))

private theorem attackerKnows_seed_of_rk_and_dh {tr : ExecTrace} {rk theirPk_c dhs : DY.Bytes} (n : Nat)
    (hrk : rk.AttackerKnows tr)
    (hdh : (DiffieHellman.dh (DY.X25519.normalizeX25519Key theirPk_c) dhs).AttackerKnows tr) :
    (kdfCk (chainKeyAt (createChain rk theirPk_c dhs).2 n)).2.AttackerKnows tr := by
  have hprk : (hmac rk (DiffieHellman.dh (DY.X25519.normalizeX25519Key theirPk_c) dhs)).AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ tr hrk hdh
  have hckr : (createChain rk theirPk_c dhs).2.AttackerKnows tr :=
    (attackerKnows_createChain_of_prk hprk).2
  exact KdfExtract.attacker_knows_kdfExtract _ (litByte 0x01) tr
    (attackerKnows_chainKeyAt_rks n hckr)
    (Literal.attacker_knows_literalToBytes _ tr)

/-- Constructs an attacker-known `TermShapeId` replacement key `theirPk_c` and seed `seed_c`
matching `gamma` of `msg₀.ratchetKey` and `mkSeed` when both `st₀.rk` and `st₀.dhs` are
attacker-known. -/
theorem rkSwap_g1_seed_known
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move)
    (msg₀ : TRSignalMsg) (st₀ : TRState) (mkSeed : DY.Bytes)
    (hfind : findRecvChain st₀.recv msg₀.ratchetKey = none)
    (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (hvar : ∀ v : DY.X25519.Variant.SubF DY.Bytes,
      msg₀.ratchetKey.view? DY.X25519.Variant.SubF = some v → ¬(v.variation = 0 ∧ v.torsion = 0))
    (hrk_ak : st₀.rk.AttackerKnows (runTraceMoves r₀ ms))
    (hdhs_ak : st₀.dhs.AttackerKnows (runTraceMoves r₀ ms)) :
    let theirPk_c := rkWrapVariant msg₀.ratchetKey
      (litOf (gamma interpretation S g (DY.X25519.normalizeX25519Key msg₀.ratchetKey)))
    let seed_c := (kdfCk (chainKeyAt (createChain st₀.rk theirPk_c st₀.dhs).2 msg₀.counter.toNat)).2
    TermShapeId theirPk_c ∧
    theirPk_c.AttackerKnows (runTraceMoves r₀ ms) ∧
    gamma interpretation S g theirPk_c = gamma interpretation S g msg₀.ratchetKey ∧
    seed_c.AttackerKnows (runTraceMoves r₀ ms) ∧
    gamma interpretation S g seed_c = gamma interpretation S g mkSeed := by
  intro theirPk_c seed_c
  let k_c := litOf (gamma interpretation S g (DY.X25519.normalizeX25519Key msg₀.ratchetKey))
  have hk_sid : TermShapeId k_c := termShapeId_litOf _
  have hk_ak : k_c.AttackerKnows (runTraceMoves r₀ ms) := knows_litOf _ (runTraceMoves r₀ ms)
  have hk_view : k_c.view? DY.X25519.Variant.SubF = none := view_variant_litOf_none _
  have hk_gam : gamma interpretation S g k_c =
      gamma interpretation S g (DY.X25519.normalizeX25519Key msg₀.ratchetKey) :=
    gamma_litOf_rks interpretation S g _
  obtain ⟨hxkey, hgam_rk, _, _, hseed_gam⟩ :=
    gamma_rkWrapVariant_and_dh_eq interpretation hEq S g
      msg₀.ratchetKey k_c st₀.rk st₀.dhs msg₀.counter.toNat hvar hk_view hk_gam
  have hdh_ak : (DiffieHellman.dh (DY.X25519.normalizeX25519Key theirPk_c) st₀.dhs).AttackerKnows (runTraceMoves r₀ ms) := by
    rw [hxkey]
    exact DiffieHellman.attacker_knows_dh k_c st₀.dhs (runTraceMoves r₀ ms) hk_ak hdhs_ak
  have hmk_eq : mkSeed = (kdfCk (chainKeyAt (createChain st₀.rk msg₀.ratchetKey st₀.dhs).2 msg₀.counter.toNat)).2 :=
    recvSeed_eq_of_findRecvChain_none hfind hseed
  refine ⟨termShapeId_rkWrapVariant msg₀.ratchetKey hk_sid,
    attackerKnows_rkWrapVariant msg₀.ratchetKey hk_ak,
    hgam_rk,
    attackerKnows_seed_of_rk_and_dh msg₀.counter.toNat hrk_ak hdh_ak,
    ?_⟩
  rw [hmk_eq]
  exact hseed_gam

/-- Constructs an attacker-known `TermShapeId` replacement key `theirPk_c` and seed `seed_c`
matching `gamma` of `msg₀.ratchetKey` and `mkSeed` via `dh_commutes` when `st₀.rk`, `dhPk st₀.dhs`,
and the peer DH secret `a₀` are attacker-known. -/
theorem rkSwap_g2_seed_known
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move)
    (msg₀ : TRSignalMsg) (st₀ : TRState) (mkSeed a₀ : DY.Bytes)
    (hfind : findRecvChain st₀.recv msg₀.ratchetKey = none)
    (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (hvar : ∀ v : DY.X25519.Variant.SubF DY.Bytes,
      msg₀.ratchetKey.view? DY.X25519.Variant.SubF = some v → ¬(v.variation = 0 ∧ v.torsion = 0))
    (hrk_ak : st₀.rk.AttackerKnows (runTraceMoves r₀ ms))
    (hdhPk_dhs_ak : (dhPk st₀.dhs).AttackerKnows (runTraceMoves r₀ ms))
    (ha₀ : DY.X25519.normalizeX25519Key msg₀.ratchetKey = dhPk a₀) :
    let theirPk_c := rkWrapVariant msg₀.ratchetKey (dhPk (litOf (gamma interpretation S g a₀)))
    let seed_c := (kdfCk (chainKeyAt (createChain st₀.rk theirPk_c st₀.dhs).2 msg₀.counter.toNat)).2
    TermShapeId theirPk_c ∧
    theirPk_c.AttackerKnows (runTraceMoves r₀ ms) ∧
    gamma interpretation S g theirPk_c = gamma interpretation S g msg₀.ratchetKey ∧
    seed_c.AttackerKnows (runTraceMoves r₀ ms) ∧
    gamma interpretation S g seed_c = gamma interpretation S g mkSeed := by
  intro theirPk_c seed_c
  let a_c := litOf (gamma interpretation S g a₀)
  let k_c := dhPk a_c
  have ha_c_ak : a_c.AttackerKnows (runTraceMoves r₀ ms) := knows_litOf _ (runTraceMoves r₀ ms)
  have hk_sid : TermShapeId k_c := termShapeId_dhPk (termShapeId_litOf _)
  have hk_ak : k_c.AttackerKnows (runTraceMoves r₀ ms) :=
    DiffieHellman.attacker_knows_dhPk a_c (runTraceMoves r₀ ms) ha_c_ak
  have hk_view : k_c.view? DY.X25519.Variant.SubF = none := view_variant_dhPk_none _
  have hk_gam : gamma interpretation S g k_c =
      gamma interpretation S g (DY.X25519.normalizeX25519Key msg₀.ratchetKey) := by
    rw [ha₀, gamma_dhPk_raw_rks, gamma_dhPk_raw_rks, gamma_litOf_rks]
  obtain ⟨hxkey, hgam_rk, _, _, hseed_gam⟩ :=
    gamma_rkWrapVariant_and_dh_eq interpretation hEq S g
      msg₀.ratchetKey k_c st₀.rk st₀.dhs msg₀.counter.toNat hvar hk_view hk_gam
  have hdh_ak : (DiffieHellman.dh (DY.X25519.normalizeX25519Key theirPk_c) st₀.dhs).AttackerKnows (runTraceMoves r₀ ms) := by
    rw [hxkey, show k_c = dhPk a_c from rfl, DiffieHellman.dh_commutes]
    exact DiffieHellman.attacker_knows_dh (dhPk st₀.dhs) a_c (runTraceMoves r₀ ms) hdhPk_dhs_ak ha_c_ak
  have hmk_eq : mkSeed = (kdfCk (chainKeyAt (createChain st₀.rk msg₀.ratchetKey st₀.dhs).2 msg₀.counter.toNat)).2 :=
    recvSeed_eq_of_findRecvChain_none hfind hseed
  refine ⟨termShapeId_rkWrapVariant msg₀.ratchetKey hk_sid,
    attackerKnows_rkWrapVariant msg₀.ratchetKey hk_ak,
    hgam_rk,
    attackerKnows_seed_of_rk_and_dh msg₀.counter.toNat hrk_ak hdh_ak,
    ?_⟩
  rw [hmk_eq]
  exact hseed_gam

/-! ## Unified replacement witness from seed shape equality -/

theorem ratchetKey_attackerKnows_of_recvRepresentations
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (b : HwBytes)
    {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) :
    msg₀.ratchetKey.AttackerKnows (runTraceMoves r₀ ms) := by
  have ht_ak : t₀.AttackerKnows (runTraceMoves r₀ ms) := ht₀.1
  obtain ⟨x, hsplit, _, hpack, hrk_eq, _, _⟩ := parseTrSignalMsg_unpack hparse₀
  have hsp_ak := Concat.attacker_knows_split t₀ (t₀.length - Trunc.trunc8Length) (runTraceMoves r₀ ms) ht_ak
  rw [hsplit] at hsp_ak
  have hwire_ak := hsp_ak.1
  rw [hpack] at hwire_ak
  have hrk_ak : x.senderRatchetKey.AttackerKnows (runTraceMoves r₀ ms) :=
    DY.Bytes.AttackerKnows.prove TrWire.trWireMsgArg.attackerKnowledge x.senderRatchetKey
      (runTraceMoves r₀ ms) ⟨x, hwire_ak, Or.inl rfl⟩
  exact hrk_eq ▸ hrk_ak

/-! ## Authentic decrypt or seed shape equality -/

unseal DY.Bytes in
private instance subTrunc0RKS (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem recvSeed_eq_some_kdfExtract_rks {st : TRState} {msg : TRSignalMsg} {seed : DY.Bytes}
    (hseed : recvSeed st msg = some seed) : ∃ ck : DY.Bytes, seed = KdfExtract.kdfExtract ck (litByte 0x01) := by
  unfold recvSeed at hseed; split at hseed <;> [skip; cases hseed]
  split at hseed <;> [cases hseed; skip]
  simp only [Option.map_eq_some_iff] at hseed; obtain ⟨⟨s, c'⟩, hcmk, rfl⟩ := hseed
  unfold consumeMessageKey at hcmk
  split at hcmk <;> [cases hcmk; (split at hcmk <;> [cases hcmk; (split at hcmk <;> [cases hcmk; skip])])]
  injection hcmk with hcmk; injection hcmk with h1 _; exact ⟨_, h1.symm⟩

unseal DY.Bytes in
private theorem literal_ne_concat_rks (b : ByteArray) (l r : DY.Bytes) :
    Literal.literalToBytes b ≠ Concat.concat l r :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none
    (F1 := DY.Literal.Literal.SubF) (F2 := DY.Concat.Concat.SubF) h

unseal DY.Bytes in
private theorem literal_ne_kdfExtract_rks (b : ByteArray) (s i : DY.Bytes) :
    Literal.literalToBytes b ≠ KdfExtract.kdfExtract s i :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none
    (F1 := DY.Literal.Literal.SubF) (F2 := DY.KdfExtract.KdfExtract.SubF) h

unseal DY.Bytes in
private theorem concat_ne_kdfExtract_rks (l r s i : DY.Bytes) :
    Concat.concat l r ≠ KdfExtract.kdfExtract s i :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none
    (F1 := DY.Concat.Concat.SubF) (F2 := DY.KdfExtract.KdfExtract.SubF) h

private theorem seed_attackerKnows_of_trMsgKeys_macKey_attackerKnows
    {r₀ : ProtocolSetup} {ms : List Move} (hreach : ReachableTrace (runTraceMoves r₀ ms))
    {pqSalt seed ck : DY.Bytes} (hseed_kdf : seed = KdfExtract.kdfExtract ck (litByte 0x01))
    (hmackey_ak : (trMsgKeys pqSalt seed).macKey.AttackerKnows (runTraceMoves r₀ ms)) :
    seed.AttackerKnows (runTraceMoves r₀ ms) := by
  let T := runTraceMoves r₀ ms; let prk := hmac pqSalt seed
  let info2 := Concat.concat (hkdfBlock1 prk (lit "WhisperMessageKeys"))
    (Concat.concat (lit "WhisperMessageKeys") (litByte 2))
  have hmk_ak : (KdfExtract.kdfExtract prk info2).AttackerKnows T := hmackey_ak
  have hprk_ak : prk.AttackerKnows T := by
    rcases macKdfSafe_c_kdfExtract_inv r₀ ms prk info2 hreach hmk_ak with
      ⟨hprk_ak, _⟩ | h01 | h02 | hwr1 | ⟨b1, hwr2 | hwr2 | hwr2⟩
    · exact hprk_ak
    · exact False.elim (literal_ne_concat_rks _ _ _ h01.symm)
    · exact False.elim (literal_ne_concat_rks _ _ _ h02.symm)
    · exact False.elim (literal_ne_concat_rks _ _ _ (concat_injective hwr1).2.symm)
    · exact False.elim (lit_whisperRatchet_ne_whisperMessageKeys (concat_injective (concat_injective hwr2).2).1.symm)
    · exact False.elim (pqxdhLabel_ne_whisperMessageKeys (concat_injective (concat_injective hwr2).2).1.symm)
    · exact False.elim (pqxdhLabel_ne_whisperMessageKeys (concat_injective (concat_injective hwr2).2).1.symm)
  rcases macKdfSafe_c_kdfExtract_inv r₀ ms pqSalt seed hreach hprk_ak with
    ⟨_, hseed_ak⟩ | h01 | h02 | hwr1 | ⟨b1, hwr2 | hwr2 | hwr2⟩
  · exact hseed_ak
  · rw [hseed_kdf] at h01; exact False.elim (literal_ne_kdfExtract_rks _ _ _ h01.symm)
  · rw [hseed_kdf] at h02; exact False.elim (literal_ne_kdfExtract_rks _ _ _ h02.symm)
  · rw [hseed_kdf] at hwr1; exact False.elim (concat_ne_kdfExtract_rks _ _ _ _ hwr1.symm)
  · rw [hseed_kdf] at hwr2; exact False.elim (concat_ne_kdfExtract_rks _ _ _ _ hwr2.symm)
  · rw [hseed_kdf] at hwr2; exact False.elim (concat_ne_kdfExtract_rks _ _ _ _ hwr2.symm)
  · rw [hseed_kdf] at hwr2; exact False.elim (concat_ne_kdfExtract_rks _ _ _ _ hwr2.symm)

unseal DY.Bytes in
private theorem trWireMsg_pack_ne_literal_rks (x : TrWire.TrWireMsg.SubF DY.Bytes) (b : ByteArray) :
    x.pack ≠ Literal.literalToBytes b :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none
    (F1 := DY.TrWire.TrWireMsg.SubF) (F2 := DY.Literal.Literal.SubF) h

unseal DY.Bytes in
private theorem trWireMsg_pack_inj_rks {x y : TrWire.TrWireMsg.SubF DY.Bytes} (h : x.pack = y.pack) : x = y := by
  have h1 : DY.Bytes.view? x.pack DY.TrWire.TrWireMsg.SubF = some x :=
    DY.BytesView.view_pack (SubF := DY.TrWire.TrWireMsg.SubF) x
  have h2 : DY.Bytes.view? y.pack DY.TrWire.TrWireMsg.SubF = some y :=
    DY.BytesView.view_pack (SubF := DY.TrWire.TrWireMsg.SubF) y
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

unseal DY.Bytes in
private theorem kdfExtract_inj_rks {s₁ i₁ s₂ i₂ : DY.Bytes}
    (h : KdfExtract.kdfExtract s₁ i₁ = KdfExtract.kdfExtract s₂ i₂) : s₁ = s₂ ∧ i₁ = i₂ := by
  have h1 := DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s₁, ikm := i₁ }
  have h2 := DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := s₂, ikm := i₂ }
  change DY.Bytes.view? (KdfExtract.kdfExtract s₁ i₁) _ = _ at h1
  change DY.Bytes.view? (KdfExtract.kdfExtract s₂ i₂) _ = _ at h2
  rw [h, h2] at h1; injection h1 with h1; cases h1; exact ⟨rfl, rfl⟩

set_option maxHeartbeats 400000 in
/-- From `AuthenticDecryptRep`, concludes either `mkSeed.AttackerKnows` or
`TermShapeId msg₀.ratchetKey`. -/
theorem seed_attackerKnows_or_termShapeId_of_authenticDecryptRep
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move)
    (b ptext : HwBytes) (msg₀ : TRSignalMsg) (st₀ : TRState) (mkSeed k_own : DY.Bytes)
    (hreach : ReachableTrace (runTraceMoves r₀ ms)) (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (hAuth : AuthenticDecryptRep interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed k_own) :
    mkSeed.AttackerKnows (runTraceMoves r₀ ms) ∨
    (TermShapeId msg₀.ratchetKey ∧
      AuthenticDecryptRep interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed k_own) := by
  have ⟨t', msg', _ptTerm, pqSalt, _ht'_mem, ht'_ak, _hpq_ak, _hpq_gam, _ht'_gam,
    hparse', _hver_eq, hrk_eq, _hcnt_eq, _hpq_eq, hmac_eq, _hdec, _hpt_gam⟩ := hAuth
  obtain ⟨ck, hseed_kdf⟩ := recvSeed_eq_some_kdfExtract_rks hseed
  obtain ⟨x', hsplit', _, hpack', hrk'_eq, _, _⟩ := parseTrSignalMsg_unpack hparse'
  have hsp_ak := Concat.attacker_knows_split t' (t'.length - Trunc.trunc8Length) (runTraceMoves r₀ ms) ht'_ak
  rw [hsplit'] at hsp_ak
  have hmac_ak : (Trunc.trunc8 (hmac (trMsgKeys pqSalt mkSeed).macKey
      (Concat.concat st₀.peerIk (Concat.concat st₀.myIk msg'.wire)))).AttackerKnows (runTraceMoves r₀ ms) := by
    change (computeMac (trMsgKeys pqSalt mkSeed).macKey st₀.peerIk st₀.myIk msg'.wire).AttackerKnows (runTraceMoves r₀ ms)
    rw [← hmac_eq]; exact hsp_ak.2
  rcases macKdfSafe_c_trunc8_inv_strong r₀ ms _ hreach hmac_ak with
    hinp_ak | ⟨pqSalt', seed', myIk', peerIk', a', ns', pn', m', pqMsg', t_s, _st_s,
      hinp_eq, _hpq_ak', _ht'_ak', ha_eq, _hst_s, _hmyIk_s, _hpeerIk_s, _hseed_s⟩
  · rcases macKdfSafe_c_kdfExtract_inv r₀ ms _ _ hreach hinp_ak with
      ⟨hmackey_ak, _⟩ | h01 | h02 | hwr1 | ⟨b1, hwr2 | hwr2 | hwr2⟩
    · exact Or.inl (seed_attackerKnows_of_trMsgKeys_macKey_attackerKnows hreach hseed_kdf hmackey_ak)
    · exact False.elim (literal_ne_concat_rks _ _ _ h01.symm)
    · exact False.elim (literal_ne_concat_rks _ _ _ h02.symm)
    · exact False.elim (literal_ne_concat_rks _ _ _ (concat_injective hwr1).2.symm)
    · have h3 := (concat_injective (concat_injective hwr2).2).2; rw [hpack'] at h3
      exact False.elim (trWireMsg_pack_ne_literal_rks x' _ h3)
    · have h3 := (concat_injective (concat_injective hwr2).2).2; rw [hpack'] at h3
      exact False.elim (trWireMsg_pack_ne_literal_rks x' _ h3)
    · have h3 := (concat_injective (concat_injective hwr2).2).2; rw [hpack'] at h3
      exact False.elim (trWireMsg_pack_ne_literal_rks x' _ h3)
  · refine Or.inr ⟨?_, hAuth⟩; unfold hmac at hinp_eq
    have hwire_eq := (concat_injective (concat_injective (kdfExtract_inj_rks hinp_eq).2).2).2
    have hx'_eq := trWireMsg_pack_inj_rks (hpack'.symm.trans hwire_eq)
    have hrk_dhPk : msg'.ratchetKey = dhPk a' :=
      hrk'_eq.trans (congrArg TrWire.TrWireMsg.SubF.senderRatchetKey hx'_eq)
    rw [← hrk_eq, hrk_dhPk, ha_eq]; exact termShapeId_dhPk (termShapeId_randTerm32 t_s)

/-! ## `TrStatesShapeId`-free replacement witnesses -/

unseal DY.Bytes in
private theorem dh_ne_literal_rks (pk sk : DY.Bytes) (b : ByteArray) :
    DiffieHellman.dh pk sk ≠ Literal.literalToBytes b := by
  intro h
  have hdh : ∃ v : DY.DiffieHellman.Dh.SubF DY.Bytes,
      (DiffieHellman.dh pk sk).view? DY.DiffieHellman.Dh.SubF = some v := by
    unfold DiffieHellman.CanDH.dh instCanDHBytes; dsimp only
    rcases pk.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩
    · exact ⟨_, DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _⟩
    · dsimp only; split <;> exact ⟨_, DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _⟩
  obtain ⟨v, hv⟩ := hdh
  have h2 : DY.Bytes.view? (Literal.literalToBytes b) DY.DiffieHellman.Dh.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none
      (F1 := DY.Literal.Literal.SubF) DY.DiffieHellman.Dh.SubF { lit := b }
  rw [h, h2] at hv; contradiction

unseal DY.Bytes in
private theorem dh_ne_concat_rks (pk sk l r : DY.Bytes) :
    DiffieHellman.dh pk sk ≠ Concat.concat l r := by
  intro h
  have hdh : ∃ v : DY.DiffieHellman.Dh.SubF DY.Bytes,
      (DiffieHellman.dh pk sk).view? DY.DiffieHellman.Dh.SubF = some v := by
    unfold DiffieHellman.CanDH.dh instCanDHBytes; dsimp only
    rcases pk.view? DY.DiffieHellman.DhPk.SubF with _ | ⟨⟨a⟩⟩
    · exact ⟨_, DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _⟩
    · dsimp only; split <;> exact ⟨_, DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF) _⟩
  obtain ⟨v, hv⟩ := hdh
  have h2 : DY.Bytes.view? (Concat.concat l r) DY.DiffieHellman.Dh.SubF = none :=
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none
      (F1 := DY.Concat.Concat.SubF) DY.DiffieHellman.Dh.SubF { lhs := l, rhs := r }
  rw [h, h2] at hv; contradiction

unseal DY.Bytes in
private theorem kdfExtract_ne_randTerm_rks (s i : DY.Bytes) (t n : Nat) :
    KdfExtract.kdfExtract s i ≠ randTerm t n :=
  fun h => Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none
    (F1 := DY.KdfExtract.KdfExtract.SubF) (F2 := DY.Random.SubF) h

private theorem pqxdhLabel_ne_whisperRatchet_rks :
    DY.Libsignal.PQXDH.pqxdhLabel ≠ lit "WhisperRatchet" := by
  intro h
  have h1 : DY.Libsignal.PQXDH.pqxdhLabel.length = 46 := by
    unfold DY.Libsignal.PQXDH.pqxdhLabel lit
    rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray]
    decide
  have h2 : (lit "WhisperRatchet").length = 14 := by
    unfold lit
    rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray]
    decide
  rw [h, h2] at h1; cases h1

unseal DY.Bytes in
private theorem kdfRkSafeS_peel_litByte_exact {T : ExecTrace} {ck : DY.Bytes} {b : UInt8}
    (hu : KdfRkSafeS T (KdfExtract.kdfExtract ck (litByte b))) : KdfRkSafeS T ck := by
  generalize hx : KdfExtract.kdfExtract ck (litByte b) = x at hu
  have hview : DY.Bytes.view? x DY.KdfExtract.KdfExtract.SubF = some { salt := ck, ikm := litByte b } := by
    rw [← hx]; exact DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := ck, ikm := litByte b }
  cases hu with
  | atom _ _ _ hk _ _ _ _ _ _ _ => rw [hk] at hview; contradiction
  | kdfExtract_ak _ _ hs_safe _ => exact (kdfExtract_inj_rks hx).1 ▸ hs_safe
  | kdfExtract_01 hs_safe | kdfExtract_02 hs_safe => exact (kdfExtract_inj_rks hx).1 ▸ hs_safe
  | kdfExtract_rk hi _ => exact False.elim (literal_ne_concat_rks _ _ _ ((kdfExtract_inj_rks hx).2.trans hi))
  | kdfExtract_dhPk h =>
    rcases h with ⟨_, _, _, _, _, _, heq⟩
    exact False.elim (literal_ne_concat_rks _ _ _ (kdfExtract_inj_rks (hx.trans heq)).2)
  | kdfExtract_step h =>
    rcases h with ⟨_, _, _, _, _, _, heq⟩
    exact False.elim (literal_ne_concat_rks _ _ _ (kdfExtract_inj_rks (hx.trans heq)).2)
  | kdfExtract_pqxdh23 h =>
    rcases h with ⟨_, hi | hi⟩ <;>
      exact False.elim (literal_ne_concat_rks _ _ _ ((kdfExtract_inj_rks hx).2.trans hi))
  | kdfExtract_alice h =>
    rcases h with ⟨_, _, _, heq⟩
    exact False.elim (literal_ne_concat_rks _ _ _ (kdfExtract_inj_rks (hx.trans heq)).2)
  | _ =>
    try dsimp only [dhPk, DY.PQKem.kemPk, Concat.concat, DY.SymEnc.symEnc] at hview
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _] at hview
    cases hview

private theorem kdfRkSafeS_peel_chainKeyAt_exact {T : ExecTrace} :
    ∀ (k : Nat) {ck : DY.Bytes}, KdfRkSafeS T (chainKeyAt ck k) → KdfRkSafeS T ck
  | 0, _, hu => hu
  | k + 1, _, hu => kdfRkSafeS_peel_litByte_exact (kdfRkSafeS_peel_chainKeyAt_exact k hu)

unseal DY.Bytes in
private theorem kdfRkSafeS_peel_createChain_snd_exact
    (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {T : ExecTrace} {st₀ : TRState} {msg₀ : TRSignalMsg}
    (hu : KdfRkSafeS T (createChain st₀.rk msg₀.ratchetKey st₀.dhs).2)
    (hst₀ : StRkDhsInv T T.length st₀) (hnrk : ¬TermShapeId msg₀.ratchetKey) :
    (hmac st₀.rk (DiffieHellman.dh (X25519.normalizeX25519Key msg₀.ratchetKey) st₀.dhs)).AttackerKnows T := by
  have hnr₀ : NotRandDhPkShape i S g (X25519.normalizeX25519Key msg₀.ratchetKey) :=
    notRandDhPkShape_of_not_termShapeId i S g (fun h => hnrk (termShapeId_of_termShapeId_x25519Key h))
  let prk₀ := hmac st₀.rk (DiffieHellman.dh (X25519.normalizeX25519Key msg₀.ratchetKey) st₀.dhs)
  let info2 := Concat.concat (hkdfBlock1 prk₀ (lit "WhisperRatchet"))
    (Concat.concat (lit "WhisperRatchet") (litByte 2))
  change KdfRkSafeS T (KdfExtract.kdfExtract prk₀ info2) at hu
  generalize hx : KdfExtract.kdfExtract prk₀ info2 = x at hu
  have hview : DY.Bytes.view? x DY.KdfExtract.KdfExtract.SubF = some { salt := prk₀, ikm := info2 } := by
    rw [← hx]; exact DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) { salt := prk₀, ikm := info2 }
  cases hu with
  | atom _ _ _ hk _ _ _ _ _ _ _ => rw [hk] at hview; contradiction
  | kdfExtract_ak hs_ak _ _ _ => change prk₀.AttackerKnows T; rw [(kdfExtract_inj_rks hx).1]; exact hs_ak
  | kdfExtract_01 _ | kdfExtract_02 _ =>
    exact False.elim (literal_ne_concat_rks _ _ _ (kdfExtract_inj_rks hx).2.symm)
  | kdfExtract_rk hi _ =>
    have h2 := (concat_injective ((kdfExtract_inj_rks hx).2.trans hi)).2
    exact False.elim (literal_ne_concat_rks _ _ _ h2.symm)
  | kdfExtract_dhPk h =>
    rcases h with ⟨_, st0, _, t_a, t_sk, _, heq⟩
    have hdh_eq := (kdfExtract_inj_rks (kdfExtract_inj_rks (hx.trans heq)).1).2
    rcases hst₀ with ⟨_, t₀, _, hdhs₀, _⟩; rw [hdhs₀] at hdh_eq
    have hdh_sh := congrArg (fun u => (gamma' i S g u).shape) hdh_eq.symm
    have hnr_a := (dh_shape_eq_of_notRandDhPkShape i S g hnr₀ hdh_sh).1
    rw [x25519Key_of_view_variant_none_rks (view_variant_dhPk_none _)] at hnr_a
    exact False.elim (not_notRandDhPkShape_dhPk_randTerm32 i S g t_a hnr_a)
  | kdfExtract_step h =>
    rcases h with ⟨rk0, pk, t_old, t_new, hlt, _, heq⟩
    obtain ⟨hrk_eq, hdh_eq⟩ := kdfExtract_inj_rks (kdfExtract_inj_rks (hx.trans heq)).1
    rcases hst₀ with ⟨_, t₀, _, hdhs₀, ⟨t_rk, hrk₀⟩ | ⟨rk_p, pk_p, hrk₀⟩⟩
    · rw [hrk₀] at hrk_eq; exact False.elim (kdfExtract_ne_randTerm_rks _ _ _ _ hrk_eq.symm)
    · rw [hdhs₀] at hdh_eq
      have hdh_sh := congrArg (fun u => (gamma' i S g u).shape) hdh_eq.symm
      obtain ⟨hpk_nr, ht_new⟩ := dh_shape_eq_of_notRandDhPkShape i S g hnr₀ hdh_sh
      rw [hrk₀] at hrk_eq
      have hdh_old_eq := (kdfExtract_inj_rks (kdfExtract_inj_rks hrk_eq).1).2
      have hdh_old_sh := congrArg (fun u => (gamma' i S g u).shape) hdh_old_eq
      have ht_old := (dh_shape_eq_of_notRandDhPkShape i S g hpk_nr hdh_old_sh).2
      omega
  | kdfExtract_pqxdh23 h =>
    rcases h with ⟨_, hi | hi⟩ <;> {
      have hikm := (kdfExtract_inj_rks hx).2.trans hi
      have hlbl := (concat_injective (concat_injective hikm).2).1
      exact False.elim (pqxdhLabel_ne_whisperRatchet_rks hlbl.symm)
    }
  | kdfExtract_alice h =>
    rcases h with ⟨ikm, pk, sk, heq⟩
    have hrk_eq := (kdfExtract_inj_rks (kdfExtract_inj_rks (hx.trans heq)).1).1
    rcases hst₀ with ⟨_, t₀, _, _, ⟨t_rk, hrk₀⟩ | ⟨rk_p, pk_p, hrk₀⟩⟩
    · rw [hrk₀] at hrk_eq; exact False.elim (kdfExtract_ne_randTerm_rks _ _ _ _ hrk_eq.symm)
    · rw [hrk₀] at hrk_eq
      have hlbl := (concat_injective (kdfExtract_inj_rks hrk_eq).2).1
      exact False.elim (pqxdhLabel_ne_whisperRatchet_rks hlbl.symm)
  | _ =>
    try dsimp only [dhPk, DY.PQKem.kemPk, Concat.concat, DY.SymEnc.symEnc] at hview
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _] at hview
    cases hview

/-- Produces the replacement witness `(theirPk_c, seed_c)` directly from
`mkSeed.AttackerKnows (runTraceMoves r₀ ms)` without assuming `TrStatesShapeId`. -/
theorem ratchetDH_rkSwap_seed_known_of_seed_attackerKnows
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move)
    (msg₀ : TRSignalMsg) (st₀ : TRState) (mkSeed : DY.Bytes)
    (hreach : ReachableTrace (runTraceMoves r₀ ms)) (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hfind : findRecvChain st₀.recv msg₀.ratchetKey = none)
    (hrkK : msg₀.ratchetKey.AttackerKnows (runTraceMoves r₀ ms))
    (hseed : recvSeed st₀ msg₀ = some mkSeed) (hmk_ak : mkSeed.AttackerKnows (runTraceMoves r₀ ms)) :
    ∃ theirPk_c : DY.Bytes,
      let seed_c := (kdfCk (chainKeyAt (createChain st₀.rk theirPk_c st₀.dhs).2 msg₀.counter.toNat)).2
      TermShapeId theirPk_c ∧ theirPk_c.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g theirPk_c = gamma interpretation S g msg₀.ratchetKey ∧
      seed_c.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g seed_c = gamma interpretation S g mkSeed := by
  by_cases hrk_sid : TermShapeId msg₀.ratchetKey
  · refine ⟨msg₀.ratchetKey, hrk_sid, hrkK, rfl, ?_, ?_⟩
    · rw [← recvSeed_eq_of_findRecvChain_none hfind hseed]; exact hmk_ak
    · rw [← recvSeed_eq_of_findRecvChain_none hfind hseed]
  · let T := runTraceMoves r₀ ms
    obtain ⟨p₀, idx₀, hstored₀⟩ := trStateStoredAt_of_mem_availableStates hst₀
    have hst₀_safe : StSafeRkS T T.length st₀ := (JRkS_reachable hreach (Trace.le_refl T)).2.1 p₀ st₀ idx₀ hstored₀
    have hmk_eq : mkSeed = KdfExtract.kdfExtract
        (chainKeyAt (createChain st₀.rk msg₀.ratchetKey st₀.dhs).2 msg₀.counter.toNat) (litByte 0x01) :=
      recvSeed_eq_of_findRecvChain_none hfind hseed
    have hmk_safe : KdfRkSafeS T mkSeed := kdfRkSafeS_of_attackerKnows_reachable hreach hmk_ak
    rw [hmk_eq] at hmk_safe
    have hckr_safe : KdfRkSafeS T (createChain st₀.rk msg₀.ratchetKey st₀.dhs).2 :=
      kdfRkSafeS_peel_chainKeyAt_exact msg₀.counter.toNat (kdfRkSafeS_peel_litByte_exact hmk_safe)
    have hprk_ak : (hmac st₀.rk (DiffieHellman.dh (X25519.normalizeX25519Key msg₀.ratchetKey) st₀.dhs)).AttackerKnows T :=
      kdfRkSafeS_peel_createChain_snd_exact interpretation S g hckr_safe hst₀_safe.1 hrk_sid
    have ⟨hrk_ak, hdh_ak⟩ : st₀.rk.AttackerKnows T ∧
        (DiffieHellman.dh (X25519.normalizeX25519Key msg₀.ratchetKey) st₀.dhs).AttackerKnows T := by
      rcases macKdfSafe_c_kdfExtract_inv r₀ ms st₀.rk
          (DiffieHellman.dh (X25519.normalizeX25519Key msg₀.ratchetKey) st₀.dhs) hreach hprk_ak with
        h | h01 | h02 | hwr1 | ⟨_, hwr2 | hwr2 | hwr2⟩
      · exact h
      · exact False.elim (dh_ne_literal_rks _ _ _ h01)
      · exact False.elim (dh_ne_literal_rks _ _ _ h02)
      · exact False.elim (dh_ne_concat_rks _ _ _ _ hwr1)
      · exact False.elim (dh_ne_concat_rks _ _ _ _ hwr2)
      · exact False.elim (dh_ne_concat_rks _ _ _ _ hwr2)
      · exact False.elim (dh_ne_concat_rks _ _ _ _ hwr2)
    have hvar : ∀ v : DY.X25519.Variant.SubF DY.Bytes,
        msg₀.ratchetKey.view? DY.X25519.Variant.SubF = some v → ¬(v.variation = 0 ∧ v.torsion = 0) :=
      variant_variation_ne_zero_of_attackerKnows_reachable hreach hrkK
    rcases hst₀_safe.1 with ⟨_, t₀, _, hdhs₀, _⟩; rw [hdhs₀] at hdh_ak
    rcases dh_not_termShapeId_attackerKnows_cases interpretation S g hreach hrkK hdh_ak rfl with
      hdhs_ak | ⟨hdhPk_dhs_ak, a₀, hk_eq, _⟩
    · exact ⟨_, rkSwap_g1_seed_known interpretation hEq r₀ S g ms msg₀ st₀ mkSeed hfind hseed hvar hrk_ak (hdhs₀ ▸ hdhs_ak)⟩
    · exact ⟨_, rkSwap_g2_seed_known interpretation hEq r₀ S g ms msg₀ st₀ mkSeed a₀ hfind hseed hvar hrk_ak (hdhs₀ ▸ hdhPk_dhs_ak) hk_eq⟩

end Symbolic.Swarm.CREF.TR.G1
