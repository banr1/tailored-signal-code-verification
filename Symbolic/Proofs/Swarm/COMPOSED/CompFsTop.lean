/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompSchedule
public import Symbolic.Proofs.Swarm.COMPOSED.CompTightClosed
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
import DY.Misc.Fixpoint
import DY.ALaCarte.Basic
import DY.ALaCarte.Ordering
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Swarm.COMPOSED.CompClosedInv
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv

/-!
# Composed Forward Secrecy

Establishes `Security.ForwardSecrecy` (`composed_forward_secrecy`) for the composed PQXDH, SPQR,
and Triple Ratchet model. Connects `CompRkSteps` and `CompChainRootFrom1` to `RootDescends` and
`DerivesChain`, proves backward schedule inversion under `CompTrClosed (CompStructuredExposure tr)`
and handshake-root compromise attribution (`handshakeRootCompromised_of_compTrClosed_hmac_zeroSalt`),
and assembles `FSQuery` on every reachable trace.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet (hmac hkdfBlock1 hkdfBlock2 litByte kdfRk createChain kdfCk
  chainKeyAt zeroSalt DerivesMsgKey RootDescends DerivesChain)
open DY.Libsignal.PQXDH (PQXDHEvent HandshakeKeys pqxdhKdf pqxdhIkm pqxdhLabel agree HandshakeKeysAt
  HandshakeWasCompromisedAt)
open DY.Libsignal.TripleRatchet (trMsgKeys)
open DY.Libsignal.TripleRatchet.Cheval (TRKeyKnown HandshakeRootCompromised
  CompromisedKey MessageSeedUsed FSQuery)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompKeyInversion
open Symbolic.Swarm.COMPOSED.CompTrace

/-! ## Schedule disjointness and KDF genealogy -/

theorem mkRand_ne_kdfExtract (ts sz : Nat) (s m : Bytes) :
    mkRand ts sz ≠ kdfExtract s m := by
  intro h
  dsimp [mkRand, KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

theorem CompRkSteps.exists_hkdfBlock1 {dh₁ ikm rk : Bytes} {d : Nat}
    (hrk : CompRkSteps dh₁ d (pqxdhKdf ikm).rk rk) : ∃ p i, rk = hkdfBlock1 p i := by
  cases hrk <;> exact ⟨_, _, rfl⟩

theorem CompChainRootFrom1.exists_hkdfBlock2 {dh₁ ikm ck₀ : Bytes} {m : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀) : ∃ p i, ck₀ = hkdfBlock2 p i := by
  rcases m with _ | _ | k
  · rw [hroot]; exact ⟨_, _, rfl⟩
  · rw [hroot]; exact ⟨_, _, rfl⟩
  · obtain ⟨_, _, _, _, rfl⟩ := hroot; exact ⟨_, _, rfl⟩

theorem compChainRootFrom1_chainKeyAt_ne_kdfCk_snd {dh₁ ikm ck₀ ck : Bytes} {m : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀) (j : Nat) :
    chainKeyAt ck₀ j ≠ (kdfCk ck).2 := by
  cases j with
  | zero => obtain ⟨p, i, rfl⟩ := hroot.exists_hkdfBlock2; exact hkdfBlock2_ne_kdfCk_snd p i ck
  | succ _ => rw [chainKeyAt_succ_eq_kdfCk_fst]; exact kdfCk_fst_ne_snd _ _

theorem compRkSteps_ne_kdfCk_snd {dh₁ ikm rk ck : Bytes} {d : Nat}
    (hrk : CompRkSteps dh₁ d (pqxdhKdf ikm).rk rk) :
    rk ≠ (kdfCk ck).2 := by
  obtain ⟨p, i, rfl⟩ := hrk.exists_hkdfBlock1; exact hkdfBlock1_ne_kdfCk_snd p i ck

theorem compRkSteps_ne_compChainRootFrom1_chainKeyAt
    {dh₁ dh₂ ikm₁ ikm₂ rk ck₀ : Bytes} {d m j : Nat}
    (hrk : CompRkSteps dh₁ d (pqxdhKdf ikm₁).rk rk)
    (hroot : CompChainRootFrom1 dh₂ ikm₂ m ck₀) :
    rk ≠ chainKeyAt ck₀ j := by
  obtain ⟨p₁, i₁, rfl⟩ := hrk.exists_hkdfBlock1
  cases j with
  | zero =>
    obtain ⟨p₂, i₂, rfl⟩ := hroot.exists_hkdfBlock2
    exact hkdfBlock1_ne_hkdfBlock2 p₁ i₁ p₂ i₂
  | succ _ =>
    rw [chainKeyAt_succ_eq_kdfCk_fst]; exact hkdfBlock1_ne_kdfCk_fst p₁ i₁ _

theorem CompRkSteps.to_rootDescends {dh₁ rk₀ rk : Bytes} {d : Nat}
    (hd : ∃ p sk, dh₁ = DiffieHellman.dh (DY.X25519.normalizeX25519Key p) sk)
    (hrk : CompRkSteps dh₁ d rk₀ rk) : RootDescends rk₀ rk := by
  induction hrk with
  | zero => exact .refl
  | step_one _ =>
    obtain ⟨p, sk, rfl⟩ := hd
    exact .step (theirPk := p) (ourSk := sk) .refl
  | @step_succ _ _ _ pk' sk' _ ih =>
    exact .step (theirPk := pk') (ourSk := sk') ih

theorem CompChainRootFrom1.derivesChain_root_of_pos {dh₁ ikm ck₀ : Bytes} {m : Nat}
    (hm : 1 ≤ m)
    (hd : ∃ p sk, dh₁ = DiffieHellman.dh (DY.X25519.normalizeX25519Key p) sk)
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀) :
    DerivesChain (pqxdhKdf ikm).rk ck₀ := by
  rcases m with _ | _ | k
  · omega
  · obtain ⟨p, sk, hdh⟩ := hd
    dsimp [CompChainRootFrom1] at hroot
    exact ⟨(pqxdhKdf ikm).rk, p, sk, .refl, hroot.trans (by rw [hdh]; rfl)⟩
  · obtain ⟨rk, pk, sk, hrk, rfl⟩ := hroot
    exact ⟨rk, pk, sk, hrk.to_rootDescends hd, rfl⟩

private theorem derivesMsgKey_of_chainKeyAt_le {ck₀ mk : Bytes} {j n : Nat}
    (hj : j ≤ n) (hmk : mk = (kdfCk (chainKeyAt ck₀ n)).2) :
    DerivesMsgKey (chainKeyAt ck₀ j) mk := by
  refine ⟨n - j, ?_⟩
  rw [hmk, ← chainKeyAt_add, Nat.add_sub_of_le hj]

/-! ## `CompStructuredExposure` disjointness and backward KDF inversion -/

theorem not_isScheduleKey_mkRand (ts sz : Nat) : ¬ IsScheduleKey (mkRand ts sz) := by
  intro h; obtain ⟨s, m, hEq⟩ := h.exists_kdfExtract; exact mkRand_ne_kdfExtract ts sz s m hEq

theorem compStructuredExposure_mkRand_iff (tr : ExecTrace) (ts sz : Nat) :
    CompStructuredExposure tr (mkRand ts sz) ↔
      ((mkRand ts sz).AttackerKnows tr ∨
        Symbolic.Swarm.COMPOSED.CompInv.MsgEncRandAt tr (mkRand ts sz)) := by
  refine ⟨fun h => ?_, CompStructuredExposure.rand⟩
  generalize hq : mkRand ts sz = q at h
  cases h with
  | rand hk => obtain ⟨rfl, rfl⟩ := mkRand_inj hq; exact hk
  | pqr => exact False.elim (mkRand_ne_kdfExtract ts sz _ _ hq)
  | exposedRK hrk _ => obtain ⟨_, _, _, rfl⟩ := hrk; exact False.elim (mkRand_ne_kdfExtract ts sz _ _ hq)
  | exposedCKs hsk _ => exact False.elim (not_isScheduleKey_mkRand ts sz (hq ▸ hsk))
  | exposedCKr hsk _ => exact False.elim (not_isScheduleKey_mkRand ts sz (hq ▸ hsk))
  | exposedMK hseed _ => obtain ⟨_, rfl⟩ := hseed; exact False.elim (mkRand_ne_kdfExtract ts sz _ _ hq)

theorem compTrClosed_mkRand_iff (tr : ExecTrace) (ts sz : Nat) :
    CompTrClosed (CompStructuredExposure tr) (mkRand ts sz) ↔
      ((mkRand ts sz).AttackerKnows tr ∨
        Symbolic.Swarm.COMPOSED.CompInv.MsgEncRandAt tr (mkRand ts sz)) :=
  ⟨fun h => (compStructuredExposure_mkRand_iff tr ts sz).mp (CompTrClosed.inv_rnd h),
   fun hk => .exposed (.rand hk)⟩

theorem dh_ne_concat (p s a b : Bytes) : DiffieHellman.dh p s ≠ Concat.concat a b := by
  intro h
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh, Concat.concat, Concat.CanConcat.concat] at h
  split at h
  · split at h <;> exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
  · exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

theorem dh_ne_litByte (p s : Bytes) (x : UInt8) : DiffieHellman.dh p s ≠ litByte x := by
  intro h
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh, litByte,
    Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes] at h
  split at h
  · split at h <;> exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
  · exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

theorem zeroSalt_ne_kdfExtract (s m : Bytes) : zeroSalt ≠ kdfExtract s m := by
  intro h
  dsimp [zeroSalt, Literal.bytesToLiteral, Literal.CanMkLiteral.bytesToLiteral,
    Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
    KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

theorem not_compStructuredExposure_of {tr : ExecTrace} {b : Bytes}
    (hrand : ∀ ts sz, b ≠ mkRand ts sz)
    (hpqr : ∀ ikm, b ≠ (pqxdhKdf ikm).pqr)
    (hrk : ∀ r p sk, b ≠ (createChain r p sk).1)
    (hsk : ¬ IsScheduleKey b)
    (hmk : ∀ c, b ≠ (kdfCk c).2) :
    ¬ CompStructuredExposure tr b := by
  intro h; generalize hq : b = q at h
  cases h with
  | rand _ => exact hrand _ _ hq
  | pqr => exact hpqr _ hq
  | exposedRK hrk' _ => obtain ⟨r, p, sk, rfl⟩ := hrk'; exact hrk r p sk hq
  | exposedCKs hsk' _ => exact hsk (hq ▸ hsk')
  | exposedCKr hsk' _ => exact hsk (hq ▸ hsk')
  | exposedMK hseed _ => obtain ⟨c, rfl⟩ := hseed; exact hmk c hq

theorem not_isScheduleKey_kdfExtract_dh (r p s : Bytes) :
    ¬ IsScheduleKey (kdfExtract r (DiffieHellman.dh p s)) := by
  rintro (⟨_, _, _, hEq⟩ | ⟨_, _, _, hEq⟩ | ⟨_, hEq⟩ | ⟨_, hEq⟩ | ⟨_, hEq⟩)
  · exact dh_ne_concat p s _ _ (hmac_inj hEq).2
  · exact dh_ne_concat p s _ _ (hmac_inj hEq).2
  · exact dh_ne_concat p s _ _ (hmac_inj hEq).2
  · exact dh_ne_litByte p s _ (hmac_inj hEq).2
  · exact dh_ne_litByte p s _ (hmac_inj hEq).2

theorem not_compStructuredExposure_kdfExtract_dh (tr : ExecTrace) (r p s : Bytes) :
    ¬ CompStructuredExposure tr (kdfExtract r (DiffieHellman.dh p s)) :=
  not_compStructuredExposure_of
    (fun _ _ h => mkRand_ne_kdfExtract _ _ _ _ h.symm)
    (fun _ h => dh_ne_concat p s _ _ (hmac_inj h).2)
    (fun _ _ _ h => dh_ne_concat p s _ _ (hmac_inj h).2)
    (not_isScheduleKey_kdfExtract_dh r p s)
    (fun _ h => dh_ne_litByte p s _ (hmac_inj h).2)

theorem not_isScheduleKey_trMsgKeys_cipherKey (pqSalt ck : Bytes) :
    ¬ IsScheduleKey (trMsgKeys pqSalt (kdfCk ck).2).cipherKey := by
  rintro (⟨r, p, sk, hEq⟩ | ⟨r, p, sk, hEq⟩ | ⟨ikm, hEq⟩ | ⟨c, hEq⟩ | ⟨c, hEq⟩)
  · exact trMsgKeys_cipherKey_ne_createChain_fst pqSalt ck r p sk hEq
  · exact trMsgKeys_cipherKey_ne_createChain_snd pqSalt ck r p sk hEq
  · exact hkdfBlock1_ne_hkdfBlock2 _ _ (hmac zeroSalt ikm) pqxdhLabel hEq
  · exact trMsgKeys_cipherKey_ne_kdfCk_fst pqSalt (kdfCk ck).2 c hEq
  · exact trMsgKeys_cipherKey_ne_kdfCk_snd pqSalt (kdfCk ck).2 c hEq

theorem not_compStructuredExposure_trMsgKeys_cipherKey (tr : ExecTrace) (pqSalt ck : Bytes) :
    ¬ CompStructuredExposure tr (trMsgKeys pqSalt (kdfCk ck).2).cipherKey :=
  not_compStructuredExposure_of
    (fun _ _ h => trMsgKeys_cipherKey_ne_mkRand pqSalt (kdfCk ck).2 _ _ h)
    (fun ikm h => hkdfBlock1_ne_hkdfBlock3 _ _ (hmac zeroSalt ikm) pqxdhLabel h)
    (fun r p sk h => trMsgKeys_cipherKey_ne_createChain_fst pqSalt ck r p sk h)
    (not_isScheduleKey_trMsgKeys_cipherKey pqSalt ck)
    (fun c h => trMsgKeys_cipherKey_ne_kdfCk_snd pqSalt (kdfCk ck).2 c h)

theorem not_isScheduleKey_hmac_kdfCk_snd (pqSalt ck : Bytes) :
    ¬ IsScheduleKey (hmac pqSalt (kdfCk ck).2) := by
  rintro (⟨r, p, sk, hEq⟩ | ⟨r, p, sk, hEq⟩ | ⟨_, hEq⟩ | ⟨c, hEq⟩ | ⟨c, hEq⟩)
  · exact hmac_kdfCk_snd_ne_createChain_fst pqSalt ck r p sk hEq
  · exact hmac_kdfCk_snd_ne_createChain_snd pqSalt ck r p sk hEq
  · exact concat_ne_kdfExtract _ _ _ _ (hmac_inj hEq).2.symm
  · exact hmac_kdfCk_snd_ne_kdfCk_fst pqSalt ck c hEq
  · exact hmac_kdfCk_snd_ne_kdfCk_snd pqSalt ck c hEq

theorem not_compStructuredExposure_hmac_kdfCk_snd (tr : ExecTrace) (pqSalt ck : Bytes) :
    ¬ CompStructuredExposure tr (hmac pqSalt (kdfCk ck).2) :=
  not_compStructuredExposure_of
    (fun _ _ h => hmac_kdfCk_snd_ne_mkRand pqSalt ck _ _ h)
    (fun _ h => concat_ne_kdfExtract _ _ _ _ (hmac_inj h).2.symm)
    (fun r p sk h => hmac_kdfCk_snd_ne_createChain_fst pqSalt ck r p sk h)
    (not_isScheduleKey_hmac_kdfCk_snd pqSalt ck)
    (fun c h => hmac_kdfCk_snd_ne_kdfCk_snd pqSalt ck c h)

theorem not_isScheduleKey_pqxdhKdf_rk (ikm : Bytes) :
    ¬ IsScheduleKey (pqxdhKdf ikm).rk := by
  rintro (⟨r, p, sk, hEq⟩ | ⟨_, _, _, hEq⟩ | ⟨ikm', hEq⟩ | ⟨c, hEq⟩ | ⟨c, hEq⟩)
  · exact pqxdhKdf_rk_ne_createChain_fst ikm r p sk hEq
  · exact hkdfBlock1_ne_hkdfBlock2 (hmac zeroSalt ikm) pqxdhLabel _ _ hEq
  · exact hkdfBlock1_ne_hkdfBlock2 (hmac zeroSalt ikm) pqxdhLabel (hmac zeroSalt ikm') pqxdhLabel hEq
  · exact hkdfBlock1_ne_kdfCk_fst (hmac zeroSalt ikm) pqxdhLabel c hEq
  · exact hkdfBlock1_ne_kdfCk_snd (hmac zeroSalt ikm) pqxdhLabel c hEq

theorem not_compStructuredExposure_pqxdhKdf_rk (tr : ExecTrace) (ikm : Bytes) :
    ¬ CompStructuredExposure tr (pqxdhKdf ikm).rk :=
  not_compStructuredExposure_of
    (fun _ _ h => mkRand_ne_kdfExtract _ _ _ _ h.symm)
    (fun ikm' h => hkdfBlock1_ne_hkdfBlock3 (hmac zeroSalt ikm) pqxdhLabel (hmac zeroSalt ikm') pqxdhLabel h)
    (fun r p sk h => pqxdhKdf_rk_ne_createChain_fst ikm r p sk h)
    (not_isScheduleKey_pqxdhKdf_rk ikm)
    (fun c h => hkdfBlock1_ne_kdfCk_snd (hmac zeroSalt ikm) pqxdhLabel c h)

theorem not_isScheduleKey_hmac_zeroSalt_concat (a b : Bytes) :
    ¬ IsScheduleKey (hmac zeroSalt (Concat.concat a b)) := by
  rintro (⟨_, _, _, hEq⟩ | ⟨_, _, _, hEq⟩ | ⟨_, hEq⟩ | ⟨_, hEq⟩ | ⟨_, hEq⟩)
  · exact zeroSalt_ne_kdfExtract _ _ (hmac_inj hEq).1
  · exact zeroSalt_ne_kdfExtract _ _ (hmac_inj hEq).1
  · exact zeroSalt_ne_kdfExtract _ _ (hmac_inj hEq).1
  · exact litByte_ne_concat _ a b (hmac_inj hEq).2.symm
  · exact litByte_ne_concat _ a b (hmac_inj hEq).2.symm

theorem not_compStructuredExposure_hmac_zeroSalt_concat (tr : ExecTrace) (a b : Bytes) :
    ¬ CompStructuredExposure tr (hmac zeroSalt (Concat.concat a b)) :=
  not_compStructuredExposure_of
    (fun _ _ h => mkRand_ne_kdfExtract _ _ _ _ h.symm)
    (fun _ h => zeroSalt_ne_kdfExtract _ _ (hmac_inj h).1)
    (fun _ _ _ h => zeroSalt_ne_kdfExtract _ _ (hmac_inj h).1)
    (not_isScheduleKey_hmac_zeroSalt_concat a b)
    (fun _ h => litByte_ne_concat _ a b (hmac_inj h).2.symm)

theorem CompStructuredExposure.exists_rand_or_kdf {tr : ExecTrace} {b : Bytes}
    (h : CompStructuredExposure tr b) :
    (∃ ts sz, b = mkRand ts sz) ∨ (∃ s m, b = kdfExtract s m) := by
  rcases h with ⟨_⟩ | _ | ⟨⟨r, p, sk, rfl⟩, _⟩ | ⟨hsk, _⟩ | ⟨hsk, _⟩ | ⟨⟨c, rfl⟩, _⟩
  · exact .inl ⟨_, _, rfl⟩
  · exact .inr ⟨_, _, rfl⟩
  · exact .inr ⟨_, _, rfl⟩
  · exact .inr hsk.exists_kdfExtract
  · exact .inr hsk.exists_kdfExtract
  · exact .inr ⟨_, _, rfl⟩

theorem CompTrClosed.inv_dh_pack {tr : ExecTrace} {sk pk : Bytes}
    (h : CompTrClosed (CompStructuredExposure tr)
      (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack)) :
    CompTrClosed (CompStructuredExposure tr) sk ∨
    (∃ s, pk = DiffieHellman.dhPk s ∧ CompTrClosed (CompStructuredExposure tr) s) := by
  generalize hq : (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack) = q at h
  cases h with
  | exposed hexp =>
    rcases hexp.exists_rand_or_kdf with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> {
      dsimp [mkRand, KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
    }
  | dhSk _ _ hsk =>
    have hv := congrArg (fun b : Bytes => b.view? DiffieHellman.Dh.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hv
    exact hv.2 ▸ .inl hsk
  | dhPeer _ s hs =>
    have hv := congrArg (fun b : Bytes => b.view? DiffieHellman.Dh.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hv
    exact .inr ⟨s, hv.1, hs⟩
  | _ =>
    try dsimp [Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
      DiffieHellman.dhPk, DiffieHellman.CanDH.dhPk,
      PQKem.kemPk, PQKem.CanPQKem.kemPk, PQKem.kemEncap, PQKem.CanPQKem.kemEncap,
      Signature.vk, Signature.CanSign.vk, Signature.sign, Signature.CanSign.sign,
      Trunc.trunc8, Trunc.CanTrunc8.trunc8,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract,
      Concat.concat, Concat.CanConcat.concat,
      SymEnc.symEnc, SymEnc.CanSymEnc.symEnc,
      TrWire.trWireMsg, TrWire.CanTrWireMsg.trWireMsg,
      Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_dh_dhPk {tr : ExecTrace} {a b : Bytes}
    (h : CompTrClosed (CompStructuredExposure tr) (DiffieHellman.dh (DiffieHellman.dhPk a) b)) :
    CompTrClosed (CompStructuredExposure tr) a ∨ CompTrClosed (CompStructuredExposure tr) b := by
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh] at h
  split at h
  · rename_i sk2 hview
    simp only [DiffieHellman.dhPk, DiffieHellman.CanDH.dhPk, BytesView.view_pack,
      Option.some.injEq, DiffieHellman.DhPk.SubF.mk.injEq] at hview
    subst hview
    split at h
    · exact (CompTrClosed.inv_dh_pack h).elim .inr fun ⟨_, hs, hcs⟩ => dhPk_inj hs ▸ .inl hcs
    · exact (CompTrClosed.inv_dh_pack h).elim .inl fun ⟨_, hs, hcs⟩ => dhPk_inj hs ▸ .inr hcs
  · exact (CompTrClosed.inv_dh_pack h).elim .inr fun ⟨_, hs, hcs⟩ => dhPk_inj hs ▸ .inl hcs

theorem CompTrClosed.inv_agree_dhPk {tr : ExecTrace} {a b : Bytes}
    (h : CompTrClosed (CompStructuredExposure tr) (agree (DiffieHellman.dhPk a) b)) :
    CompTrClosed (CompStructuredExposure tr) a ∨ CompTrClosed (CompStructuredExposure tr) b := by
  unfold agree at h; rw [x25519Key_dhPk] at h; exact CompTrClosed.inv_dh_dhPk h

theorem CompTrClosed.inv_ss {tr : ExecTrace} {pk e : Bytes}
    (h : CompTrClosed (CompStructuredExposure tr) (PQKem.kemEncap pk e).2) :
    (CompTrClosed (CompStructuredExposure tr) pk ∧ CompTrClosed (CompStructuredExposure tr) e) ∨
    (∃ sk, pk = PQKem.kemPk sk ∧ CompTrClosed (CompStructuredExposure tr) sk) := by
  generalize hq : (PQKem.kemEncap pk e).2 = q at h
  cases h with
  | exposed hexp =>
    rcases hexp.exists_rand_or_kdf with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> {
      dsimp [PQKem.kemEncap, PQKem.CanPQKem.kemEncap, mkRand,
        KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
    }
  | kemSs _ _ hpk he => obtain ⟨rfl, rfl⟩ := kemEncap_snd_inj hq; exact .inl ⟨hpk, he⟩
  | kemSsKey _ _ hsk => obtain ⟨rfl, rfl⟩ := kemEncap_snd_inj hq; exact .inr ⟨_, rfl, hsk⟩
  | _ =>
    try dsimp [Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
      DiffieHellman.dhPk, DiffieHellman.CanDH.dhPk,
      PQKem.kemPk, PQKem.CanPQKem.kemPk, PQKem.kemEncap, PQKem.CanPQKem.kemEncap,
      Signature.vk, Signature.CanSign.vk, Signature.sign, Signature.CanSign.sign,
      Trunc.trunc8, Trunc.CanTrunc8.trunc8,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract,
      Concat.concat, Concat.CanConcat.concat,
      SymEnc.symEnc, SymEnc.CanSymEnc.symEnc,
      TrWire.trWireMsg, TrWire.CanTrWireMsg.trWireMsg,
      Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_kdfRk_fst {E : Bytes → Prop}
    (hprk : ∀ r p s, ¬ E (kdfExtract r (DiffieHellman.dh p s)))
    {rk dh₁ : Bytes} (hd : ∃ p s, dh₁ = DiffieHellman.dh p s)
    (h : CompTrClosed E (kdfRk rk dh₁).1) :
    E (kdfRk rk dh₁).1 ∨ CompTrClosed E rk := by
  rcases CompTrClosed.inv_kdfExtract_salt h with hexp | h1
  · exact .inl hexp
  · obtain ⟨p, s, rfl⟩ := hd
    exact (CompTrClosed.inv_kdfExtract_salt h1).elim (fun e => False.elim (hprk _ _ _ e)) .inr

theorem CompTrClosed.inv_kdfRk_snd {E : Bytes → Prop}
    (hprk : ∀ r p s, ¬ E (kdfExtract r (DiffieHellman.dh p s)))
    {rk dh₁ : Bytes} (hd : ∃ p s, dh₁ = DiffieHellman.dh p s)
    (h : CompTrClosed E (kdfRk rk dh₁).2) :
    E (kdfRk rk dh₁).2 ∨ CompTrClosed E rk := by
  rcases CompTrClosed.inv_kdfExtract_salt h with hexp | h1
  · exact .inl hexp
  · obtain ⟨p, s, rfl⟩ := hd
    exact (CompTrClosed.inv_kdfExtract_salt h1).elim (fun e => False.elim (hprk _ _ _ e)) .inr

theorem CompTrClosed.inv_compRkSteps_descends {E : Bytes → Prop}
    (hprk : ∀ r p s, ¬ E (kdfExtract r (DiffieHellman.dh p s)))
    {dh₁ rk₀ rk : Bytes} {d : Nat}
    (hd : ∃ p s, dh₁ = DiffieHellman.dh p s)
    (hrk : CompRkSteps dh₁ d rk₀ rk) (h : CompTrClosed E rk) :
    (∃ d' ≤ d, ∃ rk', CompRkSteps dh₁ d' rk₀ rk' ∧ RootDescends rk' rk ∧ E rk') ∨
      CompTrClosed E rk₀ := by
  induction hrk with
  | zero => exact .inr h
  | @step_one rk₀' =>
    exact (CompTrClosed.inv_kdfRk_fst hprk hd h).elim
      (fun hexp => .inl ⟨1, Nat.le_refl 1, _, .step_one rk₀', .refl, hexp⟩) .inr
  | @step_succ k _ rk₁ pk sk hprev ih =>
    rcases CompTrClosed.inv_createChain_fst hprk h with hexp | hprev_c
    · exact .inl ⟨k + 2, Nat.le_refl _, _, .step_succ hprev, .refl, hexp⟩
    · exact (ih hprev_c).elim
        (fun ⟨d', hd', rk', hrk', hdesc, hexp⟩ =>
          .inl ⟨d', Nat.le_succ_of_le hd', rk', hrk', .step hdesc, hexp⟩) .inr

/-- Inverts `TRKeyKnown` along a `CompChainRootFrom1` chain, attributing attacker knowledge to an
exposed message key, chain key, intermediate root key, or initial handshake key. -/
theorem CompTrClosed.inv_compChainRootFrom1_descends {E : Bytes → Prop}
    (hprk : ∀ r p s, ¬ E (kdfExtract r (DiffieHellman.dh p s)))
    (hcipher : ∀ p c, ¬ E (trMsgKeys p (kdfCk c).2).cipherKey)
    (hprk_hyb : ∀ p c, ¬ E (hmac p (kdfCk c).2))
    {dh₁ ikm ck₀ pqSalt : Bytes} {m n : Nat}
    (hd : ∃ p s, dh₁ = DiffieHellman.dh p s)
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀)
    (h : TRKeyKnown (CompTrClosed E) (kdfCk (chainKeyAt ck₀ n)).2 pqSalt) :
    E (kdfCk (chainKeyAt ck₀ n)).2 ∨
    (∃ j ≤ n, E (chainKeyAt ck₀ j)) ∨
    (∃ d < m, ∃ rk', CompRkSteps dh₁ d (pqxdhKdf ikm).rk rk' ∧ DerivesChain rk' ck₀ ∧ E rk') ∨
    (m = 0 ∧ CompTrClosed E (pqxdhKdf ikm).ck) ∨
    (1 ≤ m ∧ CompTrClosed E (pqxdhKdf ikm).rk) := by
  have hseed := CompTrClosed.inv_trKeyKnown hcipher hprk_hyb h
  rcases CompTrClosed.inv_kdfCk_snd_chainKeyAt hseed with hexp | ⟨j, hj, hexp⟩ | hck₀
  · exact .inl hexp
  · exact .inr (.inl ⟨j, hj, hexp⟩)
  · rcases m with _ | _ | k
    · dsimp [CompChainRootFrom1] at hroot; subst hroot
      exact .inr (.inr (.inr (.inl ⟨rfl, hck₀⟩)))
    · dsimp [CompChainRootFrom1] at hroot; subst hroot
      exact (CompTrClosed.inv_kdfRk_snd hprk hd hck₀).elim
        (fun hexp => .inr (.inl ⟨0, Nat.zero_le n, hexp⟩))
        (fun hrk₀ => .inr (.inr (.inr (.inr ⟨Nat.le_refl 1, hrk₀⟩))))
    · obtain ⟨rk_prev, pk, sk, hrk, rfl⟩ := hroot
      rcases CompTrClosed.inv_createChain_snd hprk hck₀ with hexp | hrk_prev
      · exact .inr (.inl ⟨0, Nat.zero_le n, hexp⟩)
      · exact (CompTrClosed.inv_compRkSteps_descends hprk hd hrk hrk_prev).elim
          (fun ⟨d, hd', rk', hrk', hdesc, hexp⟩ =>
            .inr (.inr (.inl ⟨d, Nat.lt_succ_of_le hd', rk', hrk', ⟨rk_prev, pk, sk, hdesc, rfl⟩, hexp⟩)))
          (fun hrk₀ => .inr (.inr (.inr (.inr ⟨Nat.le_add_left 1 (k + 1), hrk₀⟩))))

section HandshakeBridge

open Symbolic.Swarm.COMPOSED.CompInv
open DY.Libsignal.PQXDH (aliceAgreement OPKAbsentOrCompromised)

theorem pub_of_compTrClosed_mkRand {tr : ExecTrace} (hinv : SpqrInv tr) {t sz : Nat}
    (h : CompTrClosed (CompStructuredExposure tr) (mkRand t sz)) :
    Pub tr (mkRand t sz) := by
  rcases (compTrClosed_mkRand_iff tr t sz).mp h with hk | hmsg
  · exact pub_of_knows hinv hk
  · exact Pub.rand (.inr (.inr (.inr (.inr (.inr (.inr (.inr hmsg)))))))

theorem pub_of_compTrClosed_ikAt {tr : ExecTrace} (hinv : SpqrInv tr) {p : Participant} {r : Bytes}
    (hik : IKAt tr p r) (h : CompTrClosed (CompStructuredExposure tr) r) : Pub tr r := by
  obtain ⟨_, rfl, _, _⟩ := hik; exact pub_of_compTrClosed_mkRand hinv h

theorem pub_of_compTrClosed_spkAt {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant} {r : Bytes}
    (hspk : SPKAt tr b r) (h : CompTrClosed (CompStructuredExposure tr) r) : Pub tr r := by
  obtain ⟨_, rfl, _, _, _⟩ := hspk; exact pub_of_compTrClosed_mkRand hinv h

theorem pub_of_compTrClosed_pqAt {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant} {r : Bytes}
    (hpq : PQAt tr b r) (h : CompTrClosed (CompStructuredExposure tr) r) : Pub tr r := by
  obtain ⟨_, rfl, _, _, _⟩ := hpq; exact pub_of_compTrClosed_mkRand hinv h

theorem pub_of_compTrClosed_opkAt {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant} {r : Bytes}
    (hopk : OPKAt tr b r) (h : CompTrClosed (CompStructuredExposure tr) r) : Pub tr r := by
  obtain ⟨_, rfl, _, _⟩ := hopk; exact pub_of_compTrClosed_mkRand hinv h

/-- Under `SpqrInv tr`, if `hmac zeroSalt ikm` is in `CompTrClosed (CompStructuredExposure tr)` for
a handshake at `doneIdx`, then `HandshakeWasCompromisedAt tr doneIdx` holds. -/
theorem handshakeExcusedAt_of_compTrClosed_hmac_zeroSalt {tr : ExecTrace}
    (hinv : SpqrInv tr)
    {doneIdx : Nat} {ikm : Bytes}
    (hhk : HandshakeKeysAt tr doneIdx (pqxdhKdf ikm))
    (hclosed : CompTrClosed (CompStructuredExposure tr) (hmac zeroSalt ikm)) :
    HandshakeWasCompromisedAt tr doneIdx := by
  have hE := isAtomic_compStructuredExposure tr
  rcases hhk with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hA⟩ | ⟨ek, ct, hB⟩⟩
  · refine .inl ⟨a, b, ikA, ikB, spk, pqpk, opk, ek, ct, pqxdhKdf ikm, hA, ?_⟩
    obtain ⟨t, sA, rfl, hslot, _hA_ik, _hikA, _hek, hagr, hbundle⟩ :=
      hinv.aliceDone a b ikA ikB spk pqpk opk ek ct (pqxdhKdf ikm) doneIdx hA
    rcases hbundle with ⟨sB, sS, sQ, hB, rfl, hS, rfl, hQ, rfl⟩ | ⟨j, hj, hlt⟩ | ⟨j, hj, hlt⟩
    rotate_left
    · exact .inl ⟨j, hj, .inl hlt⟩
    · exact .inr ⟨j, hj, .inl hlt⟩
    have hikm : ikm = pqxdhIkm (agree (DiffieHellman.dhPk sS) sA)
        (agree (DiffieHellman.dhPk sB) (rnd t 32))
        (agree (DiffieHellman.dhPk sS) (rnd t 32))
        (opk.map (agree · (rnd t 32)))
        (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).2 := by
      rcases hKem : PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32) with ⟨c, s⟩
      simp only [aliceAgreement, hKem, Prod.mk.injEq] at hagr
      exact pqxdhKdf_rk_inj (congrArg HandshakeKeys.rk hagr.2)
    rw [hikm] at hclosed
    rcases CompTrClosed.inv_kdfExtract_ikm hclosed with hexp | hikm_closed
    · exact False.elim (not_compStructuredExposure_hmac_zeroSalt_concat tr _ _ hexp)
    obtain ⟨_, hd2, hd3, _, hss⟩ :=
      pqxdhIkm_inv_generic (CompTrClosed.inv_concat hE) hikm_closed
    have hPQ : tr.EventLogged (PQXDHEvent.CompromisedPQSPK b (PQKem.kemPk sQ)) ∨
        tr.EventLogged PQXDHEvent.BrokenKEM := by
      rcases CompTrClosed.inv_ss hss with ⟨_, hc⟩ | ⟨sk, hsk, hpk⟩
      · exact absurd (pub_of_compTrClosed_mkRand hinv hc) (not_pub_coins hinv hslot)
      · obtain rfl := kemPk_inj hsk
        exact pub_PQ hinv hQ (pub_of_compTrClosed_pqAt hinv hQ hpk)
    rcases CompTrClosed.inv_agree_dhPk hd2 with h2 | h2
    · rcases pub_IK hinv hB (pub_of_compTrClosed_ikAt hinv hB h2) with ⟨j, hj⟩ | ⟨j, hj⟩
      · rcases CompTrClosed.inv_agree_dhPk hd3 with h3 | h3
        · rcases pub_SPK hinv hS (pub_of_compTrClosed_spkAt hinv hS h3) with hcs | ⟨j', hj'⟩
          · exact .inl ⟨j, hj, .inr ⟨hcs, hPQ⟩⟩
          · exact .inr ⟨j', hj', .inr hPQ⟩
        · obtain ⟨j', hj'⟩ := pub_EK hinv hslot (pub_of_compTrClosed_mkRand hinv h3)
          exact .inr ⟨j', hj', .inr hPQ⟩
      · exact .inr ⟨j, hj, .inr hPQ⟩
    · obtain ⟨j, hj⟩ := pub_EK hinv hslot (pub_of_compTrClosed_mkRand hinv h2)
      exact .inr ⟨j, hj, .inr hPQ⟩
  · refine .inr ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, pqxdhKdf ikm, hB, ?_⟩
    obtain ⟨sB, sS, sQ, o, ss, hsB, hikB, hsS, hspk, hsQ, hpqpk, ho, hopk,
      _hcan, hdec, hkeys, _hreg, hauth⟩ :=
      hinv.bobDone b a ikB ikA spk pqpk opk ek ct (pqxdhKdf ikm) doneIdx hB
    rcases hauth with ⟨j, a', b', spk', opk', _, hAlice⟩ | hCIK | hCSPK | hBDH
    · obtain ⟨t, sA, _, hSlot, _, _, hek_eq, hAliceAgree, _⟩ :=
        hinv.aliceDone a' b' ikA ikB spk' pqpk opk' ek ct (pqxdhKdf ikm) j hAlice
      have hct : ct = (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).1 := by
        simpa [aliceAgreement, hpqpk] using congrArg Prod.fst hAliceAgree
      have hss_eq : ss = (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).2 := by
        have hkd : DY.Libsignal.PQXDH.errToOption
            (PQKem.kemDecap sQ (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).1) =
            some (PQKem.kemEncap (PQKem.kemPk sQ) (rnd (t + 1) 32)).2 :=
          kemDecap_kemEncap sQ (rnd (t + 1) 32)
        rw [hdec, hct, hkd]; rfl
      have hikm : ikm = pqxdhIkm (agree ikA sS) (agree ek sB) (agree ek sS) (o.map (agree ek ·)) ss :=
        pqxdhKdf_rk_inj (congrArg HandshakeKeys.rk hkeys)
      rw [hikm] at hclosed
      rcases CompTrClosed.inv_kdfExtract_ikm hclosed with hexp | hikm_closed
      · exact False.elim (not_compStructuredExposure_hmac_zeroSalt_concat tr _ _ hexp)
      obtain ⟨_, hdh2, hdh3, hdh4, hssPub⟩ :=
        pqxdhIkm_inv_generic (CompTrClosed.inv_concat hE) hikm_closed
      rw [hss_eq] at hssPub
      have hpqPub : CompTrClosed (CompStructuredExposure tr) sQ := by
        rcases CompTrClosed.inv_ss hssPub with ⟨_, hcoins⟩ | ⟨sk, heq, hsk⟩
        · exact False.elim (not_pub_coins hinv hSlot (pub_of_compTrClosed_mkRand hinv hcoins))
        · exact kemPk_inj heq ▸ hsk
      have hpqLeak : tr.EventLogged (PQXDHEvent.CompromisedPQSPK b pqpk) ∨
          tr.EventLogged PQXDHEvent.BrokenKEM :=
        hpqpk ▸ pub_PQ hinv hsQ (pub_of_compTrClosed_pqAt hinv hsQ hpqPub)
      by_cases hBDH : tr.EventLogged PQXDHEvent.BrokenDH
      · exact .inr (.inr ⟨hBDH, hpqLeak⟩)
      · have hnotEk : ¬ CompTrClosed (CompStructuredExposure tr) (rnd t 32) := fun hekPub =>
          let ⟨j', hj'⟩ := pub_EK hinv hSlot (pub_of_compTrClosed_mkRand hinv hekPub)
          hBDH ⟨j', hj'⟩
        rw [hek_eq] at hdh2 hdh3 hdh4
        have hsBPub := (CompTrClosed.inv_agree_dhPk hdh2).resolve_left hnotEk
        have hsSPub := (CompTrClosed.inv_agree_dhPk hdh3).resolve_left hnotEk
        have hikBComp : tr.EventLogged (PQXDHEvent.CompromisedIK b ikB) := by
          rw [hikB]
          rcases pub_IK hinv hsB (pub_of_compTrClosed_ikAt hinv hsB hsBPub) with ⟨j', hj'⟩ | ⟨j', hj'⟩
          · exact ⟨j', hj'⟩
          · exact False.elim (hBDH ⟨j', hj'⟩)
        have hspkComp : tr.EventLogged (PQXDHEvent.CompromisedSPK b spk) := by
          rw [hspk]
          rcases pub_SPK hinv hsS (pub_of_compTrClosed_spkAt hinv hsS hsSPub) with hcs | ⟨j', hj'⟩
          · exact hcs
          · exact False.elim (hBDH ⟨j', hj'⟩)
        have hopkExc : OPKAbsentOrCompromised b opk doneIdx tr := by
          cases o with
          | none =>
            subst hopk
            exact .inl rfl
          | some sO =>
            subst hopk
            have hd4 := hdh4 (agree (DiffieHellman.dhPk (rnd t 32)) sO) rfl
            have hsOPub := (CompTrClosed.inv_agree_dhPk hd4).resolve_left hnotEk
            exact .inr ⟨DiffieHellman.dhPk sO, rfl,
              hinv.compOpk_loggedBefore hB
                ((pub_OPK hinv (ho sO rfl) (pub_of_compTrClosed_opkAt hinv (ho sO rfl) hsOPub)).resolve_right hBDH)⟩
        exact .inr (.inl ⟨hikBComp, hspkComp, hopkExc, hpqLeak⟩)
    · exact .inl (.inl hCIK)
    · exact .inl (.inr (.inl hCSPK))
    · exact .inl (.inr (.inr hBDH))

private theorem pqxdhKdf_rk_or_ck_inj {ikm₁ ikm₂ k : Bytes}
    (hk₁ : k = (pqxdhKdf ikm₁).rk ∨ k = (pqxdhKdf ikm₁).ck)
    (hk₂ : k = (pqxdhKdf ikm₂).rk ∨ k = (pqxdhKdf ikm₂).ck) :
    ikm₁ = ikm₂ := by
  rcases hk₁ with rfl | rfl <;> rcases hk₂ with h₂ | h₂
  · exact pqxdhKdf_rk_inj h₂
  · exact False.elim (hkdfBlock1_ne_hkdfBlock2 _ _ _ _ h₂)
  · exact False.elim (hkdfBlock1_ne_hkdfBlock2 _ _ _ _ h₂.symm)
  · exact pqxdhKdf_ck_inj h₂

/-- Under `SpqrInv tr`, if `hmac zeroSalt ikm` lies in `CompTrClosed (CompStructuredExposure tr)`
for a handshake at `doneIdx`, then `HandshakeRootCompromised tr k` holds for `k ∈ {rk, ck}`. -/
theorem handshakeRootCompromised_of_compTrClosed_hmac_zeroSalt {tr : ExecTrace}
    (hinv : SpqrInv tr)
    {doneIdx : Nat} {ikm k : Bytes}
    (hhk : HandshakeKeysAt tr doneIdx (pqxdhKdf ikm))
    (hclosed : CompTrClosed (CompStructuredExposure tr) (hmac zeroSalt ikm))
    (hk : k = (pqxdhKdf ikm).rk ∨ k = (pqxdhKdf ikm).ck) :
    HandshakeRootCompromised tr k := by
  refine ⟨⟨pqxdhKdf ikm, doneIdx, hhk, hk⟩, fun keys' j' hhk' hk' => ?_⟩
  obtain ⟨ikm', rfl⟩ := CompPubInv.handshakeKeysAt_eq_pqxdhKdf hinv hhk'
  obtain rfl := pqxdhKdf_rk_or_ck_inj hk hk'
  exact handshakeExcusedAt_of_compTrClosed_hmac_zeroSalt hinv hhk' hclosed

end HandshakeBridge

/-! ## Exposure inversion and `ForwardSecrecy` assembly -/

section ForwardSecrecyAssembly

open Symbolic.Swarm.COMPOSED.CompInv

theorem inv_compStructuredExposure_kdfCk_snd_compromised {tr : ExecTrace}
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOK tr ev)
    {ck₀ : Bytes} {n : UInt32}
    (hexp : CompStructuredExposure tr (kdfCk (chainKeyAt ck₀ n.toNat)).2) :
    CompromisedKey tr (kdfCk (chainKeyAt ck₀ n.toNat)).2 := by
  generalize hq : (kdfCk (chainKeyAt ck₀ n.toNat)).2 = q at hexp
  cases hexp with
  | rand _ => exact False.elim (mkRand_ne_kdfExtract _ _ _ _ hq.symm)
  | pqr => exact False.elim (litByte_ne_concat _ _ _ (hmac_inj hq).2)
  | exposedRK _ hev =>
    obtain ⟨_, _, _, _, _, _, _, hrk⟩ := hevOK _ hev
    exact False.elim (compRkSteps_ne_kdfCk_snd hrk hq.symm)
  | exposedCKs _ hev =>
    obtain ⟨_, _, _, _, _, _, _, hroot', hck⟩ := hevOK _ hev
    exact False.elim (compChainRootFrom1_chainKeyAt_ne_kdfCk_snd hroot' _ (hck.symm.trans hq.symm))
  | exposedCKr _ hev =>
    obtain ⟨_, _, _, _, _, _, _, hroot', hck⟩ := hevOK _ hev
    exact False.elim (compChainRootFrom1_chainKeyAt_ne_kdfCk_snd hroot' _ (hck.symm.trans hq.symm))
  | @exposedMK s' _ n' rIdx' _ hev =>
    exact .inr (.inr (.inr (.inr (.inl ⟨s', n', rIdx', hev⟩))))

theorem inv_compStructuredExposure_chainKeyAt_compromised {tr : ExecTrace}
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOK tr ev)
    {dh₁ ikm ck₀ : Bytes} {m j : Nat}
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀)
    (hexp : CompStructuredExposure tr (chainKeyAt ck₀ j)) :
    CompromisedKey tr (chainKeyAt ck₀ j) := by
  generalize hq : chainKeyAt ck₀ j = q at hexp
  cases hexp with
  | rand _ =>
    cases j with
    | zero =>
      obtain ⟨_, _, rfl⟩ := hroot.exists_hkdfBlock2
      exact False.elim (mkRand_ne_kdfExtract _ _ _ _ hq.symm)
    | succ _ =>
      rw [chainKeyAt_succ_eq_kdfCk_fst] at hq
      exact False.elim (mkRand_ne_kdfExtract _ _ _ _ hq.symm)
  | pqr =>
    cases j with
    | zero =>
      obtain ⟨p, i, rfl⟩ := hroot.exists_hkdfBlock2
      exact False.elim (hkdfBlock2_ne_hkdfBlock3 p i _ _ hq)
    | succ _ =>
      rw [chainKeyAt_succ_eq_kdfCk_fst] at hq
      exact False.elim (litByte_ne_concat _ _ _ (hmac_inj hq).2)
  | exposedRK _ hev =>
    obtain ⟨_, _, _, _, _, _, _, hrk⟩ := hevOK _ hev
    exact False.elim (compRkSteps_ne_compChainRootFrom1_chainKeyAt hrk hroot hq.symm)
  | exposedMK hseed _ =>
    obtain ⟨_, rfl⟩ := hseed
    exact False.elim (compChainRootFrom1_chainKeyAt_ne_kdfCk_snd hroot j hq)
  | @exposedCKs s' _ ns rIdx' _ hev =>
    exact .inr (.inr (.inl ⟨s', ns, rIdx', hev⟩))
  | @exposedCKr s' _ nr rIdx' _ hev =>
    exact .inr (.inr (.inr (.inl ⟨s', nr, rIdx', hev⟩)))

theorem inv_compStructuredExposure_compRkSteps_compromised {tr : ExecTrace}
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOK tr ev)
    {dh₁ ikm rk' : Bytes} {d : Nat}
    (hrk : CompRkSteps dh₁ d (pqxdhKdf ikm).rk rk')
    (hexp : CompStructuredExposure tr rk') :
    CompromisedKey tr rk' := by
  generalize hq : rk' = q at hexp
  cases hexp with
  | rand _ =>
    obtain ⟨_, _, rfl⟩ := hrk.exists_hkdfBlock1
    exact False.elim (mkRand_ne_kdfExtract _ _ _ _ hq.symm)
  | pqr =>
    obtain ⟨p, i, rfl⟩ := hrk.exists_hkdfBlock1
    exact False.elim (hkdfBlock1_ne_hkdfBlock3 p i _ _ hq)
  | exposedCKs _ hev =>
    obtain ⟨_, _, _, _, _, _, _, hroot', hck⟩ := hevOK _ hev
    exact False.elim (compRkSteps_ne_compChainRootFrom1_chainKeyAt hrk hroot' (hq.trans hck))
  | exposedCKr _ hev =>
    obtain ⟨_, _, _, _, _, _, _, hroot', hck⟩ := hevOK _ hev
    exact False.elim (compRkSteps_ne_compChainRootFrom1_chainKeyAt hrk hroot' (hq.trans hck))
  | exposedMK hseed _ =>
    obtain ⟨_, rfl⟩ := hseed
    exact False.elim (compRkSteps_ne_kdfCk_snd hrk hq)
  | @exposedRK s' _ rIdx' _ hev =>
    exact .inl ⟨s', rIdx', hev⟩

theorem fsQuery_conclusion_of_compTrClosed {tr : ExecTrace}
    (hinv : SpqrInv tr)
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOK tr ev)
    {doneIdx m : Nat} {dh₁ ikm ck₀ mk pqSalt : Bytes} {n : UInt32}
    (hhk : HandshakeKeysAt tr doneIdx (pqxdhKdf ikm))
    (hd : ∃ p sk, dh₁ = DiffieHellman.dh (DY.X25519.normalizeX25519Key p) sk)
    (hroot : CompChainRootFrom1 dh₁ ikm m ck₀)
    (hmk : mk = (kdfCk (chainKeyAt ck₀ n.toNat)).2)
    (hknown : TRKeyKnown (CompTrClosed (CompStructuredExposure tr)) mk pqSalt) :
    CompromisedKey tr mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ CompromisedKey tr ck) ∨
    (∃ rk ck, DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ CompromisedKey tr rk) := by
  subst hmk
  have hd_any : ∃ p s, dh₁ = DiffieHellman.dh p s :=
    let ⟨p, sk, hdh⟩ := hd; ⟨DY.X25519.normalizeX25519Key p, sk, hdh⟩
  have hdm₀ : DerivesMsgKey ck₀ (kdfCk (chainKeyAt ck₀ n.toNat)).2 := ⟨n.toNat, rfl⟩
  rcases CompTrClosed.inv_compChainRootFrom1_descends
      (not_compStructuredExposure_kdfExtract_dh tr)
      (not_compStructuredExposure_trMsgKeys_cipherKey tr)
      (not_compStructuredExposure_hmac_kdfCk_snd tr)
      hd_any hroot hknown with
    hexp_mk | ⟨j, hj, hexp_ck⟩ | ⟨d, _, rk', hrk', hdc, hexp_rk⟩ | ⟨rfl, hck⟩ | ⟨hm1, hrk⟩
  · exact .inl (inv_compStructuredExposure_kdfCk_snd_compromised hevOK hexp_mk)
  · exact .inr (.inl ⟨chainKeyAt ck₀ j, derivesMsgKey_of_chainKeyAt_le hj rfl,
      inv_compStructuredExposure_chainKeyAt_compromised hevOK hroot hexp_ck⟩)
  · exact .inr (.inr ⟨rk', ck₀, hdc, hdm₀,
      inv_compStructuredExposure_compRkSteps_compromised hevOK hrk' hexp_rk⟩)
  · rcases CompTrClosed.inv_kdfExtract_salt hck with hexp | hprk
    · have hroot0 : ck₀ = (pqxdhKdf ikm).ck := hroot
      have hexp0 : CompStructuredExposure tr (chainKeyAt ck₀ 0) :=
        hroot0.symm ▸ (hexp : CompStructuredExposure tr (pqxdhKdf ikm).ck)
      exact .inr (.inl ⟨ck₀, hdm₀, inv_compStructuredExposure_chainKeyAt_compromised hevOK hroot hexp0⟩)
    · have hroot0 : ck₀ = (pqxdhKdf ikm).ck := hroot
      have hcomp : CompromisedKey tr ck₀ :=
        .inr (.inr (.inr (.inr (.inr (.inl
          (handshakeRootCompromised_of_compTrClosed_hmac_zeroSalt hinv hhk hprk (.inr hroot0)))))))
      exact .inr (.inl ⟨ck₀, hdm₀, hcomp⟩)
  · rcases CompTrClosed.inv_kdfExtract_salt hrk with hexp | hprk
    · exact False.elim (not_compStructuredExposure_pqxdhKdf_rk tr ikm hexp)
    · have hdc : DerivesChain (pqxdhKdf ikm).rk ck₀ :=
        hroot.derivesChain_root_of_pos hm1 hd
      have hcomp : CompromisedKey tr (pqxdhKdf ikm).rk :=
        .inr (.inr (.inr (.inr (.inr (.inl
          (handshakeRootCompromised_of_compTrClosed_hmac_zeroSalt hinv hhk hprk (.inl rfl)))))))
      exact .inr (.inr ⟨(pqxdhKdf ikm).rk, ck₀, hdc, hdm₀, hcomp⟩)

theorem composed_forward_secrecy_of_invs {tr : ExecTrace}
    (hinv : SpqrInv tr)
    (hevOK : ∀ ev, tr.EventLogged ev → CompEventScheduleOK tr ev)
    (hclosed : ∀ t : Bytes, t.AttackerKnows tr → CompTrClosed (CompStructuredExposure tr) t) :
    FSQuery tr := by
  intro mk pqSalt hmk htrkn
  obtain ⟨s, dir, n, i, parIdx, hev⟩ := hmk
  have hknown : TRKeyKnown (CompTrClosed (CompStructuredExposure tr)) mk pqSalt :=
    htrkn.imp (hclosed _) (hclosed _)
  cases dir with
  | sender =>
    obtain ⟨_, _, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ := hevOK _ hev
    exact fsQuery_conclusion_of_compTrClosed hinv hevOK hs.2.1 hs.exists_dh hroot hseed hknown
  | receiver =>
    obtain ⟨_, _, doneIdx, ikm, dh₁, ck₀, hs, hroot, hseed⟩ := hevOK _ hev
    exact fsQuery_conclusion_of_compTrClosed hinv hevOK hs.2.1 hs.exists_dh hroot hseed hknown

/-- Forward secrecy (`FSQuery`) holds on every reachable trace of the composed protocol. -/
theorem composed_forward_secrecy : Security.ForwardSecrecy :=
  fun tr hreach =>
    composed_forward_secrecy_of_invs
      (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr hreach)
      (compScheduleInv_reachable hreach).eventOK
      (fun _ hk => attackerKnows_implies_compTrClosed hreach hk)

end ForwardSecrecyAssembly

end Symbolic.Swarm.COMPOSED.CompRatchet
