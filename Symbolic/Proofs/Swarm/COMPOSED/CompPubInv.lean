/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.X25519
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra

/-!
# `Pub` Constructor Inversions, Attacker-Knowledge Closure, and Bundle Origin

Proves constructor inversions and attacker-knowledge closure for `Pub` on `SpqrInv` traces,
establishes `CompExposure` domain separation and per-block `pqxdhKdf` inversion, and proves
honest identity-key secrecy (`pub_IK`) and prekey bundle signature origin (`bundleOK_of_verify`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompInv

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompKeyInversion

/-! ## `HandshakeKeysAt` Shape and `CompExposure.exists_kdfExtract` -/

namespace CompPubInv

theorem handshakeKeysAt_eq_pqxdhKdf {tr : ExecTrace} (hinv : SpqrInv tr) {j : Nat}
    {keys : HandshakeKeys} (hkeys : HandshakeKeysAt tr j keys) :
    ∃ ikm, keys = pqxdhKdf ikm := by
  rcases hkeys with ⟨a, b, ikA, ikB, spk, pqpk, opk, ⟨ek, ct, hA⟩ | ⟨ek, ct, hB⟩⟩
  · obtain ⟨t, sA, _, _, _, _, _, hagr, _⟩ :=
      hinv.aliceDone a b ikA ikB spk pqpk opk ek ct keys j hA
    exact ⟨_, congrArg Prod.snd hagr⟩
  · obtain ⟨sB, sS, sQ, o, e, _, _, _, _, _, _, _, _, _, _, hkeys_eq, _, _⟩ :=
      hinv.bobDone b a ikB ikA spk pqpk opk ek ct keys j hB
    exact ⟨_, hkeys_eq⟩

theorem _root_.Symbolic.Swarm.COMPOSED.CompInv.CompExposure.exists_kdfExtract
    {tr : ExecTrace} (hinv : SpqrInv tr) {b : Bytes}
    (h : CompExposure tr b) : ∃ s m, b = KdfExtract.kdfExtract s m := by
  cases h with
  | pqr hexp =>
    obtain ⟨_, j, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, rfl⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    exact ⟨_, _, rfl⟩
  | ck0 hexp =>
    obtain ⟨_, j, _, hkeys, _⟩ := hexp
    obtain ⟨ikm, rfl⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    exact ⟨_, _, rfl⟩
  | ckStep _ _ =>
    rw [chainKeyAt_succ_eq_kdfCk_fst]
    exact ⟨_, _, rfl⟩
  | rkRatchet _ _ _ =>
    exact ⟨_, _, rfl⟩
  | @chainRatchet _ _ n _ _ _ _ _ _ =>
    cases n with
    | zero => exact ⟨_, _, rfl⟩
    | succ m =>
      rw [chainKeyAt_succ_eq_kdfCk_fst]
      exact ⟨_, _, rfl⟩
  | seedCk _ _ =>
    exact ⟨_, _, rfl⟩
  | seedRatchet _ _ _ =>
    exact ⟨_, _, rfl⟩

/-! ## `Pub` Constructor Inversions -/

section PubInversions
unseal Bytes

theorem Pub.inv_rand {tr : ExecTrace} (hinv : SpqrInv tr) {t n : Nat} (h : Pub tr (rnd t n)) :
    RandExposed tr (rnd t n) := by
  generalize hq : rnd t n = q at h
  cases h with
  | rand hr =>
    obtain ⟨rfl, rfl⟩ := rnd_inj hq
    exact hr
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [rnd, KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_cat {tr : ExecTrace} (hinv : SpqrInv tr) {l r : Bytes}
    (h : Pub tr (Concat.concat l r)) : Pub tr l ∧ Pub tr r := by
  generalize hq : Concat.concat l r = q at h
  cases h with
  | cat hl hr =>
    obtain ⟨rfl, rfl⟩ := concat_inj hq
    exact ⟨hl, hr⟩
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [Concat.concat, Concat.CanConcat.concat,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_kdf {tr : ExecTrace} {s m : Bytes}
    (h : Pub tr (KdfExtract.kdfExtract s m)) :
    CompExposure tr (KdfExtract.kdfExtract s m) ∨ (Pub tr s ∧ Pub tr m) := by
  generalize hq : KdfExtract.kdfExtract s m = q at h
  cases h with
  | exp hexp =>
    subst hq
    exact .inl hexp
  | kdf hs hm =>
    obtain ⟨rfl, rfl⟩ := kdfExtract_inj hq
    exact .inr ⟨hs, hm⟩
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_trunc {tr : ExecTrace} (hinv : SpqrInv tr) {m : Bytes}
    (h : Pub tr (Trunc.trunc8 m)) : Pub tr m ∨ HonestMac tr m := by
  generalize hq : Trunc.trunc8 m = q at h
  cases h with
  | trunc hm =>
    obtain rfl := Trunc.trunc8_inj _ _ hq
    exact .inl hm
  | truncHonest hm =>
    obtain rfl := Trunc.trunc8_inj _ _ hq
    exact .inr hm
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [Trunc.trunc8, Trunc.CanTrunc8.trunc8,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_dhPk {tr : ExecTrace} (hinv : SpqrInv tr) {sk : Bytes}
    (h : Pub tr (DiffieHellman.dhPk sk)) : DhClass tr sk ∨ Pub tr sk := by
  generalize hq : DiffieHellman.dhPk sk = q at h
  cases h with
  | dhPub hdh =>
    obtain rfl := dhPk_inj hq
    exact .inl hdh
  | dhPubK hsk =>
    obtain rfl := dhPk_inj hq
    exact .inr hsk
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [DiffieHellman.dhPk, DiffieHellman.CanDH.dhPk,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_dhPack {tr : ExecTrace} (hinv : SpqrInv tr) {sk pk : Bytes}
    (h : Pub tr ((({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes)).pack)) :
    Pub tr sk ∨ ∃ s, pk = DiffieHellman.dhPk s ∧ Pub tr s := by
  generalize hq : (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes)).pack = q at h
  cases h with
  | dhSk sk' pk' hsk =>
    cases Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    exact .inl hsk
  | dhPeer sk' s hs =>
    cases Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    exact .inr ⟨s, rfl, hs⟩
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_kemPk {tr : ExecTrace} (hinv : SpqrInv tr) {sk : Bytes}
    (h : Pub tr (PQKem.kemPk sk)) : PQClass tr sk ∨ Pub tr sk := by
  generalize hq : PQKem.kemPk sk = q at h
  cases h with
  | kemPub hpq =>
    obtain rfl := kemPk_inj hq
    exact .inl hpq
  | kemPubK hsk =>
    obtain rfl := kemPk_inj hq
    exact .inr hsk
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [PQKem.kemPk, PQKem.CanPQKem.kemPk,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_ss_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) {pk e : Bytes}
    (h : Pub tr (PQKem.kemEncap pk e).2) :
    (Pub tr pk ∧ Pub tr e) ∨ (∃ sk, pk = PQKem.kemPk sk ∧ Pub tr sk) := by
  generalize hq : (PQKem.kemEncap pk e).2 = q at h
  cases h with
  | ss hpk he =>
    obtain ⟨rfl, rfl⟩ := kemEncap_snd_inj hq
    exact .inl ⟨hpk, he⟩
  | ssKey e' hsk =>
    obtain ⟨rfl, rfl⟩ := kemEncap_snd_inj hq
    exact .inr ⟨_, rfl, hsk⟩
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [PQKem.kemEncap, PQKem.CanPQKem.kemEncap,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_rejKey_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr) {sk ct : Bytes}
    (h : Pub tr (PQKem.kemRejKey sk ct)) : Pub tr sk ∧ Pub tr ct := by
  generalize hq : PQKem.kemRejKey sk ct = q at h
  cases h with
  | rejKey hsk hct =>
    obtain ⟨rfl, rfl⟩ := kemRejKey_inj.mp hq
    exact ⟨hsk, hct⟩
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [PQKem.kemRejKey, PQKem.CanPQKem.kemRejKey,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap, PQKem.kemRejKey, PQKem.CanPQKem.kemRejKey,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_sign {tr : ExecTrace} (hinv : SpqrInv tr) {sk nonce msg : Bytes}
    (h : Pub tr (Signature.sign sk nonce msg)) : Pub tr sk ∨ HonestSig tr sk msg := by
  generalize hq : Signature.sign sk nonce msg = q at h
  cases h with
  | sig _ _ hsk =>
    obtain ⟨rfl, rfl, rfl⟩ := sign_inj hq
    exact .inl hsk
  | sigHonest _ _ hsig =>
    obtain ⟨rfl, rfl, rfl⟩ := sign_inj hq
    exact .inr hsig
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [Signature.sign, Signature.CanSign.sign,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_trWire {tr : ExecTrace} (hinv : SpqrInv tr)
    {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes} {ev : TrWire.EncodingVariation}
    (h : Pub tr (TrWire.trWireMsg v rk c pc ct pq ev)) :
    Pub tr rk ∧ Pub tr ct ∧ Pub tr pq := by
  generalize hq : TrWire.trWireMsg v rk c pc ct pq ev = q at h
  cases h with
  | trWire hrk hct hpq =>
    dsimp [TrWire.trWireMsg, TrWire.CanTrWireMsg.trWireMsg] at hq
    cases Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    exact ⟨hrk, hct, hpq⟩
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [TrWire.trWireMsg, TrWire.CanTrWireMsg.trWireMsg,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_enc {tr : ExecTrace} (hinv : SpqrInv tr) {k iv m : Bytes}
    (h : Pub tr (SymEnc.symEnc k iv m)) : Pub tr m := by
  generalize hq : SymEnc.symEnc k iv m = q at h
  cases h with
  | enc hm =>
    dsimp [SymEnc.symEnc, SymEnc.CanSymEnc.symEnc] at hq
    cases Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    exact hm
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [SymEnc.symEnc, SymEnc.CanSymEnc.symEnc,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_variant {tr : ExecTrace} (hinv : SpqrInv tr) {x : X25519.Variant.SubF Bytes}
    (h : Pub tr x.pack) : Pub tr x.key := by
  generalize hq : x.pack = q at h
  cases h with
  | var v hkey =>
    have hv := Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    cases x
    cases hv
    exact hkey
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_spqrInitPack {tr : ExecTrace} (hinv : SpqrInv tr) {x : Spqr.InitState.SubF Bytes}
    (h : Pub tr x.pack) : Pub tr x.authKey ∧ Pub tr x.params := by
  generalize hq : x.pack = q at h
  cases h with
  | spqrInit hk hp =>
    dsimp [Spqr.spqrInit] at hq
    have hv := Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    cases x
    cases hv
    exact ⟨hk, hp⟩
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_spqrSendStatePack {tr : ExecTrace} (hinv : SpqrInv tr)
    {x : Spqr.SendState.SubF Bytes} (h : Pub tr x.pack) : Pub tr x.st ∧ Pub tr x.coins := by
  generalize hq : x.pack = q at h
  cases h with
  | spqrSendState hst hc =>
    have hv := Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    cases x
    cases hv
    exact ⟨hst, hc⟩
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_spqrRecvStatePack {tr : ExecTrace} (hinv : SpqrInv tr)
    {x : Spqr.RecvState.SubF Bytes} (h : Pub tr x.pack) : Pub tr x.st ∧ Pub tr x.msg := by
  generalize hq : x.pack = q at h
  cases h with
  | spqrRecvState hst hm =>
    have hv := Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    cases x
    cases hv
    exact ⟨hst, hm⟩
  | exp hexp =>
    obtain ⟨_, _, rfl⟩ := hexp.exists_kdfExtract hinv
    dsimp [KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | _ =>
    try dsimp [rnd, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

end PubInversions

theorem SpqrStateFrom.pub_of_pub {tr : ExecTrace} {pqr spqr : Bytes}
    (h : SpqrStateFrom tr pqr spqr) (hpqr : Pub tr pqr) : Pub tr spqr := by
  induction h with
  | init hp => exact .spqrInit hpqr hp
  | send _ hc ih => exact .spqrSendState ih hc
  | recv _ hm ih => exact .spqrRecvState ih hm

theorem SpqrStateFrom.of_spqrSend {tr : ExecTrace} {pqr st coins : Bytes}
    (hst : SpqrStateFrom tr pqr st) (hcoins : Pub tr coins) :
    SpqrStateFrom tr pqr (Spqr.spqrSend st coins).1 :=
  .send hst hcoins

theorem SpqrStateFrom.of_spqrRecv {tr : ExecTrace} {pqr st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r)
    (hst : SpqrStateFrom tr pqr st) (hmsg : Pub tr msg) :
    SpqrStateFrom tr pqr r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]
  exact .recv hst hmsg

/-! ## Attacker-Knowledge Closure -/

theorem Pub.dh {tr : ExecTrace} {pk sk : Bytes} (hsk : Pub tr sk) :
    Pub tr (DiffieHellman.dh pk sk) := by
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 _
    split
    · exact .dhSk sk (DiffieHellman.dhPk sk2) hsk
    · exact .dhPeer sk2 sk hsk
  · exact .dhSk sk pk hsk

theorem Pub.normalizeX25519Key {tr : ExecTrace} (hinv : SpqrInv tr) {pk : Bytes} (h : Pub tr pk) :
    Pub tr (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key
  have hp := Bytes.pack_view? X25519.Variant.SubF pk
  cases hv : pk.view? X25519.Variant.SubF with
  | none => exact h
  | some x =>
    rw [hv] at hp
    rw [← hp] at h
    exact Pub.inv_variant hinv h

theorem Pub.x25519TorsionVariant {tr : ExecTrace} (hinv : SpqrInv tr) {key : Bytes} (v : Fin 4) (t : Fin 8)
    (h : Pub tr key) : Pub tr (X25519.x25519TorsionVariant key v t) := by
  dsimp [X25519.x25519TorsionVariant]
  split
  · exact Pub.normalizeX25519Key hinv h
  · exact .var v (Pub.normalizeX25519Key hinv h)

theorem Pub.spqrSendKey_of {tr : ExecTrace} (st coins : Bytes) :
    Pub tr (Spqr.spqrSend st coins).2.1 := by
  unfold Spqr.spqrSend
  dsimp only
  cases st.view? Spqr.InitState.SubF with
  | none => exact .spqrSendKey st coins
  | some x => exact .spqrChainKey x.authKey x.params (Spqr.encodeSpqrIndexTerm 1)

theorem Pub.spqrRecvState_of {tr : ExecTrace} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r)
    (hst : Pub tr st) (hm : Pub tr msg) : Pub tr r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]
  exact .spqrRecvState hst hm

theorem Pub.spqrRecvKey_of {tr : ExecTrace} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) : Pub tr r.2 := by
  unfold Spqr.spqrRecv at hrecv
  split at hrecv
  · cases hrecv
  · cases hv : st.view? Spqr.InitState.SubF with
    | none =>
      rw [hv] at hrecv
      injection hrecv with hrecv'
      subst hrecv'
      exact .spqrRecvKey st msg
    | some x =>
      rw [hv] at hrecv
      rcases x with ⟨authKey, params⟩
      dsimp only at hrecv
      cases hd : Spqr.spqrParamsDir? params with
      | none =>
        rw [hd] at hrecv
        cases hrecv
      | some dir =>
        rw [hd] at hrecv
        injection hrecv with hrecv'
        subst hrecv'
        dsimp only
        split
        · exact .literal _
        · exact .spqrChainKey authKey _ (Spqr.encodeSpqrIndexTerm idx)

theorem Pub.attackerKnowledge_implies {tr : ExecTrace} (hinv : SpqrInv tr) :
    SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge (Pub tr) := by
  change SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge (Pub tr)
  dsimp [DY.Libsignal.Composed.attackerKnowledge]
  apply SubAttackerKnowledge.combine.implies
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hlt⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
    intro b hb
    rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hb
    exact hb.elim
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Literal.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · intro b hb
      dsimp [Literal.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hb
      rcases hb with ⟨bs, rfl⟩
      exact .literal bs
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Concat.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | n, hlt'⟩
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hb
      rcases hb with ⟨lhs, rhs, rfl, hlhs, hrhs⟩
      exact .cat hlhs hrhs
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, rhs, i, hsplit, hinp⟩
      exact (Pub.inv_cat hinv (Concat.concat_split inp i b rhs hsplit.symm ▸ hinp)).1
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, lhs, i, hsplit, hinp⟩
      exact (Pub.inv_cat hinv (Concat.concat_split inp i lhs b hsplit.symm ▸ hinp)).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, hsk⟩
      exact .dhPubK hsk
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, sk, rfl, _, hsk⟩
      exact Pub.dh hsk
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, KdfExtract.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · intro b hb
      dsimp [KdfExtract.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hb
      rcases hb with ⟨salt, ikm, rfl, hsalt, hikm⟩
      exact .kdf hsalt hikm
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, SymEnc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨k, iv, msg, rfl, _, _, hmsg⟩
      exact .enc hmsg
    · rintro b ⟨key, iv, ct, hdec, _, _, hct⟩
      dsimp [SymEnc.symDec, SymEnc.CanSymEnc.symDec] at hdec
      have hp := Bytes.pack_view? SymEnc.Enc.SubF ct
      cases hv : ct.view? SymEnc.Enc.SubF with
      | none =>
        rw [hv] at hdec
        cases hdec
      | some x =>
        rw [hv] at hdec hp
        rcases x with ⟨k', iv', msg'⟩
        dsimp only at hdec hp
        split at hdec
        · injection hdec with hdec'
          subst hdec'
          rw [← hp] at hct
          exact Pub.inv_enc hinv hct
        · cases hdec
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · rintro b ⟨m, rfl, hm⟩
      exact .trunc hm
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨key, v, t, rfl, hkey⟩
      exact Pub.x25519TorsionVariant hinv v t hkey
    · rintro b ⟨x, hpack, rfl⟩
      exact Pub.inv_variant hinv hpack
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨sk, rfl, hsk⟩
      exact .kemPubK hsk
    · rintro b ⟨pk, e, rhs, heq, _, _⟩
      have h1 : b = (PQKem.kemEncap pk e).1 := congrArg Prod.fst heq
      rw [h1]
      exact .encap pk e
    · rintro b ⟨pk, e, lhs, heq, hpk, he⟩
      have h2 : b = (PQKem.kemEncap pk e).2 := congrArg Prod.snd heq
      rw [h2]
      exact .ss hpk he
    · rintro b ⟨sk, ct, hdec, hsk, _⟩
      obtain ⟨e, _, rfl⟩ := kemDecap_eq_some_iff.mp hdec.symm
      exact .ssKey e hsk
    · rintro b ⟨sk, ct, rfl, hsk, hct⟩
      exact .rejKey hsk hct
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Signature.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, hsk⟩
      exact .vkPubK hsk
    · intro b hb
      dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, nonce, msg, rfl, hsk, _, _⟩
      exact .sig nonce msg hsk
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Spqr.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨authKey, params, rfl, hk, hp⟩
      exact .spqrInit hk hp
    · rintro b ⟨authKey, params, idx, rfl, _, _, _⟩
      exact .spqrChainKey authKey params idx
    · rintro b ⟨st, coins, rfl, hst, hc⟩
      exact .spqrSendState hst hc
    · rintro b ⟨st, coins, rfl, _, _⟩
      exact Pub.spqrSendKey_of st coins
    · rintro b ⟨st, coins, rfl, _, _⟩
      exact .spqrSendMsg st coins
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, hst, hm⟩
      exact Pub.spqrRecvState_of hrecv hst hm
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, _, _⟩
      exact Pub.spqrRecvKey_of hrecv
    · rintro b (⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩)
      · exact (Pub.inv_spqrInitPack hinv hpack).1
      · exact (Pub.inv_spqrInitPack hinv hpack).2
      · exact (Pub.inv_spqrSendStatePack hinv hpack).1
      · exact (Pub.inv_spqrSendStatePack hinv hpack).2
      · exact (Pub.inv_spqrRecvStatePack hinv hpack).1
      · exact (Pub.inv_spqrRecvStatePack hinv hpack).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, rfl, hrk, hct, hpq⟩
      exact .trWire hrk hct hpq
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, hw, hmem⟩
      obtain ⟨hrk, hct, hpq⟩ := Pub.inv_trWire hinv hw
      rcases hmem with rfl | rfl | rfl <;> assumption
    · omega
  · omega

/-- Under `SpqrInv tr`, every attacker-derivable term satisfies `Pub tr`. -/
theorem Pub.of_attackerKnows {tr : ExecTrace} (hinv : SpqrInv tr)
    {x : Bytes} (hk : x.AttackerKnows tr) : Pub tr x := by
  refine Bytes.AttackerKnows.is_least_fixpoint (Pub tr) x tr
    (Pub.attackerKnowledge_implies hinv) (fun y hy => ?_) hk
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hy
  exact hinv.netPub y hy

/-! ## `CompExposure` Domain Separation and Handshake-Block Inversion -/

section ExposureDomainSeparation
unseal Bytes

/-- The intermediate HKDF extract key `hmac zeroSalt (pqxdhIkm d1 d2 d3 d4 ss)` is never in
`CompExposure tr` on a `SpqrInv tr` trace. -/
theorem CompExposure.not_hmac_zeroSalt_pqxdhIkm {tr : ExecTrace} (hinv : SpqrInv tr)
    {d1 d2 d3 : Bytes} {d4 : Option Bytes} {ss : Bytes} :
    ¬ CompExposure tr (hmac zeroSalt (pqxdhIkm d1 d2 d3 d4 ss)) := by
  intro hexp
  generalize hq : hmac zeroSalt (pqxdhIkm d1 d2 d3 d4 ss) = q at hexp
  cases hexp with
  | pqr hsse =>
    obtain ⟨_, j, _, hkeys, _⟩ := hsse
    obtain ⟨ikm', rfl⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    have hs := (hmac_inj hq).1
    dsimp [zeroSalt, pqxdhKdf, hmac,
      Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hs
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hs)
  | ck0 hsse =>
    obtain ⟨_, j, _, hkeys, _⟩ := hsse
    obtain ⟨ikm', rfl⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    have hs := (hmac_inj hq).1
    dsimp [zeroSalt, pqxdhKdf, hmac,
      Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hs
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hs)
  | ckStep _ _ =>
    rw [chainKeyAt_succ_eq_kdfCk_fst] at hq
    have hm := (hmac_inj hq).2
    dsimp [pqxdhIkm, kdfCk,
      Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
      Concat.concat, Concat.CanConcat.concat] at hm
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm)
  | rkRatchet _ _ _ =>
    have hs := (hmac_inj hq).1
    dsimp [zeroSalt, createChain, hmac,
      Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
      KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hs
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hs)
  | @chainRatchet _ _ n _ _ _ _ _ _ =>
    cases n with
    | zero =>
      have hs := (hmac_inj hq).1
      dsimp [zeroSalt, createChain, hmac,
        Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
        KdfExtract.kdfExtract, KdfExtract.CanKdfExtract.kdfExtract] at hs
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hs)
    | succ m =>
      rw [chainKeyAt_succ_eq_kdfCk_fst] at hq
      have hm := (hmac_inj hq).2
      dsimp [pqxdhIkm, kdfCk,
        Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
        Concat.concat, Concat.CanConcat.concat] at hm
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm)
  | seedCk _ _ =>
    have hm := (hmac_inj hq).2
    dsimp [pqxdhIkm, kdfCk,
      Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
      Concat.concat, Concat.CanConcat.concat] at hm
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm)
  | seedRatchet _ _ _ =>
    have hm := (hmac_inj hq).2
    dsimp [pqxdhIkm, kdfCk,
      Literal.literalToBytes, Literal.CanMkLiteral.literalToBytes,
      Concat.concat, Concat.CanConcat.concat] at hm
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hm)

/-- Every `IsHandshakeBlock (pqxdhKdf ikm) k` has outer `hmac` salt `hmac zeroSalt ikm` and is
disjoint from `kdfCk` outputs and `createChain` outputs. -/
theorem CompExposure.sessionStateExposed_of_isHandshakeBlock {tr : ExecTrace} (hinv : SpqrInv tr)
    {ikm : Bytes} {keys : HandshakeKeys} {k : Bytes}
    (hkeys : keys = pqxdhKdf ikm)
    (hblk : IsHandshakeBlock keys k)
    (hexp : CompExposure tr k) :
    SessionStateExposed tr keys k := by
  subst hkeys
  have hprk_eq : ∀ {s m : Bytes},
      k = hmac s m → s = hmac zeroSalt ikm := by
    intro s m hk
    rcases hblk with rfl | rfl | rfl <;> exact (hmac_inj hk).1.symm
  have hnot_kdfCk_fst : ∀ ck : Bytes, k ≠ (kdfCk ck).1 := by
    intro ck hk
    rcases hblk with rfl | rfl | rfl
    · exact hkdfBlock1_ne_kdfCk_fst _ _ _ hk
    · exact hkdfBlock2_ne_kdfCk_fst _ _ _ hk
    · exact hkdfBlock3_ne_kdfCk_fst _ _ _ hk
  have hnot_kdfCk_snd : ∀ ck : Bytes, k ≠ (kdfCk ck).2 := by
    intro ck hk
    rcases hblk with rfl | rfl | rfl
    · exact hkdfBlock1_ne_kdfCk_snd _ _ _ hk
    · exact hkdfBlock2_ne_kdfCk_snd _ _ _ hk
    · exact hkdfBlock3_ne_kdfCk_snd _ _ _ hk
  generalize hq : k = q at hexp
  cases hexp with
  | pqr hsse =>
    have ⟨_, j, _, hkeys', _⟩ := hsse
    obtain ⟨ikm', rfl⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys'
    have hikm : ikm = ikm' := (hmac_inj (hprk_eq hq)).2.symm
    subst hikm hq
    exact hsse
  | ck0 hsse =>
    have ⟨_, j, _, hkeys', _⟩ := hsse
    obtain ⟨ikm', rfl⟩ := handshakeKeysAt_eq_pqxdhKdf hinv hkeys'
    have hikm : ikm = ikm' := (hmac_inj (hprk_eq hq)).2.symm
    subst hikm hq
    exact hsse
  | ckStep _ _ =>
    rw [chainKeyAt_succ_eq_kdfCk_fst] at hq
    exact False.elim (hnot_kdfCk_fst _ hq)
  | rkRatchet rk pk sk =>
    rcases hblk with rfl | rfl | rfl
    · exact False.elim (pqxdhKdf_rk_ne_createChain_fst _ _ _ _ hq)
    · exact False.elim (hkdfBlock1_ne_hkdfBlock2 _ _ _ _ hq.symm)
    · exact False.elim (hkdfBlock1_ne_hkdfBlock3 _ _ _ _ hq.symm)
  | @chainRatchet _ _ n rkChain pk sk _ _ _ =>
    cases n with
    | zero =>
      rcases hblk with rfl | rfl | rfl
      · exact False.elim (hkdfBlock1_ne_hkdfBlock2 _ _ _ _ hq)
      · exact False.elim (pqxdhKdf_ck_ne_createChain_snd _ _ _ _ hq)
      · exact False.elim (hkdfBlock2_ne_hkdfBlock3 _ _ _ _ hq.symm)
    | succ m =>
      rw [chainKeyAt_succ_eq_kdfCk_fst] at hq
      exact False.elim (hnot_kdfCk_fst _ hq)
  | seedCk _ _ =>
    exact False.elim (hnot_kdfCk_snd _ hq)
  | seedRatchet _ _ _ =>
    exact False.elim (hnot_kdfCk_snd _ hq)

end ExposureDomainSeparation

end CompPubInv

open CompPubInv

theorem pub_of_knows {tr : ExecTrace} (hinv : SpqrInv tr) {x : Bytes}
    (hk : x.AttackerKnows tr) : Pub tr x :=
  Pub.of_attackerKnows hinv hk

theorem Pub.inv_ss {tr : ExecTrace} (hinv : SpqrInv tr) {pk e : Bytes}
    (h : Pub tr (PQKem.kemEncap pk e).2) :
    (Pub tr pk ∧ Pub tr e) ∨ (∃ sk, pk = PQKem.kemPk sk ∧ Pub tr sk) :=
  CompPubInv.Pub.inv_ss_of_spqrInv hinv h

theorem Pub.inv_rejKey {tr : ExecTrace} (hinv : SpqrInv tr) {sk ct : Bytes}
    (h : Pub tr (PQKem.kemRejKey sk ct)) : Pub tr sk ∧ Pub tr ct :=
  CompPubInv.Pub.inv_rejKey_of_spqrInv hinv h

/-- Per-block `pqxdhKdf` and `pqxdhIkm` inversion over `Pub tr` on a `SpqrInv tr` trace,
splitting into `Pub tr` of all five IKM inputs or `SessionStateExposed tr keys k`. -/
theorem pub_handshakeBlock_inv_of_spqrInv {tr : ExecTrace} (hinv : SpqrInv tr)
    {d1 d2 d3 : Bytes} {d4 : Option Bytes} {ss : Bytes}
    {keys : HandshakeKeys} {k : Bytes}
    (hkeys : keys = pqxdhKdf (pqxdhIkm d1 d2 d3 d4 ss))
    (hblk : IsHandshakeBlock keys k)
    (hpub : Pub tr k) :
    (Pub tr d1 ∧ Pub tr d2 ∧ Pub tr d3 ∧ (∀ d, d4 = some d → Pub tr d) ∧ Pub tr ss) ∨
      SessionStateExposed tr keys k :=
  keyKnown_block_inv_generic
    (C := Pub tr)
    (E := CompExposure tr)
    (fun h => Pub.inv_kdf h)
    (fun h => Pub.inv_cat hinv h)
    rfl
    hkeys
    (CompExposure.not_hmac_zeroSalt_pqxdhIkm hinv)
    (CompExposure.sessionStateExposed_of_isHandshakeBlock hinv hkeys hblk)
    hblk
    hpub

theorem pub_handshakeBlock_inv {tr : ExecTrace} (hinv : SpqrInv tr)
    {d1 d2 d3 : Bytes} {d4 : Option Bytes} {ss : Bytes}
    {keys : HandshakeKeys} {k : Bytes}
    (hkeys : keys = pqxdhKdf (pqxdhIkm d1 d2 d3 d4 ss))
    (hblk : IsHandshakeBlock keys k)
    (hpub : Pub tr k) :
    (Pub tr d1 ∧ Pub tr d2 ∧ Pub tr d3 ∧ (∀ d, d4 = some d → Pub tr d) ∧ Pub tr ss) ∨
      SessionStateExposed tr keys k :=
  pub_handshakeBlock_inv_of_spqrInv hinv hkeys hblk hpub

/-! ## Identity-Key Secrecy and Bundle Signature Origin -/

theorem IKAt.owner_unique {tr : ExecTrace} {p p' : Participant} {r : Bytes} (h : IKAt tr p r)
    (h' : IKAt tr p' r) : p = p' :=
  ikAt_owner_unique h h'

namespace BundleVerifyHelpers

theorem proj_inj {E : Type} [ExecTraceTypes.Has E] (e : E) :
    (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E) = some e := by
  rw [TraceEntryHas.inj_proj_eq]

theorem evAt_unique {tr : ExecTrace} {ev ev' : PQXDHEvent} {i : Nat}
    (h : tr.EventLoggedAt ev i) (h' : tr.EventLoggedAt ev' i) : ev = ev' := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h h'
  rw [h] at h'
  cases h'
  rfl

theorem randAt_not_evAt {tr : ExecTrace} {t n : Nat} {ev : PQXDHEvent} (h : RandAt tr t n)
    (h' : tr.EventLoggedAt ev t) : False := by
  unfold RandAt at h
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h'
  rw [Trace.at?_eq_some] at h h'
  obtain ⟨_, h⟩ := h
  obtain ⟨_, h'⟩ := h'
  rw [h] at h'
  have hc := congrArg (TraceEntryHas.proj (EntryT := EvEntry)) h'
  rw [proj_inj] at hc
  cases hc

theorem netAt_not_evAt {tr : ExecTrace} {t : Nat} {msg : Bytes} {ev : PQXDHEvent}
    (h : NetAt tr msg t) (h' : tr.EventLoggedAt ev t) : False := by
  unfold NetAt at h
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h'
  rw [Trace.at?_eq_some] at h h'
  obtain ⟨_, h⟩ := h
  obtain ⟨_, h'⟩ := h'
  rw [h] at h'
  have hc := congrArg (TraceEntryHas.proj (EntryT := EvEntry)) h'
  rw [proj_inj] at hc
  cases hc

theorem pqAt_ne_rnd32 {tr : ExecTrace} {b : Participant} {t : Nat}
    (hq : PQAt tr b (rnd t 32)) : False := by
  obtain ⟨t', hr, _⟩ := hq
  have := (rnd_inj hr).2
  omega

theorem eventLoggedAt_lt_length {tr : ExecTrace} {ev : PQXDHEvent} {j : Nat}
    (h : tr.EventLoggedAt ev j) : j < tr.length := by
  have hlt := Trace.at?_eq_some_implies_length_le
    (EntryT := EvEntry) tr j
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
  rw [h] at hlt
  exact hlt

theorem loggedBefore_of_eventLogged {tr : ExecTrace} {ev : PQXDHEvent} {i : Nat}
    (hev : tr.EventLogged ev) (hi : tr.length ≤ i) : LoggedBefore ev i tr := by
  rcases hev with ⟨j, hj⟩
  have hlt : j < tr.length := eventLoggedAt_lt_length hj
  exact ⟨j, hj, Nat.lt_of_lt_of_le hlt hi⟩

end BundleVerifyHelpers

/-- An honest identity secret is in `Pub tr` only after its compromise or `BrokenDH`. -/
theorem pub_IK_ev {tr : ExecTrace} (hinv : SpqrInv tr) {p : Participant} {r : Bytes}
    (hik : IKAt tr p r) (h : Pub tr r) :
    tr.EventLogged (PQXDHEvent.CompromisedIK p (DiffieHellman.dhPk r)) ∨
    tr.EventLogged PQXDHEvent.BrokenDH := by
  have hik₀ := hik
  obtain ⟨t, rfl, _, hev⟩ := hik
  rcases Pub.inv_rand hinv h with
    ⟨p', hik', he⟩ | ⟨b, hspk, _⟩ | ⟨b, hpq, _⟩ | ⟨b, hopk, _⟩ |
    ⟨_, hbdh⟩ | ⟨⟨b, hpq⟩, _⟩ | ⟨hrat, _⟩ | hmsg
  · cases IKAt.owner_unique hik₀ hik'
    exact .inl he
  · obtain ⟨t', ht', _, hr64, _⟩ := hspk
    cases (rnd_inj ht').1
    exact (BundleVerifyHelpers.randAt_not_evAt hr64 hev).elim
  · exact (BundleVerifyHelpers.pqAt_ne_rnd32 hpq).elim
  · obtain ⟨t', ht', _, hev'⟩ := hopk
    cases (rnd_inj ht').1
    cases BundleVerifyHelpers.evAt_unique hev hev'
  · exact .inr hbdh
  · exact (BundleVerifyHelpers.pqAt_ne_rnd32 hpq).elim
  · rcases hrat with ⟨t', ht', _, _, _, a, b, ikA, ikB, spk, pqpk, opk, ek, ct, keys, hn3, _, _⟩ |
      ⟨t', msg, ht', _, hn⟩
    · have ht : t = t' + 2 := (rnd_inj ht').1
      have hidx : t' + 3 = t + 1 := by omega
      rw [hidx] at hn3
      exact (BundleVerifyHelpers.netAt_not_evAt hn3 hev).elim
    · cases (rnd_inj ht').1
      exact (BundleVerifyHelpers.netAt_not_evAt hn hev).elim
  · rcases hmsg with ⟨t', n, msg, ht', _, hr1, _, _⟩ | ⟨t', n, msg, ht', _, _, hn2, _⟩
    · cases (rnd_inj ht').1
      exact (BundleVerifyHelpers.randAt_not_evAt hr1 hev).elim
    · have ht : t = t' + 1 := (rnd_inj ht').1
      have hidx : t' + 2 = t + 1 := by omega
      rw [hidx] at hn2
      exact (BundleVerifyHelpers.netAt_not_evAt hn2 hev).elim

theorem pub_IK {tr : ExecTrace} (hinv : SpqrInv tr) {p : Participant} {r : Bytes}
    (hik : IKAt tr p r) (hpub : Pub tr r) :
    (∃ j, tr.EventLoggedAt (PQXDHEvent.CompromisedIK p (DiffieHellman.dhPk r)) j) ∨
    (∃ j, tr.EventLoggedAt PQXDHEvent.BrokenDH j) :=
  pub_IK_ev hinv hik hpub

/-- Verified prekey signatures under Bob's registered verification key yield `BundleOK`. -/
theorem bundleOK_of_verify {tr : ExecTrace} (hinv : SpqrInv tr) {b : Participant}
    {ikB vkB : Bytes} {hon : Bool} {r : Nat}
    (hreg : tr.EventLoggedAt (PQXDHEvent.IdentityRegistered b ikB vkB hon) r)
    {spk spkSig pqpk pqpkSig : Bytes}
    (hspkSig : spkSig.AttackerKnows tr) (hpqSig : pqpkSig.AttackerKnows tr)
    (hv1 : Signature.verify vkB (encodeEC spk) spkSig = true)
    (hv2 : Signature.verify vkB (encodeKEM pqpk) pqpkSig = true)
    {i : Nat} (hi : tr.length ≤ i) :
    BundleOK tr b ikB spk pqpk i := by
  cases hon with
  | false =>
    have hcomp : tr.EventLoggedAt (PQXDHEvent.CompromisedIK b ikB) (r + 1) :=
      hinv.irCorrupt b ikB vkB r hreg
    have hlt : r + 1 < tr.length := BundleVerifyHelpers.eventLoggedAt_lt_length hcomp
    exact .inr (.inl ⟨r + 1, hcomp, Nat.lt_of_lt_of_le hlt hi⟩)
  | true =>
    obtain ⟨sB, hsB, rfl, rfl⟩ := hinv.irHonest b ikB vkB r hreg
    obtain ⟨sk1, n1, hvk1, rfl⟩ := verify_eq_true_iff.mp hv1
    obtain ⟨sk2, n2, hvk2, rfl⟩ := verify_eq_true_iff.mp hv2
    cases vk_inj hvk1.symm
    cases vk_inj hvk2.symm
    have hpub1 : Pub tr (Signature.sign sB n1 (encodeEC spk)) :=
      Pub.of_attackerKnows hinv hspkSig
    have hpub2 : Pub tr (Signature.sign sB n2 (encodeKEM pqpk)) :=
      Pub.of_attackerKnows hinv hpqSig
    rcases Pub.inv_sign hinv hpub1 with hpub_sB | ⟨b1, hb1, ⟨sS, hsS, heq1⟩ | ⟨q1, _, heq1⟩⟩
    · rcases pub_IK_ev hinv hsB hpub_sB with hcomp | hdh
      · exact .inr (.inl (BundleVerifyHelpers.loggedBefore_of_eventLogged hcomp hi))
      · exact .inr (.inr (BundleVerifyHelpers.loggedBefore_of_eventLogged hdh hi))
    · cases IKAt.owner_unique hsB hb1
      have hspk_eq : spk = DiffieHellman.dhPk sS := encodeEC_inj heq1
      rcases Pub.inv_sign hinv hpub2 with hpub_sB | ⟨b2, hb2, ⟨s2, _, heq2⟩ | ⟨sQ, hsQ, heq2⟩⟩
      · rcases pub_IK_ev hinv hsB hpub_sB with hcomp | hdh
        · exact .inr (.inl (BundleVerifyHelpers.loggedBefore_of_eventLogged hcomp hi))
        · exact .inr (.inr (BundleVerifyHelpers.loggedBefore_of_eventLogged hdh hi))
      · exact (encodeEC_ne_encodeKEM (DiffieHellman.dhPk s2) pqpk heq2.symm).elim
      · cases IKAt.owner_unique hsB hb2
        have hpq_eq : pqpk = PQKem.kemPk sQ := encodeKEM_inj heq2
        exact .inl ⟨sB, sS, sQ, hsB, rfl, hsS, hspk_eq, hsQ, hpq_eq⟩
    · exact (encodeEC_ne_encodeKEM spk (PQKem.kemPk q1) heq1).elim

end Symbolic.Swarm.COMPOSED.CompInv
