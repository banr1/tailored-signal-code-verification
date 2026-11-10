/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

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
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
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
public import Symbolic.Specifications.Model.Instance
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.TermAlgebra

/-!
# Trace-Independent Attacker-Knowledge Closure

Defines `Pub L`, the set of terms built from public constants and random draws with timestamps in
`L`, and proves closure under all 13 attacker theories of `DY.Libsignal.Composed.attackerKnowledge`
(`Pub.attackerKnowledge_implies`, `Pub.of_attackerKnows`). Inversion lemmas (`Pub.inv_kdf`,
`Pub.inv_cat`, `Pub.inv_dh`, `Pub.inv_rand`) then show that keys derived from `DH2 = DH(EK_A, IK_B)`
lie outside `Pub L` whenever neither `EK_A` nor `IK_B` is in `L`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.PubClosure

open Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.TermAlgebra (concat_inj dhPk_inj
  kdfExtract_inj kemDecap_eq_some_iff kemEncap_snd_inj x25519Key_dhPk)

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed

abbrev rndTerm (t n : Nat) : Bytes :=
  ({ timestamp := t, size := n } : Random.Random Bytes).pack

theorem rndTerm_inj {t t' n n' : Nat} (h : rndTerm t n = rndTerm t' n') : t = t' ∧ n = n' := by
  have hv := congrArg (fun b : Bytes => b.view? Random.Random) h
  simp only [rndTerm, BytesView.view_pack, Option.some.injEq, Random.Random.mk.injEq] at hv
  exact hv

/-- Terms derivable from the random values with timestamps in `L` (and from public constants). -/
inductive Pub (L : Nat → Prop) : Bytes → Prop where
  | rand {t n : Nat} (h : L t) : Pub L (rndTerm t n)
  | literal (bs : ByteArray) : Pub L (Literal.literalToBytes bs)
  | cat {l r : Bytes} (hl : Pub L l) (hr : Pub L r) : Pub L (Concat.concat l r)
  | kdf {s m : Bytes} (hs : Pub L s) (hm : Pub L m) : Pub L (KdfExtract.kdfExtract s m)
  | trunc (m : Bytes) : Pub L (Trunc.trunc8 m)
  | trWire {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes} {ev : TrWire.EncodingVariation}
      (hrk : Pub L rk) (hct : Pub L ct) (hpq : Pub L pq) :
      Pub L (TrWire.trWireMsg v rk c pc ct pq ev)
  | enc {k iv m : Bytes} (hm : Pub L m) : Pub L (SymEnc.symEnc k iv m)
  | var {key : Bytes} (v : Fin 4) {t : Fin 8} (hkey : Pub L key) :
      Pub L ((({ key := key, variation := v, torsion := t } : X25519.Variant.SubF Bytes)).pack)
  | dhPub (sk : Bytes) : Pub L (DiffieHellman.dhPk sk)
  | dhSk (sk pk : Bytes) (h : Pub L sk) :
      Pub L ((({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes)).pack)
  | dhPeer (sk s : Bytes) (h : Pub L s) :
      Pub L ((({ sk := sk, pk := DiffieHellman.dhPk s } : DiffieHellman.Dh.SubF Bytes)).pack)
  | kemPub (sk : Bytes) : Pub L (PQKem.kemPk sk)
  | encap (pk e : Bytes) : Pub L (PQKem.kemEncap pk e).1
  | ss {pk e : Bytes} (hpk : Pub L pk) (he : Pub L e) : Pub L (PQKem.kemEncap pk e).2
  | ssKey {sk : Bytes} (e : Bytes) (h : Pub L sk) : Pub L (PQKem.kemEncap (PQKem.kemPk sk) e).2
  | rejKey {sk ct : Bytes} (hsk : Pub L sk) (hct : Pub L ct) :
      Pub L ((({ sk := sk, cipher := ct } : PQKem.RejKey.SubF Bytes)).pack)
  | vkPub (sk : Bytes) : Pub L (Signature.vk sk)
  | sig (sk nonce msg : Bytes) : Pub L (Signature.sign sk nonce msg)
  | spqrInit {authKey params : Bytes} (hk : Pub L authKey) (hp : Pub L params) :
      Pub L (Spqr.spqrInit authKey params)
  | spqrChainKey (authKey params idx : Bytes) :
      Pub L (Spqr.spqrChainKey authKey params idx)
  | spqrSendState {st coins : Bytes} (hst : Pub L st) (hc : Pub L coins) :
      Pub L ((({ st := st, coins := coins } : Spqr.SendState.SubF Bytes)).pack)
  | spqrSendKey (st coins : Bytes) :
      Pub L ((({ st := st, coins := coins } : Spqr.SendKey.SubF Bytes)).pack)
  | spqrSendMsg (st coins : Bytes) :
      Pub L ((({ st := st, coins := coins } : Spqr.SendMsg.SubF Bytes)).pack)
  | spqrRecvState {st msg : Bytes} (hst : Pub L st) (hm : Pub L msg) :
      Pub L ((({ st := st, msg := msg } : Spqr.RecvState.SubF Bytes)).pack)
  | spqrRecvKey (st msg : Bytes) :
      Pub L ((({ st := st, msg := msg } : Spqr.RecvKey.SubF Bytes)).pack)

/-! ## Inversions -/

section PubInversions
unseal Bytes

variable {L : Nat → Prop}

theorem Pub.inv_rand {t n : Nat} (h : Pub L (rndTerm t n)) : L t := by
  generalize hq : rndTerm t n = q at h
  cases h with
  | rand hr =>
    obtain ⟨rfl, rfl⟩ := rndTerm_inj hq
    exact hr
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_cat {l r : Bytes} (h : Pub L (Concat.concat l r)) : Pub L l ∧ Pub L r := by
  generalize hq : Concat.concat l r = q at h
  cases h with
  | cat hl hr =>
    obtain ⟨rfl, rfl⟩ := concat_inj hq
    exact ⟨hl, hr⟩
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_kdf {s m : Bytes} (h : Pub L (KdfExtract.kdfExtract s m)) : Pub L s ∧ Pub L m := by
  generalize hq : KdfExtract.kdfExtract s m = q at h
  cases h with
  | kdf hs hm =>
    obtain ⟨rfl, rfl⟩ := kdfExtract_inj hq
    exact ⟨hs, hm⟩
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_dhPack {sk pk : Bytes}
    (h : Pub L ((({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes)).pack)) :
    Pub L sk ∨ ∃ s, pk = DiffieHellman.dhPk s ∧ Pub L s := by
  generalize hq : (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes)).pack = q at h
  cases h with
  | dhSk sk' pk' hsk =>
    have hv := congrArg (fun b : Bytes => b.view? DiffieHellman.Dh.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact .inl hsk
  | dhPeer sk' s hs =>
    have hv := congrArg (fun b : Bytes => b.view? DiffieHellman.Dh.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact .inr ⟨s, rfl, hs⟩
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_ss {pk e : Bytes} (h : Pub L (PQKem.kemEncap pk e).2) :
    (Pub L pk ∧ Pub L e) ∨ (∃ sk, pk = PQKem.kemPk sk ∧ Pub L sk) := by
  generalize hq : (PQKem.kemEncap pk e).2 = q at h
  cases h with
  | ss hpk he =>
    obtain ⟨rfl, rfl⟩ := kemEncap_snd_inj hq
    exact .inl ⟨hpk, he⟩
  | ssKey e' hsk =>
    obtain ⟨rfl, rfl⟩ := kemEncap_snd_inj hq
    exact .inr ⟨_, rfl, hsk⟩
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_trWire {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes}
    {ev : TrWire.EncodingVariation} (h : Pub L (TrWire.trWireMsg v rk c pc ct pq ev)) :
    Pub L rk ∧ Pub L ct ∧ Pub L pq := by
  generalize hq : TrWire.trWireMsg v rk c pc ct pq ev = q at h
  cases h with
  | trWire hrk hct hpq =>
    have hv := congrArg (fun b : Bytes => b.view? TrWire.TrWireMsg.SubF) hq
    simp only [TrWire.trWireMsg, TrWire.CanTrWireMsg.trWireMsg, BytesView.view_pack,
      Option.some.injEq, TrWire.TrWireMsg.SubF.mk.injEq] at hv
    obtain ⟨_, rfl, _, _, rfl, rfl, _⟩ := hv
    exact ⟨hrk, hct, hpq⟩
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_enc {k iv m : Bytes} (h : Pub L (SymEnc.symEnc k iv m)) : Pub L m := by
  generalize hq : SymEnc.symEnc k iv m = q at h
  cases h with
  | enc hm =>
    have hv := congrArg (fun b : Bytes => b.view? SymEnc.Enc.SubF) hq
    simp only [SymEnc.symEnc, SymEnc.CanSymEnc.symEnc, BytesView.view_pack,
      Option.some.injEq, SymEnc.Enc.SubF.mk.injEq] at hv
    obtain ⟨_, _, rfl⟩ := hv
    exact hm
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_variant {x : X25519.Variant.SubF Bytes} (h : Pub L x.pack) : Pub L x.key := by
  generalize hq : x.pack = q at h
  cases h with
  | var v hkey =>
    have hv := congrArg (fun b : Bytes => b.view? X25519.Variant.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x
    cases hv
    exact hkey
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_spqrInitPack {x : Spqr.InitState.SubF Bytes} (h : Pub L x.pack) :
    Pub L x.authKey ∧ Pub L x.params := by
  generalize hq : x.pack = q at h
  cases h with
  | spqrInit hk hp =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.InitState.SubF) hq
    simp only [Spqr.spqrInit, BytesView.view_pack, Option.some.injEq] at hv
    cases x
    cases hv
    exact ⟨hk, hp⟩
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_spqrSendStatePack {x : Spqr.SendState.SubF Bytes} (h : Pub L x.pack) :
    Pub L x.st ∧ Pub L x.coins := by
  generalize hq : x.pack = q at h
  cases h with
  | spqrSendState hst hc =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.SendState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x
    cases hv
    exact ⟨hst, hc⟩
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem Pub.inv_spqrRecvStatePack {x : Spqr.RecvState.SubF Bytes} (h : Pub L x.pack) :
    Pub L x.st ∧ Pub L x.msg := by
  generalize hq : x.pack = q at h
  cases h with
  | spqrRecvState hst hm =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.RecvState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x
    cases hv
    exact ⟨hst, hm⟩
  | _ =>
    try dsimp [rndTerm, Literal.literalToBytes, Concat.concat, KdfExtract.kdfExtract,
      Trunc.trunc8, TrWire.trWireMsg, SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

end PubInversions

/-! ## Derived constructors -/

section Derived

variable {L : Nat → Prop}

theorem Pub.dh {pk sk : Bytes} (hsk : Pub L sk) : Pub L (DiffieHellman.dh pk sk) := by
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 _
    split
    · exact .dhSk sk (DiffieHellman.dhPk sk2) hsk
    · exact .dhPeer sk2 sk hsk
  · exact .dhSk sk pk hsk

theorem Pub.inv_dh {pk sk : Bytes} (h : Pub L (DiffieHellman.dh pk sk)) :
    Pub L sk ∨ ∃ s, pk = DiffieHellman.dhPk s ∧ Pub L s := by
  revert h
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh]
  have hp := Bytes.pack_view? DiffieHellman.DhPk.SubF pk
  cases hv : pk.view? DiffieHellman.DhPk.SubF with
  | none =>
    intro h
    exact Pub.inv_dhPack h
  | some x =>
    rw [hv] at hp
    rcases x with ⟨sk2⟩
    dsimp only
    intro h
    split at h
    · rcases Pub.inv_dhPack h with h1 | ⟨s, hs, h2⟩
      · exact .inl h1
      · exact .inr ⟨s, by rw [← hp]; exact hs, h2⟩
    · rcases Pub.inv_dhPack h with h1 | ⟨s, hs, h2⟩
      · exact .inr ⟨sk2, hp.symm, h1⟩
      · have := dhPk_inj hs
        subst this
        exact .inl h2

theorem Pub.normalizeX25519Key {pk : Bytes} (h : Pub L pk) : Pub L (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key
  have hp := Bytes.pack_view? X25519.Variant.SubF pk
  cases hv : pk.view? X25519.Variant.SubF with
  | none => exact h
  | some x =>
    rw [hv] at hp
    rw [← hp] at h
    exact Pub.inv_variant h

theorem Pub.x25519TorsionVariant {key : Bytes} (v : Fin 4) (t : Fin 8) (h : Pub L key) :
    Pub L (X25519.x25519TorsionVariant key v t) := by
  dsimp [X25519.x25519TorsionVariant]
  split
  · exact Pub.normalizeX25519Key h
  · exact .var v (Pub.normalizeX25519Key h)

theorem Pub.spqrSendKey_of (st coins : Bytes) : Pub L (Spqr.spqrSend st coins).2.1 := by
  unfold Spqr.spqrSend
  dsimp only
  cases st.view? Spqr.InitState.SubF with
  | none => exact .spqrSendKey st coins
  | some x => exact .spqrChainKey x.authKey x.params (Spqr.encodeSpqrIndexTerm 1)

theorem Pub.spqrRecvState_of {st msg : Bytes} {idx : UInt32} {r : Bytes × Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) (hst : Pub L st) (hm : Pub L msg) :
    Pub L r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]
  exact .spqrRecvState hst hm

theorem Pub.spqrRecvKey_of {st msg : Bytes} {idx : UInt32} {r : Bytes × Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) : Pub L r.2 := by
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

end Derived

/-! ## Closure under the attacker -/

theorem Pub.attackerKnowledge_implies (L : Nat → Prop) :
    SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge (Pub L) := by
  change SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge (Pub L)
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
      exact (Pub.inv_cat (Concat.concat_split inp i b rhs hsplit.symm ▸ hinp)).1
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, lhs, i, hsplit, hinp⟩
      exact (Pub.inv_cat (Concat.concat_split inp i lhs b hsplit.symm ▸ hinp)).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩
      exact .dhPub sk
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
          exact Pub.inv_enc hct
        · cases hdec
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · rintro b ⟨m, rfl, _⟩
      exact .trunc m
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨key, v, t, rfl, hkey⟩
      exact Pub.x25519TorsionVariant v t hkey
    · rintro b ⟨x, hpack, rfl⟩
      exact Pub.inv_variant hpack
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨sk, rfl, _⟩
      exact .kemPub sk
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
      rcases hb with ⟨sk, rfl, _⟩
      exact .vkPub sk
    · intro b hb
      dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, nonce, msg, rfl, _, _, _⟩
      exact .sig sk nonce msg
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
      · exact (Pub.inv_spqrInitPack hpack).1
      · exact (Pub.inv_spqrInitPack hpack).2
      · exact (Pub.inv_spqrSendStatePack hpack).1
      · exact (Pub.inv_spqrSendStatePack hpack).2
      · exact (Pub.inv_spqrRecvStatePack hpack).1
      · exact (Pub.inv_spqrRecvStatePack hpack).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, rfl, hrk, hct, hpq⟩
      exact .trWire hrk hct hpq
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, hw, hmem⟩
      obtain ⟨hrk, hct, hpq⟩ := Pub.inv_trWire hw
      rcases hmem with rfl | rfl | rfl <;> assumption
    · omega
  · omega

/-- If every network message of `tr` belongs to `Pub L`, then every attacker-known term on `tr`
belongs to `Pub L`. -/
theorem Pub.of_attackerKnows {L : Nat → Prop} {tr : ExecTrace}
    (hnet : ∀ y, tr.BaseAttackerKnows y → Pub L y) {x : Bytes} (hk : x.AttackerKnows tr) :
    Pub L x := by
  refine Bytes.AttackerKnows.is_least_fixpoint (Pub L) x tr
    (Pub.attackerKnowledge_implies L) (fun y hy => ?_) hk
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1,
    SubAttackerKnowledge.fromPred] at hy
  exact hnet y hy

/-! ## Keys derived from `DH2 = DH(EK_A, IK_B)` are not public -/

section KeyChain

variable {L : Nat → Prop}

theorem Pub.not_rand {t n : Nat} (h : ¬ L t) : ¬ Pub L (rndTerm t n) :=
  fun hp => h (Pub.inv_rand hp)

theorem Pub.not_agree {ikB ek : Bytes} (hek : ¬ Pub L ek) (hikB : ¬ Pub L ikB) :
    ¬ Pub L (agree (DiffieHellman.dhPk ikB) ek) := by
  intro h
  unfold agree at h
  rw [x25519Key_dhPk] at h
  rcases Pub.inv_dh h with h1 | ⟨s, hs, h2⟩
  · exact hek h1
  · obtain rfl := dhPk_inj hs
    exact hikB h2

theorem Pub.not_pqxdhIkm {d1 d2 d3 : Bytes} {d4 : Option Bytes} {ss : Bytes}
    (h2 : ¬ Pub L d2) : ¬ Pub L (pqxdhIkm d1 d2 d3 d4 ss) := by
  intro h
  unfold pqxdhIkm at h
  exact h2 (Pub.inv_cat (Pub.inv_cat (Pub.inv_cat h).2).2).1

theorem Pub.not_pqxdhKdf_rk {ikm : Bytes} (h : ¬ Pub L ikm) : ¬ Pub L (pqxdhKdf ikm).rk := by
  intro hp
  change Pub L (KdfExtract.kdfExtract (KdfExtract.kdfExtract _ ikm) _) at hp
  exact h (Pub.inv_kdf (Pub.inv_kdf hp).1).2

theorem Pub.not_pqxdhKdf_ck {ikm : Bytes} (h : ¬ Pub L ikm) : ¬ Pub L (pqxdhKdf ikm).ck := by
  intro hp
  change Pub L (KdfExtract.kdfExtract (KdfExtract.kdfExtract _ ikm) _) at hp
  exact h (Pub.inv_kdf (Pub.inv_kdf hp).1).2

theorem Pub.not_createChain_fst {rk : Bytes} (theirPk ourSk : Bytes) (h : ¬ Pub L rk) :
    ¬ Pub L (DY.Libsignal.TripleRatchet.createChain rk theirPk ourSk).1 := by
  intro hp
  change Pub L (KdfExtract.kdfExtract (KdfExtract.kdfExtract rk _) _) at hp
  exact h (Pub.inv_kdf (Pub.inv_kdf hp).1).1

theorem Pub.not_createChain_snd {rk : Bytes} (theirPk ourSk : Bytes) (h : ¬ Pub L rk) :
    ¬ Pub L (DY.Libsignal.TripleRatchet.createChain rk theirPk ourSk).2 := by
  intro hp
  change Pub L (KdfExtract.kdfExtract (KdfExtract.kdfExtract rk _) _) at hp
  exact h (Pub.inv_kdf (Pub.inv_kdf hp).1).1

theorem Pub.not_kdfCk_fst {ck : Bytes} (h : ¬ Pub L ck) : ¬ Pub L (kdfCk ck).1 := by
  intro hp
  change Pub L (KdfExtract.kdfExtract ck _) at hp
  exact h (Pub.inv_kdf hp).1

theorem Pub.not_kdfCk_snd {ck : Bytes} (h : ¬ Pub L ck) : ¬ Pub L (kdfCk ck).2 := by
  intro hp
  change Pub L (KdfExtract.kdfExtract ck _) at hp
  exact h (Pub.inv_kdf hp).1

theorem Pub.not_chainKeyAt {ck : Bytes} (h : ¬ Pub L ck) (n : Nat) :
    ¬ Pub L (chainKeyAt ck n) := by
  induction n generalizing ck with
  | zero => exact h
  | succ n ih => exact ih (Pub.not_kdfCk_fst h)

theorem Pub.not_trMsgKeys_cipherKey {seed : Bytes} (pqSalt : Bytes) (h : ¬ Pub L seed) :
    ¬ Pub L (trMsgKeys pqSalt seed).cipherKey := by
  intro hp
  change Pub L (KdfExtract.kdfExtract (KdfExtract.kdfExtract pqSalt seed) _) at hp
  exact h (Pub.inv_kdf (Pub.inv_kdf hp).1).2

end KeyChain

/-! ## Base knowledge of appended entries -/

@[simp] theorem baseAttackerKnows_append_net (tr : ExecTrace) (msg b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (Network.ExecEntryT.mk msg)) b ↔
      b = msg ∨ Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (Network.ExecEntryT.mk msg)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = (b = msg) :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.Network.baseAttackerKnowledge_attackerKnows tr
        (Network.ExecEntryT.mk msg) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]

@[simp] theorem baseAttackerKnows_append_rnd (tr : ExecTrace) (n : Nat) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (Random.ExecEntryT.mk n)) b ↔
      Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (Random.ExecEntryT.mk n)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.Random.baseAttackerKnowledge_attackerKnows tr
        (Random.ExecEntryT.mk n) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

@[simp] theorem baseAttackerKnows_append_trEv (tr : ExecTrace) (ev : TREvent) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (ProtocolEvent.ExecEntryT.mk ev)) b ↔
      Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (ProtocolEvent.ExecEntryT.mk ev)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows TREvent tr
        (ProtocolEvent.ExecEntryT.mk ev) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

@[simp] theorem baseAttackerKnows_append_ev (tr : ExecTrace) (ev : PQXDHEvent) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (ProtocolEvent.ExecEntryT.mk ev)) b ↔
      Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (ProtocolEvent.ExecEntryT.mk ev)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows PQXDHEvent tr
        (ProtocolEvent.ExecEntryT.mk ev) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

@[simp] theorem baseAttackerKnows_append_cEv (tr : ExecTrace) (ev : ComposedEvent) (b : Bytes) :
    Trace.BaseAttackerKnows (tr.append (ProtocolEvent.ExecEntryT.mk ev)) b ↔
      Trace.BaseAttackerKnows tr b := by
  let e : ExecTrace.Entry := TraceEntryHas.inj (ProtocolEvent.ExecEntryT.mk ev)
  have h0 : BaseAttackerKnowledge.attackerKnows.attackerKnows tr e b = False :=
    (Symbolic.DYBridge.DY.SubBaseAttackerKnowledge.combine_attackerKnows
      DY.Libsignal.Composed.baseAttackerKnowledge.internal tr e b).trans
      (Symbolic.DYBridge.DY.ProtocolEvent.baseAttackerKnowledge_attackerKnows ComposedEvent tr
        (ProtocolEvent.ExecEntryT.mk ev) b)
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2, h0]
  exact iff_of_eq (false_or _)

end Symbolic.Proofs.Tests.Model.ExplanationTightness.F3.PubClosure
