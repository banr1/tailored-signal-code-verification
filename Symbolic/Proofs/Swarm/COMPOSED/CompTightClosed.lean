/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompClosed
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
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
public import Symbolic.Proofs.Swarm.COMPOSED.CompPresTRExp
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.Misc.Fixpoint
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.Sign

/-!
# Composed Tight Attacker-Knowledge Closure

Defines the structured key-exposure predicate `CompStructuredExposure` and the inductive term
closure `CompTightClosed` refining `CompTrClosed` with invertible `dhPk` and `kemPk` witnesses,
and proves `CompTightClosed.of_attackerKnows` over `DY.Libsignal.Composed`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain createChain kdfCk chainKeyAt)
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhKdf HandshakeKeysAt)
open DY.Libsignal.TripleRatchet (TREvent TRSignalMsg parseTrSignalMsg)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompKeyInversion

/-- Syntactic shape of keys exposed by Triple Ratchet `exposeKey` and `exposeSkipped` transitions. -/
def IsScheduleKey (k : Bytes) : Prop :=
  (∃ r p sk, k = (createChain r p sk).1) ∨
  (∃ r p sk, k = (createChain r p sk).2) ∨
  (∃ ikm, k = (pqxdhKdf ikm).ck) ∨
  (∃ c, k = (kdfCk c).1) ∨
  (∃ c, k = (kdfCk c).2)

theorem IsScheduleKey.exists_kdfExtract {k : Bytes} (h : IsScheduleKey k) :
    ∃ s m, k = kdfExtract s m := by
  rcases h with ⟨r, p, sk, rfl⟩ | ⟨r, p, sk, rfl⟩ | ⟨ikm, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩ <;>
    exact ⟨_, _, rfl⟩

/-- Atomic values exposed to the attacker at trace `tr`: attacker-known or message-encryption
random draws, initial SPQR keys `(pqxdhKdf ikm).pqr`, and logged Triple Ratchet key exposures. -/
inductive CompStructuredExposure (tr : ExecTrace) : Bytes → Prop
  | rand {ts sz : Nat} :
      (mkRand ts sz).AttackerKnows tr ∨
        Symbolic.Swarm.COMPOSED.CompInv.MsgEncRandAt tr (mkRand ts sz) →
      CompStructuredExposure tr (mkRand ts sz)
  | pqr {ikm : Bytes} :
      CompStructuredExposure tr (pqxdhKdf ikm).pqr
  | exposedRK {s : SessionInfo} {rk : Bytes} {rIdx : Nat} :
      (∃ r p sk, rk = (createChain r p sk).1) →
      tr.EventLogged (TREvent.ExposedRK s rk rIdx) →
      CompStructuredExposure tr rk
  | exposedCKs {s : SessionInfo} {cks : Bytes} {n : UInt32} {rIdx : Nat} :
      IsScheduleKey cks →
      tr.EventLogged (TREvent.ExposedCKs s cks n rIdx) →
      CompStructuredExposure tr cks
  | exposedCKr {s : SessionInfo} {ckr : Bytes} {n : UInt32} {rIdx : Nat} :
      IsScheduleKey ckr →
      tr.EventLogged (TREvent.ExposedCKr s ckr n rIdx) →
      CompStructuredExposure tr ckr
  | exposedMK {s : SessionInfo} {seed : Bytes} {n : UInt32} {rIdx : Nat} :
      (∃ c, seed = (kdfCk c).2) →
      tr.EventLogged (TREvent.ExposedMK s seed n rIdx) →
      CompStructuredExposure tr seed

theorem isAtomic_compStructuredExposure (tr : ExecTrace) :
    IsAtomicExposure (CompStructuredExposure tr) := by
  intro b hb
  rcases hb with ⟨_⟩ | _ | ⟨⟨r, p, sk, rfl⟩, _⟩ | ⟨hsk, _⟩ | ⟨hsk, _⟩ | ⟨⟨c, rfl⟩, _⟩
  · exact isAtomic_mkRand _ _
  · exact isAtomic_kdfExtract _ _
  · exact isAtomic_kdfExtract _ _
  · obtain ⟨s, m, rfl⟩ := hsk.exists_kdfExtract; exact isAtomic_kdfExtract s m
  · obtain ⟨s, m, rfl⟩ := hsk.exists_kdfExtract; exact isAtomic_kdfExtract s m
  · exact isAtomic_kdfExtract _ _

theorem baseAttackerKnows_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes}
    (hb : tr.BaseAttackerKnows b) : tr'.BaseAttackerKnows b := by
  induction hle with
  | equal => exact hb
  | extend _ _ _ ih =>
    rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2]
    exact .inr ih

theorem attackerKnows_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes}
    (hk : b.AttackerKnows tr) : b.AttackerKnows tr' := by
  refine Bytes.AttackerKnows.is_least_fixpoint (fun x => x.AttackerKnows tr') b tr
    (fun x hx => Bytes.AttackerKnows.prove AttackerKnowledge.attackerKnowledge x tr' hx)
    (fun x hx => ?_) hk
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
  exact Bytes.AttackerKnows.prove_from_base x tr' (baseAttackerKnows_mono hle hx)

theorem CompStructuredExposure.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes}
    (h : CompStructuredExposure tr b) : CompStructuredExposure tr' b := by
  cases h with
  | rand hr =>
    refine .rand ?_
    rcases hr with hk | hmsg
    · exact .inl (attackerKnows_mono hle hk)
    · exact .inr (Symbolic.Swarm.COMPOSED.CompInv.MsgEncRandAt.mono hle hmsg)
  | pqr => exact .pqr
  | exposedRK hshape hev => exact .exposedRK hshape (CompTrace.eventLogged_mono hle hev)
  | exposedCKs hsk hev => exact .exposedCKs hsk (CompTrace.eventLogged_mono hle hev)
  | exposedCKr hsk hev => exact .exposedCKr hsk (CompTrace.eventLogged_mono hle hev)
  | exposedMK hseed hev => exact .exposedMK hseed (CompTrace.eventLogged_mono hle hev)

theorem isScheduleKey_chainKeyAt_createChain_snd (rk pk sk : Bytes) (n : Nat) :
    IsScheduleKey (chainKeyAt (createChain rk pk sk).2 n) := by
  cases n with
  | zero => exact .inr (.inl ⟨rk, pk, sk, rfl⟩)
  | succ m =>
    exact .inr (.inr (.inr (.inl ⟨chainKeyAt (createChain rk pk sk).2 m,
      chainKeyAt_succ_eq_kdfCk_fst (createChain rk pk sk).2 m⟩)))

theorem isScheduleKey_of_recvChainInv {tr : ExecTrace}
    (hinv : Symbolic.Swarm.COMPOSED.CompInv.SpqrInv tr)
    {j : Nat} {keys : HandshakeKeys}
    (hkeys : HandshakeKeysAt tr j keys)
    {c : RecvChain} (hc : Symbolic.Swarm.COMPOSED.CompPresTRExp.RecvChainInv keys c) :
    IsScheduleKey c.chainKey := by
  rcases hc with ⟨_, _, hck⟩ | ⟨n, _, _, hck⟩ | ⟨rkChain, pk, sk, n, _, hck⟩
  · obtain ⟨ikm, hikm⟩ :=
      Symbolic.Swarm.COMPOSED.CompInv.CompPubInv.handshakeKeysAt_eq_pqxdhKdf hinv hkeys
    exact .inr (.inr (.inl ⟨ikm, hck.trans (congrArg HandshakeKeys.ck hikm)⟩))
  · exact .inr (.inr (.inr (.inl ⟨chainKeyAt keys.ck n,
      hck.trans (chainKeyAt_succ_eq_kdfCk_fst keys.ck n)⟩)))
  · rw [hck]
    exact isScheduleKey_chainKeyAt_createChain_snd rkChain pk sk n

/-! ## Tight Closure and Attacker-Knowledge Induction -/

/-- Refinement of `CompTrClosed (CompStructuredExposure tr)` recording that the secret key inside
any `dhPk` or `kemPk` term is either a `mkRand` draw or itself in `CompTightClosed tr`. -/
inductive CompTightClosed (tr : ExecTrace) : Bytes → Prop where
  | exposed {b : Bytes} (h : CompStructuredExposure tr b) : CompTightClosed tr b
  | literal (bs : ByteArray) : CompTightClosed tr (literalToBytes bs)
  | dhPkRand {sk : Bytes} (h : ∃ ts sz, sk = mkRand ts sz) :
      CompTightClosed tr (DiffieHellman.dhPk sk)
  | dhPkClosed {sk : Bytes} (h : CompTightClosed tr sk) :
      CompTightClosed tr (DiffieHellman.dhPk sk)
  | dhSk (sk pk : Bytes) (h : CompTightClosed tr sk) :
      CompTightClosed tr (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack)
  | dhPeer (sk s : Bytes) (h : CompTightClosed tr s) :
      CompTightClosed tr (({ sk := sk, pk := DiffieHellman.dhPk s } : DiffieHellman.Dh.SubF Bytes).pack)
  | kemPkRand {sk : Bytes} (h : ∃ ts sz, sk = mkRand ts sz) :
      CompTightClosed tr (PQKem.kemPk sk)
  | kemPkClosed {sk : Bytes} (h : CompTightClosed tr sk) :
      CompTightClosed tr (PQKem.kemPk sk)
  | kemEncap (pk e : Bytes) : CompTightClosed tr (PQKem.kemEncap pk e).1
  | kemSs (pk e : Bytes) (hpk : CompTightClosed tr pk) (he : CompTightClosed tr e) :
      CompTightClosed tr (PQKem.kemEncap pk e).2
  | kemSsKey (sk e : Bytes) (hsk : CompTightClosed tr sk) :
      CompTightClosed tr (PQKem.kemEncap (PQKem.kemPk sk) e).2
  | kemRejKey {sk ct : Bytes} (hsk : CompTightClosed tr sk) (hct : CompTightClosed tr ct) :
      CompTightClosed tr (({ sk := sk, cipher := ct } : PQKem.RejKey.SubF Bytes).pack)
  | vk (sk : Bytes) : CompTightClosed tr (Signature.vk sk)
  | sign (sk nonce msg : Bytes) : CompTightClosed tr (Signature.sign sk nonce msg)
  | trunc8 (m : Bytes) : CompTightClosed tr (Trunc.trunc8 m)
  | kdf {salt ikm : Bytes} (hsalt : CompTightClosed tr salt) (hikm : CompTightClosed tr ikm) :
      CompTightClosed tr (kdfExtract salt ikm)
  | concat {lhs rhs : Bytes} (hlhs : CompTightClosed tr lhs) (hrhs : CompTightClosed tr rhs) :
      CompTightClosed tr (Concat.concat lhs rhs)
  | symEnc {k iv msg : Bytes} (hmsg : CompTightClosed tr msg) :
      CompTightClosed tr (SymEnc.symEnc k iv msg)
  | variant {key : Bytes} (v : Fin 4) {t : Fin 8} (hkey : CompTightClosed tr key) :
      CompTightClosed tr (({ key := key, variation := v, torsion := t } : X25519.Variant.SubF Bytes).pack)
  | trWireMsg {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes}
      {ev : TrWire.EncodingVariation}
      (hrk : CompTightClosed tr rk) (hct : CompTightClosed tr ct) (hpq : CompTightClosed tr pq) :
      CompTightClosed tr (TrWire.trWireMsg v rk c pc ct pq ev)
  | spqrInit {authKey params : Bytes}
      (hauth : CompTightClosed tr authKey) (hparams : CompTightClosed tr params) :
      CompTightClosed tr (Spqr.spqrInit authKey params)
  | spqrChainKey (authKey params idx : Bytes) :
      CompTightClosed tr (Spqr.spqrChainKey authKey params idx)
  | spqrSendState {st coins : Bytes}
      (hst : CompTightClosed tr st) (hcoins : CompTightClosed tr coins) :
      CompTightClosed tr (({ st := st, coins := coins } : Spqr.SendState.SubF Bytes).pack)
  | spqrSendKey (st coins : Bytes) :
      CompTightClosed tr (({ st := st, coins := coins } : Spqr.SendKey.SubF Bytes).pack)
  | spqrSendMsg (st coins : Bytes) :
      CompTightClosed tr (({ st := st, coins := coins } : Spqr.SendMsg.SubF Bytes).pack)
  | spqrRecvState {st msg : Bytes}
      (hst : CompTightClosed tr st) (hmsg : CompTightClosed tr msg) :
      CompTightClosed tr (({ st := st, msg := msg } : Spqr.RecvState.SubF Bytes).pack)
  | spqrRecvKey (st msg : Bytes) :
      CompTightClosed tr (({ st := st, msg := msg } : Spqr.RecvKey.SubF Bytes).pack)

theorem CompTightClosed.dhPk {tr : ExecTrace} {sk : Bytes}
    (h : (∃ ts sz, sk = mkRand ts sz) ∨ CompTightClosed tr sk) :
    CompTightClosed tr (DiffieHellman.dhPk sk) :=
  h.elim .dhPkRand .dhPkClosed

theorem CompTightClosed.kemPk {tr : ExecTrace} {sk : Bytes}
    (h : (∃ ts sz, sk = mkRand ts sz) ∨ CompTightClosed tr sk) :
    CompTightClosed tr (PQKem.kemPk sk) :=
  h.elim .kemPkRand .kemPkClosed

theorem CompTightClosed.to_compTrClosed {tr : ExecTrace} {b : Bytes}
    (h : CompTightClosed tr b) : CompTrClosed (CompStructuredExposure tr) b := by
  induction h with
  | exposed h => exact .exposed h
  | literal bs => exact .literal bs
  | @dhPkRand sk _ => exact .dhPk sk
  | @dhPkClosed sk _ _ => exact .dhPk sk
  | dhSk sk pk _ ih => exact .dhSk sk pk ih
  | dhPeer sk s _ ih => exact .dhPeer sk s ih
  | @kemPkRand sk _ => exact .kemPk sk
  | @kemPkClosed sk _ _ => exact .kemPk sk
  | kemEncap pk e => exact .kemEncap pk e
  | kemSs pk e _ _ ih1 ih2 => exact .kemSs pk e ih1 ih2
  | kemSsKey sk e _ ih => exact .kemSsKey sk e ih
  | kemRejKey _ _ ih1 ih2 => exact .kemRejKey ih1 ih2
  | vk sk => exact .vk sk
  | sign sk nonce msg => exact .sign sk nonce msg
  | trunc8 m => exact .trunc8 m
  | kdf _ _ ih1 ih2 => exact .kdf ih1 ih2
  | concat _ _ ih1 ih2 => exact .concat ih1 ih2
  | symEnc _ ih => exact .symEnc ih
  | variant v _ ih => exact .variant v ih
  | trWireMsg _ _ _ ih1 ih2 ih3 =>
    exact .trWireMsg ih1 ih2 ih3
  | spqrInit _ _ ih1 ih2 => exact .spqrInit ih1 ih2
  | spqrChainKey authKey params idx => exact .spqrChainKey authKey params idx
  | spqrSendState _ _ ih1 ih2 => exact .spqrSendState ih1 ih2
  | spqrSendKey st coins => exact .spqrSendKey st coins
  | spqrSendMsg st coins => exact .spqrSendMsg st coins
  | spqrRecvState _ _ ih1 ih2 => exact .spqrRecvState ih1 ih2
  | spqrRecvKey st msg => exact .spqrRecvKey st msg

theorem CompTightClosed.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes}
    (h : CompTightClosed tr b) : CompTightClosed tr' b := by
  induction h with
  | exposed h => exact .exposed (CompStructuredExposure.mono hle h)
  | literal bs => exact .literal bs
  | dhPkRand h => exact .dhPkRand h
  | dhPkClosed _ ih => exact .dhPkClosed ih
  | dhSk sk pk _ ih => exact .dhSk sk pk ih
  | dhPeer sk s _ ih => exact .dhPeer sk s ih
  | kemPkRand h => exact .kemPkRand h
  | kemPkClosed _ ih => exact .kemPkClosed ih
  | kemEncap pk e => exact .kemEncap pk e
  | kemSs pk e _ _ ih1 ih2 => exact .kemSs pk e ih1 ih2
  | kemSsKey sk e _ ih => exact .kemSsKey sk e ih
  | kemRejKey _ _ ih1 ih2 => exact .kemRejKey ih1 ih2
  | vk sk => exact .vk sk
  | sign sk nonce msg => exact .sign sk nonce msg
  | trunc8 m => exact .trunc8 m
  | kdf _ _ ih1 ih2 => exact .kdf ih1 ih2
  | concat _ _ ih1 ih2 => exact .concat ih1 ih2
  | symEnc _ ih => exact .symEnc ih
  | variant v _ ih => exact .variant v ih
  | trWireMsg _ _ _ ih1 ih2 ih3 =>
    exact .trWireMsg ih1 ih2 ih3
  | spqrInit _ _ ih1 ih2 => exact .spqrInit ih1 ih2
  | spqrChainKey authKey params idx => exact .spqrChainKey authKey params idx
  | spqrSendState _ _ ih1 ih2 => exact .spqrSendState ih1 ih2
  | spqrSendKey st coins => exact .spqrSendKey st coins
  | spqrSendMsg st coins => exact .spqrSendMsg st coins
  | spqrRecvState _ _ ih1 ih2 => exact .spqrRecvState ih1 ih2
  | spqrRecvKey st msg => exact .spqrRecvKey st msg

theorem CompTightClosed.dh {tr : ExecTrace} {pk sk : Bytes} (hsk : CompTightClosed tr sk) :
    CompTightClosed tr (DiffieHellman.dh pk sk) := by
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 _
    split
    · exact .dhSk sk (DiffieHellman.dhPk sk2) hsk
    · exact .dhPeer sk2 sk hsk
  · exact .dhSk sk pk hsk

theorem CompStructuredExposure.exists_mkRand_or_kdfExtract {tr : ExecTrace} {b : Bytes}
    (h : CompStructuredExposure tr b) :
    (∃ ts sz, b = mkRand ts sz) ∨ (∃ s m, b = kdfExtract s m) := by
  rcases h with ⟨_⟩ | _ | ⟨⟨r, p, sk, rfl⟩, _⟩ | ⟨hsk, _⟩ | ⟨hsk, _⟩ | ⟨⟨c, rfl⟩, _⟩
  · exact .inl ⟨_, _, rfl⟩
  · exact .inr ⟨_, _, rfl⟩
  · exact .inr ⟨_, _, rfl⟩
  · exact .inr hsk.exists_kdfExtract
  · exact .inr hsk.exists_kdfExtract
  · exact .inr ⟨_, _, rfl⟩

section TightInversions
unseal Bytes

theorem CompTightClosed.inv_dhPk {tr : ExecTrace} {sk : Bytes}
    (h : CompTightClosed tr (DiffieHellman.dhPk sk)) :
    (∃ ts sz, sk = mkRand ts sz) ∨ CompTightClosed tr sk := by
  generalize hq : DiffieHellman.dhPk sk = q at h
  cases h with
  | exposed hexp =>
    rcases hexp.exists_mkRand_or_kdfExtract with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      · dsimp [DiffieHellman.dhPk, mkRand, kdfExtract] at hq
        exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | dhPkRand hsk =>
    obtain rfl := dhPk_inj hq
    exact .inl hsk
  | dhPkClosed hsk =>
    obtain rfl := dhPk_inj hq
    exact .inr hsk
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosed.inv_kemPk {tr : ExecTrace} {sk : Bytes}
    (h : CompTightClosed tr (PQKem.kemPk sk)) :
    (∃ ts sz, sk = mkRand ts sz) ∨ CompTightClosed tr sk := by
  generalize hq : PQKem.kemPk sk = q at h
  cases h with
  | exposed hexp =>
    rcases hexp.exists_mkRand_or_kdfExtract with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      · dsimp [PQKem.kemPk, mkRand, kdfExtract] at hq
        exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | kemPkRand hsk =>
    obtain rfl := kemPk_inj hq
    exact .inl hsk
  | kemPkClosed hsk =>
    obtain rfl := kemPk_inj hq
    exact .inr hsk
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosed.inv_concat {tr : ExecTrace} {lhs rhs : Bytes}
    (h : CompTightClosed tr (Concat.concat lhs rhs)) :
    CompTightClosed tr lhs ∧ CompTightClosed tr rhs := by
  generalize hq : Concat.concat lhs rhs = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compStructuredExposure tr _ hexp).1
    rw [← hq] at hnone
    dsimp [Concat.concat] at hnone
    rw [BytesView.view_pack] at hnone
    cases hnone
  | concat hlhs hrhs =>
    obtain ⟨rfl, rfl⟩ := concat_inj hq
    exact ⟨hlhs, hrhs⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosed.inv_trWireMsg {tr : ExecTrace}
    {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes} {ev : TrWire.EncodingVariation}
    (h : CompTightClosed tr (TrWire.trWireMsg v rk c pc ct pq ev)) :
    CompTightClosed tr rk ∧ CompTightClosed tr ct ∧ CompTightClosed tr pq := by
  generalize hq : TrWire.trWireMsg v rk c pc ct pq ev = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compStructuredExposure tr _ hexp).2.2.2.1
    rw [← hq] at hnone
    dsimp [TrWire.trWireMsg] at hnone
    rw [BytesView.view_pack] at hnone
    cases hnone
  | trWireMsg hrk hct hpq =>
    have hv := congrArg (fun b : Bytes => b.view? TrWire.TrWireMsg.SubF) hq
    simp only [TrWire.trWireMsg, TrWire.CanTrWireMsg.trWireMsg, BytesView.view_pack,
      Option.some.injEq, TrWire.TrWireMsg.SubF.mk.injEq] at hv
    obtain ⟨_, rfl, _, _, rfl, rfl, _⟩ := hv
    exact ⟨hrk, hct, hpq⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosed.inv_symEnc {tr : ExecTrace} {k iv msg : Bytes}
    (h : CompTightClosed tr (SymEnc.symEnc k iv msg)) : CompTightClosed tr msg := by
  generalize hq : SymEnc.symEnc k iv msg = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compStructuredExposure tr _ hexp).2.1
    rw [← hq] at hnone
    dsimp [SymEnc.symEnc] at hnone
    rw [BytesView.view_pack] at hnone
    cases hnone
  | symEnc hmsg =>
    have hv := congrArg (fun b : Bytes => b.view? SymEnc.Enc.SubF) hq
    simp only [SymEnc.symEnc, SymEnc.CanSymEnc.symEnc, BytesView.view_pack,
      Option.some.injEq, SymEnc.Enc.SubF.mk.injEq] at hv
    obtain ⟨_, _, rfl⟩ := hv
    exact hmsg
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosed.inv_variant {tr : ExecTrace} {x : X25519.Variant.SubF Bytes}
    (h : CompTightClosed tr x.pack) : CompTightClosed tr x.key := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compStructuredExposure tr _ hexp).2.2.1
    rw [← hq, BytesView.view_pack] at hnone
    cases hnone
  | variant v hkey =>
    have hv := congrArg (fun b : Bytes => b.view? X25519.Variant.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact hkey
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosed.inv_spqrInit {tr : ExecTrace} {x : Spqr.InitState.SubF Bytes}
    (h : CompTightClosed tr x.pack) :
    CompTightClosed tr x.authKey ∧ CompTightClosed tr x.params := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compStructuredExposure tr _ hexp).2.2.2.2.1
    rw [← hq, BytesView.view_pack] at hnone
    cases hnone
  | spqrInit hauth hparams =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.InitState.SubF) hq
    simp only [Spqr.spqrInit, BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact ⟨hauth, hparams⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosed.inv_spqrSendState {tr : ExecTrace} {x : Spqr.SendState.SubF Bytes}
    (h : CompTightClosed tr x.pack) :
    CompTightClosed tr x.st ∧ CompTightClosed tr x.coins := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compStructuredExposure tr _ hexp).2.2.2.2.2.1
    rw [← hq, BytesView.view_pack] at hnone
    cases hnone
  | spqrSendState hst hcoins =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.SendState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact ⟨hst, hcoins⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosed.inv_spqrRecvState {tr : ExecTrace} {x : Spqr.RecvState.SubF Bytes}
    (h : CompTightClosed tr x.pack) :
    CompTightClosed tr x.st ∧ CompTightClosed tr x.msg := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compStructuredExposure tr _ hexp).2.2.2.2.2.2
    rw [← hq, BytesView.view_pack] at hnone
    cases hnone
  | spqrRecvState hst hmsg =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.RecvState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact ⟨hst, hmsg⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

end TightInversions

theorem CompTightClosed.normalizeX25519Key {tr : ExecTrace} {pk : Bytes} (h : CompTightClosed tr pk) :
    CompTightClosed tr (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key
  have hp := Bytes.pack_view? X25519.Variant.SubF pk
  cases hv : pk.view? X25519.Variant.SubF with
  | none => exact h
  | some x =>
    rw [hv] at hp; rw [← hp] at h
    exact CompTightClosed.inv_variant h

theorem CompTightClosed.x25519TorsionVariant {tr : ExecTrace} {key : Bytes} (v : Fin 4) (t : Fin 8)
    (h : CompTightClosed tr key) : CompTightClosed tr (X25519.x25519TorsionVariant key v t) := by
  dsimp [X25519.x25519TorsionVariant]
  split
  · exact CompTightClosed.normalizeX25519Key h
  · exact .variant v (CompTightClosed.normalizeX25519Key h)

theorem CompTightClosed.spqrSendKey_of {tr : ExecTrace} (st coins : Bytes) :
    CompTightClosed tr (Spqr.spqrSend st coins).2.1 := by
  unfold Spqr.spqrSend
  dsimp only
  cases st.view? Spqr.InitState.SubF with
  | none => exact .spqrSendKey st coins
  | some x => exact .spqrChainKey x.authKey x.params (Spqr.encodeSpqrIndexTerm 1)

theorem CompTightClosed.spqrSendMsg_of {tr : ExecTrace} (st coins : Bytes) :
    CompTightClosed tr (Spqr.spqrSend st coins).2.2 := .spqrSendMsg st coins

theorem CompTightClosed.spqrRecvState_of {tr : ExecTrace} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r)
    (hst : CompTightClosed tr st) (hm : CompTightClosed tr msg) : CompTightClosed tr r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]
  exact .spqrRecvState hst hm

theorem CompTightClosed.spqrRecvKey_of {tr : ExecTrace} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) : CompTightClosed tr r.2 := by
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
      | none => rw [hd] at hrecv; cases hrecv
      | some dir =>
        rw [hd] at hrecv
        injection hrecv with hrecv'
        subst hrecv'
        dsimp only
        split
        · exact .literal _
        · exact .spqrChainKey authKey _ (Spqr.encodeSpqrIndexTerm idx)

set_option maxHeartbeats 400000 in
theorem CompTightClosed.attackerKnowledge_implies (tr : ExecTrace) :
    SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge (CompTightClosed tr) := by
  change SubAttackerKnowledge.Implies
    DY.Libsignal.Composed.attackerKnowledge (CompTightClosed tr)
  dsimp [DY.Libsignal.Composed.attackerKnowledge]
  apply SubAttackerKnowledge.combine.implies
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hlt⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
    intro b hb
    rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hb
    exact hb.elim
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Literal.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · intro b hb
      dsimp [Literal.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hb
      rcases hb with ⟨bs, rfl⟩; exact .literal bs
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Concat.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | n, hlt'⟩
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hb
      rcases hb with ⟨lhs, rhs, rfl, hlhs, hrhs⟩; exact .concat hlhs hrhs
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, rhs, i, hsplit, hinp⟩
      exact (CompTightClosed.inv_concat (Concat.concat_split inp i b rhs hsplit.symm ▸ hinp)).1
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, lhs, i, hsplit, hinp⟩
      exact (CompTightClosed.inv_concat (Concat.concat_split inp i lhs b hsplit.symm ▸ hinp)).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DiffieHellman.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, hsk⟩; exact .dhPk (.inr hsk)
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, sk, rfl, _, hsk⟩; exact CompTightClosed.dh hsk
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      KdfExtract.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · intro b hb
      dsimp [KdfExtract.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hb
      rcases hb with ⟨salt, ikm, rfl, hsalt, hikm⟩; exact .kdf hsalt hikm
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      SymEnc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨k', iv, msg, rfl, _, _, hmsg⟩; exact .symEnc hmsg
    · rintro b ⟨key, iv, ct, hdec, _, _, hct⟩
      dsimp [SymEnc.symDec, SymEnc.CanSymEnc.symDec] at hdec
      have hp := Bytes.pack_view? SymEnc.Enc.SubF ct
      cases hv : ct.view? SymEnc.Enc.SubF with
      | none => rw [hv] at hdec; cases hdec
      | some x =>
        rw [hv] at hdec hp
        rcases x with ⟨k', iv', msg'⟩
        dsimp only at hdec hp
        split at hdec
        · injection hdec with hdec'
          subst hdec'
          rw [← hp] at hct
          exact CompTightClosed.inv_symEnc hct
        · cases hdec
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Trunc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · rintro b ⟨m, rfl, _⟩; exact .trunc8 m
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      X25519.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨key, v, t, rfl, hkey⟩; exact CompTightClosed.x25519TorsionVariant v t hkey
    · rintro b ⟨x, hpack, rfl⟩; exact CompTightClosed.inv_variant hpack
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      PQKem.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨sk, rfl, hsk⟩; exact .kemPk (.inr hsk)
    · rintro b ⟨pk, e, rhs, heq, _, _⟩
      have h1 : b = (PQKem.kemEncap pk e).1 := congrArg Prod.fst heq
      rw [h1]; exact .kemEncap pk e
    · rintro b ⟨pk, e, lhs, heq, hpk, he⟩
      have h2 : b = (PQKem.kemEncap pk e).2 := congrArg Prod.snd heq
      rw [h2]; exact .kemSs pk e hpk he
    · rintro b ⟨sk, ct, hdec, hsk, _⟩
      obtain ⟨e, _, rfl⟩ := kemDecap_eq_some_iff.mp hdec.symm
      exact .kemSsKey sk e hsk
    · rintro b ⟨sk, ct, rfl, hsk, hct⟩
      exact .kemRejKey hsk hct
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Signature.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩; exact .vk sk
    · intro b hb
      dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, nonce, msg, rfl, _, _, _⟩; exact .sign sk nonce msg
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Spqr.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨authKey, params, rfl, hauth, hparams⟩; exact .spqrInit hauth hparams
    · rintro b ⟨authKey, params, idx, rfl, _, _, _⟩; exact .spqrChainKey authKey params idx
    · rintro b ⟨st, coins, rfl, hst, hcoins⟩; exact .spqrSendState hst hcoins
    · rintro b ⟨st, coins, rfl, _, _⟩; exact CompTightClosed.spqrSendKey_of st coins
    · rintro b ⟨st, coins, rfl, _, _⟩; exact .spqrSendMsg st coins
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, hst, hmsg⟩
      exact CompTightClosed.spqrRecvState_of hrecv hst hmsg
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, _, _⟩
      exact CompTightClosed.spqrRecvKey_of hrecv
    · rintro b (⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩)
      · exact (CompTightClosed.inv_spqrInit hpack).1
      · exact (CompTightClosed.inv_spqrInit hpack).2
      · exact (CompTightClosed.inv_spqrSendState hpack).1
      · exact (CompTightClosed.inv_spqrSendState hpack).2
      · exact (CompTightClosed.inv_spqrRecvState hpack).1
      · exact (CompTightClosed.inv_spqrRecvState hpack).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      TrWire.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, rfl, hrk, hct, hpq⟩
      exact .trWireMsg hrk hct hpq
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, hw, hmem⟩
      obtain ⟨hrk, hct, hpq⟩ := CompTightClosed.inv_trWireMsg hw
      rcases hmem with rfl | rfl | rfl <;> assumption
    · omega
  · omega

theorem CompTightClosed.of_attackerKnows {tr : ExecTrace}
    (hbase : ∀ b, tr.BaseAttackerKnows b → CompTightClosed tr b)
    {b : Bytes} (hk : b.AttackerKnows tr) : CompTightClosed tr b := by
  refine Bytes.AttackerKnows.is_least_fixpoint (CompTightClosed tr) b tr
    (CompTightClosed.attackerKnowledge_implies tr) (fun x hx => ?_) hk
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
  exact hbase x hx

theorem CompTightClosed.parseTrSignalMsg_pqRatchet {tr : ExecTrace}
    {t : Bytes} {msg : TRSignalMsg} (ht : CompTightClosed tr t)
    (hp : parseTrSignalMsg t = some msg) :
    CompTightClosed tr msg.pqRatchet := by
  unfold parseTrSignalMsg at hp
  rcases hsplit : Concat.split t (t.length - Trunc.trunc8Length) with _ | ⟨wire, mac⟩
  · rw [hsplit] at hp; cases hp
  · rw [hsplit] at hp; dsimp only [bind, Option.bind] at hp
    rcases hwf : TrWire.trWireMsgFields? wire with _ | x
    · rw [hwf] at hp; cases hp
    · rw [hwf] at hp
      injection hp with hp'
      subst hp'
      have hcat : Concat.concat wire mac = t :=
        Concat.concat_split t (t.length - Trunc.trunc8Length) wire mac hsplit
      obtain ⟨hwire, _⟩ := CompTightClosed.inv_concat (hcat ▸ ht)
      have htw := TrWire.trWireMsg_of_fields? hwf
      exact (CompTightClosed.inv_trWireMsg (htw ▸ hwire)).2.2

end Symbolic.Swarm.COMPOSED.CompRatchet
