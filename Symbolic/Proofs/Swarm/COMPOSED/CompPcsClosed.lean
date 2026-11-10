/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.COMPOSED.CompClosed
import DY.Bytes.Basic
import DY.Bytes.AttackerKnowledge
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
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
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
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra

/-!
# Composed DH-Share Origin Invariant and KDF-Closed Closure

Defines `IsCompDhsOf`, `CompPcsClosed`, and `CompDhsOriginInv`, showing on reachable composed
traces that every session DH ratchet secret is a fresh 32-byte random draw uniquely bound to its
session and ratchet index, and that stored states and network messages lie in `CompPcsClosed`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain hmac createChain kdfCk chainKeyAt
  findRecvChain recvChainFor x25519LowOrder)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent guardTrace)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg parseTrSignalMsg receiveSignalMsg
  ensureReceiverChain dhRatchetStep verifyMacAndDecrypt logSkippedKeys guardTrace)
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED.CompTermAlgebra
open Symbolic.Swarm.COMPOSED.CompTrace

/-- A secret DH ratchet share `dhs` belongs to session `s` at sending ratchet index `rIdx` on `tr`
if it is stored in a `TRState` snapshot of `s`, logged in `HonestDH s dhs prevRIdx` with
`rIdx = prevRIdx + 2`, or logged in `ExposedDHs s dhs rIdx`. -/
def IsCompDhsOf (tr : ExecTrace) (dhs : Bytes) (s : SessionInfo) (rIdx : Nat) : Prop :=
  (∃ st idx, StateStoredAt s.me st idx tr ∧ st.sessionInfo s.me = s ∧ st.dhs = dhs ∧ st.rIdx = rIdx) ∨
  (∃ prevRIdx, tr.EventLogged (TREvent.HonestDH s dhs prevRIdx) ∧ rIdx = prevRIdx + 2) ∨
  tr.EventLogged (TREvent.ExposedDHs s dhs rIdx)

theorem IsCompDhsOf.mono {tr tr' : ExecTrace} (hle : tr ≤ tr')
    {dhs : Bytes} {s : SessionInfo} {rIdx : Nat}
    (h : IsCompDhsOf tr dhs s rIdx) : IsCompDhsOf tr' dhs s rIdx := by
  rcases h with ⟨st, idx, hst, hs, hdhs, hr⟩ | ⟨prev, hev, hr⟩ | hev
  · exact .inl ⟨st, idx, trStateStoredAt_mono hle hst, hs, hdhs, hr⟩
  · exact .inr (.inl ⟨prev, eventLogged_mono hle hev, hr⟩)
  · exact .inr (.inr (eventLogged_mono hle hev))

theorem isCompDhsOf_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    {dhs : Bytes} {s : SessionInfo} {rIdx : Nat}
    (h : IsCompDhsOf (tr.append e) dhs s rIdx) : IsCompDhsOf tr dhs s rIdx := by
  rcases h with ⟨st, idx, hst, hs, hdhs, hr⟩ | ⟨prev, ⟨k, hk⟩, hr⟩ | ⟨k, hk⟩
  · exact .inl ⟨st, idx, trStateStoredAt_append_other hnone_st hst, hs, hdhs, hr⟩
  · exact .inr (.inl ⟨prev, ⟨k, eventLoggedAt_append_other hnone_tr hk⟩, hr⟩)
  · exact .inr (.inr ⟨k, eventLoggedAt_append_other hnone_tr hk⟩)

theorem isCompDhsOf_append_tr_inert {tr : ExecTrace} {ev : TREvent}
    (hne_hon : ∀ s dhs r, ev ≠ .HonestDH s dhs r)
    (hne_exp : ∀ s dhs r, ev ≠ .ExposedDHs s dhs r)
    {dhs : Bytes} {s : SessionInfo} {rIdx : Nat}
    (h : IsCompDhsOf (tr.append (TREvE ev)) dhs s rIdx) : IsCompDhsOf tr dhs s rIdx := by
  rcases h with ⟨st, idx, hst, hs, hdhs, hr⟩ | ⟨prev, ⟨k, hk⟩, hr⟩ | ⟨k, hk⟩
  · exact .inl ⟨st, idx, trStateStoredAt_append_other rfl hst, hs, hdhs, hr⟩
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact .inr (.inl ⟨prev, ⟨k, hk⟩, hr⟩)
    · exact False.elim (hne_hon s dhs prev heq)
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact .inr (.inr ⟨k, hk⟩)
    · exact False.elim (hne_exp s dhs rIdx heq)

theorem isCompDhsOf_append_trSt {tr : ExecTrace} {me : Participant} {st₀ : TRState}
    {dhs : Bytes} {s : SessionInfo} {rIdx : Nat}
    (h : IsCompDhsOf (tr.append (TRStE me st₀)) dhs s rIdx) :
    IsCompDhsOf tr dhs s rIdx ∨ (dhs = st₀.dhs ∧ s = st₀.sessionInfo me ∧ rIdx = st₀.rIdx) := by
  rcases h with ⟨st, idx, hst, hs, hdhs, hr⟩ | ⟨prev, ⟨k, hk⟩, hr⟩ | ⟨k, hk⟩
  · rcases trStateStoredAt_append_same hst with ⟨_, hst⟩ | ⟨_, hme, rfl⟩
    · exact .inl (.inl ⟨st, idx, hst, hs, hdhs, hr⟩)
    · exact .inr ⟨hdhs.symm, (hme ▸ hs).symm, hr.symm⟩
  · exact .inl (.inr (.inl ⟨prev, ⟨k, eventLoggedAt_append_other rfl hk⟩, hr⟩))
  · exact .inl (.inr (.inr ⟨k, eventLoggedAt_append_other rfl hk⟩))

theorem isCompDhsOf_append_honestDH {tr : ExecTrace} {s₀ : SessionInfo} {dhs₀ : Bytes} {prev₀ : Nat}
    {dhs : Bytes} {s : SessionInfo} {rIdx : Nat}
    (h : IsCompDhsOf (tr.append (TREvE (.HonestDH s₀ dhs₀ prev₀))) dhs s rIdx) :
    IsCompDhsOf tr dhs s rIdx ∨ (dhs = dhs₀ ∧ s = s₀ ∧ rIdx = prev₀ + 2) := by
  rcases h with ⟨st, idx, hst, hs, hdhs, hr⟩ | ⟨prev, ⟨k, hk⟩, hr⟩ | ⟨k, hk⟩
  · exact .inl (.inl ⟨st, idx, trStateStoredAt_append_other rfl hst, hs, hdhs, hr⟩)
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact .inl (.inr (.inl ⟨prev, ⟨k, hk⟩, hr⟩))
    · injection heq with hs_eq hdhs_eq hprev_eq
      subst hs_eq hdhs_eq hprev_eq
      exact .inr ⟨rfl, rfl, hr⟩
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact .inl (.inr (.inr ⟨k, hk⟩))
    · cases heq

theorem isCompDhsOf_append_exposedDHs {tr : ExecTrace} {s₀ : SessionInfo} {dhs₀ : Bytes} {r₀ : Nat}
    (hex : IsCompDhsOf tr dhs₀ s₀ r₀)
    {dhs : Bytes} {s : SessionInfo} {rIdx : Nat}
    (h : IsCompDhsOf (tr.append (TREvE (.ExposedDHs s₀ dhs₀ r₀))) dhs s rIdx) :
    IsCompDhsOf tr dhs s rIdx := by
  rcases h with ⟨st, idx, hst, hs, hdhs, hr⟩ | ⟨prev, ⟨k, hk⟩, hr⟩ | ⟨k, hk⟩
  · exact .inl ⟨st, idx, trStateStoredAt_append_other rfl hst, hs, hdhs, hr⟩
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact .inr (.inl ⟨prev, ⟨k, hk⟩, hr⟩)
    · cases heq
  · rcases eventLoggedAt_append_same hk with ⟨_, hk⟩ | ⟨_, heq⟩
    · exact .inr (.inr ⟨k, hk⟩)
    · injection heq with hs_eq hdhs_eq hr_eq
      subst hs_eq hdhs_eq hr_eq
      exact hex

/-- A random value `mkRand t sz` is allowed to be known by the attacker on `tr` only if it is
not a session DH ratchet secret (`¬ IsCompDhsOf`), or `ExposedDHs` was logged for it, or
`PQXDHEvent.BrokenDH` was logged. -/
def AllowedRand (tr : ExecTrace) (t sz : Nat) : Prop :=
  RandAt tr t sz ∧
  ((∀ s rIdx, ¬ IsCompDhsOf tr (mkRand t sz) s rIdx) ∨
   (∃ s rIdx, tr.EventLogged (TREvent.ExposedDHs s (mkRand t sz) rIdx)) ∨
   tr.EventLogged PQXDHEvent.BrokenDH)

theorem randAt_lt_length {tr : ExecTrace} {t sz : Nat} (h : RandAt tr t sz) :
    t < tr.length := by
  have hlt := Trace.at?_eq_some_implies_length_le (EntryT := Random.ExecEntryT) tr t
  unfold RandAt at h
  rw [h] at hlt
  exact hlt

theorem AllowedRand.mono_of_fresh {tr tr' : ExecTrace} (hle : tr ≤ tr')
    (hfresh : ∀ dhs s rIdx, IsCompDhsOf tr' dhs s rIdx →
      IsCompDhsOf tr dhs s rIdx ∨ ∀ t < tr.length, ∀ sz, dhs ≠ mkRand t sz)
    {t sz : Nat} (h : AllowedRand tr t sz) : AllowedRand tr' t sz := by
  refine ⟨randAt_mono hle h.1, ?_⟩
  have hlt : t < tr.length := randAt_lt_length h.1
  rcases h.2 with hnot | ⟨s, rIdx, hexp⟩ | hbrk
  · refine .inl fun s rIdx hdhs' => ?_
    rcases hfresh (mkRand t sz) s rIdx hdhs' with hdhs | hne
    · exact hnot s rIdx hdhs
    · exact hne t hlt sz rfl
  · exact .inr (.inl ⟨s, rIdx, eventLogged_mono hle hexp⟩)
  · exact .inr (.inr (eventLogged_mono hle hbrk))

/-- Inductive over-approximation of attacker-known terms on `tr` inverting `mkRand t sz` into
`AllowedRand tr t sz` and `PQKem.kemPk sk` for `invertKEM`, with unconditional `dhPk` and
`kdfExtract` constructors (`invertDH` is covered by `.brokenDH`). -/
inductive CompPcsClosed (tr : ExecTrace) : Bytes → Prop where
  | rand {t sz : Nat} (h : AllowedRand tr t sz) : CompPcsClosed tr (mkRand t sz)
  | brokenDH (h : tr.EventLogged PQXDHEvent.BrokenDH) (b : Bytes) : CompPcsClosed tr b
  | literal (bs : ByteArray) : CompPcsClosed tr (literalToBytes bs)
  | dhPk (sk : Bytes) : CompPcsClosed tr (DiffieHellman.dhPk sk)
  | dhPack (sk pk : Bytes) :
      CompPcsClosed tr (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack)
  | kemPk {sk : Bytes} (hsk : CompPcsClosed tr sk) : CompPcsClosed tr (PQKem.kemPk sk)
  | kemEncap (pk e : Bytes) : CompPcsClosed tr (PQKem.kemEncap pk e).1
  | kemSs (pk e : Bytes) : CompPcsClosed tr (PQKem.kemEncap pk e).2
  | kemRejKey (sk ct : Bytes) :
      CompPcsClosed tr (({ sk := sk, cipher := ct } : PQKem.RejKey.SubF Bytes).pack)
  | vk (sk : Bytes) : CompPcsClosed tr (DY.Signature.vk sk)
  | sign (sk nonce msg : Bytes) : CompPcsClosed tr (DY.Signature.sign sk nonce msg)
  | trunc8 (m : Bytes) : CompPcsClosed tr (DY.Trunc.trunc8 m)
  | kdf (salt ikm : Bytes) : CompPcsClosed tr (kdfExtract salt ikm)
  | concat {lhs rhs : Bytes} (hlhs : CompPcsClosed tr lhs) (hrhs : CompPcsClosed tr rhs) :
      CompPcsClosed tr (Concat.concat lhs rhs)
  | symEnc {k iv msg : Bytes} (hmsg : CompPcsClosed tr msg) :
      CompPcsClosed tr (DY.SymEnc.symEnc k iv msg)
  | variant {key : Bytes} (v : Fin 4) {t : Fin 8} (hkey : CompPcsClosed tr key) :
      CompPcsClosed tr (({ key := key, variation := v, torsion := t } : DY.X25519.Variant.SubF Bytes).pack)
  | trWireMsg {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes}
      {ev : DY.TrWire.EncodingVariation}
      (hrk : CompPcsClosed tr rk) (hct : CompPcsClosed tr ct) (hpq : CompPcsClosed tr pq) :
      CompPcsClosed tr (DY.TrWire.trWireMsg v rk c pc ct pq ev)
  | spqrInit {authKey params : Bytes}
      (hauth : CompPcsClosed tr authKey) (hparams : CompPcsClosed tr params) :
      CompPcsClosed tr (DY.Spqr.spqrInit authKey params)
  | spqrChainKey (authKey params idx : Bytes) :
      CompPcsClosed tr (DY.Spqr.spqrChainKey authKey params idx)
  | spqrSendState {st coins : Bytes}
      (hst : CompPcsClosed tr st) (hcoins : CompPcsClosed tr coins) :
      CompPcsClosed tr (({ st := st, coins := coins } : DY.Spqr.SendState.SubF Bytes).pack)
  | spqrSendKey (st coins : Bytes) :
      CompPcsClosed tr (({ st := st, coins := coins } : DY.Spqr.SendKey.SubF Bytes).pack)
  | spqrSendMsg (st coins : Bytes) :
      CompPcsClosed tr (({ st := st, coins := coins } : DY.Spqr.SendMsg.SubF Bytes).pack)
  | spqrRecvState {st msg : Bytes}
      (hst : CompPcsClosed tr st) (hmsg : CompPcsClosed tr msg) :
      CompPcsClosed tr (({ st := st, msg := msg } : DY.Spqr.RecvState.SubF Bytes).pack)
  | spqrRecvKey (st msg : Bytes) :
      CompPcsClosed tr (({ st := st, msg := msg } : DY.Spqr.RecvKey.SubF Bytes).pack)

theorem CompPcsClosed.mono_of_fresh {tr tr' : ExecTrace} (hle : tr ≤ tr')
    (hfresh : ∀ dhs s rIdx, IsCompDhsOf tr' dhs s rIdx →
      IsCompDhsOf tr dhs s rIdx ∨ ∀ t < tr.length, ∀ sz, dhs ≠ mkRand t sz)
    {b : Bytes} (h : CompPcsClosed tr b) : CompPcsClosed tr' b := by
  induction h with
  | rand hr => exact .rand (hr.mono_of_fresh hle hfresh)
  | brokenDH hbrk b => exact .brokenDH (eventLogged_mono hle hbrk) b
  | literal bs => exact .literal bs
  | dhPk sk => exact .dhPk sk
  | dhPack sk pk => exact .dhPack sk pk
  | kemPk _ ih => exact .kemPk ih
  | kemEncap pk e => exact .kemEncap pk e
  | kemSs pk e => exact .kemSs pk e
  | kemRejKey sk ct => exact .kemRejKey sk ct
  | vk sk => exact .vk sk
  | sign sk nonce msg => exact .sign sk nonce msg
  | trunc8 m => exact .trunc8 m
  | kdf salt ikm => exact .kdf salt ikm
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

theorem CompPcsClosed.dh {tr : ExecTrace} (pk sk : Bytes) :
    CompPcsClosed tr (DiffieHellman.dh pk sk) := by
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh]
  split
  · split <;> exact .dhPack _ _
  · exact .dhPack _ _

theorem CompPcsClosed.inv_rnd {tr : ExecTrace} {t sz : Nat}
    (h : CompPcsClosed tr (mkRand t sz)) :
    AllowedRand tr t sz ∨ tr.EventLogged PQXDHEvent.BrokenDH := by
  generalize hq : mkRand t sz = q at h
  cases h with
  | rand hr =>
    obtain ⟨rfl, rfl⟩ := mkRand_inj hq
    exact .inl hr
  | brokenDH hbrk => exact .inr hbrk
  | _ =>
    try dsimp [mkRand, literalToBytes, Concat.concat, kdfExtract,
      DY.Trunc.trunc8, DY.TrWire.trWireMsg, DY.SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      DY.Signature.vk, DY.Signature.sign, DY.Spqr.spqrInit, DY.Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompPcsClosed.inv_kemPk {tr : ExecTrace} {sk : Bytes}
    (h : CompPcsClosed tr (PQKem.kemPk sk)) :
    CompPcsClosed tr sk := by
  generalize hq : PQKem.kemPk sk = q at h
  cases h with
  | brokenDH hbrk => exact .brokenDH hbrk sk
  | kemPk hsk =>
    obtain rfl := kemPk_inj hq
    exact hsk
  | _ =>
    try dsimp [mkRand, literalToBytes, Concat.concat, kdfExtract,
      DY.Trunc.trunc8, DY.TrWire.trWireMsg, DY.SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      DY.Signature.vk, DY.Signature.sign, DY.Spqr.spqrInit, DY.Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompPcsClosed.inv_concat {tr : ExecTrace} {lhs rhs : Bytes}
    (h : CompPcsClosed tr (Concat.concat lhs rhs)) :
    CompPcsClosed tr lhs ∧ CompPcsClosed tr rhs := by
  generalize hq : Concat.concat lhs rhs = q at h
  cases h with
  | brokenDH hbrk => exact ⟨.brokenDH hbrk lhs, .brokenDH hbrk rhs⟩
  | concat hlhs hrhs =>
    dsimp [Concat.concat, Concat.CanConcat.concat] at hq
    cases Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    exact ⟨hlhs, hrhs⟩
  | _ =>
    try dsimp [mkRand, literalToBytes, Concat.concat, kdfExtract,
      DY.Trunc.trunc8, DY.TrWire.trWireMsg, DY.SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      DY.Signature.vk, DY.Signature.sign, DY.Spqr.spqrInit, DY.Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompPcsClosed.inv_symEnc {tr : ExecTrace} {k iv msg : Bytes}
    (h : CompPcsClosed tr (DY.SymEnc.symEnc k iv msg)) : CompPcsClosed tr msg := by
  generalize hq : DY.SymEnc.symEnc k iv msg = q at h
  cases h with
  | brokenDH hbrk => exact .brokenDH hbrk msg
  | symEnc hmsg =>
    dsimp [DY.SymEnc.symEnc, DY.SymEnc.CanSymEnc.symEnc] at hq
    cases Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    exact hmsg
  | _ =>
    try dsimp [mkRand, literalToBytes, Concat.concat, kdfExtract,
      DY.Trunc.trunc8, DY.TrWire.trWireMsg, DY.SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      DY.Signature.vk, DY.Signature.sign, DY.Spqr.spqrInit, DY.Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompPcsClosed.inv_variant {tr : ExecTrace}
    {x : DY.X25519.Variant.SubF Bytes} (h : CompPcsClosed tr x.pack) :
    CompPcsClosed tr x.key := by
  generalize hq : x.pack = q at h
  cases h with
  | brokenDH hbrk => exact .brokenDH hbrk x.key
  | variant v hkey =>
    have hv := Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    cases x; cases hv; exact hkey
  | _ =>
    try dsimp [mkRand, literalToBytes, Concat.concat, kdfExtract,
      DY.Trunc.trunc8, DY.TrWire.trWireMsg, DY.SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      DY.Signature.vk, DY.Signature.sign, DY.Spqr.spqrInit, DY.Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompPcsClosed.normalizeX25519Key {tr : ExecTrace} {pk : Bytes}
    (h : CompPcsClosed tr pk) : CompPcsClosed tr (DY.X25519.normalizeX25519Key pk) := by
  unfold DY.X25519.normalizeX25519Key
  have hp := Bytes.pack_view? DY.X25519.Variant.SubF pk
  cases hv : pk.view? DY.X25519.Variant.SubF with
  | none => exact h
  | some x => rw [hv] at hp; rw [← hp] at h; exact CompPcsClosed.inv_variant h

theorem CompPcsClosed.x25519TorsionVariant {tr : ExecTrace}
    {key : Bytes} (v : Fin 4) (t : Fin 8) (hkey : CompPcsClosed tr key) :
    CompPcsClosed tr (DY.X25519.x25519TorsionVariant key v t) := by
  dsimp [DY.X25519.x25519TorsionVariant]
  split
  · exact CompPcsClosed.normalizeX25519Key hkey
  · exact .variant v (CompPcsClosed.normalizeX25519Key hkey)

theorem CompPcsClosed.inv_trWireMsg {tr : ExecTrace}
    {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes} {ev : DY.TrWire.EncodingVariation}
    (h : CompPcsClosed tr (DY.TrWire.trWireMsg v rk c pc ct pq ev)) :
    CompPcsClosed tr rk ∧ CompPcsClosed tr ct ∧ CompPcsClosed tr pq := by
  generalize hq : DY.TrWire.trWireMsg v rk c pc ct pq ev = q at h
  cases h with
  | brokenDH hbrk =>
    exact ⟨.brokenDH hbrk rk, .brokenDH hbrk ct, .brokenDH hbrk pq⟩
  | trWireMsg hrk hct hpq =>
    dsimp [DY.TrWire.trWireMsg, DY.TrWire.CanTrWireMsg.trWireMsg] at hq
    cases Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    exact ⟨hrk, hct, hpq⟩
  | _ =>
    try dsimp [mkRand, literalToBytes, Concat.concat, kdfExtract,
      DY.Trunc.trunc8, DY.TrWire.trWireMsg, DY.SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      DY.Signature.vk, DY.Signature.sign, DY.Spqr.spqrInit, DY.Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompPcsClosed.inv_spqrInit {tr : ExecTrace}
    {x : DY.Spqr.InitState.SubF Bytes} (h : CompPcsClosed tr x.pack) :
    CompPcsClosed tr x.authKey ∧ CompPcsClosed tr x.params := by
  generalize hq : x.pack = q at h
  cases h with
  | brokenDH hbrk => exact ⟨.brokenDH hbrk x.authKey, .brokenDH hbrk x.params⟩
  | spqrInit hauth hparams =>
    dsimp [DY.Spqr.spqrInit] at hq
    have hv := Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    cases x; cases hv; exact ⟨hauth, hparams⟩
  | _ =>
    try dsimp [mkRand, literalToBytes, Concat.concat, kdfExtract,
      DY.Trunc.trunc8, DY.TrWire.trWireMsg, DY.SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      DY.Signature.vk, DY.Signature.sign, DY.Spqr.spqrInit, DY.Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompPcsClosed.inv_spqrSendState {tr : ExecTrace}
    {x : DY.Spqr.SendState.SubF Bytes} (h : CompPcsClosed tr x.pack) :
    CompPcsClosed tr x.st ∧ CompPcsClosed tr x.coins := by
  generalize hq : x.pack = q at h
  cases h with
  | brokenDH hbrk => exact ⟨.brokenDH hbrk x.st, .brokenDH hbrk x.coins⟩
  | spqrSendState hst hcoins =>
    have hv := Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    cases x; cases hv; exact ⟨hst, hcoins⟩
  | _ =>
    try dsimp [mkRand, literalToBytes, Concat.concat, kdfExtract,
      DY.Trunc.trunc8, DY.TrWire.trWireMsg, DY.SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      DY.Signature.vk, DY.Signature.sign, DY.Spqr.spqrInit, DY.Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompPcsClosed.inv_spqrRecvState {tr : ExecTrace}
    {x : DY.Spqr.RecvState.SubF Bytes} (h : CompPcsClosed tr x.pack) :
    CompPcsClosed tr x.st ∧ CompPcsClosed tr x.msg := by
  generalize hq : x.pack = q at h
  cases h with
  | brokenDH hbrk => exact ⟨.brokenDH hbrk x.st, .brokenDH hbrk x.msg⟩
  | spqrRecvState hst hmsg =>
    have hv := Symbolic.DYBridge.DY.BytesView.pack_inj.mp hq
    cases x; cases hv; exact ⟨hst, hmsg⟩
  | _ =>
    try dsimp [mkRand, literalToBytes, Concat.concat, kdfExtract,
      DY.Trunc.trunc8, DY.TrWire.trWireMsg, DY.SymEnc.symEnc,
      DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      DY.Signature.vk, DY.Signature.sign, DY.Spqr.spqrInit, DY.Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompPcsClosed.spqrSendKey_of {tr : ExecTrace} (st coins : Bytes) :
    CompPcsClosed tr (DY.Spqr.spqrSend st coins).2.1 := by
  unfold DY.Spqr.spqrSend
  dsimp only
  cases st.view? DY.Spqr.InitState.SubF with
  | none => exact .spqrSendKey st coins
  | some x => exact .spqrChainKey x.authKey x.params (DY.Spqr.encodeSpqrIndexTerm 1)

theorem CompPcsClosed.spqrRecvState_of {tr : ExecTrace} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : DY.Spqr.spqrRecv st msg idx = some r)
    (hst : CompPcsClosed tr st) (hm : CompPcsClosed tr msg) : CompPcsClosed tr r.1 := by
  rw [DY.Spqr.spqrRecv_state st msg idx r hrecv]
  exact .spqrRecvState hst hm

theorem CompPcsClosed.spqrRecvKey_of {tr : ExecTrace} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : DY.Spqr.spqrRecv st msg idx = some r) :
    CompPcsClosed tr r.2 := by
  unfold DY.Spqr.spqrRecv at hrecv
  split at hrecv
  · cases hrecv
  · cases hv : st.view? DY.Spqr.InitState.SubF with
    | none =>
      rw [hv] at hrecv
      injection hrecv with hrecv'
      subst hrecv'
      exact .spqrRecvKey st msg
    | some x =>
      rw [hv] at hrecv
      rcases x with ⟨authKey, params⟩
      dsimp only at hrecv
      cases hd : DY.Spqr.spqrParamsDir? params with
      | none => rw [hd] at hrecv; cases hrecv
      | some dir =>
        rw [hd] at hrecv
        injection hrecv with hrecv'
        subst hrecv'
        dsimp only
        split
        · exact .literal _
        · exact .spqrChainKey authKey _ (DY.Spqr.encodeSpqrIndexTerm idx)

set_option maxHeartbeats 400000 in
theorem CompPcsClosed.attackerKnowledge_implies (tr : ExecTrace) :
    SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge (CompPcsClosed tr) := by
  change SubAttackerKnowledge.Implies
    DY.Libsignal.Composed.attackerKnowledge (CompPcsClosed tr)
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
      exact (CompPcsClosed.inv_concat (Concat.concat_split inp i b rhs hsplit.symm ▸ hinp)).1
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, lhs, i, hsplit, hinp⟩
      exact (CompPcsClosed.inv_concat (Concat.concat_split inp i lhs b hsplit.symm ▸ hinp)).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DiffieHellman.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩; exact .dhPk sk
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, sk, rfl, _, _⟩; exact CompPcsClosed.dh pk sk
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      KdfExtract.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · intro b hb
      dsimp [KdfExtract.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hb
      rcases hb with ⟨salt, ikm, rfl, _, _⟩; exact .kdf salt ikm
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DY.SymEnc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨k', iv, msg, rfl, _, _, hmsg⟩; exact .symEnc hmsg
    · rintro b ⟨key, iv, ct, hdec, _, _, hct⟩
      dsimp [DY.SymEnc.symDec, DY.SymEnc.CanSymEnc.symDec] at hdec
      have hp := Bytes.pack_view? DY.SymEnc.Enc.SubF ct
      cases hv : ct.view? DY.SymEnc.Enc.SubF with
      | none => rw [hv] at hdec; cases hdec
      | some x =>
        rw [hv] at hdec hp
        rcases x with ⟨k', iv', msg'⟩
        dsimp only at hdec hp
        split at hdec
        · injection hdec with hdec'
          subst hdec'
          rw [← hp] at hct
          exact CompPcsClosed.inv_symEnc hct
        · cases hdec
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DY.Trunc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · rintro b ⟨m, rfl, _⟩; exact .trunc8 m
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DY.X25519.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨key, v, t, rfl, hkey⟩; exact CompPcsClosed.x25519TorsionVariant v t hkey
    · rintro b ⟨x, hpack, rfl⟩; exact CompPcsClosed.inv_variant hpack
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DY.PQKem.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨sk, rfl, hsk⟩; exact .kemPk hsk
    · rintro b ⟨pk, e, rhs, heq, _, _⟩
      have h1 : b = (PQKem.kemEncap pk e).1 := congrArg Prod.fst heq
      rw [h1]; exact .kemEncap pk e
    · rintro b ⟨pk, e, lhs, heq, _, _⟩
      have h2 : b = (PQKem.kemEncap pk e).2 := congrArg Prod.snd heq
      rw [h2]; exact .kemSs pk e
    · rintro b ⟨sk, ct, hdec, _, _⟩
      obtain ⟨e, _, rfl⟩ := kemDecap_eq_some_iff.mp hdec.symm
      exact .kemSs (PQKem.kemPk sk) e
    · rintro b ⟨sk, ct, rfl, _, _⟩
      exact .kemRejKey sk ct
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DY.Signature.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [DY.Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩; exact .vk sk
    · intro b hb
      dsimp [DY.Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, nonce, msg, rfl, _, _, _⟩; exact .sign sk nonce msg
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DY.Spqr.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨authKey, params, rfl, hauth, hparams⟩; exact .spqrInit hauth hparams
    · rintro b ⟨authKey, params, idx, rfl, _, _, _⟩; exact .spqrChainKey authKey params idx
    · rintro b ⟨st, coins, rfl, hst, hcoins⟩; exact .spqrSendState hst hcoins
    · rintro b ⟨st, coins, rfl, _, _⟩; exact CompPcsClosed.spqrSendKey_of st coins
    · rintro b ⟨st, coins, rfl, _, _⟩; exact .spqrSendMsg st coins
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, hst, hmsg⟩
      exact CompPcsClosed.spqrRecvState_of hrecv hst hmsg
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, _, _⟩
      exact CompPcsClosed.spqrRecvKey_of hrecv
    · rintro b (⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩)
      · exact (CompPcsClosed.inv_spqrInit hpack).1
      · exact (CompPcsClosed.inv_spqrInit hpack).2
      · exact (CompPcsClosed.inv_spqrSendState hpack).1
      · exact (CompPcsClosed.inv_spqrSendState hpack).2
      · exact (CompPcsClosed.inv_spqrRecvState hpack).1
      · exact (CompPcsClosed.inv_spqrRecvState hpack).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DY.TrWire.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, rfl, hrk, hct, hpq⟩
      exact .trWireMsg hrk hct hpq
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, hw, hmem⟩
      obtain ⟨hrk, hct, hpq⟩ := CompPcsClosed.inv_trWireMsg hw
      rcases hmem with rfl | rfl | rfl <;> assumption
    · omega
  · omega

theorem CompPcsClosed.of_attackerKnows {tr : ExecTrace}
    (hbase : ∀ b, tr.BaseAttackerKnows b → CompPcsClosed tr b)
    {b : Bytes} (hk : b.AttackerKnows tr) : CompPcsClosed tr b := by
  refine Bytes.AttackerKnows.is_least_fixpoint (CompPcsClosed tr) b tr
    (CompPcsClosed.attackerKnowledge_implies tr) (fun x hx => ?_) hk
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
  exact hbase x hx

theorem CompPcsClosed.parseTrSignalMsg_fields {tr : ExecTrace}
    {t : Bytes} {msg : TRSignalMsg} (ht : CompPcsClosed tr t)
    (hp : DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg) :
    CompPcsClosed tr msg.wire ∧ CompPcsClosed tr msg.mac ∧ CompPcsClosed tr msg.ratchetKey ∧
      CompPcsClosed tr msg.ciphertext ∧ CompPcsClosed tr msg.pqRatchet := by
  unfold DY.Libsignal.TripleRatchet.parseTrSignalMsg at hp
  rcases hsplit : Concat.split t (t.length - DY.Trunc.trunc8Length) with _ | ⟨wire, mac⟩
  · rw [hsplit] at hp; cases hp
  · rw [hsplit] at hp; dsimp only [bind, Option.bind] at hp
    rcases hwf : DY.TrWire.trWireMsgFields? wire with _ | x
    · rw [hwf] at hp; cases hp
    · rw [hwf] at hp
      injection hp with hp'
      subst hp'
      have hcat : Concat.concat wire mac = t :=
        Concat.concat_split t (t.length - DY.Trunc.trunc8Length) wire mac hsplit
      obtain ⟨hwire, hmac⟩ := CompPcsClosed.inv_concat (hcat ▸ ht)
      have htw := DY.TrWire.trWireMsg_of_fields? hwf
      obtain ⟨hrk, hct, hpq⟩ := CompPcsClosed.inv_trWireMsg (htw ▸ hwire)
      exact ⟨hwire, hmac, hrk, hct, hpq⟩

/-- Structural closure of a stored `TRState` snapshot under `CompPcsClosed`. -/
def TRStateClosed (tr : ExecTrace) (st : TRState) : Prop :=
  1 ≤ st.rIdx ∧
  CompPcsClosed tr st.rk ∧
  CompPcsClosed tr st.cks ∧
  (∀ c ∈ st.recv, CompPcsClosed tr c.chainKey) ∧
  CompPcsClosed tr st.spqr

theorem TRStateClosed.mono_of_fresh {tr tr' : ExecTrace} (hle : tr ≤ tr')
    (hfresh : ∀ dhs s rIdx, IsCompDhsOf tr' dhs s rIdx →
      IsCompDhsOf tr dhs s rIdx ∨ ∀ t < tr.length, ∀ sz, dhs ≠ mkRand t sz)
    {st : TRState} (h : TRStateClosed tr st) : TRStateClosed tr' st :=
  ⟨h.1, h.2.1.mono_of_fresh hle hfresh, h.2.2.1.mono_of_fresh hle hfresh,
   fun c hc => (h.2.2.2.1 c hc).mono_of_fresh hle hfresh,
   h.2.2.2.2.mono_of_fresh hle hfresh⟩

/-- Inductive invariant on reachable composed traces stating that every session DH ratchet secret
(`IsCompDhsOf`) is a 32-byte random draw uniquely bound to `(s, rIdx)`, and every stored state
field and network message is in `CompPcsClosed`. -/
structure CompDhsOriginInv (tr : ExecTrace) : Prop where
  dhs_rand : ∀ dhs s rIdx, IsCompDhsOf tr dhs s rIdx → ∃ t, RandAt tr t 32 ∧ dhs = mkRand t 32
  dhs_unique : ∀ dhs s₁ r₁ s₂ r₂,
    IsCompDhsOf tr dhs s₁ r₁ → IsCompDhsOf tr dhs s₂ r₂ → s₁ = s₂ ∧ r₁ = r₂
  trSt_ok : ∀ p st idx, StateStoredAt p st idx tr → TRStateClosed tr st
  skipped_ok : ∀ s pk n seed rIdx src,
    tr.EventLogged (TREvent.SkippedKeyStored s pk n seed rIdx src) → CompPcsClosed tr seed
  pqxSt_ok : ∀ p st idx, PQXDHStoredAt tr p st idx → CompPcsClosed tr st.sk
  base_ok : ∀ b, tr.BaseAttackerKnows b → CompPcsClosed tr b

theorem CompDhsOriginInv.nil : CompDhsOriginInv Trace.nil where
  dhs_rand _ _ _ h := by
    rcases h with ⟨_, k, h, _⟩ | ⟨_, ⟨k, h⟩, _⟩ | ⟨k, h⟩
    · obtain ⟨hlt, _⟩ := (Trace.at?_eq_some (Trace.nil : ExecTrace) k _).mp h
      exact absurd hlt (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)
    · exact absurd (Trace.EventLoggedAt_implies_i_le_length _ k Trace.nil h)
        (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)
    · exact absurd (Trace.EventLoggedAt_implies_i_le_length _ k Trace.nil h)
        (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)
  dhs_unique _ _ _ _ _ h _ := by
    rcases h with ⟨_, k, h, _⟩ | ⟨_, ⟨k, h⟩, _⟩ | ⟨k, h⟩
    · obtain ⟨hlt, _⟩ := (Trace.at?_eq_some (Trace.nil : ExecTrace) k _).mp h
      exact absurd hlt (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)
    · exact absurd (Trace.EventLoggedAt_implies_i_le_length _ k Trace.nil h)
        (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)
    · exact absurd (Trace.EventLoggedAt_implies_i_le_length _ k Trace.nil h)
        (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)
  trSt_ok _ _ k h := by
    obtain ⟨hlt, _⟩ := (Trace.at?_eq_some (Trace.nil : ExecTrace) k _).mp h
    exact absurd hlt (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)
  skipped_ok _ _ _ _ _ _ h := by
    obtain ⟨k, h⟩ := h
    exact absurd (Trace.EventLoggedAt_implies_i_le_length _ k Trace.nil h)
      (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)
  pqxSt_ok _ _ k h := by
    obtain ⟨hlt, _⟩ := (Trace.at?_eq_some (Trace.nil : ExecTrace) k _).mp h
    exact absurd hlt (Symbolic.DYBridge.DY.Trace.nil_length_not_lt k)
  base_ok _ h := by
    rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1] at h
    exact False.elim h

theorem CompDhsOriginInv.not_isCompDhsOf_of_ge {tr : ExecTrace} (hInv : CompDhsOriginInv tr)
    {t sz : Nat} (ht : tr.length ≤ t) (s : SessionInfo) (rIdx : Nat) :
    ¬ IsCompDhsOf tr (mkRand t sz) s rIdx := by
  intro hdhs
  obtain ⟨t', hrnd', heq⟩ := hInv.dhs_rand _ s rIdx hdhs
  have hlt : t' < tr.length := randAt_lt_length hrnd'
  obtain ⟨rfl, _⟩ := mkRand_inj heq
  omega

theorem CompDhsOriginInv.preserve_fresh {tr tr' : ExecTrace} (hle : tr ≤ tr')
    (t₀ : Nat) (s₀ : SessionInfo) (r₀ : Nat)
    (ht₀ : tr.length ≤ t₀) (hrnd₀ : RandAt tr' t₀ 32)
    (hdhs : ∀ dhs s rIdx, IsCompDhsOf tr' dhs s rIdx →
      IsCompDhsOf tr dhs s rIdx ∨ (dhs = mkRand t₀ 32 ∧ s = s₀ ∧ rIdx = r₀))
    (htrSt : ∀ p st idx, StateStoredAt p st idx tr' →
      StateStoredAt p st idx tr ∨ TRStateClosed tr' st)
    (hsk : ∀ s pk n seed rIdx src,
      tr'.EventLogged (TREvent.SkippedKeyStored s pk n seed rIdx src) →
      tr.EventLogged (TREvent.SkippedKeyStored s pk n seed rIdx src) ∨ CompPcsClosed tr' seed)
    (hpqx : ∀ p st idx, PQXDHStoredAt tr' p st idx →
      PQXDHStoredAt tr p st idx ∨ CompPcsClosed tr' st.sk)
    (hbase : ∀ b, tr'.BaseAttackerKnows b →
      tr.BaseAttackerKnows b ∨ CompPcsClosed tr' b)
    (hInv : CompDhsOriginInv tr) : CompDhsOriginInv tr' := by
  have hfresh : ∀ dhs s rIdx, IsCompDhsOf tr' dhs s rIdx →
      IsCompDhsOf tr dhs s rIdx ∨ ∀ t < tr.length, ∀ sz, dhs ≠ mkRand t sz := by
    intro dhs s rIdx h
    rcases hdhs dhs s rIdx h with h₀ | ⟨rfl, _, _⟩
    · exact .inl h₀
    · refine .inr fun t hlt sz heq => ?_
      obtain ⟨rfl, _⟩ := mkRand_inj heq
      omega
  refine {
    dhs_rand := fun dhs s rIdx h => ?_
    dhs_unique := fun dhs s₁ r₁ s₂ r₂ h₁ h₂ => ?_
    trSt_ok := fun p st idx h => ?_
    skipped_ok := fun s pk n seed rIdx src h => ?_
    pqxSt_ok := fun p st idx h => ?_
    base_ok := fun b h => ?_
  }
  · rcases hdhs dhs s rIdx h with h₀ | ⟨rfl, _, _⟩
    · obtain ⟨t, hrnd, heq⟩ := hInv.dhs_rand dhs s rIdx h₀
      exact ⟨t, randAt_mono hle hrnd, heq⟩
    · exact ⟨t₀, hrnd₀, rfl⟩
  · rcases hdhs dhs s₁ r₁ h₁ with h₁₀ | ⟨hdhs₁, rfl, rfl⟩ <;>
      rcases hdhs dhs s₂ r₂ h₂ with h₂₀ | ⟨hdhs₂, rfl, rfl⟩
    · exact hInv.dhs_unique dhs s₁ r₁ s₂ r₂ h₁₀ h₂₀
    · exact False.elim (hInv.not_isCompDhsOf_of_ge ht₀ s₁ r₁ (hdhs₂ ▸ h₁₀))
    · exact False.elim (hInv.not_isCompDhsOf_of_ge ht₀ s₂ r₂ (hdhs₁ ▸ h₂₀))
    · exact ⟨rfl, rfl⟩
  · rcases htrSt p st idx h with h₀ | hclosed
    · exact (hInv.trSt_ok p st idx h₀).mono_of_fresh hle hfresh
    · exact hclosed
  · rcases hsk s pk n seed rIdx src h with h₀ | hclosed
    · exact (hInv.skipped_ok s pk n seed rIdx src h₀).mono_of_fresh hle hfresh
    · exact hclosed
  · rcases hpqx p st idx h with h₀ | hclosed
    · exact (hInv.pqxSt_ok p st idx h₀).mono_of_fresh hle hfresh
    · exact hclosed
  · rcases hbase b h with h₀ | hclosed
    · exact (hInv.base_ok b h₀).mono_of_fresh hle hfresh
    · exact hclosed

theorem CompDhsOriginInv.preserve_same {tr tr' : ExecTrace} (hle : tr ≤ tr')
    (hdhs : ∀ dhs s rIdx, IsCompDhsOf tr' dhs s rIdx → IsCompDhsOf tr dhs s rIdx)
    (htrSt : ∀ p st idx, StateStoredAt p st idx tr' →
      StateStoredAt p st idx tr ∨ TRStateClosed tr' st)
    (hsk : ∀ s pk n seed rIdx src,
      tr'.EventLogged (TREvent.SkippedKeyStored s pk n seed rIdx src) →
      tr.EventLogged (TREvent.SkippedKeyStored s pk n seed rIdx src) ∨ CompPcsClosed tr' seed)
    (hpqx : ∀ p st idx, PQXDHStoredAt tr' p st idx →
      PQXDHStoredAt tr p st idx ∨ CompPcsClosed tr' st.sk)
    (hbase : ∀ b, tr'.BaseAttackerKnows b →
      tr.BaseAttackerKnows b ∨ CompPcsClosed tr' b)
    (hInv : CompDhsOriginInv tr) : CompDhsOriginInv tr' := by
  have hfresh : ∀ dhs s rIdx, IsCompDhsOf tr' dhs s rIdx →
      IsCompDhsOf tr dhs s rIdx ∨ ∀ t < tr.length, ∀ sz, dhs ≠ mkRand t sz :=
    fun dhs s rIdx h => .inl (hdhs dhs s rIdx h)
  refine {
    dhs_rand := fun dhs s rIdx h => ?_
    dhs_unique := fun dhs s₁ r₁ s₂ r₂ h₁ h₂ =>
      hInv.dhs_unique dhs s₁ r₁ s₂ r₂ (hdhs dhs s₁ r₁ h₁) (hdhs dhs s₂ r₂ h₂)
    trSt_ok := fun p st idx h => ?_
    skipped_ok := fun s pk n seed rIdx src h => ?_
    pqxSt_ok := fun p st idx h => ?_
    base_ok := fun b h => ?_
  }
  · obtain ⟨t, hrnd, heq⟩ := hInv.dhs_rand dhs s rIdx (hdhs dhs s rIdx h)
    exact ⟨t, randAt_mono hle hrnd, heq⟩
  · rcases htrSt p st idx h with h₀ | hclosed
    · exact (hInv.trSt_ok p st idx h₀).mono_of_fresh hle hfresh
    · exact hclosed
  · rcases hsk s pk n seed rIdx src h with h₀ | hclosed
    · exact (hInv.skipped_ok s pk n seed rIdx src h₀).mono_of_fresh hle hfresh
    · exact hclosed
  · rcases hpqx p st idx h with h₀ | hclosed
    · exact (hInv.pqxSt_ok p st idx h₀).mono_of_fresh hle hfresh
    · exact hclosed
  · rcases hbase b h with h₀ | hclosed
    · exact (hInv.base_ok b h₀).mono_of_fresh hle hfresh
    · exact hclosed

theorem CompPcsClosed.mono_append_other {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} {e : E}
    (hnone_tr : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TREntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none)
    {b : Bytes} (h : CompPcsClosed tr b) : CompPcsClosed (tr.append e) b :=
  h.mono_of_fresh (Trace.append_le tr e) fun _ _ _ hdhs =>
    .inl (isCompDhsOf_append_other hnone_tr hnone_st hdhs)

theorem CompDhsOriginInv.append_rnd {tr : ExecTrace} (n : Nat) (hInv : CompDhsOriginInv tr) :
    CompDhsOriginInv (tr.append (RndE n)) :=
  hInv.preserve_same (Trace.append_le tr _)
    (fun _ _ _ h => isCompDhsOf_append_other rfl rfl h)
    (fun _ _ _ h => .inl (trStateStoredAt_append_other rfl h))
    (fun _ _ _ _ _ _ h => .inl ((eventLogged_append_other_iff rfl).mp h))
    (fun _ _ _ h => .inl (pqxdhStoredAt_append_other rfl h))
    (fun b h => .inl ((baseAttackerKnows_append_rnd tr n b).mp h))

theorem CompDhsOriginInv.fresh_rand_closed {tr : ExecTrace} (n : Nat) (hInv : CompDhsOriginInv tr) :
    CompPcsClosed (tr.append (RndE n)) (mkRand tr.length n) :=
  .rand ⟨randAt_here tr n, .inl fun s rIdx h =>
    hInv.not_isCompDhsOf_of_ge (Nat.le_refl _) s rIdx (isCompDhsOf_append_other rfl rfl h)⟩

theorem CompDhsOriginInv.append_pqEv {tr : ExecTrace} (ev : PQXDHEvent) (hInv : CompDhsOriginInv tr) :
    CompDhsOriginInv (tr.append (PQEvE ev)) :=
  hInv.preserve_same (Trace.append_le tr _)
    (fun _ _ _ h => isCompDhsOf_append_other rfl rfl h)
    (fun _ _ _ h => .inl (trStateStoredAt_append_other rfl h))
    (fun _ _ _ _ _ _ h => .inl ((eventLogged_append_other_iff rfl).mp h))
    (fun _ _ _ h => .inl (pqxdhStoredAt_append_other rfl h))
    (fun b h => .inl ((baseAttackerKnows_append_pqEv tr ev b).mp h))

theorem CompDhsOriginInv.append_net {tr : ExecTrace} {msg : Bytes}
    (hmsg : CompPcsClosed (tr.append (NetE msg)) msg) (hInv : CompDhsOriginInv tr) :
    CompDhsOriginInv (tr.append (NetE msg)) :=
  hInv.preserve_same (Trace.append_le tr _)
    (fun _ _ _ h => isCompDhsOf_append_other rfl rfl h)
    (fun _ _ _ h => .inl (trStateStoredAt_append_other rfl h))
    (fun _ _ _ _ _ _ h => .inl ((eventLogged_append_other_iff rfl).mp h))
    (fun _ _ _ h => .inl (pqxdhStoredAt_append_other rfl h))
    (fun b h => by
      rcases (baseAttackerKnows_append_net tr msg b).mp h with rfl | hb
      · exact .inr hmsg
      · exact .inl hb)

theorem CompDhsOriginInv.append_net_of {tr : ExecTrace} {msg : Bytes}
    (hmsg : CompPcsClosed tr msg) (hInv : CompDhsOriginInv tr) :
    CompDhsOriginInv (tr.append (NetE msg)) :=
  hInv.append_net (hmsg.mono_append_other rfl rfl)

theorem CompDhsOriginInv.append_pqSt {tr : ExecTrace} (p : Participant) (st : PQXDHState)
    (hsk : CompPcsClosed tr st.sk) (hInv : CompDhsOriginInv tr) :
    CompDhsOriginInv (tr.append (PQStE p st)) :=
  hInv.preserve_same (Trace.append_le tr _)
    (fun _ _ _ h => isCompDhsOf_append_other rfl rfl h)
    (fun _ _ _ h => .inl (trStateStoredAt_append_other rfl h))
    (fun _ _ _ _ _ _ h => .inl ((eventLogged_append_other_iff rfl).mp h))
    (fun p' st' idx h => by
      rcases pqxdhStoredAt_append_same h with ⟨_, h₀⟩ | ⟨_, rfl, rfl⟩
      · exact .inl h₀
      · exact .inr (hsk.mono_append_other rfl rfl))
    (fun b h => .inl ((baseAttackerKnows_append_pqSt tr p st b).mp h))

namespace CompDhsHelpers

/-- Trace specification for `logSkippedKeys`: records only `SkippedKeyStored` events whose seeds
are chain-key steps from `ck_base`, without storing any `TRState`. -/
structure LogSkippedSpec (s : SessionInfo) (pk : Bytes) (rIdx origIdx : Nat)
    (ck_base : Bytes) (k : Nat) (tr tr' : ExecTrace) : Prop where
  le : tr ≤ tr'
  len : tr'.length = tr.length + k
  stateStored : ∀ p st j, StateStoredAt p st j tr' → StateStoredAt p st j tr
  eventLogged : ∀ ev : TREvent, tr'.EventLogged ev →
    tr.EventLogged ev ∨
    ∃ n' seed', ev = TREvent.SkippedKeyStored s pk n' seed' rIdx origIdx ∧
      ∃ d, seed' = (kdfCk (chainKeyAt ck_base d)).2

theorem logSkippedKeys_spec (s : SessionInfo) (pk : Bytes)
    (rIdx origIdx : Nat) (ck_base : Bytes) :
    ∀ (ck : Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace),
      (∃ d, ck = chainKeyAt ck_base d) →
      ((logSkippedKeys s pk rIdx origIdx ck n k).run tr).1 = some () ∧
      LogSkippedSpec s pk rIdx origIdx ck_base k tr
        (((logSkippedKeys s pk rIdx origIdx ck n k).run tr).2.val)
  | _, _, 0, tr, _ => by
    rw [logSkippedKeys, DY.Traceful.run_pure]
    exact ⟨rfl, Trace.le_refl tr, (Nat.add_zero tr.length).symm,
      fun _ _ _ h => h, fun _ h => .inl h⟩
  | ck, n, k + 1, tr, ⟨d, hck⟩ => by
    let ev₀ := TREvent.SkippedKeyStored s pk n (kdfCk ck).2 rIdx origIdx
    let tr₁ := tr.append (TREvE ev₀)
    rw [logSkippedKeys, run_bind_fst, run_bind_snd]
    have hlog1 : ((ProtocolEvent.logEvent ev₀).run tr).1 = some () := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, run_bind_fst, DY.Traceful.run_pure]
      rw [DY.Traceful.run_mk]
    have hlog2 : ((ProtocolEvent.logEvent ev₀).run tr).2.val = tr₁ := by
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, run_bind_snd, DY.Traceful.run_pure]
      rw [DY.Traceful.run_mk]
    rw [hlog1, hlog2]
    dsimp only
    have hck1 : ∃ d', (kdfCk ck).1 = chainKeyAt ck_base d' :=
      ⟨d + 1, by rw [hck, chainKeyAt_succ_eq_kdfCk_fst]⟩
    obtain ⟨hfst, hle1, hlen1, hst1, hev1⟩ :=
      logSkippedKeys_spec s pk rIdx origIdx ck_base (kdfCk ck).1 (n + 1) k tr₁ hck1
    refine ⟨hfst, Trace.le_trans _ _ _ (Trace.append_le tr _) hle1, ?_, ?_, ?_⟩
    · have hlen_tr₁ : tr₁.length = tr.length + 1 := by
        simp [tr₁, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      rw [hlen1, hlen_tr₁]; omega
    · intro p st j hst
      exact trStateStoredAt_append_other rfl (hst1 p st j hst)
    · intro ev hev
      rcases hev1 ev hev with hev_tr₁ | hsk
      · rcases (eventLogged_append_same_iff (tr := tr) (ev₀ := ev₀) (ev := ev)).mp hev_tr₁ with
          hev_tr | rfl
        · exact .inl hev_tr
        · exact .inr ⟨n, (kdfCk ck).2, rfl, d, by rw [hck]⟩
      · exact .inr hsk

theorem findRecvChain_some {recv : List RecvChain} {pk : Bytes} {c : RecvChain}
    (h : findRecvChain recv pk = some c) : c ∈ recv ∧ c.ratchetKey = pk :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem receiveSignalMsg_trace (msgH : Nat) (tr : ExecTrace) :
    ((receiveSignalMsg msgH).run tr).2.val = tr :=
  Preserves.receiveSignalMsg (Inv := fun t => t = tr) msgH tr rfl

theorem run_bind_receiveMessage {Inv : ExecTrace → Prop} {α : Type}
    (idx : Nat) {f : Bytes → Traceful α} (tr : ExecTrace)
    (hInv : Inv tr) (hf : ∀ msg, Inv ((f msg).run tr).2.val) :
    Inv ((Network.receiveMessage idx >>= f).run tr).2.val := by
  rw [run_bind_snd, receiveMessage_snd]
  rcases ((Network.receiveMessage idx).run tr).1 with _ | msg
  · exact hInv
  · exact hf msg

theorem run_bind_verifyMacAndDecrypt {Inv : ExecTrace → Prop} {α : Type}
    (st : TRState) (msg : TRSignalMsg) (pqSalt seed : Bytes) {f : Bytes → Traceful α} (tr : ExecTrace)
    (hInv : Inv tr) (hf : ∀ m, Inv ((f m).run tr).2.val) :
    Inv ((verifyMacAndDecrypt st msg pqSalt seed >>= f).run tr).2.val := by
  rw [run_bind_snd, verifyMacAndDecrypt_trace]
  rcases ((verifyMacAndDecrypt st msg pqSalt seed).run tr).1 with _ | m
  · exact hInv
  · exact hf m

theorem guardTrace_snd (p : ExecTrace → Bool) (tr : ExecTrace) :
    ((guardTrace p).run tr).2.val = tr := by
  unfold guardTrace
  rw [DY.Traceful.run_mk]

theorem run_bind_guardTrace {Inv : ExecTrace → Prop} {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α} (tr : ExecTrace)
    (hInv : Inv tr) (hf : Inv ((f ()).run tr).2.val) :
    Inv ((guardTrace p >>= f).run tr).2.val := by
  rw [run_bind_snd, guardTrace_snd]
  rcases ((guardTrace p).run tr).1 with _ | ⟨⟩
  · exact hInv
  · exact hf

theorem guardOnTrace_snd (p : ExecTrace → Bool) (tr : ExecTrace) :
    ((DY.Libsignal.PQXDH.guardTrace p).run tr).2.val = tr := by
  unfold DY.Libsignal.PQXDH.guardTrace
  rw [DY.Traceful.run_mk]

theorem run_bind_guardOnTrace {Inv : ExecTrace → Prop} {α : Type}
    (p : ExecTrace → Bool) {f : Unit → Traceful α} (tr : ExecTrace)
    (hInv : Inv tr) (hf : Inv ((f ()).run tr).2.val) :
    Inv ((DY.Libsignal.PQXDH.guardTrace p >>= f).run tr).2.val := by
  rw [run_bind_snd, guardOnTrace_snd]
  rcases ((DY.Libsignal.PQXDH.guardTrace p).run tr).1 with _ | ⟨⟩
  · exact hInv
  · exact hf

theorem run_bind_genRand {Inv : ExecTrace → Prop} {α : Type}
    (sz : Nat) {f : Bytes → Traceful α} (tr : ExecTrace)
    (hf : Inv ((f (mkRand tr.length sz)).run (tr.append (RndE sz))).2.val) :
    Inv ((Random.genRand sz >>= f).run tr).2.val := by
  rw [run_genRand_bind_snd]
  exact hf

theorem run_bind_sendMessage {Inv : ExecTrace → Prop} {α : Type}
    (key : Bytes) {f : Nat → Traceful α} (tr : ExecTrace)
    (hf : Inv ((f tr.length).run (tr.append (NetE key))).2.val) :
    Inv ((Network.sendMessage key >>= f).run tr).2.val := by
  simp only [run_bind_snd,
    Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [DY.Traceful.run_mk]
  exact hf

theorem bind_getEntry_tr_eq {Inv : ExecTrace → Prop} {α : Type}
    (idx : Nat) {f : TREntry → Traceful α} (tr : ExecTrace) (hInv : Inv tr)
    (hf : ∀ ev, tr.EventLogged ev → Inv (((f ⟨ev⟩).run tr).2.val)) :
    Inv (((DY.getEntry idx >>= f).run tr).2.val) := by
  rw [run_bind_snd, Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]; dsimp only
  rcases he : (tr.at? idx : Option TREntry) with _ | ⟨ev⟩
  · exact hInv
  · exact hf ev.ev ⟨idx, by rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]; exact he⟩

theorem bind_ensureReceiverChain_empty {Inv : ExecTrace → Prop} {α : Type}
    (st₀ : TRState) (pk : Bytes) (tr₀ : ExecTrace)
    (hrecv : st₀.recv = []) (hns : st₀.ns = 0) (hrIdx : st₀.rIdx = 0) (hInv₀ : Inv tr₀)
    {f : TRState × RecvChain × Bool → Traceful α}
    (hf :
      let dhs' := mkRand tr₀.length 32
      let rk1 := (createChain st₀.rk pk st₀.dhs).1
      let ckr := (createChain st₀.rk pk st₀.dhs).2
      let rk2 := (createChain rk1 pk dhs').1
      let cks := (createChain rk1 pk dhs').2
      let c : RecvChain := { ratchetKey := pk, chainKey := ckr, index := 0, rIdx := 2 }
      let st : TRState := { st₀ with rk := rk2, dhs := dhs', cks := cks, ns := 0, pn := 0,
                                     rIdx := 2, recv := [c] }
      Inv (((f (st, c, true)).run (tr₀.append (RndE 32))).2.val)) :
    Inv (((ensureReceiverChain st₀ pk >>= f).run tr₀).2.val) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold recvChainFor; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  have hfind : findRecvChain st₀.recv pk = none := by rw [hrecv]; rfl
  rw [hfind]; dsimp only
  by_cases hlo : x25519LowOrder pk = true
  · rw [ite_eq_left_iff.mpr fun h => absurd hlo h, run_bind_snd]
    simp [DY.Traceful.run_failure, hInv₀]
  · rw [ite_eq_right_iff.mpr fun h => absurd h hlo]; dsimp only; unfold _root_.guard
    have hlo' : (!x25519LowOrder pk) = true := by cases h : x25519LowOrder pk <;> simp_all
    rw [ite_eq_left_iff.mpr fun h => absurd hlo' h]
    simp only [run_bind_assoc_snd, run_pure_bind_snd, run_genRand_bind_snd]
    dsimp only at hf ⊢
    rw [hrecv, hns, hrIdx]
    exact hf

end CompDhsHelpers

end Symbolic.Swarm.COMPOSED.CompRatchet
