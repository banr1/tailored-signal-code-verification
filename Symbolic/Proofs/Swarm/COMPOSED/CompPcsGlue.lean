/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.COMPOSED.CompPcsClosed
public import Symbolic.Proofs.Swarm.COMPOSED.CompPcsEngine
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
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.COMPOSED.CompDhsOrigin
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
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
# Composed PCS Witness Closure and Engine Bridges

Defines the witness-based exposure set `CompPcsWitnessExposure` and tight closure
`CompTightClosedW`, proves honest DH-share compromise inversion under witness exposure, and
instantiates `CompPcsEngine.PcsKdfClosureInv` and `CompPcsEngine.PcsWitnessClosureInv` for
`CompTrClosed`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse
open DY.Literal DY.Concat DY.DiffieHellman DY.KdfExtract DY.SymEnc DY.Trunc
open DY.X25519 DY.PQKem DY.Signature DY.Spqr DY.TrWire
open DY.Libsignal.TripleRatchet (SessionInfo createChain kdfCk)
open DY.Libsignal.PQXDH (PQXDHEvent pqxdhKdf)
open DY.Libsignal.TripleRatchet (TREvent TRSignalMsg parseTrSignalMsg)
open DY.Libsignal.TripleRatchet.Cheval (StateStoredAt)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTermAlgebra

/-! ## `MsgEncWitnessAt` and Honest DH-Share Compromise Inversion -/

private theorem baseAttackerKnows_mono_pcs {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes}
    (hb : tr.BaseAttackerKnows b) : tr'.BaseAttackerKnows b := by
  induction hle with
  | equal => exact hb
  | extend _ _ _ ih =>
    rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_2]
    exact .inr ih

private theorem attackerKnows_mono_pcs {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes}
    (hk : b.AttackerKnows tr) : b.AttackerKnows tr' := by
  refine Bytes.AttackerKnows.is_least_fixpoint (fun x => x.AttackerKnows tr') b tr
    (fun x hx => Bytes.AttackerKnows.prove AttackerKnowledge.attackerKnowledge x tr' hx)
    (fun x hx => ?_) hk
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
  exact Bytes.AttackerKnows.prove_from_base x tr' (baseAttackerKnows_mono_pcs hle hx)

/-- Monotone witness that `r` was stored as SPQR send coins in a `TRState` or sent as a
`SymEnc.symEnc` plaintext inside a `TrWireMsg` on `tr` (`messageEncrypt`). -/
def MsgEncWitnessAt (tr : ExecTrace) (r : Bytes) : Prop :=
  (∃ me st idx s, StateStoredAt me st idx tr ∧ st.spqr = (Spqr.spqrSend s r).1) ∨
  (∃ v rk c pc k iv pq ev mac,
    tr.BaseAttackerKnows (Concat.concat
      (TrWire.trWireMsg v rk c pc (SymEnc.symEnc k iv r) pq ev) mac))

theorem MsgEncWitnessAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {r : Bytes}
    (h : MsgEncWitnessAt tr r) : MsgEncWitnessAt tr' r := by
  rcases h with ⟨me, st, idx, s, hst, hspqr⟩ | ⟨v, rk, c, pc, k, iv, pq, ev, mac, hbase⟩
  · exact .inl ⟨me, st, idx, s, CompTrace.trStateStoredAt_mono hle hst, hspqr⟩
  · exact .inr ⟨v, rk, c, pc, k, iv, pq, ev, mac, baseAttackerKnows_mono_pcs hle hbase⟩

theorem msgEncWitnessAt_implies_compPcsClosed {tr : ExecTrace} (hInv : CompDhsOriginInv tr)
    {r : Bytes} (hw : MsgEncWitnessAt tr r) : CompPcsClosed tr r := by
  rcases hw with ⟨me, st, idx, s, hst, hspqr⟩ | ⟨v, rk, c, pc, k, iv, pq, ev, mac, hbase⟩
  · have hspqr_c : CompPcsClosed tr st.spqr := (hInv.trSt_ok me st idx hst).2.2.2.2
    rw [hspqr] at hspqr_c
    exact (CompPcsClosed.inv_spqrSendState hspqr_c).2
  · have hcat_c : CompPcsClosed tr _ := hInv.base_ok _ hbase
    have hwire_c := (CompPcsClosed.inv_concat hcat_c).1
    have hct_c := (CompPcsClosed.inv_trWireMsg hwire_c).2.1
    exact CompPcsClosed.inv_symEnc hct_c

theorem honestDH_implies_isCompDhsOf {tr : ExecTrace} {d : Bytes}
    (hdh : CompPcsEngine.IsHonestDH tr d) :
    ∃ s rIdx, IsCompDhsOf tr d s rIdx := by
  rcases hdh with ⟨s, i, hev⟩ | ⟨me, st, idx, hst, hdhs⟩
  · exact ⟨s, i + 2, .inr (.inl ⟨i, hev, rfl⟩)⟩
  · exact ⟨st.sessionInfo me, st.rIdx, .inl ⟨st, idx, hst, rfl, hdhs, rfl⟩⟩

theorem honestDH_rand_of_reachable {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability)
    (d : Bytes) (hdh : CompPcsEngine.IsHonestDH tr d) :
    ∃ ts, d = mkRand ts 32 := by
  obtain ⟨s, rIdx, hdhs⟩ := honestDH_implies_isCompDhsOf hdh
  obtain ⟨t, _, hdhs_eq⟩ := (compDhsOriginInv_reachable hreach).dhs_rand d s rIdx hdhs
  exact ⟨t, hdhs_eq⟩

theorem exposedDHs_rand_of_reachable {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability)
    (s : SessionInfo) (d : Bytes) (i : Nat)
    (hev : tr.EventLogged (TREvent.ExposedDHs s d i)) :
    ∃ ts, d = mkRand ts 32 := by
  obtain ⟨t, _, hdhs_eq⟩ := (compDhsOriginInv_reachable hreach).dhs_rand d s i (.inr (.inr hev))
  exact ⟨t, hdhs_eq⟩

/-- On any reachable composed trace, if `IsCompDhsOf tr dhs s rIdx` holds and `dhs` satisfies
`dhs.AttackerKnows tr ∨ MsgEncWitnessAt tr dhs`, then `TREvent.ExposedDHs s dhs rIdx` or
`PQXDHEvent.BrokenDH` was logged on `tr`. -/
theorem dhs_exposed_or_brokenDH_of_knows_or_witness {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability)
    {s : SessionInfo} {dhs : Bytes} {rIdx : Nat}
    (hdhs : IsCompDhsOf tr dhs s rIdx)
    (hk : dhs.AttackerKnows tr ∨ MsgEncWitnessAt tr dhs) :
    tr.EventLogged (TREvent.ExposedDHs s dhs rIdx) ∨ tr.EventLogged PQXDHEvent.BrokenDH := by
  have hInv := compDhsOriginInv_reachable hreach
  obtain ⟨t, _, rfl⟩ := hInv.dhs_rand dhs s rIdx hdhs
  have hclosed : CompPcsClosed tr (mkRand t 32) := by
    rcases hk with hkn | hw
    · exact CompPcsClosed.of_attackerKnows hInv.base_ok hkn
    · exact msgEncWitnessAt_implies_compPcsClosed hInv hw
  rcases CompPcsClosed.inv_rnd hclosed with ⟨_, hnot | ⟨s', r', hexp⟩ | hbrk⟩ | hbrk
  · exact False.elim (hnot s rIdx hdhs)
  · obtain ⟨rfl, rfl⟩ := hInv.dhs_unique _ s' r' s rIdx (.inr (.inr hexp)) hdhs
    exact .inl hexp
  · exact .inr hbrk
  · exact .inr hbrk

/-- On any reachable composed trace, if `CompPcsEngine.IsHonestDH tr d` holds and `d` satisfies
`d.AttackerKnows tr ∨ MsgEncWitnessAt tr d`, then `ExposedDHs` or `BrokenDH` was logged. -/
theorem honestDH_exposed_or_brokenDH_of_knows_or_witness {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability)
    {d : Bytes} (hdh : CompPcsEngine.IsHonestDH tr d)
    (hk : d.AttackerKnows tr ∨ MsgEncWitnessAt tr d) :
    (∃ s i, tr.EventLogged (TREvent.ExposedDHs s d i)) ∨ tr.EventLogged PQXDHEvent.BrokenDH := by
  obtain ⟨s, rIdx, hdhs⟩ := honestDH_implies_isCompDhsOf hdh
  exact (dhs_exposed_or_brokenDH_of_knows_or_witness hreach hdhs hk).imp
    (fun hexp => ⟨s, rIdx, hexp⟩) id

/-! ## `CompPcsWitnessExposure` and `CompTightClosedW` -/

private theorem isScheduleKey_exists_kdfExtract {k : Bytes}
    (h : CompPcsEngine.IsScheduleKey k) : ∃ s m, k = kdfExtract s m := by
  rcases h with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    exact ⟨_, _, rfl⟩

/-- Witness-based structured exposure set replacing `MsgEncRandAt` with `MsgEncWitnessAt`. -/
inductive CompPcsWitnessExposure (tr : ExecTrace) : Bytes → Prop
  | rand {ts sz : Nat} :
      (mkRand ts sz).AttackerKnows tr ∨ MsgEncWitnessAt tr (mkRand ts sz) →
      CompPcsWitnessExposure tr (mkRand ts sz)
  | pqr {ikm : Bytes} :
      CompPcsWitnessExposure tr (pqxdhKdf ikm).pqr
  | exposedRK {s : SessionInfo} {rk : Bytes} {rIdx : Nat} :
      (∃ r p sk, rk = (createChain r p sk).1) →
      tr.EventLogged (TREvent.ExposedRK s rk rIdx) →
      CompPcsWitnessExposure tr rk
  | exposedCKs {s : SessionInfo} {cks : Bytes} {n : UInt32} {rIdx : Nat} :
      CompPcsEngine.IsScheduleKey cks →
      tr.EventLogged (TREvent.ExposedCKs s cks n rIdx) →
      CompPcsWitnessExposure tr cks
  | exposedCKr {s : SessionInfo} {ckr : Bytes} {n : UInt32} {rIdx : Nat} :
      CompPcsEngine.IsScheduleKey ckr →
      tr.EventLogged (TREvent.ExposedCKr s ckr n rIdx) →
      CompPcsWitnessExposure tr ckr
  | exposedMK {s : SessionInfo} {seed : Bytes} {n : UInt32} {rIdx : Nat} :
      (∃ c, seed = (kdfCk c).2) →
      tr.EventLogged (TREvent.ExposedMK s seed n rIdx) →
      CompPcsWitnessExposure tr seed

theorem isAtomic_compPcsWitnessExposure (tr : ExecTrace) :
    IsAtomicExposure (CompPcsWitnessExposure tr) := by
  intro b hb
  rcases hb with ⟨_⟩ | _ | ⟨⟨r, p, sk, rfl⟩, _⟩ | ⟨hsk, _⟩ | ⟨hsk, _⟩ | ⟨⟨c, rfl⟩, _⟩
  · exact isAtomic_mkRand _ _
  · exact isAtomic_kdfExtract _ _
  · exact isAtomic_kdfExtract _ _
  · obtain ⟨s, m, rfl⟩ := isScheduleKey_exists_kdfExtract hsk; exact isAtomic_kdfExtract s m
  · obtain ⟨s, m, rfl⟩ := isScheduleKey_exists_kdfExtract hsk; exact isAtomic_kdfExtract s m
  · exact isAtomic_kdfExtract _ _

theorem CompPcsWitnessExposure.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes}
    (h : CompPcsWitnessExposure tr b) : CompPcsWitnessExposure tr' b := by
  cases h with
  | rand hr =>
    exact .rand (hr.imp (attackerKnows_mono_pcs hle) (MsgEncWitnessAt.mono hle))
  | pqr => exact .pqr
  | exposedRK hshape hev => exact .exposedRK hshape (CompTrace.eventLogged_mono hle hev)
  | exposedCKs hsk hev => exact .exposedCKs hsk (CompTrace.eventLogged_mono hle hev)
  | exposedCKr hsk hev => exact .exposedCKr hsk (CompTrace.eventLogged_mono hle hev)
  | exposedMK hseed hev => exact .exposedMK hseed (CompTrace.eventLogged_mono hle hev)

theorem CompPcsWitnessExposure.exists_mkRand_or_kdfExtract {tr : ExecTrace} {b : Bytes}
    (h : CompPcsWitnessExposure tr b) :
    (∃ ts sz, b = mkRand ts sz) ∨ (∃ s m, b = kdfExtract s m) := by
  rcases h with ⟨_⟩ | _ | ⟨⟨r, p, sk, rfl⟩, _⟩ | ⟨hsk, _⟩ | ⟨hsk, _⟩ | ⟨⟨c, rfl⟩, _⟩
  · exact .inl ⟨_, _, rfl⟩
  · exact .inr ⟨_, _, rfl⟩
  · exact .inr ⟨_, _, rfl⟩
  · exact .inr (isScheduleKey_exists_kdfExtract hsk)
  · exact .inr (isScheduleKey_exists_kdfExtract hsk)
  · exact .inr ⟨_, _, rfl⟩

/-- On any reachable trace `tr`, `CompPcsWitnessExposure tr` embeds into
`CompPcsEngine.CompPcsWitnessExposureFor (MsgEncWitnessAt tr) tr` using `CompDhsOriginInv`. -/
theorem CompPcsWitnessExposure.to_engineExposure {tr : ExecTrace}
    (hreach : tr.Reachable DY.Libsignal.Composed.reachability) {b : Bytes}
    (hexp : CompPcsWitnessExposure tr b) :
    CompPcsEngine.CompPcsWitnessExposureFor (MsgEncWitnessAt tr) tr b := by
  cases hexp with
  | rand hr =>
    exact .rand hr (fun hhon => honestDH_exposed_or_brokenDH_of_knows_or_witness hreach hhon hr)
  | pqr => exact .pqr
  | exposedRK hrk hev => exact .exposedRK hrk hev
  | exposedCKs hsk hev => exact .exposedCKs hsk hev
  | exposedCKr hsk hev => exact .exposedCKr hsk hev
  | exposedMK hm hev => exact .exposedMK hm hev

/-- Tight witness-exposure closure with invertible `dhPk` and `kemPk` constructors for
`invertDH` / `invertKEM` preservation across all 23 composed transitions. -/
inductive CompTightClosedW (tr : ExecTrace) : Bytes → Prop where
  | exposed {b : Bytes} (h : CompPcsWitnessExposure tr b) : CompTightClosedW tr b
  | literal (bs : ByteArray) : CompTightClosedW tr (literalToBytes bs)
  | dhPkRand {sk : Bytes} (h : ∃ ts sz, sk = mkRand ts sz) :
      CompTightClosedW tr (DiffieHellman.dhPk sk)
  | dhPkClosed {sk : Bytes} (h : CompTightClosedW tr sk) :
      CompTightClosedW tr (DiffieHellman.dhPk sk)
  | dhSk (sk pk : Bytes) (h : CompTightClosedW tr sk) :
      CompTightClosedW tr (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack)
  | dhPeer (sk s : Bytes) (h : CompTightClosedW tr s) :
      CompTightClosedW tr (({ sk := sk, pk := DiffieHellman.dhPk s } : DiffieHellman.Dh.SubF Bytes).pack)
  | kemPkRand {sk : Bytes} (h : ∃ ts sz, sk = mkRand ts sz) :
      CompTightClosedW tr (PQKem.kemPk sk)
  | kemPkClosed {sk : Bytes} (h : CompTightClosedW tr sk) :
      CompTightClosedW tr (PQKem.kemPk sk)
  | kemEncap (pk e : Bytes) : CompTightClosedW tr (PQKem.kemEncap pk e).1
  | kemSs (pk e : Bytes) (hpk : CompTightClosedW tr pk) (he : CompTightClosedW tr e) :
      CompTightClosedW tr (PQKem.kemEncap pk e).2
  | kemSsKey (sk e : Bytes) (hsk : CompTightClosedW tr sk) :
      CompTightClosedW tr (PQKem.kemEncap (PQKem.kemPk sk) e).2
  | kemRejKey {sk ct : Bytes} (hsk : CompTightClosedW tr sk) (hct : CompTightClosedW tr ct) :
      CompTightClosedW tr (({ sk := sk, cipher := ct } : PQKem.RejKey.SubF Bytes).pack)
  | vk (sk : Bytes) : CompTightClosedW tr (Signature.vk sk)
  | sign (sk nonce msg : Bytes) : CompTightClosedW tr (Signature.sign sk nonce msg)
  | trunc8 (m : Bytes) : CompTightClosedW tr (Trunc.trunc8 m)
  | kdf {salt ikm : Bytes} (hsalt : CompTightClosedW tr salt) (hikm : CompTightClosedW tr ikm) :
      CompTightClosedW tr (kdfExtract salt ikm)
  | concat {lhs rhs : Bytes} (hlhs : CompTightClosedW tr lhs) (hrhs : CompTightClosedW tr rhs) :
      CompTightClosedW tr (Concat.concat lhs rhs)
  | symEnc {k iv msg : Bytes} (hmsg : CompTightClosedW tr msg) :
      CompTightClosedW tr (SymEnc.symEnc k iv msg)
  | variant {key : Bytes} (v : Fin 4) {t : Fin 8} (hkey : CompTightClosedW tr key) :
      CompTightClosedW tr (({ key := key, variation := v, torsion := t } : X25519.Variant.SubF Bytes).pack)
  | trWireMsg {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes}
      {ev : TrWire.EncodingVariation}
      (hrk : CompTightClosedW tr rk) (hct : CompTightClosedW tr ct) (hpq : CompTightClosedW tr pq) :
      CompTightClosedW tr (TrWire.trWireMsg v rk c pc ct pq ev)
  | spqrInit {authKey params : Bytes}
      (hauth : CompTightClosedW tr authKey) (hparams : CompTightClosedW tr params) :
      CompTightClosedW tr (Spqr.spqrInit authKey params)
  | spqrChainKey (authKey params idx : Bytes) :
      CompTightClosedW tr (Spqr.spqrChainKey authKey params idx)
  | spqrSendState {st coins : Bytes}
      (hst : CompTightClosedW tr st) (hcoins : CompTightClosedW tr coins) :
      CompTightClosedW tr (({ st := st, coins := coins } : Spqr.SendState.SubF Bytes).pack)
  | spqrSendKey (st coins : Bytes) :
      CompTightClosedW tr (({ st := st, coins := coins } : Spqr.SendKey.SubF Bytes).pack)
  | spqrSendMsg (st coins : Bytes) :
      CompTightClosedW tr (({ st := st, coins := coins } : Spqr.SendMsg.SubF Bytes).pack)
  | spqrRecvState {st msg : Bytes}
      (hst : CompTightClosedW tr st) (hmsg : CompTightClosedW tr msg) :
      CompTightClosedW tr (({ st := st, msg := msg } : Spqr.RecvState.SubF Bytes).pack)
  | spqrRecvKey (st msg : Bytes) :
      CompTightClosedW tr (({ st := st, msg := msg } : Spqr.RecvKey.SubF Bytes).pack)

theorem CompTightClosedW.dhPk {tr : ExecTrace} {sk : Bytes}
    (h : (∃ ts sz, sk = mkRand ts sz) ∨ CompTightClosedW tr sk) :
    CompTightClosedW tr (DiffieHellman.dhPk sk) :=
  h.elim .dhPkRand .dhPkClosed

theorem CompTightClosedW.kemPk {tr : ExecTrace} {sk : Bytes}
    (h : (∃ ts sz, sk = mkRand ts sz) ∨ CompTightClosedW tr sk) :
    CompTightClosedW tr (PQKem.kemPk sk) :=
  h.elim .kemPkRand .kemPkClosed

theorem CompTightClosedW.to_compTrClosed {tr : ExecTrace} {b : Bytes}
    (h : CompTightClosedW tr b) : CompTrClosed (CompPcsWitnessExposure tr) b := by
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
  | trWireMsg _ _ _ ih1 ih2 ih3 => exact .trWireMsg ih1 ih2 ih3
  | spqrInit _ _ ih1 ih2 => exact .spqrInit ih1 ih2
  | spqrChainKey authKey params idx => exact .spqrChainKey authKey params idx
  | spqrSendState _ _ ih1 ih2 => exact .spqrSendState ih1 ih2
  | spqrSendKey st coins => exact .spqrSendKey st coins
  | spqrSendMsg st coins => exact .spqrSendMsg st coins
  | spqrRecvState _ _ ih1 ih2 => exact .spqrRecvState ih1 ih2
  | spqrRecvKey st msg => exact .spqrRecvKey st msg

theorem CompTightClosedW.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes}
    (h : CompTightClosedW tr b) : CompTightClosedW tr' b := by
  induction h with
  | exposed h => exact .exposed (CompPcsWitnessExposure.mono hle h)
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
  | trWireMsg _ _ _ ih1 ih2 ih3 => exact .trWireMsg ih1 ih2 ih3
  | spqrInit _ _ ih1 ih2 => exact .spqrInit ih1 ih2
  | spqrChainKey authKey params idx => exact .spqrChainKey authKey params idx
  | spqrSendState _ _ ih1 ih2 => exact .spqrSendState ih1 ih2
  | spqrSendKey st coins => exact .spqrSendKey st coins
  | spqrSendMsg st coins => exact .spqrSendMsg st coins
  | spqrRecvState _ _ ih1 ih2 => exact .spqrRecvState ih1 ih2
  | spqrRecvKey st msg => exact .spqrRecvKey st msg

theorem CompTightClosedW.dh {tr : ExecTrace} {pk sk : Bytes} (hsk : CompTightClosedW tr sk) :
    CompTightClosedW tr (DiffieHellman.dh pk sk) := by
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 _
    split
    · exact .dhSk sk (DiffieHellman.dhPk sk2) hsk
    · exact .dhPeer sk2 sk hsk
  · exact .dhSk sk pk hsk

section TightWInversions
unseal Bytes

theorem CompTightClosedW.inv_dhPk {tr : ExecTrace} {sk : Bytes}
    (h : CompTightClosedW tr (DiffieHellman.dhPk sk)) :
    (∃ ts sz, sk = mkRand ts sz) ∨ CompTightClosedW tr sk := by
  generalize hq : DiffieHellman.dhPk sk = q at h
  cases h with
  | exposed hexp =>
    rcases hexp.exists_mkRand_or_kdfExtract with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      · dsimp [DiffieHellman.dhPk, mkRand, kdfExtract] at hq
        exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | dhPkRand hsk => obtain rfl := dhPk_inj hq; exact .inl hsk
  | dhPkClosed hsk => obtain rfl := dhPk_inj hq; exact .inr hsk
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosedW.inv_kemPk {tr : ExecTrace} {sk : Bytes}
    (h : CompTightClosedW tr (PQKem.kemPk sk)) :
    (∃ ts sz, sk = mkRand ts sz) ∨ CompTightClosedW tr sk := by
  generalize hq : PQKem.kemPk sk = q at h
  cases h with
  | exposed hexp =>
    rcases hexp.exists_mkRand_or_kdfExtract with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      · dsimp [PQKem.kemPk, mkRand, kdfExtract] at hq
        exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | kemPkRand hsk => obtain rfl := kemPk_inj hq; exact .inl hsk
  | kemPkClosed hsk => obtain rfl := kemPk_inj hq; exact .inr hsk
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosedW.inv_concat {tr : ExecTrace} {lhs rhs : Bytes}
    (h : CompTightClosedW tr (Concat.concat lhs rhs)) :
    CompTightClosedW tr lhs ∧ CompTightClosedW tr rhs := by
  generalize hq : Concat.concat lhs rhs = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compPcsWitnessExposure tr _ hexp).1
    rw [← hq] at hnone; dsimp [Concat.concat] at hnone; rw [BytesView.view_pack] at hnone; cases hnone
  | concat hlhs hrhs => obtain ⟨rfl, rfl⟩ := concat_inj hq; exact ⟨hlhs, hrhs⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosedW.inv_trWireMsg {tr : ExecTrace}
    {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes} {ev : TrWire.EncodingVariation}
    (h : CompTightClosedW tr (TrWire.trWireMsg v rk c pc ct pq ev)) :
    CompTightClosedW tr rk ∧ CompTightClosedW tr ct ∧ CompTightClosedW tr pq := by
  generalize hq : TrWire.trWireMsg v rk c pc ct pq ev = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compPcsWitnessExposure tr _ hexp).2.2.2.1
    rw [← hq] at hnone; dsimp [TrWire.trWireMsg] at hnone; rw [BytesView.view_pack] at hnone; cases hnone
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

theorem CompTightClosedW.inv_symEnc {tr : ExecTrace} {k iv msg : Bytes}
    (h : CompTightClosedW tr (SymEnc.symEnc k iv msg)) : CompTightClosedW tr msg := by
  generalize hq : SymEnc.symEnc k iv msg = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compPcsWitnessExposure tr _ hexp).2.1
    rw [← hq] at hnone; dsimp [SymEnc.symEnc] at hnone; rw [BytesView.view_pack] at hnone; cases hnone
  | symEnc hmsg =>
    have hv := congrArg (fun b : Bytes => b.view? SymEnc.Enc.SubF) hq
    simp only [SymEnc.symEnc, SymEnc.CanSymEnc.symEnc, BytesView.view_pack,
      Option.some.injEq, SymEnc.Enc.SubF.mk.injEq] at hv
    obtain ⟨_, _, rfl⟩ := hv; exact hmsg
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosedW.inv_variant {tr : ExecTrace} {x : X25519.Variant.SubF Bytes}
    (h : CompTightClosedW tr x.pack) : CompTightClosedW tr x.key := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compPcsWitnessExposure tr _ hexp).2.2.1
    rw [← hq, BytesView.view_pack] at hnone; cases hnone
  | variant v hkey =>
    have hv := congrArg (fun b : Bytes => b.view? X25519.Variant.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact hkey
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosedW.inv_spqrInit {tr : ExecTrace} {x : Spqr.InitState.SubF Bytes}
    (h : CompTightClosedW tr x.pack) :
    CompTightClosedW tr x.authKey ∧ CompTightClosedW tr x.params := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compPcsWitnessExposure tr _ hexp).2.2.2.2.1
    rw [← hq, BytesView.view_pack] at hnone; cases hnone
  | spqrInit hauth hparams =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.InitState.SubF) hq
    simp only [Spqr.spqrInit, BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact ⟨hauth, hparams⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosedW.inv_spqrSendState {tr : ExecTrace} {x : Spqr.SendState.SubF Bytes}
    (h : CompTightClosedW tr x.pack) :
    CompTightClosedW tr x.st ∧ CompTightClosedW tr x.coins := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compPcsWitnessExposure tr _ hexp).2.2.2.2.2.1
    rw [← hq, BytesView.view_pack] at hnone; cases hnone
  | spqrSendState hst hcoins =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.SendState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact ⟨hst, hcoins⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTightClosedW.inv_spqrRecvState {tr : ExecTrace} {x : Spqr.RecvState.SubF Bytes}
    (h : CompTightClosedW tr x.pack) :
    CompTightClosedW tr x.st ∧ CompTightClosedW tr x.msg := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (isAtomic_compPcsWitnessExposure tr _ hexp).2.2.2.2.2.2
    rw [← hq, BytesView.view_pack] at hnone; cases hnone
  | spqrRecvState hst hmsg =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.RecvState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact ⟨hst, hmsg⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

end TightWInversions

theorem CompTightClosedW.normalizeX25519Key {tr : ExecTrace} {pk : Bytes} (h : CompTightClosedW tr pk) :
    CompTightClosedW tr (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key
  have hp := Bytes.pack_view? X25519.Variant.SubF pk
  cases hv : pk.view? X25519.Variant.SubF with
  | none => exact h
  | some x => rw [hv] at hp; rw [← hp] at h; exact CompTightClosedW.inv_variant h

theorem CompTightClosedW.x25519TorsionVariant {tr : ExecTrace} {key : Bytes} (v : Fin 4) (t : Fin 8)
    (h : CompTightClosedW tr key) : CompTightClosedW tr (X25519.x25519TorsionVariant key v t) := by
  dsimp [X25519.x25519TorsionVariant]
  split
  · exact CompTightClosedW.normalizeX25519Key h
  · exact .variant v (CompTightClosedW.normalizeX25519Key h)

theorem CompTightClosedW.spqrSendKey_of {tr : ExecTrace} (st coins : Bytes) :
    CompTightClosedW tr (Spqr.spqrSend st coins).2.1 := by
  unfold Spqr.spqrSend; dsimp only
  cases st.view? Spqr.InitState.SubF with
  | none => exact .spqrSendKey st coins
  | some x => exact .spqrChainKey x.authKey x.params (Spqr.encodeSpqrIndexTerm 1)

theorem CompTightClosedW.spqrSendMsg_of {tr : ExecTrace} (st coins : Bytes) :
    CompTightClosedW tr (Spqr.spqrSend st coins).2.2 := .spqrSendMsg st coins

theorem CompTightClosedW.spqrRecvState_of {tr : ExecTrace} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r)
    (hst : CompTightClosedW tr st) (hm : CompTightClosedW tr msg) : CompTightClosedW tr r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]
  exact .spqrRecvState hst hm

theorem CompTightClosedW.spqrRecvKey_of {tr : ExecTrace} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) : CompTightClosedW tr r.2 := by
  unfold Spqr.spqrRecv at hrecv
  split at hrecv
  · cases hrecv
  · cases hv : st.view? Spqr.InitState.SubF with
    | none =>
      rw [hv] at hrecv; injection hrecv with hrecv'; subst hrecv'; exact .spqrRecvKey st msg
    | some x =>
      rw [hv] at hrecv; rcases x with ⟨authKey, params⟩; dsimp only at hrecv
      cases hd : Spqr.spqrParamsDir? params with
      | none => rw [hd] at hrecv; cases hrecv
      | some dir =>
        rw [hd] at hrecv; injection hrecv with hrecv'; subst hrecv'; dsimp only
        split
        · exact .literal _
        · exact .spqrChainKey authKey _ (Spqr.encodeSpqrIndexTerm idx)

set_option maxHeartbeats 400000 in
theorem CompTightClosedW.attackerKnowledge_implies (tr : ExecTrace) :
    SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge (CompTightClosedW tr) := by
  change SubAttackerKnowledge.Implies
    DY.Libsignal.Composed.attackerKnowledge (CompTightClosedW tr)
  dsimp [DY.Libsignal.Composed.attackerKnowledge]
  apply SubAttackerKnowledge.combine.implies
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hlt⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
    intro b hb
    rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hb
    exact hb.elim
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Literal.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, hlt'⟩
    · intro b hb
      dsimp [Literal.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hb
      rcases hb with ⟨bs, rfl⟩; exact .literal bs
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Concat.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | n, hlt'⟩
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hb
      rcases hb with ⟨lhs, rhs, rfl, hlhs, hrhs⟩; exact .concat hlhs hrhs
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, rhs, i, hsplit, hinp⟩
      exact (CompTightClosedW.inv_concat (Concat.concat_split inp i b rhs hsplit.symm ▸ hinp)).1
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, lhs, i, hsplit, hinp⟩
      exact (CompTightClosedW.inv_concat (Concat.concat_split inp i lhs b hsplit.symm ▸ hinp)).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, hsk⟩; exact .dhPk (.inr hsk)
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, sk, rfl, _, hsk⟩; exact CompTightClosedW.dh hsk
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, KdfExtract.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, hlt'⟩
    · intro b hb
      dsimp [KdfExtract.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hb
      rcases hb with ⟨salt, ikm, rfl, hsalt, hikm⟩; exact .kdf hsalt hikm
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, SymEnc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨k', iv, msg, rfl, _, _, hmsg⟩; exact .symEnc hmsg
    · rintro b ⟨key, iv, ct, hdec, _, _, hct⟩
      dsimp [SymEnc.symDec, SymEnc.CanSymEnc.symDec] at hdec
      have hp := Bytes.pack_view? SymEnc.Enc.SubF ct
      cases hv : ct.view? SymEnc.Enc.SubF with
      | none => rw [hv] at hdec; cases hdec
      | some x =>
        rw [hv] at hdec hp; rcases x with ⟨k', iv', msg'⟩; dsimp only at hdec hp
        split at hdec
        · injection hdec with hdec'; subst hdec'; rw [← hp] at hct
          exact CompTightClosedW.inv_symEnc hct
        · cases hdec
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | n, hlt'⟩
    · rintro b ⟨m, rfl, _⟩; exact .trunc8 m
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨key, v, t, rfl, hkey⟩; exact CompTightClosedW.x25519TorsionVariant v t hkey
    · rintro b ⟨x, hpack, rfl⟩; exact CompTightClosedW.inv_variant hpack
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | n, hlt'⟩
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
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Signature.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩; exact .vk sk
    · intro b hb
      dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, nonce, msg, rfl, _, _, _⟩; exact .sign sk nonce msg
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Spqr.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨authKey, params, rfl, hauth, hparams⟩; exact .spqrInit hauth hparams
    · rintro b ⟨authKey, params, idx, rfl, _, _, _⟩; exact .spqrChainKey authKey params idx
    · rintro b ⟨st, coins, rfl, hst, hcoins⟩; exact .spqrSendState hst hcoins
    · rintro b ⟨st, coins, rfl, _, _⟩; exact CompTightClosedW.spqrSendKey_of st coins
    · rintro b ⟨st, coins, rfl, _, _⟩; exact .spqrSendMsg st coins
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, hst, hmsg⟩
      exact CompTightClosedW.spqrRecvState_of hrecv hst hmsg
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, _, _⟩
      exact CompTightClosedW.spqrRecvKey_of hrecv
    · rintro b (⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩)
      · exact (CompTightClosedW.inv_spqrInit hpack).1
      · exact (CompTightClosedW.inv_spqrInit hpack).2
      · exact (CompTightClosedW.inv_spqrSendState hpack).1
      · exact (CompTightClosedW.inv_spqrSendState hpack).2
      · exact (CompTightClosedW.inv_spqrRecvState hpack).1
      · exact (CompTightClosedW.inv_spqrRecvState hpack).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies; rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, rfl, hrk, hct, hpq⟩
      exact .trWireMsg hrk hct hpq
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, hw, hmem⟩
      obtain ⟨hrk, hct, hpq⟩ := CompTightClosedW.inv_trWireMsg hw
      rcases hmem with rfl | rfl | rfl <;> assumption
    · omega
  · omega

theorem CompTightClosedW.of_attackerKnows {tr : ExecTrace}
    (hbase : ∀ b, tr.BaseAttackerKnows b → CompTightClosedW tr b)
    {b : Bytes} (hk : b.AttackerKnows tr) : CompTightClosedW tr b := by
  refine Bytes.AttackerKnows.is_least_fixpoint (CompTightClosedW tr) b tr
    (CompTightClosedW.attackerKnowledge_implies tr) (fun x hx => ?_) hk
  simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
  exact hbase x hx

theorem CompTightClosedW.parseTrSignalMsg_pqRatchet {tr : ExecTrace}
    {t : Bytes} {msg : TRSignalMsg} (ht : CompTightClosedW tr t)
    (hp : parseTrSignalMsg t = some msg) :
    CompTightClosedW tr msg.pqRatchet := by
  unfold parseTrSignalMsg at hp
  rcases hsplit : Concat.split t (t.length - Trunc.trunc8Length) with _ | ⟨wire, mac⟩
  · rw [hsplit] at hp; cases hp
  · rw [hsplit] at hp; dsimp only [bind, Option.bind] at hp
    rcases hwf : TrWire.trWireMsgFields? wire with _ | x
    · rw [hwf] at hp; cases hp
    · rw [hwf] at hp; injection hp with hp'; subst hp'
      have hcat : Concat.concat wire mac = t :=
        Concat.concat_split t (t.length - Trunc.trunc8Length) wire mac hsplit
      obtain ⟨hwire, _⟩ := CompTightClosedW.inv_concat (hcat ▸ ht)
      have htw := TrWire.trWireMsg_of_fields? hwf
      exact (CompTightClosedW.inv_trWireMsg (htw ▸ hwire)).2.2

/-! ## `CompTrClosed` Closure Interface Instances -/

section DhPackWitnessInversion
unseal Bytes

theorem CompTrClosed.inv_dh_pack_of_nonDh {EW : Bytes → Prop}
    (hEW : ∀ sk pk, ¬ EW (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack))
    {sk pk : Bytes}
    (h : CompTrClosed EW (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack)) :
    CompTrClosed EW sk ∨ (∃ s, pk = DiffieHellman.dhPk s ∧ CompTrClosed EW s) := by
  generalize hq : (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack) = q at h
  cases h with
  | exposed hexp => exact False.elim (hEW sk pk (hq ▸ hexp))
  | dhSk sk' pk' hsk =>
    have hv := congrArg (fun b : Bytes => b.view? DiffieHellman.Dh.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv; exact .inl hsk
  | dhPeer sk' s hs =>
    have hv := congrArg (fun b : Bytes => b.view? DiffieHellman.Dh.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq, DiffieHellman.Dh.SubF.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv; exact .inr ⟨s, rfl, hs⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_dh_dhPk_of_nonDh {EW : Bytes → Prop}
    (hEW : ∀ sk pk, ¬ EW (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack))
    {a b : Bytes}
    (h : CompTrClosed EW (DiffieHellman.dh (DiffieHellman.dhPk a) b)) :
    CompTrClosed EW a ∨ CompTrClosed EW b := by
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh] at h
  split at h
  · rename_i sk2 hview
    simp only [DiffieHellman.dhPk, DiffieHellman.CanDH.dhPk, BytesView.view_pack,
      Option.some.injEq, DiffieHellman.DhPk.SubF.mk.injEq] at hview
    subst hview
    split at h
    · rcases CompTrClosed.inv_dh_pack_of_nonDh hEW h with hb | ⟨s, hs, hcs⟩
      · exact .inr hb
      · rw [dhPk_inj hs]; exact .inl hcs
    · rcases CompTrClosed.inv_dh_pack_of_nonDh hEW h with ha | ⟨s, hs, hcs⟩
      · exact .inl ha
      · rw [dhPk_inj hs]; exact .inr hcs
  · rcases CompTrClosed.inv_dh_pack_of_nonDh hEW h with hb | ⟨s, hs, hcs⟩
    · exact .inr hb
    · rw [dhPk_inj hs]; exact .inl hcs

theorem not_witnessExposureFor_dh_pack {MsgEncWitness : Bytes → Prop} {tr : ExecTrace}
    (hdhs : ∀ d, CompPcsEngine.IsHonestDH tr d → ∃ ts, d = mkRand ts 32)
    (hexpDH : ∀ s d i, tr.EventLogged (TREvent.ExposedDHs s d i) → ∃ ts, d = mkRand ts 32)
    (sk pk : Bytes) :
    ¬ CompPcsEngine.CompPcsWitnessExposureFor MsgEncWitness tr
        (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack) := by
  intro hexp
  generalize hq : (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack) = q at hexp
  cases hexp with
  | rand _ _ =>
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | exposedDHs hev =>
    obtain ⟨ts, hts⟩ := hexpDH _ _ _ hev
    rw [hts] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | brokenDH hhon _ =>
    obtain ⟨ts, hts⟩ := hdhs _ hhon
    rw [hts] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | pqr =>
    change _ = kdfExtract _ _ at hq; dsimp [kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | exposedRK hrk _ =>
    obtain ⟨_, _, _, rfl⟩ := hrk
    change _ = kdfExtract _ _ at hq; dsimp [kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | exposedCKs hsk _ | exposedCKr hsk _ =>
    obtain ⟨_, _, rfl⟩ := isScheduleKey_exists_kdfExtract hsk
    dsimp [kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)
  | exposedMK hm _ =>
    obtain ⟨_, rfl⟩ := hm
    change _ = kdfExtract _ _ at hq; dsimp [kdfExtract] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

end DhPackWitnessInversion

theorem pcsKdfClosureInv_compTrClosed (E : Bytes → Prop) :
    CompPcsEngine.PcsKdfClosureInv E (CompTrClosed E) where
  inv_trKeyKnown hc hp _ _ h := CompTrClosed.inv_trKeyKnown hc hp h
  inv_kdfCk_snd_chainKeyAt h := CompTrClosed.inv_kdfCk_snd_chainKeyAt h
  inv_kdfExtract_salt h := CompTrClosed.inv_kdfExtract_salt h

theorem pcsWitnessClosureInv_compTrClosed {EW : Bytes → Prop}
    (hEW : ∀ sk pk, ¬ EW (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack)) :
    CompPcsEngine.PcsWitnessClosureInv EW (CompTrClosed EW) where
  inv_trKeyKnown hc hp _ _ h := CompTrClosed.inv_trKeyKnown hc hp h
  inv_kdfCk_snd_chainKeyAt h := CompTrClosed.inv_kdfCk_snd_chainKeyAt h
  inv_kdfExtract h := CompTrClosed.inv_kdfExtract h
  inv_dh_dhPk _ _ h := CompTrClosed.inv_dh_dhPk_of_nonDh hEW h
  inv_mkRand h := CompTrClosed.inv_rnd h

end Symbolic.Swarm.COMPOSED.CompRatchet
