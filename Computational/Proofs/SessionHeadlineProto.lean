/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFs
public import Computational.Proofs.SessionCostedFig8
import Computational.Proofs.CryptoGames.CKA.DHProof
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PrivRedQueries
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.CryptoGames.SM.Theorem6Libsignal
import Computational.Proofs.CryptoGames.SM.Theorem8
import Computational.Proofs.SessionCostedHalt
import Computational.Proofs.SessionCostedSim
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp

/-!
# Libsignal Session Security with Prost's Codec

**Checked by Lean.** Proves `libsignal_session_sm_r1_proto`, bounding any `q`-query adversary's
advantage against `libsignalSessionScheme` with prost's codec (`protoSignalCodec`) in the restricted
ACD19 H1 game (DEV-LS1, DEV-LS2, DEV-LS3, DEV-LS4, DEV-LS5, DEV-LS6, DEV-LS7, DEV-LS22, DEV-LS27)
under SPQR-off correctness (`Corr.SpqrOffCorrect`, DEV-LS24). The bound leaves primitive and CKA
advantages uncomposed (DEV-LS30, DEV-LS31) and adds the Fig. 8 H1/authenticity and window terms
(DEV-LS12), evicted-epoch spurious steps (DEV-LS11), epoch-0 signed-pre-key injections (DEV-LS26),
and ratchet-key collisions (DEV-LS18).
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalProtoCodec
open Computational.Proofs.ReductionDsl.FsAtomicMacros (atomicShortB)

open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst Ratchet LibsignalInst
  LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme
  WireAEAD FSAEAD

/-- Tightened message, SPQR, and address length bounds matching `atomicFsOps` and `atomicFig8Ops` (`AtomicLengthsOk P ℓ → LengthsOk P ℓ`). -/
def AtomicLengthsOk {PQ PQC : Type} (P : Params PQ PQC) (ℓ : ℕ) : Prop :=
  ℓ < 10 ^ 6 ∧
    (∀ st rq st' salt msg, P.spqr.send st rq = some (st', salt, msg) → msg.length ≤ 96) ∧
    (∀ a, P.addrAB = some a → a.length ≤ 128) ∧
    (∀ a, P.addrBA = some a → a.length ≤ 128)

theorem AtomicLengthsOk.toLengthsOk {PQ PQC : Type} {P : Params PQ PQC} {ℓ : ℕ}
    (hL : AtomicLengthsOk P ℓ) : LengthsOk P ℓ := by
  have hℓ := hL.1
  refine ⟨by omega, fun st rq st' salt msg hs => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have hm := hL.2.1 st rq st' salt msg hs; omega
  · have ha' := hL.2.2.1 a ha; omega
  · have ha' := hL.2.2.2 a ha; omega

section AtomicShortSim

open LibsignalSM.Proofs.QueryBounds
open LibsignalSM.Proofs.SessionShort (SendMsgsOk)
open LibsignalSM.Proofs.SessionShort.SimAndSM (badSendMsg)

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}

private abbrev QAtomicShort (Pt : Type) (ℓ : ℕ) : (FSpec Pt ℓ).Domain → Prop :=
  fun t => badSendMsg (St := LibsignalSim.Fig8St Pt) (Coins := BitVec 256)
    (C := LibsignalSim.Fig8C Pt) (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1) t =
      true

omit [DecidableEq Pt] [Zero Pt] in
private theorem hQu_QAtomicShort : ∀ u : ℕ, ¬ QAtomicShort Pt ℓ (.inl u) := by
  intro _ h; nomatch h

omit [DecidableEq Pt] [Zero Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem atomicShortB_mkPub {P : Params PQ PQC} (hL : AtomicLengthsOk P ℓ)
    (s : LibsignalSim.SimState PQ Pt ℓ) (R : Party) (rq : PQC) (pn : BitVec 32)
    {pq' : PQ} {pub : LibsignalMsgPublicPart}
    (hmk : LibsignalSim.mkPub (P := P) s R rq pn = some (pq', pub)) :
    atomicShortB pub = true := by
  unfold LibsignalSim.mkPub at hmk
  rcases Option.mem_map.mp hmk with ⟨⟨st', salt, msg⟩, hsend, hpair⟩
  obtain ⟨_, rfl⟩ := Prod.mk.inj hpair
  have hmsg : msg.length ≤ 96 := hL.2.1 (s.pq R) rq st' salt msg hsend
  have haddr : (if R == Party.A && s.unackA then P.addrAB else none).all
      (fun a => decide (a.length ≤ 128)) = true := by
    split
    · cases hAB : P.addrAB with
      | none => rfl
      | some a =>
        have ha := hL.2.2.1 a hAB
        simp only [Option.all, decide_eq_true_eq]
        exact ha
    · rfl
  unfold atomicShortB
  rw [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hmsg, haddr⟩

private theorem qb_simSend_QAtomicShort (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ) (qep : ℕ)
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    QB (QAtomicShort Pt ℓ) (LibsignalSim.simSend (P := P) (qep := qep) R m₀ chal r) 0 := by
  unfold LibsignalSim.simSend
  refine qb_bind0 qb_get fun s => ?_
  split
  · exact qb_pure none 0
  · cases s.mir.epMgmt 3 qep R r.isSome with
    | none => exact qb_pure none 0
    | some s₁ =>
      dsimp only
      split
      · exact qb_pure none 0
      · cases r with
        | some rq =>
          simp only [pure_bind]
          refine qb_bind0 (qb_map some (qb_coin hQu_QAtomicShort (BitVec 256))) fun _ => ?_
          cases hmk : LibsignalSim.mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with
          | none => exact qb_pure none 0
          | some p =>
            rcases p with ⟨pq', pub⟩
            have hpub := atomicShortB_mkPub hL s R rq _ hmk
            dsimp only
            cases chal with
            | none =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some _ => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
            | some _ =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some _ => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
        | none =>
          refine qb_bind0 (qb_coin hQu_QAtomicShort PQC) fun rq => ?_
          simp only [pure_bind]
          cases hmk : LibsignalSim.mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with
          | none => exact qb_pure none 0
          | some p =>
            rcases p with ⟨pq', pub⟩
            have hpub := atomicShortB_mkPub hL s R rq _ hmk
            dsimp only
            cases chal with
            | none =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some _ => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
            | some _ =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QAtomicShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some _ => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0

omit [SampleableType PQC] in
private theorem qb_simRecv_QAtomicShort (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ) (R : Party) (w : List (BitVec 8))
    (isDel : Bool) :
    QB (QAtomicShort Pt ℓ)
      (LibsignalSim.simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) R w
        isDel) 0 := by
  have hQd : ∀ R c, QAtomicShort Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) → 0 < 0 := by
    intro _ _ h; nomatch h
  have hQi : ∀ R c, QAtomicShort Pt ℓ (.inr (.inl (.inr (R, c)))) → 0 < 0 := by
    intro _ _ h; nomatch h
  unfold LibsignalSim.simRecv
  refine qb_bind0 qb_get fun s => ?_
  dsimp only
  refine qb_ite_pure (qb_ite_pure (qb_ite_pure (qb_ite_pure ?_)))
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact qb_pure (some RecvResult.rejected) 0
  | some hp =>
    dsimp only
    refine qb_ite_pure ?_
    cases P.spqr.recv (s.pq R) hp.1.pqRatchet with
    | error _ => exact qb_pure (some RecvResult.rejected) 0
    | ok ps =>
      dsimp only
      cases (s.chains R).findIdx? (fun g => g.key == some hp.1.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine qb_ite_pure ?_
        exact qb_bind_r (qb_fwd 0 hQd hQi R _) fun res =>
          qb_onAnswer qep R w isDel _ _ _ res
      | none =>
        dsimp only
        refine qb_ite_pure (qb_ite_pure ?_)
        refine qb_ite (qb_bind0 (qb_putS _) fun _ => ?_) ?_ <;>
        · split
          · refine qb_ite ?_ ?_
            · refine qb_ite ?_ (qb_bind0 (qb_modify _) fun _ => qb_pure none 0)
              cases decT hp.1.senderRatchetKey with
              | none => exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
              | some _ =>
                refine qb_bind_r (qb_fwd 0 hQd hQi R _) fun _ => ?_
                exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
            · refine qb_bind0 (qb_liftQ_query fun h => ?_) fun _ => ?_
              · simp [QAtomicShort, badSendMsg, atomicShortB, Option.all] at h
              · cases decT hp.1.senderRatchetKey with
                | none => exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
                | some _ =>
                  refine qb_bind_r (qb_fwd 0 hQd hQi R _) fun _ => ?_
                  exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
          · refine qb_ite_pure ?_
            cases decT hp.1.senderRatchetKey with
            | none => exact qb_pure (some RecvResult.rejected) 0
            | some _ =>
              exact qb_bind_r (qb_fwd 0 hQd hQi R _) fun res =>
                qb_onAnswer qep R w isDel none _ _ res

private theorem qb_simImpl_QAtomicShort (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (k : Option ℕ)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) :
    QB (QAtomicShort Pt ℓ) (LibsignalSim.simImpl P Dh encT decT qep k t) 0 := by
  have hQcorr : ∀ R, QAtomicShort Pt ℓ (.inr (.inr R)) → 0 < 0 := by
    intro _ h; nomatch h
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
  · exact qb_liftQ_query fun h => absurd h (hQu_QAtomicShort n)
  · exact qb_guard (qb_simSend_QAtomicShort P hL qep R m none r)
  · exact qb_guard (qb_simSend_QAtomicShort P hL qep R m₀ (some m₁) r)
  · exact qb_guard (qb_simRecv_QAtomicShort P encT decT qep k R w true)
  · exact qb_guard (qb_simRecv_QAtomicShort P encT decT qep k R w false)
  · exact qb_guard (qb_simCorr P Dh encT 0 hQcorr R)

theorem simRun_sendAtomicShort (P : Params PQ PQC) (hL : AtomicLengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (k : Option ℕ) (A : LibAdv PQ PQC ℓ) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortB m.1)
      (LibsignalSim.simRun P Dh encT decT qep k A) := by
  have haux : IsQueryBoundP (LibsignalSim.simRun P Dh encT decT qep k A)
      (QAtomicShort Pt ℓ) 0 := by
    unfold LibsignalSim.simRun
    rw [← Nat.zero_add 0]
    refine isQueryBoundP_bind
      (isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QAtomicShort ($ᵗ BitVec 256)) fun pqrKey _ => ?_
    have hsim : IsQueryBoundP
        ((simulateQ (LibsignalSim.simImpl P Dh encT decT qep k) A).run
          (LibsignalSim.initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)))
        (QAtomicShort Pt ℓ) 0 :=
      isQueryBoundP_simulateQ_run_zero A (qb_simImpl_QAtomicShort P hL Dh encT decT qep k) _
    rw [StateT.run'_eq, ← Nat.add_zero 0]
    refine isQueryBoundP_bind ((isQueryBoundP_map_iff _ _ _).mpr hsim) fun b' _ => ?_
    cases k with
    | none => exact isQueryBoundP_pure _ b' 0
    | some _ => exact isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QAtomicShort ($ᵗ Bool)
  exact isQueryBoundP_congr (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) haux

end AtomicShortSim

section Session

variable {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC]

theorem simRun_fsReds_ok (P : Params PQ PQC) (hP : P.codec = protoSignalCodec) (ℓ : ℕ)
    (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep qep' : ℕ)
    (k : Option ℕ) (A : LibAdv PQ PQC ℓ) (qB : ℕ)
    (hqB : SM.MakesAtMostQueries (LibsignalSim.simRun P Dh encT decT qep k A) qB) :
    let B := LibsignalSim.simRun P Dh encT decT qep k A
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    (∀ j tL t, FsOk ℓ (2 * qB) qB
      (redFSAuth (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' j tL t
        (Thm1.challSim (2 + 1) qep' B))) ∧
    (∀ tL i,
      FsOk ℓ (2 * qB) qB (redFSPriv (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i
        (ThmB.privRedB (2 + 1) qep' i (lBlank ℓ) B)) ∧
      FsOk ℓ (2 * qB) qB (redFSPrivCoin (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i
        (ThmB.privRedB (2 + 1) qep' i (lBlank ℓ) B))) := by
  intro B fs
  have heqB := LibsignalSM.Proofs.QueryBounds.simRun_equalPub P Dh encT decT qep k A
  have hsh :=
    LibsignalSM.Proofs.SessionShort.fig8_fsReds_short P ℓ hL Dh encPt encT decT idOf lam qep qep'
      k A
  have hgsh :=
    LibsignalSM.Proofs.SessionShort.fig8_fsReds_guardedShort P (hP ▸ signalEncodeFits32_proto)
      ℓ hL Dh encPt encT decT idOf lam qep qep' k A
  refine ⟨fun j tL t => ?_, fun tL i => ?_⟩
  · obtain ⟨heqR, hclsR⟩ := Pres.auth_restricted Dh encPt P.C P.codec ℓ encT idOf 25000 lam qep'
      B heqB j tL t
    have hcs := Thm1.challSim_queries (2 + 1) qep' B qB hqB
    exact ⟨redFSAuth_queries (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' j tL t _ hcs,
      redFSAuth_dec_queries (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' j tL t _ hcs,
      heqR, hclsR, hsh.1 j tL t, hgsh.1 j tL t⟩
  · obtain ⟨⟨heq₁, hcls₁⟩, ⟨heq₂, hcls₂⟩⟩ := Pres.priv_restricted Dh encPt P.C P.codec ℓ encT idOf
      25000 lam qep' B heqB tL i
    have hqP :=
      LibsignalSM.Proofs.PrivRedQueries.privRedB_queries (2 + 1) qep' i (lBlank ℓ) B qB hqB
    exact ⟨⟨redFSPriv_queries (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i _ hqP,
        redFSPriv_dec_queries (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i _ hqP,
        heq₁, hcls₁, (hsh.2 tL i).1, (hgsh.2 tL i).1⟩,
      ⟨redFSPrivCoin_queries (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i _ hqP,
        redFSPrivCoin_dec_queries (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i _ hqP,
        heq₂, hcls₂, (hsh.2 tL i).2, (hgsh.2 tL i).2⟩⟩

theorem fig8_hybrid_le_shortWith (P : Params PQ PQC) (hP : P.codec = protoSignalCodec) (ℓ : ℕ)
    (hL : AtomicLengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (k : Option ℕ) (A : LibAdv PQ PQC ℓ) (qB : ℕ) (hq32 : 2 * qB + 25002 < 2 ^ 32)
    (hqB : SM.MakesAtMostQueries (LibsignalSim.simRun P Dh encT decT qep k A) qB) :
    hybridAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1)
        Config.h1 (LibsignalSim.simRun P Dh encT decT qep k A) ≤
      fig8ShortBoundWith Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) qB
        (fig8RedsInst Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) qB)
        (fsCostedRedsInst P.C P.codec ℓ encT idOf (min (2 * qB) (qB + 2)))
        (LibsignalSim.simRun P Dh encT decT qep k A) := by
  have h6 : hybridAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1)
      Config.h1 (LibsignalSim.simRun P Dh encT decT qep k A) ≤
      fig8H1Bound Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) qB
        (LibsignalSim.simRun P Dh encT decT qep k A) :=
    theorem6_h1_blank_concrete (dhScheme Dh) (rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) (dhScheme_correct Dh hDh)
      (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1) (lBlank ℓ) (fun _ _ h => by simp [lBlank, h])
      (LibsignalSim.simRun P Dh encT decT qep k A)
      (LibsignalSM.Proofs.QueryBounds.simRun_equalPub P Dh encT decT qep k A) qB hqB
  exact h6.trans (fig8H1Bound_le_fig8ShortBoundWith Dh encPt P.C hD P.codec hP ℓ hL.1
    encT hinj hdum idOf lam (qep + 1) qB hq32
    (fsCostedRedsInst P.C P.codec ℓ encT idOf (min (2 * qB) (qB + 2)))
    (fun R hR hRsh => by
      rw [hP]
      exact (fsShortBoundWith_inst_eq P.C ℓ encT idOf (min (2 * qB) (qB + 2)) qB hL.1 hinj R hR.1 hRsh).symm.le)
    _ hqB (simRun_sendAtomicShort P hL Dh encT decT qep k A)
    (LibsignalSM.Proofs.SessionShort.simRun_guardedSMShort P Dh encT decT qep k A))

theorem fig8_auth_le_shortWith (P : Params PQ PQC) (hP : P.codec = protoSignalCodec) (ℓ : ℕ)
    (hL : AtomicLengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (k : Option ℕ) (A : LibAdv PQ PQC ℓ) (qB : ℕ) (hq32 : 2 * qB + 25002 < 2 ^ 32)
    (hqB : SM.MakesAtMostQueries (LibsignalSim.simRun P Dh encT decT qep k A) qB) :
    2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
        authAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) tL t
          (Thm1.challSim (2 + 1) (qep + 1) (LibsignalSim.simRun P Dh encT decT qep k A)) ≤
      fig8ShortBoundWith Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) qB
        (fig8RedsInst Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) qB)
        (fsCostedRedsInst P.C P.codec ℓ encT idOf (min (2 * qB) (qB + 2)))
        (LibsignalSim.simRun P Dh encT decT qep k A) := by
  let B := LibsignalSim.simRun P Dh encT decT qep k A
  have hcs := Thm1.challSim_queries (2 + 1) (qep + 1) B qB hqB
  have h8 : 2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
      authAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep + 1) tL t
        (Thm1.challSim (2 + 1) (qep + 1) B) ≤
      fig8H1Bound Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) qB B := by
    unfold fig8H1Bound
    refine le_trans ?_ le_self_add
    gcongr with t _ tL _
    exact theorem8 (dhScheme Dh) (rootPRNG P.C.F encPt) (lFS P.C P.codec ℓ encT idOf 25000)
      lam 1 (qep + 1) (dhScheme_correct Dh hDh) tL t qB _ hcs
  exact h8.trans (fig8H1Bound_le_fig8ShortBoundWith Dh encPt P.C hD P.codec hP ℓ hL.1
    encT hinj hdum idOf lam (qep + 1) qB hq32
    (fsCostedRedsInst P.C P.codec ℓ encT idOf (min (2 * qB) (qB + 2)))
    (fun R hR hRsh => by
      rw [hP]
      exact (fsShortBoundWith_inst_eq P.C ℓ encT idOf (min (2 * qB) (qB + 2)) qB hL.1 hinj R hR.1 hRsh).symm.le)
    _ hqB (simRun_sendAtomicShort P hL Dh encT decT qep k A)
    (LibsignalSM.Proofs.SessionShort.simRun_guardedSMShort P Dh encT decT qep k A))

private theorem probComp_bind_congr_of_support {α β : Type}
    (m : ProbComp α) (f g : α → ProbComp β) (h : ∀ z ∈ support m, f z = g z) :
    m >>= f = m >>= g := by
  induction m using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t cont ih =>
    simp only [bind_assoc]
    congr 1; funext u
    exact ih u fun z hz => h z (by
      simp only [mem_support_bind_iff]
      exact ⟨u, by simp, hz⟩)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem oracleImplR_eq_fixedSpk {Key : Type} (P : Params PQ PQC) (ℓ Δ qep : ℕ)
    (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sm : SMSchemeR Key (GhostState PQ) (Plain ℓ) PQC (BitVec 256) (List (BitVec 8)))
    (hsend : sm.send = (CryptoVerification.E2E.sessionSchemeFixedSpk P ℓ 0).send)
    (hrecv : sm.receive = (CryptoVerification.E2E.sessionSchemeFixedSpk P ℓ 0).receive) :
    SM.oracleImplR sm Δ qep cfg =
      SM.oracleImplR (CryptoVerification.E2E.sessionSchemeFixedSpk P ℓ 0) Δ qep cfg := by
  funext q
  rcases q with (((x | x) | x) | x) | Q
  · change SM.transmitR sm Δ qep cfg x = SM.transmitR _ Δ qep cfg x
    unfold SM.transmitR SM.transmitImpl SMSchemeR.sendPart; rw [hsend]
  · change SM.challR sm Δ qep cfg x = SM.challR _ Δ qep cfg x
    unfold SM.challR SM.challImpl SMSchemeR.sendPart; rw [hsend]
  · change SM.deliverR sm cfg x = SM.deliverR _ cfg x
    unfold SM.deliverR; rw [hrecv]
  · change SM.injectR sm Δ qep cfg x = SM.injectR _ Δ qep cfg x
    unfold SM.injectR; rw [hrecv]
  · rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem transmitR_fixedSpk_step (P : Params PQ PQC) (ℓ Δ qep₁ qep₂ k : ℕ)
    (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (x : Party × Plain ℓ × Option PQC)
    {gs : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    (hgs : Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded k gs)
    (h₁ : k + 1 ≤ qep₁) (h₂ : k + 1 ≤ qep₂) :
    let sm₀ := CryptoVerification.E2E.sessionSchemeFixedSpk P ℓ 0
    (SM.transmitR sm₀ Δ qep₁ cfg x).run gs = (SM.transmitR sm₀ Δ qep₂ cfg x).run gs ∧
      ∀ z ∈ support ((SM.transmitR sm₀ Δ qep₁ cfg x).run gs),
        Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded (k + 1) z.2 := by
  rcases x with ⟨Q, m, r⟩
  have hQ : gs.epoch Q ≤ k := hgs.gs_epoch_le Q
  refine ⟨?_, ?_⟩
  · unfold SM.transmitR SM.transmitImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hok : cfg.sendOK gs Q
    · simp
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind]
      cases hwin : gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind]
        refine bind_congr fun cb => ?_
        rw [Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.epMgmt_eq_of_epoch_lt
          gs Δ qep₁ qep₂ Q cb.2 (by omega) (by omega)]
      · simp
  · intro z hz
    unfold SM.transmitR SM.transmitImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hok : cfg.sendOK gs Q
    · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hgs.mono (Nat.le_succ k)
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind] at hz
      cases hwin : gs.win
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind, mem_support_bind_iff] at hz
        rcases hz with ⟨cb, _, hz⟩
        cases hep : gs.epMgmt Δ qep₁ Q cb.2 with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hgs.mono (Nat.le_succ k)
        | some gs₁ =>
          simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.smEpochBounded_epMgmt_record
            P ℓ 0 m cb.1 hgs hep
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hgs.mono (Nat.le_succ k)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem challR_fixedSpk_step (P : Params PQ PQC) (ℓ Δ qep₁ qep₂ k : ℕ)
    (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (x : Party × Plain ℓ × Plain ℓ × Option PQC)
    {gs : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    (hgs : Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded k gs)
    (h₁ : k + 1 ≤ qep₁) (h₂ : k + 1 ≤ qep₂) :
    let sm₀ := CryptoVerification.E2E.sessionSchemeFixedSpk P ℓ 0
    (SM.challR sm₀ Δ qep₁ cfg x).run gs = (SM.challR sm₀ Δ qep₂ cfg x).run gs ∧
      ∀ z ∈ support ((SM.challR sm₀ Δ qep₁ cfg x).run gs),
        Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded (k + 1) z.2 := by
  rcases x with ⟨Q, m₀, m₁, r⟩
  have hQ : gs.epoch Q ≤ k := hgs.gs_epoch_le Q
  refine ⟨?_, ?_⟩
  · unfold SM.challR SM.challImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hok : cfg.sendOK gs Q
    · simp
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind]
      cases hwin : gs.win
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind]
        refine bind_congr fun cb => ?_
        rw [Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.epMgmt_eq_of_epoch_lt
          gs Δ qep₁ qep₂ Q cb.2 (by omega) (by omega)]
      · simp
  · intro z hz
    unfold SM.challR SM.challImpl at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    cases hok : cfg.sendOK gs Q
    · simp only [hok, Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hgs.mono (Nat.le_succ k)
    · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind] at hz
      cases hwin : gs.win
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind, mem_support_bind_iff] at hz
        rcases hz with ⟨cb, _, hz⟩
        cases hep : gs.epMgmt Δ qep₁ Q cb.2 with
        | none =>
          simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact hgs.mono (Nat.le_succ k)
        | some gs₁ =>
          simp only [hep] at hz
          cases hch : (!(gs₁.safeCh Δ Q) || !(cfg.base.challAllowedIn (gs₁.epoch Q)))
          · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.smEpochBounded_epMgmt_record
              P ℓ 0 ((cfg.base.challMsg (gs₁.epoch Q)).getD (if gs.b then m₁ else m₀)) cb.1 hgs hep
          · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; exact hgs.mono (Nat.le_succ k)
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hgs.mono (Nat.le_succ k)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem oracleImplR_fixedSpk_step (P : Params PQ PQC) (ℓ Δ qep₁ qep₂ k : ℕ)
    (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (o : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    {gs : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    (hgs : Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded k gs)
    (h₁ : k + 1 ≤ qep₁) (h₂ : k + 1 ≤ qep₂) :
    let sm₀ := CryptoVerification.E2E.sessionSchemeFixedSpk P ℓ 0
    (SM.oracleImplR sm₀ Δ qep₁ cfg o).run gs = (SM.oracleImplR sm₀ Δ qep₂ cfg o).run gs ∧
      ∀ z ∈ support ((SM.oracleImplR sm₀ Δ qep₁ cfg o).run gs),
        Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded (k + 1) z.2 := by
  rcases o with (((x | x) | x) | x) | Q
  · exact transmitR_fixedSpk_step P ℓ Δ qep₁ qep₂ k cfg x hgs h₁ h₂
  · exact challR_fixedSpk_step P ℓ Δ qep₁ qep₂ k cfg x hgs h₁ h₂
  · refine ⟨rfl, fun z hz =>
      Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.smEpochBounded_deliverR
        P ℓ k 0 cfg x hgs hz⟩
  · refine ⟨Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.injectR_run_eq_of_smEpochBounded
        P ℓ Δ qep₁ qep₂ k 0 cfg x hgs (by omega) (by omega),
      fun z hz =>
        Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.smEpochBounded_injectR
          P ℓ Δ qep₁ k 0 cfg x hgs hz⟩
  · refine ⟨rfl, fun z hz =>
      Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.smEpochBounded_corrR
        ℓ k cfg Q hgs hz⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem simulateQ_fixedSpk_run_eq (P : Params PQ PQC) (ℓ Δ qep₁ qep₂ : ℕ)
    (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    {oa : LibAdv PQ PQC ℓ} {rem k : ℕ} (hoa : SM.MakesAtMostQueries oa rem)
    {gs : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    (hgs : Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded k gs)
    (h₁ : k + rem ≤ qep₁) (h₂ : k + rem ≤ qep₂) :
    let uImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))) ProbComp)
    let sm₀ := CryptoVerification.E2E.sessionSchemeFixedSpk P ℓ 0
    (simulateQ (uImpl + SM.oracleImplR sm₀ Δ qep₁ cfg) oa).run gs =
      (simulateQ (uImpl + SM.oracleImplR sm₀ Δ qep₂ cfg) oa).run gs := by
  intro uImpl sm₀
  unfold SM.MakesAtMostQueries at hoa
  induction oa using OracleComp.inductionOn generalizing rem k gs with
  | pure a => rfl
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    cases t with
    | inl u =>
      change (uImpl u).run gs >>= _ = (uImpl u).run gs >>= _
      exact probComp_bind_congr_of_support _ _ _ fun z hz => by
        have hrem := hoa.2 z.1
        dsimp only at hrem
        have hgs_eq : z.2 = gs := by
          simp only [uImpl, QueryImpl.liftTarget_apply, StateT.run_monadLift, monadLift_self,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          rcases hz with ⟨_, _, hpair⟩
          exact (Prod.mk.inj hpair).2
        exact ih z.1 hrem (hgs_eq ▸ hgs) h₁ h₂
    | inr o =>
      have hpos : 0 < rem := hoa.1.resolve_left (by simp)
      have hstep := oracleImplR_fixedSpk_step P ℓ Δ qep₁ qep₂ k cfg o hgs (by omega) (by omega)
      change (SM.oracleImplR sm₀ Δ qep₁ cfg o).run gs >>= _ =
        (SM.oracleImplR sm₀ Δ qep₂ cfg o).run gs >>= _
      rw [← hstep.1]
      exact probComp_bind_congr_of_support _ _ _ fun z hz => by
        have hrem := hoa.2 z.1
        simp only [ite_true] at hrem
        exact ih z.1 hrem (hstep.2 z hz) (by omega) (by omega)

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
private theorem smEpochBounded_init_of_params {Key : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (sm : SMSchemeR Key (GhostState PQ) (Plain ℓ) PQC (BitVec 256) (List (BitVec 8)))
    (k : Key) (b : Bool)
    (hA : ∃ ik, sm.initA k = P.initA ik)
    (hB : ∃ ik, sm.initB k = P.initB ik) :
    Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded 0
      (SM.initState sm.sendPart k b) where
  gs_epoch_le _ := Nat.le_refl 0
  st_epoch_le Q := by
    cases Q
    · rcases hA with ⟨ik, hik⟩
      dsimp only [SM.initState, SMSchemeR.sendPart]; rw [hik]
      dsimp only [Params.initA]; split <;> exact Nat.le_refl 0
    · rcases hB with ⟨ik, hik⟩
      dsimp only [SM.initState, SMSchemeR.sendPart]; rw [hik]
      exact Nat.le_refl 0
  chains_le Q e he := by
    cases Q
    · rcases hA with ⟨ik, hik⟩
      dsimp only [SM.initState, SMSchemeR.sendPart] at he ⊢; rw [hik] at he ⊢
      dsimp only [Params.initA] at he ⊢; split at he <;> simp_all
    · rcases hB with ⟨ik, hik⟩
      dsimp only [SM.initState, SMSchemeR.sendPart] at he; rw [hik] at he
      dsimp only [Params.initB] at he; nomatch he
  trans_epoch_le _ hr := nomatch hr

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
private theorem runR_qepClamp_eq {Key : Type} [SampleableType Key]
    (P : Params PQ PQC) (ℓ Δ qep q : ℕ)
    (cfg : SM.ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sm : SMSchemeR Key (GhostState PQ) (Plain ℓ) PQC (BitVec 256) (List (BitVec 8)))
    (hsend : sm.send = (CryptoVerification.E2E.sessionSchemeFixedSpk P ℓ 0).send)
    (hrecv : sm.receive = (CryptoVerification.E2E.sessionSchemeFixedSpk P ℓ 0).receive)
    (hinit : ∀ k b, Computational.Proofs.SpecLemmas.Session.KemFailTrackEpochClamp.SmEpochBounded 0
      (SM.initState sm.sendPart k b))
    (b : Bool) (A : LibAdv PQ PQC ℓ) (hq : SM.MakesAtMostQueries A q) :
    SM.runR sm Δ qep cfg b A =
      SM.runR sm Δ (Computational.Proofs.SessionCostedHalt.qepClamp qep q) cfg b A := by
  by_cases hle : qep ≤ q + 4
  · rw [Computational.Proofs.SessionCostedHalt.qepClamp_eq_qep_of_le hle]
  · have hc : Computational.Proofs.SessionCostedHalt.qepClamp qep q = q + 4 :=
      Nat.min_eq_right (by omega)
    rw [hc]
    unfold SM.runR
    refine bind_congr fun k => ?_
    rw [oracleImplR_eq_fixedSpk P ℓ Δ qep cfg sm hsend hrecv,
      oracleImplR_eq_fixedSpk P ℓ Δ (q + 4) cfg sm hsend hrecv]
    exact simulateQ_fixedSpk_run_eq P ℓ Δ qep (q + 4) cfg hq (hinit k b) (by omega) (by omega)

private theorem fig8ShortBoundWith_clamp_le (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂) (q : ℕ)
    (base dummy : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam)
    (Rfs : FsCostedReds C codec ℓ encT idOf) (B : Fig8Adv Pt ℓ) :
    fig8ShortBoundWith Dh encPt C codec ℓ encT idOf lam qep₁ q base Rfs B ≤
      fig8ShortBoundWith Dh encPt C codec ℓ encT idOf lam qep₂ q
        (Computational.Proofs.SessionCostedHalt.clampFig8CostedReds qep₁ base dummy) Rfs B := by
  unfold fig8ShortBoundWith
  dsimp only [Computational.Proofs.SessionCostedHalt.clampFig8CostedReds]
  refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le) (mul_le_mul_of_nonneg_left ?_ zero_le)
  · refine le_trans ?_ (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.add_le_add_right hqep 2)))
    refine Finset.sum_le_sum fun t ht => ?_
    have hlt : t < qep₁ + 2 := Finset.mem_range.mp ht
    simp only [hlt, ↓reduceIte, le_refl]
  · refine le_trans ?_ (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.add_le_add_right hqep 1)))
    refine Finset.sum_le_sum fun i hi => ?_
    have hlt : i < qep₁ + 1 := Finset.mem_range.mp hi
    simp only [hlt, ↓reduceIte, le_refl]

/-- Bounds any `q`-query adversary's advantage against `libsignalSessionScheme` at `protoSignalCodec`
in the restricted on-curve ACD19 H1 game (DEV-LS1–DEV-LS7) via costed `ReductionDsl` bundles,
assuming atomic length bounds (DEV-LS21), abstract X25519 realization (DEV-LS29), SPQR switched off
(DEV-LS24), libsignal identity keys (DEV-LS15), and the `u32` message-counter bound (DEV-LS19).

**DEV-LS31 (formalization): the bound is vacuous beyond about 620,000,000 queries at `qep = 0`.**
Because `macForgeryProb ≥ 2⁻⁶⁴` is multiplied by `4 * q` per FS-AEAD instance, summed across
epoch/message guesses, and doubled by the authenticity term, the bound reaches 1 at `q = 619925131`
for `qep = 0` and at `q = 38967` for `qep = q`. Effect: constants (no claim for longer sessions).

**DEV-LS18 (libsignal): ratchet-key collisions.** Libsignal indexes epochs by ratchet public key
(DEV-LS8), so collisions between honest ratchet keys break chain lookup and are paid for by
`2·(qep + 2)·(q + qep + 2)·δ`. Effect: constants. -/
theorem libsignal_session_sm_r1_proto (P : Params PQ PQC) (hP : P.codec = protoSignalCodec)
    (ℓ : ℕ) (hL : AtomicLengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : Corr.SpqrOffCorrect P.spqr) (hD : ∀ k x, P.C.D k (P.C.E k x) = x)
    (idOf : Party → IdentityKey) (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ)
    (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) :
    ∃ (Rsim : Refine.SimProg PQ PQC Pt ℓ P Dh encT decT)
      (Rfig8 : Fig8CostedReds Dh encPt P.C P.codec ℓ encT idOf lam)
      (Rfs : FsCostedReds P.C P.codec ℓ encT idOf),
      simCostedBounds q qep Rsim ∧
      fig8CostedBounds q (qep + 1) Rfig8 ∧
      fsCostedBounds (min (2 * q) (q + 2)) (qep + 1) Rfs ∧
      ∀ (A : LibAdv PQ PQC ℓ) (_hq : SM.MakesAtMostQueries A q),
        hybridAdvantageR (libsignalSessionScheme P ℓ encPt lam) (2 + 1) qep
            (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) A ≤
          2 * fig8ShortBoundWith Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) q
              Rfig8 Rfs (Refine.evalSim Rsim A)
            + 2 * LibsignalSim.forgedEpochStartSpuriousStepTerm P.C.F encPt Dh q
            + 2 * LibsignalSim.spuriousStepTerm P.C.F encPt Dh q qep
            + 2 * LibsignalSim.epoch0Term P ℓ encPt lam
                (ratchetKeyAdmissible P.codec decT encT) qep q A
            + 2 * ((qep + 2) * (q + qep + 2) * δ) := by
  let qep_c := Computational.Proofs.SessionCostedHalt.qepClamp qep q
  have hqep_le : qep_c ≤ qep := Computational.Proofs.SessionCostedHalt.qepClamp_le_qep qep q
  have hqep_add : qep_c ≤ q + 4 := Computational.Proofs.SessionCostedHalt.qepClamp_le_add qep q
  let baseFig8 := fig8RedsInst Dh encPt P.C P.codec ℓ encT idOf lam (qep_c + 1) q
  let Rfig8 := Computational.Proofs.SessionCostedHalt.clampFig8CostedReds (qep_c + 1) baseFig8
    (fig8CostedRedsBoundedWitness Dh encPt P.C P.codec ℓ encT idOf lam)
  let Rfs := fsCostedRedsInst P.C P.codec ℓ encT idOf (min (2 * q) (q + 2))
  refine ⟨simProgInst P Dh encT decT q qep_c, Rfig8, Rfs,
    Computational.Proofs.SessionCostedHalt.gRedBounded_mono_budget
      (Computational.Proofs.SessionCostedHalt.ratchetCostBudget_qepClamp_le q qep)
      (simProgInst_bounds P Dh encT decT q qep_c (by omega)),
    Computational.Proofs.SessionCostedHalt.clampFig8CostedReds_bounds (Nat.add_le_add_right hqep_le 1)
      (fig8RedsInst_bounds Dh encPt P.C P.codec ℓ encT idOf lam (qep_c + 1) q (by omega))
      (fig8CostedRedsBoundedWitness_bounds Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) q),
    fsCostedRedsInst_bounds P.C P.codec ℓ encT idOf (min (2 * q) (q + 2)) (qep + 1),
    fun A hq => ?_⟩
  rw [evalSim_simProgInst P Dh encT decT q qep_c A hq]
  have hhyb_eq :
      hybridAdvantageR (libsignalSessionScheme P ℓ encPt lam) (2 + 1) qep
          (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) A =
        hybridAdvantageR (libsignalSessionScheme P ℓ encPt lam) (2 + 1) qep_c
          (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) A := by
    unfold hybridAdvantageR SM.gameR
    congr 2
    refine bind_congr fun b => ?_
    rw [runR_qepClamp_eq P ℓ (2 + 1) qep q
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT))
      (libsignalSessionScheme P ℓ encPt lam) rfl rfl
      (fun k b' => smEpochBounded_init_of_params P ℓ _ k b' ⟨_, rfl⟩ ⟨_, rfl⟩) b A hq]
  have hep0_eq :
      LibsignalSim.epoch0Term P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep_c q A =
        LibsignalSim.epoch0Term P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep q A := by
    unfold LibsignalSim.epoch0Term
    congr 2
    funext rc
    unfold LibsignalSim.epoch0Distinguisher
    refine bind_congr fun b => ?_
    rw [runR_qepClamp_eq P ℓ 3 qep q
      (LibsignalSim.configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT))
      (libsignalSessionSchemeFromEpoch0Keys P ℓ rc.1 rc.2) rfl rfl
      (fun k b' => smEpochBounded_init_of_params P ℓ _ k b' ⟨_, rfl⟩ ⟨_, rfl⟩) b A hq]
  rw [hhyb_eq, ← hep0_eq]
  refine (libsignal_refines_proto P hP ℓ Dh encPt encT decT hX hdec hL.toLengthsOk hinj hdum hz hS
    idOf hid lam qep_c q (by omega) δ hδ A hq).trans ?_
  have hfig8_bound :
      2 * fig8ShortBoundWith Dh encPt P.C P.codec ℓ encT idOf lam (qep_c + 1) q
          baseFig8 Rfs (Refine.sim P ℓ Dh encT decT qep_c A) ≤
        2 * fig8ShortBoundWith Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) q
          Rfig8 Rfs (Refine.sim P ℓ Dh encT decT qep_c A) :=
    mul_le_mul_of_nonneg_left (fig8ShortBoundWith_clamp_le Dh encPt P.C P.codec ℓ encT idOf lam
      (Nat.add_le_add_right hqep_le 1) q baseFig8
      (fig8CostedRedsBoundedWitness Dh encPt P.C P.codec ℓ encT idOf lam) Rfs _) zero_le
  have hfig8_le :
      hybridAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep_c + 1)
          Config.h1 (Refine.sim P ℓ Dh encT decT qep_c A) +
        2 * ∑ t ∈ Finset.range ((qep_c + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
          authAdvantage (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (2 + 1) (qep_c + 1) tL t
            (Thm1.challSim (2 + 1) (qep_c + 1) (Refine.sim P ℓ Dh encT decT qep_c A)) ≤
        2 * fig8ShortBoundWith Dh encPt P.C P.codec ℓ encT idOf lam (qep + 1) q
          Rfig8 Rfs (Refine.sim P ℓ Dh encT decT qep_c A) := by
    refine (add_le_add
      (fig8_hybrid_le_shortWith P hP ℓ hL Dh hDh encPt encT decT hinj hdum hD idOf lam qep_c
        none A q (by omega) (Refine.sim_queries P ℓ Dh encT decT qep_c q A hq))
      (fig8_auth_le_shortWith P hP ℓ hL Dh hDh encPt encT decT hinj hdum hD idOf lam qep_c
        none A q (by omega) (Refine.sim_queries P ℓ Dh encT decT qep_c q A hq))).trans ?_
    rw [← two_mul]
    exact hfig8_bound
  have hsp_le := Computational.Proofs.SessionCostedHalt.spuriousStepTerm_mono_qep
    P.C.F encPt Dh q hqep_le
  have hcoll_le :
      2 * (((qep_c : ℝ≥0∞) + 2) * ((q : ℝ≥0∞) + (qep_c : ℝ≥0∞) + 2) * δ) ≤
        2 * (((qep : ℝ≥0∞) + 2) * ((q : ℝ≥0∞) + (qep : ℝ≥0∞) + 2) * δ) := by
    have hqep_cast : (qep_c : ℝ≥0∞) ≤ (qep : ℝ≥0∞) := Nat.cast_le.mpr hqep_le
    gcongr
  exact add_le_add (add_le_add (add_le_add (add_le_add hfig8_le le_rfl)
    (mul_le_mul_of_nonneg_left hsp_le zero_le)) le_rfl) hcoll_le

end Session

/-! ## Joint satisfiability witness -/

section JointSat

local instance toyZero : Zero Bool := ⟨false⟩

def toyDh : DHFun (BitVec 256) Bool := ⟨true, fun _ P => P⟩

def toyEncPt : Bool → List (BitVec 8) := fun b => if b then x25519Base else List.replicate 32 0

def toyCrypto (F : ShaCompress) : Crypto :=
  ⟨F, fun _ b => b, fun _ b => b, fun _ u => u, fun _ => vec32 x25519Base⟩

def toyEncT (P : Bool) : PublicKey := ⟨vec32 (toyEncPt P)⟩

def toyDecT (pk : PublicKey) : Option Bool :=
  if pk = toyEncT true then some true else if pk = toyEncT false then some false else none

private theorem atomicLengthsOk_satisfiable (C : Crypto) (idA idB : IdentityKey) :
    let P : Params Unit Unit := ⟨C, protoSignalCodec, spqrOff, idA, idB, none, none⟩
    P.codec = protoSignalCodec ∧ AtomicLengthsOk P 0 ∧ Corr.SpqrOffCorrect P.spqr := by
  refine ⟨rfl, ⟨by decide, ?_, by simp, by simp⟩, ?_⟩
  · intro st rq st' salt msg h
    simp only [spqrOff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    decide
  · refine ⟨fun _ _ => rfl, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    intro st r st' salt msg h st₂
    simp only [spqrOff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨(), rfl⟩

example (F : ShaCompress) (idA idB : IdentityKey) :
    let P : Params Unit Unit := ⟨toyCrypto F, protoSignalCodec, spqrOff, idA, idB, none, none⟩
    let idOf : Party → IdentityKey := fun p => match p with | .A => idA | .B => idB
    P.codec = protoSignalCodec ∧ AtomicLengthsOk P 0 ∧ toyDh.Commutes ∧
      X25519RealizesDh P.C toyDh toyEncPt toyEncT ∧ (∀ T, toyDecT (toyEncT T) = some T) ∧
      Function.Injective toyEncT ∧ (∀ T, toyEncT T ≠ dummyKey) ∧ (∀ x, toyDh.dh x 0 = 0) ∧
      Corr.SpqrOffCorrect P.spqr ∧ (∀ k x, P.C.D k (P.C.E k x) = x) ∧
      (idOf .A = P.idA ∧ idOf .B = P.idB) ∧ 2 * (0 + 1) + 25002 < 2 ^ 32 ∧
      (∀ Q : Bool,
        𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | toyDh.dh x toyDh.base = Q} ≤ 1) := by
  intro P idOf
  obtain ⟨hP, hL, hS⟩ := atomicLengthsOk_satisfiable (toyCrypto F) idA idB
  refine ⟨hP, hL, fun _ _ => rfl, ⟨?_, fun _ => rfl⟩, ?_, ?_, ?_, fun _ => rfl, hS,
    fun _ _ => rfl, ⟨rfl, rfl⟩, by norm_num, fun _ => MeasureTheory.prob_le_one⟩
  · exact
      { enc_injective := by
          intro a b h; cases a <;> cases b <;> simp_all [toyEncPt, x25519Base]
        enc_length := by intro P; cases P <;> simp [toyEncPt, x25519Base]
        enc_zero := rfl
        enc_base := rfl
        base_ne_zero := by decide
        hook := fun _ P => by
          cases P
          · exact (by decide : (vec32 (toyEncPt false)).toList = toyEncPt false)
          · exact (by decide : (vec32 (toyEncPt true)).toList = toyEncPt true)
        pubKey_hook := fun _ => (by decide : (vec32 x25519Base).toList = x25519Base)
        dh_clamp := fun _ _ => rfl
        dh_ne_zero := fun _ _ h => h }
  · intro T; cases T <;> decide
  · intro a b h; cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))
  · intro T; cases T <;> decide

end JointSat

end CryptoVerification.LibsignalSession
