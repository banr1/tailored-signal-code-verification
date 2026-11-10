/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.QueryBounds
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RestrictedReds

/-!
# Short-message and short-wire invariants for `simRun`, `challSim`, and `privRedB`

**Checked by Lean.**

Proves that `LibsignalSim.simRun` emits only short public parts under `LengthsOk` and satisfies
`GuardedSMShort`, and that `challSim` and `privRedB` preserve both invariants.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM

set_option linter.unusedSectionVars false

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD LibsignalSim QueryBounds RestrictedReds

section Defs

variable {St Msg Coins C : Type}

def badSendMsg (ok : Msg → Bool) : (unifSpec + SM.spec St Msg Coins C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inl ⟨_, m, _⟩)))) => !ok m
  | .inr (.inl (.inl (.inl (.inr ⟨_, m₀, m₁, _⟩)))) => !ok m₀ || !ok m₁
  | _ => false

def SendMsgsOk (ok : Msg → Bool) (A : SM.Adversary St Msg Coins C) : Prop :=
  A.IsQueryBoundP (fun t => badSendMsg (St := St) (Coins := Coins) (C := C) ok t = true) 0

def smRespShort {St Msg Coins T : Type} :
    (t : (unifSpec + SM.spec St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32))).Domain) →
      (unifSpec + SM.spec St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32))).Range t → Prop
  | .inr (.inl (.inl (.inl (.inl _)))), r =>
      ∀ c : Header T × (ℕ × LibsignalCiphertextWithSalt32), r = some c → c.2.2.1.1.length + 8 < 2 ^ 32
  | .inr (.inl (.inl (.inl (.inr _)))), r =>
      ∀ c : Header T × (ℕ × LibsignalCiphertextWithSalt32), r = some c → c.2.2.1.1.length + 8 < 2 ^ 32
  | _, _ => True

def smRecvLong {St Msg Coins T : Type} :
    (unifSpec + SM.spec St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32))).Domain → Prop
  | .inr (.inl (.inl (.inr ⟨_, c⟩))) => ¬ c.2.2.1.1.length < 2 ^ 32
  | .inr (.inl (.inr ⟨_, c⟩)) => ¬ c.2.2.1.1.length < 2 ^ 32
  | _ => False

instance instDecidablePredSmRecvLong {St Msg Coins T : Type} :
    DecidablePred (smRecvLong (St := St) (Msg := Msg) (Coins := Coins) (T := T))
  | .inr (.inl (.inl (.inr ⟨_, c⟩))) => inferInstanceAs (Decidable (¬ c.2.2.1.1.length < 2 ^ 32))
  | .inr (.inl (.inr ⟨_, c⟩)) => inferInstanceAs (Decidable (¬ c.2.2.1.1.length < 2 ^ 32))
  | .inl _ => isFalse not_false
  | .inr (.inl (.inl (.inl (.inl _)))) => isFalse not_false
  | .inr (.inl (.inl (.inl (.inr _)))) => isFalse not_false
  | .inr (.inr _) => isFalse not_false

/-- Under `smRespShort`, `A` never queries `deliver` or `inject` on a serialized wire of length
`≥ 2 ^ 32`. -/
def GuardedSMShort {St Msg Coins T : Type}
    (A : SM.Adversary St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32))) : Prop :=
  GuardedSafe.GuardedSafePost smRespShort smRecvLong (fun _ => True) A

end Defs

/-! ## Short public parts in `simRun` -/

section Sim

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
  {ℓ : ℕ}

abbrev QShort (Pt : Type) (ℓ : ℕ) : (FSpec Pt ℓ).Domain → Prop :=
  fun t => badSendMsg (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
    (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) t = true

theorem hQu_QShort : ∀ u : ℕ, ¬ QShort Pt ℓ (.inl u) := by
  intro _ h; nomatch h

theorem shortB_mkPub {P : Params PQ PQC} (hL : LengthsOk P ℓ)
    (s : SimState PQ Pt ℓ) (R : Party) (rq : PQC) (pn : BitVec 32)
    {pq' : PQ} {pub : LibsignalMsgPublicPart} (hmk : mkPub (P := P) s R rq pn = some (pq', pub)) :
    pub.shortB = true := by
  unfold mkPub at hmk
  rcases Option.mem_map.mp hmk with ⟨⟨st', salt, msg⟩, hsend, hpair⟩
  obtain ⟨_, rfl⟩ := Prod.mk.inj hpair
  have hmsg : msg.length < 2 ^ 29 := hL.2.1 (s.pq R) rq st' salt msg hsend
  have haddr : (if R == Party.A && s.unackA then P.addrAB else none).all
      (fun a => decide (a.length < 2 ^ 29)) = true := by
    split
    · cases hAB : P.addrAB with
      | none => rfl
      | some a =>
        have ha := hL.2.2.1 a hAB
        simp only [Option.all, decide_eq_true_eq]
        exact ha
    · rfl
  unfold LibsignalMsgPublicPart.shortB
  rw [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hmsg, haddr⟩

theorem qb_simSend_QShort (P : Params PQ PQC) (hL : LengthsOk P ℓ) (qep : ℕ)
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    QB (QShort Pt ℓ) (simSend (P := P) (qep := qep) R m₀ chal r) 0 := by
  unfold simSend
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
          refine qb_bind0 (qb_map some (qb_coin hQu_QShort (BitVec 256))) fun rc => ?_
          cases hmk : mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with
          | none => exact qb_pure none 0
          | some p =>
            rcases p with ⟨pq', pub⟩
            have hpub := shortB_mkPub hL s R rq _ hmk
            dsimp only
            cases chal with
            | none =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some c => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
            | some m₁ =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some c => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
        | none =>
          refine qb_bind0 (qb_coin hQu_QShort PQC) fun rq => ?_
          simp only [pure_bind]
          cases hmk : mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with
          | none => exact qb_pure none 0
          | some p =>
            rcases p with ⟨pq', pub⟩
            have hpub := shortB_mkPub hL s R rq _ hmk
            dsimp only
            cases chal with
            | none =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some c => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0
            | some m₁ =>
              refine qb_bind_r (qb_liftQ_query fun h => ?_) fun res => ?_
              · simp [QShort, badSendMsg, hpub] at h
              · cases res with
                | none => exact qb_pure none 0
                | some c => exact qb_bind0 (qb_putS _) fun _ => qb_pure _ 0

theorem qb_simRecv_QShort (P : Params PQ PQC) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (qep : ℕ) (k : Option ℕ) (R : Party) (w : List (BitVec 8)) (isDel : Bool) :
    QB (QShort Pt ℓ) (simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) R w isDel) 0 := by
  have hQd : ∀ R c, QShort Pt ℓ (.inr (.inl (.inl (.inr (R, c))))) → 0 < 0 := by
    intro _ _ h; nomatch h
  have hQi : ∀ R c, QShort Pt ℓ (.inr (.inl (.inr (R, c)))) → 0 < 0 := by
    intro _ _ h; nomatch h
  unfold simRecv
  refine qb_bind0 qb_get fun s => ?_
  dsimp only
  refine qb_ite_pure ?_
  refine qb_ite_pure ?_
  refine qb_ite_pure ?_
  refine qb_ite_pure ?_
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
        refine qb_ite_pure ?_
        refine qb_ite_pure ?_
        refine qb_ite (qb_bind0 (qb_putS _) fun _ => ?_) ?_ <;>
        · split
          · refine qb_ite ?_ ?_
            · refine qb_ite ?_ (qb_bind0 (qb_modify _) fun _ => qb_pure none 0)
              cases decT hp.1.senderRatchetKey with
              | none => exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
              | some T =>
                refine qb_bind_r (qb_fwd 0 hQd hQi R _) fun _ => ?_
                exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
            · refine qb_bind0 (qb_liftQ_query fun h => ?_) fun _ => ?_
              · simp [QShort, badSendMsg, LibsignalMsgPublicPart.shortB, Option.all] at h
              · cases decT hp.1.senderRatchetKey with
                | none => exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
                | some T =>
                  refine qb_bind_r (qb_fwd 0 hQd hQi R _) fun _ => ?_
                  exact qb_bind0 (qb_modify _) fun _ => qb_pure none 0
          · refine qb_ite_pure ?_
            cases decT hp.1.senderRatchetKey with
            | none => exact qb_pure (some RecvResult.rejected) 0
            | some T =>
              exact qb_bind_r (qb_fwd 0 hQd hQi R _) fun res =>
                qb_onAnswer qep R w isDel none _ _ res

theorem qb_simImpl_QShort (P : Params PQ PQC) (hL : LengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (t : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain) :
    QB (QShort Pt ℓ) (simImpl P Dh encT decT qep k t) 0 := by
  have hQcorr : ∀ R, QShort Pt ℓ (.inr (.inr R)) → 0 < 0 := by
    intro _ h; nomatch h
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R))
  · exact qb_liftQ_query fun h => absurd h (hQu_QShort n)
  · exact qb_guard (qb_simSend_QShort P hL qep R m none r)
  · exact qb_guard (qb_simSend_QShort P hL qep R m₀ (some m₁) r)
  · exact qb_guard (qb_simRecv_QShort P encT decT qep k R w true)
  · exact qb_guard (qb_simRecv_QShort P encT decT qep k R w false)
  · exact qb_guard (qb_simCorr P Dh encT 0 hQcorr R)

theorem simRun_sendShort_aux (P : Params PQ PQC) (hL : LengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (LibsignalSim.simRun P Dh encT decT qep k A) := by
  unfold SendMsgsOk simRun
  change IsQueryBoundP _ (QShort Pt ℓ) 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QShort ($ᵗ BitVec 256))
    fun pqrKey _ => ?_
  have hsim : IsQueryBoundP
      ((simulateQ (simImpl P Dh encT decT qep k) A).run
        (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QShort Pt ℓ) 0 :=
    isQueryBoundP_simulateQ_run_zero A (qb_simImpl_QShort P hL Dh encT decT qep k) _
  rw [StateT.run'_eq, ← Nat.add_zero 0]
  have hmap : IsQueryBoundP
      (Prod.fst <$> (simulateQ (simImpl P Dh encT decT qep k) A).run
        (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) (QShort Pt ℓ) 0 :=
    (isQueryBoundP_map_iff _ _ _).mpr hsim
  refine isQueryBoundP_bind hmap fun b' _ => ?_
  cases k with
  | none => exact isQueryBoundP_pure _ b' 0
  | some _ => exact isQueryBoundP_liftProb (Pt := Pt) (ℓ := ℓ) hQu_QShort ($ᵗ Bool)

theorem simRun_sendShort_proof (P : Params PQ PQC) (hL : LengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
    {bad : (FSpec Pt ℓ).Domain → Bool}
    (hbad : ∀ t, bad t = badSendMsg (St := Fig8St Pt) (Coins := BitVec 256) (C := Fig8C Pt)
      (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) t := by
      rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) :
    (LibsignalSim.simRun P Dh encT decT qep k A).IsQueryBoundP (fun t => bad t = true) 0 := by
  refine isQueryBoundP_congr (fun t => by rw [hbad]) ?_
  exact simRun_sendShort_aux P hL Dh encT decT qep k A

end Sim

/-! ## Preservation under `challSim` and `privRedB` -/

section Red

variable {St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

abbrev QBadSend (ok : Msg → Bool) : (unifSpec + SM.spec St Msg Coins C).Domain → Prop :=
  fun t => badSendMsg (St := St) (Coins := Coins) (C := C) ok t = true

theorem hQu_QBadSend (ok : Msg → Bool) (u : ℕ) :
    ¬ QBadSend (St := St) (Coins := Coins) (C := C) ok (.inl u) := by
  simp [QBadSend, badSendMsg]

theorem safeS_thm1_simOracles_sendOk (Δ qep : ℕ) (ok : Msg → Bool)
    (o : (SM.spec St Msg Coins C).Domain)
    (ho : ¬ QBadSend (St := St) (Coins := Coins) (C := C) ok (.inr o)) :
    SafeS (QBadSend (St := St) (Coins := Coins) (C := C) ok) (fun _ => True) (fun _ _ => True)
      (Thm1.simOracles (St := St) (Coins := Coins) Δ qep (fun _ => none) none o) := by
  rcases o with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change SafeS _ _ _ (Thm1.simTransmit (St := St) Δ qep (P, m, r))
    unfold Thm1.simTransmit SM.transmitQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query ho fun res => ?_
    cases res <;> cases s.epMgmt Δ qep P r.isSome
    all_goals first
      | exact safeS_pure_true _
      | exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (Thm1.simChall (St := St) Δ qep (fun _ => none) none (P, m₀, m₁, r))
    unfold Thm1.simChall Thm1.simSend SM.transmitQuery
    simp only [QBadSend, badSendMsg, Bool.or_eq_true, Bool.not_eq_true', not_or,
      Bool.not_eq_false] at ho
    refine safeS_get_bind fun s _ => ?_
    cases s.epMgmt Δ qep P r.isSome with
    | none => exact safeS_pure_true _
    | some s₁ =>
      dsimp only
      cases s₁.safeCh Δ P
      · exact safeS_pure_true _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hmb : ¬ QBadSend (St := St) (Coins := Coins) (C := C) ok
            (.inr (.inl (.inl (.inl (.inl (P, if s.b then m₁ else m₀, r)))))) := by
          cases s.b <;> simp [QBadSend, badSendMsg, ho.1, ho.2]
        refine safeS_bind_query hmb fun res => ?_
        cases res
        · exact safeS_pure_true _
        · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (Thm1.simDeliver (St := St) (Coins := Coins) (P, c))
    unfold Thm1.simDeliver SM.deliverQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QBadSend, badSendMsg]) fun res => ?_
    cases res with
    | none => exact safeS_pure_true _
    | some rr =>
      cases rr <;> cases s.inTransit P.other c
      all_goals first
        | exact safeS_pure_true _
        | exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (Thm1.simInject (St := St) (Coins := Coins) (P, c))
    unfold Thm1.simInject SM.injectQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QBadSend, badSendMsg]) fun res => ?_
    cases res with
    | none => exact safeS_pure_true _
    | some rr =>
      cases rr
      · exact safeS_pure_true _
      · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (Thm1.simCorr (St := St) (Msg := Msg) (Coins := Coins) (C := C) P)
    unfold Thm1.simCorr SM.corrQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QBadSend, badSendMsg]) fun res => ?_
    cases res <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]
    · exact safeS_pure_true _
    · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _

theorem challSim_sendOk_aux (Δ qep : ℕ) (ok : Msg → Bool) (A : SM.Adversary St Msg Coins C)
    (hA : SendMsgsOk ok A) : SendMsgsOk ok (Thm1.challSim Δ qep A) := by
  unfold SendMsgsOk at hA ⊢
  dsimp only [Thm1.challSim, Thm1.simRun]
  rw [bind_assoc]
  refine SafePost.to_isQueryBoundP (P := fun _ => True) ?_
  refine (SafePost.liftComp_unif (hQu_QBadSend (St := St) (Coins := Coins) (C := C) ok) ($ᵗ Bool)).bind
    fun b _ => ?_
  rw [bind_assoc, StateT.run'_eq]
  have hsim : SafePost (QBadSend (St := St) (Coins := Coins) (C := C) ok) (fun _ => True)
      ((simulateQ (Thm1.simImpl Δ qep (fun _ => none) none) A).run
        ({ st := fun _ => (), b } : Thm1.Mirror Msg C)) := by
    refine SafePost.simulateQ_run (I := fun _ => True) (SafePost.of_isQueryBoundP hA) ?_ trivial
    rintro (u | o) ho
    · exact safeS_lift_query (hQu_QBadSend (St := St) (Coins := Coins) (C := C) ok u)
    · exact safeS_thm1_simOracles_sendOk Δ qep ok o ho
  exact (hsim.map (R := fun _ => True) Prod.fst (fun _ _ => trivial)).bind fun _ _ =>
    SafePost.pure trivial

theorem challSim_sendOk_proof (Δ qep : ℕ) (ok : Msg → Bool) (A : SM.Adversary St Msg Coins C)
    {bad : (unifSpec + SM.spec St Msg Coins C).Domain → Bool}
    (hA : A.IsQueryBoundP (fun t => bad t = true) 0)
    (hbad : ∀ t, bad t = badSendMsg (St := St) (Coins := Coins) (C := C) ok t := by
      rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) :
    (Thm1.challSim Δ qep A).IsQueryBoundP (fun t => bad t = true) 0 := by
  refine isQueryBoundP_congr (fun t => by rw [hbad]) ?_
  exact challSim_sendOk_aux Δ qep ok A (isQueryBoundP_congr (fun t => by rw [hbad]) hA)

theorem safeS_thmB_simOracles_sendOk (Δ qep i : ℕ) (ok : Msg → Bool) (blank : Msg → Msg)
    (hblank : ∀ m, ok (blank m) = ok m)
    (o : (SM.spec St Msg Coins C).Domain)
    (ho : ¬ QBadSend (St := St) (Coins := Coins) (C := C) ok (.inr o)) :
    SafeS (QBadSend (St := St) (Coins := Coins) (C := C) ok) (fun _ => True) (fun _ _ => True)
      (ThmB.simOracles (St := St) (Coins := Coins) Δ qep
        (fun t => if t < i then some blank else none) (some (i, blank)) o) := by
  rcases o with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change SafeS _ _ _ (ThmB.simTransmit (St := St) Δ qep (P, m, r))
    unfold ThmB.simTransmit SM.transmitQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query ho fun res => ?_
    cases res <;> cases s.epMgmt Δ qep P r.isSome
    all_goals first
      | exact safeS_pure_true _
      | exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (ThmB.simChall (St := St) Δ qep
      (fun t => if t < i then some blank else none) (some (i, blank)) (P, m₀, m₁, r))
    unfold ThmB.simChall ThmB.simSend SM.transmitQuery SM.challQuery
    simp only [QBadSend, badSendMsg, Bool.or_eq_true, Bool.not_eq_true', not_or,
      Bool.not_eq_false] at ho
    refine safeS_get_bind fun s _ => ?_
    cases s.epMgmt Δ qep P r.isSome with
    | none => exact safeS_pure_true _
    | some s₁ =>
      dsimp only
      cases s₁.safeCh Δ P
      · exact safeS_pure_true _
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases hti : s₁.epoch P = i
        · simp only [hti, ↓reduceIte]
          have hmb : ¬ QBadSend (St := St) (Coins := Coins) (C := C) ok
              (.inr (.inl (.inl (.inl (.inr
                (P, blank (if s.b then m₁ else m₀), if s.b then m₁ else m₀, r)))))) := by
            cases s.b <;> simp [QBadSend, badSendMsg, hblank, ho.1, ho.2]
          refine safeS_bind_query hmb fun res => ?_
          cases res
          · exact safeS_pure_true _
          · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
        · simp only [hti, ↓reduceIte]
          have hmb : ¬ QBadSend (St := St) (Coins := Coins) (C := C) ok
              (.inr (.inl (.inl (.inl (.inl
                (P, (((if s₁.epoch P < i then some blank else none).map
                  (· (if s.b then m₁ else m₀))).getD (if s.b then m₁ else m₀)), r)))))) := by
            by_cases hlt : s₁.epoch P < i <;> cases s.b <;>
              simp [hlt, QBadSend, badSendMsg, hblank, ho.1, ho.2]
          refine safeS_bind_query hmb fun res => ?_
          cases res
          · exact safeS_pure_true _
          · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (ThmB.simDeliver (St := St) (Coins := Coins) (P, c))
    unfold ThmB.simDeliver SM.deliverQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QBadSend, badSendMsg]) fun res => ?_
    cases res with
    | none => exact safeS_pure_true _
    | some rr =>
      cases rr <;> cases s.inTransit P.other c
      all_goals first
        | exact safeS_pure_true _
        | exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (ThmB.simInject (St := St) (Coins := Coins) (P, c))
    unfold ThmB.simInject SM.injectQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QBadSend, badSendMsg]) fun res => ?_
    cases res with
    | none => exact safeS_pure_true _
    | some rr =>
      cases rr
      · exact safeS_pure_true _
      · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _
  · change SafeS _ _ _ (ThmB.simCorr (St := St) (Msg := Msg) (Coins := Coins) (C := C) P)
    unfold ThmB.simCorr SM.corrQuery
    refine safeS_get_bind fun s _ => ?_
    refine safeS_bind_query (by simp [QBadSend, badSendMsg]) fun res => ?_
    cases res <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]
    · exact safeS_pure_true _
    · exact safeS_bind_true (safeS_set_true _ (fun _ _ => trivial)) fun _ => safeS_pure_true _

theorem privRedB_sendOk_aux (Δ qep i : ℕ) (ok : Msg → Bool) (blank : Msg → Msg)
    (hblank : ∀ m, ok (blank m) = ok m) (A : SM.Adversary St Msg Coins C)
    (hA : SendMsgsOk ok A) : SendMsgsOk ok (ThmB.privRedB Δ qep i blank A) := by
  unfold SendMsgsOk at hA ⊢
  dsimp only [ThmB.privRedB, ThmB.simRun]
  rw [bind_assoc]
  refine SafePost.to_isQueryBoundP (P := fun _ => True) ?_
  refine (SafePost.liftComp_unif (hQu_QBadSend (St := St) (Coins := Coins) (C := C) ok) ($ᵗ Bool)).bind
    fun b _ => ?_
  rw [bind_assoc, StateT.run'_eq]
  have hsim : SafePost (QBadSend (St := St) (Coins := Coins) (C := C) ok) (fun _ => True)
      ((simulateQ (ThmB.simImpl Δ qep (fun t => if t < i then some blank else none) (some (i, blank))) A).run
        ({ st := fun _ => (), b } : Thm1.Mirror Msg C)) := by
    refine SafePost.simulateQ_run (I := fun _ => True) (SafePost.of_isQueryBoundP hA) ?_ trivial
    rintro (u | o) ho
    · exact safeS_lift_query (hQu_QBadSend (St := St) (Coins := Coins) (C := C) ok u)
    · exact safeS_thmB_simOracles_sendOk Δ qep i ok blank hblank o ho
  exact (hsim.map (R := fun _ => True) Prod.fst (fun _ _ => trivial)).bind fun _ _ =>
    SafePost.pure trivial

theorem privRedB_sendOk_proof (Δ qep i : ℕ) (ok : Msg → Bool) (blank : Msg → Msg)
    (hblank : ∀ m, ok (blank m) = ok m) (A : SM.Adversary St Msg Coins C)
    {bad : (unifSpec + SM.spec St Msg Coins C).Domain → Bool}
    (hA : A.IsQueryBoundP (fun t => bad t = true) 0)
    (hbad : ∀ t, bad t = badSendMsg (St := St) (Coins := Coins) (C := C) ok t := by
      rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) :
    (ThmB.privRedB Δ qep i blank A).IsQueryBoundP (fun t => bad t = true) 0 := by
  refine isQueryBoundP_congr (fun t => by rw [hbad]) ?_
  exact privRedB_sendOk_aux Δ qep i ok blank hblank A
    (isQueryBoundP_congr (fun t => by rw [hbad]) hA)

end Red

/-! ## Guarded short-wire invariants -/

section GuardedShort

open GuardedSafe

theorem length_toWire_eq {Pt : Type} (c : Fig8C Pt) :
    (toWire c).length = c.2.2.1.1.length + 8 := by
  simp [toWire, tagBytes]

theorem epMgmt_trans_eq {St Msg C : Type} {s s₁ : SM.GameState St Msg C} {Δ qep : ℕ}
    {Q : Party} {bad : Bool} (h : s.epMgmt Δ qep Q bad = some s₁) : s₁.trans = s.trans := by
  unfold SM.GameState.epMgmt at h
  split at h
  · split at h
    · cases h
    · cases h
      dsimp only
      split <;> rfl
  · split at h
    · cases h
    · cases h; rfl

theorem mem_accept_trans {St Msg C : Type} {s : SM.GameState St Msg C}
    {Q : Party} {st' : St} {pos : SM.Pos} {r : SM.Record Msg C}
    (hr : r ∈ (s.accept Q st' pos).trans) : r ∈ s.trans := by
  simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr
  exact hr.1

theorem inTransit_mem_and_ct {St Msg C : Type} [DecidableEq C]
    {s : SM.GameState St Msg C} {Q : Party} {c : C} {r : SM.Record Msg C}
    (h : s.inTransit Q c = some r) : r ∈ s.trans ∧ r.ct = c := by
  unfold SM.GameState.inTransit at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨hmem, hp.2⟩

section SimGuarded

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
  {ℓ : ℕ}

/-- State invariant of `simRun`: every in-transit mirrored wire and every recorded honest Fig. 8
serialized wire has length `< 2 ^ 32`. -/
def SimShortInv (s : SimState PQ Pt ℓ) : Prop :=
  (∀ r ∈ s.mir.trans, r.ct.length < 2 ^ 32) ∧
    (∀ wc ∈ s.honest, wc.2.2.2.1.1.length < 2 ^ 32)

theorem simShortInv_initSim (pqA pqB : PQ) :
    SimShortInv (Pt := Pt) (ℓ := ℓ) (initSim pqA pqB) :=
  ⟨by simp [initSim], by simp [initSim]⟩

theorem hQu_smRecvLong {St Msg Coins T : Type} (u : ℕ) :
    ¬ smRecvLong (St := St) (Msg := Msg) (Coins := Coins) (T := T) (.inl u) :=
  not_false

abbrev SimSafeS (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) : Prop :=
  GuardedSafeS
    (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (SimShortInv (PQ := PQ) (Pt := Pt) (ℓ := ℓ))
    (fun _ s => SimShortInv s) x

theorem simSafeS_ite {α : Type} {c : Prop} [Decidable c]
    {t e : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    (ht : SimSafeS PQ Pt ℓ t) (he : SimSafeS PQ Pt ℓ e) :
    SimSafeS PQ Pt ℓ (if c then t else e) := by
  split
  · exact ht
  · exact he

theorem simSafeS_ite_pure {α : Type} {c : Prop} [Decidable c] {a : α}
    {e : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α}
    (he : ¬ c → SimSafeS PQ Pt ℓ e) :
    SimSafeS PQ Pt ℓ (if c then pure a else e) := by
  split
  · exact guardedSafeS_pure_true a
  · rename_i hc; exact he hc

theorem guardedSafeS_coin_sim (α : Type) [SampleableType α] :
    SimSafeS PQ Pt ℓ (coin α) :=
  guardedSafeS_lift_true (GuardedSafePost.liftComp_unif hQu_smRecvLong ($ᵗ α))

theorem guardedSafeS_fwd (Q : Party) (c : Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32) :
    SimSafeS PQ Pt ℓ (fwd Q c) := by
  unfold fwd SM.deliverQuery SM.injectQuery liftQ
  refine guardedSafeS_get_bind fun s _ => ?_
  dsimp only
  refine simSafeS_ite ?_ ?_
  · exact guardedSafeS_bind_query (fun h => h hc) fun _ _ => guardedSafeS_pure_true _
  · exact guardedSafeS_bind_query (fun h => h hc) fun _ _ => guardedSafeS_pure_true _

theorem guardedSafeS_onAccept (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ) :
    SimSafeS PQ Pt ℓ (onAccept (qep := qep) Q w isDel t i m ci? T pq') := by
  unfold onAccept putS
  refine guardedSafeS_get_bind fun s hs => ?_
  dsimp only
  refine simSafeS_ite ?_ ?_
  · cases s.mir.inTransit Q.other w with
    | none => exact guardedSafeS_pure_true none
    | some r =>
      refine guardedSafeS_bind_true
        (guardedSafeS_set_true _ fun _ _ =>
          ⟨fun r' hr' => hs.1 r' (mem_accept_trans hr'), hs.2⟩)
        fun _ => guardedSafeS_pure_true _
  · refine simSafeS_ite_pure fun _ => ?_
    refine simSafeS_ite ?_ ?_
    · refine guardedSafeS_bind_true
        (guardedSafeS_set_true _ fun _ _ =>
          ⟨fun r' hr' => hs.1 r' (mem_accept_trans hr'), hs.2⟩)
        fun _ => guardedSafeS_pure_true _
    · refine guardedSafeS_bind_true
        (guardedSafeS_set_true _ fun _ _ => ⟨hs.1, hs.2⟩)
        fun _ => guardedSafeS_pure_true _

theorem guardedSafeS_onAnswer (qep : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ))) :
    SimSafeS PQ Pt ℓ (onAnswer (qep := qep) Q w isDel ci? T pq' res) := by
  unfold onAnswer
  cases res with
  | none => exact guardedSafeS_pure_true _
  | some rr =>
    cases rr with
    | rejected => exact guardedSafeS_pure_true _
    | accepted t i pm => exact guardedSafeS_onAccept qep Q w isDel t i _ ci? T pq'

theorem simShortInv_record {s : SimState PQ Pt ℓ} (hs : SimShortInv s)
    {s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8))} (htr₁ : s₁.trans = s.mir.trans)
    (R : Party) (m₀ : Plain ℓ) (isChall : Bool) (pq' : PQ) (pn' : BitVec 32)
    (c : Fig8C Pt) (hc8 : c.2.2.1.1.length + 8 < 2 ^ 32) :
    SimShortInv
      { s with
        mir := s₁.record 3 R () ⟨⟨R, s₁.epoch R, s₁.idx R + 1⟩, m₀, toWire c⟩ isChall,
        pq := Function.update s.pq R pq',
        pn := Function.update s.pn R pn',
        honest := (toWire c, c) :: s.honest } := by
  refine ⟨?_, ?_⟩
  · intro rec' hmem
    simp only [SM.GameState.record, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simpa [length_toWire_eq] using hc8
    · rw [htr₁] at hmem
      exact hs.1 rec' hmem
  · intro wc hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · dsimp only; omega
    · exact hs.2 wc hmem

theorem guardedSafeS_simSend (P : Params PQ PQC) (qep : ℕ)
    (R : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    SimSafeS PQ Pt ℓ (simSend (P := P) (qep := qep) R m₀ chal r) := by
  unfold simSend SM.transmitQuery SM.challQuery liftQ putS
  refine guardedSafeS_get_bind fun s hs => ?_
  split
  · exact guardedSafeS_pure_true none
  · cases hep : s.mir.epMgmt 3 qep R r.isSome with
    | none => exact guardedSafeS_pure_true none
    | some s₁ =>
      have htr₁ : s₁.trans = s.mir.trans := epMgmt_trans_eq hep
      dsimp only
      split
      · exact guardedSafeS_pure_true none
      · cases r with
        | some rq =>
          simp only [pure_bind]
          refine guardedSafeS_bind_true
            (fun s' hs' => (guardedSafeS_coin_sim (BitVec 256) s' hs').map (R := fun p => SimShortInv p.2)
              (Prod.map some id) fun _ hp => hp)
            fun rc => ?_
          rcases mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with _ | ⟨pq', pub⟩
          · exact guardedSafeS_pure_true none
          · dsimp only
            cases chal with
            | none =>
              refine guardedSafeS_bind_query not_false fun res hres => ?_
              cases res with
              | none => exact guardedSafeS_pure_true none
              | some c =>
                exact guardedSafeS_bind_true
                  (guardedSafeS_set_true _ fun _ _ => simShortInv_record hs htr₁ R m₀ false pq' _ c (hres c rfl))
                  fun _ => guardedSafeS_pure_true _
            | some m₁ =>
              refine guardedSafeS_bind_query not_false fun res hres => ?_
              cases res with
              | none => exact guardedSafeS_pure_true none
              | some c =>
                exact guardedSafeS_bind_true
                  (guardedSafeS_set_true _ fun _ _ => simShortInv_record hs htr₁ R m₀ true pq' _ c (hres c rfl))
                  fun _ => guardedSafeS_pure_true _
        | none =>
          refine guardedSafeS_bind_true (guardedSafeS_coin_sim PQC) fun rq => ?_
          simp only [pure_bind]
          rcases mkPub (P := P) s R rq
              (if s₁.epoch R ≠ s.mir.epoch R then BitVec.ofNat 32 (s.mir.idx R - 1) else s.pn R) with _ | ⟨pq', pub⟩
          · exact guardedSafeS_pure_true none
          · dsimp only
            cases chal with
            | none =>
              refine guardedSafeS_bind_query not_false fun res hres => ?_
              cases res with
              | none => exact guardedSafeS_pure_true none
              | some c =>
                exact guardedSafeS_bind_true
                  (guardedSafeS_set_true _ fun _ _ => simShortInv_record hs htr₁ R m₀ false pq' _ c (hres c rfl))
                  fun _ => guardedSafeS_pure_true _
            | some m₁ =>
              refine guardedSafeS_bind_query not_false fun res hres => ?_
              cases res with
              | none => exact guardedSafeS_pure_true none
              | some c =>
                exact guardedSafeS_bind_true
                  (guardedSafeS_set_true _ fun _ _ => simShortInv_record hs htr₁ R m₀ true pq' _ c (hres c rfl))
                  fun _ => guardedSafeS_pure_true _

private theorem guardedSafeS_simRecv (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (R : Party) (w : List (BitVec 8)) (isDel : Bool) :
    SimSafeS PQ Pt ℓ (simRecv (P := P) (encT := encT) (decT := decT) (qep := qep) (k := k) R w isDel) := by
  unfold simRecv
  refine guardedSafeS_get_bind fun s hs => ?_
  dsimp only
  refine simSafeS_ite_pure fun _ => ?_
  refine simSafeS_ite_pure fun hw2 => ?_
  refine simSafeS_ite_pure fun hw3 => ?_
  refine simSafeS_ite_pure fun hw4 => ?_
  rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, rest⟩
  · exact guardedSafeS_pure_true (some SM.RecvResult.rejected)
  · have hwlen : w.length < 2 ^ 32 := by
      cases isDel with
      | true =>
        rcases htr : s.mir.inTransit R.other w with _ | rec'
        · simp [htr] at hw2
        · obtain ⟨hmem, rfl⟩ := inTransit_mem_and_ct htr
          exact hs.1 rec' hmem
      | false =>
        simp only [Bool.not_false, Bool.true_and, Bool.or_eq_true, Bool.not_eq_true',
          not_or, Bool.not_eq_false] at hw3
        have hadm := hw3.2
        unfold ratchetKeyAdmissible at hadm
        simp only [hw4, ↓reduceIte, hparse, Bool.and_eq_true, decide_eq_true_eq] at hadm
        exact hadm.1
    have hser : (w.take (w.length - 8)).length < 2 ^ 32 := by
      rw [List.length_take]; omega
    dsimp only
    refine simSafeS_ite_pure fun _ => ?_
    rcases P.spqr.recv (s.pq R) h.pqRatchet with _ | ⟨pq', salt⟩
    · exact guardedSafeS_pure_true (some SM.RecvResult.rejected)
    · dsimp only
      have hmkC : ∀ (t : ℕ) (To : Option Pt),
          (match (s.honest.find? fun (wc : List (BitVec 8) × Fig8C Pt) =>
               wc.1 == w && Party.senderOf wc.2.1.1 == R.other).map (fun (wc : List (BitVec 8) × Fig8C Pt) => wc.2) with
           | some (c : Fig8C Pt) =>
             if c.2.2.2 = effectiveHkdfSalt32 salt then c
             else ((t, To), (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))
           | none =>
             ((t, To), (h.counter.toNat + 1, ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))).2.2.1.1.length < 2 ^ 32 := by
        intro t To
        rcases hfind : s.honest.find? (fun (wc : List (BitVec 8) × Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == R.other) with _ | wc
        · exact hser
        · simp only [Option.map]
          split
          · exact hs.2 wc (List.mem_of_find?_eq_some hfind)
          · exact hser
      cases (s.chains R).findIdx? (fun g => g.key == some h.senderRatchetKey) with
      | some ci =>
        dsimp only
        refine simSafeS_ite_pure fun _ => ?_
        exact guardedSafeS_bind_true (guardedSafeS_fwd R _ (hmkC _ _)) fun res =>
          guardedSafeS_onAnswer qep R w isDel (some ci) h.senderRatchetKey pq' res
      | none =>
        dsimp only
        refine simSafeS_ite_pure fun _ => ?_
        refine simSafeS_ite_pure fun _ => ?_
        refine simSafeS_ite
          (guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => ⟨hs.1, hs.2⟩) fun _ => ?_) ?_ <;>
        · split
          · refine simSafeS_ite ?_ ?_
            · refine simSafeS_ite ?_
                (guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ hs' => ⟨hs'.1, hs'.2⟩)
                  fun _ => guardedSafeS_pure_true none)
              cases decT h.senderRatchetKey with
              | none =>
                exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ hs' => ⟨hs'.1, hs'.2⟩)
                  fun _ => guardedSafeS_pure_true none
              | some T =>
                refine guardedSafeS_bind_true (guardedSafeS_fwd R _ (hmkC _ _)) fun _ => ?_
                exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ hs' => ⟨hs'.1, hs'.2⟩)
                  fun _ => guardedSafeS_pure_true none
            · dsimp only [liftQ, SM.transmitQuery]
              refine guardedSafeS_bind_query not_false fun _ _ => ?_
              cases decT h.senderRatchetKey with
              | none =>
                exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ hs' => ⟨hs'.1, hs'.2⟩)
                  fun _ => guardedSafeS_pure_true none
              | some T =>
                refine guardedSafeS_bind_true (guardedSafeS_fwd R _ (hmkC _ _)) fun _ => ?_
                exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ hs' => ⟨hs'.1, hs'.2⟩)
                  fun _ => guardedSafeS_pure_true none
          · refine simSafeS_ite_pure fun _ => ?_
            cases decT h.senderRatchetKey with
            | none => exact guardedSafeS_pure_true (some SM.RecvResult.rejected)
            | some T =>
              exact guardedSafeS_bind_true (guardedSafeS_fwd R _ (hmkC _ _)) fun res =>
                guardedSafeS_onAnswer qep R w isDel none h.senderRatchetKey pq' res

private theorem guardedSafeS_simCorr (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (R : Party) :
    SimSafeS PQ Pt ℓ (simCorr (P := P) (Dh := Dh) (encT := encT) R) := by
  unfold simCorr liftQ SM.corrQuery putS
  refine guardedSafeS_get_bind fun s hs => ?_
  dsimp only
  refine simSafeS_ite_pure fun _ => ?_
  refine guardedSafeS_bind_query not_false fun res _ => ?_
  cases res with
  | none => exact guardedSafeS_pure_true none
  | some st =>
    dsimp only
    exact guardedSafeS_bind_true
      (guardedSafeS_set_true _ fun _ _ => ⟨hs.1, hs.2⟩)
      fun _ => guardedSafeS_pure_true _

private theorem guardedSafeS_guard {α : Type} (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option α))
    (hx : SimSafeS PQ Pt ℓ x) :
    GuardedSafeS
      (smRespShort (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smRecvLong (St := Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (SimShortInv (PQ := PQ) (Pt := Pt) (ℓ := ℓ))
      (fun _ s => True ∧ SimShortInv s)
      (LibsignalSim.guard x) := by
  unfold LibsignalSim.guard
  refine guardedSafeS_get_bind fun s _ => ?_
  split
  · exact guardedSafeS_pure none fun _ hs' => ⟨trivial, hs'⟩
  · exact fun s' hs' => (hx s' hs').mono fun _ hp => ⟨trivial, hp⟩

theorem simRun_guardedSMShort_proof (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    GuardedSMShort (LibsignalSim.simRun P Dh encT decT qep k A) := by
  unfold GuardedSMShort LibsignalSim.simRun
  refine (GuardedSafePost.liftComp_unif hQu_smRecvLong ($ᵗ BitVec 256)).bind fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  have hsim : GuardedSafePost smRespShort smRecvLong (fun r => SimShortInv r.2)
      ((simulateQ (simImpl P Dh encT decT qep k) A).run
        (initSim (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))) := by
    refine GuardedSafePost.simulateQ_run (GuardedSafePost.true_of_false A) ?_
      (simShortInv_initSim _ _)
    rintro (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, w⟩) | ⟨R, w⟩) | R)) _
    · exact fun s hs =>
        (GuardedSafePost.query (hQu_smRecvLong n)).bind fun a _ => GuardedSafePost.pure ⟨trivial, hs⟩
    · exact guardedSafeS_guard _ (guardedSafeS_simSend P qep R m none r)
    · exact guardedSafeS_guard _ (guardedSafeS_simSend P qep R m₀ (some m₁) r)
    · exact guardedSafeS_guard _ (guardedSafeS_simRecv P encT decT qep k R w true)
    · exact guardedSafeS_guard _ (guardedSafeS_simRecv P encT decT qep k R w false)
    · exact guardedSafeS_guard _ (guardedSafeS_simCorr P Dh encT R)
  refine (hsim.map (R := fun _ => True) Prod.fst fun _ _ => trivial).bind fun b' _ => ?_
  cases k with
  | none => exact GuardedSafePost.pure trivial
  | some _ => exact GuardedSafePost.liftComp_unif hQu_smRecvLong ($ᵗ Bool)

end SimGuarded

section RedGuarded

variable {St Msg Coins T : Type} [DecidableEq Msg] [DecidableEq T]

theorem guardedSafeS_thm1_simOracles (Δ qep : ℕ)
    (o : (SM.spec St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (ho : ¬ smRecvLong (St := St) (Msg := Msg) (Coins := Coins) (T := T) (.inr o)) :
    GuardedSafeS smRespShort smRecvLong
      (fun (_ : Thm1.Mirror Msg (Header T × (ℕ × LibsignalCiphertextWithSalt32))) => True)
      (fun a _ => smRespShort (St := St) (Msg := Msg) (Coins := Coins) (T := T) (.inr o) a ∧ True)
      (Thm1.simOracles (St := St) (Coins := Coins) Δ qep (fun _ => none) none o) := by
  rcases o with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change GuardedSafeS _ _ _ _ (Thm1.simTransmit (St := St) Δ qep (P, m, r))
    unfold Thm1.simTransmit SM.transmitQuery
    refine guardedSafeS_get_bind fun s _ => ?_
    refine guardedSafeS_bind_query (by simp [smRecvLong]) fun res hres => ?_
    cases res <;> cases s.epMgmt Δ qep P r.isSome
    all_goals first
      | exact guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
      | exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
          guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
  · change GuardedSafeS _ _ _ _ (Thm1.simChall (St := St) Δ qep (fun _ => none) none (P, m₀, m₁, r))
    unfold Thm1.simChall Thm1.simSend SM.transmitQuery
    refine guardedSafeS_get_bind fun s _ => ?_
    cases s.epMgmt Δ qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      dsimp only
      cases s₁.safeCh Δ P
      · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine guardedSafeS_bind_query (by simp [smRecvLong]) fun res hres => ?_
        cases res
        · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
            guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
  · change GuardedSafeS _ _ _ _ (Thm1.simDeliver (St := St) (Coins := Coins) (P, c))
    unfold Thm1.simDeliver SM.deliverQuery
    refine guardedSafeS_get_bind fun s _ => ?_
    refine guardedSafeS_bind_query ho fun res _ => ?_
    cases res with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    | some rr =>
      cases rr <;> cases s.inTransit P.other c
      all_goals first
        | exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
        | exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
            guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
  · change GuardedSafeS _ _ _ _ (Thm1.simInject (St := St) (Coins := Coins) (P, c))
    unfold Thm1.simInject SM.injectQuery
    refine guardedSafeS_get_bind fun _ _ => ?_
    refine guardedSafeS_bind_query ho fun res _ => ?_
    cases res with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    | some rr =>
      cases rr
      · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
      · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
          guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
  · change GuardedSafeS _ _ _ _ (Thm1.simCorr (St := St) (Msg := Msg) (Coins := Coins) P)
    unfold Thm1.simCorr SM.corrQuery
    refine guardedSafeS_get_bind fun _ _ => ?_
    refine guardedSafeS_bind_query (by simp [smRecvLong]) fun res _ => ?_
    cases res <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]
    · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
    · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
        guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩

theorem challSim_guardedSMShort_proof (Δ qep : ℕ)
    (A : SM.Adversary St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32)))
    (hA : GuardedSMShort A) :
    GuardedSMShort (Thm1.challSim Δ qep A) := by
  unfold GuardedSMShort at hA ⊢
  dsimp only [Thm1.challSim, Thm1.simRun]
  rw [bind_assoc]
  refine (GuardedSafePost.liftComp_unif hQu_smRecvLong ($ᵗ Bool)).bind fun b _ => ?_
  rw [bind_assoc, StateT.run'_eq]
  have hsim : GuardedSafePost smRespShort smRecvLong (fun _ => True)
      ((simulateQ (Thm1.simImpl Δ qep (fun _ => none) none) A).run
        ({ st := fun _ => (), b } : Thm1.Mirror Msg (Header T × (ℕ × LibsignalCiphertextWithSalt32)))) := by
    refine GuardedSafePost.simulateQ_run (I := fun _ => True) hA ?_ trivial
    rintro (u | o) ho
    · exact guardedSafeS_lift_query (hQu_smRecvLong u)
    · exact guardedSafeS_thm1_simOracles Δ qep o ho
  exact (hsim.map (P := fun _ => True) (R := fun _ => True) Prod.fst fun _ _ => trivial).bind
    fun _ _ => GuardedSafePost.pure (P := fun _ => True) trivial

theorem guardedSafeS_thmB_simOracles (Δ qep i : ℕ) (blank : Msg → Msg)
    (o : (SM.spec St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (ho : ¬ smRecvLong (St := St) (Msg := Msg) (Coins := Coins) (T := T) (.inr o)) :
    GuardedSafeS smRespShort smRecvLong
      (fun (_ : Thm1.Mirror Msg (Header T × (ℕ × LibsignalCiphertextWithSalt32))) => True)
      (fun a _ => smRespShort (St := St) (Msg := Msg) (Coins := Coins) (T := T) (.inr o) a ∧ True)
      (ThmB.simOracles (St := St) (Coins := Coins) Δ qep
        (fun t => if t < i then some blank else none) (some (i, blank)) o) := by
  rcases o with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
  · change GuardedSafeS _ _ _ _ (ThmB.simTransmit (St := St) Δ qep (P, m, r))
    unfold ThmB.simTransmit SM.transmitQuery
    refine guardedSafeS_get_bind fun s _ => ?_
    refine guardedSafeS_bind_query (by simp [smRecvLong]) fun res hres => ?_
    cases res <;> cases s.epMgmt Δ qep P r.isSome
    all_goals first
      | exact guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
      | exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
          guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
  · change GuardedSafeS _ _ _ _ (ThmB.simChall (St := St) Δ qep
      (fun t => if t < i then some blank else none) (some (i, blank)) (P, m₀, m₁, r))
    unfold ThmB.simChall ThmB.simSend SM.transmitQuery SM.challQuery
    refine guardedSafeS_get_bind fun s _ => ?_
    cases s.epMgmt Δ qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      dsimp only
      cases s₁.safeCh Δ P
      · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases hti : s₁.epoch P = i
        · simp only [hti, ↓reduceIte]
          refine guardedSafeS_bind_query (by simp [smRecvLong]) fun res hres => ?_
          cases res
          · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
          · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
        · simp only [hti, ↓reduceIte]
          refine guardedSafeS_bind_query (by simp [smRecvLong]) fun res hres => ?_
          cases res
          · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
          · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨hres, trivial⟩
  · change GuardedSafeS _ _ _ _ (ThmB.simDeliver (St := St) (Coins := Coins) (P, c))
    unfold ThmB.simDeliver SM.deliverQuery
    refine guardedSafeS_get_bind fun s _ => ?_
    refine guardedSafeS_bind_query ho fun res _ => ?_
    cases res with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    | some rr =>
      cases rr <;> cases s.inTransit P.other c
      all_goals first
        | exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
        | exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
            guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
  · change GuardedSafeS _ _ _ _ (ThmB.simInject (St := St) (Coins := Coins) (P, c))
    unfold ThmB.simInject SM.injectQuery
    refine guardedSafeS_get_bind fun _ _ => ?_
    refine guardedSafeS_bind_query ho fun res _ => ?_
    cases res with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    | some rr =>
      cases rr
      · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
      · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
          guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
  · change GuardedSafeS _ _ _ _ (ThmB.simCorr (St := St) (Msg := Msg) (Coins := Coins) P)
    unfold ThmB.simCorr SM.corrQuery
    refine guardedSafeS_get_bind fun _ _ => ?_
    refine guardedSafeS_bind_query (by simp [smRecvLong]) fun res _ => ?_
    cases res <;> simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]
    · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
    · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ =>
        guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩

theorem privRedB_guardedSMShort_proof (Δ qep i : ℕ) (blank : Msg → Msg)
    (A : SM.Adversary St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32)))
    (hA : GuardedSMShort A) :
    GuardedSMShort (ThmB.privRedB Δ qep i blank A) := by
  unfold GuardedSMShort at hA ⊢
  dsimp only [ThmB.privRedB, ThmB.simRun]
  rw [bind_assoc]
  refine (GuardedSafePost.liftComp_unif hQu_smRecvLong ($ᵗ Bool)).bind fun b _ => ?_
  rw [bind_assoc, StateT.run'_eq]
  have hsim : GuardedSafePost smRespShort smRecvLong (fun _ => True)
      ((simulateQ (ThmB.simImpl Δ qep (fun t => if t < i then some blank else none) (some (i, blank))) A).run
        ({ st := fun _ => (), b } : Thm1.Mirror Msg (Header T × (ℕ × LibsignalCiphertextWithSalt32)))) := by
    refine GuardedSafePost.simulateQ_run (I := fun _ => True) hA ?_ trivial
    rintro (u | o) ho
    · exact guardedSafeS_lift_query (hQu_smRecvLong u)
    · exact guardedSafeS_thmB_simOracles Δ qep i blank o ho
  exact (hsim.map (P := fun _ => True) (R := fun _ => True) Prod.fst fun _ _ => trivial).bind
    fun _ _ => GuardedSafePost.pure (P := fun _ => True) trivial

end RedGuarded

end GuardedShort

end CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
