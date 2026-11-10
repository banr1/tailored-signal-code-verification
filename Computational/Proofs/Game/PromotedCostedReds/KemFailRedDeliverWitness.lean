/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
public import Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
public import Computational.Proofs.E2E.Dsl.SpqrSimChain
public import Computational.Proofs.E2E.Dsl.ClampsLossless
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync

/-!
# Atomic SPQR V1 Braid-Tracker Delivery Step

Proves `KemTrackDeliverInv` preservation and exact `.eval` lemmas for `kemTrackDeliverAtomicE` and
`kemOnDeliverPostAtomicE`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness

open _root_.ReductionDsl (Ty Env Expr
  atomicSig atomicSessionOps partyToBool recvResultT recvResultEnc spqrMsgPayloadSuffix)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (RecvResult)
open CryptoGames.Ratchet.LibsignalSim
  (SimKemFailTrack simStepKemFailSend simStepKemFailDeliver kemTrackEnc)
open CryptoGames.LibsignalSM.Proofs.Refinement
  (KemFailTrackState initKemFailTrack stepKemFailSend stepKemFailDeliver)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes)

export Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (kemCoinsT kemSentEntryT kemTrackT kemCoinsAtomicEnc kemTrackAtomicEnc)
export Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (b64Take48ToB32E listNthOptB findRevHonestIdxE kemTrackDeliverAtomicE kemOnDeliverPostAtomicE)
export Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (b64Take48ToB32E_eval b64Take48ToB32E_cost b64Take48ToB32E_descBits_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (listNthOptB_eval listNthOptB_cost listNthOptB_descBits_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (findRevHonestIdxE_eval findRevHonestIdxE_cost findRevHonestIdxE_descBits_le)
export Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitnessSub
  (kemTrackDeliverAtomicE_cost kemTrackDeliverAtomicE_descBits_le
   kemOnDeliverPostAtomicE_cost kemOnDeliverPostAtomicE_descBits_le)



/-- Braid-tracker invariant ensuring lossless `V1State` and `SimBraidMsg` roundtrips across
deliveries. -/
structure KemTrackDeliverInv (F : ShaCompress) (K : MlKem) (L : ℕ)
    (tr : SimKemFailTrack F) : Prop where
  sentB_len : tr.sentB.length ≤ L
  bOk : ∀ Q : Party, CryptoVerification.SpqrV1Sync.SendTotal.BOkTight (tr.st Q)
  sentB_deser : ∀ mc ∈ tr.sentB,
    CryptoVerification.LibsignalSpqrV1.Message.deserialize
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi mc.1.epoch (spqrMsgPayloadSuffix mc.1) = .ok mc.1

theorem KemTrackDeliverInv.mono {F : ShaCompress} {K : MlKem} {L L' : ℕ}
    {tr : SimKemFailTrack F} (h : KemTrackDeliverInv F K L tr) (hLL : L ≤ L') :
    KemTrackDeliverInv F K L' tr :=
  ⟨h.sentB_len.trans hLL, h.bOk, h.sentB_deser⟩

theorem kemTrackDeliverInv_init (F : ShaCompress) (K : MlKem) (L : ℕ) (pqrKey : BitVec 256) :
    KemTrackDeliverInv F K L (kemTrackEnc (initKemFailTrack F pqrKey)) := by
  refine ⟨Nat.zero_le L, ?_, ?_⟩
  · intro Q
    have hlen : (CryptoGames.HMAC.keyToBytes32 pqrKey).length = 32 := by
      simp [CryptoGames.HMAC.keyToBytes32]
    cases Q with
    | A =>
      obtain ⟨stA, hinitA, hbokA, -⟩ :=
        CryptoVerification.SpqrV1Sync.SendTotal.st_bInit_tight F (dir := .a2b) hlen
      change Except.ok ((kemTrackEnc (initKemFailTrack F pqrKey)).st .A) = Except.ok stA at hinitA
      cases hinitA
      exact hbokA
    | B =>
      obtain ⟨stB, hinitB, hbokB, -⟩ :=
        CryptoVerification.SpqrV1Sync.SendTotal.st_bInit_tight F (dir := .b2a) hlen
      change CryptoVerification.LibsignalSpqrV1.States.init_b
        CryptoVerification.LibsignalSpqrV1.spqrPolyApi
        (CryptoVerification.LibsignalSpqrV1.spqrAuthApi F)
        (CryptoGames.HMAC.keyToBytes32 pqrKey) = Except.ok stB at hinitB
      simp only [CryptoVerification.LibsignalSpqrV1.States.init_b,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.new,
        CryptoVerification.LibsignalSpqrV1.HEADER_SIZE,
        CryptoVerification.LibsignalSpqrV1.AUTHENTICATOR_MACSIZE,
        CryptoVerification.LibsignalSpqrV1.spqrPolyApi,
        CryptoVerification.SpqrV1Sync.InSync.decoderNew_eq 96 (by decide),
        Except.mapError] at hinitB
      change Except.ok ((kemTrackEnc (initKemFailTrack F pqrKey)).st .B) = Except.ok stB at hinitB
      cases hinitB
      exact hbokB
  · intro mc hmc
    cases hmc

theorem kemTrackDeliverInv_stepSim (F : ShaCompress) (K : MlKem) (L : ℕ)
    (tr : SimKemFailTrack F) (Q : Party) (j : ℕ)
    (hInv : KemTrackDeliverInv F K L tr) :
    KemTrackDeliverInv F K L (simStepKemFailDeliver F K tr Q j) := by
  unfold simStepKemFailDeliver
  cases hj : tr.sentB[j]? with
  | none => exact hInv
  | some mc =>
    rcases mc with ⟨m, ctr⟩
    dsimp only
    cases hrecv : (tr.st Q).recv K m with
    | error _ => exact hInv
    | ok out =>
      rcases out with ⟨key, st'⟩
      have hbok' : ∀ Q' : Party,
          CryptoVerification.SpqrV1Sync.SendTotal.BOkTight (Function.update tr.st Q st' Q') := by
        intro Q'
        by_cases hQ : Q' = Q
        · subst hQ
          rw [Function.update_self]
          cases hek : CryptoVerification.SpqrV1Sync.SendTotal.isEkSide (tr.st Q') with
          | true =>
            exact CryptoVerification.SpqrV1Sync.SendTotal.st_bRecvEk_tight
              F K hek (hInv.bOk Q') hrecv
          | false =>
            exact CryptoVerification.SpqrV1Sync.SendTotal.st_bRecvCt_tight
              F K hek (hInv.bOk Q') hrecv
        · rw [Function.update_of_ne hQ]
          exact hInv.bOk Q'
      dsimp only
      split_ifs with hm
      · cases tr.c <;> exact ⟨hInv.sentB_len, hbok', hInv.sentB_deser⟩
      · exact ⟨hInv.sentB_len, hbok', hInv.sentB_deser⟩

theorem kemTrackDeliverInv_step (F : ShaCompress) (K : MlKem) (L : ℕ)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ)
    (hInv : KemTrackDeliverInv F K L (kemTrackEnc tr)) :
    KemTrackDeliverInv F K L (kemTrackEnc (stepKemFailDeliver F K tr Q j)) := by
  rw [← CryptoGames.Ratchet.LibsignalSim.simStepKemFailDeliver_kemTrackEnc]
  exact kemTrackDeliverInv_stepSim F K L (kemTrackEnc tr) Q j hInv

theorem kemTrackDeliverInv_stepSendSim (F : ShaCompress) (K : MlKem) (L : ℕ)
    (tr : SimKemFailTrack F) (Q : Party) (r : BitVec 512)
    (hInv : KemTrackDeliverInv F K L tr) :
    KemTrackDeliverInv F K (L + 1) (simStepKemFailSend F K tr Q r) := by
  unfold simStepKemFailSend
  dsimp only
  cases hsend : (tr.st Q).send K (CryptoVerification.LibsignalSpqrV1.coinBytes r) with
  | error _ =>
    exact ⟨Nat.le_trans hInv.sentB_len (Nat.le_succ L), hInv.bOk, hInv.sentB_deser⟩
  | ok p =>
    rcases p with ⟨⟨m, key, st'⟩, tape'⟩
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      exact Nat.add_le_add_right hInv.sentB_len 1
    · intro Q'
      dsimp only
      by_cases hQ : Q' = Q
      · subst hQ
        rw [Function.update_self]
        exact CryptoVerification.SpqrV1Sync.SendTotal.st_bSendClosed_tight F K (hInv.bOk Q') hsend
      · rw [Function.update_of_ne hQ]
        exact hInv.bOk Q'
    · intro mc hmc
      rw [List.mem_append, List.mem_singleton] at hmc
      rcases hmc with hmc | rfl
      · exact hInv.sentB_deser mc hmc
      · dsimp only
        obtain ⟨-, -, hp, -⟩ :=
          CryptoVerification.SpqrV1Sync.TopSync.send_facts F K (tr.st Q) st'
            (CryptoVerification.LibsignalSpqrV1.coinBytes r) tape' m key hsend
        obtain ⟨-, hsfx⟩ :=
          Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffix_lossless m
        have hsfxEq : spqrMsgPayloadSuffix m =
            (CryptoVerification.LibsignalSpqrV1.MessageType.from_payload m.payload).toU8 ::
              CryptoVerification.SpqrV1Sync.Codec.payloadBytes m.payload := by
          change CryptoVerification.E2E.Costed.spqrMsgPayloadSuffix m = _
          rw [hsfx]
          rcases m with ⟨ep, pay⟩
          unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffixRaw
            CryptoVerification.SpqrV1Sync.Codec.payloadBytes
          cases pay <;> rfl
        rw [hsfxEq]
        have hdes := CryptoVerification.SpqrV1Sync.Codec.deserialize_payload
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi
          CryptoVerification.SpqrV1Sync.Codec.spqrPolyApi_mkChunk m.epoch m.payload hp
        cases m
        exact hdes

theorem kemTrackDeliverInv_stepSend (F : ShaCompress) (K : MlKem) (L : ℕ)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512)
    (hInv : KemTrackDeliverInv F K L (kemTrackEnc tr)) :
    KemTrackDeliverInv F K (L + 1) (kemTrackEnc (stepKemFailSend F K tr Q r)) := by
  rw [← CryptoGames.Ratchet.LibsignalSim.simStepKemFailSend_kemTrackEnc]
  exact kemTrackDeliverInv_stepSendSim F K L (kemTrackEnc tr) Q r hInv

section EvalCostDesc

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

omit [SampleableType Pt] in
private theorem eval_caseOpt {Γ : List (Ty ASig)} {a b : Ty ASig}
    (e : Expr AOps Γ (.opt a)) (n : Expr AOps Γ b) (s : Expr AOps (a :: Γ) b) (ρ : Env Γ) :
    (Expr.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | none => n.eval ρ
      | some v => s.eval (Env.cons v ρ) := by
  simp only [Expr.eval]
  cases e.eval ρ <;> rfl

theorem kemTrackDeliverAtomicE_eval_sim (L : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (jE : Expr AOps Γ .nat)
    (ρ : Env Γ) (tr : SimKemFailTrack C.F) (Q : Party) (j : ℕ)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr)
    (hq : qBE.eval ρ = partyToBool Q)
    (hj : jE.eval ρ = j)
    (hInv : KemTrackDeliverInv C.F K L tr) :
    (kemTrackDeliverAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L trE qBE jE).eval ρ =
    kemTrackAtomicEnc (simStepKemFailDeliver C.F K tr Q j) := by
  unfold kemTrackDeliverAtomicE
  rw [SimFig8State.eval_eLet]
  have hp0 : (Expr.pair trE (.pair qBE jE)).eval ρ =
      (kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) tr, (partyToBool Q, j)) := by
    simp only [Expr.eval, htr, hq, hj]
  rw [hp0]
  set t0 : Ty ASig := .prod (kemTrackT ℓ Pt) (.prod .bool .nat)
  set ρ0 : Env (t0 :: Γ) :=
    Env.cons (t := t0) (kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) tr, (partyToBool Q, j)) ρ
  have hnth : (listNthOptB (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L
      (.fst (.snd (.snd (.snd (.fst .v0))))) (.snd (.snd .v0))).eval ρ0 =
      (tr.sentB[j]?).map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr)) := by
    rw [listNthOptB_eval L _ _ ρ0
      (tr.sentB.map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr))) j rfl rfl
      (by simp only [List.length_map]; exact hInv.sentB_len)]
    exact List.getElem?_map
  rw [eval_caseOpt, hnth]
  unfold simStepKemFailDeliver
  cases hj_get : tr.sentB[j]? with
  | none => rfl
  | some mc =>
    rcases mc with ⟨m, ctr⟩
    dsimp only [Option.map]
    set ρ1 : Env (kemSentEntryT ℓ Pt :: t0 :: Γ) :=
      Env.cons (t := kemSentEntryT ℓ Pt) ((m.epoch, spqrMsgPayloadSuffix m), ctr) ρ0
    have hm_mem : (m, ctr) ∈ tr.sentB := List.mem_of_getElem? hj_get
    have hdes := hInv.sentB_deser (m, ctr) hm_mem
    have hsfx_len : (spqrMsgPayloadSuffix m).length ≤ 48 := by
      obtain ⟨hlen43, hsfx_eq⟩ :=
        Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffix_lossless m
      have hEq : spqrMsgPayloadSuffix m = CryptoVerification.E2E.Costed.spqrMsgPayloadSuffix m := rfl
      rw [hEq, hsfx_eq]
      exact Nat.le_trans hlen43 (by decide)
    have hmSuf1 : (b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.snd (.fst .v0))).eval ρ1 = spqrMsgPayloadSuffix m :=
      b64Take48ToB32E_eval _ ρ1 (spqrMsgPayloadSuffix m) rfl hsfx_len
    have hrecvOut : (Expr.snd (.snd (SimFig8State.sOpSpqr (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) .spqrBraidRecv
        (.pair (.ite (.fst (.snd .v1))
          (.snd (.fst (.snd (.snd (.fst .v1)))))
          (.fst (.fst (.snd (.snd (.fst .v1))))))
          (.pair (.fst (.fst .v0)) (b64Take48ToB32E (.snd (.fst .v0)))))))).eval ρ1 =
        (CryptoVerification.E2E.Costed.spqrBraidRecvEval (ℓ := ℓ) C.F K
          (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw (tr.st Q).into_pb)
          m.epoch (spqrMsgPayloadSuffix m)).2.2 := by
      change ((SimFig8State.sOpSpqr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) .spqrBraidRecv _).eval ρ1).2.2 = _
      rw [SimFig8State.eval_sOpSpqr]
      simp only [Expr.eval, hmSuf1]
      cases Q <;> rfl
    rw [eval_caseOpt, hrecvOut,
      Computational.Proofs.E2E.Dsl.SpqrSimChain.spqrBraidRecvEval_of_bOkTight
        (ℓ := ℓ) C.F K (tr.st Q) (hInv.bOk Q) m.epoch (spqrMsgPayloadSuffix m), hdes]
    dsimp only
    cases hrecv : (tr.st Q).recv K m with
    | error err =>
      cases err <;> rfl
    | ok out =>
      rcases out with ⟨key, st'⟩
      dsimp only
      set t2 : Ty ASig :=
        .prod (.opt (.prod (_root_.ReductionDsl.U64 (ℓ := ℓ) (Pt := Pt))
          (_root_.ReductionDsl.BV256 (ℓ := ℓ) (Pt := Pt))))
          (_root_.ReductionDsl.B (ℓ := ℓ) (Pt := Pt) 32)
      set ρ2 : Env (t2 :: kemSentEntryT ℓ Pt :: t0 :: Γ) := Env.cons (t := t2)
        (key.map (fun es => (es.epoch, CryptoGames.HKDF.bytesToKey32 es.secret)),
          CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw st'.into_pb) ρ1
      have hmSuf2 : (b64Take48ToB32E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (.snd (.fst .v1))).eval ρ2 = spqrMsgPayloadSuffix m :=
        b64Take48ToB32E_eval _ ρ2 (spqrMsgPayloadSuffix m) rfl hsfx_len
      have hNoneIff :
          ((m.epoch == tr.e + 1#64) && (spqrMsgPayloadSuffix m == [0#8])) =
            decide (m = { epoch := tr.e + 1#64, payload := .none }) := by
        by_cases hm_eq : m = { epoch := tr.e + 1#64, payload := .none }
        · subst hm_eq
          have hsfxNone :
              spqrMsgPayloadSuffix (P := CryptoVerification.LibsignalSpqrV1.spqrPolyApi)
                { epoch := tr.e + 1#64, payload := .none } = [0#8] := rfl
          simp [hsfxNone]
        · cases hep : (m.epoch == tr.e + 1#64)
          · simp [hm_eq]
          · cases hsfx0 : (spqrMsgPayloadSuffix m == [0#8])
            · simp [hm_eq]
            · exfalso
              rw [eq_of_beq hep, eq_of_beq hsfx0] at hdes
              have hdes0 : CryptoVerification.LibsignalSpqrV1.Message.deserialize
                  CryptoVerification.LibsignalSpqrV1.spqrPolyApi (tr.e + 1#64) [0#8] =
                  .ok { epoch := tr.e + 1#64, payload := .none } := by
                simp [CryptoVerification.LibsignalSpqrV1.Message.deserialize,
                  CryptoVerification.LibsignalSpqrV1.MessageType.tryFromU8, bind, Except.bind]
              rw [hdes0] at hdes
              cases hdes
              exact hm_eq rfl
      simp only [SimFig8State.eval_sOpPure, _root_.ReductionDsl.AtomicPureOp.eval,
        Expr.eval, hmSuf2]
      simp only [Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, ρ2, ρ1, ρ0,
        kemTrackAtomicEnc, hNoneIff]
      by_cases hm_eq : m = { epoch := tr.e + 1#64, payload := .none }
      · simp only [hm_eq, decide_true, ↓reduceIte, Bool.true_and]
        cases tr.c <;> cases Q <;> rfl
      · simp only [hm_eq, decide_false, ↓reduceIte, Bool.false_and]
        cases tr.c <;> cases Q <;> rfl

theorem kemTrackDeliverAtomicE_eval (L : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool) (jE : Expr AOps Γ .nat)
    (ρ : Env Γ) (tr : KemFailTrackState C.F) (Q : Party) (j : ℕ)
    (htr : trE.eval ρ = kemTrackAtomicEnc (kemTrackEnc tr))
    (hq : qBE.eval ρ = partyToBool Q)
    (hj : jE.eval ρ = j)
    (hInv : KemTrackDeliverInv C.F K L (kemTrackEnc tr)) :
    (kemTrackDeliverAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L trE qBE jE).eval ρ =
    kemTrackAtomicEnc (kemTrackEnc (stepKemFailDeliver C.F K tr Q j)) := by
  rw [← CryptoGames.Ratchet.LibsignalSim.simStepKemFailDeliver_kemTrackEnc]
  exact kemTrackDeliverAtomicE_eval_sim L trE qBE jE ρ (kemTrackEnc tr) Q j htr hq hj hInv


theorem kemOnDeliverPostAtomicE_eval_sim (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt))
    (ρ : Env Γ) (Q : Party) (j? : Option ℕ) (rr? : Option (RecvResult (Plain ℓ)))
    (tr : SimKemFailTrack C.F)
    (hq : qBE.eval ρ = partyToBool Q)
    (hj : jOptE.eval ρ = j?)
    (hrr : rrOptE.eval ρ = rr?.map recvResultEnc)
    (htr : trE.eval ρ = kemTrackAtomicEnc tr)
    (hInv : KemTrackDeliverInv C.F K L tr) :
    (kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L qBE jOptE rrOptE trE).eval ρ =
    kemTrackAtomicEnc (
      match rr?, j? with
      | some (.accepted _ _ _), some j => simStepKemFailDeliver C.F K tr Q j
      | _, _ => tr) := by
  unfold kemOnDeliverPostAtomicE
  rw [SimFig8State.eval_eLet]
  have hp0 : (Expr.pair qBE (.pair jOptE (.pair rrOptE trE))).eval ρ =
      (partyToBool Q, (j?, (rr?.map (recvResultEnc (ℓ := ℓ) (Pt := Pt)),
        kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) tr))) := by
    simp only [Expr.eval, hq, hj, hrr, htr]
  rw [hp0]
  cases rr? with
  | none => rfl
  | some rr =>
    cases rr with
    | rejected => rfl
    | accepted t i m =>
      cases j? with
      | none => rfl
      | some j =>
        dsimp only [Option.map, recvResultEnc, Expr.eval,
          Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]
        exact kemTrackDeliverAtomicE_eval_sim L
          (.snd (.snd (.snd .v3))) (.fst .v3) .v0 _ tr Q j rfl rfl rfl hInv

theorem kemOnDeliverPostAtomicE_eval (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt))
    (ρ : Env Γ) (Q : Party) (j? : Option ℕ) (rr? : Option (RecvResult (Plain ℓ)))
    (tr : KemFailTrackState C.F)
    (hq : qBE.eval ρ = partyToBool Q)
    (hj : jOptE.eval ρ = j?)
    (hrr : rrOptE.eval ρ = rr?.map recvResultEnc)
    (htr : trE.eval ρ = kemTrackAtomicEnc (kemTrackEnc tr))
    (hInv : KemTrackDeliverInv C.F K L (kemTrackEnc tr)) :
    (kemOnDeliverPostAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) L qBE jOptE rrOptE trE).eval ρ =
    kemTrackAtomicEnc (kemTrackEnc (
      match rr?, j? with
      | some (.accepted _ _ _), some j => stepKemFailDeliver C.F K tr Q j
      | _, _ => tr)) := by
  rw [kemOnDeliverPostAtomicE_eval_sim L qBE jOptE rrOptE trE ρ Q j? rr? (kemTrackEnc tr)
    hq hj hrr htr hInv]
  cases rr? with
  | none => rfl
  | some rr =>
    cases rr with
    | rejected => rfl
    | accepted _ _ _ =>
      cases j? with
      | none => rfl
      | some j =>
        dsimp only
        rw [CryptoGames.Ratchet.LibsignalSim.simStepKemFailDeliver_kemTrackEnc]


end EvalCostDesc

end Computational.Proofs.Game.PromotedCostedReds.KemFailRedDeliverWitness
