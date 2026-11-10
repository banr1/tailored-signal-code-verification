/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TightSize -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg
import Computational.Proofs.E2E.Dsl.ClampsLossless

/-!
# Tracker Invariants and ML-KEM Evaluation Lemmas

Proves `KemTrackDeliverInv` preservation across tracker initialization, send, and deliver steps,
together with `.eval` characterizations for `issue1275FixEsC` and `honestExchangeFailsC`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  iterM bytesToWordLE spqrMsgPayloadSuffix
  atomicSig AtomicPureOp AtomicSpqrKemOp B BV256 BV512)
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.Ratchet.LibsignalSim (SimKemSeed SimKemEncRand SimKemCoins SimKemFailTrack
  simInitKemFailTrack simStepKemFailSend simStepKemFailDeliver)
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes coinBytes_length
  issue1275NeedsFlip swapAdjacentPairs flipEndiannessOfEncapsulationStateBytes
  potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (KemTrackOpEmbed kemCandVecToBv kemCandBvToVec
   boolOrE bytes2EqLitE issue1275ScanStepE swapPairsStep64E swapChunk64StepC
   issue1275FixEsC honestExchangeFailsC)

/-! ## `KemTrackDeliverInv` preservation -/

@[expose] def kemBridgeCoinsToSim : CryptoVerification.SpqrV1Sync.Braid.Coins → SimKemCoins
  | .init => .init
  | .seed s => .seed s
  | .both s r => .both s r

private theorem extractLsb'_zero_wordLE_cons (w : ℕ) (hw : 8 ≤ w) (b : BitVec 8) (acc : BitVec w) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have hiw : i < w := by omega
  simp [hi, hiw]

private theorem extractLsb'_succ_wordLE_cons (w : ℕ) (b : BitVec 8) (acc : BitVec w) (j : ℕ)
    (hjw : 8 * (j + 2) ≤ w) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' (8 * (j + 1)) 8 = acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < w := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToWordLE (w : ℕ) (bs : Bytes) (j : ℕ)
    (hj : j < bs.length) (hjw : 8 * (j + 1) ≤ w) :
    (bytesToWordLE w bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToWordLE] using extractLsb'_zero_wordLE_cons w (by omega) b (bytesToWordLE w rest)
    | succ j =>
      have hcons : bytesToWordLE w (b :: rest) =
          (bytesToWordLE w rest <<< 8) ||| b.zeroExtend w := rfl
      rw [hcons, extractLsb'_succ_wordLE_cons w b (bytesToWordLE w rest) j (by omega),
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem coinBytes_bytesToWordLE512 (bs : Bytes) (h : bs.length = 64) :
    coinBytes (bytesToWordLE 512 bs) = bs := by
  refine List.ext_getElem (by simp [coinBytes_length, h]) fun j _ h2 => ?_
  simp only [coinBytes, CryptoVerification.LibsignalAesCbc.toLEBytes, List.getElem_ofFn]
  exact extractLsb'_bytesToWordLE 512 bs j h2 (by omega)

theorem keyToBytes32_bytesToWordLE256 (bs : Bytes) (h : bs.length = 32) :
    keyToBytes32 (bytesToWordLE 256 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j _ h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToWordLE 256 bs j h2 (by omega)

theorem bytesToWordLE512_coinBytes (seed : BitVec 512) :
    bytesToWordLE 512 (coinBytes seed) = seed := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 64 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToWordLE 512 (coinBytes seed) (i / 8)
      (by simp [coinBytes_length, hj]) (by omega))
  simpa only [coinBytes, CryptoVerification.LibsignalAesCbc.toLEBytes, List.getElem_ofFn,
    BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and, Nat.div_add_mod] using hbyte

theorem bytesToWordLE256_keyToBytes32 (rand : BitVec 256) :
    bytesToWordLE 256 (keyToBytes32 rand) = rand := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToWordLE 256 (keyToBytes32 rand) (i / 8)
      (by simp [keyToBytes32, hj]) (by omega))
  simpa only [keyToBytes32, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr,
    decide_true, Bool.true_and, Nat.div_add_mod] using hbyte

@[simp] theorem kemCandBvToVec_kemCandVecToBv (p : SimKemSeed × SimKemEncRand) :
    kemCandBvToVec (kemCandVecToBv p) = p := by
  rcases p with ⟨s, r⟩
  exact Prod.ext (Subtype.ext (coinBytes_bytesToWordLE512 s.toList s.2))
    (Subtype.ext (keyToBytes32_bytesToWordLE256 r.toList r.2))

@[simp] theorem kemCandVecToBv_kemCandBvToVec (p : BitVec 512 × BitVec 256) :
    kemCandVecToBv (kemCandBvToVec p) = p := by
  rcases p with ⟨s, r⟩
  exact Prod.ext (bytesToWordLE512_coinBytes s) (bytesToWordLE256_keyToBytes32 r)

/-- Invariant on `SimKemFailTrack` ensuring bounded `sentB` length and lossless `V1State` and `SimBraidMsg` roundtrips. -/
structure KemTrackDeliverInv (F : ShaCompress) (K : MlKem) (L : ℕ)
    (tr : SimKemFailTrack F) : Prop where
  sentB_len : tr.sentB.length ≤ L
  bOk : ∀ Q : Party, BOkTight (tr.st Q)
  sentB_deser : ∀ mc ∈ tr.sentB,
    CryptoVerification.LibsignalSpqrV1.Message.deserialize
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi mc.1.epoch (spqrMsgPayloadSuffix mc.1) =
      .ok mc.1

theorem KemTrackDeliverInv.mono {F : ShaCompress} {K : MlKem} {L L' : ℕ}
    {tr : SimKemFailTrack F} (h : KemTrackDeliverInv F K L tr) (hLL : L ≤ L') :
    KemTrackDeliverInv F K L' tr :=
  ⟨h.sentB_len.trans hLL, h.bOk, h.sentB_deser⟩

theorem KemTrackDeliverInv.withCand {F : ShaCompress} {K : MlKem} {L : ℕ}
    {tr : SimKemFailTrack F} (h : KemTrackDeliverInv F K L tr)
    (cand' : Option (SimKemSeed × SimKemEncRand)) :
    KemTrackDeliverInv F K L { tr with cand := cand' } :=
  ⟨h.sentB_len, h.bOk, h.sentB_deser⟩

theorem kemTrackDeliverInv_initSim (F : ShaCompress) (K : MlKem) (L : ℕ) (pqrKey : BitVec 256) :
    KemTrackDeliverInv F K L (simInitKemFailTrack F pqrKey) := by
  refine ⟨Nat.zero_le L, ?_, ?_⟩
  · intro Q
    have hlen : (keyToBytes32 pqrKey).length = 32 := by simp [keyToBytes32]
    cases Q with
    | A =>
      obtain ⟨stA, hinitA, hbokA, -⟩ :=
        CryptoVerification.SpqrV1Sync.SendTotal.st_bInit_tight F (dir := .a2b) hlen
      change Except.ok ((simInitKemFailTrack F pqrKey).st .A) = Except.ok stA at hinitA
      cases hinitA; exact hbokA
    | B =>
      obtain ⟨stB, hinitB, hbokB, -⟩ :=
        CryptoVerification.SpqrV1Sync.SendTotal.st_bInit_tight F (dir := .b2a) hlen
      change CryptoVerification.LibsignalSpqrV1.States.init_b
        CryptoVerification.LibsignalSpqrV1.spqrPolyApi
        (CryptoVerification.LibsignalSpqrV1.spqrAuthApi F)
        (keyToBytes32 pqrKey) = Except.ok stB at hinitB
      simp only [CryptoVerification.LibsignalSpqrV1.States.init_b,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.new,
        CryptoVerification.LibsignalSpqrV1.HEADER_SIZE,
        CryptoVerification.LibsignalSpqrV1.AUTHENTICATOR_MACSIZE,
        CryptoVerification.LibsignalSpqrV1.spqrPolyApi,
        CryptoVerification.SpqrV1Sync.InSync.decoderNew_eq 96 (by decide),
        Except.mapError] at hinitB
      change Except.ok ((simInitKemFailTrack F pqrKey).st .B) = Except.ok stB at hinitB
      cases hinitB; exact hbokB
  · intro _ hmc; cases hmc

theorem kemTrackDeliverInv_stepDeliverSim (F : ShaCompress) (K : MlKem) (L : ℕ)
    (tr : SimKemFailTrack F) (Q : Party) (j : ℕ) (hInv : KemTrackDeliverInv F K L tr) :
    KemTrackDeliverInv F K L (simStepKemFailDeliver F K tr Q j) := by
  unfold simStepKemFailDeliver
  cases hj : tr.sentB[j]? with
  | none => exact hInv
  | some mc =>
    rcases mc with ⟨m, ctr⟩; dsimp only
    cases hrecv : (tr.st Q).recv K m with
    | error _ => exact hInv
    | ok out =>
      rcases out with ⟨key, st'⟩
      have hbok' : ∀ Q' : Party, BOkTight (Function.update tr.st Q st' Q') := by
        intro Q'
        by_cases hQ : Q' = Q
        · subst hQ; rw [Function.update_self]
          cases hek : CryptoVerification.SpqrV1Sync.SendTotal.isEkSide (tr.st Q') with
          | true =>
            exact CryptoVerification.SpqrV1Sync.SendTotal.st_bRecvEk_tight F K hek (hInv.bOk Q') hrecv
          | false =>
            exact CryptoVerification.SpqrV1Sync.SendTotal.st_bRecvCt_tight F K hek (hInv.bOk Q') hrecv
        · rw [Function.update_of_ne hQ]; exact hInv.bOk Q'
      dsimp only
      split_ifs with hm
      · cases tr.c <;> exact ⟨hInv.sentB_len, hbok', hInv.sentB_deser⟩
      · exact ⟨hInv.sentB_len, hbok', hInv.sentB_deser⟩

theorem kemTrackDeliverInv_stepSendSim (F : ShaCompress) (K : MlKem) (L : ℕ)
    (tr : SimKemFailTrack F) (Q : Party) (r : BitVec 512)
    (hInv : KemTrackDeliverInv F K L tr) :
    KemTrackDeliverInv F K (L + 1) (simStepKemFailSend F K tr Q r) := by
  unfold simStepKemFailSend; dsimp only
  cases hsend : (tr.st Q).send K (coinBytes r) with
  | error _ =>
    exact ⟨Nat.le_trans hInv.sentB_len (Nat.le_succ L), hInv.bOk, hInv.sentB_deser⟩
  | ok p =>
    rcases p with ⟨⟨m, key, st'⟩, tape'⟩; dsimp only
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      exact Nat.add_le_add_right hInv.sentB_len 1
    · intro Q'; dsimp only
      by_cases hQ : Q' = Q
      · subst hQ; rw [Function.update_self]
        exact CryptoVerification.SpqrV1Sync.SendTotal.st_bSendClosed_tight F K (hInv.bOk Q') hsend
      · rw [Function.update_of_ne hQ]; exact hInv.bOk Q'
    · intro mc hmc
      rw [List.mem_append, List.mem_singleton] at hmc
      rcases hmc with hmc | rfl
      · exact hInv.sentB_deser mc hmc
      · dsimp only
        obtain ⟨-, -, hp, -⟩ :=
          CryptoVerification.SpqrV1Sync.TopSync.send_facts F K (tr.st Q) st'
            (coinBytes r) tape' m key hsend
        obtain ⟨-, hsfx⟩ :=
          Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffix_lossless m
        have hsfxEq : spqrMsgPayloadSuffix m =
            (CryptoVerification.LibsignalSpqrV1.MessageType.from_payload m.payload).toU8 ::
              CryptoVerification.SpqrV1Sync.Codec.payloadBytes m.payload := by
          change CryptoVerification.E2E.Costed.spqrMsgPayloadSuffix m = _
          rw [hsfx]; rcases m with ⟨ep, pay⟩
          unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffixRaw
            CryptoVerification.SpqrV1Sync.Codec.payloadBytes
          cases pay <;> rfl
        rw [hsfxEq]
        have hdes := CryptoVerification.SpqrV1Sync.Codec.deserialize_payload
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi
          CryptoVerification.SpqrV1Sync.Codec.spqrPolyApi_mkChunk m.epoch m.payload hp
        cases m; exact hdes

/-! ## ML-KEM evaluation lemmas -/

section KemEval

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} {C : Crypto} {K : MlKem} {O : Ops (atomicSig ℓ Pt)}

local notation "ASig" => atomicSig ℓ Pt

theorem iterM_pure_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (f : α → α) (n : ℕ) (a : α) :
    iterM (fun x => (pure (f x) : m α)) n a = pure (f^[n] a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [iterM, ih, Function.iterate_succ_apply]

private def pack16 (b0 b1 : BitVec 8) : BitVec 16 :=
  (b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16
private theorem pack16_extract0 (b0 b1 : BitVec 8) :
    (pack16 b0 b1).extractLsb' 0 8 = b0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [pack16, hi]; omega
private theorem pack16_extract8 (b0 b1 : BitVec 8) :
    (pack16 b0 b1).extractLsb' 8 8 = b1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h16 : 8 + i < 16 := by omega
  have h8 : ¬ (8 + i < 8) := by omega
  simp [pack16, hi, h16, h8]
private theorem pack16_inj {a0 a1 b0 b1 : BitVec 8} :
    pack16 a0 a1 = pack16 b0 b1 ↔ a0 = b0 ∧ a1 = b1 := by
  refine ⟨fun h => ⟨by simpa [pack16_extract0] using congrArg (·.extractLsb' 0 8) h,
    by simpa [pack16_extract8] using congrArg (·.extractLsb' 8 8) h⟩, ?_⟩
  rintro ⟨rfl, rfl⟩; rfl
private theorem pack16_beq (a0 a1 b0 b1 : BitVec 8) :
    (pack16 a0 a1 == pack16 b0 b1) = ([a0, a1] == [b0, b1]) := by
  rw [Bool.eq_iff_iff]; simp [pack16_inj]

private def issue1275ScanStepFn : Bytes × Option Bool → Bytes × Option Bool
  | (rem, some b) => (rem, some b)
  | (rem, none) =>
    if 1 < rem.length then
      let p2 := rem.take 2
      let isCont := (p2 == [0x00#8, 0x00#8]) || (p2 == [0xff#8, 0xff#8])
      let isFlip := (p2 == [0x00#8, 0x01#8]) || ((p2 == [0x00#8, 0x02#8]) || (p2 == [0xff#8, 0xfe#8]))
      if isCont then (rem.drop 2, none) else (rem, some isFlip)
    else (rem, some false)

private theorem issue1275ScanStepE_eval (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (ρ : Env Γ)
    (st : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 512) (Ty.opt .bool)).denote) :
    (issue1275ScanStepE emb).eval (.cons st ρ) = issue1275ScanStepFn st := by
  have hOr (a b : Bool) : (if a = true then true else b) = (a || b) := by cases a <;> rfl
  have hp2 : ((2 : ℕ+) : ℕ) = 2 := rfl
  rcases st with ⟨rem, _ | b⟩
  · by_cases hlen : 1 < rem.length
    · simp only [issue1275ScanStepE, issue1275ScanStepFn, bytes2EqLitE, boolOrE, Expr.eval,
        Expr.v0, Expr.v1, Env.get, emb.eval_pureE, AtomicPureOp.eval, hp2, hlen, decide_true,
        ↓reduceIte, hOr]
    · simp only [issue1275ScanStepE, issue1275ScanStepFn, Expr.eval, Expr.v0, Env.get,
        emb.eval_pureE, AtomicPureOp.eval, hlen, decide_false, Bool.false_eq_true, ↓reduceIte]
  · rfl

private theorem issue1275ScanStepFn_iter_some (n : ℕ) (rem : Bytes) (b : Bool) :
    issue1275ScanStepFn^[n] (rem, some b) = (rem, some b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, issue1275ScanStepFn, ih]

private theorem issue1275_two_byte_step (b0 b1 : BitVec 8) (rest : Bytes) :
    let p2 := [b0, b1]
    let isCont := (p2 == [0x00#8, 0x00#8]) || (p2 == [0xff#8, 0xff#8])
    let isFlip := (p2 == [0x00#8, 0x01#8]) ||
      ((p2 == [0x00#8, 0x02#8]) || (p2 == [0xff#8, 0xfe#8]))
    issue1275NeedsFlip (b0 :: b1 :: rest) =
      if isCont then issue1275NeedsFlip rest else isFlip := by
  dsimp only
  rw [issue1275NeedsFlip]
  change (let w := pack16 b0 b1
    if (w == pack16 0x00#8 0x00#8 || w == pack16 0xff#8 0xff#8) = true then _
    else if (w == pack16 0x01#8 0x00#8 || w == pack16 0x02#8 0x00#8 ||
      w == pack16 0xfe#8 0xff#8) = true then false
    else if (w == pack16 0x00#8 0x01#8 || w == pack16 0x00#8 0x02#8 ||
      w == pack16 0xff#8 0xfe#8) = true then true
    else false) = _
  simp only [pack16_beq]
  cases hc : ([b0, b1] == [0x00#8, 0x00#8] || [b0, b1] == [0xff#8, 0xff#8])
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hf : ([b0, b1] == [0x00#8, 0x01#8] ||
        ([b0, b1] == [0x00#8, 0x02#8] || [b0, b1] == [0xff#8, 0xfe#8])) = true
    · simp only [Bool.or_eq_true, beq_iff_eq, List.cons.injEq, and_true] at hf
      clear hc; rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · have hf' : ([b0, b1] == [0x00#8, 0x01#8] || [b0, b1] == [0x00#8, 0x02#8] ||
          [b0, b1] == [0xff#8, 0xfe#8]) = false := by
        revert hf; cases ([b0, b1] == [0x00#8, 0x01#8]) <;>
          cases ([b0, b1] == [0x00#8, 0x02#8]) <;>
          cases ([b0, b1] == [0xff#8, 0xfe#8]) <;> decide
      have hf'' : ([b0, b1] == [0x00#8, 0x01#8] ||
          ([b0, b1] == [0x00#8, 0x02#8] || [b0, b1] == [0xff#8, 0xfe#8])) = false := by
        simpa [Bool.or_assoc] using hf'
      rw [hf', hf'']
      cases ([b0, b1] == [0x01#8, 0x00#8] || [b0, b1] == [0x02#8, 0x00#8] ||
        [b0, b1] == [0xfe#8, 0xff#8]) <;> rfl
  · rfl

private theorem issue1275ScanStepFn_iter_none (n : ℕ) :
    ∀ (rem : Bytes), rem.length ≤ 2 * n →
      ((issue1275ScanStepFn^[n] (rem, none)).2).getD false = issue1275NeedsFlip rem := by
  induction n with
  | zero =>
    intro rem hlen
    cases rem with
    | nil => rfl
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro rem hlen
    rw [Function.iterate_succ_apply]
    rcases rem with _ | ⟨b0, _ | ⟨b1, rest⟩⟩
    · simp [issue1275ScanStepFn, issue1275ScanStepFn_iter_some, issue1275NeedsFlip]
    · simp [issue1275ScanStepFn, issue1275ScanStepFn_iter_some, issue1275NeedsFlip]
    · have hgt : 1 < (b0 :: b1 :: rest).length := by simp
      have hrest : rest.length ≤ 2 * n := by simp at hlen; omega
      rw [issue1275_two_byte_step b0 b1 rest]
      simp only [issue1275ScanStepFn, hgt, ↓reduceIte, List.take_succ_cons, List.take_zero,
        List.drop_succ_cons, List.drop_zero]
      split
      · exact ih rest hrest
      · rw [issue1275ScanStepFn_iter_some]; rfl

private def swapPairsStep64Fn : Bytes × Bytes → Bytes × Bytes
  | (rem, acc) =>
    if 1 < rem.length then
      (rem.drop 2, (acc ++ ((rem.drop 1).take 1 ++ rem.take 1)).take 64)
    else (rem, acc)

private theorem swapPairsStep64E_eval (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (ρ : Env Γ)
    (st : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 64) (B (ℓ := ℓ) (Pt := Pt) 64)).denote) :
    (swapPairsStep64E emb).eval (.cons st ρ) = swapPairsStep64Fn st := by
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  rcases st with ⟨rem, acc⟩
  by_cases hlen : 1 < rem.length
  · simp only [swapPairsStep64E, swapPairsStep64Fn, Expr.eval, Expr.v0, Env.get,
      emb.eval_pureE, AtomicPureOp.eval, hp1, hp64, hlen, decide_true, ↓reduceIte]
  · simp only [swapPairsStep64E, swapPairsStep64Fn, Expr.eval, Expr.v0, Env.get,
      emb.eval_pureE, AtomicPureOp.eval, hlen, decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem swapAdjacentPairs_length :
    ∀ xs : Bytes, (swapAdjacentPairs xs).length = xs.length
  | [] | [_] => rfl
  | _ :: _ :: rest => by simp [swapAdjacentPairs, swapAdjacentPairs_length rest]

private theorem swapAdjacentPairs_append_two_mul (k : ℕ) :
    ∀ (u v : Bytes), u.length = 2 * k →
      swapAdjacentPairs (u ++ v) = swapAdjacentPairs u ++ swapAdjacentPairs v := by
  induction k with
  | zero =>
    rintro (_ | _) _ hlen
    · rfl
    · simp at hlen
  | succ k ih =>
    rintro (_ | ⟨b0, _ | ⟨b1, rest⟩⟩) v hlen
    · simp at hlen
    · simp at hlen; omega
    · have hrest : rest.length = 2 * k := by simp at hlen; omega
      simp [swapAdjacentPairs, ih rest v hrest]

private theorem swapPairsStep64Fn_iter (n : ℕ) :
    ∀ (rem acc : Bytes), rem.length = 2 * n → acc.length + 2 * n ≤ 64 →
      swapPairsStep64Fn^[n] (rem, acc) = ([], acc ++ swapAdjacentPairs rem) := by
  induction n with
  | zero =>
    rintro (_ | _) acc hlen _
    · simp [swapAdjacentPairs]
    · simp at hlen
  | succ n ih =>
    rintro (_ | ⟨b0, _ | ⟨b1, rest⟩⟩) acc hlen hacc
    · simp at hlen
    · simp at hlen; omega
    · have hgt : 1 < (b0 :: b1 :: rest).length := by simp
      have hrest : rest.length = 2 * n := by simp at hlen; omega
      have htk : (acc ++ [b1, b0]).take 64 = acc ++ [b1, b0] :=
        List.take_of_length_le (by simp; omega)
      rw [Function.iterate_succ_apply]
      simp only [swapPairsStep64Fn, hgt, ↓reduceIte, List.drop_succ_cons, List.drop_zero,
        List.take_succ_cons, List.take_zero]
      change swapPairsStep64Fn^[n] (rest, (acc ++ [b1, b0]).take 64) = _
      rw [htk, ih rest (acc ++ [b1, b0]) hrest (by simp; omega)]
      simp [swapAdjacentPairs, List.append_assoc]

private def swapChunk64StepFn : Bytes × Bytes → Bytes × Bytes
  | (rem, acc) =>
    if 63 < rem.length then
      (rem.drop 64, (acc ++ swapAdjacentPairs (rem.take 64)).take 2048)
    else (rem, acc)

private theorem swapChunk64StepC_eval (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (ρ : Env Γ)
    (st : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 2048) (B (ℓ := ℓ) (Pt := Pt) 2048)).denote) :
    (swapChunk64StepC emb (I := I)).eval (.cons st ρ) = pure (swapChunk64StepFn st) := by
  rcases st with ⟨rem, acc⟩
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  by_cases hlen : 63 < rem.length
  · have h64 : (rem.take 64).length = 2 * 32 := by simp; omega
    simp only [swapChunk64StepC, swapChunk64StepFn, Comp.eval, Expr.eval,
      Expr.v0, Expr.v1, Env.get, emb.eval_pureE, AtomicPureOp.eval,
      hp64, hp2048, hlen, decide_true, ↓reduceIte]
    have hInner :
        iterM (m := OracleComp T)
          (fun a => pure ((swapPairsStep64E emb).eval
            (.cons a (Env.cons (t := .prod (B (ℓ := ℓ) (Pt := Pt) 2048)
              (B (ℓ := ℓ) (Pt := Pt) 2048)) (rem, acc) ρ))))
          32 (rem.take 64, []) =
        pure (swapPairsStep64Fn^[32] (rem.take 64, [])) := by
      simp only [swapPairsStep64E_eval]
      exact iterM_pure_eq swapPairsStep64Fn 32 _
    rw [hInner, pure_bind, swapPairsStep64Fn_iter 32 (rem.take 64) [] h64 (by simp)]
    simp
  · simp only [swapChunk64StepC, swapChunk64StepFn, Comp.eval, Expr.eval,
      Expr.v0, Env.get, emb.eval_pureE, AtomicPureOp.eval,
      hlen, decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem swapChunk64StepFn_iter (m : ℕ) :
    ∀ (rem acc : Bytes), rem.length = 64 * m → acc.length + 64 * m ≤ 2048 →
      swapChunk64StepFn^[m] (rem, acc) = ([], acc ++ swapAdjacentPairs rem) := by
  induction m with
  | zero =>
    rintro (_ | _) acc hlen _
    · simp [swapAdjacentPairs]
    · simp at hlen
  | succ m ih =>
    intro rem acc hlen hacc
    have hgt : 63 < rem.length := by omega
    have hu : (rem.take 64).length = 2 * 32 := by simp; omega
    have hrest : (rem.drop 64).length = 64 * m := by simp; omega
    have hsu : (swapAdjacentPairs (rem.take 64)).length = 64 := by
      rw [swapAdjacentPairs_length]; omega
    have htk : (acc ++ swapAdjacentPairs (rem.take 64)).take 2048 =
        acc ++ swapAdjacentPairs (rem.take 64) :=
      List.take_of_length_le (by simp [hsu]; omega)
    rw [Function.iterate_succ_apply]
    simp only [swapChunk64StepFn, hgt, ↓reduceIte, htk]
    rw [ih (rem.drop 64) (acc ++ swapAdjacentPairs (rem.take 64)) hrest (by simp [hsu]; omega)]
    rw [List.append_assoc, ← swapAdjacentPairs_append_two_mul 32 (rem.take 64) (rem.drop 64) hu,
      List.take_append_drop]

private theorem flipEndianness_length (es : Bytes) (hlen : es.length = 2080) :
    (flipEndiannessOfEncapsulationStateBytes es).length = 2080 := by
  simp [flipEndiannessOfEncapsulationStateBytes, swapAdjacentPairs_length, hlen]

theorem issue1275FixEsC_eval (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (esE : Expr O Γ (B 2080)) (ρ : Env Γ) (es : Bytes)
    (hes : esE.eval ρ = es) (hlen : es.length = 2080) :
    (issue1275FixEsC emb (I := I) esE).eval ρ =
      pure ((potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es).getD es) := by
  let esD : (B (ℓ := ℓ) (Pt := Pt) 2080).denote := es
  have hes' : esE.eval ρ = esD := hes
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hp512 : ((512 : ℕ+) : ℕ) = 512 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  have hp2080 : ((2080 : ℕ+) : ℕ) = 2080 := rfl
  simp only [issue1275FixEsC, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get, hes',
    emb.eval_pureE, AtomicPureOp.eval, hp32, hp512, hp2048, hp2080, pure_bind]
  have hIter1 :
      iterM (m := OracleComp T)
        (fun a => pure ((issue1275ScanStepE emb).eval (.cons a (.cons esD ρ))))
        256 ((esD.drop 1536).take 512, none) =
      pure (issue1275ScanStepFn^[256] ((esD.drop 1536).take 512, none)) := by
    simp only [issue1275ScanStepE_eval]
    exact iterM_pure_eq issue1275ScanStepFn 256 _
  rw [hIter1, pure_bind]
  have hScan := issue1275ScanStepFn_iter_none 256 ((esD.drop 1536).take 512)
    (le_trans (List.length_take_le 512 _) (by omega))
  generalize issue1275ScanStepFn^[256] ((esD.drop 1536).take 512, none) = stScan at hScan ⊢
  rcases stScan with ⟨remS, _ | b⟩
  · dsimp only at hScan
    change pure esD = _
    simp [potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes,
      show 2080 - 32 - 1536 = 512 by decide, ← hScan, esD]
  · cases b
    · dsimp only at hScan
      change pure esD = _
      simp [potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes,
        show 2080 - 32 - 1536 = 512 by decide, ← hScan, esD]
    · dsimp only at hScan ⊢
      have hIter2 :
          iterM (m := OracleComp T)
            (fun a => (swapChunk64StepC emb (I := I)).eval
              (.cons a (Env.cons (t := .prod (B (ℓ := ℓ) (Pt := Pt) 512) (.opt .bool))
                (remS, some true) (.cons esD ρ))))
            32 (esD.take 2048, []) =
          pure (swapChunk64StepFn^[32] (esD.take 2048, [])) := by
        simp only [swapChunk64StepC_eval]
        exact iterM_pure_eq swapChunk64StepFn 32 _
      rw [hIter2, pure_bind]
      have htk32 : (es.drop 2048).take 32 = es.drop 2048 :=
        List.take_of_length_le (by simp [hlen])
      have htk2080 : (swapAdjacentPairs (es.take 2048) ++ es.drop 2048).take 2080 =
          swapAdjacentPairs (es.take 2048) ++ es.drop 2048 :=
        List.take_of_length_le (by simp [swapAdjacentPairs_length, hlen])
      simp [Expr.eval, Env.get, Expr.v2,
        swapChunk64StepFn_iter 32 (esD.take 2048) [] (by simp [esD, hlen]) (by simp),
        potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes,
        flipEndiannessOfEncapsulationStateBytes,
        show 2080 - 32 - 1536 = 512 by decide, show 2080 - 32 = 2048 by decide,
        htk32, htk2080, ← hScan, esD, hlen]

private theorem issue1275_except_eq (es : Bytes) (hlen : es.length = 2080) :
    CryptoVerification.LibsignalSpqrV1.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es =
      .ok (potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es) ∧
    ((potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es).getD es).length = 2080 := by
  unfold CryptoVerification.LibsignalSpqrV1.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
    potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes
    CryptoVerification.LibsignalSpqrV1.flip_endianness_of_encapsulation_state
  have hNe : (es.length != CryptoVerification.LibsignalSpqrV1.ENCAPSULATION_STATE_SIZE) = false := by
    simp [CryptoVerification.LibsignalSpqrV1.ENCAPSULATION_STATE_SIZE, hlen]
  have hBad : (es.length % 2 != 0 || !(es.length > 32)) = false := by simp [hlen]
  simp only [hNe, Bool.false_eq_true, ↓reduceIte]
  cases issue1275NeedsFlip ((es.drop 1536).take (2080 - 32 - 1536))
  · exact ⟨rfl, hlen⟩
  · simp only [↓reduceIte, hBad, Bool.false_eq_true, Option.getD_some,
      flipEndianness_length es hlen]
    exact ⟨rfl, trivial⟩

private theorem bytesToWordLE256_eq_bytesToKey32 (bs : Bytes) :
    bytesToWordLE 256 bs = bytesToKey32 bs := by
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    change (bytesToWordLE 256 tl <<< 8) ||| b.zeroExtend 256 =
      (bytesToKey32 tl <<< 8) ||| b.zeroExtend 256
    rw [ih]

private theorem bytesToKey32_beq_iff {a b : Bytes} (ha : a.length = 32) (hb : b.length = 32) :
    (!(bytesToKey32 a == bytesToKey32 b)) = decide (a ≠ b) := by
  suffices h : (bytesToKey32 a = bytesToKey32 b) ↔ a = b by
    by_cases hab : a = b <;> simp [hab, h]
  refine ⟨fun heq => ?_, fun h => h ▸ rfl⟩
  have ha' : keyToBytes32 (bytesToKey32 a) = a := by
    rw [← bytesToWordLE256_eq_bytesToKey32 a]
    exact keyToBytes32_bytesToWordLE256 a ha
  have hb' : keyToBytes32 (bytesToKey32 b) = b := by
    rw [← bytesToWordLE256_eq_bytesToKey32 b]
    exact keyToBytes32_bytesToWordLE256 b hb
  calc a = keyToBytes32 (bytesToKey32 a) := ha'.symm
    _ = keyToBytes32 (bytesToKey32 b) := by rw [heq]
    _ = b := hb'

theorem honestExchangeFailsC_eval (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr O Γ BV512) (randE : Expr O Γ BV256) (ρ : Env Γ)
    (seed : BitVec 512) (rand : BitVec 256)
    (hs : seedE.eval ρ = seed) (hr : randE.eval ρ = rand) :
    (honestExchangeFailsC emb (I := I) seedE randE).eval ρ =
      pure (K.honestExchangeFails ⟨coinBytes seed, coinBytes_length seed⟩ (keyToBytesVec32 rand)) := by
  set seedVec : List.Vector (BitVec 8) 64 := ⟨coinBytes seed, coinBytes_length seed⟩
  set mVec : List.Vector (BitVec 8) 32 := keyToBytesVec32 rand
  have hGen : CryptoVerification.LibsignalSpqrV1.generate K seedVec.toList =
      let (hdr, ek, dk) := K.fromSeed seedVec
      .ok ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList }, []) := by
    unfold CryptoVerification.LibsignalSpqrV1.generate
    have htk : seedVec.toList.take CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE =
        coinBytes seed :=
      List.take_of_length_le (by simp [seedVec, coinBytes_length,
        CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE])
    have hdrp : seedVec.toList.drop CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE = [] :=
      List.drop_eq_nil_of_le (by simp [seedVec, coinBytes_length,
        CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE])
    rw [htk, hdrp]
    simp [CryptoVerification.LibsignalSpqrV1.bytesToVector?,
      CryptoVerification.LibsignalSpqrV1.KEY_GENERATION_SEED_SIZE, coinBytes_length, seedVec]
  simp only [honestExchangeFailsC, Comp.eval, Expr.eval,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get,
    hs, hr, emb.eval_spqrE, emb.eval_pureE,
    AtomicSpqrKemOp.eval, AtomicPureOp.eval, pure_bind]
  unfold MlKem.honestExchangeFails
  rw [hGen]
  rcases hFrom : K.fromSeed seedVec with ⟨hdr, ek, dk⟩
  dsimp only
  have hEnc1Rhs : CryptoVerification.LibsignalSpqrV1.encaps1 K hdr.toList mVec.toList =
      match K.encaps1 hdr.toList mVec with
      | none => .error .encaps1Failed
      | some (ct1, es, ss) => .ok ((ct1.toList, es.toList, ss.toList), []) := by
    unfold CryptoVerification.LibsignalSpqrV1.encaps1
    have htk : mVec.toList.take CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE = mVec.toList :=
      List.take_of_length_le (by simp [CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE])
    have hdrp : mVec.toList.drop CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE = [] :=
      List.drop_eq_nil_of_le (by simp [CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE])
    rw [htk, hdrp]
    simp only [CryptoVerification.LibsignalSpqrV1.bytesToVector?,
      CryptoVerification.LibsignalSpqrV1.SHARED_SECRET_SIZE, List.Vector.toList_length, ↓reduceDIte]
    generalize_proofs pf
    have hV : ⟨mVec.toList, pf⟩ = mVec := Subtype.ext rfl
    rw [hV]
    rcases K.encaps1 hdr.toList mVec with _ | ⟨ct1, es, ss⟩ <;> rfl
  rw [hEnc1Rhs]
  rcases hE1 : K.encaps1 hdr.toList mVec with _ | ⟨ct1, es, ssB⟩
  · rfl
  · simp only [Option.map_some, CryptoVerification.LibsignalSpqrV1.ek_matches_header]
    have hIteF {α : Type} {P : Prop} [Decidable P] (h : ¬ P) (a b : α) :
        (if P then a else b) = b := by split <;> [exact absurd ‹_› h; rfl]
    have hIteT {α : Type} {P : Prop} [Decidable P] (h : P) (a b : α) :
        (if P then a else b) = a := by split <;> [rfl; exact absurd h ‹_›]
    by_cases hPk : K.validPkBytes hdr.toList ek.toList = true
    · refine Eq.trans (hIteF (by simp [hPk]) _ _)
        (Eq.trans ?_ (congrArg pure (hIteF (by simp [hPk]) _ _).symm))
      refine Eq.trans (congrArg (· >>= _) (issue1275FixEsC_eval emb _ _ es.toList rfl es.2)) ?_
      rw [pure_bind]
      obtain ⟨hFixOk, hEs'Len⟩ := issue1275_except_eq es.toList es.2
      set es' := (potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es.toList).getD es.toList
      have hVecEq {n : ℕ} (v : List.Vector (BitVec 8) n) (h : v.toList.length = n) :
          (⟨v.toList, h⟩ : List.Vector (BitVec 8) n) = v := Subtype.ext rfl
      have hEnc2Rhs : CryptoVerification.LibsignalSpqrV1.encaps2 K ek.toList es.toList =
          .ok (K.encaps2 ⟨es', hEs'Len⟩ ek).toList := by
        unfold CryptoVerification.LibsignalSpqrV1.encaps2
          CryptoVerification.LibsignalSpqrV1.bytesToVector?
        rw [hFixOk]
        dsimp only [Bind.bind, Except.bind]
        rw [show (potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es.toList).getD es.toList =
          es' from rfl]
        simp only [CryptoVerification.LibsignalSpqrV1.ENCAPSULATION_STATE_SIZE,
          CryptoVerification.LibsignalSpqrV1.ENCAPSULATION_KEY_SIZE, hEs'Len,
          List.Vector.toList_length, ↓reduceDIte]
        rfl
      rw [hEnc2Rhs]; dsimp only
      set ct2 := K.encaps2 ⟨es', hEs'Len⟩ ek
      have hDecRhs : CryptoVerification.LibsignalSpqrV1.decaps K dk.toList ct1.toList ct2.toList =
          .ok (K.decaps dk ct1 ct2).toList := by
        unfold CryptoVerification.LibsignalSpqrV1.decaps
          CryptoVerification.LibsignalSpqrV1.bytesToVector?
        simp only [CryptoVerification.LibsignalSpqrV1.CIPHERTEXT1_SIZE,
          CryptoVerification.LibsignalSpqrV1.CIPHERTEXT2_SIZE,
          CryptoVerification.LibsignalSpqrV1.DECAPSULATION_KEY_SIZE,
          List.Vector.toList_length, ↓reduceDIte]
        rfl
      rw [hDecRhs]; dsimp only
      simp only [hEs'Len, List.Vector.toList_length, ↓reduceDIte, hVecEq]
      exact congrArg pure (bytesToKey32_beq_iff (K.decaps dk ct1 ct2).2 ssB.2)
    · exact Eq.trans (hIteT (by simp [hPk]) _ _)
        (congrArg pure (hIteT (by simp [hPk]) _ _).symm)

end KemEval

end Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux
