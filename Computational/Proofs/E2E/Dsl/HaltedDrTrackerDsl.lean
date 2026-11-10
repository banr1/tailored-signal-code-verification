/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
public import Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge -- proof-setup: allow-public-import
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TightSize -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1Sync.CoinBridge
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg
import Computational.Proofs.E2E.Dsl.ClampsLossless
import Computational.Proofs.E2E.Dsl.SpqrSimChain
import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux
import Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl

/-!
# Per-Session `KemFailSessionTrack` Types, Invariant, and Atomic Combinators

Defines the `atomicSig` encodings for `KemFailSessionTrack`, proves `KemBridgeTrackInv`
preservation across tracker initialization, send, and deliver steps, and specializes the
`KemFailTrackDsl` combinators to `atomicE2EOps`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Env Iface Expr Comp
  atomicSig atomicE2EOps B U32 U64 BV256 BV512 recvResultT recvResultEnc
  partyToBool bytesToWordLE spqrMsgPayloadSuffix bits)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (RecvResult)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.Ratchet.LibsignalSim (SimKemCoins SimKemFailTrack simEncRandOf simEkSideIsA
  simNextKemCoins simInitKemFailTrack simStepKemFailSend simStepKemFailDeliver)
open CryptoGames.LibsignalSession (Crypto PublicKey ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State coinBytes)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
  (kemBraidParty KemFailTrackState KemFailSessionTrack initKemFailTrack initKemFailSessionTrack
   stepKemFailSend stepKemFailDeliver)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
  (e2eEmbed kemTrackAtomicEnc kemSessionTrackAtomicEnc simInitKemSessionTrack
   initV1BraidStE initKemFailTrackE initKemFailSessionTrackE
   stepKemFailSendC prependHonestWireE findRevHonestWireIdxE kemOnDeliverPostE
   initKemFailSessionTrackE_cost_le initKemFailSessionTrackE_size_le
   stepKemFailSendC_queries_zero stepKemFailSendC_cost_le stepKemFailSendC_size_le
   prependHonestWireE_cost prependHonestWireE_size
   findRevHonestWireIdxE_cost_le findRevHonestWireIdxE_size_le
   kemOnDeliverPostE_cost_le kemOnDeliverPostE_size_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslEvalAux (KemTrackDeliverInv)
open Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDsl
  (initKemFailSessionTrackE_eval stepKemFailSendC_eval findRevHonestWireIdxE_eval
   kemOnDeliverPostE_eval)

/-! ## Tracker types, encodings, and `KemBridgeTrackInv` -/

@[expose, reducible] def kemCoinsT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum .unit (.sum (BV512 (ℓ := ℓ) (Pt := Pt)) (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))

@[expose, reducible] def kemSentEntryT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (.prod (U64 (ℓ := ℓ) (Pt := Pt)) (B (ℓ := ℓ) (Pt := Pt) 64)) (U32 (ℓ := ℓ) (Pt := Pt))

@[expose, reducible] def kemTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (U64 (ℓ := ℓ) (Pt := Pt))
    (.prod (kemCoinsT ℓ Pt)
      (.prod (.prod (B (ℓ := ℓ) (Pt := Pt) 32) (B (ℓ := ℓ) (Pt := Pt) 32))
        (.prod (.list (kemSentEntryT ℓ Pt))
          (.prod (.prod (.tbl .nat) (.tbl .nat))
            (.opt (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))))))))

@[expose, reducible] def honestWireEntryT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (B (ℓ := ℓ) (Pt := Pt) 32) .bool

/-- Per-session halted tracker DSL type over `atomicSig ℓ Pt`. -/
@[expose, reducible] def sessHTy (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackT ℓ Pt) (.list (honestWireEntryT ℓ Pt))

@[expose, reducible] def kemCoinsBridgeAtomicEnc {ℓ : ℕ} {Pt : Type} :
    CryptoVerification.SpqrV1Sync.Braid.Coins → (kemCoinsT ℓ Pt).denote
  | .init => .inl ()
  | .seed s => .inr (.inl (bytesToWordLE 512 s.toList))
  | .both s r => .inr (.inr (bytesToWordLE 512 s.toList, bytesToWordLE 256 r.toList))

@[expose, reducible] def kemTrackBridgeAtomicEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (tr : KemFailTrackState F) : (kemTrackT ℓ Pt).denote :=
  (tr.e,
   (kemCoinsBridgeAtomicEnc tr.c,
    ((V1State.encodeRaw (tr.st .A).into_pb, V1State.encodeRaw (tr.st .B).into_pb),
     (tr.sentB.map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr)),
      ((tr.sendCtr .A, tr.sendCtr .B),
       tr.cand.map fun p => (bytesToWordLE 512 p.1.toList, bytesToWordLE 256 p.2.toList))))))

@[expose, reducible] def sessHEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (st : KemFailSessionTrack F Bytes) : (sessHTy ℓ Pt).denote :=
  (kemTrackBridgeAtomicEnc st.1, st.2.map fun (w, P) => (w, partyToBool P))

private def bridgeCoinsToSim : CryptoVerification.SpqrV1Sync.Braid.Coins → SimKemCoins
  | .init => .init
  | .seed s => .seed s
  | .both s r => .both s r

private def bridgeToSim {F : ShaCompress} (tr : KemFailTrackState F) : SimKemFailTrack F :=
  { e := tr.e
    auth := tr.auth
    c := bridgeCoinsToSim tr.c
    st := tr.st
    sentB := tr.sentB
    sendCtr := tr.sendCtr
    cand := tr.cand }

private theorem kemTrackBridgeAtomicEnc_eq_sim {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (tr : KemFailTrackState F) :
    kemTrackBridgeAtomicEnc (ℓ := ℓ) (Pt := Pt) tr =
      kemTrackAtomicEnc (ℓ := ℓ) (Pt := Pt) (bridgeToSim tr) := by
  unfold kemTrackBridgeAtomicEnc kemTrackAtomicEnc bridgeToSim
    kemCoinsBridgeAtomicEnc Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.kemCoinsAtomicEnc
    bridgeCoinsToSim Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase.kemCandVecToBv
  cases tr.c <;> cases tr.cand <;> rfl

private theorem bridgeToSim_init (F : ShaCompress) (pqrKey : BitVec 256) :
    bridgeToSim (initKemFailTrack F pqrKey) = simInitKemFailTrack F pqrKey :=
  rfl

private theorem bridgeToSim_stepDeliver (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    bridgeToSim (stepKemFailDeliver F K tr Q j) =
      simStepKemFailDeliver F K (bridgeToSim tr) Q j := by
  unfold stepKemFailDeliver simStepKemFailDeliver bridgeToSim
  dsimp only
  cases tr.sentB[j]? with
  | none => rfl
  | some mc =>
    rcases mc with ⟨m, _⟩; dsimp only
    cases (tr.st Q).recv K m with
    | error _ => rfl
    | ok out =>
      dsimp only
      have hnone : CryptoVerification.SpqrV1Sync.Braid.noneMsg (tr.e + 1#64) =
          ({ epoch := tr.e + 1#64, payload := .none } :
            CryptoVerification.LibsignalSpqrV1.Message CryptoVerification.LibsignalSpqrV1.spqrPolyApi) := rfl
      rw [hnone]
      split_ifs <;> cases tr.c <;> rfl

private theorem bridgeToSim_stepSend (F : ShaCompress) (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (r : BitVec 512) :
    bridgeToSim (stepKemFailSend F K tr Q r) =
      simStepKemFailSend F K (bridgeToSim tr) Q r := by
  unfold stepKemFailSend simStepKemFailSend bridgeToSim
  dsimp only
  have hparty : (CryptoVerification.SpqrV1Sync.Braid.ekSide tr.e != kemBraidParty Q) =
      (simEkSideIsA tr.e != (Q == .A)) := by
    unfold CryptoVerification.SpqrV1Sync.Braid.ekSide simEkSideIsA kemBraidParty
    by_cases h : tr.e.toNat % 2 = 1 <;> cases Q <;> (simp [h]; try decide)
  have hrand : CryptoVerification.SpqrV1Sync.Braid.encRandOf r = simEncRandOf r := rfl
  have hnext : ∀ c stQ,
      bridgeCoinsToSim (CryptoVerification.SpqrV1Sync.Braid.nextCoins F c stQ (coinBytes r)) =
        simNextKemCoins F (bridgeCoinsToSim c) stQ (coinBytes r) := by
    intro c stQ
    cases c <;> cases stQ <;> rfl
  rw [hparty, hrand]
  cases (tr.st Q).send K (coinBytes r) with
  | error _ =>
    dsimp only; congr 1
    cases tr.cand with
    | some _ => rfl
    | none =>
      split_ifs <;> cases tr.c <;> cases tr.st Q <;> rfl
  | ok out =>
    rcases out with ⟨out, _⟩; dsimp only
    rw [hnext]
    congr 1
    cases tr.cand with
    | some _ => rfl
    | none =>
      split_ifs <;> cases tr.c <;> cases tr.st Q <;> rfl

/-- Reachability and length invariant on `KemFailSessionTrack F Bytes` after at most `qBound` oracle steps. -/
structure KemBridgeTrackInv (F : ShaCompress) (_K : MlKem) (qBound : ℕ)
    (st : KemFailSessionTrack F Bytes) : Prop where
  sentB_len : st.1.sentB.length ≤ qBound
  wires_len : st.2.length ≤ qBound
  bOk : ∀ Q : Party, BOkTight (st.1.st Q)
  sentB_deser : ∀ mc ∈ st.1.sentB,
    CryptoVerification.LibsignalSpqrV1.Message.deserialize
      CryptoVerification.LibsignalSpqrV1.spqrPolyApi mc.1.epoch (spqrMsgPayloadSuffix mc.1) =
      .ok mc.1

theorem kemBridgeTrackInv_mono {F : ShaCompress} {K : MlKem} {q₁ q₂ : ℕ}
    {st : KemFailSessionTrack F Bytes} (hq : q₁ ≤ q₂)
    (h : KemBridgeTrackInv F K q₁ st) :
    KemBridgeTrackInv F K q₂ st :=
  ⟨h.sentB_len.trans hq, h.wires_len.trans hq, h.bOk, h.sentB_deser⟩

alias KemBridgeTrackInv_mono := kemBridgeTrackInv_mono

theorem kemBridgeTrackInv_init (F : ShaCompress) (K : MlKem) (qBound : ℕ)
    (_hq : qBound < 2 ^ 31) (pqrKey : BitVec 256) :
    KemBridgeTrackInv F K qBound (initKemFailSessionTrack F Bytes pqrKey) := by
  refine ⟨Nat.zero_le qBound, Nat.zero_le qBound, ?_, ?_⟩
  · intro Q
    have hlen : (keyToBytes32 pqrKey).length = 32 := by simp [keyToBytes32]
    cases Q with
    | A =>
      obtain ⟨stA, hinitA, hbokA, -⟩ :=
        CryptoVerification.SpqrV1Sync.SendTotal.st_bInit_tight F (dir := .a2b) hlen
      change Except.ok ((initKemFailTrack F pqrKey).st .A) = Except.ok stA at hinitA
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
      change Except.ok ((initKemFailTrack F pqrKey).st .B) = Except.ok stB at hinitB
      cases hinitB; exact hbokB
  · intro _ hmc; cases hmc

alias KemBridgeTrackInv_init := kemBridgeTrackInv_init

private theorem kemBridgeTrackInv_stepDeliver {F : ShaCompress} {K : MlKem} {L : ℕ}
    {st : KemFailSessionTrack F Bytes} (Q : Party) (j : ℕ)
    (hInv : KemBridgeTrackInv F K L st) :
    KemBridgeTrackInv F K L (stepKemFailDeliver F K st.1 Q j, st.2) := by
  unfold stepKemFailDeliver
  cases st.1.sentB[j]? with
  | none => exact hInv
  | some mc =>
    rcases mc with ⟨m, _⟩; dsimp only
    cases hrecv : (st.1.st Q).recv K m with
    | error _ => exact hInv
    | ok out =>
      rcases out with ⟨_, st'⟩
      have hbok' : ∀ Q' : Party, BOkTight (Function.update st.1.st Q st' Q') := by
        intro Q'
        by_cases hQ : Q' = Q
        · subst hQ; rw [Function.update_self]
          cases hek : CryptoVerification.SpqrV1Sync.SendTotal.isEkSide (st.1.st Q') with
          | true =>
            exact CryptoVerification.SpqrV1Sync.SendTotal.st_bRecvEk_tight F K hek (hInv.bOk Q') hrecv
          | false =>
            exact CryptoVerification.SpqrV1Sync.SendTotal.st_bRecvCt_tight F K hek (hInv.bOk Q') hrecv
        · rw [Function.update_of_ne hQ]; exact hInv.bOk Q'
      dsimp only
      split_ifs
      · cases st.1.c <;> exact ⟨hInv.sentB_len, hInv.wires_len, hbok', hInv.sentB_deser⟩
      · exact ⟨hInv.sentB_len, hInv.wires_len, hbok', hInv.sentB_deser⟩

private theorem kemBridgeTrackInv_stepSend {F : ShaCompress} {K : MlKem} {q : ℕ}
    {st : KemFailSessionTrack F Bytes} (Q : Party) (r : BitVec 512)
    (hInv : KemBridgeTrackInv F K q st) :
    let tr' := stepKemFailSend F K st.1 Q r
    KemBridgeTrackInv F K (q + 1) ({ st.1 with cand := tr'.cand }, st.2) ∧
    ∀ ct : Bytes, KemBridgeTrackInv F K (q + 1) (tr', (ct, Q) :: st.2) := by
  refine ⟨⟨Nat.le_trans hInv.sentB_len (Nat.le_succ q), Nat.le_trans hInv.wires_len (Nat.le_succ q),
    hInv.bOk, hInv.sentB_deser⟩, fun ct => ?_⟩
  have hwires' : ((ct, Q) :: st.2).length ≤ q + 1 := Nat.succ_le_succ hInv.wires_len
  unfold stepKemFailSend; dsimp only
  cases hsend : (st.1.st Q).send K (coinBytes r) with
  | error _ =>
    exact ⟨Nat.le_trans hInv.sentB_len (Nat.le_succ q), hwires', hInv.bOk, hInv.sentB_deser⟩
  | ok p =>
    rcases p with ⟨⟨m, key, st'⟩, tape'⟩; dsimp only
    refine ⟨?_, hwires', ?_, ?_⟩
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
          CryptoVerification.SpqrV1Sync.TopSync.send_facts F K (st.1.st Q) st'
            (coinBytes r) tape' m key hsend
        obtain ⟨-, hsfx⟩ :=
          Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffix_lossless m
        have hsfxEq : spqrMsgPayloadSuffix m =
            (CryptoVerification.LibsignalSpqrV1.MessageType.from_payload m.payload).toU8 ::
              CryptoVerification.SpqrV1Sync.Codec.payloadBytes m.payload := by
          change CryptoVerification.E2E.Costed.spqrMsgPayloadSuffix m = _
          rw [hsfx]; rcases m with ⟨_, pay⟩
          unfold Computational.Proofs.E2E.Dsl.ClampsLossless.spqrMsgPayloadSuffixRaw
            CryptoVerification.SpqrV1Sync.Codec.payloadBytes
          cases pay <;> rfl
        rw [hsfxEq]
        have hdes := CryptoVerification.SpqrV1Sync.Codec.deserialize_payload
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi
          CryptoVerification.SpqrV1Sync.Codec.spqrPolyApi_mkChunk m.epoch m.payload hp
        cases m; exact hdes

/-! ## Atomic tracker combinators -/

section AtomicTrackerDsl

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicE2EOps ℓ P C K decT encT

@[expose] def initV1BraidStAtomicE (isAlice : Bool) {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) : Expr AOps Γ (B 32) :=
  initV1BraidStE (e2eEmbed ℓ P C K decT encT) isAlice pqrKeyE

@[expose] def initKemFailTrackAtomicE {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) : Expr AOps Γ (kemTrackT ℓ Pt) :=
  initKemFailTrackE (e2eEmbed ℓ P C K decT encT) pqrKeyE

@[expose] def initKemFailSessionTrackAtomicE {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) : Expr AOps Γ (sessHTy ℓ Pt) :=
  initKemFailSessionTrackE (e2eEmbed ℓ P C K decT encT) pqrKeyE

theorem initKemFailSessionTrackAtomicE_cost_le {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) :
    (initKemFailSessionTrackAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      pqrKeyE).cost ≤ pqrKeyE.cost + 3505 :=
  initKemFailSessionTrackE_cost_le (e2eEmbed ℓ P C K decT encT) pqrKeyE

theorem initKemFailSessionTrackAtomicE_size_le {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) :
    (initKemFailSessionTrackAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      pqrKeyE).size ≤ pqrKeyE.size + 80 :=
  Nat.le_trans (initKemFailSessionTrackE_size_le (e2eEmbed ℓ P C K decT encT) pqrKeyE) (by omega)

theorem initKemFailSessionTrackAtomicE_eval {Γ : List (Ty ASig)}
    (pqrKeyE : Expr AOps Γ BV256) (ρ : Env Γ) (pqrKey : BitVec 256)
    (hk : pqrKeyE.eval ρ = pqrKey) :
    (initKemFailSessionTrackAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      pqrKeyE).eval ρ = sessHEnc (initKemFailSessionTrack C.F Bytes pqrKey) := by
  change (initKemFailSessionTrackE (e2eEmbed ℓ P C K decT encT) pqrKeyE).eval ρ = _
  rw [initKemFailSessionTrackE_eval (e2eEmbed ℓ P C K decT encT) pqrKeyE ρ, hk]
  unfold kemSessionTrackAtomicEnc simInitKemSessionTrack sessHEnc initKemFailSessionTrack
  rw [kemTrackBridgeAtomicEnc_eq_sim, bridgeToSim_init]

/-- Tracker-halted send-step `Comp` over `atomicE2EOps` returning `(halted, trOut)`. -/
@[expose] def stepKemFailSendAtomicC (q : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) : Comp AOps I Γ (.prod .bool (kemTrackT ℓ Pt)) :=
  stepKemFailSendC (e2eEmbed ℓ P C K decT encT) q (I := I) trE qBE rqE

@[expose] def prependHonestWireAtomicE {Γ : List (Ty ASig)}
    (trOutE : Expr AOps Γ (kemTrackT ℓ Pt))
    (hwE : Expr AOps Γ (.list (honestWireEntryT ℓ Pt)))
    (wE : Expr AOps Γ (B 32)) (pBE : Expr AOps Γ .bool) : Expr AOps Γ (sessHTy ℓ Pt) :=
  prependHonestWireE trOutE hwE wE pBE

@[expose] def findRevHonestWireIdxAtomicE (L : ℕ) {Γ : List (Ty ASig)}
    (hwE : Expr AOps Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) : Expr AOps Γ (.opt .nat) :=
  findRevHonestWireIdxE (e2eEmbed ℓ P C K decT encT) L hwE qBE wE

/-- Post-`deliver` tracker update given `rrOptE : Option (RecvResult (Plain ℓ))`. -/
@[expose] def kemOnDeliverPostAtomicE (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) : Expr AOps Γ (kemTrackT ℓ Pt) :=
  kemOnDeliverPostE (e2eEmbed ℓ P C K decT encT) L qBE jOptE rrOptE trE

@[simp] theorem stepKemFailSendAtomicC_queries_zero (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (w : I.Tag → ℕ) :
    (stepKemFailSendAtomicC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      q (I := I) trE qBE rqE).queries w (fun _ => 0) = 0 :=
  stepKemFailSendC_queries_zero (e2eEmbed ℓ P C K decT encT) q trE qBE rqE w (fun _ => 0)

theorem stepKemFailSendAtomicC_cost_le (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendAtomicC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      q (I := I) trE qBE rqE).cost ≤
      trE.cost + qBE.cost + rqE.cost + q + 1160000 :=
  stepKemFailSendC_cost_le (e2eEmbed ℓ P C K decT encT) q trE qBE rqE

theorem stepKemFailSendAtomicC_size_le (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) :
    (stepKemFailSendAtomicC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      q (I := I) trE qBE rqE).size ≤
      trE.size + qBE.size + rqE.size + 880 + bits (q + 1) :=
  stepKemFailSendC_size_le (e2eEmbed ℓ P C K decT encT) q trE qBE rqE

theorem prependHonestWireAtomicE_cost {Γ : List (Ty ASig)}
    (trOutE : Expr AOps Γ (kemTrackT ℓ Pt))
    (hwE : Expr AOps Γ (.list (honestWireEntryT ℓ Pt)))
    (wE : Expr AOps Γ (B 32)) (pBE : Expr AOps Γ .bool) :
    (prependHonestWireAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      trOutE hwE wE pBE).cost = trOutE.cost + hwE.cost + wE.cost + pBE.cost + 3 :=
  prependHonestWireE_cost trOutE hwE wE pBE

theorem prependHonestWireAtomicE_size {Γ : List (Ty ASig)}
    (trOutE : Expr AOps Γ (kemTrackT ℓ Pt))
    (hwE : Expr AOps Γ (.list (honestWireEntryT ℓ Pt)))
    (wE : Expr AOps Γ (B 32)) (pBE : Expr AOps Γ .bool) :
    (prependHonestWireAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      trOutE hwE wE pBE).size = trOutE.size + hwE.size + wE.size + pBE.size + 3 :=
  prependHonestWireE_size trOutE hwE wE pBE

theorem findRevHonestWireIdxAtomicE_cost_le (L : ℕ) {Γ : List (Ty ASig)}
    (hwE : Expr AOps Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWireIdxAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      L hwE qBE wE).cost ≤ hwE.cost + qBE.cost + wE.cost + 120 * L + 64 :=
  findRevHonestWireIdxE_cost_le (e2eEmbed ℓ P C K decT encT) L hwE qBE wE

theorem findRevHonestWireIdxAtomicE_size_le (L : ℕ) {Γ : List (Ty ASig)}
    (hwE : Expr AOps Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) :
    (findRevHonestWireIdxAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      L hwE qBE wE).size ≤ hwE.size + qBE.size + wE.size + 50 + bits L :=
  Nat.le_trans (findRevHonestWireIdxE_size_le (e2eEmbed ℓ P C K decT encT) L hwE qBE wE) (by omega)

theorem kemOnDeliverPostAtomicE_cost_le (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) :
    (kemOnDeliverPostAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      L qBE jOptE rrOptE trE).cost ≤
      qBE.cost + jOptE.cost + rrOptE.cost + trE.cost + 40 * L + 8100 :=
  Nat.le_trans
    (kemOnDeliverPostE_cost_le (e2eEmbed ℓ P C K decT encT) L qBE jOptE rrOptE trE)
    (by omega)

theorem kemOnDeliverPostAtomicE_size_le (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) :
    (kemOnDeliverPostAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      L qBE jOptE rrOptE trE).size ≤
      qBE.size + jOptE.size + rrOptE.size + trE.size + 356 + 2 * bits L :=
  kemOnDeliverPostE_size_le (e2eEmbed ℓ P C K decT encT) L qBE jOptE rrOptE trE

theorem stepKemFailSendAtomicC_eval_and_inv (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ)
    (st : KemFailSessionTrack C.F Bytes) (Q : Party) (coins : BitVec 512)
    (hInv : KemBridgeTrackInv C.F K q st)
    (htr : trE.eval ρ = kemTrackBridgeAtomicEnc st.1)
    (hqB : qBE.eval ρ = partyToBool Q)
    (hrq : rqE.eval ρ = coins) :
    let tr' := stepKemFailSend C.F K st.1 Q coins
    (stepKemFailSendAtomicC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      q (I := I) trE qBE rqE).eval ρ =
      pure (if tr'.cand.isSome then (true, kemTrackBridgeAtomicEnc { st.1 with cand := tr'.cand })
            else (false, kemTrackBridgeAtomicEnc tr')) ∧
    KemBridgeTrackInv C.F K (q + 1) ({ st.1 with cand := tr'.cand }, st.2) ∧
    ∀ ct : Bytes, KemBridgeTrackInv C.F K (q + 1) (tr', (ct, Q) :: st.2) := by
  have hInv' := kemBridgeTrackInv_stepSend Q coins hInv
  refine ⟨?_, hInv'.1, hInv'.2⟩
  have htrSim : trE.eval ρ = kemTrackAtomicEnc (bridgeToSim st.1) :=
    htr.trans (kemTrackBridgeAtomicEnc_eq_sim st.1)
  have heval := stepKemFailSendC_eval (e2eEmbed ℓ P C K decT encT) q (I := I)
    trE qBE rqE ρ (bridgeToSim st.1) Q coins htrSim hqB hrq (hInv.bOk Q) hInv.sentB_len
  change (stepKemFailSendC (e2eEmbed ℓ P C K decT encT) q (I := I) trE qBE rqE).eval ρ = _
  rw [heval]
  dsimp only
  rw [← bridgeToSim_stepSend C.F K st.1 Q coins]
  have hCandEq :
      ({ bridgeToSim st.1 with cand := (bridgeToSim (stepKemFailSend C.F K st.1 Q coins)).cand } :
        SimKemFailTrack C.F) =
      bridgeToSim { st.1 with cand := (stepKemFailSend C.F K st.1 Q coins).cand } := rfl
  have hIsSome : (bridgeToSim (stepKemFailSend C.F K st.1 Q coins)).cand.isSome =
      (stepKemFailSend C.F K st.1 Q coins).cand.isSome := rfl
  rw [hCandEq, hIsSome, ← kemTrackBridgeAtomicEnc_eq_sim, ← kemTrackBridgeAtomicEnc_eq_sim]
  cases (stepKemFailSend C.F K st.1 Q coins).cand.isSome <;> rfl

theorem findRevHonestWireIdxAtomicE_eval (L : ℕ) {Γ : List (Ty ASig)}
    (hwE : Expr AOps Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32)) (ρ : Env Γ)
    (hw : List (Bytes × Party)) (Q : Party) (w : Bytes)
    (hlen : hw.length ≤ L) (hhw : hwE.eval ρ = hw.map fun (x, Q') => (x, partyToBool Q'))
    (hqB : qBE.eval ρ = partyToBool Q) (hwVal : wE.eval ρ = w) :
    (findRevHonestWireIdxAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      L hwE qBE wE).eval ρ =
      hw.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) :=
  findRevHonestWireIdxE_eval (e2eEmbed ℓ P C K decT encT) L hwE qBE wE ρ hw Q w hhw hqB hwVal hlen

theorem kemOnDeliverPostAtomicE_eval_and_inv (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (jOptE : Expr AOps Γ (.opt .nat))
    (rrOptE : Expr AOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr AOps Γ (kemTrackT ℓ Pt)) (ρ : Env Γ)
    (st : KemFailSessionTrack C.F Bytes) (Q : Party) (w : Bytes)
    (res : Option (RecvResult (Plain ℓ)))
    (hInv : KemBridgeTrackInv C.F K L st)
    (hqB : qBE.eval ρ = partyToBool Q)
    (hj : jOptE.eval ρ = st.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other))
    (hrr : rrOptE.eval ρ = res.map recvResultEnc)
    (htr : trE.eval ρ = kemTrackBridgeAtomicEnc st.1) :
    let st' :=
      match res, st.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with
      | some (.accepted _ _ _), some j => (stepKemFailDeliver C.F K st.1 Q j, st.2)
      | _, _ => st
    (kemOnDeliverPostAtomicE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      L qBE jOptE rrOptE trE).eval ρ = kemTrackBridgeAtomicEnc st'.1 ∧
    KemBridgeTrackInv C.F K L st' := by
  dsimp only [kemOnDeliverPostAtomicE]
  have htrSim : trE.eval ρ = kemTrackAtomicEnc (bridgeToSim st.1) :=
    htr.trans (kemTrackBridgeAtomicEnc_eq_sim st.1)
  have hDelInv : KemTrackDeliverInv C.F K L (bridgeToSim st.1) :=
    ⟨hInv.sentB_len, hInv.bOk, hInv.sentB_deser⟩
  have heval := kemOnDeliverPostE_eval (e2eEmbed ℓ P C K decT encT) L
    qBE jOptE rrOptE trE ρ Q
    (st.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other))
    res (bridgeToSim st.1) hqB hj hrr htrSim hDelInv
  rcases res with _ | rr
  · exact ⟨heval.trans (kemTrackBridgeAtomicEnc_eq_sim st.1).symm, hInv⟩
  · cases rr with
    | rejected => exact ⟨heval.trans (kemTrackBridgeAtomicEnc_eq_sim st.1).symm, hInv⟩
    | accepted _ _ _ =>
      rcases hFind : st.2.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with _ | j
      · rw [hFind] at heval ⊢
        exact ⟨heval.trans (kemTrackBridgeAtomicEnc_eq_sim st.1).symm, hInv⟩
      · rw [hFind] at heval ⊢
        dsimp only at heval ⊢
        rw [← bridgeToSim_stepDeliver C.F K st.1 Q j, ← kemTrackBridgeAtomicEnc_eq_sim] at heval
        exact ⟨heval, kemBridgeTrackInv_stepDeliver Q j hInv⟩

end AtomicTrackerDsl

end Computational.Proofs.E2E.Dsl.HaltedDrTrackerDsl
