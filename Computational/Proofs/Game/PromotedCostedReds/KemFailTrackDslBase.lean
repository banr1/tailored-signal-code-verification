/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.CostedTables -- proof-setup: allow-public-import
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SizeBudgetBridge -- proof-setup: allow-public-import

/-!
# Base Combinators and Cost Bounds for KEM-Failure Session Tracking

Defines the minimal operation table `kemTrackOps`, zero-cast embeddings `KemTrackOpEmbed` into
`atomicSessionOps` and `atomicE2EOps`, and `ReductionDsl` combinators for `SimKemFailTrack` and
`SimKemSessionTrack` along with their static query, cost, and size bounds.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  iterM bits partyToBool boolToParty bytesToWordLE spqrMsgPayloadSuffix
  atomicSig atomicPureOps atomicSpqrKemOps atomicSessionOps atomicE2EOps
  AtomicPureOp AtomicSpqrKemOp B BV256 BV512 U32 U64 fig8CtT fig8CtV recvResultT)
open CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.Ratchet.LibsignalSim (SimBraidSt SimBraidMsg SimKemSeed
  SimKemEncRand SimKemCoins SimKemFailTrack SimFig8C simEncRandOf simEkSideIsA
  simNextKemCoins simInitKemFailTrack simStepKemFailSend simStepKemFailDeliver)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State coinBytes coinBytes_length
  issue1275NeedsFlip swapAdjacentPairs flipEndiannessOfEncapsulationStateBytes
  potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes encode_varint)
open CryptoVerification.E2E (Bytes)

/-! ## Operation embeddings and tracker state encodings -/

/-- Operation table `atomicPureOps ⊕ atomicSpqrKemOps` for SPQR V1 braid tracking. -/
@[expose, reducible] def kemTrackOps (ℓ : ℕ) (Pt : Type) (C : Crypto) (K : MlKem) : Ops (atomicSig ℓ Pt) :=
  Ops.sum (atomicPureOps ℓ Pt) (atomicSpqrKemOps ℓ Pt C K)

/-- Structure-preserving embedding of `AtomicPureOp` and `AtomicSpqrKemOp` into `O`. -/
structure KemTrackOpEmbed (ℓ : ℕ) (Pt : Type) (C : Crypto) (K : MlKem)
    (O : Ops (atomicSig ℓ Pt)) where
  pureE : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} (o : AtomicPureOp),
    Expr O Γ (o.dom ℓ Pt) → Expr O Γ (o.cod ℓ Pt)
  spqrE : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} (o : AtomicSpqrKemOp),
    Expr O Γ (o.dom ℓ Pt) → Expr O Γ (o.cod ℓ Pt)
  eval_pureE : ∀ {Γ} (o : AtomicPureOp) (e : Expr O Γ (o.dom ℓ Pt)) (ρ : Env Γ),
    (pureE o e).eval ρ = AtomicPureOp.eval ℓ Pt o (e.eval ρ)
  cost_pureE : ∀ {Γ} (o : AtomicPureOp) (e : Expr O Γ (o.dom ℓ Pt)),
    (pureE o e).cost = e.cost + AtomicPureOp.cost ℓ o
  size_pureE : ∀ {Γ} (o : AtomicPureOp) (e : Expr O Γ (o.dom ℓ Pt)),
    (pureE o e).size = e.size + o.opSize + 1
  eval_spqrE : ∀ {Γ} (o : AtomicSpqrKemOp) (e : Expr O Γ (o.dom ℓ Pt)) (ρ : Env Γ),
    (spqrE o e).eval ρ = AtomicSpqrKemOp.eval ℓ Pt C K o (e.eval ρ)
  cost_spqrE : ∀ {Γ} (o : AtomicSpqrKemOp) (e : Expr O Γ (o.dom ℓ Pt)),
    (spqrE o e).cost = e.cost + AtomicSpqrKemOp.cost o
  size_spqrE : ∀ {Γ} (o : AtomicSpqrKemOp) (e : Expr O Γ (o.dom ℓ Pt)),
    (spqrE o e).size = e.size + 1

attribute [simp] KemTrackOpEmbed.eval_pureE KemTrackOpEmbed.cost_pureE KemTrackOpEmbed.size_pureE
  KemTrackOpEmbed.eval_spqrE KemTrackOpEmbed.cost_spqrE KemTrackOpEmbed.size_spqrE

abbrev baseEmbed (ℓ : ℕ) (Pt : Type) (C : Crypto) (K : MlKem) :
    KemTrackOpEmbed ℓ Pt C K (kemTrackOps ℓ Pt C K) :=
  { pureE := fun o e => @Expr.op (atomicSig ℓ Pt) (kemTrackOps ℓ Pt C K) _ (Sum.inl o) e
    spqrE := fun o e => @Expr.op (atomicSig ℓ Pt) (kemTrackOps ℓ Pt C K) _ (Sum.inr o) e
    eval_pureE := fun _ _ _ => rfl, cost_pureE := fun _ _ => rfl, size_pureE := fun _ _ => rfl
    eval_spqrE := fun _ _ _ => rfl, cost_spqrE := fun _ _ => rfl, size_spqrE := fun _ _ => rfl }

abbrev embedSessionShape {ℓ : ℕ} {Pt : Type} {C : Crypto} {K : MlKem}
    (R1 R2 R3 : Ops (atomicSig ℓ Pt)) :
    KemTrackOpEmbed ℓ Pt C K (Ops.sum (Ops.sum (Ops.sum (Ops.sum (atomicPureOps ℓ Pt) R1) R2) R3)
      (atomicSpqrKemOps ℓ Pt C K)) :=
  let O := Ops.sum (Ops.sum (Ops.sum (Ops.sum (atomicPureOps ℓ Pt) R1) R2) R3)
    (atomicSpqrKemOps ℓ Pt C K)
  { pureE := fun o e => @Expr.op (atomicSig ℓ Pt) O _ (Sum.inl (Sum.inl (Sum.inl (Sum.inl o)))) e
    spqrE := fun o e => @Expr.op (atomicSig ℓ Pt) O _ (Sum.inr o) e
    eval_pureE := fun _ _ _ => rfl, cost_pureE := fun _ _ => rfl, size_pureE := fun _ _ => rfl
    eval_spqrE := fun _ _ _ => rfl, cost_spqrE := fun _ _ => rfl, size_spqrE := fun _ _ => rfl }

abbrev sessionEmbed (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt := 0) :
    KemTrackOpEmbed ℓ Pt C K (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) :=
  embedSessionShape
    (Ops.sum (_root_.ReductionDsl.atomicPtEncOps ℓ encT) (_root_.ReductionDsl.atomicSymOps ℓ Pt C))
    (_root_.ReductionDsl.atomicGroupOps ℓ Pt C Dh encPt lam)
    (Ops.sum (_root_.ReductionDsl.atomicPtDecOps ℓ decT)
      (_root_.ReductionDsl.atomicCurveCheckOps ℓ decT encT))

abbrev embedE2EShape {ℓ : ℕ} {Pt : Type} {C : Crypto} {K : MlKem}
    (R1 R2 R3 R4 : Ops (atomicSig ℓ Pt)) :
    KemTrackOpEmbed ℓ Pt C K (Ops.sum (Ops.sum (atomicPureOps ℓ Pt) R1)
      (Ops.sum R2 (Ops.sum R3 (Ops.sum (atomicSpqrKemOps ℓ Pt C K) R4)))) :=
  let O := Ops.sum (Ops.sum (atomicPureOps ℓ Pt) R1)
    (Ops.sum R2 (Ops.sum R3 (Ops.sum (atomicSpqrKemOps ℓ Pt C K) R4)))
  { pureE := fun o e => @Expr.op (atomicSig ℓ Pt) O _ (Sum.inl (Sum.inl o)) e
    spqrE := fun o e => @Expr.op (atomicSig ℓ Pt) O _ (Sum.inr (Sum.inr (Sum.inr (Sum.inl o)))) e
    eval_pureE := fun _ _ _ => rfl, cost_pureE := fun _ _ => rfl, size_pureE := fun _ _ => rfl
    eval_spqrE := fun _ _ _ => rfl, cost_spqrE := fun _ _ => rfl, size_spqrE := fun _ _ => rfl }

abbrev e2eEmbed (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    KemTrackOpEmbed ℓ Pt C K (atomicE2EOps ℓ P C K decT encT) :=
  embedE2EShape
    (_root_.ReductionDsl.atomicCurveCheckOps ℓ decT encT)
    (Ops.sum (_root_.ReductionDsl.atomicPtEncOps ℓ encT) (_root_.ReductionDsl.atomicPtDecOps ℓ decT))
    (_root_.ReductionDsl.atomicSymOps ℓ Pt C)
    (_root_.ReductionDsl.atomicPqxdhOps ℓ Pt P)

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

@[expose, reducible] def kemSessionTrackT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (kemTrackT ℓ Pt) (.list (honestWireEntryT ℓ Pt))

@[expose] def kemCandVecToBv (p : SimKemSeed × SimKemEncRand) : BitVec 512 × BitVec 256 :=
  (bytesToWordLE 512 p.1.toList, bytesToWordLE 256 p.2.toList)

@[expose] def kemCandBvToVec (p : BitVec 512 × BitVec 256) : SimKemSeed × SimKemEncRand :=
  (⟨coinBytes p.1, coinBytes_length p.1⟩, keyToBytesVec32 p.2)

@[expose, reducible] def kemCoinsAtomicEnc {ℓ : ℕ} {Pt : Type} : SimKemCoins → (kemCoinsT ℓ Pt).denote
  | .init => .inl ()
  | .seed s => .inr (.inl (bytesToWordLE 512 s.toList))
  | .both s r => .inr (.inr (bytesToWordLE 512 s.toList, bytesToWordLE 256 r.toList))

@[expose, reducible] def kemTrackAtomicEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (tr : SimKemFailTrack F) : (kemTrackT ℓ Pt).denote :=
  (tr.e,
   (kemCoinsAtomicEnc tr.c,
    ((V1State.encodeRaw (tr.st .A).into_pb, V1State.encodeRaw (tr.st .B).into_pb),
     (tr.sentB.map (fun (m, ctr) => ((m.epoch, spqrMsgPayloadSuffix m), ctr)),
      ((tr.sendCtr .A, tr.sendCtr .B),
       tr.cand.map kemCandVecToBv)))))

/-- Per-session tracker state pairing `SimKemFailTrack F` with prepend-only `(wire, sender)` history. -/
abbrev SimKemSessionTrack (F : ShaCompress) (C : Type) : Type :=
  SimKemFailTrack F × List (C × Party)

@[expose] def simInitKemSessionTrack (F : ShaCompress) (C : Type) (k : BitVec 256) :
    SimKemSessionTrack F C :=
  (simInitKemFailTrack F k, [])

@[expose, reducible] def kemSessionTrackAtomicEnc {ℓ : ℕ} {Pt : Type} {F : ShaCompress}
    (st : SimKemSessionTrack F Bytes) : (kemSessionTrackT ℓ Pt).denote :=
  (kemTrackAtomicEnc st.1, st.2.map fun (w, P) => (w, partyToBool P))

@[expose, reducible] def honestPairEnc {ℓ : ℕ} {Pt : Type} (wc : Bytes × SimFig8C Pt) :
    Bytes × (fig8CtT (ℓ := ℓ) (Pt := Pt)).denote :=
  (wc.1, fig8CtV wc.2)

section Combinators

variable {ℓ : ℕ} {Pt : Type} {C : Crypto} {K : MlKem} {O : Ops (atomicSig ℓ Pt)}

local notation "ASig" => atomicSig ℓ Pt

@[expose] def trE_e {Γ : List (Ty ASig)} (tr : Expr O Γ (kemTrackT ℓ Pt)) : Expr O Γ U64 := .fst tr
@[expose] def trE_c {Γ : List (Ty ASig)} (tr : Expr O Γ (kemTrackT ℓ Pt)) : Expr O Γ (kemCoinsT ℓ Pt) :=
  .fst (.snd tr)
@[expose] def trE_st {Γ : List (Ty ASig)} (tr : Expr O Γ (kemTrackT ℓ Pt)) :
    Expr O Γ (.prod (B 32) (B 32)) := .fst (.snd (.snd tr))
@[expose] def trE_sentB {Γ : List (Ty ASig)} (tr : Expr O Γ (kemTrackT ℓ Pt)) :
    Expr O Γ (.list (kemSentEntryT ℓ Pt)) := .fst (.snd (.snd (.snd tr)))
@[expose] def trE_sendCtr {Γ : List (Ty ASig)} (tr : Expr O Γ (kemTrackT ℓ Pt)) :
    Expr O Γ (.prod (.tbl .nat) (.tbl .nat)) := .fst (.snd (.snd (.snd (.snd tr))))
@[expose] def trE_cand {Γ : List (Ty ASig)} (tr : Expr O Γ (kemTrackT ℓ Pt)) :
    Expr O Γ (.opt (.prod BV512 BV256)) := .snd (.snd (.snd (.snd (.snd tr))))
@[expose] def trCandIsSomeE {Γ : List (Ty ASig)} (tr : Expr O Γ (kemTrackT ℓ Pt)) : Expr O Γ .bool :=
  .caseOpt (trE_cand tr) (.bool false) (.bool true)

@[expose] def trMk {Γ : List (Ty ASig)}
    (e : Expr O Γ U64) (c : Expr O Γ (kemCoinsT ℓ Pt))
    (st : Expr O Γ (.prod (B 32) (B 32)))
    (sentB : Expr O Γ (.list (kemSentEntryT ℓ Pt)))
    (sendCtr : Expr O Γ (.prod (.tbl .nat) (.tbl .nat)))
    (cand : Expr O Γ (.opt (.prod BV512 BV256))) : Expr O Γ (kemTrackT ℓ Pt) :=
  .pair e (.pair c (.pair st (.pair sentB (.pair sendCtr cand))))

@[expose] def pGet {Γ : List (Ty ASig)} {t : Ty ASig}
    (p : Expr O Γ (.prod t t)) (qB : Expr O Γ .bool) : Expr O Γ t :=
  .ite qB (.snd p) (.fst p)

@[expose] def pSet {Γ : List (Ty ASig)} {t : Ty ASig}
    (p : Expr O Γ (.prod t t)) (qB : Expr O Γ .bool) (v : Expr O Γ t) : Expr O Γ (.prod t t) :=
  .letE (.pair p (.pair qB v))
    (.pair (.ite (.fst (.snd .v0)) (.fst (.fst .v0)) (.snd (.snd .v0)))
           (.ite (.fst (.snd .v0)) (.snd (.snd .v0)) (.snd (.fst .v0))))

@[expose] def boolOrE {Γ : List (Ty ASig)} (a b : Expr O Γ .bool) : Expr O Γ .bool :=
  .ite a (.bool true) b

@[expose] def boolEqE {Γ : List (Ty ASig)} (a b : Expr O Γ .bool) : Expr O Γ .bool :=
  .ite a b (.not b)

@[expose] def bytes2EqLitE (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (x : Expr O Γ (B 2)) (b0 b1 : BitVec 8) : Expr O Γ .bool :=
  emb.pureE (.bytesEq 2 2) (.pair x (emb.pureE (.bytesLit 2 [b0, b1]) .unit))

@[expose] def issue1275ScanStepE (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)} :
    Expr O (.prod (B 512) (.opt .bool) :: Γ) (.prod (B 512) (.opt .bool)) :=
  let rem : Expr O _ (B 512) := .fst .v0
  .caseOpt (.snd .v0)
    (.ite (.lt (.nat 1) (emb.pureE (.bytesLen 512) rem))
      (.letE (emb.pureE (.bytesTakeK 512 2) rem)
        (let p2 : Expr O (B 2 :: .prod (B 512) (.opt .bool) :: Γ) (B 2) := .v0
         let rem1 : Expr O (B 2 :: .prod (B 512) (.opt .bool) :: Γ) (B 512) := .fst .v1
         let b2eq := bytes2EqLitE emb p2
         let isCont := boolOrE (b2eq 0x00#8 0x00#8) (b2eq 0xff#8 0xff#8)
         let isFlip := boolOrE (b2eq 0x00#8 0x01#8)
           (boolOrE (b2eq 0x00#8 0x02#8) (b2eq 0xff#8 0xfe#8))
         .ite isCont
           (.pair (emb.pureE (.bytesDrop 512) (.pair (.nat 2) rem1)) .none)
           (.pair rem1 (.some isFlip))))
      (.pair rem (.some (.bool false))))
    .v1

@[expose] def swapPairsStep64E (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)} :
    Expr O (.prod (B 64) (B 64) :: Γ) (.prod (B 64) (B 64)) :=
  let rem : Expr O _ (B 64) := .fst .v0
  let acc : Expr O _ (B 64) := .snd .v0
  .ite (.lt (.nat 1) (emb.pureE (.bytesLen 64) rem))
    (let b0 : Expr O _ (B 1) := emb.pureE (.bytesTakeK 64 1) rem
     let b1 : Expr O _ (B 1) := emb.pureE (.bytesTakeK 64 1)
       (emb.pureE (.bytesDrop 64) (.pair (.nat 1) rem))
     let swapped2 : Expr O _ (B (1 + 1)) := emb.pureE (.bytesCat 1 1) (.pair b1 b0)
     let rest : Expr O _ (B 64) := emb.pureE (.bytesDrop 64) (.pair (.nat 2) rem)
     let acc' : Expr O _ (B 64) := emb.pureE (.bytesTakeK (64 + (1 + 1)) 64)
       (emb.pureE (.bytesCat 64 (1 + 1)) (.pair acc swapped2))
     .pair rest acc')
    .v0

@[expose] def swapChunk64StepC (emb : KemTrackOpEmbed ℓ Pt C K O) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)} :
    Comp O I (.prod (B 2048) (B 2048) :: Γ) (.prod (B 2048) (B 2048)) :=
  let rem : Expr O _ (B 2048) := .fst .v0
  .ite (.lt (.nat 63) (emb.pureE (.bytesLen 2048) rem))
    (.bind
      (.iter 32
        (.pair (emb.pureE (.bytesTakeK 2048 64) rem) (emb.pureE (.bytesLit 64 []) .unit))
        (.ret (swapPairsStep64E emb)))
      (let chunkSwapped : Expr O _ (B 64) := .snd .v0
       let remOuter : Expr O _ (B 2048) := .fst .v1
       let accOuter : Expr O _ (B 2048) := .snd .v1
       let restOuter : Expr O _ (B 2048) := emb.pureE (.bytesDrop 2048) (.pair (.nat 64) remOuter)
       let accOuter' : Expr O _ (B 2048) := emb.pureE (.bytesTakeK (2048 + 64) 2048)
         (emb.pureE (.bytesCat 2048 64) (.pair accOuter chunkSwapped))
       .ret (.pair restOuter accOuter')))
    (.ret .v0)

/-- Polymorphic computation for `(potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es).getD es`. -/
@[expose] def issue1275FixEsC (emb : KemTrackOpEmbed ℓ Pt C K O) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)} (esE : Expr O Γ (B 2080)) : Comp O I Γ (B 2080) :=
  .bind (.ret esE)
    (let errSlice : Expr O (B 2080 :: Γ) (B 512) :=
       emb.pureE (.bytesTakeK 2080 512) (emb.pureE (.bytesDrop 2080) (.pair (.nat 1536) .v0))
     .bind
       (.iter 256 (.pair errSlice .none) (.ret (issue1275ScanStepE emb)))
       (let needsFlip : Expr O (.prod (B 512) (.opt .bool) :: B 2080 :: Γ) .bool :=
          .caseOpt (.snd .v0) (.bool false) .v0
        .ite needsFlip
          (let initSwap : Expr O _ (.prod (B 2048) (B 2048)) :=
             .pair (emb.pureE (.bytesTakeK 2080 2048) .v1) (emb.pureE (.bytesLit 2048 []) .unit)
           .bind
             (.iter 32 initSwap (swapChunk64StepC emb))
             (let tail32 := emb.pureE (.bytesTakeK 2080 32)
                (emb.pureE (.bytesDrop 2080) (.pair (.nat 2048) .v2))
              .ret (emb.pureE (.bytesTakeK (2048 + 32) 2080)
                (emb.pureE (.bytesCat 2048 32) (.pair (.snd .v0) tail32)))))
          (.ret .v1)))

/-- Polymorphic computation for `K.honestExchangeFails`. -/
@[expose] def honestExchangeFailsC (emb : KemTrackOpEmbed ℓ Pt C K O) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)}
    (seedE : Expr O Γ BV512) (randE : Expr O Γ BV256) : Comp O I Γ .bool :=
  .bind (.ret (.pair (emb.spqrE .kem768FromSeed seedE) randE))
    (let hdr1 := Expr.fst (.fst .v0)
     let rand1 := Expr.snd .v0
     .caseOpt (emb.spqrE .kem768Encaps1 (.pair hdr1 rand1))
       (.ret (.bool true))
       (let hdr2 := Expr.fst (.fst .v1)
        let ek2 := Expr.fst (.snd (.fst .v1))
        let es2 := Expr.fst (.snd .v0)
        .ite (.not (emb.spqrE .kem768ValidPk (.pair hdr2 ek2)))
          (.ret (.bool true))
          (.bind
            (issue1275FixEsC emb es2)
            (let ek3 := Expr.fst (.snd (.fst .v2))
             .ret
               (Expr.caseOpt (emb.spqrE .kem768Encaps2 (.pair .v0 ek3))
                 (.bool true)
                 (Expr.caseOpt
                   (emb.spqrE .kem768Decaps (.pair (.snd (.snd (.fst .v3))) (.pair (.fst .v2) .v0)))
                   (.bool true)
                   (.not (emb.pureE .bv256Eq (.pair .v0 (.snd (.snd .v3)))))))))))

@[expose] def initV1BraidStE (emb : KemTrackOpEmbed ℓ Pt C K O) (isAlice : Bool) {Γ : List (Ty ASig)}
    (pqrKeyE : Expr O Γ BV256) : Expr O Γ (B 32) :=
  let ver1 := emb.pureE (.u8Lit 1#8) .unit
  let dirE := emb.pureE (.u32Lit (if isAlice then 0#32 else 1#32)) .unit
  let authKeyE := emb.pureE .bv256ToBytes32 pqrKeyE
  .caseOpt (.snd (emb.spqrE .spqrNegotiateInit (.pair ver1 (.pair dirE authKeyE))))
    (emb.pureE (.bytesLit 32 []) .unit)
    (.caseOpt .v0 (emb.pureE (.bytesLit 32 []) .unit) .v0)

@[expose] def initKemFailTrackE (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (pqrKeyE : Expr O Γ BV256) : Expr O Γ (kemTrackT ℓ Pt) :=
  .letE pqrKeyE
    (.pair (emb.pureE (.u64Lit 1#64) .unit)
      (.pair (.inl .unit)
        (.pair (.pair (initV1BraidStE emb true .v0) (initV1BraidStE emb false .v0))
          (.pair .nil
            (.pair (.pair (.tconst (.nat 0)) (.tconst (.nat 0))) .none)))))

@[expose] def initKemFailSessionTrackE (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (pqrKeyE : Expr O Γ BV256) : Expr O Γ (kemSessionTrackT ℓ Pt) :=
  .pair (initKemFailTrackE emb pqrKeyE) .nil

@[expose] def encRandBvE (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (rqE : Expr O Γ BV512) : Expr O Γ BV256 :=
  emb.pureE .bytesToBv256 (emb.pureE (.bytesTakeK 64 32) (emb.pureE .bv512ToBytes64 rqE))

@[expose] def isKeysUnsampledV1E (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (v1E : Expr O Γ (B 32)) : Expr O Γ .bool :=
  emb.pureE (.bytesEq 1 1) (.pair (emb.pureE (.bytesTakeK 32 1) v1E) (emb.pureE (.bytesLit 1 [0x0a#8]) .unit))

@[expose] def isHeaderReceivedV1E (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (v1E : Expr O Γ (B 32)) : Expr O Γ .bool :=
  emb.pureE (.bytesEq 1 1) (.pair (emb.pureE (.bytesTakeK 32 1) v1E) (emb.pureE (.bytesLit 1 [0x3a#8]) .unit))

@[expose] def ekSideIsAE (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (eE : Expr O Γ U64) : Expr O Γ .bool :=
  .eqN (.modK 2 (emb.pureE .u64ToNat eE)) (.nat 1)

@[expose] def nextKemCoinsE (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (cE : Expr O Γ (kemCoinsT ℓ Pt)) (v1QE : Expr O Γ (B 32))
    (rqE : Expr O Γ BV512) : Expr O Γ (kemCoinsT ℓ Pt) :=
  .letE (.pair cE (.pair v1QE rqE))
    (.caseSum (.fst .v0)
      (.ite (isKeysUnsampledV1E emb (.fst (.snd .v1)))
        (.inr (.inl (.snd (.snd .v1))))
        (.inl .unit))
      (.caseSum .v0
        (.ite (isHeaderReceivedV1E emb (.fst (.snd .v2)))
          (.inr (.inr (.pair .v0 (encRandBvE emb (.snd (.snd .v2))))))
          (.inr (.inl .v0)))
        (.inr (.inr .v0))))

@[expose] def nextKemCandC (emb : KemTrackOpEmbed ℓ Pt C K O) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) : Comp O I Γ (.opt (.prod BV512 BV256)) :=
  .bind (.ret (.pair trE (.pair qBE rqE)))
    (let tr0 : Expr O _ (kemTrackT ℓ Pt) := .fst .v0
     let q0 : Expr O _ .bool := .fst (.snd .v0)
     .caseOpt (trE_cand tr0)
       (let v1Q := pGet (trE_st tr0) q0
        let cond := Expr.and (boolEqE (ekSideIsAE emb (trE_e tr0)) q0) (isHeaderReceivedV1E emb v1Q)
        .ite cond
          (.caseSum (trE_c tr0)
            (.ret .none)
            (.caseSum .v0
              (.bind (honestExchangeFailsC emb .v0 (encRandBvE emb (.snd (.snd .v2))))
                (.ret (.ite .v0 (.some (.pair .v1 (encRandBvE emb (.snd (.snd .v3))))) .none)))
              (.ret .none)))
          (.ret .none))
       (.ret (.some .v0)))

@[expose] def stepPostKemSendE (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) (candE : Expr O Γ (.opt (.prod BV512 BV256))) :
    Expr O Γ (.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)) :=
  .letE (.pair trE (.pair qBE (.pair rqE candE)))
    (let tr0 : Expr O _ (kemTrackT ℓ Pt) := .fst .v0
     let q0 : Expr O _ .bool := .fst (.snd .v0)
     let rq0 : Expr O _ BV512 := .fst (.snd (.snd .v0))
     let cand0 : Expr O _ (.opt (.prod BV512 BV256)) := .snd (.snd (.snd .v0))
     let v1Q := pGet (trE_st tr0) q0
     let trCandOnly := trMk (trE_e tr0) (trE_c tr0) (trE_st tr0)
       (trE_sentB tr0) (trE_sendCtr tr0) cand0
     .caseOpt (.snd (emb.spqrE .spqrBraidSend (.pair v1Q rq0)))
       (.pair trCandOnly trCandOnly)
       (let tr1 : Expr O _ (kemTrackT ℓ Pt) := .fst .v1
        let q1 : Expr O _ .bool := .fst (.snd .v1)
        let rq1 : Expr O _ BV512 := .fst (.snd (.snd .v1))
        let cand1 : Expr O _ (.opt (.prod BV512 BV256)) := .snd (.snd (.snd .v1))
        let newV1 := Expr.fst .v0
        let msgEpoch := Expr.fst (.snd .v0)
        let payloadSuffix := Expr.snd (.snd (.snd .v0))
        let epIdx := Expr.sub (emb.pureE .u64ToNat msgEpoch) (.nat 1)
        let ctrTblQ := pGet (trE_sendCtr tr1) q1
        let n1 := Expr.add (.tget ctrTblQ epIdx) (.nat 1)
        let ctrBv := emb.pureE .u32OfNat n1
        let newEntry : Expr O _ (kemSentEntryT ℓ Pt) := .pair (.pair msgEpoch payloadSuffix) ctrBv
        let sentB' := Expr.appendL (q + 1) (trE_sentB tr1) (.cons newEntry .nil)
        let sendCtr' := pSet (trE_sendCtr tr1) q1 (.tset ctrTblQ epIdx n1)
        let st' := pSet (trE_st tr1) q1 newV1
        let c' := nextKemCoinsE emb (trE_c tr1) (pGet (trE_st tr1) q1) rq1
        let trFull := trMk (trE_e tr1) c' st' sentB' sendCtr' cand1
        let trCandOnly1 := trMk (trE_e tr1) (trE_c tr1) (trE_st tr1)
          (trE_sentB tr1) (trE_sendCtr tr1) cand1
        .pair trFull trCandOnly1))

@[expose] def stepKemFailSendPairC (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) : Comp O I Γ (.prod (kemTrackT ℓ Pt) (kemTrackT ℓ Pt)) :=
  .bind (.ret (.pair trE (.pair qBE rqE)))
    (.bind (nextKemCandC emb (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)))
      (.ret (stepPostKemSendE emb q (.fst .v1) (.fst (.snd .v1)) (.snd (.snd .v1)) .v0)))

/-- Tracker-halted send step returning `(halted, trOut)`, latching `cand` without advancing braid state when `cand.isSome`. -/
@[expose] def stepKemFailSendC (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) : Comp O I Γ (.prod .bool (kemTrackT ℓ Pt)) :=
  .bind (stepKemFailSendPairC emb q trE qBE rqE)
    (.ret (.ite (trCandIsSomeE (.fst .v0))
      (.pair (.bool true) (.snd .v0))
      (.pair (.bool false) (.fst .v0))))

@[expose] def prependHonestWireE {Γ : List (Ty ASig)}
    (trOutE : Expr O Γ (kemTrackT ℓ Pt))
    (hwE : Expr O Γ (.list (honestWireEntryT ℓ Pt)))
    (wE : Expr O Γ (B 32)) (pBE : Expr O Γ .bool) : Expr O Γ (kemSessionTrackT ℓ Pt) :=
  .pair trOutE (.cons (.pair wE pBE) hwE)

@[expose] def b64Take48ToB32E (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)}
    (suf : Expr O Γ (B 64)) : Expr O Γ (B 32) :=
  emb.pureE (.bytesDrop 32)
    (.pair (.nat 3)
      (emb.pureE .spqrAssembleMsg
        (.pair (emb.pureE (.u64Lit 0#64) .unit)
          (.pair (emb.pureE (.u32Lit 0#32) .unit) suf))))

@[expose] def listNthOptB (L : ℕ) {t : Ty ASig} {Γ : List (Ty ASig)}
    (xsE : Expr O Γ (.list t)) (jE : Expr O Γ .nat) : Expr O Γ (.opt t) :=
  .letE (.pair xsE jE)
    (let xs := Expr.fst .v0
     let len := Expr.foldrB L xs (.nat 0) (.add (.nat 1) .v1)
     .snd (.foldrB L xs (.pair len .none)
       (let dec := Expr.sub (.fst .v1) (.nat 1)
        .pair dec (.ite (.eqN dec (.snd .v2)) (.some .v0) (.snd .v1)))))

/-- Bounded reverse index lookup in `honestWires` matching `(w, Q.other)`. -/
@[expose] def findRevHonestWireIdxE (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ) {Γ : List (Ty ASig)}
    (hwE : Expr O Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr O Γ .bool) (wE : Expr O Γ (B 32)) : Expr O Γ (.opt .nat) :=
  .letE (.pair hwE (.pair qBE wE))
    (.fst (.foldrB L (.fst .v0) (.pair .none (.nat 0))
      (let qOtherB := Expr.not (.fst (.snd .v2))
       let w := Expr.snd (.snd .v2)
       let eqW := emb.pureE (.bytesEq 32 32) (.pair (.fst .v0) w)
       let eqSender := boolEqE (.snd .v0) qOtherB
       let matched := Expr.and eqW eqSender
       let prevOpt := Expr.fst .v1
       let cnt := Expr.snd .v1
       let nextOpt := Expr.caseOpt prevOpt (.ite matched (.some cnt) .none) (.some .v0)
       .pair nextOpt (.add cnt (.nat 1)))))

/-- Bounded reverse index lookup in `sC.base.honest` matching `(w, Q.other)`. -/
@[expose] def findRevHonestIdxE (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ) {Γ : List (Ty ASig)}
    (honestE : Expr O Γ (.list (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
    (qBE : Expr O Γ .bool) (wE : Expr O Γ (B 32)) : Expr O Γ (.opt .nat) :=
  .letE (.pair honestE (.pair qBE wE))
    (.fst (.foldrB L (.fst .v0) (.pair .none (.nat 0))
      (let qOtherB := Expr.not (.fst (.snd .v2))
       let w := Expr.snd (.snd .v2)
       let epEntry := Expr.fst (.fst (.snd .v0))
       let eqW := emb.pureE (.bytesEq 32 32) (.pair (.fst .v0) w)
       let eqSender := Expr.ite qOtherB (.eqN (.modK 2 epEntry) (.nat 0)) (.eqN (.modK 2 epEntry) (.nat 1))
       let matched := Expr.and eqW eqSender
       let prevOpt := Expr.fst .v1
       let cnt := Expr.snd .v1
       let nextOpt := Expr.caseOpt prevOpt (.ite matched (.some cnt) .none) (.some .v0)
       .pair nextOpt (.add cnt (.nat 1)))))

/-- Expression implementing `simStepKemFailDeliver` at index `jE`. -/
@[expose] def stepKemFailDeliverE (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ) {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jE : Expr O Γ .nat) : Expr O Γ (kemTrackT ℓ Pt) :=
  .letE (.pair trE (.pair qBE jE))
    (let tr0 := Expr.fst .v0
     let j0 := Expr.snd (.snd .v0)
     .caseOpt (listNthOptB L (trE_sentB tr0) j0) tr0
       (let tr1 := Expr.fst .v1
        let q1 := Expr.fst (.snd .v1)
        let mEp1 := Expr.fst (.fst .v0)
        let mSuf1 := b64Take48ToB32E emb (.snd (.fst .v0))
        let stQ1 := pGet (trE_st tr1) q1
        let recvOut := emb.spqrE .spqrBraidRecv (.pair stQ1 (.pair mEp1 mSuf1))
        .caseOpt (.snd (.snd recvOut)) tr1
          (let newV1 := Expr.snd .v0
           let mEp2 := Expr.fst (.fst .v1)
           let mSuf2 := b64Take48ToB32E emb (.snd (.fst .v1))
           let tr2 := Expr.fst .v2
           let q2 := Expr.fst (.snd .v2)
           let e2 := trE_e tr2
           let c2 := trE_c tr2
           let v1Pair' := pSet (trE_st tr2) q2 newV1
           let rest2 := Expr.snd (.snd (.snd tr2))
           let eNext := emb.pureE .u64Add (.pair e2 (emb.pureE (.u64Lit 1#64) .unit))
           let isNoneNext := Expr.and
             (emb.pureE .u64Eq (.pair mEp2 eNext))
             (emb.pureE (.bytesEq 32 32) (.pair mSuf2 (emb.pureE (.bytesLit 32 [0#8]) .unit)))
           let isBoth := Expr.caseSum c2 (.bool false) (.caseSum .v0 (.bool false) (.bool true))
           let advance := Expr.and isNoneNext isBoth
           .pair (.ite advance eNext e2)
             (.pair (.ite advance (.inl .unit) c2) (.pair v1Pair' rest2)))))

@[expose] def stepKemFailDeliverC (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jE : Expr O Γ .nat) : Comp O I Γ (kemTrackT ℓ Pt) :=
  .ret (stepKemFailDeliverE emb L trE qBE jE)

@[expose] def stepKemSessionDeliverOptE (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr O Γ (kemSessionTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jOptE : Expr O Γ (.opt .nat)) : Expr O Γ (kemSessionTrackT ℓ Pt) :=
  .letE (.pair stE (.pair qBE jOptE))
    (let st0 := Expr.fst .v0
     .caseOpt (.snd (.snd .v0)) st0
       (.pair (stepKemFailDeliverE emb L (.fst (.fst .v1)) (.fst (.snd .v1)) .v0)
              (.snd (.fst .v1))))

@[expose] def kemOnDeliverPostE (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr O Γ .bool) (jOptE : Expr O Γ (.opt .nat))
    (rrOptE : Expr O Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr O Γ (kemTrackT ℓ Pt)) : Expr O Γ (kemTrackT ℓ Pt) :=
  .letE (.pair qBE (.pair jOptE (.pair rrOptE trE)))
    (.caseOpt (.fst (.snd (.snd .v0))) (.snd (.snd (.snd .v0)))
      (.caseSum .v0 (.snd (.snd (.snd .v2)))
        (.caseOpt (.fst (.snd .v2)) (.snd (.snd (.snd .v2)))
          (stepKemFailDeliverE emb L (.snd (.snd (.snd .v3))) (.fst .v3) .v0))))

end Combinators

section SessionAliases
variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {encT : Pt → PublicKey}
  {decT : PublicKey → Option Pt} {lam : Pt} {Γ : List (Ty (atomicSig ℓ Pt))}
local notation "SOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "sEmb" => sessionEmbed ℓ Pt C K Dh encPt encT decT lam

abbrev initKemFailTrackPolyE (pqrKeyE : Expr SOps Γ BV256) := initKemFailTrackE sEmb pqrKeyE
abbrev initKemFailSessionTrackPolyE (pqrKeyE : Expr SOps Γ BV256) :=
  initKemFailSessionTrackE sEmb pqrKeyE
abbrev stepKemFailSendPairPolyC (q : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (trE : Expr SOps Γ (kemTrackT ℓ Pt))
    (qBE : Expr SOps Γ .bool) (rqE : Expr SOps Γ BV512) :=
  stepKemFailSendPairC sEmb q (I := I) trE qBE rqE
abbrev stepKemFailSendPolyC (q : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (trE : Expr SOps Γ (kemTrackT ℓ Pt))
    (qBE : Expr SOps Γ .bool) (rqE : Expr SOps Γ BV512) :=
  stepKemFailSendC sEmb q (I := I) trE qBE rqE
abbrev stepKemFailDeliverPolyE (L : ℕ) (trE : Expr SOps Γ (kemTrackT ℓ Pt))
    (qBE : Expr SOps Γ .bool) (jE : Expr SOps Γ .nat) :=
  stepKemFailDeliverE sEmb L trE qBE jE
abbrev stepKemFailDeliverPolyC (L : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (trE : Expr SOps Γ (kemTrackT ℓ Pt))
    (qBE : Expr SOps Γ .bool) (jE : Expr SOps Γ .nat) :=
  stepKemFailDeliverC sEmb L (I := I) trE qBE jE
abbrev stepKemSessionDeliverOptPolyE (L : ℕ) (stE : Expr SOps Γ (kemSessionTrackT ℓ Pt))
    (qBE : Expr SOps Γ .bool) (jOptE : Expr SOps Γ (.opt .nat)) :=
  stepKemSessionDeliverOptE sEmb L stE qBE jOptE
abbrev kemOnDeliverPostPolyE (L : ℕ) (qBE : Expr SOps Γ .bool) (jOptE : Expr SOps Γ (.opt .nat))
    (rrOptE : Expr SOps Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr SOps Γ (kemTrackT ℓ Pt)) :=
  kemOnDeliverPostE sEmb L qBE jOptE rrOptE trE
abbrev findRevHonestWireIdxPolyE (L : ℕ) (hwE : Expr SOps Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr SOps Γ .bool) (wE : Expr SOps Γ (B 32)) :=
  findRevHonestWireIdxE sEmb L hwE qBE wE
abbrev findRevHonestIdxPolyE (L : ℕ)
    (honestE : Expr SOps Γ (.list (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
    (qBE : Expr SOps Γ .bool) (wE : Expr SOps Γ (B 32)) :=
  findRevHonestIdxE sEmb L honestE qBE wE
end SessionAliases

section E2EAliases
variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} {Γ : List (Ty (atomicSig ℓ Pt))}
local notation "EOps" => atomicE2EOps ℓ P C K decT encT
local notation "eEmb" => e2eEmbed ℓ P C K decT encT

abbrev initKemFailTrackE2EE (pqrKeyE : Expr EOps Γ BV256) := initKemFailTrackE eEmb pqrKeyE
abbrev initKemFailSessionTrackE2EE (pqrKeyE : Expr EOps Γ BV256) :=
  initKemFailSessionTrackE eEmb pqrKeyE
abbrev stepKemFailSendE2EC (q : ℕ) {ι : Type} {T : OracleSpec ι}
    {I : Iface (atomicSig ℓ Pt) T} (trE : Expr EOps Γ (kemTrackT ℓ Pt))
    (qBE : Expr EOps Γ .bool) (rqE : Expr EOps Γ BV512) :=
  stepKemFailSendC eEmb q (I := I) trE qBE rqE
abbrev stepKemFailDeliverE2EE (L : ℕ) (trE : Expr EOps Γ (kemTrackT ℓ Pt))
    (qBE : Expr EOps Γ .bool) (jE : Expr EOps Γ .nat) :=
  stepKemFailDeliverE eEmb L trE qBE jE
abbrev stepKemSessionDeliverOptE2EE (L : ℕ) (stE : Expr EOps Γ (kemSessionTrackT ℓ Pt))
    (qBE : Expr EOps Γ .bool) (jOptE : Expr EOps Γ (.opt .nat)) :=
  stepKemSessionDeliverOptE eEmb L stE qBE jOptE
abbrev findRevHonestWireIdxE2EE (L : ℕ) (hwE : Expr EOps Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr EOps Γ .bool) (wE : Expr EOps Γ (B 32)) :=
  findRevHonestWireIdxE eEmb L hwE qBE wE
end E2EAliases


/-! ## Static query, cost, and size bounds -/

section CostAndSizeBounds

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} {C : Crypto} {K : MlKem} {O : Ops (atomicSig ℓ Pt)}

local notation "ASig" => atomicSig ℓ Pt

private theorem hb0 : bits 0 = 1 := by decide
private theorem hb1 : bits 1 = 1 := by decide
private theorem hb2 : bits 2 = 2 := by decide
private theorem hb3 : bits 3 = 2 := by decide
private theorem hb32 : bits 32 = 6 := by decide
private theorem hb63 : bits 63 = 6 := by decide
private theorem hb64 : bits 64 = 7 := by decide
private theorem hb256 : bits 256 = 9 := by decide
private theorem hb512 : bits 512 = 10 := by decide
private theorem hb1536 : bits 1536 = 11 := by decide
private theorem hb2048 : bits 2048 = 12 := by decide

@[simp] theorem swapChunk64StepC_queries_zero (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (swapChunk64StepC emb (I := I) (Γ := Γ)).queries w ws = 0 := by
  simp [swapChunk64StepC, Comp.queries]
@[simp] theorem issue1275FixEsC_queries_zero (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (esE : Expr O Γ (B 2080)) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (issue1275FixEsC emb (I := I) esE).queries w ws = 0 := by
  simp [issue1275FixEsC, Comp.queries]
@[simp] theorem honestExchangeFailsC_queries_zero (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr O Γ BV512) (randE : Expr O Γ BV256)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (honestExchangeFailsC emb (I := I) seedE randE).queries w ws = 0 := by
  simp [honestExchangeFailsC, Comp.queries]
@[simp] theorem honestExchangeFailsC_nq_zero (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr O Γ BV512) (randE : Expr O Γ BV256) :
    (honestExchangeFailsC emb (I := I) seedE randE).nq = 0 := by
  simp only [Comp.nq, honestExchangeFailsC_queries_zero]
@[simp] theorem nextKemCandC_queries_zero (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (nextKemCandC emb (I := I) trE qBE rqE).queries w ws = 0 := by
  simp [nextKemCandC, Comp.queries]
@[simp] theorem stepKemFailSendPairC_queries_zero (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (stepKemFailSendPairC emb q (I := I) trE qBE rqE).queries w ws = 0 := by
  simp [stepKemFailSendPairC, Comp.queries]
@[simp] theorem stepKemFailSendPairC_nq_zero (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) :
    (stepKemFailSendPairC emb q (I := I) trE qBE rqE).nq = 0 := by
  simp only [Comp.nq, stepKemFailSendPairC_queries_zero]
@[simp] theorem stepKemFailSendC_queries_zero (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (stepKemFailSendC emb q (I := I) trE qBE rqE).queries w ws = 0 := by
  simp [stepKemFailSendC, Comp.queries]
@[simp] theorem stepKemFailSendC_nq_zero (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (rqE : Expr O Γ BV512) :
    (stepKemFailSendC emb q (I := I) trE qBE rqE).nq = 0 := by
  simp only [Comp.nq, stepKemFailSendC_queries_zero]
@[simp] theorem stepKemFailDeliverC_queries_zero (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jE : Expr O Γ .nat) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (stepKemFailDeliverC emb L (I := I) trE qBE jE).queries w ws = 0 := rfl
@[simp] theorem stepKemFailDeliverC_nq_zero (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jE : Expr O Γ .nat) :
    (stepKemFailDeliverC emb L (I := I) trE qBE jE).nq = 0 := rfl

private theorem issue1275ScanStepE_cost (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)} :
    (issue1275ScanStepE emb (Γ := Γ)).cost = 1080 := by
  have hp2 : ((2 : ℕ+) : ℕ) = 2 := rfl
  have hp512 : ((512 : ℕ+) : ℕ) = 512 := rfl
  simp only [issue1275ScanStepE, bytes2EqLitE, boolOrE, emb.cost_pureE, AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, List.length_cons, List.length_nil, hb1, hb2, hb512, hp2, hp512]
  decide

private theorem swapPairsStep64E_cost (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)} :
    (swapPairsStep64E emb (Γ := Γ)).cost = 487 := by
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hp2 : (((1 : ℕ+) + 1 : ℕ+) : ℕ) = 2 := rfl
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  have hp66 : (((64 : ℕ+) + (1 + 1) : ℕ+) : ℕ) = 66 := rfl
  simp only [swapPairsStep64E, emb.cost_pureE, AtomicPureOp.cost, Expr.cost, Expr.v0,
    hb1, hb2, hp1, hp2, hp64, hp66]
  decide

private theorem swapChunk64StepC_cost (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)} :
    (swapChunk64StepC emb (I := I) (Γ := Γ)).cost ≤ 26200 := by
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  have hp2112 : (((2048 : ℕ+) + 64 : ℕ+) : ℕ) = 2112 := rfl
  have hs64 := swapPairsStep64E_cost emb (Γ := .prod (B 2048) (B 2048) :: Γ)
  dsimp only [swapChunk64StepC]
  generalize swapPairsStep64E emb (Γ := .prod (B 2048) (B 2048) :: Γ) = e64 at hs64 ⊢
  simp only [Comp.cost, emb.cost_pureE, AtomicPureOp.cost, Expr.cost, Expr.v0, Expr.v1,
    hb63, hb64, hb2048, hp64, hp2048, hp2112, List.length_nil, hs64]
  omega

theorem issue1275FixEsC_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (esE : Expr O Γ (B 2080)) :
    (issue1275FixEsC emb (I := I) esE).cost ≤ esE.cost + 1140000 := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hp512 : ((512 : ℕ+) : ℕ) = 512 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  have hp2080 : ((2080 : ℕ+) : ℕ) = 2080 := rfl
  have hp2080' : (((2048 : ℕ+) + 32 : ℕ+) : ℕ) = 2080 := rfl
  have hscan := issue1275ScanStepE_cost emb (Γ := B 2080 :: Γ)
  have hchunk := swapChunk64StepC_cost emb (I := I) (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ)
  dsimp only [issue1275FixEsC]
  generalize issue1275ScanStepE emb (Γ := B 2080 :: Γ) = eScan at hscan ⊢
  generalize swapChunk64StepC emb (I := I)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ) = cChunk at hchunk ⊢
  simp only [Comp.cost, emb.cost_pureE, AtomicPureOp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    hb1536, hb2048, hp32, hp512, hp2048, hp2080, hp2080', List.length_nil] at hscan hchunk ⊢
  omega

theorem honestExchangeFailsC_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr O Γ BV512) (randE : Expr O Γ BV256) :
    (honestExchangeFailsC emb (I := I) seedE randE).cost ≤ seedE.cost + randE.cost + 1141000 := by
  let Γ1 := Ty.prod (AtomicSpqrKemOp.kem768FromSeed.cod ℓ Pt) BV256 :: Γ
  let Γ2 := Ty.prod (B 960) (.prod (B 2080) BV256) :: Γ1
  have hfix := issue1275FixEsC_cost_le emb (I := I) (Γ := Γ2) (.fst (.snd .v0))
  dsimp only [honestExchangeFailsC]
  generalize issue1275FixEsC emb (I := I) (Γ := Γ2) (.fst (.snd .v0)) = cFix at hfix ⊢
  simp only [Comp.cost, Expr.cost, emb.cost_spqrE, emb.cost_pureE,
    AtomicSpqrKemOp.cost, AtomicPureOp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hfix ⊢
  omega

theorem initKemFailTrackE_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (pqrKeyE : Expr O Γ BV256) :
    (initKemFailTrackE emb pqrKeyE).cost ≤ pqrKeyE.cost + 3500 := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  simp only [initKemFailTrackE, initV1BraidStE, emb.cost_spqrE, emb.cost_pureE,
    AtomicSpqrKemOp.cost, AtomicPureOp.cost, Expr.cost, Expr.v0, hb0, hp32, List.length_nil]
  omega

theorem initKemFailSessionTrackE_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (pqrKeyE : Expr O Γ BV256) :
    (initKemFailSessionTrackE emb pqrKeyE).cost ≤ pqrKeyE.cost + 3505 := by
  have h := initKemFailTrackE_cost_le emb pqrKeyE
  simp only [initKemFailSessionTrackE, Expr.cost]; omega

private theorem encRandBvE_cost (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (rqE : Expr O Γ BV512) :
    (encRandBvE emb rqE).cost = rqE.cost + 192 := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  simp only [encRandBvE, emb.cost_pureE, AtomicPureOp.cost, hp32, hp64]

theorem nextKemCandC_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool) (rqE : Expr O Γ BV512) :
    (nextKemCandC emb (I := I) trE qBE rqE).cost ≤
      trE.cost + qBE.cost + rqE.cost + 1142000 := by
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  let Γ1 := Ty.sum BV512 (.prod BV512 BV256) :: Γ0
  let Γ2 := BV512 :: Γ1
  have hhef := honestExchangeFailsC_cost_le emb (I := I) (Γ := Γ2) .v0
    (encRandBvE emb (.snd (.snd .v2)))
  dsimp only [nextKemCandC]
  generalize honestExchangeFailsC emb (I := I) (Γ := Γ2) .v0
    (encRandBvE emb (.snd (.snd .v2))) = cHef at hhef ⊢
  simp only [Comp.cost, Expr.cost, encRandBvE_cost, boolEqE, ekSideIsAE, isHeaderReceivedV1E,
    pGet, trE_cand, trE_st, trE_e, trE_c, emb.cost_pureE, AtomicPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1, hb2, hp1, hp32, List.length_cons, List.length_nil] at hhef ⊢
  omega

theorem stepKemFailSendPairC_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool) (rqE : Expr O Γ BV512) :
    (stepKemFailSendPairC emb q (I := I) trE qBE rqE).cost ≤
      trE.cost + qBE.cost + rqE.cost + q + 1155000 := by
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  have hcand := nextKemCandC_cost_le emb (I := I) (Γ := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  dsimp only [stepKemFailSendPairC]
  generalize nextKemCandC emb (I := I) (Γ := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)) = cCand at hcand ⊢
  simp only [Comp.cost, stepPostKemSendE, nextKemCoinsE, isKeysUnsampledV1E, isHeaderReceivedV1E,
    encRandBvE_cost, trMk, pGet, pSet, trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr,
    emb.cost_spqrE, emb.cost_pureE, AtomicSpqrKemOp.cost, AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, hb1, hp1, hp32, List.length_cons, List.length_nil] at hcand ⊢
  omega

theorem stepKemFailSendC_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool) (rqE : Expr O Γ BV512) :
    (stepKemFailSendC emb q (I := I) trE qBE rqE).cost ≤
      trE.cost + qBE.cost + rqE.cost + q + 1160000 := by
  have h := stepKemFailSendPairC_cost_le emb q (I := I) trE qBE rqE
  dsimp only [stepKemFailSendC]
  generalize stepKemFailSendPairC emb q (I := I) trE qBE rqE = cPair at h ⊢
  simp only [Comp.cost, trCandIsSomeE, trE_cand, Expr.cost, Expr.v0]; omega

@[simp] theorem prependHonestWireE_cost {Γ : List (Ty ASig)}
    (trOutE : Expr O Γ (kemTrackT ℓ Pt)) (hwE : Expr O Γ (.list (honestWireEntryT ℓ Pt)))
    (wE : Expr O Γ (B 32)) (pBE : Expr O Γ .bool) :
    (prependHonestWireE trOutE hwE wE pBE).cost =
      trOutE.cost + hwE.cost + wE.cost + pBE.cost + 3 := by
  simp only [prependHonestWireE, Expr.cost]; omega

private theorem b64Take48ToB32E_cost (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (suf : Expr O Γ (B 64)) :
    (b64Take48ToB32E emb suf).cost ≤ suf.cost + 200 := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  simp only [b64Take48ToB32E, emb.cost_pureE, AtomicPureOp.cost, Expr.cost, hb3, hp32]; omega

theorem listNthOptB_cost_le (L : ℕ) {t : Ty ASig} {Γ : List (Ty ASig)}
    (xsE : Expr O Γ (.list t)) (jE : Expr O Γ .nat) :
    (listNthOptB L xsE jE).cost ≤ xsE.cost + jE.cost + 40 * L + 64 := by
  simp [listNthOptB, Expr.cost, Expr.v0, Expr.v1, Expr.v2, hb0, hb1]; omega

theorem findRevHonestWireIdxE_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (hwE : Expr O Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr O Γ .bool) (wE : Expr O Γ (B 32)) :
    (findRevHonestWireIdxE emb L hwE qBE wE).cost ≤
      hwE.cost + qBE.cost + wE.cost + 120 * L + 64 := by
  simp [findRevHonestWireIdxE, boolEqE, emb.cost_pureE, AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, hb0, hb1]; omega

theorem findRevHonestIdxE_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)}
    (honestE : Expr O Γ (.list (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
    (qBE : Expr O Γ .bool) (wE : Expr O Γ (B 32)) :
    (findRevHonestIdxE emb L honestE qBE wE).cost ≤
      honestE.cost + qBE.cost + wE.cost + 140 * L + 64 := by
  simp [findRevHonestIdxE, emb.cost_pureE, AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, hb0, hb1, hb2]; omega

theorem stepKemFailDeliverE_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jE : Expr O Γ .nat) :
    (stepKemFailDeliverE emb L trE qBE jE).cost ≤
      trE.cost + qBE.cost + jE.cost + 40 * L + 8000 := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool .nat) :: Γ
  let Γ1 := kemSentEntryT ℓ Pt :: Γ0
  let Γ2 := Ty.prod (.opt (.prod U64 BV256)) (B 32) :: Γ1
  have hnth := listNthOptB_cost_le (O := O) L (t := kemSentEntryT ℓ Pt) (Γ := Γ0)
    (trE_sentB (.fst .v0)) (.snd (.snd .v0))
  have hb1 := b64Take48ToB32E_cost emb (Γ := Γ1) (.snd (.fst .v0))
  have hb2 := b64Take48ToB32E_cost emb (Γ := Γ2) (.snd (.fst .v1))
  dsimp only [stepKemFailDeliverE]
  generalize listNthOptB (O := O) L (trE_sentB (.fst .v0)) (.snd (.snd .v0)) = eNth at hnth ⊢
  generalize b64Take48ToB32E emb (Γ := Γ1) (.snd (.fst .v0)) = eb1 at hb1 ⊢
  generalize b64Take48ToB32E emb (Γ := Γ2) (.snd (.fst .v1)) = eb2 at hb2 ⊢
  simp only [pGet, pSet, trE_e, trE_c, trE_st, trE_sentB,
    emb.cost_spqrE, emb.cost_pureE, AtomicSpqrKemOp.cost, AtomicPureOp.cost,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, hp32, List.length_cons, List.length_nil] at hnth hb1 hb2 ⊢
  omega

theorem stepKemFailDeliverC_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool) (jE : Expr O Γ .nat) :
    (stepKemFailDeliverC emb L (I := I) trE qBE jE).cost ≤
      trE.cost + qBE.cost + jE.cost + 40 * L + 8001 := by
  have h := stepKemFailDeliverE_cost_le emb L trE qBE jE
  simp only [stepKemFailDeliverC, Comp.cost]; omega

theorem stepKemSessionDeliverOptE_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (stE : Expr O Γ (kemSessionTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jOptE : Expr O Γ (.opt .nat)) :
    (stepKemSessionDeliverOptE emb L stE qBE jOptE).cost ≤
      stE.cost + qBE.cost + jOptE.cost + 40 * L + 8020 := by
  let Γ1 := Ty.nat :: Ty.prod (kemSessionTrackT ℓ Pt) (.prod .bool (.opt .nat)) :: Γ
  have h := stepKemFailDeliverE_cost_le emb L (Γ := Γ1) (.fst (.fst .v1)) (.fst (.snd .v1)) .v0
  dsimp only [stepKemSessionDeliverOptE]
  generalize stepKemFailDeliverE emb L (Γ := Γ1) (.fst (.fst .v1)) (.fst (.snd .v1)) .v0 = eD at h ⊢
  simp only [Expr.cost, Expr.v0, Expr.v1] at h ⊢; omega

theorem kemOnDeliverPostE_cost_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (qBE : Expr O Γ .bool) (jOptE : Expr O Γ (.opt .nat))
    (rrOptE : Expr O Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr O Γ (kemTrackT ℓ Pt)) :
    (kemOnDeliverPostE emb L qBE jOptE rrOptE trE).cost ≤
      qBE.cost + jOptE.cost + rrOptE.cost + trE.cost + 40 * L + 8040 := by
  let t0 := Ty.prod .bool (.prod (.opt .nat) (.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (kemTrackT ℓ Pt)))
  let Γ3 := Ty.nat :: Ty.prod .nat (.prod .nat (.opt (_root_.ReductionDsl.PlainT (ℓ := ℓ) (Pt := Pt)))) ::
    recvResultT (ℓ := ℓ) (Pt := Pt) :: t0 :: Γ
  have h := stepKemFailDeliverE_cost_le emb L (Γ := Γ3) (.snd (.snd (.snd .v3))) (.fst .v3) .v0
  dsimp only [kemOnDeliverPostE]
  generalize stepKemFailDeliverE emb L (Γ := Γ3) (.snd (.snd (.snd .v3))) (.fst .v3) .v0 = eD at h ⊢
  simp only [Expr.cost, Expr.v0, Expr.v2, Expr.v3] at h ⊢; omega

private theorem issue1275ScanStepE_size (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)} :
    (issue1275ScanStepE emb (Γ := Γ)).size ≤ 78 := by
  simp only [issue1275ScanStepE, bytes2EqLitE, boolOrE, emb.size_pureE, AtomicPureOp.opSize,
    List.length_cons, List.length_nil, Expr.size, Expr.v0, Expr.v1, hb1, hb2]
  decide

private theorem swapPairsStep64E_size (emb : KemTrackOpEmbed ℓ Pt C K O) {Γ : List (Ty ASig)} :
    (swapPairsStep64E emb (Γ := Γ)).size ≤ 33 := by
  simp only [swapPairsStep64E, emb.size_pureE, AtomicPureOp.opSize, Expr.size, Expr.v0, hb1, hb2]
  decide

private theorem swapChunk64StepC_size (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)} :
    (swapChunk64StepC emb (I := I) (Γ := Γ)).size ≤ 82 := by
  have hs64 := swapPairsStep64E_size emb (Γ := .prod (B 2048) (B 2048) :: Γ)
  dsimp only [swapChunk64StepC]
  generalize swapPairsStep64E emb (Γ := .prod (B 2048) (B 2048) :: Γ) = e64 at hs64 ⊢
  simp only [Comp.size, emb.size_pureE, AtomicPureOp.opSize, List.length_nil,
    Expr.size, Expr.v0, Expr.v1, hb32, hb63, hb64]
  omega

theorem issue1275FixEsC_size_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (esE : Expr O Γ (B 2080)) :
    (issue1275FixEsC emb (I := I) esE).size ≤ esE.size + 240 := by
  have hscan := issue1275ScanStepE_size emb (Γ := B 2080 :: Γ)
  have hchunk := swapChunk64StepC_size emb (I := I) (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ)
  dsimp only [issue1275FixEsC]
  generalize issue1275ScanStepE emb (Γ := B 2080 :: Γ) = eScan at hscan ⊢
  generalize swapChunk64StepC emb (I := I)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ) = cChunk at hchunk ⊢
  simp only [Comp.size, emb.size_pureE, AtomicPureOp.opSize, List.length_nil,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, hb32, hb256, hb1536, hb2048] at hscan hchunk ⊢
  omega

theorem honestExchangeFailsC_size_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr O Γ BV512) (randE : Expr O Γ BV256) :
    (honestExchangeFailsC emb (I := I) seedE randE).size ≤ seedE.size + randE.size + 310 := by
  let Γ1 := Ty.prod (AtomicSpqrKemOp.kem768FromSeed.cod ℓ Pt) BV256 :: Γ
  let Γ2 := Ty.prod (B 960) (.prod (B 2080) BV256) :: Γ1
  have hfix := issue1275FixEsC_size_le emb (I := I) (Γ := Γ2) (.fst (.snd .v0))
  dsimp only [honestExchangeFailsC]
  generalize issue1275FixEsC emb (I := I) (Γ := Γ2) (.fst (.snd .v0)) = cFix at hfix ⊢
  simp only [Comp.size, Expr.size, emb.size_spqrE, emb.size_pureE, AtomicPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hfix ⊢
  omega

theorem initKemFailTrackE_size_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (pqrKeyE : Expr O Γ BV256) :
    (initKemFailTrackE emb pqrKeyE).size ≤ pqrKeyE.size + 75 := by
  simp only [initKemFailTrackE, initV1BraidStE, emb.size_spqrE, emb.size_pureE, AtomicPureOp.opSize,
    List.length_nil, Expr.size, Expr.v0, hb0]
  omega

theorem initKemFailSessionTrackE_size_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (pqrKeyE : Expr O Γ BV256) :
    (initKemFailSessionTrackE emb pqrKeyE).size ≤ pqrKeyE.size + 77 := by
  have h := initKemFailTrackE_size_le emb pqrKeyE
  simp only [initKemFailSessionTrackE, Expr.size]; omega

private theorem encRandBvE_size (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (rqE : Expr O Γ BV512) :
    (encRandBvE emb rqE).size = rqE.size + 3 := by
  simp only [encRandBvE, emb.size_pureE, AtomicPureOp.opSize]

theorem nextKemCandC_size_le (emb : KemTrackOpEmbed ℓ Pt C K O)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool) (rqE : Expr O Γ BV512) :
    (nextKemCandC emb (I := I) trE qBE rqE).size ≤
      trE.size + qBE.size + rqE.size + 420 := by
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  let Γ1 := Ty.sum BV512 (.prod BV512 BV256) :: Γ0
  let Γ2 := BV512 :: Γ1
  have hhef := honestExchangeFailsC_size_le emb (I := I) (Γ := Γ2) .v0
    (encRandBvE emb (.snd (.snd .v2)))
  dsimp only [nextKemCandC]
  generalize honestExchangeFailsC emb (I := I) (Γ := Γ2) .v0
    (encRandBvE emb (.snd (.snd .v2))) = cHef at hhef ⊢
  simp only [Comp.size, Expr.size, encRandBvE_size, boolEqE, ekSideIsAE, isHeaderReceivedV1E,
    pGet, trE_cand, trE_st, trE_e, trE_c, emb.size_pureE, AtomicPureOp.opSize,
    List.length_cons, List.length_nil, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1, hb2] at hhef ⊢
  omega

theorem stepKemFailSendPairC_size_le (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool) (rqE : Expr O Γ BV512) :
    (stepKemFailSendPairC emb q (I := I) trE qBE rqE).size ≤
      trE.size + qBE.size + rqE.size + 850 + bits (q + 1) := by
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool BV512) :: Γ
  have hcand := nextKemCandC_size_le emb (I := I) (Γ := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0))
  dsimp only [stepKemFailSendPairC]
  generalize nextKemCandC emb (I := I) (Γ := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.snd (.snd .v0)) = cCand at hcand ⊢
  simp only [Comp.size, stepPostKemSendE, nextKemCoinsE, isKeysUnsampledV1E, isHeaderReceivedV1E,
    encRandBvE_size, trMk, pGet, pSet, trE_e, trE_c, trE_st, trE_sentB, trE_sendCtr,
    emb.size_spqrE, emb.size_pureE, AtomicPureOp.opSize, List.length_cons, List.length_nil,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, hb1] at hcand ⊢
  omega

theorem stepKemFailSendC_size_le (emb : KemTrackOpEmbed ℓ Pt C K O) (q : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool) (rqE : Expr O Γ BV512) :
    (stepKemFailSendC emb q (I := I) trE qBE rqE).size ≤
      trE.size + qBE.size + rqE.size + 880 + bits (q + 1) := by
  have h := stepKemFailSendPairC_size_le emb q (I := I) trE qBE rqE
  dsimp only [stepKemFailSendC]
  generalize stepKemFailSendPairC emb q (I := I) trE qBE rqE = cPair at h ⊢
  simp only [Comp.size, trCandIsSomeE, trE_cand, Expr.size, Expr.v0] at h ⊢; omega

@[simp] theorem prependHonestWireE_size {Γ : List (Ty ASig)}
    (trOutE : Expr O Γ (kemTrackT ℓ Pt)) (hwE : Expr O Γ (.list (honestWireEntryT ℓ Pt)))
    (wE : Expr O Γ (B 32)) (pBE : Expr O Γ .bool) :
    (prependHonestWireE trOutE hwE wE pBE).size =
      trOutE.size + hwE.size + wE.size + pBE.size + 3 := by
  simp only [prependHonestWireE, Expr.size]; omega

private theorem b64Take48ToB32E_size (emb : KemTrackOpEmbed ℓ Pt C K O)
    {Γ : List (Ty ASig)} (suf : Expr O Γ (B 64)) :
    (b64Take48ToB32E emb suf).size ≤ suf.size + 24 := by
  simp only [b64Take48ToB32E, emb.size_pureE, AtomicPureOp.opSize, Expr.size, hb3]; omega

theorem listNthOptB_size_le (L : ℕ) {t : Ty ASig} {Γ : List (Ty ASig)}
    (xsE : Expr O Γ (.list t)) (jE : Expr O Γ .nat) :
    (listNthOptB L xsE jE).size ≤ xsE.size + jE.size + 41 + 2 * bits L := by
  simp only [listNthOptB, Expr.size, Expr.v0, Expr.v1, Expr.v2, hb0, hb1]; omega

theorem findRevHonestWireIdxE_size_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (hwE : Expr O Γ (.list (honestWireEntryT ℓ Pt)))
    (qBE : Expr O Γ .bool) (wE : Expr O Γ (B 32)) :
    (findRevHonestWireIdxE emb L hwE qBE wE).size ≤
      hwE.size + qBE.size + wE.size + 45 + bits L := by
  simp only [findRevHonestWireIdxE, boolEqE, emb.size_pureE, AtomicPureOp.opSize,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, hb0, hb1]; omega

theorem findRevHonestIdxE_size_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)}
    (honestE : Expr O Γ (.list (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
    (qBE : Expr O Γ .bool) (wE : Expr O Γ (B 32)) :
    (findRevHonestIdxE emb L honestE qBE wE).size ≤
      honestE.size + qBE.size + wE.size + 55 + bits L := by
  simp only [findRevHonestIdxE, emb.size_pureE, AtomicPureOp.opSize,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, hb0, hb1, hb2]; omega

theorem stepKemFailDeliverE_size_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jE : Expr O Γ .nat) :
    (stepKemFailDeliverE emb L trE qBE jE).size ≤
      trE.size + qBE.size + jE.size + 310 + 2 * bits L := by
  let Γ0 := Ty.prod (kemTrackT ℓ Pt) (.prod .bool .nat) :: Γ
  let Γ1 := kemSentEntryT ℓ Pt :: Γ0
  let Γ2 := Ty.prod (.opt (.prod U64 BV256)) (B 32) :: Γ1
  have hnth := listNthOptB_size_le (O := O) L (t := kemSentEntryT ℓ Pt) (Γ := Γ0)
    (trE_sentB (.fst .v0)) (.snd (.snd .v0))
  have hb1 := b64Take48ToB32E_size emb (Γ := Γ1) (.snd (.fst .v0))
  have hb2 := b64Take48ToB32E_size emb (Γ := Γ2) (.snd (.fst .v1))
  dsimp only [stepKemFailDeliverE]
  generalize listNthOptB (O := O) L (trE_sentB (.fst .v0)) (.snd (.snd .v0)) = eNth at hnth ⊢
  generalize b64Take48ToB32E emb (Γ := Γ1) (.snd (.fst .v0)) = eb1 at hb1 ⊢
  generalize b64Take48ToB32E emb (Γ := Γ2) (.snd (.fst .v1)) = eb2 at hb2 ⊢
  simp only [pGet, pSet, trE_e, trE_c, trE_st, trE_sentB,
    emb.size_spqrE, emb.size_pureE, AtomicPureOp.opSize, List.length_cons, List.length_nil,
    Expr.size, Expr.v0, Expr.v1, Expr.v2] at hnth hb1 hb2 ⊢
  omega

theorem stepKemFailDeliverC_size_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)}
    (trE : Expr O Γ (kemTrackT ℓ Pt)) (qBE : Expr O Γ .bool) (jE : Expr O Γ .nat) :
    (stepKemFailDeliverC emb L (I := I) trE qBE jE).size ≤
      trE.size + qBE.size + jE.size + 315 + 2 * bits L := by
  have h := stepKemFailDeliverE_size_le emb L trE qBE jE
  simp only [stepKemFailDeliverC, Comp.size]; omega

theorem stepKemSessionDeliverOptE_size_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (stE : Expr O Γ (kemSessionTrackT ℓ Pt)) (qBE : Expr O Γ .bool)
    (jOptE : Expr O Γ (.opt .nat)) :
    (stepKemSessionDeliverOptE emb L stE qBE jOptE).size ≤
      stE.size + qBE.size + jOptE.size + 335 + 2 * bits L := by
  let Γ1 := Ty.nat :: Ty.prod (kemSessionTrackT ℓ Pt) (.prod .bool (.opt .nat)) :: Γ
  have h := stepKemFailDeliverE_size_le emb L (Γ := Γ1) (.fst (.fst .v1)) (.fst (.snd .v1)) .v0
  dsimp only [stepKemSessionDeliverOptE]
  generalize stepKemFailDeliverE emb L (Γ := Γ1) (.fst (.fst .v1)) (.fst (.snd .v1)) .v0 = eD at h ⊢
  simp only [Expr.size, Expr.v0, Expr.v1] at h ⊢; omega

theorem kemOnDeliverPostE_size_le (emb : KemTrackOpEmbed ℓ Pt C K O) (L : ℕ)
    {Γ : List (Ty ASig)} (qBE : Expr O Γ .bool) (jOptE : Expr O Γ (.opt .nat))
    (rrOptE : Expr O Γ (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))))
    (trE : Expr O Γ (kemTrackT ℓ Pt)) :
    (kemOnDeliverPostE emb L qBE jOptE rrOptE trE).size ≤
      qBE.size + jOptE.size + rrOptE.size + trE.size + 356 + 2 * bits L := by
  let t0 := Ty.prod .bool (.prod (.opt .nat) (.prod (.opt (recvResultT (ℓ := ℓ) (Pt := Pt))) (kemTrackT ℓ Pt)))
  let Γ3 := Ty.nat :: Ty.prod .nat (.prod .nat (.opt (_root_.ReductionDsl.PlainT (ℓ := ℓ) (Pt := Pt)))) ::
    recvResultT (ℓ := ℓ) (Pt := Pt) :: t0 :: Γ
  have h := stepKemFailDeliverE_size_le emb L (Γ := Γ3) (.snd (.snd (.snd .v3))) (.fst .v3) .v0
  dsimp only [kemOnDeliverPostE]
  generalize stepKemFailDeliverE emb L (Γ := Γ3) (.snd (.snd (.snd .v3))) (.fst .v3) .v0 = eD at h ⊢
  simp only [Expr.size, Expr.v0, Expr.v2, Expr.v3] at h ⊢; omega

end CostAndSizeBounds

end Computational.Proofs.Game.PromotedCostedReds.KemFailTrackDslBase
