/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import LibsignalBinary.Specifications.LibsignalSpqrV1.KemFailFind
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Incremental `KemFailBad` Send-Coin Log Guard

Defines `kemFailBadSendCheckC`, an interface-polymorphic `ReductionDsl.Comp` gadget over
`atomicSessionOps` checking whether appending a 64-byte send tape to a `KemFailBad`-free coin log
triggers `K.KemFailBad`, and proves its query, cost, size, and evaluation lemmas.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailBadHalted

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp
  OpsSizeHonest SampSizeHonest supportWhen iterM anyML bits
  atomicSig atomicPureOps atomicSpqrKemOps atomicSessionOps
  AtomicPureOp AtomicSpqrKemOp B BV256 BV512)
open CryptoGames.CKA (DHFun)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes coinBytes_length
  issue1275NeedsFlip swapAdjacentPairs flipEndiannessOfEncapsulationStateBytes
  potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes)
open CryptoVerification.E2E (Bytes)

section Definitions

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[expose] def sessPureE {Γ : List (Ty ASig)} (o : AtomicPureOp) (e : Expr AOps Γ (o.dom ℓ Pt)) :
    Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inl (Sum.inl (Sum.inl (Sum.inl o)))) e
@[expose] def sessSpqrE {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp) (e : Expr AOps Γ (o.dom ℓ Pt)) :
    Expr AOps Γ (o.cod ℓ Pt) :=
  ReductionDsl.Expr.op (O := AOps) (Sum.inr o) e
@[expose] def boolOrE {Γ : List (Ty ASig)} (a b : Expr AOps Γ .bool) : Expr AOps Γ .bool :=
  .ite a (.bool true) b
@[expose] def bytes2EqLitE {Γ : List (Ty ASig)} (x : Expr AOps Γ (B 2)) (b0 b1 : BitVec 8) :
    Expr AOps Γ .bool :=
  sessPureE (.bytesEq 2 2) (.pair x (sessPureE (.bytesLit 2 [b0, b1]) .unit))

@[expose] def issue1275ScanStepPolyE {Γ : List (Ty ASig)} :
    Expr AOps (.prod (B 512) (.opt .bool) :: Γ) (.prod (B 512) (.opt .bool)) :=
  let rem : Expr AOps (.prod (B 512) (.opt .bool) :: Γ) (B 512) := .fst .v0
  .caseOpt (.snd .v0)
    (.ite (.lt (.nat 1) (sessPureE (.bytesLen 512) rem))
      (.letE (sessPureE (.bytesTakeK 512 2) rem)
        (let p2 : Expr AOps (B 2 :: .prod (B 512) (.opt .bool) :: Γ) (B 2) := .v0
         let rem1 : Expr AOps (B 2 :: .prod (B 512) (.opt .bool) :: Γ) (B 512) := .fst .v1
         let b2eq := bytes2EqLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
           (encT := encT) (decT := decT) (lam := lam) p2
         let isCont := boolOrE (b2eq 0x00#8 0x00#8) (b2eq 0xff#8 0xff#8)
         let isFlip := boolOrE (b2eq 0x00#8 0x01#8)
           (boolOrE (b2eq 0x00#8 0x02#8) (b2eq 0xff#8 0xfe#8))
         .ite isCont
           (.pair (sessPureE (.bytesDrop 512) (.pair (.nat 2) rem1)) .none)
           (.pair rem1 (.some isFlip))))
      (.pair rem (.some (.bool false))))
    .v1

@[expose] def swapPairsStep64E {Γ : List (Ty ASig)} :
    Expr AOps (.prod (B 64) (B 64) :: Γ) (.prod (B 64) (B 64)) :=
  let rem : Expr AOps (.prod (B 64) (B 64) :: Γ) (B 64) := .fst .v0
  let acc : Expr AOps (.prod (B 64) (B 64) :: Γ) (B 64) := .snd .v0
  .ite (.lt (.nat 1) (sessPureE (.bytesLen 64) rem))
    (let b0 := sessPureE (.bytesTakeK 64 1) rem
     let b1 := sessPureE (.bytesTakeK 64 1) (sessPureE (.bytesDrop 64) (.pair (.nat 1) rem))
     let swapped2 : Expr AOps _ (B 2) := sessPureE (.bytesCat 1 1) (.pair b1 b0)
     let rem' := sessPureE (.bytesDrop 64) (.pair (.nat 2) rem)
     let acc' := sessPureE (.bytesTakeK 66 64) (sessPureE (.bytesCat 64 2) (.pair acc swapped2))
     .pair rem' acc')
    .v0

@[expose] def swapChunk64StepC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T} {Γ : List (Ty ASig)} :
    Comp AOps I (.prod (B 2048) (B 2048) :: Γ) (.prod (B 2048) (B 2048)) :=
  .ite (.lt (.nat 63) (sessPureE (.bytesLen 2048) (.fst .v0)))
    (.bind
      (.iter 32
        (.pair (sessPureE (.bytesTakeK 2048 64) (.fst .v0)) (sessPureE (.bytesLit 64 []) .unit))
        (.ret (swapPairsStep64E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam))))
      (.ret
        (.pair
          (sessPureE (.bytesDrop 2048) (.pair (.nat 64) (.fst .v1)))
          (sessPureE (.bytesTakeK 2112 2048)
            (sessPureE (.bytesCat 2048 64) (.pair (.snd .v1) (.snd .v0)))))))
    (.ret .v0)

/-- Compute `(potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es).getD es` for `es`
of length `2080`. -/
@[expose] def issue1275FixEsPolyC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) :
    Comp AOps I Γ (B 2080) :=
  .bind (.ret esE)
    (let errSlice : Expr AOps (B 2080 :: Γ) (B 512) :=
       sessPureE (.bytesTakeK 2080 512) (sessPureE (.bytesDrop 2080) (.pair (.nat 1536) .v0))
     .bind
       (.iter 256 (.pair errSlice .none)
         (.ret (issue1275ScanStepPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
           (encT := encT) (decT := decT) (lam := lam))))
       (let needsFlip : Expr AOps (.prod (B 512) (.opt .bool) :: B 2080 :: Γ) .bool :=
          .caseOpt (.snd .v0) (.bool false) .v0
        .ite needsFlip
          (let initSwap : Expr AOps _ (.prod (B 2048) (B 2048)) :=
             .pair (sessPureE (.bytesTakeK 2080 2048) .v1) (sessPureE (.bytesLit 2048 []) .unit)
           .bind
             (.iter 32 initSwap
               (swapChunk64StepC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
                 (encT := encT) (decT := decT) (lam := lam)))
             (let tail32 := sessPureE (.bytesTakeK 2080 32)
                (sessPureE (.bytesDrop 2080) (.pair (.nat 2048) .v2))
              .ret (sessPureE (.bytesCat 2048 32) (.pair (.snd .v0) tail32))))
          (.ret .v1)))

@[expose] def encRandBvPolyE {Γ : List (Ty ASig)} (rqE : Expr AOps Γ BV512) : Expr AOps Γ BV256 :=
  sessPureE .bytesToBv256 (sessPureE (.bytesTakeK 64 32) (sessPureE .bv512ToBytes64 rqE))

@[expose] def honestExchangeFailsPolyC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) :
    Comp AOps I Γ .bool :=
  .bind (.ret (.pair (sessSpqrE .kem768FromSeed seedE) randE))
    (let hdr1 := Expr.fst (.fst .v0)
     let rand1 := Expr.snd .v0
     .caseOpt (sessSpqrE .kem768Encaps1 (.pair hdr1 rand1))
       (.ret (.bool true))
       (let hdr2 := Expr.fst (.fst .v1)
        let ek2 := Expr.fst (.snd (.fst .v1))
        let es2 := Expr.fst (.snd .v0)
        .ite (.not (sessSpqrE .kem768ValidPk (.pair hdr2 ek2)))
          (.ret (.bool true))
          (.bind
            (issue1275FixEsPolyC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) es2)
            (let ek3 := Expr.fst (.snd (.fst .v2))
             .ret
               (Expr.caseOpt (sessSpqrE .kem768Encaps2 (.pair .v0 ek3))
                 (.bool true)
                 (Expr.caseOpt
                   (sessSpqrE .kem768Decaps (.pair (.snd (.snd (.fst .v3))) (.pair (.fst .v2) .v0)))
                   (.bool true)
                   (.not (sessPureE .bv256Eq (.pair .v0 (.snd (.snd .v3)))))))))))

@[expose] def tapePairFailsPolyC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (r1E r2E : Expr AOps Γ BV512) :
    Comp AOps I Γ .bool :=
  honestExchangeFailsPolyC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) r1E
    (encRandBvPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) r2E)

@[expose] def logAppendSingletonE {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) :
    Expr AOps Γ (.list BV512) :=
  .appendL (q + 1) logE (.cons coinsE .nil)

/-- Incremental `KemFailBad` send-coin guard checking `log ++ [coins]` via `Comp.anyM (q + 1)`. -/
@[expose] def kemFailBadSendCheckC {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) :
    Comp AOps I Γ .bool :=
  .bind (.ret (.pair logE coinsE))
    (let logExt : Expr AOps (.prod (.list BV512) BV512 :: Γ) (.list BV512) :=
       logAppendSingletonE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
         (encT := encT) (decT := decT) (lam := lam) q (.fst .v0) (.snd .v0)
     .anyM (q + 1) logExt
       (.bind
         (tapePairFailsPolyC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
           (encT := encT) (decT := decT) (lam := lam) .v0 (.snd .v1))
         (.ite .v0
           (.ret (.bool true))
           (tapePairFailsPolyC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
             (encT := encT) (decT := decT) (lam := lam) (.snd .v2) .v1))))

end Definitions

/-! ## Pure incremental characterization -/

section PureKemFailBad

theorem tapePairFails_coinBytes_eq (K : MlKem) (r₁ r₂ : BitVec 512) :
    K.tapePairFails (coinBytes r₁) (coinBytes r₂) =
      K.honestExchangeFails ⟨coinBytes r₁, coinBytes_length r₁⟩
        ⟨(coinBytes r₂).take 32, by simp [coinBytes_length r₂]⟩ := by
  unfold MlKem.tapePairFails
  simp [coinBytes_length r₁, coinBytes_length r₂]

theorem kemFailBad_append_singleton_eq_any (K : MlKem)
    (log : List (BitVec 512)) (coins : BitVec 512)
    (hgood : K.KemFailBad (log.map coinBytes) = false) :
    K.KemFailBad ((log ++ [coins]).map coinBytes) =
      (log ++ [coins]).any fun r' =>
        K.tapePairFails (coinBytes r') (coinBytes coins) ||
          K.tapePairFails (coinBytes coins) (coinBytes r') := by
  rw [Bool.eq_iff_iff]
  have hno : ∀ r₁ ∈ log, ∀ r₂ ∈ log,
      K.tapePairFails (coinBytes r₁) (coinBytes r₂) = false := by
    simpa [MlKem.KemFailBad, List.any_eq_false] using hgood
  simp only [MlKem.KemFailBad, List.map_append, List.map_cons, List.map_nil,
    List.any_eq_true, List.mem_append, List.mem_singleton, Bool.or_eq_true]
  constructor
  · rintro ⟨t₁, ht₁, t₂, ht₂, hfail⟩
    have hm1 : (∃ r₁ ∈ log, coinBytes r₁ = t₁) ∨ t₁ = coinBytes coins := by
      simpa [List.mem_map] using ht₁
    have hm2 : (∃ r₂ ∈ log, coinBytes r₂ = t₂) ∨ t₂ = coinBytes coins := by
      simpa [List.mem_map] using ht₂
    rcases hm1 with ⟨r₁, hr₁, rfl⟩ | rfl <;> rcases hm2 with ⟨r₂, hr₂, rfl⟩ | rfl
    · rw [hno r₁ hr₁ r₂ hr₂] at hfail; cases hfail
    · exact ⟨r₁, Or.inl hr₁, Or.inl hfail⟩
    · exact ⟨r₂, Or.inl hr₂, Or.inr hfail⟩
    · exact ⟨coins, Or.inr rfl, Or.inl hfail⟩
  · rintro ⟨r', hr', hfail | hfail⟩
    · refine ⟨coinBytes r', ?_, coinBytes coins, Or.inr rfl, hfail⟩
      rcases hr' with hr' | rfl
      · exact Or.inl (List.mem_map_of_mem hr')
      · exact Or.inr rfl
    · refine ⟨coinBytes coins, Or.inr rfl, coinBytes r', ?_, hfail⟩
      rcases hr' with hr' | rfl
      · exact Or.inl (List.mem_map_of_mem hr')
      · exact Or.inr rfl

end PureKemFailBad

/-! ## Query, cost, and size bounds -/

section CostAndSizeBounds

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[simp] theorem eval_sessPureE {Γ : List (Ty ASig)} (o : AtomicPureOp) (e : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sessPureE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) o e).eval ρ =
      AtomicPureOp.eval ℓ Pt o (e.eval ρ) := rfl
@[simp] theorem cost_sessPureE {Γ : List (Ty ASig)} (o : AtomicPureOp) (e : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessPureE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) o e).cost =
      e.cost + AtomicPureOp.cost ℓ o := rfl
@[simp] theorem size_sessPureE {Γ : List (Ty ASig)} (o : AtomicPureOp) (e : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessPureE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) o e).size =
      e.size + o.opSize + 1 := rfl
@[simp] theorem eval_sessSpqrE {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp) (e : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (sessSpqrE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) o e).eval ρ =
      AtomicSpqrKemOp.eval ℓ Pt C K o (e.eval ρ) := rfl
@[simp] theorem cost_sessSpqrE {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp) (e : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessSpqrE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) o e).cost =
      e.cost + AtomicSpqrKemOp.cost o := rfl
@[simp] theorem size_sessSpqrE {Γ : List (Ty ASig)} (o : AtomicSpqrKemOp) (e : Expr AOps Γ (o.dom ℓ Pt)) :
    (sessSpqrE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) o e).size =
      e.size + 1 := rfl

@[simp] theorem swapChunk64StepC_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (swapChunk64StepC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).queries w ws = 0 := by
  simp [swapChunk64StepC, Comp.queries]
@[simp] theorem issue1275FixEsPolyC_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (issue1275FixEsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) esE).queries w ws = 0 := by
  simp [issue1275FixEsPolyC, Comp.queries]
@[simp] theorem honestExchangeFailsPolyC_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (honestExchangeFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) seedE randE).queries w ws = 0 := by
  simp [honestExchangeFailsPolyC, Comp.queries]
@[simp] theorem tapePairFailsPolyC_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (r1E r2E : Expr AOps Γ BV512) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (tapePairFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) r1E r2E).queries w ws = 0 := by
  simp [tapePairFailsPolyC]
@[simp] theorem kemFailBadSendCheckC_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (q : ℕ) (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (kemFailBadSendCheckC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE).queries w ws = 0 := by
  simp [kemFailBadSendCheckC, Comp.queries]
@[simp] theorem kemFailBadSendCheckC_nq_zero {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (q : ℕ) (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) :
    (kemFailBadSendCheckC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE).nq = 0 := by
  simp [Comp.nq]

private theorem hb1 : bits 1 = 1 := by decide
private theorem hb2 : bits 2 = 2 := by decide
private theorem hb32 : bits 32 = 6 := by decide
private theorem hb63 : bits 63 = 6 := by decide
private theorem hb64 : bits 64 = 7 := by decide
private theorem hb256 : bits 256 = 9 := by decide
private theorem hb512 : bits 512 = 10 := by decide
private theorem hb1536 : bits 1536 = 11 := by decide
private theorem hb2048 : bits 2048 = 12 := by decide

private theorem issue1275ScanStepPolyE_cost {Γ : List (Ty ASig)} :
    (issue1275ScanStepPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost = 1080 := by
  have hp2 : ((2 : ℕ+) : ℕ) = 2 := rfl
  have hp512 : ((512 : ℕ+) : ℕ) = 512 := rfl
  simp only [issue1275ScanStepPolyE, bytes2EqLitE, boolOrE, cost_sessPureE,
    Expr.cost, AtomicPureOp.cost, Expr.v0, Expr.v1, List.length_cons, List.length_nil,
    hb1, hb2, hb512, hp2, hp512]
  decide

private theorem swapPairsStep64E_cost {Γ : List (Ty ASig)} :
    (swapPairsStep64E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost = 487 := by
  have hp1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  have hp2 : ((2 : ℕ+) : ℕ) = 2 := rfl
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  have hp66 : ((66 : ℕ+) : ℕ) = 66 := rfl
  simp only [swapPairsStep64E, sessPureE, Expr.cost, Expr.v0, hb1, hb2]
  dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
    Ops.sum, Sum.elim, AtomicPureOp.cost]
  simp only [hb64, hp1, hp2, hp64, hp66]
  decide

private theorem swapChunk64StepC_cost {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} :
    (swapChunk64StepC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost ≤ 26200 := by
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  have hp2112 : ((2112 : ℕ+) : ℕ) = 2112 := rfl
  simp only [swapChunk64StepC, Comp.cost, sessPureE, Expr.cost,
    Expr.v0, Expr.v1, hb63, hb64, swapPairsStep64E_cost]
  dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
    Ops.sum, Sum.elim, AtomicPureOp.cost]
  simp only [List.length_nil, hb2048, hp64, hp2048, hp2112]
  omega

theorem issue1275FixEsPolyC_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) :
    (issue1275FixEsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) esE).cost ≤ esE.cost + 1140000 := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hp512 : ((512 : ℕ+) : ℕ) = 512 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  have hp2080 : ((2080 : ℕ+) : ℕ) = 2080 := rfl
  have hscan := issue1275ScanStepPolyE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ)
  have hchunk := swapChunk64StepC_cost (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ)
  dsimp only [issue1275FixEsPolyC]
  generalize issue1275ScanStepPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ) = eScan at hscan ⊢
  generalize swapChunk64StepC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ) = cChunk at hchunk ⊢
  simp only [Comp.cost, sessPureE, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2,
    hb1536, hb2048, hscan] at hchunk ⊢
  dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
    Ops.sum, Sum.elim, AtomicPureOp.cost] at hchunk ⊢
  simp only [List.length_nil, hp32, hp512, hp2048, hp2080] at hchunk ⊢
  omega

theorem honestExchangeFailsPolyC_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) :
    (honestExchangeFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) seedE randE).cost ≤
      seedE.cost + randE.cost + 1141000 := by
  let Γ1 := Ty.prod (AtomicSpqrKemOp.kem768FromSeed.cod ℓ Pt) BV256 :: Γ
  let Γ2 := Ty.prod (B 960) (.prod (B 2080) BV256) :: Γ1
  have hfix := issue1275FixEsPolyC_cost_le (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.fst (.snd .v0))
  dsimp only [honestExchangeFailsPolyC]
  generalize issue1275FixEsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.fst (.snd .v0)) = cFix at hfix ⊢
  simp only [Comp.cost, Expr.cost, cost_sessSpqrE, cost_sessPureE,
    AtomicSpqrKemOp.cost, AtomicPureOp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hfix ⊢
  omega

@[simp] theorem encRandBvPolyE_cost {Γ : List (Ty ASig)} (rqE : Expr AOps Γ BV512) :
    (encRandBvPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) rqE).cost = rqE.cost + 192 := by
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  simp only [encRandBvPolyE, cost_sessPureE, AtomicPureOp.cost, hp32, hp64]; try omega

theorem tapePairFailsPolyC_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (r1E r2E : Expr AOps Γ BV512) :
    (tapePairFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) r1E r2E).cost ≤
      r1E.cost + r2E.cost + 1141200 := by
  have h := honestExchangeFailsPolyC_cost_le (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) r1E
    (encRandBvPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) r2E)
  simp only [encRandBvPolyE_cost] at h
  dsimp only [tapePairFailsPolyC]
  omega

@[simp] theorem logAppendSingletonE_cost {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) :
    (logAppendSingletonE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE).cost =
      logE.cost + coinsE.cost + q + 4 := by
  simp only [logAppendSingletonE, Expr.cost]
  omega

theorem kemFailBadSendCheckC_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) :
    (kemFailBadSendCheckC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE).cost ≤
      logE.cost + coinsE.cost + 2300000 * (q + 1) := by
  let Γ0 := Ty.prod (.list BV512) BV512 :: Γ
  let Γ1 := BV512 :: Γ0
  let Γ2 := Ty.bool :: Γ1
  have h1 := tapePairFailsPolyC_cost_le (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) .v0 (.snd .v1)
  have h2 := tapePairFailsPolyC_cost_le (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd .v2) .v1
  dsimp only [kemFailBadSendCheckC]
  generalize tapePairFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) .v0 (.snd .v1) = c1 at h1 ⊢
  generalize tapePairFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd .v2) .v1 = c2 at h2 ⊢
  simp only [Comp.cost, Expr.cost, logAppendSingletonE_cost, Expr.v0, Expr.v1, Expr.v2] at h1 h2 ⊢
  have hbody : c1.cost + (1 + max (1 + 1) c2.cost + 1) + 1 + 1 ≤ 2299980 := by omega
  have hmul : (q + 1) * (c1.cost + (1 + max (1 + 1) c2.cost + 1) + 1 + 1) ≤ (q + 1) * 2299980 :=
    Nat.mul_le_mul_left (q + 1) hbody
  omega

private theorem issue1275ScanStepPolyE_size {Γ : List (Ty ASig)} :
    (issue1275ScanStepPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).size ≤ 78 := by
  simp only [issue1275ScanStepPolyE, bytes2EqLitE, boolOrE, size_sessPureE, AtomicPureOp.opSize,
    List.length_cons, List.length_nil, Expr.size, Expr.v0, Expr.v1, hb1, hb2]
  decide

private theorem swapPairsStep64E_size {Γ : List (Ty ASig)} :
    (swapPairsStep64E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).size ≤ 33 := by
  simp only [swapPairsStep64E, sessPureE, Expr.size, Expr.v0, hb1, hb2]
  dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
    Ops.sum, Sum.elim, AtomicPureOp.opSize]
  decide

private theorem swapChunk64StepC_size {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} :
    (swapChunk64StepC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).size ≤ 82 := by
  have hs64 := swapPairsStep64E_size (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := .prod (B 2048) (B 2048) :: Γ)
  dsimp only [swapChunk64StepC]
  generalize swapPairsStep64E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := .prod (B 2048) (B 2048) :: Γ) = e64 at hs64 ⊢
  simp only [Comp.size, sessPureE, Expr.size, Expr.v0, Expr.v1, hb32, hb63, hb64]
  dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
    Ops.sum, Sum.elim, AtomicPureOp.opSize, List.length_nil] at hs64 ⊢
  omega

theorem issue1275FixEsPolyC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) :
    (issue1275FixEsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) esE).size ≤ esE.size + 235 := by
  have hscan := issue1275ScanStepPolyE_size (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ)
  have hchunk := swapChunk64StepC_size (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ)
  dsimp only [issue1275FixEsPolyC]
  generalize issue1275ScanStepPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := B 2080 :: Γ) = eScan at hscan ⊢
  generalize swapChunk64StepC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := .prod (B 512) (.opt .bool) :: B 2080 :: Γ) = cChunk at hchunk ⊢
  simp only [Comp.size, sessPureE, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, hb32, hb256, hb1536, hb2048]
  dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
    _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
    Ops.sum, Sum.elim, AtomicPureOp.opSize, List.length_nil] at hscan hchunk ⊢
  omega

theorem honestExchangeFailsPolyC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) :
    (honestExchangeFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) seedE randE).size ≤
      seedE.size + randE.size + 300 := by
  let Γ1 := Ty.prod (AtomicSpqrKemOp.kem768FromSeed.cod ℓ Pt) BV256 :: Γ
  let Γ2 := Ty.prod (B 960) (.prod (B 2080) BV256) :: Γ1
  have hfix := issue1275FixEsPolyC_size_le (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.fst (.snd .v0))
  dsimp only [honestExchangeFailsPolyC]
  generalize issue1275FixEsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.fst (.snd .v0)) = cFix at hfix ⊢
  simp only [Comp.size, Expr.size, size_sessSpqrE, size_sessPureE, AtomicPureOp.opSize,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hfix ⊢
  omega

@[simp] theorem encRandBvPolyE_size {Γ : List (Ty ASig)} (rqE : Expr AOps Γ BV512) :
    (encRandBvPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) rqE).size = rqE.size + 3 := by
  simp only [encRandBvPolyE, size_sessPureE, AtomicPureOp.opSize]; try omega

theorem tapePairFailsPolyC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (r1E r2E : Expr AOps Γ BV512) :
    (tapePairFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) r1E r2E).size ≤
      r1E.size + r2E.size + 303 := by
  have h := honestExchangeFailsPolyC_size_le (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) r1E
    (encRandBvPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) r2E)
  simp only [encRandBvPolyE_size] at h
  dsimp only [tapePairFailsPolyC]
  omega

@[simp] theorem logAppendSingletonE_size {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) :
    (logAppendSingletonE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE).size =
      logE.size + coinsE.size + bits (q + 1) + 3 := by
  simp only [logAppendSingletonE, Expr.size]
  omega

theorem kemFailBadSendCheckC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) :
    (kemFailBadSendCheckC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE).size ≤
      logE.size + coinsE.size + 640 + 2 * bits (q + 1) := by
  let Γ0 := Ty.prod (.list BV512) BV512 :: Γ
  let Γ1 := BV512 :: Γ0
  let Γ2 := Ty.bool :: Γ1
  have h1 := tapePairFailsPolyC_size_le (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) .v0 (.snd .v1)
  have h2 := tapePairFailsPolyC_size_le (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd .v2) .v1
  dsimp only [kemFailBadSendCheckC]
  generalize tapePairFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) .v0 (.snd .v1) = c1 at h1 ⊢
  generalize tapePairFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ2) (.snd .v2) .v1 = c2 at h2 ⊢
  simp only [Comp.size, Expr.size, logAppendSingletonE_size, Expr.v0, Expr.v1, Expr.v2] at h1 h2 ⊢
  omega

end CostAndSizeBounds

/-! ## Evaluation semantics -/

section EvalProofs

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem iterM_pure_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (f : α → α) (n : ℕ) (a : α) :
    iterM (fun x => (pure (f x) : m α)) n a = pure (f^[n] a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [iterM, ih, Function.iterate_succ_apply]

private theorem anyML_pure_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (p : α → Bool) :
    ∀ xs : List α, anyML (fun x => (pure (p x) : m Bool)) xs = pure (xs.any p)
  | [] => rfl
  | x :: xs => by
    simp only [anyML, pure_bind, List.any_cons]
    cases p x
    · simpa using anyML_pure_eq p xs
    · rfl

private theorem anyML_congr_mem {m : Type → Type} [Monad m] {α : Type}
    {p q : α → m Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = q x) → anyML p xs = anyML q xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [anyML, h x List.mem_cons_self]
    congr 1; funext b
    split
    · rfl
    · exact anyML_congr_mem (fun y hy => h y (List.mem_cons_of_mem x hy))

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

private theorem issue1275ScanStepPolyE_eval {Γ : List (Ty ASig)} (ρ : Env Γ)
    (st : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 512) (Ty.opt .bool)).denote) :
    (issue1275ScanStepPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam)).eval (.cons st ρ) = issue1275ScanStepFn st := by
  have hOr (a b : Bool) : (if a = true then true else b) = (a || b) := by cases a <;> rfl
  rcases st with ⟨rem, _ | b⟩
  · by_cases hlen : 1 < rem.length
    · simp only [issue1275ScanStepPolyE, issue1275ScanStepFn, bytes2EqLitE, boolOrE, Expr.eval,
        Expr.v0, Expr.v1, Env.get, eval_sessPureE, AtomicPureOp.eval, hlen, decide_true,
        ↓reduceIte, hOr]; rfl
    · simp only [issue1275ScanStepPolyE, issue1275ScanStepFn, Expr.eval, Expr.v0, Env.get,
        eval_sessPureE, AtomicPureOp.eval, hlen, decide_false, Bool.false_eq_true, ↓reduceIte]
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
      clear hc
      rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
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

private theorem swapPairsStep64E_eval {Γ : List (Ty ASig)} (ρ : Env Γ)
    (st : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 64) (B (ℓ := ℓ) (Pt := Pt) 64)).denote) :
    (swapPairsStep64E (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam)).eval (.cons st ρ) = swapPairsStep64Fn st := by
  rcases st with ⟨rem, acc⟩
  by_cases hlen : 1 < rem.length
  · simp only [swapPairsStep64E, swapPairsStep64Fn, Expr.eval, Expr.v0, Env.get,
      eval_sessPureE, AtomicPureOp.eval, hlen, decide_true, ↓reduceIte]
    rfl
  · simp only [swapPairsStep64E, swapPairsStep64Fn, Expr.eval, Expr.v0, Env.get,
      eval_sessPureE, AtomicPureOp.eval, hlen, decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem swapAdjacentPairs_length :
    ∀ xs : Bytes, (swapAdjacentPairs xs).length = xs.length
  | [] | [_] => rfl
  | _ :: _ :: rest => by simp [swapAdjacentPairs, swapAdjacentPairs_length rest]

private theorem swapAdjacentPairs_append_two_mul (k : ℕ) :
    ∀ (u v : Bytes), u.length = 2 * k →
      swapAdjacentPairs (u ++ v) = swapAdjacentPairs u ++ swapAdjacentPairs v := by
  induction k with
  | zero =>
    rintro (_ | _) v hlen
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

private theorem swapChunk64StepC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (ρ : Env Γ)
    (st : (Ty.prod (B (ℓ := ℓ) (Pt := Pt) 2048) (B (ℓ := ℓ) (Pt := Pt) 2048)).denote) :
    (swapChunk64StepC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam)).eval (.cons st ρ) = pure (swapChunk64StepFn st) := by
  rcases st with ⟨rem, acc⟩
  have hp64 : ((64 : ℕ+) : ℕ) = 64 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  by_cases hlen : 63 < rem.length
  · have h64 : (rem.take 64).length = 2 * 32 := by simp; omega
    simp only [swapChunk64StepC, swapChunk64StepFn, Comp.eval, Expr.eval,
      Expr.v0, Expr.v1, Env.get, eval_sessPureE, AtomicPureOp.eval,
      hp64, hlen, decide_true, ↓reduceIte]
    have hInner :
        iterM (m := OracleComp T)
          (fun a => pure ((swapPairsStep64E (C := C) (K := K) (Dh := Dh) (encPt := encPt)
            (encT := encT) (decT := decT) (lam := lam)).eval
            (.cons a (Env.cons (t := .prod (B (ℓ := ℓ) (Pt := Pt) 2048)
              (B (ℓ := ℓ) (Pt := Pt) 2048)) (rem, acc) ρ))))
          32 (rem.take 64, []) =
        pure (swapPairsStep64Fn^[32] (rem.take 64, [])) := by
      simp only [swapPairsStep64E_eval]
      exact iterM_pure_eq swapPairsStep64Fn 32 _
    rw [hInner, pure_bind, swapPairsStep64Fn_iter 32 (rem.take 64) [] h64 (by simp)]
    simp only [sessPureE, Expr.eval, Env.get]
    dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
      _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
      Ops.sum, AtomicPureOp.eval]
    simp
  · simp only [swapChunk64StepC, swapChunk64StepFn, Comp.eval, Expr.eval,
      Expr.v0, Env.get, eval_sessPureE, AtomicPureOp.eval,
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

theorem issue1275FixEsPolyC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (esE : Expr AOps Γ (B 2080)) (ρ : Env Γ) (es : Bytes)
    (hes : esE.eval ρ = es) (hlen : es.length = 2080) :
    (issue1275FixEsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) esE).eval ρ =
      pure ((potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes es).getD es) := by
  let esD : (B (ℓ := ℓ) (Pt := Pt) 2080).denote := es
  have hes' : esE.eval ρ = esD := hes
  have hp512 : ((512 : ℕ+) : ℕ) = 512 := rfl
  have hp2048 : ((2048 : ℕ+) : ℕ) = 2048 := rfl
  simp only [issue1275FixEsPolyC, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Env.get, hes',
    eval_sessPureE, AtomicPureOp.eval, hp512, hp2048, pure_bind]
  have hIter1 :
      iterM (m := OracleComp T)
        (fun a => pure ((issue1275ScanStepPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)).eval (.cons a (.cons esD ρ))))
        256 ((esD.drop 1536).take 512, none) =
      pure (issue1275ScanStepFn^[256] ((esD.drop 1536).take 512, none)) := by
    simp only [issue1275ScanStepPolyE_eval]
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
            (fun a => (swapChunk64StepC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam)).eval
              (.cons a (Env.cons (t := .prod (B (ℓ := ℓ) (Pt := Pt) 512) (.opt .bool))
                (remS, some true) (.cons esD ρ))))
            32 (esD.take 2048, []) =
          pure (swapChunk64StepFn^[32] (esD.take 2048, [])) := by
        simp only [swapChunk64StepC_eval]
        exact iterM_pure_eq swapChunk64StepFn 32 _
      rw [hIter2, pure_bind]
      simp only [sessPureE, Expr.eval, Env.get, Expr.v2,
        swapChunk64StepFn_iter 32 (esD.take 2048) [] (by simp [esD, hlen]) (by simp)]
      dsimp only [atomicSessionOps, _root_.ReductionDsl.atomicFig8Ops,
        _root_.ReductionDsl.atomicFsOps, _root_.ReductionDsl.atomicPureOps,
        Ops.sum, AtomicPureOp.eval]
      simp [potentiallyFixStateIncorrectlyEncodedByLibcruxIssue1275Bytes,
        flipEndiannessOfEncapsulationStateBytes,
        show 2080 - 32 - 1536 = 512 by decide, show 2080 - 32 = 2048 by decide,
        show (es.drop 2048).take 32 = es.drop 2048 from List.take_of_length_le (by simp [hlen]),
        ← hScan, esD, hlen]

private theorem flipEndianness_length (es : Bytes) (hlen : es.length = 2080) :
    (flipEndiannessOfEncapsulationStateBytes es).length = 2080 := by
  simp [flipEndiannessOfEncapsulationStateBytes, swapAdjacentPairs_length, hlen]

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

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : ℕ)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (bytesToKey32 rest)
    | succ j =>
      have hcons : bytesToKey32 (b :: rest) =
          (bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

private theorem keyToBytes32_bytesToKey32_local (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j _ h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

private theorem bytesToKey32_beq_iff {a b : Bytes} (ha : a.length = 32) (hb : b.length = 32) :
    (!(bytesToKey32 a == bytesToKey32 b)) = decide (a ≠ b) := by
  suffices h : (bytesToKey32 a = bytesToKey32 b) ↔ a = b by
    by_cases hab : a = b <;> simp [hab, h]
  constructor
  · intro heq
    calc a = keyToBytes32 (bytesToKey32 a) := (keyToBytes32_bytesToKey32_local a ha).symm
      _ = keyToBytes32 (bytesToKey32 b) := by rw [heq]
      _ = b := keyToBytes32_bytesToKey32_local b hb
  · intro rfl; rfl

theorem honestExchangeFailsPolyC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (seedE : Expr AOps Γ BV512) (randE : Expr AOps Γ BV256) (ρ : Env Γ)
    (seed : BitVec 512) (rand : BitVec 256)
    (hs : seedE.eval ρ = seed) (hr : randE.eval ρ = rand) :
    (honestExchangeFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) seedE randE).eval ρ =
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
  simp only [honestExchangeFailsPolyC, Comp.eval, Expr.eval,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Env.get,
    hs, hr, eval_sessSpqrE, eval_sessPureE,
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
      refine Eq.trans (congrArg (· >>= _) (issue1275FixEsPolyC_eval _ _ es.toList rfl es.2)) ?_
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

theorem encRandBvPolyE_vec_eq {Γ : List (Ty ASig)}
    (rqE : Expr AOps Γ BV512) (ρ : Env Γ) (rq : BitVec 512) (hrq : rqE.eval ρ = rq) :
    keyToBytesVec32
      ((encRandBvPolyE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) rqE).eval ρ) =
      ⟨(coinBytes rq).take 32, by simp [coinBytes_length rq]⟩ := by
  have hlen : ((coinBytes rq).take 32).length = 32 := by simp [coinBytes_length rq]
  apply Subtype.ext
  simp only [encRandBvPolyE, hrq, eval_sessPureE, AtomicPureOp.eval, keyToBytesVec32]
  exact keyToBytes32_bytesToKey32_local _ hlen

theorem tapePairFailsPolyC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (r1E r2E : Expr AOps Γ BV512) (ρ : Env Γ)
    (r₁ r₂ : BitVec 512) (hr₁ : r1E.eval ρ = r₁) (hr₂ : r2E.eval ρ = r₂) :
    (tapePairFailsPolyC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) r1E r2E).eval ρ =
      pure (K.tapePairFails (coinBytes r₁) (coinBytes r₂)) := by
  unfold tapePairFailsPolyC
  rw [honestExchangeFailsPolyC_eval _ _ ρ r₁ _ hr₁ rfl,
    encRandBvPolyE_vec_eq r2E ρ r₂ hr₂, ← tapePairFails_coinBytes_eq]

theorem logAppendSingletonE_eval {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) (ρ : Env Γ)
    (log : List (BitVec 512)) (coins : BitVec 512)
    (hlog : logE.eval ρ = log) (hcoins : coinsE.eval ρ = coins)
    (hlen : log.length ≤ q) :
    (logAppendSingletonE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE).eval ρ =
      log ++ [coins] := by
  simp only [logAppendSingletonE, Expr.eval, hlog, hcoins]
  exact List.take_of_length_le (by simp; omega)

theorem kemFailBadSendCheckC_eval_any {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) (ρ : Env Γ)
    (log : List (BitVec 512)) (coins : BitVec 512)
    (hlog : logE.eval ρ = log) (hcoins : coinsE.eval ρ = coins)
    (hlen : log.length ≤ q) :
    (kemFailBadSendCheckC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE).eval ρ =
      pure ((log ++ [coins]).any fun r' =>
        K.tapePairFails (coinBytes r') (coinBytes coins) ||
          K.tapePairFails (coinBytes coins) (coinBytes r')) := by
  let p0 : (Ty.prod (.list (BV512 (ℓ := ℓ) (Pt := Pt))) (BV512 (ℓ := ℓ) (Pt := Pt))).denote :=
    (log, coins)
  have hp0 : (Expr.pair logE coinsE).eval ρ = p0 := by simp [Expr.eval, hlog, hcoins, p0]
  simp only [kemFailBadSendCheckC, Comp.eval, hp0, pure_bind]
  have hExt :
      (logAppendSingletonE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) q (.fst .v0) (.snd .v0)).eval (.cons p0 ρ) =
      log ++ [coins] :=
    logAppendSingletonE_eval q (.fst .v0) (.snd .v0) (.cons p0 ρ) log coins rfl rfl hlen
  rw [hExt, List.take_of_length_le (by simp; omega)]
  refine Eq.trans (anyML_congr_mem fun r' _ => ?_) (anyML_pure_eq _ (log ++ [coins]))
  have ht1 := tapePairFailsPolyC_eval (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) .v0 (.snd .v1)
    (Env.cons (t := BV512) r' (.cons p0 ρ)) r' coins rfl rfl
  rw [ht1, pure_bind]
  cases h1 : K.tapePairFails (coinBytes r') (coinBytes coins)
  · simp only [Expr.eval, Expr.v0, Env.get, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    exact tapePairFailsPolyC_eval (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (.snd .v2) .v1
      (Env.cons (t := .bool) false (Env.cons (t := BV512) r' (.cons p0 ρ))) coins r' rfl rfl
  · simp [Expr.eval, Expr.v0, Env.get]

/-- When `log.length ≤ q` and `log` is `KemFailBad`-free, `kemFailBadSendCheckC` evaluates to
`pure (K.KemFailBad ((log ++ [coins]).map coinBytes))`. -/
theorem kemFailBadSendCheckC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512) (ρ : Env Γ)
    (log : List (BitVec 512)) (coins : BitVec 512)
    (hlog : logE.eval ρ = log) (hcoins : coinsE.eval ρ = coins)
    (hlen : log.length ≤ q)
    (hgood : K.KemFailBad (log.map coinBytes) = false) :
    (kemFailBadSendCheckC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE).eval ρ =
      pure (K.KemFailBad ((log ++ [coins]).map coinBytes)) := by
  rw [kemFailBadSendCheckC_eval_any q logE coinsE ρ log coins hlog hcoins hlen,
    ← kemFailBad_append_singleton_eq_any K log coins hgood]

theorem kemFailBadSendCheckC_fits_eval_when {ι : Type} {T : OracleSpec ι} {I : Iface ASig T}
    (hO : OpsSizeHonest AOps) (hS : SampSizeHonest I.smp) (aB : ℕ)
    {Γ : List (Ty ASig)} (q : ℕ)
    (logE : Expr AOps Γ (.list BV512)) (coinsE : Expr AOps Γ BV512)
    (B : ℕ) (ρ : Env Γ) (hρ : Env.Fits B ρ)
    (y : Bool)
    (hy : y ∈ supportWhen (I.AnswerFits aB)
      ((kemFailBadSendCheckC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) q logE coinsE).eval ρ)) :
    (Ty.bool : Ty ASig).Fits
      (B + (kemFailBadSendCheckC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) q logE coinsE).cost) y := by
  simpa using Comp.fits_eval_when hO hS aB
    (kemFailBadSendCheckC (I := I) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) q logE coinsE) B ρ hρ y hy

end EvalProofs

end Computational.Proofs.Game.PromotedCostedReds.KemFailBadHalted

