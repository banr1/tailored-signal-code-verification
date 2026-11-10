/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF
import VCVio.EvalDist.Monad.Basic

/-!
# Loop Invariant, Cost, and Description-Size Infrastructure for `kemFailRed`

Defines the `(BitVec 512 × BitVec 256) ↔ SimKemSeed × SimKemEncRand` candidate codec, syntactic
`descBits` measures (`atomicRedDescBits`, `ratchetDescBudget`), and relational `simulateQ` loop
coupling lemmas. Assembles `kemFailRedProg` (`KemFailAtomicClampBundle`, `KemFailAtomicRealBundle`)
with unconditional `GRedBounded` and `descBits` bounds and call-site advantage bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost

open OracleSpec OracleComp
open scoped ENNReal
open MeasureTheory (lintegral_mono_ae lintegral_add_left lintegral_finsetSum lintegral_const)
open ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp GameCodec CostedReduction
  UniformSamplerTag AtomicSort AtomicUnifBase AtomicPureOp AtomicSymOp AtomicGroupOp
  AtomicSpqrKemOp AtomicPtEncOp AtomicPtDecOp AtomicCurveCheckOp
  bits bits_mono lt_two_pow_bits bytesToWordLE reductionSizeBudget
  isGameQuery handlerImpl bind_congr_of_mem_support'
  atomicSig atomicSamplers atomicSessionOps coinOnlyIface e2eSessionCodec
  BV256 BV512 GhostStT PlainT B)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.Ratchet.LibsignalSim (SimKemSeed SimKemEncRand SimKemFailTrack
  simDefaultKemCand simKemFailCand KemExtraRaw SimOp simOpsUnitCost fig8GsTy Fig8St Fig8C
  kemFailOracle kemFailOracleDedup redKemFailHiddenSaltClamp
  redKemFailHiddenSaltClamp_evalDistEq redKemFailHiddenSaltClamp_advantage_eq)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState initSimC)
open CryptoGames.Ratchet.LibsignalInst (lFig8 LibsignalMsgPublicPart)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState initKemFailTrack
  kemFailSimImpl redKemFailHiddenSalt)
open CryptoGames.SM (GameState initState MakesAtMostQueries)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey ShaCompress GhostState
  maxForwardJumps Params)
open CryptoVerification.LibsignalSpqrV1 (MlKem coinBytes coinBytes_length spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes idsOf paramsV1)
open CryptoVerification.E2E.HeadlineU (sample_prod_bindU)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicSessionOps_sizeHonest
  atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (sessPureOp
  eval_sessPureOp cost_sessPureOp)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (eval_eq_simulateQ_of_enc
  isQueryBoundP_of_makesAtMostQueries liftP_unif_eq_self
  bits_le_succ bits_succ_le ratchetCostBudgetTight ratchetCostBudgetTight_le_ratchetCostBudget
  session_cost_le_ratchetCostBudgetTight session_cost_le_ratchetCostBudget
  session_cost_cubic_le_ratchetCostBudgetTight session_cost_cubic_le_ratchetCostBudget
  dummyPairSessionRed dummyPairSessionRed_totalQueries dummyPairSessionRed_totalCost_le)

/-! ## Candidate codec -/

section CandidateCodec

private theorem extractLsb'_zero_wordLE_cons (w : ℕ) (hw : 8 ≤ w) (b : BitVec 8) (acc : BitVec w) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have hiw : i < w := by omega
  simp [hi, hiw]

private theorem extractLsb'_succ_wordLE_cons (w : ℕ) (b : BitVec 8) (acc : BitVec w) (j : ℕ)
    (hjw : 8 * (j + 2) ≤ w) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < w := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
  simp [h1, h2, h3, hb]

theorem extractLsb'_bytesToWordLE (w : ℕ) (bs : Bytes) (j : ℕ)
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

/-- Map raw `(seed, rand) : BitVec 512 × BitVec 256` output of `SessionCostedReductions.kemFailRed`
to `(SimKemSeed × SimKemEncRand)` as in `StatementComposed.hiddenSaltMixtureBound`. -/
def kemCandBvToVec (p : BitVec 512 × BitVec 256) : SimKemSeed × SimKemEncRand :=
  (⟨coinBytes p.1, coinBytes_length p.1⟩, keyToBytesVec32 p.2)

def kemCandVecToBv (p : SimKemSeed × SimKemEncRand) : BitVec 512 × BitVec 256 :=
  (bytesToWordLE 512 p.1.toList, bytesToWordLE 256 p.2.toList)

theorem coinBytes_bytesToWordLE512 (bs : Bytes) (h : bs.length = 64) :
    coinBytes (bytesToWordLE 512 bs) = bs := by
  refine List.ext_getElem (by simp [coinBytes_length, h]) fun j h1 h2 => ?_
  simp only [coinBytes, toLEBytes, List.getElem_ofFn]
  exact extractLsb'_bytesToWordLE 512 bs j h2 (by omega)

theorem keyToBytes32_bytesToWordLE256 (bs : Bytes) (h : bs.length = 32) :
    keyToBytes32 (bytesToWordLE 256 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToWordLE 256 bs j h2 (by omega)

theorem bytesToWordLE512_coinBytes (seed : BitVec 512) :
    bytesToWordLE 512 (coinBytes seed) = seed := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < 64 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToWordLE 512 (coinBytes seed) (i / 8)
      (by simp [coinBytes_length, hj]) (by omega))
  simp only [coinBytes, toLEBytes, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr,
    decide_true, Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem bytesToWordLE256_keyToBytes32 (rand : BitVec 256) :
    bytesToWordLE 256 (keyToBytes32 rand) = rand := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8))
    (extractLsb'_bytesToWordLE 256 (keyToBytes32 rand) (i / 8)
      (by simp [keyToBytes32, hj]) (by omega))
  simp only [keyToBytes32, List.getElem_ofFn, BitVec.getLsbD_extractLsb', hr,
    decide_true, Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

theorem coinBytes_zero : coinBytes 0#512 = List.replicate 64 0#8 := by
  refine List.ext_getElem (by simp [coinBytes_length]) fun i _ _ => ?_
  simp only [coinBytes, toLEBytes, List.getElem_ofFn, List.getElem_replicate]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [hj]

theorem keyToBytes32_zero : keyToBytes32 0#256 = List.replicate 32 0#8 := by
  refine List.ext_getElem (by simp [keyToBytes32]) fun i _ _ => ?_
  simp only [keyToBytes32, List.getElem_ofFn, List.getElem_replicate]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [hj]

theorem keyToBytesVec32_zero : keyToBytesVec32 0#256 = List.Vector.replicate 32 0#8 := by
  apply Subtype.ext
  change keyToBytes32 0#256 = (List.Vector.replicate 32 0#8).1
  rw [keyToBytes32_zero]
  rfl

@[simp] theorem kemCandBvToVec_zero :
    kemCandBvToVec (0#512, 0#256) = simDefaultKemCand := by
  unfold kemCandBvToVec simDefaultKemCand
  ext1
  · apply Subtype.ext
    simpa [List.Vector.replicate] using coinBytes_zero
  · exact keyToBytesVec32_zero

@[simp] theorem kemCandBvToVec_kemCandVecToBv (p : SimKemSeed × SimKemEncRand) :
    kemCandBvToVec (kemCandVecToBv p) = p := by
  rcases p with ⟨⟨s, hs⟩, ⟨r, hr⟩⟩
  unfold kemCandBvToVec kemCandVecToBv keyToBytesVec32
  ext1
  · apply Subtype.ext
    exact coinBytes_bytesToWordLE512 s hs
  · apply Subtype.ext
    exact keyToBytes32_bytesToWordLE256 r hr

@[simp] theorem kemCandVecToBv_kemCandBvToVec (p : BitVec 512 × BitVec 256) :
    kemCandVecToBv (kemCandBvToVec p) = p := by
  rcases p with ⟨seed, rand⟩
  unfold kemCandBvToVec kemCandVecToBv keyToBytesVec32
  ext1
  · exact bytesToWordLE512_coinBytes seed
  · exact bytesToWordLE256_keyToBytes32 rand

theorem kemCandBvToVec_getD (opt : Option (BitVec 512 × BitVec 256)) :
    kemCandBvToVec (opt.getD (0#512, 0#256)) = (opt.map kemCandBvToVec).getD simDefaultKemCand := by
  cases opt <;> simp

end CandidateCodec

/-! ## Atomic candidate and coin-sampling combinators -/

section AtomicCombinators

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def defaultKemCandAtomicE {Γ : List (Ty ASig)} : Expr AOps Γ (.prod BV512 BV256) :=
  .pair
    (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.bv512Lit 0#512) .unit)
    (sessPureOp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.bv256Lit 0#256) .unit)

omit [SampleableType Pt] in
@[simp] theorem eval_defaultKemCandAtomicE {Γ : List (Ty ASig)} (ρ : Env Γ) :
    (defaultKemCandAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).eval ρ =
      (0#512, 0#256) := rfl

omit [SampleableType Pt] in
theorem cost_defaultKemCandAtomicE {Γ : List (Ty ASig)} :
    (defaultKemCandAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost ≤ 10 := by
  have h : (defaultKemCandAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost = 8 := rfl
  omega

def kemCandOptGetDE {Γ : List (Ty ASig)}
    (optE : Expr AOps Γ (.opt (.prod BV512 BV256))) : Expr AOps Γ (.prod BV512 BV256) :=
  .caseOpt optE
    (defaultKemCandAtomicE (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    (.var .zero)

omit [SampleableType Pt] in
@[simp] theorem eval_kemCandOptGetDE {Γ : List (Ty ASig)}
    (optE : Expr AOps Γ (.opt (.prod BV512 BV256))) (ρ : Env Γ) :
    (kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optE).eval ρ = (optE.eval ρ).getD (0#512, 0#256) := by
  unfold kemCandOptGetDE
  dsimp only [Expr.eval]
  cases optE.eval ρ <;> rfl

omit [SampleableType Pt] in
theorem cost_kemCandOptGetDE {Γ : List (Ty ASig)}
    (optE : Expr AOps Γ (.opt (.prod BV512 BV256))) :
    (kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) optE).cost ≤ optE.cost + 12 := by
  have hd := cost_defaultKemCandAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  simp only [kemCandOptGetDE, Expr.cost]
  omega

def kemFailInitCoinsC {σ : Ty ASig}
    (mkInitE : Expr AOps [BV256, BV256, BV256, .bool, .unit] σ) :
    Comp AOps (coinOnlyIface ℓ Pt) [.unit] (.prod .unit σ) :=
  .bind (Comp.sample (I := coinOnlyIface ℓ Pt) UniformSamplerTag.bool .unit)
    (.bind (Comp.sample (I := coinOnlyIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit)
      (.bind (Comp.sample (I := coinOnlyIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit)
        (.bind (Comp.sample (I := coinOnlyIface ℓ Pt) (UniformSamplerTag.base .bv256) .unit)
          (.ret (.pair .unit mkInitE)))))

theorem kemFailInitCoinsC_queries_zero {σ : Ty ASig}
    (mkInitE : Expr AOps [BV256, BV256, BV256, .bool, .unit] σ)
    (w : Empty → ℕ) :
    (kemFailInitCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) mkInitE).queries w (fun _ => 0) = 0 := by
  simp [kemFailInitCoinsC, Comp.queries]

theorem kemFailInitCoinsC_cost {σ : Ty ASig}
    (mkInitE : Expr AOps [BV256, BV256, BV256, .bool, .unit] σ) :
    (kemFailInitCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) mkInitE).cost ≤ mkInitE.cost + 40 := by
  unfold kemFailInitCoinsC
  dsimp only [Comp.cost, Expr.cost, coinOnlyIface, atomicSamplers,
    ReductionDsl.unifSamplers, AtomicUnifBase.cost, BV256, AtomicUnifBase.sort]
  omega

theorem kemFailInitCoinsC_eval {σ : Ty ASig}
    (mkInitE : Expr AOps [BV256, BV256, BV256, .bool, .unit] σ) :
    (kemFailInitCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) mkInitE).eval (.cons () .nil) =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        return ((), mkInitE.eval
          (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil))))))) := by
  have hlift : ∀ {α : Type} (p : ProbComp α), (coinOnlyIface ℓ Pt).liftP p = p :=
    fun p => liftP_unif_eq_self _ (fun _ => rfl) p
  unfold kemFailInitCoinsC
  simp only [Comp.eval, Expr.eval, coinOnlyIface, atomicSamplers, ReductionDsl.unifSamplers, hlift]
  rfl

end AtomicCombinators

/-! ## Syntactic description-bit measures -/

section DescBits

def atomicSortDescBits : AtomicSort → ℕ
  | .pbytes w | .bytes w => 2 * bits w + 4
  | .fin n => 2 * bits n + 4
  | .pu32 | .u8 | .u32 | .u64 | .bv128 | .bv256 | .bv512
  | .pk | .idKey | .plain | .pt | .ghostSt | .binSt => 4

def atomicTyDescBits {ℓ : ℕ} {Pt : Type} : Ty (atomicSig ℓ Pt) → ℕ
  | .base b => atomicSortDescBits b + 4
  | .unit | .bool | .nat => 4
  | .opt t | .list t | .tbl t => atomicTyDescBits t + 4
  | .prod t u | .sum t u => atomicTyDescBits t + atomicTyDescBits u + 4

def varIdx {S : Sig} : {Γ : List (Ty S)} → {t : Ty S} → Var Γ t → ℕ
  | _, _, .zero => 0
  | _, _, .succ v => varIdx v + 1

def atomicPureOpDescBits : AtomicPureOp → ℕ
  | .pbytesLit w v => 8 * v.length + 2 * bits v.length + 2 * bits w + 8
  | .bytesLit w v => 8 * v.length + 2 * bits v.length + 2 * bits w + 8
  | .pbytesCat m n | .pbytesEq m n | .bytesCat m n | .bytesEq m n | .bytesLtOp m n =>
    2 * bits m + 2 * bits n + 8
  | .pbytesCons _ w | .bytesCons _ w => 2 * bits w + 16
  | .pbytesWiden w d | .bytesWiden w d => 2 * bits w + 2 * bits d + 8
  | .pbytesTakeK w k | .bytesTakeK w k => 2 * bits w + 2 * bits k + 8
  | .pbytesTake w | .pbytesDrop w | .pbytesLen w | .pbytesToBytes w
  | .bytesTake w | .bytesDrop w | .bytesLen w | .bytesToPbytes w => 2 * bits w + 8
  | .pu32Lit _ | .u32Lit _ => 40
  | .u8Lit _ => 16
  | .u64Lit _ => 72
  | .bv128Lit _ => 136
  | .bv256Lit _ => 264
  | .bv512Lit _ => 520
  | .finVal n | .finEq n => 2 * bits n + 8
  | .pbVarint | .bytesAppend8 | .bytesAppend16
  | .pu32OfNat | .pu32ToNat | .pu32Eq | .pu32ToU32 | .u32ToPu32
  | .u8OfNat | .u8ToNat | .u8Eq | .u8Lt
  | .u32OfNat | .u32ToNat | .u32Eq | .u32Lt | .u32Add | .u32Sub | .u32BeBytes
  | .u64OfNat | .u64ToNat | .u64Eq | .u64Lt | .u64Add | .u64Sub | .u64Trunc8
  | .u64LeBytes | .bytesToU64Le
  | .bv128Eq | .bv128Xor | .bv128ToBytes16 | .bytesToBv128
  | .bv256Eq | .bv256ToPbytes32 | .pbytesToBv256 | .bv256ToBytes32 | .bytesToBv256
  | .bv512ToBytes64 | .bv512ToPbytes64
  | .idKeyOfPbytes | .idKeySerialize | .idKeyEq
  | .pkOfPbytes | .pkDeserialize | .pkSerialize | .pkEq
  | .plainDefault | .plainToBytes | .bytesToPlain | .fitPlain | .plainEq
  | .checkShortCiphertext | .parsePreKeyWire | .partneredInnerBytes | .wireInnerBytes
  | .splitWhisperWire | .isValidSignalWire | .signalMsgParse | .wrapWhisperWire | .wrapPreKeyWire
  | .spqrParsePreamble | .spqrAssembleMsg | .spqrStateSplit | .spqrStateJoin
  | .ghostStateSplit | .ghostStateJoin | .encodeSessionRecord => 8

def atomicSymOpDescBits : AtomicSymOp → ℕ
  | .hmacSha256Op w => 2 * bits w + 8
  | _ => 8

def atomicSessionOpDescBits {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt} :
    (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).Op → ℕ
  | .inl (.inl (.inl (.inl o))) => atomicPureOpDescBits o + 4
  | .inl (.inl (.inl (.inr (.inl _)))) => 8 + 5
  | .inl (.inl (.inl (.inr (.inr o)))) => atomicSymOpDescBits o + 5
  | .inl (.inl (.inr _)) => 8 + 3
  | .inl (.inr (.inl _)) => 8 + 3
  | .inl (.inr (.inr _)) => 8 + 3
  | .inr _ => 8 + 1

def atomicExprDescBits {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)} (opBits : O.Op → ℕ) :
    {Γ : List (Ty (atomicSig ℓ Pt))} → {t : Ty (atomicSig ℓ Pt)} → Expr O Γ t → ℕ
  | _, _, .var v => 2 * bits (varIdx v) + 6
  | _, _, .unit => 6
  | _, _, .bool _ => 7
  | _, _, .nat n => 2 * bits n + 6
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b
  | _, _, .and a b | _, _, .pair a b | _, _, .cons a b | _, _, .take a b
  | _, _, .tget a b => atomicExprDescBits opBits a + atomicExprDescBits opBits b + 6
  | _, _, .mulK k a | _, _, .divK k a | _, _, .modK k a =>
    2 * bits k + atomicExprDescBits opBits a + 6
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .some a
  | _, _, .len a | _, _, .tconst a => atomicExprDescBits opBits a + 6
  | _, _, .ite c a b | _, _, .tset c a b =>
    atomicExprDescBits opBits c + atomicExprDescBits opBits a + atomicExprDescBits opBits b + 6
  | _, .sum _ u, .inl a => atomicTyDescBits u + atomicExprDescBits opBits a + 6
  | _, .sum t _, .inr a => atomicTyDescBits t + atomicExprDescBits opBits a + 6
  | _, .opt t, .none => atomicTyDescBits t + 6
  | _, .list t, .nil => atomicTyDescBits t + 6
  | _, _, .caseOpt e n s =>
    atomicExprDescBits opBits e + atomicExprDescBits opBits n + atomicExprDescBits opBits s + 6
  | _, _, .caseSum e l r =>
    atomicExprDescBits opBits e + atomicExprDescBits opBits l + atomicExprDescBits opBits r + 6
  | _, _, .letE e b => atomicExprDescBits opBits e + atomicExprDescBits opBits b + 6
  | _, _, .op o a => opBits o + atomicExprDescBits opBits a + 6
  | _, _, .appendL k a b | _, _, .findB k a b | _, _, .anyB k a b | _, _, .mapB k a b =>
    2 * bits k + atomicExprDescBits opBits a + atomicExprDescBits opBits b + 6
  | _, _, .foldrB k l z f =>
    2 * bits k + atomicExprDescBits opBits l + atomicExprDescBits opBits z +
      atomicExprDescBits opBits f + 6

def atomicCompDescBits {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (atomicSig ℓ Pt) T}
    (opBits : O.Op → ℕ) (sBits : I.smp.Samp → ℕ) (qBits : I.Tag → ℕ) :
    {Γ : List (Ty (atomicSig ℓ Pt))} → {t : Ty (atomicSig ℓ Pt)} → Comp O I Γ t → ℕ
  | _, _, .ret e => atomicExprDescBits opBits e + 6
  | _, _, .bind c k =>
    atomicCompDescBits opBits sBits qBits c + atomicCompDescBits opBits sBits qBits k + 6
  | _, _, .ite b c d =>
    atomicExprDescBits opBits b + atomicCompDescBits opBits sBits qBits c +
      atomicCompDescBits opBits sBits qBits d + 6
  | _, _, .caseOpt e n s =>
    atomicExprDescBits opBits e + atomicCompDescBits opBits sBits qBits n +
      atomicCompDescBits opBits sBits qBits s + 6
  | _, _, .caseSum e l r =>
    atomicExprDescBits opBits e + atomicCompDescBits opBits sBits qBits l +
      atomicCompDescBits opBits sBits qBits r + 6
  | _, _, .sample s e => sBits s + atomicExprDescBits opBits e + 6
  | _, _, .query g e => qBits g + atomicExprDescBits opBits e + 6
  | _, _, .iter n e body =>
    2 * bits n + atomicExprDescBits opBits e + atomicCompDescBits opBits sBits qBits body + 6
  | _, _, .findM k l p | _, _, .anyM k l p | _, _, .mapM k l p =>
    2 * bits k + atomicExprDescBits opBits l + atomicCompDescBits opBits sBits qBits p + 6
  | _, _, .consumeFirstM k l p mk =>
    2 * bits k + atomicExprDescBits opBits l + atomicCompDescBits opBits sBits qBits p +
      atomicExprDescBits opBits mk + 6
  | _, _, .foldM k l z f =>
    2 * bits k + atomicExprDescBits opBits l + atomicExprDescBits opBits z +
      atomicCompDescBits opBits sBits qBits f + 6

/-- Total syntactic description bit-length of a session-level `CostedReduction` over
`atomicSessionOps` and `coinOnlyIface`. -/
def atomicRedDescBits {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {κ : Type} {G : OracleSpec κ} {GC : GameCodec (atomicSig ℓ Pt) G}
    {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt) G GC rIn aIn aOut out) : ℕ :=
  atomicTyDescBits R.σ + atomicTyDescBits rIn + atomicTyDescBits aIn +
    atomicTyDescBits aOut + atomicTyDescBits out +
    (atomicTyDescBits GC.Q + atomicTyDescBits GC.R) +
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim R.init +
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim R.handle +
    atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim R.finish

abbrev defaultDescBitBudget : ℕ := 2 ^ 24

def descBitBudget (costBudget : ℕ) : ℕ :=
  2 ^ 23 + 2 ^ 13 * bits costBudget

/-- Per-session ratchet/SM description-bit budget at query bound `q` and epoch cap `qep`. -/
def ratchetDescBudget (q qep : ℕ) : ℕ :=
  descBitBudget (ratchetCostBudget q qep + qep)

theorem descBitBudget_mono {B₁ B₂ : ℕ} (h : B₁ ≤ B₂) :
    descBitBudget B₁ ≤ descBitBudget B₂ := by
  unfold descBitBudget
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (bits_mono h)) _

theorem ratchetDescBudget_mono {q₁ q₂ qep₁ qep₂ : ℕ} (hq : q₁ ≤ q₂) (hqep : qep₁ ≤ qep₂) :
    ratchetDescBudget q₁ qep₁ ≤ ratchetDescBudget q₂ qep₂ := by
  apply descBitBudget_mono
  unfold ratchetCostBudget
  have h1 : (q₁ + 1) ^ 2 ≤ (q₂ + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : CryptoGames.LibsignalSession.maxForwardJumps + bits qep₁ ≤
      CryptoGames.LibsignalSession.maxForwardJumps + bits qep₂ := by
    have hb := bits_mono hqep
    omega
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2) hqep

theorem descBitBudget_le_default {B : ℕ} (hB : B < 2 ^ 126) :
    descBitBudget B ≤ defaultDescBitBudget := by
  have hbits : bits B ≤ 126 := by
    by_cases h0 : B = 0
    · subst h0; decide
    · have hlog : Nat.log 2 B < 126 := Nat.log_lt_of_lt_pow h0 hB
      dsimp only [bits]
      omega
  unfold descBitBudget defaultDescBitBudget
  omega

theorem ratchetDescBudget_le_default {q qep : ℕ}
    (hB : ratchetCostBudget q qep + qep < 2 ^ 126) :
    ratchetDescBudget q qep ≤ defaultDescBitBudget :=
  descBitBudget_le_default hB

theorem ratchetDescBudget_le_reductionSizeBudget {q qep : ℕ}
    (hB : ratchetCostBudget q qep + qep < 2 ^ 126) :
    ratchetDescBudget q qep ≤ reductionSizeBudget :=
  descBitBudget_le_default hB

theorem two_mul_atomicPureOp_opSize_le (o : AtomicPureOp) :
    2 * o.opSize ≤ atomicPureOpDescBits o := by
  cases o <;> simp only [AtomicPureOp.opSize, atomicPureOpDescBits] <;> omega

theorem two_mul_atomicSessionOps_opSize_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (o : (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).Op) :
    2 * (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).opSize o ≤
      atomicSessionOpDescBits o := by
  rcases o with (((o | (_ | _)) | _) | (_ | _)) | _
  · have h := two_mul_atomicPureOp_opSize_le o
    change 2 * o.opSize ≤ atomicPureOpDescBits o + 4
    omega
  · change 2 * 0 ≤ 8 + 5; omega
  · change 2 * 0 ≤ atomicSymOpDescBits _ + 5; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 3; omega
  · change 2 * 0 ≤ 8 + 1; omega

theorem atomicSessionOps_opSize_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (o : (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).Op) :
    (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).opSize o ≤
      atomicSessionOpDescBits o := by
  have h := two_mul_atomicSessionOps_opSize_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) o
  omega

theorem expr_size_le_atomicExprDescBits {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    (opBits : O.Op → ℕ) {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (e : Expr O Γ t)
    (hop : ∀ o, O.opSize o ≤ opBits o := by intro o; exact atomicSessionOps_opSize_le o) :
    e.size ≤ atomicExprDescBits opBits e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp only [Expr.size, atomicExprDescBits]; omega
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | tget _ _ ha hb
  | appendL _ _ _ ha hb | findB _ _ _ ha hb | anyB _ _ _ ha hb | mapB _ _ _ ha hb
  | letE _ _ ha hb =>
    simp only [Expr.size, atomicExprDescBits]; omega
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | len _ ha | tconst _ ha =>
    simp only [Expr.size, atomicExprDescBits]; omega
  | ite _ _ _ hc ha hb | tset _ _ _ hc ha hb | caseOpt _ _ _ hc ha hb
  | caseSum _ _ _ hc ha hb | foldrB _ _ _ _ hc ha hb =>
    simp only [Expr.size, atomicExprDescBits]; omega
  | op o _ ha =>
    have ho := hop o
    simp only [Expr.size, atomicExprDescBits]; omega

theorem comp_size_le_atomicCompDescBits {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (atomicSig ℓ Pt) T}
    (opBits : O.Op → ℕ) (sBits : I.smp.Samp → ℕ) (qBits : I.Tag → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (c : Comp O I Γ t)
    (hop : ∀ o, O.opSize o ≤ opBits o := by intro o; exact atomicSessionOps_opSize_le o) :
    c.size ≤ atomicCompDescBits opBits sBits qBits c := by
  induction c with
  | ret e =>
    have he := expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | bind c k ihc ihk =>
    simp only [Comp.size, atomicCompDescBits]; omega
  | ite b c d ihc ihd =>
    have hb := expr_size_le_atomicExprDescBits opBits b hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | caseOpt e n s ihn ihs =>
    have he := expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | caseSum e l r ihl ihr =>
    have he := expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | sample s e =>
    have he := expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | query g e =>
    have he := expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | iter n e body ih =>
    have he := expr_size_le_atomicExprDescBits opBits e hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | findM k l p ih | anyM k l p ih | mapM k l p ih =>
    have hl := expr_size_le_atomicExprDescBits opBits l hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | consumeFirstM k l p mk ih =>
    have hl := expr_size_le_atomicExprDescBits opBits l hop
    have hmk := expr_size_le_atomicExprDescBits opBits mk hop
    simp only [Comp.size, atomicCompDescBits]; omega
  | foldM k l z f ih =>
    have hl := expr_size_le_atomicExprDescBits opBits l hop
    have hz := expr_size_le_atomicExprDescBits opBits z hop
    simp only [Comp.size, atomicCompDescBits]; omega

theorem red_size_le_of_atomicCompDescBits {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I : Iface (atomicSig ℓ Pt) T}
    (opBits : O.Op → ℕ) (sBits : I.smp.Samp → ℕ) (qBits : I.Tag → ℕ)
    {κ : Type} {G : OracleSpec κ} {GC : GameCodec (atomicSig ℓ Pt) G}
    {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction O I G GC rIn aIn aOut out)
    (hop : ∀ o, O.opSize o ≤ opBits o := by intro o; exact atomicSessionOps_opSize_le o) :
    R.size ≤ atomicCompDescBits opBits sBits qBits R.init +
      atomicCompDescBits opBits sBits qBits R.handle +
      atomicCompDescBits opBits sBits qBits R.finish := by
  have hi := comp_size_le_atomicCompDescBits opBits sBits qBits R.init hop
  have hh := comp_size_le_atomicCompDescBits opBits sBits qBits R.handle hop
  have hf := comp_size_le_atomicCompDescBits opBits sBits qBits R.finish hop
  dsimp only [CostedReduction.size]
  omega

theorem red_size_le_atomicRedDescBits {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {κ : Type} {G : OracleSpec κ} {GC : GameCodec (atomicSig ℓ Pt) G}
    {rIn aIn aOut out : Ty (atomicSig ℓ Pt)}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt) G GC rIn aIn aOut out) :
    R.size ≤ atomicRedDescBits R := by
  refine (red_size_le_of_atomicCompDescBits (I := coinOnlyIface ℓ Pt)
    (atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
    (fun _ => 8) Empty.elim R).trans ?_
  unfold atomicRedDescBits
  let T := atomicTyDescBits R.σ + atomicTyDescBits rIn + atomicTyDescBits aIn +
    atomicTyDescBits aOut + atomicTyDescBits out +
    (atomicTyDescBits GC.Q + atomicTyDescBits GC.R)
  change _ ≤ T + _ + _ + _
  rw [Nat.add_assoc T, Nat.add_assoc T]
  exact Nat.le_add_left _ T

theorem dummyPairSessionRed_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {rIn : Ty (atomicSig ℓ Pt)} (hrIn : atomicTyDescBits rIn ≤ 64) (q qep : ℕ) :
    atomicRedDescBits
      (dummyPairSessionRed (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        (coinOnlyIface ℓ Pt) rIn) ≤
      ratchetDescBudget q qep := by
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
  have hcodecQ : atomicTyDescBits (e2eSessionCodec ℓ Pt).Q ≤ 200 := by
    dsimp only [e2eSessionCodec, ReductionDsl.smQT, ReductionDsl.B, atomicTyDescBits,
      atomicSortDescBits]
    rw [hb32]
    omega
  have hcodecR : atomicTyDescBits (e2eSessionCodec ℓ Pt).R ≤ 200 := by
    dsimp only [e2eSessionCodec, ReductionDsl.smRT, atomicTyDescBits, atomicSortDescBits]
    omega
  have hhandle :
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
        (dummyPairSessionRed (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
          (coinOnlyIface ℓ Pt) rIn).handle ≤ 300 := by
    dsimp only [dummyPairSessionRed, e2eSessionCodec, ReductionDsl.smRT,
      atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits]
    omega
  have hfin :
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
        (dummyPairSessionRed (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
          (coinOnlyIface ℓ Pt) rIn).finish ≤ 1500 := by
    dsimp only [dummyPairSessionRed, sessPureOp,
      atomicCompDescBits, atomicExprDescBits, atomicSessionOpDescBits, atomicPureOpDescBits]
    omega
  have hinit :
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
        (dummyPairSessionRed (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
          (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
          (coinOnlyIface ℓ Pt) rIn).init ≤ 50 := by
    dsimp only [dummyPairSessionRed, atomicCompDescBits, atomicExprDescBits]
    omega
  have hout : atomicTyDescBits (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) BV256) = 20 := rfl
  have hbase : 2 ^ 23 ≤ ratchetDescBudget q qep := by
    unfold ratchetDescBudget descBitBudget
    omega
  unfold atomicRedDescBits
  have hsig : atomicTyDescBits
      (dummyPairSessionRed (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)
        (coinOnlyIface ℓ Pt) rIn).σ = 4 := rfl
  have hain : atomicTyDescBits (.unit : Ty (atomicSig ℓ Pt)) = 4 := rfl
  have haout : atomicTyDescBits (.bool : Ty (atomicSig ℓ Pt)) = 4 := rfl
  omega

theorem defaultKemCandAtomicE_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    atomicExprDescBits
      (atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      (defaultKemCandAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)) ≤ 900 := by
  dsimp only [defaultKemCandAtomicE, sessPureOp, atomicExprDescBits,
    atomicSessionOpDescBits, atomicPureOpDescBits]
  omega

theorem kemCandOptGetDE_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (optE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.opt (.prod BV512 BV256))) :
    atomicExprDescBits
      (atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      (kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) optE) ≤
      atomicExprDescBits atomicSessionOpDescBits optE + 920 := by
  have hd := defaultKemCandAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  have hb0 : bits 0 = 1 := by decide
  dsimp only [kemCandOptGetDE, atomicExprDescBits, varIdx]
  rw [hb0]
  omega

theorem kemFailInitCoinsC_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {σ : Ty (atomicSig ℓ Pt)}
    (mkInitE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [BV256, BV256, BV256, .bool, .unit] σ) :
    atomicCompDescBits
      (atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam))
      (fun _ => 8) Empty.elim
      (kemFailInitCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) mkInitE) ≤
      atomicExprDescBits atomicSessionOpDescBits mkInitE + 124 := by
  unfold kemFailInitCoinsC
  dsimp only [coinOnlyIface, atomicSamplers, ReductionDsl.unifSamplers,
    AtomicUnifBase.sort, BV256, atomicCompDescBits, atomicExprDescBits]
  omega

theorem bits_two_mul_add_two_le_ratchetCostBudget (q qep : ℕ) :
    bits (2 * q + 2) ≤ bits (ratchetCostBudget q qep + qep) := by
  apply bits_mono
  unfold ratchetCostBudget maxForwardJumps
  nlinarith

theorem bits_qep_le_ratchetCostBudget (q qep : ℕ) :
    bits qep ≤ bits (ratchetCostBudget q qep + qep) :=
  bits_mono (by omega)

theorem kemFailRed_descBits_le_of_parts {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (R : CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool (.prod BV512 BV256))
    (q qep : ℕ)
    (hparts :
      atomicTyDescBits R.σ +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim R.init +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim R.handle +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim R.finish ≤
      2 ^ 22 + 2 ^ 13 * bits (ratchetCostBudget q qep + qep)) :
    atomicRedDescBits R ≤ ratchetDescBudget q qep := by
  have hb32 : bits ((32 : ℕ+) : ℕ) = 6 := by decide
  have hcodecQ : atomicTyDescBits (e2eSessionCodec ℓ Pt).Q ≤ 200 := by
    dsimp only [e2eSessionCodec, ReductionDsl.smQT, ReductionDsl.B, atomicTyDescBits,
      atomicSortDescBits]
    rw [hb32]
    omega
  have hcodecR : atomicTyDescBits (e2eSessionCodec ℓ Pt).R ≤ 200 := by
    dsimp only [e2eSessionCodec, ReductionDsl.smRT, atomicTyDescBits, atomicSortDescBits]
    omega
  have hout : atomicTyDescBits (.prod (BV512 (ℓ := ℓ) (Pt := Pt)) BV256) = 20 := rfl
  have hu : atomicTyDescBits (.unit : Ty (atomicSig ℓ Pt)) = 4 := rfl
  have hb : atomicTyDescBits (.bool : Ty (atomicSig ℓ Pt)) = 4 := rfl
  unfold atomicRedDescBits ratchetDescBudget descBitBudget
  omega

end DescBits

/-! ## Iterated `simulateQ` loop couplings -/

section LoopInvariants

/-- Relational coupling loop invariant for `simulateQ` on `unifSpec + G` under a remaining-query
bound `oa.IsQueryBoundP (isGameQuery (G := G)) qAdv`. -/
theorem simulateQ_bind_eq_of_rel_couple {ι κ : Type} {T : OracleSpec ι} {G : OracleSpec κ}
    {σ₁ σ₂ α β : Type}
    (uImpl : (n : unifSpec.Domain) → OracleComp T (unifSpec.Range n))
    (so₁ : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T)))
    (so₂ : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T)))
    (Rel : ℕ → σ₁ → σ₂ → Prop)
    (k₁ : α → σ₁ → OracleComp T β)
    (k₂ : α → σ₂ → OracleComp T β)
    (hU₁ : ∀ n s₁, (so₁ (.inl n)).run s₁ = (StateT.lift (uImpl n)).run s₁)
    (hU₂ : ∀ n s₂, (so₂ (.inl n)).run s₂ = (StateT.lift (uImpl n)).run s₂)
    (hstep : ∀ m t s₁ s₂, Rel (m + 1) s₁ s₂ →
      ∃ c : OracleComp T (G.Range t × σ₁ × σ₂),
        ((fun r => (r.1, r.2.1)) <$> c) = (so₁ (.inr t)).run s₁ ∧
        ((fun r => (r.1, r.2.2)) <$> c) = (so₂ (.inr t)).run s₂ ∧
        ∀ r ∈ support c, Rel m r.2.1 r.2.2)
    (hmono : ∀ {m n} {s₁ s₂}, m ≤ n → Rel n s₁ s₂ → Rel m s₁ s₂)
    (hk : ∀ a s₁ s₂, Rel 0 s₁ s₂ → k₁ a s₁ = k₂ a s₂) :
    ∀ {oa : OracleComp (unifSpec + G) α} {qAdv : ℕ},
      oa.IsQueryBoundP (isGameQuery (G := G)) qAdv →
      ∀ s₁ s₂, Rel qAdv s₁ s₂ →
        ((simulateQ so₁ oa).run s₁ >>= fun p => k₁ p.1 p.2) =
        ((simulateQ so₂ oa).run s₂ >>= fun p => k₂ p.1 p.2) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qAdv _ s₁ s₂ hs
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hk a s₁ s₂ (hmono (Nat.zero_le qAdv) hs)
  | query_bind q mx ih =>
    intro qAdv hq s₁ s₂ hs
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, bind_assoc, bind_assoc]
    cases q with
    | inl n =>
      rw [hU₁, hU₂]
      simp only [StateT.run_lift, bind_assoc, pure_bind]
      exact bind_congr fun u => ih u (hq.2 u) s₁ s₂ hs
    | inr t =>
      have hpos : 0 < qAdv := hq.1.resolve_left (by simp [isGameQuery])
      obtain ⟨m, rfl⟩ : ∃ m, qAdv = m + 1 := ⟨qAdv - 1, by omega⟩
      have hqm : ∀ u, (mx u).IsQueryBoundP (isGameQuery (G := G)) m := by
        intro u; simpa [isGameQuery] using hq.2 u
      obtain ⟨c, hc₁, hc₂, hsupp⟩ := hstep m t s₁ s₂ hs
      rw [← hc₁, ← hc₂, bind_map_left, bind_map_left]
      exact bind_congr_of_mem_support' c fun r hr =>
        ih r.1 (hqm r.1) r.2.1 r.2.2 (hsupp r hr)

/-- Relational `f <$> R.eval A x` bridge for `CostedReduction` via per-step couplings. -/
theorem eval_map_eq_simulateQ_of_rel {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {GC : GameCodec S G}
    {rIn aIn aOut out : Ty S} {β : Type}
    (R : CostedReduction O I G GC rIn aIn aOut out) (f : out.denote → β)
    {σ₁ : Type} (Rel : ℕ → σ₁ → R.σ.denote → Prop)
    (initImpl : rIn.denote → OracleComp T (aIn.denote × σ₁))
    (so : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T)))
    (finishImpl : σ₁ → aOut.denote → OracleComp T β)
    (qAdv : ℕ) (x : rIn.denote)
    (hinit : ∃ c₀ : OracleComp T (aIn.denote × σ₁ × R.σ.denote),
      ((fun r => (r.1, r.2.1)) <$> c₀) = initImpl x ∧
      ((fun r => (r.1, r.2.2)) <$> c₀) = R.init.eval (.cons x .nil) ∧
      ∀ r ∈ support c₀, Rel qAdv r.2.1 r.2.2)
    (hU : ∀ n s₁, (so (.inl n)).run s₁ = (StateT.lift (I.fwdU n)).run s₁)
    (hstep : ∀ m t s₁ s₂, Rel (m + 1) s₁ s₂ →
      ∃ c : OracleComp T (G.Range t × σ₁ × R.σ.denote),
        ((fun r => (r.1, r.2.1)) <$> c) = (so (.inr t)).run s₁ ∧
        ((fun r => (r.1, r.2.2)) <$> c) = (R.impl (.inr t)).run s₂ ∧
        ∀ r ∈ support c, Rel m r.2.1 r.2.2)
    (hfin : ∀ s₁ s₂ b, Rel 0 s₁ s₂ →
      (f <$> R.finish.eval (.cons s₂ (.cons b .nil))) = finishImpl s₁ b)
    (hmono : ∀ {m n} {s₁ s₂}, m ≤ n → Rel n s₁ s₂ → Rel m s₁ s₂)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hb : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) qAdv) :
    (f <$> R.eval A x) = (do
      let (a, s₀) ← initImpl x
      let (b, s₁) ← (simulateQ so (A a)).run s₀
      finishImpl s₁ b) := by
  obtain ⟨c₀, hc₀₁, hc₀₂, hsupp₀⟩ := hinit
  unfold CostedReduction.eval
  rw [← hc₀₁, ← hc₀₂, map_bind, bind_map_left, bind_map_left]
  refine bind_congr_of_mem_support' c₀ fun ⟨a, s₁, s₂⟩ hr₀ => ?_
  rw [map_bind]
  symm
  exact simulateQ_bind_eq_of_rel_couple I.fwdU so R.impl Rel
    (fun b s₁' => finishImpl s₁' b)
    (fun b s₂' => f <$> R.finish.eval (.cons s₂' (.cons b .nil)))
    hU (fun _ _ => rfl) hstep hmono
    (fun b s₁' s₂' h0 => (hfin s₁' s₂' b h0).symm)
    (hb a) s₁ s₂ (hsupp₀ (a, s₁, s₂) hr₀)

theorem eval_map_eq_simulateQ_of_enc {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {GC : GameCodec S G}
    {rIn aIn aOut out : Ty S} {β : Type}
    (R : CostedReduction O I G GC rIn aIn aOut out) (f : out.denote → β)
    {σ₁ : Type} (enc : σ₁ → R.σ.denote) (Inv : ℕ → σ₁ → Prop)
    (initImpl : rIn.denote → OracleComp T (aIn.denote × σ₁))
    (so : QueryImpl (unifSpec + G) (StateT σ₁ (OracleComp T)))
    (finishImpl : σ₁ → aOut.denote → OracleComp T out.denote)
    (qAdv : ℕ) (x : rIn.denote)
    (hinit : R.init.eval (.cons x .nil) = Prod.map id enc <$> initImpl x)
    (hinitInv : ∀ r ∈ support (initImpl x), Inv qAdv r.2)
    (hU : ∀ n s, (so (.inl n)).run s = (StateT.lift (I.fwdU n)).run s)
    (hstep : ∀ m t s, Inv (m + 1) s →
      (R.impl (.inr t)).run (enc s) = Prod.map id enc <$> (so (.inr t)).run s ∧
      ∀ r ∈ support ((so (.inr t)).run s), Inv m r.2)
    (hfin : ∀ s b, Inv 0 s → R.finish.eval (.cons (enc s) (.cons b .nil)) = finishImpl s b)
    (hmono : ∀ {m n} (s), m ≤ n → Inv n s → Inv m s)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hb : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) qAdv) :
    (f <$> R.eval A x) = (do
      let (a, s₀) ← initImpl x
      let (b, s₁) ← (simulateQ so (A a)).run s₀
      f <$> finishImpl s₁ b) := by
  rw [eval_eq_simulateQ_of_enc R enc Inv initImpl so finishImpl qAdv x
    hinit hinitInv hU hstep hfin hmono A hb]
  simp only [map_bind]

theorem eval_map_eq_simulateQ_of_abs {S : Sig} {O : Ops S} {ι κ : Type} {T : OracleSpec ι}
    {I : Iface S T} {G : OracleSpec κ} {GC : GameCodec S G}
    {rIn aIn aOut out : Ty S} {β : Type}
    (R : CostedReduction O I G GC rIn aIn aOut out) (f : out.denote → β)
    {σ₂ : Type} (abs : R.σ.denote → σ₂) (Inv : ℕ → R.σ.denote → Prop)
    (initImpl : rIn.denote → OracleComp T (aIn.denote × σ₂))
    (so : QueryImpl (unifSpec + G) (StateT σ₂ (OracleComp T)))
    (finishImpl : σ₂ → aOut.denote → OracleComp T out.denote)
    (qAdv : ℕ) (x : rIn.denote)
    (hinit : (Prod.map id abs <$> R.init.eval (.cons x .nil)) = initImpl x)
    (hinitInv : ∀ r ∈ support (R.init.eval (.cons x .nil)), Inv qAdv r.2)
    (hU : ∀ n s, (so (.inl n)).run s = (StateT.lift (I.fwdU n)).run s)
    (hstep : ∀ m t s, Inv (m + 1) s →
      (Prod.map id abs <$> ((R.impl (.inr t)).run s)) = (so (.inr t)).run (abs s) ∧
      ∀ r ∈ support ((R.impl (.inr t)).run s), Inv m r.2)
    (hfin : ∀ s b, Inv 0 s → R.finish.eval (.cons s (.cons b .nil)) = finishImpl (abs s) b)
    (hmono : ∀ {m n} (s), m ≤ n → Inv n s → Inv m s)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (hb : ∀ a, (A a).IsQueryBoundP (isGameQuery (G := G)) qAdv) :
    (f <$> R.eval A x) = (do
      let (a, s₀) ← initImpl x
      let (b, s₁) ← (simulateQ so (A a)).run s₀
      f <$> finishImpl s₁ b) := by
  rw [R.eval_eq_simulateQ_of_abs abs Inv initImpl so finishImpl qAdv x
    hinit hinitInv hU hstep hfin hmono A hb]
  simp only [map_bind]

theorem map_run_simulateQ_self_of_proj {ι₁ ι₂ : Type} {S₁ : OracleSpec ι₁} {S₂ : OracleSpec ι₂}
    {σ α : Type} (so : QueryImpl S₁ (StateT σ (OracleComp S₂))) (proj : σ → σ)
    (hidem : ∀ s, proj (proj s) = proj s)
    (hso : ∀ {t : S₁.Domain} (q : S₁.Domain) (s : σ),
      t = q → (Prod.map id proj <$> (so q).run s) = (Prod.map id proj <$> (so q).run (proj s))) :
    ∀ (oa : OracleComp S₁ α) (s : σ),
      (Prod.map id proj <$> (simulateQ so oa).run s) =
      (Prod.map id proj <$> (simulateQ so oa).run (proj s)) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s
    simp [simulateQ_pure, Prod.map, hidem]
  | query_bind q mx ih =>
    intro s
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, map_bind, map_bind]
    trans ((so q).run s >>= fun p => Prod.map id proj <$> (simulateQ so (mx p.1)).run (proj p.2))
    · exact bind_congr fun p => ih p.1 p.2
    · have hstep := congrArg
        (fun m => m >>= fun q' : S₁.Range q × σ =>
          Prod.map id proj <$> (simulateQ so (mx q'.1)).run q'.2)
        (hso q s rfl)
      simp only [bind_map_left, Prod.map, id_eq] at hstep
      rw [hstep]
      exact bind_congr fun p => (ih p.1 p.2).symm

theorem simulateQ_bind_eq_of_proj_comm {ι₁ ι₂ : Type} {S₁ : OracleSpec ι₁} {S₂ : OracleSpec ι₂}
    {σ α β : Type}
    (so₁ so₂ : QueryImpl S₁ (StateT σ (OracleComp S₂))) (proj : σ → σ)
    (hidem : ∀ s, proj (proj s) = proj s)
    (h₁₂ : ∀ (q : S₁.Domain) (s : σ),
      (Prod.map id proj <$> (so₁ q).run s) = (Prod.map id proj <$> (so₂ q).run (proj s)))
    (h₂₂ : ∀ (q : S₁.Domain) (s : σ),
      (Prod.map id proj <$> (so₂ q).run s) = (Prod.map id proj <$> (so₂ q).run (proj s)))
    (k : α → σ → OracleComp S₂ β) (hk : ∀ a s, k a (proj s) = k a s)
    (oa : OracleComp S₁ α) {s₁ s₂ : σ} (hs : proj s₁ = proj s₂) :
    ((simulateQ so₁ oa).run s₁ >>= fun p => k p.1 p.2) =
    ((simulateQ so₂ oa).run s₂ >>= fun p => k p.1 p.2) := by
  have hmap : ∀ (oa' : OracleComp S₁ α) (s : σ),
      (Prod.map id proj <$> (simulateQ so₁ oa').run s) =
      (Prod.map id proj <$> (simulateQ so₂ oa').run (proj s)) := by
    intro oa'
    induction oa' using OracleComp.inductionOn with
    | pure a =>
      intro s
      simp [simulateQ_pure, Prod.map, hidem]
    | query_bind q mx ih =>
      intro s
      rw [run_simulateQ_query_bind, run_simulateQ_query_bind, map_bind, map_bind]
      trans ((so₁ q).run s >>= fun p => Prod.map id proj <$> (simulateQ so₂ (mx p.1)).run (proj p.2))
      · exact bind_congr fun p => ih p.1 p.2
      · have hstep := congrArg
          (fun m => m >>= fun q' : S₁.Range q × σ =>
            Prod.map id proj <$> (simulateQ so₂ (mx q'.1)).run q'.2)
          (h₁₂ q s)
        simp only [bind_map_left, Prod.map, id_eq] at hstep
        rw [hstep]
        exact bind_congr fun p =>
          (map_run_simulateQ_self_of_proj so₂ proj hidem (fun q' s' _ => h₂₂ q' s') (mx p.1) p.2).symm
  have hfull :
      (Prod.map id proj <$> (simulateQ so₁ oa).run s₁) =
      (Prod.map id proj <$> (simulateQ so₂ oa).run s₂) := by
    rw [hmap oa s₁, hs, ← map_run_simulateQ_self_of_proj so₂ proj hidem (fun q' s' _ => h₂₂ q' s') oa s₂]
  calc ((simulateQ so₁ oa).run s₁ >>= fun p => k p.1 p.2)
      = ((simulateQ so₁ oa).run s₁ >>= fun p => k p.1 (proj p.2)) :=
          bind_congr fun p => (hk p.1 p.2).symm
    _ = ((Prod.map id proj <$> (simulateQ so₁ oa).run s₁) >>= fun p => k p.1 p.2) :=
          (bind_map_left (Prod.map id proj) ((simulateQ so₁ oa).run s₁) (fun p => k p.1 p.2)).symm
    _ = ((Prod.map id proj <$> (simulateQ so₂ oa).run s₂) >>= fun p => k p.1 p.2) := by
          rw [hfull]
    _ = ((simulateQ so₂ oa).run s₂ >>= fun p => k p.1 (proj p.2)) :=
          bind_map_left (Prod.map id proj) ((simulateQ so₂ oa).run s₂) (fun p => k p.1 p.2)
    _ = ((simulateQ so₂ oa).run s₂ >>= fun p => k p.1 p.2) :=
          bind_congr fun p => hk p.1 p.2

end LoopInvariants

/-! ## Promoted `kemFailRed` assembly and bounds -/

section KemFailRedAssembly

def kemFailClampInitState {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (K : MlKem) (b : Bool) (k1 k2 pqrKey : BitVec 256) :
    LibsignalToModularSchemeSimState Bytes Pt ℓ × KemExtraRaw Bytes (BitVec 512) Pt ℓ :=
  let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
  let gFig₀ : (@fig8GsTy Bytes (BitVec 512) Pt ℓ).denote :=
    ((simOpsUnitCost (ℓ := ℓ) P Dh encPt encT decT lam K id).eval SimOp.fig8Init (k1, k2),
     (b, false, (0, 0), (0, 0), none, [], [], [], (fun _ => 0, fun _ => 0), [], []))
  let trCand₀ :=
    (simOpsUnitCost (ℓ := ℓ) P Dh encPt encT decT lam K id).eval SimOp.initKemFailTrack pqrKey
  (sC₀, (gFig₀, trCand₀))

def kemFailSimInitState {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params Bytes (BitVec 512)) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (b : Bool) (k1 k2 pqrKey : BitVec 256) :
    LibsignalToModularSchemeSimState Bytes Pt ℓ ×
      (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
      KemFailTrackState P.C.F :=
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let sC₀ := initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
  let gh₀ := (initState fig (k1, k2) b, false)
  let tr₀ := initKemFailTrack P.C.F pqrKey
  (sC₀, gh₀, tr₀)

theorem redKemFailHiddenSalt_eq_splitCoins {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] (P : Params Bytes (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    redKemFailHiddenSalt P K ℓ Dh encPt encT decT idOf lam qep A =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let (_, (_, _, tr)) ←
          (simulateQ (kemFailSimImpl P K ℓ Dh encPt encT decT idOf lam qep) A).run
            (kemFailSimInitState P Dh encPt encT idOf lam b k1 k2 pqrKey)
        return tr.cand.getD simDefaultKemCand) := by
  unfold redKemFailHiddenSalt kemFailSimInitState
  refine bind_congr fun b => ?_
  rw [sample_prod_bindU]
  rfl

/-- Real-branch `CostedReduction` package over `atomicSessionOps` at `ℓ < 10 ^ 6` matching
`LibsignalSim.redKemFailHiddenSaltClamp` at `(L, qep, B)`. -/
structure KemFailAtomicClampBundle (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep B q : ℕ) where
  realRed :
    CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt)
      .unit .unit .bool (.prod BV512 BV256)
  queries_zero : ∀ w, realRed.totalQueries w (fun _ => 0) q = 0
  init_cost : realRed.init.cost ≤ 50000000
  finish_cost : realRed.finish.cost ≤ 50000000 + 2048 * q
  handle_cost :
    realRed.handle.cost + 16 ≤
      200000000 + 100000000 * q + 4096 * (q * q) + 4096 * bits (qep + 1)
  parts_desc :
    atomicTyDescBits realRed.σ +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim realRed.init +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim realRed.handle +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim realRed.finish ≤
    2 ^ 22 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  eval_clamp :
    ∀ A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes,
      MakesAtMostQueries A q →
      (((realRed.eval (fun _ => A) ()).map fun (seed, rand) =>
        (⟨coinBytes seed, coinBytes_length seed⟩, keyToBytesVec32 rand))) =
      redKemFailHiddenSaltClamp (paramsV1 C K idA idB) Dh encPt encT decT lam K id L qep B A

def KemFailAtomicClampBundle.ofOracleStepRel
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {L qep B q : ℕ}
    (σ : Ty (atomicSig ℓ Pt))
    (mkInitE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [BV256, BV256, BV256, .bool, .unit] σ)
    (stepC : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (coinOnlyIface ℓ Pt)
      [σ, (e2eSessionCodec ℓ Pt).Q] (.prod (e2eSessionCodec ℓ Pt).R σ))
    (finishOptE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [σ, .bool] (.opt (.prod BV512 BV256)))
    (hStepQueries : ∀ w, stepC.queries w (fun _ => 0) = 0)
    (hInitCost : mkInitE.cost + 40 ≤ 50000000)
    (hFinCost : finishOptE.cost + 13 ≤ 50000000 + 2048 * q)
    (hStepCost :
      stepC.cost + 16 ≤ 200000000 + 100000000 * q + 4096 * (q * q) + 4096 * bits (qep + 1))
    (hDesc :
      atomicTyDescBits σ +
        atomicExprDescBits atomicSessionOpDescBits mkInitE +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim stepC +
        atomicExprDescBits atomicSessionOpDescBits finishOptE + 1050 ≤
      2 ^ 22 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (Rel : ℕ →
      (LibsignalToModularSchemeSimState Bytes Pt ℓ × KemExtraRaw Bytes (BitVec 512) Pt ℓ) →
      σ.denote → Prop)
    (hInitRel : ∀ b k1 k2 pqrKey,
      Rel q
        (kemFailClampInitState (paramsV1 C K idA idB) Dh encPt encT decT lam K b k1 k2 pqrKey)
        (mkInitE.eval (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil)))))))
    (hStepRel : ∀ m t s₁ s₂, Rel (m + 1) s₁ s₂ →
      ∃ c : OracleComp unifSpec
        ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range t ×
          (LibsignalToModularSchemeSimState Bytes Pt ℓ × KemExtraRaw Bytes (BitVec 512) Pt ℓ) ×
          σ.denote),
        ((fun r => (r.1, r.2.1)) <$> c) =
          (kemFailOracle (paramsV1 C K idA idB) Dh encPt encT decT lam K id L qep B (.inr t)).run s₁ ∧
        ((fun r => (r.1, r.2.2)) <$> c) =
          (handlerImpl (C := e2eSessionCodec ℓ Pt) stepC (.inr t)).run s₂ ∧
        ∀ r ∈ support c, Rel m r.2.1 r.2.2)
    (hFinRel : ∀ s₁ s₂ b, Rel 0 s₁ s₂ →
      kemCandBvToVec ((finishOptE.eval (.cons s₂ (.cons b .nil))).getD (0#512, 0#256)) = s₁.2.2.2)
    (hMono : ∀ {m n} {s₁ s₂}, m ≤ n → Rel n s₁ s₂ → Rel m s₁ s₂) :
    KemFailAtomicClampBundle Pt ℓ C K idA idB Dh encPt encT decT lam L qep B q :=
  let R : CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool (.prod BV512 BV256) :=
    { σ := σ
      init := kemFailInitCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) mkInitE
      handle := stepC
      finish := .ret (kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finishOptE) }
  { realRed := R
    queries_zero := fun w => by
      simp [R, CostedReduction.totalQueries, kemFailInitCoinsC_queries_zero,
        hStepQueries, Comp.queries]
    init_cost := (kemFailInitCoinsC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mkInitE).trans hInitCost
    finish_cost := by
      have hc := cost_kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finishOptE
      dsimp only [R, Comp.cost]
      omega
    handle_cost := hStepCost
    parts_desc := by
      have hi := kemFailInitCoinsC_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) mkInitE
      have hf := kemCandOptGetDE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) finishOptE
      change atomicTyDescBits σ +
          atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
            (kemFailInitCoinsC mkInitE) +
          atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim stepC +
          (atomicExprDescBits atomicSessionOpDescBits (kemCandOptGetDE finishOptE) + 6) ≤ _
      omega
    eval_clamp := fun A hq => by
      have hb := isQueryBoundP_of_makesAtMostQueries hq
      let P := paramsV1 C K idA idB
      let initImpl : Unit → OracleComp unifSpec
          (Unit × (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
            KemExtraRaw Bytes (BitVec 512) Pt ℓ)) := fun _ => do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        return ((), kemFailClampInitState P Dh encPt encT decT lam K b k1 k2 pqrKey)
      let c₀ : OracleComp unifSpec
          (Unit × (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
            KemExtraRaw Bytes (BitVec 512) Pt ℓ) × σ.denote) := do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        return ((),
          kemFailClampInitState P Dh encPt encT decT lam K b k1 k2 pqrKey,
          mkInitE.eval (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil))))))
      have hinit :
          ((fun r => (r.1, r.2.1)) <$> c₀) = initImpl () ∧
          ((fun r => (r.1, r.2.2)) <$> c₀) = R.init.eval (.cons () .nil) ∧
          ∀ r ∈ support c₀, Rel q r.2.1 r.2.2 := by
        refine ⟨?_, ?_, ?_⟩
        · dsimp only [c₀, initImpl]
          simp only [map_bind, map_pure]
        · dsimp only [R]
          rw [kemFailInitCoinsC_eval]
          dsimp only [c₀]
          simp only [map_bind, map_pure]
        · rintro ⟨_, s₁, s₂⟩ hr
          dsimp only [c₀] at hr
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hr
          obtain ⟨b, -, k1, -, k2, -, pqrKey, -, _, rfl, rfl⟩ := hr
          exact hInitRel b k1 k2 pqrKey
      have heval := eval_map_eq_simulateQ_of_rel R kemCandBvToVec Rel initImpl
        (kemFailOracle P Dh encPt encT decT lam K id L qep B)
        (fun s₁ _ => pure s₁.2.2.2)
        q () ⟨c₀, hinit⟩
        (fun _ _ => rfl)
        hStepRel
        (fun s₁ s₂ b' h0 => by
          dsimp only [R]
          rw [SessionProgCommon.comp_eval_ret, eval_kemCandOptGetDE, map_pure, hFinRel s₁ s₂ b' h0])
        hMono (fun _ => A) (fun _ => hb)
      change (kemCandBvToVec <$> R.eval (fun _ => A) ()) = _
      rw [heval]
      dsimp only [initImpl, P]
      unfold redKemFailHiddenSaltClamp kemFailClampInitState
      dsimp only []
      simp only [bind_assoc, pure_bind] }

def KemFailAtomicClampBundle.ofOracleStepAbs
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {L qep B q : ℕ}
    (σ : Ty (atomicSig ℓ Pt))
    (mkInitE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [BV256, BV256, BV256, .bool, .unit] σ)
    (stepC : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (coinOnlyIface ℓ Pt)
      [σ, (e2eSessionCodec ℓ Pt).Q] (.prod (e2eSessionCodec ℓ Pt).R σ))
    (finishOptE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [σ, .bool] (.opt (.prod BV512 BV256)))
    (hStepQueries : ∀ w, stepC.queries w (fun _ => 0) = 0)
    (hInitCost : mkInitE.cost + 40 ≤ 50000000)
    (hFinCost : finishOptE.cost + 13 ≤ 50000000 + 2048 * q)
    (hStepCost :
      stepC.cost + 16 ≤ 200000000 + 100000000 * q + 4096 * (q * q) + 4096 * bits (qep + 1))
    (hDesc :
      atomicTyDescBits σ +
        atomicExprDescBits atomicSessionOpDescBits mkInitE +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim stepC +
        atomicExprDescBits atomicSessionOpDescBits finishOptE + 1050 ≤
      2 ^ 22 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (abs : σ.denote →
      LibsignalToModularSchemeSimState Bytes Pt ℓ × KemExtraRaw Bytes (BitVec 512) Pt ℓ)
    (Inv : ℕ → σ.denote → Prop)
    (so : QueryImpl
      (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
        KemExtraRaw Bytes (BitVec 512) Pt ℓ) (OracleComp unifSpec)))
    (hU : ∀ n s, (so (.inl n)).run s = (StateT.lift ((coinOnlyIface ℓ Pt).fwdU n)).run s)
    (hInitAbs : ∀ b k1 k2 pqrKey,
      abs (mkInitE.eval (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil)))))) =
        kemFailClampInitState (paramsV1 C K idA idB) Dh encPt encT decT lam K b k1 k2 pqrKey)
    (hInitInv : ∀ b k1 k2 pqrKey,
      Inv q (mkInitE.eval (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil)))))))
    (hStepAbs : ∀ m t s, Inv (m + 1) s →
      (Prod.map id abs <$>
        ((handlerImpl (C := e2eSessionCodec ℓ Pt) stepC (.inr t)).run s)) =
        (so (.inr t)).run (abs s) ∧
      ∀ r ∈ support ((handlerImpl (C := e2eSessionCodec ℓ Pt) stepC (.inr t)).run s), Inv m r.2)
    (hFinAbs : ∀ s b, Inv 0 s →
      kemCandBvToVec ((finishOptE.eval (.cons s (.cons b .nil))).getD (0#512, 0#256)) =
        (abs s).2.2.2)
    (hMono : ∀ {m n} (s), m ≤ n → Inv n s → Inv m s)
    (hSoEq : ∀ (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) st,
      ((simulateQ so A).run st >>= fun x => pure x.2.2.2.2) =
      ((simulateQ (kemFailOracle (paramsV1 C K idA idB) Dh encPt encT decT lam K id L qep B) A).run st >>=
        fun x => pure x.2.2.2.2)) :
    KemFailAtomicClampBundle Pt ℓ C K idA idB Dh encPt encT decT lam L qep B q :=
  let R : CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool (.prod BV512 BV256) :=
    { σ := σ
      init := kemFailInitCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) mkInitE
      handle := stepC
      finish := .ret (kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finishOptE) }
  { realRed := R
    queries_zero := fun w => by
      simp [R, CostedReduction.totalQueries, kemFailInitCoinsC_queries_zero,
        hStepQueries, Comp.queries]
    init_cost := (kemFailInitCoinsC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mkInitE).trans hInitCost
    finish_cost := by
      have hc := cost_kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finishOptE
      dsimp only [R, Comp.cost]
      omega
    handle_cost := hStepCost
    parts_desc := by
      have hi := kemFailInitCoinsC_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) mkInitE
      have hf := kemCandOptGetDE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) finishOptE
      change atomicTyDescBits σ +
          atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
            (kemFailInitCoinsC mkInitE) +
          atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim stepC +
          (atomicExprDescBits atomicSessionOpDescBits (kemCandOptGetDE finishOptE) + 6) ≤ _
      omega
    eval_clamp := fun A hq => by
      have hb := isQueryBoundP_of_makesAtMostQueries hq
      let P := paramsV1 C K idA idB
      let initImpl : Unit → OracleComp unifSpec
          (Unit × (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
            KemExtraRaw Bytes (BitVec 512) Pt ℓ)) := fun _ => do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        return ((), kemFailClampInitState P Dh encPt encT decT lam K b k1 k2 pqrKey)
      have hinit : (Prod.map id abs <$> R.init.eval (.cons () .nil)) = initImpl () := by
        dsimp only [R, initImpl, P]
        rw [kemFailInitCoinsC_eval]
        simp only [map_bind, map_pure, Prod.map, id_eq, hInitAbs]
      have hinitInv : ∀ r ∈ support (R.init.eval (.cons () .nil)), Inv q r.2 := by
        rintro ⟨_, s₀⟩ hr
        dsimp only [R] at hr
        rw [kemFailInitCoinsC_eval] at hr
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hr
        obtain ⟨b, -, k1, -, k2, -, pqrKey, -, _, rfl⟩ := hr
        exact hInitInv b k1 k2 pqrKey
      have heval := eval_map_eq_simulateQ_of_abs R kemCandBvToVec abs Inv initImpl so
        (fun s _ => pure (kemCandVecToBv s.2.2.2)) q ()
        hinit hinitInv hU hStepAbs
        (fun s b' h0 => by
          dsimp only [R]
          rw [SessionProgCommon.comp_eval_ret, eval_kemCandOptGetDE, ← hFinAbs s b' h0,
            kemCandVecToBv_kemCandBvToVec])
        hMono (fun _ => A) (fun _ => hb)
      change (kemCandBvToVec <$> R.eval (fun _ => A) ()) = _
      rw [heval]
      dsimp only [initImpl, P]
      unfold redKemFailHiddenSaltClamp kemFailClampInitState
      dsimp only []
      simp only [bind_assoc, pure_bind, map_pure, kemCandBvToVec_kemCandVecToBv]
      refine bind_congr fun b => bind_congr fun k1 => bind_congr fun k2 =>
        bind_congr fun pqrKey => ?_
      exact hSoEq A _ }

def KemFailAtomicClampBundle.ofOracleStepEnc
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {L qep B q : ℕ}
    (σ : Ty (atomicSig ℓ Pt))
    (mkInitE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [BV256, BV256, BV256, .bool, .unit] σ)
    (stepC : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (coinOnlyIface ℓ Pt)
      [σ, (e2eSessionCodec ℓ Pt).Q] (.prod (e2eSessionCodec ℓ Pt).R σ))
    (finishOptE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [σ, .bool] (.opt (.prod BV512 BV256)))
    (hStepQueries : ∀ w, stepC.queries w (fun _ => 0) = 0)
    (hInitCost : mkInitE.cost + 40 ≤ 50000000)
    (hFinCost : finishOptE.cost + 13 ≤ 50000000 + 2048 * q)
    (hStepCost :
      stepC.cost + 16 ≤ 200000000 + 100000000 * q + 4096 * (q * q) + 4096 * bits (qep + 1))
    (hDesc :
      atomicTyDescBits σ +
        atomicExprDescBits atomicSessionOpDescBits mkInitE +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim stepC +
        atomicExprDescBits atomicSessionOpDescBits finishOptE + 1050 ≤
      2 ^ 22 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (enc : (LibsignalToModularSchemeSimState Bytes Pt ℓ × KemExtraRaw Bytes (BitVec 512) Pt ℓ) →
      σ.denote)
    (Inv : ℕ →
      (LibsignalToModularSchemeSimState Bytes Pt ℓ × KemExtraRaw Bytes (BitVec 512) Pt ℓ) → Prop)
    (so : QueryImpl
      (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
        KemExtraRaw Bytes (BitVec 512) Pt ℓ) (OracleComp unifSpec)))
    (hU : ∀ n s, (so (.inl n)).run s = (StateT.lift ((coinOnlyIface ℓ Pt).fwdU n)).run s)
    (hInitEnc : ∀ b k1 k2 pqrKey,
      mkInitE.eval (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil))))) =
        enc (kemFailClampInitState (paramsV1 C K idA idB) Dh encPt encT decT lam K b k1 k2 pqrKey))
    (hInitInv : ∀ b k1 k2 pqrKey,
      Inv q (kemFailClampInitState (paramsV1 C K idA idB) Dh encPt encT decT lam K b k1 k2 pqrKey))
    (hStepEnc : ∀ m t s, Inv (m + 1) s →
      (handlerImpl (C := e2eSessionCodec ℓ Pt) stepC (.inr t)).run (enc s) =
        Prod.map id enc <$> (so (.inr t)).run s ∧
      ∀ r ∈ support ((so (.inr t)).run s), Inv m r.2)
    (hFinEnc : ∀ s b, Inv 0 s →
      kemCandBvToVec ((finishOptE.eval (.cons (enc s) (.cons b .nil))).getD (0#512, 0#256)) =
        s.2.2.2)
    (hMono : ∀ {m n} (s), m ≤ n → Inv n s → Inv m s)
    (hSoEq : ∀ (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) st,
      ((simulateQ so A).run st >>= fun x => pure x.2.2.2.2) =
      ((simulateQ (kemFailOracle (paramsV1 C K idA idB) Dh encPt encT decT lam K id L qep B) A).run st >>=
        fun x => pure x.2.2.2.2)) :
    KemFailAtomicClampBundle Pt ℓ C K idA idB Dh encPt encT decT lam L qep B q :=
  let R : CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool (.prod BV512 BV256) :=
    { σ := σ
      init := kemFailInitCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) mkInitE
      handle := stepC
      finish := .ret (kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finishOptE) }
  { realRed := R
    queries_zero := fun w => by
      simp [R, CostedReduction.totalQueries, kemFailInitCoinsC_queries_zero,
        hStepQueries, Comp.queries]
    init_cost := (kemFailInitCoinsC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mkInitE).trans hInitCost
    finish_cost := by
      have hc := cost_kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finishOptE
      dsimp only [R, Comp.cost]
      omega
    handle_cost := hStepCost
    parts_desc := by
      have hi := kemFailInitCoinsC_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) mkInitE
      have hf := kemCandOptGetDE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) finishOptE
      change atomicTyDescBits σ +
          atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
            (kemFailInitCoinsC mkInitE) +
          atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim stepC +
          (atomicExprDescBits atomicSessionOpDescBits (kemCandOptGetDE finishOptE) + 6) ≤ _
      omega
    eval_clamp := fun A hq => by
      have hb := isQueryBoundP_of_makesAtMostQueries hq
      let P := paramsV1 C K idA idB
      let initImpl : Unit → OracleComp unifSpec
          (Unit × (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
            KemExtraRaw Bytes (BitVec 512) Pt ℓ)) := fun _ => do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        return ((), kemFailClampInitState P Dh encPt encT decT lam K b k1 k2 pqrKey)
      have hinit : R.init.eval (.cons () .nil) = Prod.map id enc <$> initImpl () := by
        dsimp only [R, initImpl, P]
        rw [kemFailInitCoinsC_eval]
        simp only [map_bind, map_pure, Prod.map, id_eq, hInitEnc]
      have hinitInv : ∀ r ∈ support (initImpl ()), Inv q r.2 := by
        rintro ⟨_, s₀⟩ hr
        dsimp only [initImpl] at hr
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hr
        obtain ⟨b, -, k1, -, k2, -, pqrKey, -, _, rfl⟩ := hr
        exact hInitInv b k1 k2 pqrKey
      have heval := eval_map_eq_simulateQ_of_enc R kemCandBvToVec enc Inv initImpl so
        (fun s _ => pure (kemCandVecToBv s.2.2.2)) q ()
        hinit hinitInv hU hStepEnc
        (fun s b' h0 => by
          dsimp only [R]
          rw [SessionProgCommon.comp_eval_ret, eval_kemCandOptGetDE, ← hFinEnc s b' h0,
            kemCandVecToBv_kemCandBvToVec])
        hMono (fun _ => A) (fun _ => hb)
      change (kemCandBvToVec <$> R.eval (fun _ => A) ()) = _
      rw [heval]
      dsimp only [initImpl, P]
      unfold redKemFailHiddenSaltClamp kemFailClampInitState
      dsimp only []
      simp only [bind_assoc, pure_bind, map_pure, kemCandBvToVec_kemCandVecToBv]
      refine bind_congr fun b => bind_congr fun k1 => bind_congr fun k2 =>
        bind_congr fun pqrKey => ?_
      exact hSoEq A _ }

/-- Real-branch `CostedReduction` package over `atomicSessionOps` at `ℓ < 10 ^ 6` targeting
`Refinement.redKemFailHiddenSalt` up to `=ᵈ` (`q + 3 ≤ 2 ^ 32`). -/
structure KemFailAtomicRealBundle (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) where
  realRed :
    CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt)
      .unit .unit .bool (.prod BV512 BV256)
  queries_zero : ∀ w, realRed.totalQueries w (fun _ => 0) q = 0
  init_cost : realRed.init.cost ≤ 50000000
  finish_cost : realRed.finish.cost ≤ 50000000 + 2048 * q
  handle_cost :
    realRed.handle.cost + 16 ≤
      200000000 + 100000000 * q + 4096 * (q * q) + 4096 * bits (qep + 1)
  parts_desc :
    atomicTyDescBits realRed.σ +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim realRed.init +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim realRed.handle +
      atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim realRed.finish ≤
    2 ^ 22 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1))
  eval_dist :
    ∀ A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes,
      MakesAtMostQueries A q →
      q + 3 ≤ 2 ^ 32 →
      (((realRed.eval (fun _ => A) ()).map fun (seed, rand) =>
        (⟨coinBytes seed, coinBytes_length seed⟩, keyToBytesVec32 rand))) =ᵈ
      redKemFailHiddenSalt (paramsV1 C K idA idB) K ℓ Dh encPt encT decT (idsOf idA idB) lam qep A

def KemFailAtomicClampBundle.toRealBundle
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {L qep B q : ℕ} (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B)
    (cb : KemFailAtomicClampBundle Pt ℓ C K idA idB Dh encPt encT decT lam L qep B q) :
    KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q where
  realRed := cb.realRed
  queries_zero := cb.queries_zero
  init_cost := cb.init_cost
  finish_cost := cb.finish_cost
  handle_cost := cb.handle_cost
  parts_desc := cb.parts_desc
  eval_dist := fun A hq hq32 => by
    rw [cb.eval_clamp A hq]
    have hid : idsOf idA idB =
        fun R => if R == Party.A then (paramsV1 C K idA idB).idA else (paramsV1 C K idA idB).idB := by
      funext R; cases R <;> rfl
    exact redKemFailHiddenSaltClamp_evalDistEq (paramsV1 C K idA idB) Dh encPt encT decT lam K
      id rfl (idsOf idA idB) hid L qep B h232 A q hq (hq32.trans h232) hqL

def KemFailAtomicRealBundle.ofSimImplRel
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {qep q : ℕ}
    (σ : Ty (atomicSig ℓ Pt))
    (mkInitE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [BV256, BV256, BV256, .bool, .unit] σ)
    (stepC : Comp (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) (coinOnlyIface ℓ Pt)
      [σ, (e2eSessionCodec ℓ Pt).Q] (.prod (e2eSessionCodec ℓ Pt).R σ))
    (finishOptE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      [σ, .bool] (.opt (.prod BV512 BV256)))
    (hStepQueries : ∀ w, stepC.queries w (fun _ => 0) = 0)
    (hInitCost : mkInitE.cost + 40 ≤ 50000000)
    (hFinCost : finishOptE.cost + 13 ≤ 50000000 + 2048 * q)
    (hStepCost :
      stepC.cost + 16 ≤ 200000000 + 100000000 * q + 4096 * (q * q) + 4096 * bits (qep + 1))
    (hDesc :
      atomicTyDescBits σ +
        atomicExprDescBits atomicSessionOpDescBits mkInitE +
        atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim stepC +
        atomicExprDescBits atomicSessionOpDescBits finishOptE + 1050 ≤
      2 ^ 22 + 2 ^ 13 * bits (ratchetCostBudget q (qep + 1) + (qep + 1)))
    (Rel : ℕ →
      (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
        (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
        KemFailTrackState (paramsV1 C K idA idB).C.F) →
      σ.denote → Prop)
    (hInitRel : q + 3 ≤ 2 ^ 32 → ∀ b k1 k2 pqrKey,
      Rel q
        (kemFailSimInitState (paramsV1 C K idA idB) Dh encPt encT (idsOf idA idB) lam b k1 k2 pqrKey)
        (mkInitE.eval (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil)))))))
    (hStepRel : q + 3 ≤ 2 ^ 32 → ∀ m t s₁ s₂, Rel (m + 1) s₁ s₂ →
      ∃ c : OracleComp unifSpec
        ((CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range t ×
          (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
            (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
            KemFailTrackState (paramsV1 C K idA idB).C.F) ×
          σ.denote),
        ((fun r => (r.1, r.2.1)) <$> c) =
          (kemFailSimImpl (paramsV1 C K idA idB) K ℓ Dh encPt encT decT (idsOf idA idB) lam qep
            (.inr t)).run s₁ ∧
        ((fun r => (r.1, r.2.2)) <$> c) =
          (handlerImpl (C := e2eSessionCodec ℓ Pt) stepC (.inr t)).run s₂ ∧
        ∀ r ∈ support c, Rel m r.2.1 r.2.2)
    (hFinRel : ∀ s₁ s₂ b, Rel 0 s₁ s₂ →
      kemCandBvToVec ((finishOptE.eval (.cons s₂ (.cons b .nil))).getD (0#512, 0#256)) =
        s₁.2.2.cand.getD simDefaultKemCand)
    (hMono : ∀ {m n} {s₁ s₂}, m ≤ n → Rel n s₁ s₂ → Rel m s₁ s₂) :
    KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q :=
  let R : CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) .unit .unit .bool (.prod BV512 BV256) :=
    { σ := σ
      init := kemFailInitCoinsC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) mkInitE
      handle := stepC
      finish := .ret (kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finishOptE) }
  { realRed := R
    queries_zero := fun w => by
      simp [R, CostedReduction.totalQueries, kemFailInitCoinsC_queries_zero,
        hStepQueries, Comp.queries]
    init_cost := (kemFailInitCoinsC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mkInitE).trans hInitCost
    finish_cost := by
      have hc := cost_kemCandOptGetDE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finishOptE
      dsimp only [R, Comp.cost]
      omega
    handle_cost := hStepCost
    parts_desc := by
      have hi := kemFailInitCoinsC_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) mkInitE
      have hf := kemCandOptGetDE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) finishOptE
      change atomicTyDescBits σ +
          atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim
            (kemFailInitCoinsC mkInitE) +
          atomicCompDescBits atomicSessionOpDescBits (fun _ => 8) Empty.elim stepC +
          (atomicExprDescBits atomicSessionOpDescBits (kemCandOptGetDE finishOptE) + 6) ≤ _
      omega
    eval_dist := fun A hq hq32 => by
      have hb := isQueryBoundP_of_makesAtMostQueries hq
      let P := paramsV1 C K idA idB
      let initImpl : Unit → OracleComp unifSpec
          (Unit × (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
            (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
            KemFailTrackState P.C.F)) := fun _ => do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        return ((), kemFailSimInitState P Dh encPt encT (idsOf idA idB) lam b k1 k2 pqrKey)
      let c₀ : OracleComp unifSpec
          (Unit × (LibsignalToModularSchemeSimState Bytes Pt ℓ ×
            (GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) ×
            KemFailTrackState P.C.F) × σ.denote) := do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let k1 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let k2 ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        let pqrKey ← ($ᵗ (BitVec 256) : ProbComp (BitVec 256))
        return ((),
          kemFailSimInitState P Dh encPt encT (idsOf idA idB) lam b k1 k2 pqrKey,
          mkInitE.eval (.cons pqrKey (.cons k2 (.cons k1 (.cons b (.cons () .nil))))))
      have hinit :
          ((fun r => (r.1, r.2.1)) <$> c₀) = initImpl () ∧
          ((fun r => (r.1, r.2.2)) <$> c₀) = R.init.eval (.cons () .nil) ∧
          ∀ r ∈ support c₀, Rel q r.2.1 r.2.2 := by
        refine ⟨?_, ?_, ?_⟩
        · dsimp only [c₀, initImpl]; simp only [map_bind, map_pure]
        · dsimp only [R]; rw [kemFailInitCoinsC_eval]; dsimp only [c₀]; simp only [map_bind, map_pure]
        · rintro ⟨_, s₁, s₂⟩ hr
          dsimp only [c₀] at hr
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hr
          obtain ⟨b, -, k1, -, k2, -, pqrKey, -, _, rfl, rfl⟩ := hr
          exact hInitRel hq32 b k1 k2 pqrKey
      have heval := eval_map_eq_simulateQ_of_rel R kemCandBvToVec Rel initImpl
        (kemFailSimImpl P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep)
        (fun s₁ _ => pure (s₁.2.2.cand.getD simDefaultKemCand))
        q () ⟨c₀, hinit⟩
        (fun _ _ => rfl)
        (hStepRel hq32)
        (fun s₁ s₂ b' h0 => by
          dsimp only [R]
          rw [SessionProgCommon.comp_eval_ret, eval_kemCandOptGetDE, map_pure, hFinRel s₁ s₂ b' h0])
        hMono (fun _ => A) (fun _ => hb)
      have heq : (((R.eval (fun _ => A) ()).map fun (seed, rand) =>
          (⟨coinBytes seed, coinBytes_length seed⟩, keyToBytesVec32 rand))) =
          redKemFailHiddenSalt P K ℓ Dh encPt encT decT (idsOf idA idB) lam qep A := by
        change (kemCandBvToVec <$> R.eval (fun _ => A) ()) = _
        rw [heval, redKemFailHiddenSalt_eq_splitCoins]
        dsimp only [initImpl]
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun b => bind_congr fun k1 => bind_congr fun k2 =>
          bind_congr fun pqrKey => bind_congr fun ⟨_, _, _, _⟩ => rfl
      rw [heq] }

/-- Promoted `SessionCostedReductions.kemFailRed` witness over `atomicSessionOps` and
`coinOnlyIface ℓ Pt`, guarded by `ℓ < 10 ^ 6` with fallback `dummyPairSessionRed`. -/
def kemFailRedProg {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q) :
    CostedReduction
      (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt)
      .unit .unit .bool (.prod BV512 BV256) :=
  if hℓ : ℓ < 10 ^ 6 then (mkReal hℓ).realRed
  else dummyPairSessionRed (coinOnlyIface ℓ Pt) .unit

theorem kemFailRedProg_totalQueries_zero {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q)
    (w : Empty → ℕ) :
    (kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q mkReal).totalQueries
      w (fun _ => 0) q = 0 := by
  unfold kemFailRedProg
  split_ifs with hℓ
  · exact (mkReal hℓ).queries_zero w
  · exact dummyPairSessionRed_totalQueries (coinOnlyIface ℓ Pt) .unit w (fun _ => 0) q

theorem kemFailRedProg_totalCost_le_tight {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q) :
    (kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q mkReal).totalCost q ≤
      ratchetCostBudgetTight q (qep + 1) + 2 ^ 12 * (q + 1) ^ 2 * q := by
  unfold kemFailRedProg
  split_ifs with hℓ
  · let rb := mkReal hℓ
    have htot : rb.realRed.totalCost q =
        rb.realRed.init.cost + q * (rb.realRed.handle.cost + 16) + rb.realRed.finish.cost := by
      simp only [CostedReduction.totalCost, e2eSessionCodec, coinOnlyIface]
      rw [Nat.max_eq_right (by omega)]
    rw [htot]
    have hstep := Nat.mul_le_mul_left q rb.handle_cost
    have hsum :
        rb.realRed.init.cost + q * (rb.realRed.handle.cost + 16) + rb.realRed.finish.cost ≤
        (rb.realRed.init.cost +
          q * (200000000 + 100000000 * q + 4096 * bits (qep + 1)) +
          rb.realRed.finish.cost) + q * (4096 * (q * q)) := by
      have hd : q * (200000000 + 100000000 * q + 4096 * (q * q) + 4096 * bits (qep + 1)) =
          q * (200000000 + 100000000 * q + 4096 * bits (qep + 1)) + q * (4096 * (q * q)) := by ring
      omega
    have hlin := session_cost_le_ratchetCostBudgetTight q (qep + 1)
      rb.realRed.init.cost rb.realRed.finish.cost 200000000 100000000 4096
      rb.init_cost rb.finish_cost le_rfl le_rfl le_rfl
    have hcub : q * (4096 * (q * q)) ≤ 2 ^ 12 * (q + 1) ^ 2 * q := by nlinarith
    exact hsum.trans (Nat.add_le_add hlin hcub)
  · have hb :
        (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).cost
          (Sum.inl (Sum.inl (Sum.inl (Sum.inl (AtomicPureOp.bv512Lit 0#512))))) = 3 := rfl
    have hc :
        (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam).cost
          (Sum.inl (Sum.inl (Sum.inl (Sum.inl (AtomicPureOp.bv256Lit 0#256))))) = 2 := rfl
    have hcost :
        (dummyPairSessionRed (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam)
          (coinOnlyIface ℓ Pt) .unit).totalCost q ≤ 32 + q * 24 := by
      simp [dummyPairSessionRed, CostedReduction.totalCost, e2eSessionCodec, coinOnlyIface,
        Comp.cost, Expr.cost, hb, hc]
      omega
    refine hcost.trans ((?_ : 32 + q * 24 ≤ ratchetCostBudgetTight q (qep + 1)).trans
      (Nat.le_add_right _ _))
    simpa using session_cost_le_ratchetCostBudgetTight q (qep + 1) 32 0 24 0 0
      (by omega) (by omega) (by omega) (by omega) (by omega)

theorem kemFailRedProg_totalCost_le {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q) :
    (kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q mkReal).totalCost q ≤
      ratchetCostBudget q (qep + 1) + 2 ^ 12 * (q + 1) ^ 2 * q :=
  (kemFailRedProg_totalCost_le_tight ℓ C K idA idB Dh encPt encT decT lam qep q mkReal).trans
    (Nat.add_le_add_right (ratchetCostBudgetTight_le_ratchetCostBudget q (qep + 1)) _)

theorem kemFailRedProg_descBits_le {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q) :
    atomicRedDescBits (kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q mkReal) ≤
      ratchetDescBudget q (qep + 1) := by
  unfold kemFailRedProg
  split_ifs with hℓ
  · exact kemFailRed_descBits_le_of_parts (mkReal hℓ).realRed q (qep + 1) (mkReal hℓ).parts_desc
  · exact dummyPairSessionRed_descBits_le (by dsimp [atomicTyDescBits]; omega) q (qep + 1)

theorem kemFailRedProg_size_le {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q)
    (hB : ratchetCostBudget q (qep + 1) + (qep + 1) < 2 ^ 126) :
    (kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q mkReal).size ≤
      reductionSizeBudget :=
  (red_size_le_atomicRedDescBits _).trans
    ((kemFailRedProg_descBits_le ℓ C K idA idB Dh encPt encT decT lam qep q mkReal).trans
      (ratchetDescBudget_le_reductionSizeBudget hB))

theorem kemFailRedProg_gRedBounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q)
    (hB : ratchetCostBudget q (qep + 1) + (qep + 1) < 2 ^ 126) :
    GRedBounded
      (kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q mkReal)
      Empty.elim (fun _ => 0) q 0
      (ratchetCostBudget q (qep + 1) + 2 ^ 12 * (q + 1) ^ 2 * q) :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0
    (ratchetCostBudget q (qep + 1) + 2 ^ 12 * (q + 1) ^ 2 * q)
    (kemFailRedProg_totalCost_le ℓ C K idA idB Dh encPt encT decT lam qep q mkReal)
    ((kemFailRedProg_size_le ℓ C K idA idB Dh encPt encT decT lam qep q mkReal hB).trans
      (Nat.le_add_right _ _))
    (Nat.le_of_eq (kemFailRedProg_totalQueries_zero ℓ C K idA idB Dh encPt encT decT lam
      qep q mkReal Empty.elim))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem kemFailRedProg_eval {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (L qep B q : ℕ) (hqL : q ≤ L) (h232 : 2 ^ 32 ≤ B)
    (mkClamp : ℓ < 10 ^ 6 →
      KemFailAtomicClampBundle Pt ℓ C K idA idB Dh encPt encT decT lam L qep B q)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) :
    (((kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q
        (fun h => (mkClamp h).toRealBundle hqL h232)).eval (fun _ => A) ()).map
      fun (seed, rand) => (⟨coinBytes seed, coinBytes_length seed⟩, keyToBytesVec32 rand)) =
    redKemFailHiddenSaltClamp (paramsV1 C K idA idB) Dh encPt encT decT lam K id L qep B A := by
  unfold kemFailRedProg
  simp only [hℓ, ↓reduceDIte]
  exact (mkClamp hℓ).eval_clamp A hq

end KemFailRedAssembly

/-! ## Advantage bridges -/

section CallSiteBridges

theorem kemFailRedProg_evalDistEq {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) (hqB : q + 3 ≤ 2 ^ 32) :
    (((kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q mkReal).eval (fun _ => A) ()).map
      fun (seed, rand) => (⟨coinBytes seed, coinBytes_length seed⟩, keyToBytesVec32 rand)) =ᵈ
    redKemFailHiddenSalt (paramsV1 C K idA idB) K ℓ Dh encPt encT decT (idsOf idA idB) lam qep A := by
  unfold kemFailRedProg
  simp only [hℓ, ↓reduceDIte]
  exact (mkReal hℓ).eval_dist A hq hqB

/-- `K.kemFailFindAdvantage` equality between `kemFailRedProg` and `redKemFailHiddenSalt`. -/
theorem kemFailRedProg_advantage_eq {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) (hqB : q + 3 ≤ 2 ^ 32) :
    K.kemFailFindAdvantage
      (((kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q mkReal).eval (fun _ => A) ()).map
        fun (seed, rand) => (⟨coinBytes seed, coinBytes_length seed⟩, keyToBytesVec32 rand)) =
    K.kemFailFindAdvantage
      (redKemFailHiddenSalt (paramsV1 C K idA idB) K ℓ Dh encPt encT decT
        (idsOf idA idB) lam qep A) := by
  unfold MlKem.kemFailFindAdvantage MlKem.kemFailFindGame
  congr 1
  exact ((kemFailRedProg_evalDistEq hℓ C K idA idB Dh encPt encT decT lam qep q mkReal
    A hq hqB).bind fun _ => EvalDistEq.rfl).evalDist_eq

theorem kemFailRedProg_advantage_eq_of_hq32 {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
    (mkReal : ℓ < 10 ^ 6 →
      KemFailAtomicRealBundle Pt ℓ C K idA idB Dh encPt encT decT lam qep q)
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hq : MakesAtMostQueries A q) :
    K.kemFailFindAdvantage
      (((kemFailRedProg ℓ C K idA idB Dh encPt encT decT lam qep q mkReal).eval (fun _ => A) ()).map
        fun (seed, rand) => (⟨coinBytes seed, coinBytes_length seed⟩, keyToBytesVec32 rand)) =
    K.kemFailFindAdvantage
      (redKemFailHiddenSalt (paramsV1 C K idA idB) K ℓ Dh encPt encT decT
        (idsOf idA idB) lam qep A) :=
  kemFailRedProg_advantage_eq hℓ C K idA idB Dh encPt encT decT lam qep q mkReal A hq (by omega)

end CallSiteBridges

end Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
