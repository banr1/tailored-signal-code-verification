/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKem
import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.ReductionDsl.Size

/-!
# Cost and Query Bounds for the `KeyInd` `SigEufCma` and `KemShCr` Programs

Syntactic step-cost, oracle-query, and AST-size bounds for `sigKeyIndProg` and `shcrKeyIndProg`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000

open SignalPqxdh SignalPqxdh.Security
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

/-- Polynomial step-cost budget for `KeyInd` and `Auth` reductions. -/
def stepCostBudget (S : Setup) (b : QueryBudget) : Nat :=
  2 ^ 16 * (b.q_total + 1) * (b.q_total + S.N_dh + S.N_sess_tot + 1) +
    2 ^ 11 * S.N_dh ^ 2 + 2 ^ 8 * S.N_dh * S.N_sess_tot

attribute [local simp] Expr.cost Comp.cost

@[simp] theorem bits_0 : bits 0 = 1 := by decide
@[simp] theorem bits_1 : bits 1 = 1 := by decide
@[simp] theorem bits_2 : bits 2 = 2 := by decide
@[simp] theorem bits_3 : bits 3 = 2 := by decide
@[simp] theorem bits_32 : bits 32 = 6 := by decide
@[simp] theorem bits_33 : bits 33 = 6 := by decide

theorem F_X25519_length : F_X25519.length = 32 := by decide

theorem Expr.cost_pos {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    1 ≤ e.cost := by
  induction e <;> simp [Expr.cost, bits] <;> omega

@[simp] theorem cost_v {Γ Δ : List PT} {τ : PT} (x : Var Γ τ) [Ext Γ Δ] :
    (v x : Expr pqxdhOps Δ τ).cost = 1 := rfl

@[simp] theorem cost_orE {Γ : List PT} (a b : Expr pqxdhOps Γ .bool) :
    (orE a b).cost = a.cost + b.cost + 1 := by
  have := Expr.cost_pos b
  simp [orE, Nat.max_eq_right this]

@[simp] theorem cost_mulRight {Γ : List PT} (a : Expr pqxdhOps Γ .nat) (k : ℕ) :
    (mulRight a k).cost = a.cost + bits k := rfl

@[simp] theorem cost_litB {Γ : List PT} (w : ℕ+) (bs : Bytes) :
    (litB w bs (Γ := Γ)).cost = w.val + bs.length + 1 := by
  simp [litB, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem cost_encEC {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) :
    (encEC pk).cost = pk.cost + 33 := by
  simp [encEC, consB, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem cost_encKEM {Γ : List PT} (pk : Expr pqxdhOps Γ (B 1568)) :
    (encKEM pk).cost = pk.cost + 1569 := by
  simp [encKEM, consB, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem cost_widenEC {Γ : List PT} (x : Expr pqxdhOps Γ (B 33)) :
    (widenEC x).cost = x.cost + 1569 := by
  simp [widenEC, widenB, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem cost_lenB {w : ℕ+} {Γ : List PT} (x : Expr pqxdhOps Γ (B w)) :
    (lenB x).cost = x.cost + bits w.val := by
  simp [lenB, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem cost_eqB {m n : ℕ+} {Γ : List PT}
    (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (eqB a b).cost = a.cost + b.cost + m.val + n.val + 1 := by
  simp [eqB, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem cost_u32OfNat {Γ : List PT} (n : Expr pqxdhOps Γ .nat) :
    (u32OfNat n).cost = n.cost + 1 := by
  simp [u32OfNat, pqxdhOps, Ops.sum, pqU32Ops]

@[simp] theorem cost_eqU32 {Γ : List PT} (a b : Expr pqxdhOps Γ U32) :
    (eqU32 a b).cost = a.cost + b.cost + 2 := by
  simp [eqU32, pqxdhOps, Ops.sum, pqU32Ops]

@[simp] theorem cost_sBool {Γ : List PT} : (sBool (Γ := Γ)).cost = 2 := rfl
@[simp] theorem cost_sBytes32 {Γ : List PT} : (sBytes32 (Γ := Γ)).cost = 34 := rfl
@[simp] theorem cost_sRandom64 {Γ : List PT} : (sRandom64 (Γ := Γ)).cost = 66 := rfl
@[simp] theorem cost_sDrKey96 {Γ : List PT} : (sDrKey96 (Γ := Γ)).cost = 98 := rfl
@[simp] theorem cost_sIndex (N : ℕ) {Γ : List PT} : (sIndex N (Γ := Γ)).cost = bits N + 2 := by
  simp [sIndex, Comp.cost, Expr.cost, pqPrimIface, pqSamplers, PSamp.cost]; omega

@[simp] theorem cost_qX25519 {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    (qX25519 e).cost = e.cost + 97 := rfl
@[simp] theorem cost_qX25519Base {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base e).cost = e.cost + 65 := rfl
@[simp] theorem cost_qIsCanonical {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qIsCanonical e).cost = e.cost + 33 := rfl
@[simp] theorem cost_qPow8 {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qPow8 e).cost = e.cost + 65 := rfl
@[simp] theorem cost_qSigPkGen {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qSigPkGen e).cost = e.cost + 65 := rfl
@[simp] theorem cost_qSigSign (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigSign m e).cost = e.cost + (1 + (32 + (m.val + 64)) + 64) := rfl
@[simp] theorem cost_qSigVerify (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigVerify m e).cost = e.cost + (1 + (32 + (m.val + 64)) + 0) := rfl
@[simp] theorem cost_qKemKeyGen {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).cost = e.cost + 4801 := rfl
@[simp] theorem cost_qKemEncaps {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    (qKemEncaps e).cost = e.cost + 3201 := rfl
@[simp] theorem cost_qKemDecaps {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    (qKemDecaps e).cost = e.cost + 4769 := rfl
@[simp] theorem cost_qHkdfDerive96 (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) :
    (qHkdfDerive96 w e).cost = e.cost + (1 + w.val + 96) := rfl
@[simp] theorem cost_qChalSign (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B m)) :
    (qChalSign m e).cost = e.cost + (1 + m.val + 0 + 64) := rfl

@[simp] theorem cost_liftBase {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).cost = c.cost := by
  induction c with
  | ret _ => rfl
  | bind _ _ ih1 ih2 => simp [liftBase, ih1, ih2]
  | ite _ _ _ ih1 ih2 => simp [liftBase, ih1, ih2]
  | caseOpt _ _ _ ih1 ih2 => simp [liftBase, ih1, ih2]
  | caseSum _ _ _ ih1 ih2 => simp [liftBase, ih1, ih2]
  | sample _ _ => rfl
  | query _ _ => rfl
  | iter _ _ _ ih => simp [liftBase, ih]
  | findM _ _ _ ih => simp [liftBase, ih]
  | anyM _ _ _ ih => simp [liftBase, ih]
  | mapM _ _ _ ih => simp [liftBase, ih]
  | consumeFirstM _ _ _ _ ih => simp [liftBase, ih]
  | foldM _ _ _ _ ih => simp [liftBase, ih]

@[simp] theorem buildSecretsE_cost {Γ : List PT} (dh1 dh2 dh3 : Expr pqxdhOps Γ (B 32))
    (dh4? : Expr pqxdhOps Γ (.opt (B 32))) (ss : Expr pqxdhOps Γ (B 32)) :
    (buildSecretsE dh1 dh2 dh3 dh4? ss).cost =
      dh1.cost + dh2.cost + dh3.cost + dh4?.cost + ss.cost + 737 := by
  dsimp only [buildSecretsE, eLet2, eLet, eCaseOpt, widenB, catB, litB, v, Expr.cost]
  simp only [pqxdhOps, Ops.sum, pqBytesOps, Sum.elim_inl, PNat.add_coe, PNat.val_ofNat, F_X25519_length]
  omega

@[simp] theorem sidEq_cost {Γ : List PT} (a b : Expr pqxdhOps Γ sidT) :
    (sidEq a b).cost = a.cost + b.cost + 41 := by
  simp only [sidEq, eLet2, eLet, eCaseSum, nat2Eq, nat3Eq, natEq, cost_v, Expr.cost]
  omega

@[simp] theorem optU32Eq_cost {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt U32)) :
    (optU32Eq a b).cost = a.cost + b.cost + 16 := by
  simp only [optU32Eq, eLet2, eLet, eCaseOpt, cost_eqU32, cost_v, Expr.cost]
  omega

@[simp] theorem optBytesEq_cost {w : ℕ+} {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt (B w))) :
    (optBytesEq a b).cost = a.cost + b.cost + 2 * w.val + 15 := by
  simp only [optBytesEq, eLet2, eLet, eCaseOpt, cost_eqB, cost_v, Expr.cost]
  omega

@[simp] theorem kyberEq_cost {Γ : List PT}
    (a b : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32))))) :
    (kyberEq a b).cost = 4 * a.cost + 4 * b.cost + 91 := by
  simp only [kyberEq, natEq, cost_eqU32, cost_eqB, Expr.cost, PNat.val_ofNat]
  omega

@[simp] theorem kyberCheckE_cost {Γ : List PT} (K : Nat)
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32))))) :
    (kyberCheckE K used entry).cost = used.cost + entry.cost + K * 100 + 16 := by
  simp only [kyberCheckE, eLet2, eLet, eAny, kyberEq_cost, cost_v, Expr.cost]
  omega

@[simp] theorem nonZero32_cost {Γ : List PT} (b : Expr pqxdhOps Γ (B 32)) :
    (nonZero32 b).cost = b.cost + 131 := by
  simp only [nonZero32, cost_eqB, cost_litB, Expr.cost, PNat.val_ofNat, List.length_replicate]

@[simp] theorem dhOptNZ_cost {Γ : List PT} (d : Expr pqxdhOps Γ (.opt (B 32))) :
    (dhOptNZ d).cost = d.cost + 133 := by
  simp [dhOptNZ, eCaseOpt]

@[simp] theorem findHonestC_cost (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).cost = ik.cost + (min K S.N_dh) * 206 + 6 := by
  simp only [findHonestC, letV, findMV, bindV, stPrin, peIkAPk, cost_qPow8, cost_eqB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  omega

@[simp] theorem isAdvRegC_cost (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).cost = pk.cost + K * 69 + 79 := by
  simp only [isAdvRegC, bindV, eAny, stAdv, cost_qPow8, cost_eqB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  omega

@[simp] theorem isGameSpkC_cost (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).cost = pk.cost + (min K S.N_dh) * 206 + 7 := by
  simp only [isGameSpkC, letV, anyMV, bindV, stSpks, sbSpkPk, cost_qPow8, cost_eqB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  omega

@[simp] theorem isGameOpkC_cost (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).cost = pk.cost + (min K S.N_dh) * 206 + 8 := by
  simp only [isGameOpkC, letV, anyMV, bindV, stOpks, oeOpkPk, cost_qPow8, cost_eqB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  omega

@[simp] theorem koskBundleOkC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).cost = 301 + (min K S.N_dh) * 618 + K * 207 := by
  simp only [koskBundleOkC, bindV, caseOptV, findHonestC_cost, isAdvRegC_cost,
    isGameSpkC_cost, isGameOpkC_cost, isSomeE, buIkB, buSpkB, buOpkB,
    cost_orE, cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem koskSenderOkC_cost (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).cost = ik.cost + 97 + (min K S.N_dh) * 206 + K * 69 := by
  simp only [koskSenderOkC, letV, bindV, findHonestC_cost, isAdvRegC_cost,
    isSomeE, cost_orE, cost_v, Comp.cost, Expr.cost]
  omega

@[simp] theorem resolveSigPkC_cost (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).cost = ik.cost + 19 + (min K S.N_dh) * 206 := by
  simp only [resolveSigPkC, letV, bindV, findHonestC_cost, eCaseOpt, peIkSignPk,
    cost_v, Comp.cost, Expr.cost]
  omega

@[simp] theorem honestPeerC_cost (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).cost = ik.cost + 21 + (min K S.N_dh) * 206 := by
  simp only [honestPeerC, bindV, findHonestC_cost, eCaseOpt, peCorrupted,
    cost_v, Comp.cost, Expr.cost]
  omega

@[simp] theorem checkProvC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkProvC (Δ := Δ) S K st bu).cost = 44 + (min K S.N_dh) * 636 + K * 3160 := by
  simp only [checkProvC, bindV, letV, caseOptV, anyMV, eAny, findHonestC_cost,
    natEq, stSpks, stOpks, sbSpkPk, sbPqspkPk, oeOpkPk, buIkB, buSpkB, buPqspkB, buOpkB,
    cost_qPow8, cost_eqB, cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem partnerC_cost {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (partnerC (Δ := Δ) s r).cost = 7361 := by
  simp only [partnerC, bindV, getDBytes, eCaseOpt, hdIkAPk, hdEkAPk, hdKemCt,
    seHdr, reHdr, sePeerIk, reRespIk, sePeerSpk, reSpk, sePeerOpk, reOpk,
    sePeerPqspk, rePqspk, optBytesEq_cost, cost_qPow8, cost_eqB, cost_litB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  rfl

@[simp] theorem recordRespC_cost (S : Setup) (K : Nat) {Δ : List PT}
    (p : Expr pqxdhOps Δ (.prod keyIndRespEntryTy keyIndStateTy)) :
    (recordRespC S K p).cost = p.cost + 292 + (min K S.N_dh) * 7362 := by
  simp only [recordRespC, letV, bindV, findMV, caseOptV, partnerC_cost,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stMk, stUpd, reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest,
    reDrReal, reTested, reRevealed, reMk, reUpd, seDrRand,
    cost_sDrKey96, cost_v, Comp.cost, Expr.cost]
  omega

@[simp] theorem hkdfOrRoC_true_cost (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K true st sec).cost = sec.cost + 132 + K * 389 := by
  simp only [hkdfOrRoC, letV, caseOptV, bindV, eFind, stRo, cost_sDrKey96, cost_eqB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, ↓reduceIte]
  omega

@[simp] theorem hkdfOrRoC_false_cost (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K false st sec).cost = sec.cost + 307 := by
  simp only [hkdfOrRoC, letV, bindV, stRo, cost_qHkdfDerive96,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, Bool.false_eq_true, ↓reduceIte]

@[simp] theorem acceptKeysC_cost {Δ : List PT} (inp : Expr pqxdhOps Δ accInpTy) :
    (acceptKeysC inp).cost = inp.cost + 6988 := by
  simp only [acceptKeysC, letV, bindV, eCaseOpt, getDBytes, guardE, natEq,
    aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, hdIkAPk, hdEkAPk, hdOpkId, hdKemCt,
    buildSecretsE_cost, nonZero32_cost, dhOptNZ_cost, cost_qIsCanonical, cost_qX25519,
    cost_qKemDecaps, cost_qHkdfDerive96, cost_lenB, cost_litB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil, bits_32]
  omega

@[simp] theorem freshE_cost {Γ : List PT} (K : Nat)
    (st : Expr pqxdhOps Γ keyIndStateTy) (sid : Expr pqxdhOps Γ sidT) :
    (freshE K st sid).cost = st.cost + sid.cost + 16 + K * 45 + max (43 + K * 45) 48 := by
  simp only [freshE, eLet2, eLet, eCaseOpt, eFind, sidEq_cost, stSess, stResps,
    seSid, reSid, reSenderHonest, reTested, reRevealed, seFresh, seTested, seRevealed,
    cost_v, Expr.cost]
  ring_nf; omega

@[simp] theorem initFinishC_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT)
    (bu : Var Γ₃ bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy)) (ekSk : Var Γ₅ (B 32))
    (sc : Var Γ₆ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) true S K st sid bu uE ekSk sc).cost =
      1937 + (min K S.N_dh) * 1048 + (min K S.N_sess_tot) * 7362 + K * 3549 := by
  simp only [initFinishC, bindV, letV, caseOptV, findMV,
    peSecIKA0, peIkAPk, buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB,
    optFst, optSnd, getDBytes, eCaseOpt, isSomeE, hdMk, seMk, seUpd,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon,
    sePqspkHon, seEkASk, seFresh, seDrReal, seHdr, seTested, seRevealed, reDrRand,
    rs, rInitUnfresh, rHdr, stUpd, stMk,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
    buildSecretsE_cost, hkdfOrRoC_true_cost, honestPeerC_cost, checkProvC_cost,
    partnerC_cost, findHonestC_cost, cost_qX25519Base, cost_qX25519, cost_sDrKey96,
    cost_litB, cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem initFinishC_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT)
    (bu : Var Γ₃ bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy)) (ekSk : Var Γ₅ (B 32))
    (sc : Var Γ₆ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) false S K st sid bu uE ekSk sc).cost =
      2112 + (min K S.N_dh) * 1048 + (min K S.N_sess_tot) * 7362 + K * 3160 := by
  simp only [initFinishC, bindV, letV, caseOptV, findMV,
    peSecIKA0, peIkAPk, buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB,
    optFst, optSnd, getDBytes, eCaseOpt, isSomeE, hdMk, seMk, seUpd,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon,
    sePqspkHon, seEkASk, seFresh, seDrReal, seHdr, seTested, seRevealed, reDrRand,
    rs, rInitUnfresh, rHdr, stUpd, stMk,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
    buildSecretsE_cost, hkdfOrRoC_false_cost, honestPeerC_cost, checkProvC_cost,
    partnerC_cost, findHonestC_cost, cost_qX25519Base, cost_qX25519, cost_sDrKey96,
    cost_litB, cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem preCheckC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT)
    (u : Var Γ₃ .nat) (bu : Var Γ₄ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (preCheckC (Δ := Δ) S K st sid u bu).cost = 321 + (min K S.N_dh) * 618 + K * 257 := by
  simp only [preCheckC, caseOptV, bindV, eAny, eFind, sidEq_cost, natEq,
    koskBundleOkC_cost, stSess, stPrin, seSid, cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem checkSigsC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkSigsC (Δ := Δ) S K st bu).cost = 3457 + (min K S.N_dh) * 206 := by
  simp only [checkSigsC, bindV, resolveSigPkC_cost, buIkB, buSpkB, buSpkSig,
    buPqspkB, buPqspkSig, cost_encEC, cost_encKEM, cost_qSigVerify,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  ring_nf

@[simp] theorem extractC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (extractC (Δ := Δ) S K s bu).cost =
      3490 + (min K S.N_dh) * 206 + K * 80 + max 1613 (1597 + K * 3159) := by
  simp only [extractC, bindV, letV, cost_liftBase, honestPeerC_cost,
    sgGame, sgTarget, sgPk, sgForgery, stSpks, sbSpkPk, sbPqspkPk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig,
    eCaseOpt, eAny, natEq, cost_encEC, cost_encKEM, cost_widenEC, cost_qSigVerify, cost_eqB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem initPrinB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrinB (Δ := Δ) K st u).cost = 314 + K * 5 := by
  simp only [initPrinB, bindV, eAny, natEq, rs, rNone, rInitPrin, stUpd, stMk, peMk,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    cost_sBytes32, cost_qX25519Base, cost_qSigPkGen, cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem corruptB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (corruptB (Δ := Δ) K st u).cost = 107 + K * 37 := by
  simp only [corruptB, caseOptV, eFind, eMap, natEq, rs, rNone, rCorr, stUpd, stMk, peUpd, peMk,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem genSpkB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genSpkB (Δ := Δ) K st x).cost = 8798 + K * 20 := by
  simp only [genSpkB, caseOptV, bindV, eAny, eFind, nat2Eq, natEq,
    rs, rNone, rBundle, buMk, stUpd, stMk, sbMk, peIkAPk, peSecIKAsign,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    cost_sBytes32, cost_qX25519Base, cost_sRandom64, cost_qSigSign, cost_qKemKeyGen,
    cost_encEC, cost_encKEM, cost_u32OfNat, cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem genOpkB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genOpkB (Δ := Δ) K st x).cost = 209 + K * 25 := by
  simp only [genOpkB, bindV, eAny, nat3Eq, nat2Eq, natEq, rs, rNone, rPk, stUpd, stMk, oeMk,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    cost_sBytes32, cost_qX25519Base, cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem initiateOpkB_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initiateOpkB (Δ := Δ) true S K st x).cost =
      9023 + (min K S.N_dh) * 1872 + (min K S.N_sess_tot) * 7362 + K * 3807 := by
  simp only [initiateOpkB, initiateC, initSidE, letV, bindV, caseOptV,
    eAny, eFind, sidEq_cost, natEq, isSomeE, rs, rNone,
    koskBundleOkC_cost, resolveSigPkC_cost, initFinishC_true_cost,
    stSess, stPrin, seSid, buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig,
    cost_sBytes32, cost_encEC, cost_encKEM, cost_qSigVerify, cost_qKemEncaps,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem initiateOpkB_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initiateOpkB (Δ := Δ) false S K st x).cost =
      9198 + (min K S.N_dh) * 1872 + (min K S.N_sess_tot) * 7362 + K * 3418 := by
  simp only [initiateOpkB, initiateC, initSidE, letV, bindV, caseOptV,
    eAny, eFind, sidEq_cost, natEq, isSomeE, rs, rNone,
    koskBundleOkC_cost, resolveSigPkC_cost, initFinishC_false_cost,
    stSess, stPrin, seSid, buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig,
    cost_sBytes32, cost_encEC, cost_encKEM, cost_qSigVerify, cost_qKemEncaps,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem initiateNoOpkB_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initiateNoOpkB (Δ := Δ) true S K st x).cost =
      9023 + (min K S.N_dh) * 1872 + (min K S.N_sess_tot) * 7362 + K * 3807 := by
  simp only [initiateNoOpkB, initiateC, initSidE, letV, bindV, caseOptV,
    eAny, eFind, sidEq_cost, natEq, isSomeE, rs, rNone,
    koskBundleOkC_cost, resolveSigPkC_cost, initFinishC_true_cost,
    stSess, stPrin, seSid, buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig,
    cost_sBytes32, cost_encEC, cost_encKEM, cost_qSigVerify, cost_qKemEncaps,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, Bool.false_eq_true, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem initiateNoOpkB_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initiateNoOpkB (Δ := Δ) false S K st x).cost =
      9198 + (min K S.N_dh) * 1872 + (min K S.N_sess_tot) * 7362 + K * 3418 := by
  simp only [initiateNoOpkB, initiateC, initSidE, letV, bindV, caseOptV,
    eAny, eFind, sidEq_cost, natEq, isSomeE, rs, rNone,
    koskBundleOkC_cost, resolveSigPkC_cost, initFinishC_false_cost,
    stSess, stPrin, seSid, buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig,
    cost_sBytes32, cost_encEC, cost_encKEM, cost_qSigVerify, cost_qKemEncaps,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, Bool.false_eq_true, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem acceptOpkB_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (acceptOpkB (Δ := Δ) true S K st x).cost =
      13884 + (min K S.N_dh) * 7980 + K * 764 := by
  simp only [acceptOpkB, letV, bindV, caseOptV, eAny, eFind, eMap, eCaseOpt,
    natEq, nat2Eq, nat3Eq, optU32Eq_cost, kyberCheckE_cost,
    koskSenderOkC_cost, acceptKeysC_cost, hkdfOrRoC_true_cost, buildSecretsE_cost,
    findHonestC_cost, recordRespC_cost, isSomeE,
    qK, qJ, qO, qHdr, qKJO, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    oeOpkSk, oeOpkPk, oeConsumed, oeUpd, oeMk, reMk,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
    rs, rNone, rDrKey, rAccFresh,
    cost_eqU32, cost_u32OfNat, cost_lenB, cost_qKemDecaps, cost_qX25519,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_32]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem acceptOpkB_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (acceptOpkB (Δ := Δ) false S K st x).cost =
      14059 + (min K S.N_dh) * 7980 + K * 375 := by
  simp only [acceptOpkB, letV, bindV, caseOptV, eAny, eFind, eMap, eCaseOpt,
    natEq, nat2Eq, nat3Eq, optU32Eq_cost, kyberCheckE_cost,
    koskSenderOkC_cost, acceptKeysC_cost, hkdfOrRoC_false_cost, buildSecretsE_cost,
    findHonestC_cost, recordRespC_cost, isSomeE,
    qK, qJ, qO, qHdr, qKJO, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    oeOpkSk, oeOpkPk, oeConsumed, oeUpd, oeMk, reMk,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
    rs, rNone, rDrKey, rAccFresh,
    cost_eqU32, cost_u32OfNat, cost_lenB, cost_qKemDecaps, cost_qX25519,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_32]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem acceptNoOpkB_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (acceptNoOpkB (Δ := Δ) true S K st x).cost =
      13751 + (min K S.N_dh) * 7980 + K * 640 := by
  simp only [acceptNoOpkB, letV, bindV, caseOptV, eAny, eFind, eCaseOpt,
    natEq, nat2Eq, nat3Eq, optU32Eq_cost, kyberCheckE_cost,
    koskSenderOkC_cost, acceptKeysC_cost, hkdfOrRoC_true_cost, buildSecretsE_cost,
    findHonestC_cost, recordRespC_cost, isSomeE,
    qK, qJ, qO, qHdr, qKJO, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, reMk,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
    rs, rNone, rDrKey, rAccFresh,
    cost_eqU32, cost_u32OfNat, cost_lenB, cost_qKemDecaps, cost_qX25519,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_32]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem acceptNoOpkB_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (acceptNoOpkB (Δ := Δ) false S K st x).cost =
      13926 + (min K S.N_dh) * 7980 + K * 251 := by
  simp only [acceptNoOpkB, letV, bindV, caseOptV, eAny, eFind, eCaseOpt,
    natEq, nat2Eq, nat3Eq, optU32Eq_cost, kyberCheckE_cost,
    koskSenderOkC_cost, acceptKeysC_cost, hkdfOrRoC_false_cost, buildSecretsE_cost,
    findHonestC_cost, recordRespC_cost, isSomeE,
    qK, qJ, qO, qHdr, qKJO, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, reMk,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
    rs, rNone, rDrKey, rAccFresh,
    cost_eqU32, cost_u32OfNat, cost_lenB, cost_qKemDecaps, cost_qX25519,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_32]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem testB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (testB (Δ := Δ) K st sid).cost =
      28 + K * 90 + max (43 + K * 45) 48 + max (120 + K * 167) (115 + K * 197) := by
  simp only [testB, caseOptV, freshE_cost, eFind, eMap, sidEq_cost,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon,
    sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr, seRevealed, seUpd, seMk,
    reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
    reRevealed, reUpd, reMk, stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps,
    stUsedO, stUsedN, stKyb, stRo, stAdv, rs, rNone, rDrKey, cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem revealB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (revealB (Δ := Δ) K st sid).cost = 8 + K * 45 + max (128 + K * 167) (128 + K * 197) := by
  simp only [revealB, caseOptV, eFind, eMap, sidEq_cost,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon,
    sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr, seTested, seUpd, seMk,
    reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
    reTested, reUpd, reMk, stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps,
    stUsedO, stUsedN, stKyb, stRo, stAdv, rs, rNone, rDrKey, cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem roB_true_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roB (Δ := Δ) true K st sec).cost = 224 + K * 389 := by
  simp only [roB, bindV, hkdfOrRoC_true_cost, rs, rDrKey, stUpd, stMk,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
    cost_v, Comp.cost, Expr.cost, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  ring_nf

@[simp] theorem roB_false_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roB (Δ := Δ) false K st sec).cost = 5 := by
  simp only [roB, rs, rNone, cost_v, Comp.cost, Expr.cost, Bool.not_false, ↓reduceIte]

@[simp] theorem revealDhB_true_cost (K : Nat) {Γ₁ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) [Ext Γ₁ Δ] :
    (revealDhB (Δ := Δ) true K st).cost = 5 := by
  simp only [revealDhB, rs, rNone, cost_v, Comp.cost, Expr.cost, ↓reduceIte]

@[simp] theorem revealDhB_false_cost (K : Nat) {Γ₁ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) [Ext Γ₁ Δ] :
    (revealDhB (Δ := Δ) false K st).cost = 38 + K * 24 := by
  simp only [revealDhB, eMap, peSecIKA0, sbSpkSk, oeOpkSk, seEkASk,
    stPrin, stSpks, stOpks, stSess, rs, rDh,
    cost_v, Comp.cost, Expr.cost, Bool.false_eq_true, ↓reduceIte]
  ring_nf

@[simp] theorem registerB_cost {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (registerB (Δ := Δ) st sk).cost = 246 := by
  simp only [registerB, bindV, natEq, rs, rNone, rPk, stUpd, stMk,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    cost_lenB, cost_qX25519Base, cost_qPow8,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_32]
  rfl

@[simp] theorem revealSpkB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (revealSpkB (Δ := Δ) K st x).cost = 108 + K * 72 := by
  simp only [revealSpkB, caseOptV, eFind, eMap, nat2Eq, natEq,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbUpd, sbMk,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
    stKyb, stRo, stAdv, rs, rNone, rSpkSk, cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem onGame_cost {Γ₁ Δ : List PT} (s : Var Γ₁ sigStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS) :
    (onGame (Δ := Δ) s br).cost = (br .zero).cost + 32 := by
  simp only [onGame, bindV, letV, cost_liftBase, sgUpd, sgGame, sgTarget, sgPk, sgForgery, sgBudget,
    cost_v, Comp.cost, Expr.cost]
  ring_nf

@[simp] theorem onBase_cost {Γ₁ Δ : List PT} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS) :
    (onBase (Δ := Δ) s br).cost = (br .zero).cost + 70 := by
  simp only [onBase, bindV, letV, scUpd, scMk, scBase, scTB, scTPk, scTSk, scCnt,
    scIR, scRR, scSIdx, scChosen, cost_v, Comp.cost, Expr.cost]
  ring_nf

@[simp] theorem sigInitPrinB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigInitPrinB (Δ := Δ) K s u).cost = 358 + K * 10 := by
  simp only [sigInitPrinB, bindV, cost_liftBase, onGame_cost, initPrinB_cost,
    eAny, natEq, sgGame, sgTarget, sgPk, sgUpd, sgForgery, sgBudget,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
    stKyb, stRo, stAdv, peMk, rNone, rInitPrin, cost_sBytes32, cost_qX25519Base, cost_litB,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem sigCorruptB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigCorruptB (Δ := Δ) K s u).cost = 145 + K * 37 := by
  simp only [sigCorruptB, caseOptV, onGame_cost, corruptB_cost,
    eFind, eMap, natEq, sgGame, sgTarget, sgPk, sgUpd, sgForgery, sgBudget,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
    stKyb, stRo, stAdv, peUpd, peMk, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, rNone,
    cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem sigGenSpkB_cost (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigGenSpkB (Δ := Δ) K s x).cost = 8837 + K * 20 := by
  simp only [sigGenSpkB, caseOptV, bindV, cost_liftBase, onGame_cost, genSpkB_cost,
    eAny, eFind, nat2Eq, natEq, sgGame, sgTarget, sgPk, sgUpd, sgForgery, sgBudget,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
    stKyb, stRo, stAdv, sbMk, buMk, peIkAPk, rNone, rBundle,
    cost_sBytes32, cost_qX25519Base, cost_qChalSign, cost_sRandom64, cost_qKemKeyGen,
    cost_encEC, cost_encKEM, cost_u32OfNat,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_0, bits_1]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem sigInitiateB_true_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigInitiateB (Δ := Δ) true S K true s x).cost =
      12547 + (min K S.N_dh) * 2078 + (min K S.N_sess_tot) * 7362 + K * 3887 + max 1613 (1597 + K * 3159) := by
  simp only [sigInitiateB, letV, bindV, cost_liftBase, extractC_cost, initiateOpkB_true_cost,
    sgGame, sgTarget, sgPk, sgUpd, sgBudget, cost_v, Comp.cost, Expr.cost, ↓reduceIte]
  ring_nf

@[simp] theorem sigInitiateB_true_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigInitiateB (Δ := Δ) true S K false s x).cost =
      12547 + (min K S.N_dh) * 2078 + (min K S.N_sess_tot) * 7362 + K * 3887 + max 1613 (1597 + K * 3159) := by
  simp only [sigInitiateB, letV, bindV, cost_liftBase, extractC_cost, initiateNoOpkB_true_cost,
    sgGame, sgTarget, sgPk, sgUpd, sgBudget,
    cost_v, Comp.cost, Expr.cost, Bool.false_eq_true, ↓reduceIte]
  ring_nf

@[simp] theorem sigInitiateB_false_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigInitiateB (Δ := Δ) false S K true s x).cost =
      12722 + (min K S.N_dh) * 2078 + (min K S.N_sess_tot) * 7362 + K * 3498 + max 1613 (1597 + K * 3159) := by
  simp only [sigInitiateB, letV, bindV, cost_liftBase, extractC_cost, initiateOpkB_false_cost,
    sgGame, sgTarget, sgPk, sgUpd, sgBudget, cost_v, Comp.cost, Expr.cost, ↓reduceIte]
  ring_nf

@[simp] theorem sigInitiateB_false_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigInitiateB (Δ := Δ) false S K false s x).cost =
      12722 + (min K S.N_dh) * 2078 + (min K S.N_sess_tot) * 7362 + K * 3498 + max 1613 (1597 + K * 3159) := by
  simp only [sigInitiateB, letV, bindV, cost_liftBase, extractC_cost, initiateNoOpkB_false_cost,
    sgGame, sgTarget, sgPk, sgUpd, sgBudget,
    cost_v, Comp.cost, Expr.cost, Bool.false_eq_true, ↓reduceIte]
  ring_nf

@[simp] theorem shcrGenSpkB_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrGenSpkB (Δ := Δ) S K s x).cost = 8885 + K * 20 := by
  simp only [shcrGenSpkB, caseOptV, bindV, onBase_cost, genSpkB_cost,
    eAny, eFind, nat2Eq, natEq,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
    stUpd, stMk, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
    stKyb, stRo, stAdv, sbMk, buMk, peIkAPk, peSecIKAsign, rNone, rBundle,
    cost_sBytes32, cost_qX25519Base, cost_sRandom64, cost_qSigSign,
    cost_encEC, cost_encKEM, cost_u32OfNat,
    cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem shcrInitiateC_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrInitiateC (Δ := Δ) S K true s x).cost =
      9132 + (min K S.N_dh) * 1872 + (min K S.N_sess_tot) * 7362 + K * 3806 := by
  simp only [shcrInitiateC, initGuardE, initSidE, letV, bindV, caseOptV,
    preCheckC_cost, checkSigsC_cost, initFinishC_true_cost,
    isSomeE, buOpkB, buPqspkB, rNone, shcrFinE,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
    cost_sBytes32, cost_qKemEncaps,
    cost_v, Comp.cost, Expr.cost, bits_1, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem shcrInitiateC_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrInitiateC (Δ := Δ) S K false s x).cost =
      9132 + (min K S.N_dh) * 1872 + (min K S.N_sess_tot) * 7362 + K * 3806 := by
  simp only [shcrInitiateC, initGuardE, initSidE, letV, bindV, caseOptV,
    preCheckC_cost, checkSigsC_cost, initFinishC_true_cost,
    isSomeE, buOpkB, buPqspkB, rNone, shcrFinE,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
    cost_sBytes32, cost_qKemEncaps,
    cost_v, Comp.cost, Expr.cost, bits_1, Bool.false_eq_true, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem shcrAcceptB_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K true s x).cost =
      18866 + (min K S.N_dh) * 7980 + K * 788 := by
  simp only [shcrAcceptB, bindV, caseOptV, onBase_cost, acceptOpkB_true_cost,
    isNoneRespE, eCaseSum, eFind, nat2Eq, natEq, bits_0,
    qK, qJ, qHdr, hdKemCt, sbPqspkPk, sbPqspkSk, stSpks,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
    cost_qKemDecaps, cost_v, Comp.cost, Expr.cost, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem shcrAcceptB_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K false s x).cost =
      18733 + (min K S.N_dh) * 7980 + K * 664 := by
  simp only [shcrAcceptB, bindV, caseOptV, onBase_cost, acceptNoOpkB_true_cost,
    isNoneRespE, eCaseSum, eFind, nat2Eq, natEq, bits_0,
    qK, qJ, qHdr, hdKemCt, sbPqspkPk, sbPqspkSk, stSpks,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scUpd, scMk,
    cost_qKemDecaps, cost_v, Comp.cost, Expr.cost, Bool.false_eq_true, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

@[simp] theorem tryPauseC_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (tryPauseC (Δ := Δ) S K true s x).cost = 3843 + (min K S.N_dh) * 824 + K * 257 := by
  simp only [tryPauseC, initGuardE, initSidE, letV, bindV, caseOptV,
    preCheckC_cost, checkSigsC_cost, isSomeE, buOpkB, natEq, scBase, scCnt, scSIdx,
    cost_v, Comp.cost, Expr.cost, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem tryPauseC_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (tryPauseC (Δ := Δ) S K false s x).cost = 3843 + (min K S.N_dh) * 824 + K * 257 := by
  simp only [tryPauseC, initGuardE, initSidE, letV, bindV, caseOptV,
    preCheckC_cost, checkSigsC_cost, isSomeE, buOpkB, natEq, scBase, scCnt, scSIdx,
    cost_v, Comp.cost, Expr.cost, Bool.false_eq_true, ↓reduceIte]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem pauseCheckC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (pauseCheckC (Δ := Δ) S K s q).cost = 3855 + (min K S.N_dh) * 824 + K * 257 := by
  simp only [pauseCheckC, caseSumV, tryPauseC_true_cost, tryPauseC_false_cost,
    cost_v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  ring_nf

@[simp] theorem shcrResumeC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy)
    (s : Var Γ₃ shcrStTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (shcrResumeC (Δ := Δ) S K sc d s).cost =
      2155 + (min K S.N_dh) * 1048 + (min K S.N_sess_tot) * 7362 + K * 3549 := by
  simp only [shcrResumeC, letV, bindV, initFinishC_true_cost,
    shcrFinE, buPqspkB, scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scUpd, scMk,
    cost_sBytes32, cost_v, Comp.cost, Expr.cost, bits_1]
  ring_nf

@[simp] theorem shcrExtractC_cost (Q : Nat) {Γ₁ Γ₃ Δ : List PT}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₃ Δ] :
    (shcrExtractC (Δ := Δ) Q sc s).cost = 20 + Q * 11168 := by
  simp only [shcrExtractC, bindV, findMV, eCaseOpt, optBytesEq_cost,
    scRR, scTSk, scChosen, scTPk, rrCt,
    cost_qKemDecaps, cost_orE, cost_eqB, cost_v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  ring_nf

/-! ## Handler and reduction cost bounds -/

/-- Loop bound for `KeyInd` game-state lists across at most `b.q_total` queries. -/
def keyIndLoopBound (b : QueryBudget) : Nat := 2 * b.q_total + 1

theorem bits_le_add_one (n : Nat) : bits n ≤ n + 1 :=
  ReductionDsl.bits_le_succ n

theorem nRecv_le_spk_tot (S : Setup) : nRecv S ≤ S.N_spk_tot := by
  unfold nRecv Setup.N_spk_tot
  split
  · exact Nat.zero_le _
  · next h =>
    have : 1 ≤ S.N_id := by omega
    exact Nat.le_mul_of_pos_left S.N_recv this

theorem bits_nRecv_le (S : Setup) : bits (nRecv S) ≤ S.N_dh + 1 := by
  have h1 := bits_le_add_one (nRecv S)
  have h2 := nRecv_le_spk_tot S
  unfold Setup.N_dh
  omega

theorem bits_N_id_le (S : Setup) : bits S.N_id ≤ S.N_dh + 1 := by
  have h1 := bits_le_add_one S.N_id
  unfold Setup.N_dh
  omega

theorem bits_N_spk_tot_le (S : Setup) : bits S.N_spk_tot ≤ S.N_dh + 1 := by
  have h1 := bits_le_add_one S.N_spk_tot
  unfold Setup.N_dh
  omega

theorem bits_N_send_tot_le (S : Setup) : bits S.N_send_tot ≤ S.N_dh + 1 := by
  have h1 := bits_le_add_one S.N_send_tot
  unfold Setup.N_dh
  omega

theorem sigHandleC_cost_le (useRo : Bool) (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigHandleC (Δ := Δ) useRo S K s q).cost ≤
      14389 + (min K S.N_dh) * 7980 + (min K S.N_sess_tot) * 7362 + K * 7046 := by
  cases useRo <;> (
    simp only [sigHandleC, caseSumV, isSomeE, sgForgery, rNone,
      onGame_cost, sigInitPrinB_cost, sigCorruptB_cost, sigGenSpkB_cost, genOpkB_cost,
      sigInitiateB_true_true_cost, sigInitiateB_true_false_cost,
      sigInitiateB_false_true_cost, sigInitiateB_false_false_cost,
      acceptOpkB_true_cost, acceptOpkB_false_cost,
      acceptNoOpkB_true_cost, acceptNoOpkB_false_cost,
      testB_cost, roB_true_cost, roB_false_cost,
      revealDhB_true_cost, revealDhB_false_cost,
      revealB_cost, registerB_cost, revealSpkB_cost,
      cost_v, Comp.cost, Expr.cost]
    generalize min K S.N_dh = md
    generalize min K S.N_sess_tot = ms
    omega)

theorem sigKeyIndProg_handle_cost_le (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).handle.cost ≤
      14389 + (min K S.N_dh) * 7980 + (min K S.N_sess_tot) * 7362 + K * 7046 :=
  sigHandleC_cost_le useRo S K (Γ₁ := [sigStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [sigStTy, keyIndQueryTy]) .zero .zero

theorem sigKeyIndProg_init_cost (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).init.cost = 37 + bits S.N_id + bits (min K S.N_spk_tot) := by
  simp only [sigKeyIndProg, emptyStE, stMk, bindV,
    cost_liftBase, cost_sIndex, cost_sBool, cost_v, Comp.cost, Expr.cost]
  omega

theorem sigKeyIndProg_finish_cost (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).finish.cost = if S.N_id = 0 then 1637 else 1643 := by
  dsimp only [sigKeyIndProg]
  split
  · simp only [cost_litB, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  · simp only [sgForgery, eCaseOpt, cost_litB, cost_v,
      Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
    simp (discharger := clear *- ; omega) only [Nat.max_eq_left]

theorem sigKeyIndProg_finish_cost_le (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).finish.cost ≤ 1643 := by
  rw [sigKeyIndProg_finish_cost]
  split <;> omega

theorem bits_eq_log2_succ (n : Nat) : bits n = Nat.log 2 n + 1 := rfl

theorem security_stepCostBudget_le (S : Setup) (b : QueryBudget) :
    _root_.SignalPqxdh.Security.stepCostBudget S b ≤ stepCostBudget S b := by
  unfold _root_.SignalPqxdh.Security.stepCostBudget stepCostBudget
  dsimp only
  have hmd : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hld : Nat.log 2 S.N_dh ≤ S.N_dh := Nat.log_le_self 2 S.N_dh
  have hls : Nat.log 2 S.N_sess_tot ≤ S.N_sess_tot := Nat.log_le_self 2 S.N_sess_tot
  have hsq : (min b.q_total S.N_dh) ^ 2 ≤ S.N_dh ^ 2 := Nat.pow_le_pow_left hmd 2
  have hpr : 2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot ≤
      2 ^ 8 * S.N_dh * S.N_sess_tot :=
    Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ 8) hmd) hms
  have hlin : (b.q_total + 1) *
      (2 ^ 16 * (b.q_total + 1) +
        2 ^ 15 * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
        2 ^ 10 * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot)) ≤
      (b.q_total + 1) * (2 ^ 16 * (b.q_total + S.N_dh + S.N_sess_tot + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have hring1 : 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) =
      (b.q_total + 1) *
        (2 ^ 16 * (b.q_total + 1) +
          2 ^ 15 * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
          2 ^ 10 * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot)) := by ring
  have hring2 : 2 ^ 16 * (b.q_total + 1) * (b.q_total + S.N_dh + S.N_sess_tot + 1) =
      (b.q_total + 1) * (2 ^ 16 * (b.q_total + S.N_dh + S.N_sess_tot + 1)) := by ring
  omega

theorem total_le_stepCostBudget (S : Setup) (b : QueryBudget) (c0 h : Nat)
    (hc : c0 ≤ 2 ^ 16 * (b.q_total + S.N_dh + S.N_sess_tot + 1))
    (hh : h ≤ 2 ^ 16 * (b.q_total + S.N_dh + S.N_sess_tot + 1)) :
    c0 + b.q_total * h ≤ stepCostBudget S b := by
  unfold stepCostBudget
  generalize b.q_total + S.N_dh + S.N_sess_tot + 1 = X at *
  have h1 : b.q_total * h ≤ b.q_total * (2 ^ 16 * X) := Nat.mul_le_mul_left _ hh
  have h2 : 2 ^ 16 * X + b.q_total * (2 ^ 16 * X) = 2 ^ 16 * (b.q_total + 1) * X := by ring
  have h3 : 2 ^ 16 * (b.q_total + 1) * X ≤
      2 ^ 16 * (b.q_total + 1) * X + 2 ^ 11 * S.N_dh ^ 2 + 2 ^ 8 * S.N_dh * S.N_sess_tot :=
    le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  omega

theorem sigKeyIndProg_totalCost_le_security_of_le (useRo : Bool) (S : Setup) (b : QueryBudget)
    (K : Nat) (hK : K ≤ keyIndLoopBound b) :
    (sigKeyIndProg useRo S K).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have hh := sigKeyIndProg_handle_cost_le useRo S K
  have hi := sigKeyIndProg_init_cost useRo S K
  have hf := sigKeyIndProg_finish_cost_le useRo S K
  have hKB : keyIndLoopBound b = 2 * b.q_total + 1 := rfl
  have hIdLeDh : S.N_id ≤ S.N_dh := by unfold Setup.N_dh; omega
  have hbId : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 := by
    rw [bits_eq_log2_succ]
    exact Nat.add_le_add_right (Nat.log_mono_right hIdLeDh) 1
  have hbMin : bits (min K S.N_spk_tot) ≤ K + 1 :=
    (ReductionDsl.bits_mono (Nat.min_le_left _ _)).trans (bits_le_add_one K)
  have hu : pqxdhEufCmaIface.uCost = 1 := rfl
  have hc : (keyIndCodec S).codecCost = 32 := rfl
  rw [CostedReduction.totalCost, hu, hc]
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  generalize hq : b.q_total = q at hKB ⊢
  cases q with
  | zero =>
    omega
  | succ q' =>
    have hmd3 : min K S.N_dh ≤ 3 * min (q' + 1) S.N_dh := by omega
    have hms3 : min K S.N_sess_tot ≤ 3 * min (q' + 1) S.N_sess_tot := by omega
    set M_dh := min (q' + 1) S.N_dh
    set M_sess := min (q' + 1) S.N_sess_tot
    have hMax : max 1 ((sigKeyIndProg useRo S K).handle.cost + 32) ≤
        2 ^ 16 * (q' + 2) + 2 ^ 15 * (M_dh + M_sess) := by omega
    have hMul := Nat.mul_le_mul_left (q' + 1) hMax
    have hRest : (sigKeyIndProg useRo S K).init.cost + (sigKeyIndProg useRo S K).finish.cost ≤
        (2 ^ 16 * (q' + 2) + 2 ^ 15 * (M_dh + M_sess)) +
          2 ^ 10 * (q' + 1 + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by
      have hLog : Nat.log 2 S.N_dh ≤
          2 ^ 10 * (q' + 1 + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by
        have hle1 : 1 ≤ 2 ^ 10 * (q' + 1 + 1) := by omega
        have hle2 : Nat.log 2 S.N_dh ≤ Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot :=
          Nat.le_add_right _ _
        have hmul := Nat.mul_le_mul hle1 hle2
        omega
      omega
    have hComb : (q' + 1) * (2 ^ 16 * (q' + 2) + 2 ^ 15 * (M_dh + M_sess)) +
        (2 ^ 16 * (q' + 2) + 2 ^ 15 * (M_dh + M_sess)) =
        2 ^ 16 * (q' + 1 + 1) * (q' + 1 + 1) +
          2 ^ 15 * (q' + 1 + 1) * (M_dh + M_sess) := by ring
    omega

theorem sigKeyIndProg_totalCost_le_of_le (useRo : Bool) (S : Setup) (b : QueryBudget)
    (K : Nat) (hK : K ≤ keyIndLoopBound b) :
    (sigKeyIndProg useRo S K).totalCost b.q_total ≤ stepCostBudget S b :=
  (sigKeyIndProg_totalCost_le_security_of_le useRo S b K hK).trans
    (security_stepCostBudget_le S b)

theorem shcrPostC_cost_tight_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).cost ≤
      18910 + (min K S.N_dh) * 7980 + (min K S.N_sess_tot) * 7362 + K * 3806 := by
  simp only [shcrPostC, caseSumV, onBase_cost,
    initPrinB_cost, corruptB_cost, shcrGenSpkB_cost, genOpkB_cost,
    shcrInitiateC_true_cost, shcrInitiateC_false_cost,
    shcrAcceptB_true_cost, shcrAcceptB_false_cost,
    testB_cost, roB_true_cost, revealDhB_true_cost,
    revealB_cost, registerB_cost, revealSpkB_cost,
    cost_v, Comp.cost]
  omega

theorem shcrPostC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).cost ≤
      18910 + bits (nRecv S) + (min K S.N_dh) * 7980 + (min K S.N_sess_tot) * 7362 + K * 3806 := by
  have h := shcrPostC_cost_tight_le (Δ := Δ) S K s q
  omega

theorem shcrKeyIndProg_handlePost_cost_tight_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePost.cost ≤
      18910 + (min K S.N_dh) * 7980 + (min K S.N_sess_tot) * 7362 + K * 3806 :=
  shcrPostC_cost_tight_le S K (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero

theorem shcrKeyIndProg_handlePost_cost_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePost.cost ≤
      18910 + bits (nRecv S) + (min K S.N_dh) * 7980 + (min K S.N_sess_tot) * 7362 + K * 3806 :=
  shcrPostC_cost_le S K (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero

theorem shcrPreC_cost_tight_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPreC (Δ := Δ) S K s q).cost ≤
      22778 + (min K S.N_dh) * 8804 + (min K S.N_sess_tot) * 7362 + K * 4063 := by
  simp only [shcrPreC, bindV, caseOptV, pauseCheckC_cost, buPqspkB,
    cost_v, Comp.cost, Expr.cost]
  have hPost := shcrPostC_cost_tight_le S K (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := (.opt pauseTy) :: Δ) s q
  omega

theorem shcrPreC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPreC (Δ := Δ) S K s q).cost ≤
      22778 + bits (nRecv S) + (min K S.N_dh) * 8804 + (min K S.N_sess_tot) * 7362 + K * 4063 := by
  have h := shcrPreC_cost_tight_le (Δ := Δ) S K s q
  omega

theorem shcrKeyIndProg_handlePre_cost_tight_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePre.cost ≤
      22778 + (min K S.N_dh) * 8804 + (min K S.N_sess_tot) * 7362 + K * 4063 :=
  shcrPreC_cost_tight_le S K (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero

theorem shcrKeyIndProg_handlePre_cost_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePre.cost ≤
      22778 + bits (nRecv S) + (min K S.N_dh) * 8804 + (min K S.N_sess_tot) * 7362 + K * 4063 :=
  shcrPreC_cost_le S K (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero

theorem shcrKeyIndProg_resume_cost (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).resume.cost =
      2155 + (min K S.N_dh) * 1048 + (min K S.N_sess_tot) * 7362 + K * 3549 :=
  shcrResumeC_cost S K (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₂ := [pauseTy, .prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)]) .zero .zero .zero

theorem shcrKeyIndProg_finish_cost (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).finish.cost = 20 + Q * 11168 :=
  shcrExtractC_cost Q (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) .zero .zero

theorem shcrKeyIndProg_init_cost (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).init.cost =
      if S.N_spk_tot * S.N_send_tot = 0 then 49
      else 58 + bits S.N_id + bits S.N_recv + bits S.N_send_tot := by
  dsimp only [shcrKeyIndProg]
  split
  · simp only [emptyStE, stMk, scMk, bindV,
      cost_sBool, cost_v, Comp.cost, Expr.cost, bits_0]
  · simp only [emptyStE, stMk, scMk, bindV,
      cost_sIndex, cost_sBool, cost_v, Comp.cost, Expr.cost, bits_0]
    omega

theorem shcrKeyIndProg_init_cost_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).init.cost ≤ 61 + 3 * Nat.log 2 S.N_dh := by
  rw [shcrKeyIndProg_init_cost]
  split
  · omega
  · next h =>
    have hSpkPos : 0 < S.N_spk_tot := by
      rcases Nat.eq_zero_or_pos S.N_spk_tot with h0 | hp
      · exfalso; simp [h0] at h
      · exact hp
    have hIdPos : 1 ≤ S.N_id := by
      unfold Setup.N_spk_tot at hSpkPos
      rcases Nat.eq_zero_or_pos S.N_id with h0 | hp
      · simp [h0] at hSpkPos
      · exact hp
    have hRecvLeSpk : S.N_recv ≤ S.N_spk_tot := by
      unfold Setup.N_spk_tot
      exact Nat.le_mul_of_pos_left S.N_recv hIdPos
    have hIdLeDh : S.N_id ≤ S.N_dh := by unfold Setup.N_dh; omega
    have hRecvLeDh : S.N_recv ≤ S.N_dh := by unfold Setup.N_dh; omega
    have hSendLeDh : S.N_send_tot ≤ S.N_dh := by unfold Setup.N_dh; omega
    have hbId : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 := by
      rw [bits_eq_log2_succ]; exact Nat.add_le_add_right (Nat.log_mono_right hIdLeDh) 1
    have hbRecv : bits S.N_recv ≤ Nat.log 2 S.N_dh + 1 := by
      rw [bits_eq_log2_succ]; exact Nat.add_le_add_right (Nat.log_mono_right hRecvLeDh) 1
    have hbSend : bits S.N_send_tot ≤ Nat.log 2 S.N_dh + 1 := by
      rw [bits_eq_log2_succ]; exact Nat.add_le_add_right (Nat.log_mono_right hSendLeDh) 1
    omega

theorem shcrKeyIndProg_chDone_cost (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).chDone.cost = 5 := by
  simp [shcrKeyIndProg, scTPk, Comp.cost, Expr.cost]

theorem shcrKeyIndProg_totalCost_le_security_of_le (S : Setup) (b : QueryBudget)
    (K : Nat) (hK : K ≤ keyIndLoopBound b) :
    (shcrKeyIndProg S b.q_total K).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have hKB : keyIndLoopBound b = 2 * b.q_total + 1 := rfl
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  generalize hq : b.q_total = q at hKB ⊢
  have h1 := shcrKeyIndProg_handlePre_cost_tight_le S q K
  have h2 := shcrKeyIndProg_handlePost_cost_tight_le S q K
  have h3 := shcrKeyIndProg_resume_cost S q K
  have h4 := shcrKeyIndProg_finish_cost S q K
  have h5 := shcrKeyIndProg_init_cost_le S q K
  have h6 := shcrKeyIndProg_chDone_cost S q K
  have hu : SignalPqxdh.LegacyCosted.pqPrimIface.uCost = 1 := rfl
  have hc : (keyIndCodec S).codecCost = 32 := rfl
  rw [TwoStageCostedReduction.totalCost, hu, hc, h4, h6]
  cases q with
  | zero =>
    have hmd1 : min K S.N_dh ≤ K := Nat.min_le_left _ _
    have hms1 : min K S.N_sess_tot ≤ K := Nat.min_le_left _ _
    have hlog : 3 * Nat.log 2 S.N_dh ≤
        2 ^ 10 * (0 + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by omega
    omega
  | succ q' =>
    have hmd3 : min K S.N_dh ≤ 3 * min (q' + 1) S.N_dh := by omega
    have hms3 : min K S.N_sess_tot ≤ 3 * min (q' + 1) S.N_sess_tot := by omega
    set M_dh := min (q' + 1) S.N_dh
    set M_sess := min (q' + 1) S.N_sess_tot
    have hMax : max 1 (max (shcrKeyIndProg S (q' + 1) K).handlePre.cost
        (shcrKeyIndProg S (q' + 1) K).handlePost.cost + 32) ≤
        2 ^ 16 * (q' + 2) + 2 ^ 15 * (M_dh + M_sess) := by omega
    have hMul := Nat.mul_le_mul_left (q' + 1) hMax
    have hRest : (shcrKeyIndProg S (q' + 1) K).init.cost +
        max 5 (shcrKeyIndProg S (q' + 1) K).resume.cost + (20 + (q' + 1) * 11168) ≤
        (2 ^ 16 * (q' + 2) + 2 ^ 15 * (M_dh + M_sess)) +
          2 ^ 10 * (q' + 1 + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by
      have hLog : 3 * Nat.log 2 S.N_dh ≤
          2 ^ 10 * (q' + 1 + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by
        have hle1 : 3 ≤ 2 ^ 10 * (q' + 1 + 1) := by omega
        have hle2 : Nat.log 2 S.N_dh ≤ Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot :=
          Nat.le_add_right _ _
        exact Nat.mul_le_mul hle1 hle2
      omega
    have hComb : (q' + 1) * (2 ^ 16 * (q' + 2) + 2 ^ 15 * (M_dh + M_sess)) +
        (2 ^ 16 * (q' + 2) + 2 ^ 15 * (M_dh + M_sess)) =
        2 ^ 16 * (q' + 1 + 1) * (q' + 1 + 1) +
          2 ^ 15 * (q' + 1 + 1) * (M_dh + M_sess) := by ring
    omega

theorem shcrKeyIndProg_totalCost_le_security (S : Setup) (b : QueryBudget) :
    (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b :=
  shcrKeyIndProg_totalCost_le_security_of_le S b (keyIndLoopBound b) le_rfl

theorem shcrKeyIndProg_totalCost_le_of_le (S : Setup) (b : QueryBudget)
    (K : Nat) (hK : K ≤ keyIndLoopBound b) :
    (shcrKeyIndProg S b.q_total K).totalCost b.q_total ≤ stepCostBudget S b :=
  (shcrKeyIndProg_totalCost_le_security_of_le S b K hK).trans
    (security_stepCostBudget_le S b)

theorem shcrKeyIndProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (shcrKeyIndProg S b.q_total (keyIndLoopBound b)).totalCost b.q_total ≤ stepCostBudget S b :=
  shcrKeyIndProg_totalCost_le_of_le S b (keyIndLoopBound b) le_rfl

/-! ## Primitive-query weights and bounds -/

def primW : pqPrimIface.Tag → ℕ := fun _ => 1
def primWS : pqPrimIface.smp.Samp → ℕ := fun _ => 0

def sigPrimW : pqxdhEufCmaIface.Tag → ℕ
  | .inl _ => 1
  | .inr _ => 0

def sigWS : pqxdhEufCmaIface.smp.Samp → ℕ := fun _ => 0

@[simp] theorem queries_liftBase {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (liftBase c).queries sigPrimW sigWS = c.queries primW primWS := by
  induction c <;> simp [liftBase, Comp.queries, sigPrimW, primW, sigWS, primWS, *]

@[simp] theorem queries_sBool {Γ : List PT} :
    (sBool (Γ := Γ)).queries primW primWS = 0 := rfl
@[simp] theorem queries_sBytes32 {Γ : List PT} :
    (sBytes32 (Γ := Γ)).queries primW primWS = 0 := rfl
@[simp] theorem queries_sRandom64 {Γ : List PT} :
    (sRandom64 (Γ := Γ)).queries primW primWS = 0 := rfl
@[simp] theorem queries_sDrKey96 {Γ : List PT} :
    (sDrKey96 (Γ := Γ)).queries primW primWS = 0 := rfl
@[simp] theorem queries_sIndex (N : Nat) {Γ : List PT} :
    (sIndex (Γ := Γ) N).queries primW primWS = 0 := rfl
@[simp] theorem queries_qKemKeyGen {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).queries primW primWS = 1 := rfl
@[simp] theorem queries_qX25519Base {Γ : List PT} (sk : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base sk).queries primW primWS = 1 := rfl
@[simp] theorem queries_qX25519 {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    (qX25519 e).queries primW primWS = 1 := rfl
@[simp] theorem queries_qPow8 {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) :
    (qPow8 pk).queries primW primWS = 1 := rfl
@[simp] theorem queries_qIsCanonical {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) :
    (qIsCanonical pk).queries primW primWS = 1 := rfl
@[simp] theorem queries_qSigPkGen {Γ : List PT} (sk : Expr pqxdhOps Γ (B 32)) :
    (qSigPkGen sk).queries primW primWS = 1 := rfl
@[simp] theorem queries_qSigSign (w : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B w) (B 64)))) :
    (qSigSign w e).queries primW primWS = 1 := rfl
@[simp] theorem queries_qSigVerify (w : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B w) (B 64)))) :
    (qSigVerify w e).queries primW primWS = 1 := rfl
@[simp] theorem queries_qKemEncaps {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    (qKemEncaps e).queries primW primWS = 1 := rfl
@[simp] theorem queries_qKemDecaps {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    (qKemDecaps e).queries primW primWS = 1 := rfl
@[simp] theorem queries_qHkdfDerive96 (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) :
    (qHkdfDerive96 w e).queries primW primWS = 1 := rfl
@[simp] theorem queries_qChalSign (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B m)) :
    (qChalSign m e).queries sigPrimW sigWS = 0 := rfl

@[simp] theorem findHonestC_queries (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).queries primW primWS = (min K S.N_dh) * 2 := by
  simp [findHonestC, letV, findMV, bindV, Comp.queries]

@[simp] theorem isAdvRegC_queries (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).queries primW primWS = 1 := by
  simp [isAdvRegC, bindV, Comp.queries]

@[simp] theorem isGameSpkC_queries (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).queries primW primWS = (min K S.N_dh) * 2 := by
  simp [isGameSpkC, letV, anyMV, bindV, Comp.queries]

@[simp] theorem isGameOpkC_queries (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).queries primW primWS = (min K S.N_dh) * 2 := by
  simp [isGameOpkC, letV, anyMV, bindV, Comp.queries]

@[simp] theorem koskBundleOkC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).queries primW primWS = 3 + (min K S.N_dh) * 6 := by
  simp only [koskBundleOkC, bindV, caseOptV, findHonestC_queries, isAdvRegC_queries,
    isGameSpkC_queries, isGameOpkC_queries, Comp.queries]
  omega

@[simp] theorem koskSenderOkC_queries (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).queries primW primWS = 1 + (min K S.N_dh) * 2 := by
  simp only [koskSenderOkC, letV, bindV, findHonestC_queries, isAdvRegC_queries, Comp.queries]
  omega

@[simp] theorem resolveSigPkC_queries (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).queries primW primWS = (min K S.N_dh) * 2 := by
  simp [resolveSigPkC, letV, bindV, findHonestC_queries, Comp.queries]

@[simp] theorem honestPeerC_queries (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).queries primW primWS = (min K S.N_dh) * 2 := by
  simp [honestPeerC, bindV, findHonestC_queries, Comp.queries]

@[simp] theorem checkProvC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkProvC (Δ := Δ) S K st bu).queries primW primWS = (min K S.N_dh) * 6 := by
  simp only [checkProvC, bindV, letV, caseOptV, anyMV,
    findHonestC_queries, queries_qPow8, Comp.queries]
  omega

@[simp] theorem partnerC_queries {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (partnerC (Δ := Δ) s r).queries primW primWS = 8 := rfl

@[simp] theorem recordRespC_queries (S : Setup) (K : Nat) {Δ : List PT}
    (p : Expr pqxdhOps Δ (.prod keyIndRespEntryTy keyIndStateTy)) :
    (recordRespC S K p).queries primW primWS = (min K S.N_dh) * 8 := by
  simp [recordRespC, letV, bindV, caseOptV, findMV, partnerC_queries, Comp.queries]

@[simp] theorem hkdfOrRoC_true_queries (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K true st sec).queries primW primWS = 0 := by
  simp [hkdfOrRoC, letV, caseOptV, bindV, Comp.queries]

@[simp] theorem hkdfOrRoC_false_queries (K : Nat) {Γ Δ : List PT}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K false st sec).queries primW primWS = 1 := by
  simp [hkdfOrRoC, letV, bindV, Comp.queries]

@[simp] theorem acceptKeysC_queries {Δ : List PT} (inp : Expr pqxdhOps Δ accInpTy) :
    (acceptKeysC inp).queries primW primWS = 7 := rfl

@[simp] theorem initFinishC_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT)
    (bu : Var Γ₃ bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy)) (ekSk : Var Γ₅ (B 32))
    (sc : Var Γ₆ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) true S K st sid bu uE ekSk sc).queries primW primWS =
      5 + (min K S.N_dh) * 10 + (min K S.N_sess_tot) * 8 := by
  simp only [initFinishC, bindV, letV, caseOptV, findMV,
    hkdfOrRoC_true_queries, honestPeerC_queries, checkProvC_queries,
    partnerC_queries, findHonestC_queries,
    queries_qX25519, queries_qX25519Base, queries_sDrKey96,
    Comp.queries]
  omega

@[simp] theorem initFinishC_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT)
    (bu : Var Γ₃ bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy)) (ekSk : Var Γ₅ (B 32))
    (sc : Var Γ₆ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) false S K st sid bu uE ekSk sc).queries primW primWS =
      6 + (min K S.N_dh) * 10 + (min K S.N_sess_tot) * 8 := by
  simp only [initFinishC, bindV, letV, caseOptV, findMV,
    hkdfOrRoC_false_queries, honestPeerC_queries, checkProvC_queries,
    partnerC_queries, findHonestC_queries,
    queries_qX25519, queries_qX25519Base, queries_sDrKey96,
    Comp.queries]
  omega

@[simp] theorem preCheckC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT)
    (u : Var Γ₃ .nat) (bu : Var Γ₄ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (preCheckC (Δ := Δ) S K st sid u bu).queries primW primWS = 3 + (min K S.N_dh) * 6 := by
  simp only [preCheckC, caseOptV, bindV, koskBundleOkC_queries, Comp.queries]
  omega

@[simp] theorem checkSigsC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkSigsC (Δ := Δ) S K st bu).queries primW primWS = 2 + (min K S.N_dh) * 2 := by
  simp only [checkSigsC, bindV, resolveSigPkC_queries, queries_qSigVerify, Comp.queries]
  omega

@[simp] theorem extractC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (extractC (Δ := Δ) S K s bu).queries sigPrimW sigWS = 2 + (min K S.N_dh) * 2 := by
  simp only [extractC, bindV, letV, queries_liftBase, honestPeerC_queries,
    queries_qSigVerify, Comp.queries]
  omega

@[simp] theorem onGame_queries {Γ₁ Δ : List PT} (s : Var Γ₁ sigStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS) :
    (onGame (Δ := Δ) s br).queries sigPrimW sigWS = (br .zero).queries primW primWS := by
  simp [onGame, bindV, letV, queries_liftBase, Comp.queries]

@[simp] theorem onBase_queries {Γ₁ Δ : List PT} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS) :
    (onBase (Δ := Δ) s br).queries primW primWS = (br .zero).queries primW primWS := by
  simp [onBase, bindV, letV, Comp.queries]

@[simp] theorem initPrinB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrinB (Δ := Δ) K st u).queries primW primWS = 2 := by
  simp [initPrinB, bindV, Comp.queries]

@[simp] theorem corruptB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (corruptB (Δ := Δ) K st u).queries primW primWS = 0 := by
  simp [corruptB, caseOptV, Comp.queries]

@[simp] theorem genSpkB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genSpkB (Δ := Δ) K st x).queries primW primWS = 4 := by
  simp [genSpkB, caseOptV, bindV, Comp.queries]

@[simp] theorem genOpkB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genOpkB (Δ := Δ) K st x).queries primW primWS = 1 := by
  simp [genOpkB, bindV, Comp.queries]

@[simp] theorem initiateOpkB_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initiateOpkB (Δ := Δ) true S K st x).queries primW primWS =
      11 + (min K S.N_dh) * 18 + (min K S.N_sess_tot) * 8 := by
  simp only [initiateOpkB, initiateC, letV, bindV, caseOptV,
    koskBundleOkC_queries, resolveSigPkC_queries, initFinishC_true_queries,
    queries_sBytes32, queries_qSigVerify, queries_qKemEncaps, Comp.queries]
  omega

@[simp] theorem initiateOpkB_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initiateOpkB (Δ := Δ) false S K st x).queries primW primWS =
      12 + (min K S.N_dh) * 18 + (min K S.N_sess_tot) * 8 := by
  simp only [initiateOpkB, initiateC, letV, bindV, caseOptV,
    koskBundleOkC_queries, resolveSigPkC_queries, initFinishC_false_queries,
    queries_sBytes32, queries_qSigVerify, queries_qKemEncaps, Comp.queries]
  omega

@[simp] theorem initiateNoOpkB_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initiateNoOpkB (Δ := Δ) true S K st x).queries primW primWS =
      11 + (min K S.N_dh) * 18 + (min K S.N_sess_tot) * 8 := by
  simp only [initiateNoOpkB, initiateC, letV, bindV, caseOptV,
    koskBundleOkC_queries, resolveSigPkC_queries, initFinishC_true_queries,
    queries_sBytes32, queries_qSigVerify, queries_qKemEncaps, Comp.queries]
  omega

@[simp] theorem initiateNoOpkB_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initiateNoOpkB (Δ := Δ) false S K st x).queries primW primWS =
      12 + (min K S.N_dh) * 18 + (min K S.N_sess_tot) * 8 := by
  simp only [initiateNoOpkB, initiateC, letV, bindV, caseOptV,
    koskBundleOkC_queries, resolveSigPkC_queries, initFinishC_false_queries,
    queries_sBytes32, queries_qSigVerify, queries_qKemEncaps, Comp.queries]
  omega

@[simp] theorem acceptOpkB_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (acceptOpkB (Δ := Δ) true S K st x).queries primW primWS = 13 + (min K S.N_dh) * 14 := by
  simp only [acceptOpkB, letV, bindV, caseOptV,
    koskSenderOkC_queries, acceptKeysC_queries, hkdfOrRoC_true_queries,
    findHonestC_queries, recordRespC_queries,
    queries_qKemDecaps, queries_qX25519, Comp.queries]
  omega

@[simp] theorem acceptOpkB_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (acceptOpkB (Δ := Δ) false S K st x).queries primW primWS = 14 + (min K S.N_dh) * 14 := by
  simp only [acceptOpkB, letV, bindV, caseOptV,
    koskSenderOkC_queries, acceptKeysC_queries, hkdfOrRoC_false_queries,
    findHonestC_queries, recordRespC_queries,
    queries_qKemDecaps, queries_qX25519, Comp.queries]
  omega

@[simp] theorem acceptNoOpkB_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (acceptNoOpkB (Δ := Δ) true S K st x).queries primW primWS = 12 + (min K S.N_dh) * 14 := by
  simp only [acceptNoOpkB, letV, bindV, caseOptV,
    koskSenderOkC_queries, acceptKeysC_queries, hkdfOrRoC_true_queries,
    findHonestC_queries, recordRespC_queries,
    queries_qKemDecaps, queries_qX25519, Comp.queries]
  omega

@[simp] theorem acceptNoOpkB_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (acceptNoOpkB (Δ := Δ) false S K st x).queries primW primWS = 13 + (min K S.N_dh) * 14 := by
  simp only [acceptNoOpkB, letV, bindV, caseOptV,
    koskSenderOkC_queries, acceptKeysC_queries, hkdfOrRoC_false_queries,
    findHonestC_queries, recordRespC_queries,
    queries_qKemDecaps, queries_qX25519, Comp.queries]
  omega

@[simp] theorem testB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (testB (Δ := Δ) K st sid).queries primW primWS = 0 := by
  simp [testB, caseOptV, Comp.queries]

@[simp] theorem revealB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (revealB (Δ := Δ) K st sid).queries primW primWS = 0 := by
  simp [revealB, caseOptV, Comp.queries]

@[simp] theorem roB_queries (useRo : Bool) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roB (Δ := Δ) useRo K st sec).queries primW primWS = 0 := by
  cases useRo <;> simp [roB, bindV, Comp.queries]

@[simp] theorem revealDhB_queries (useRo : Bool) (K : Nat) {Γ₁ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) [Ext Γ₁ Δ] :
    (revealDhB (Δ := Δ) useRo K st).queries primW primWS = 0 := by
  cases useRo <;> simp [revealDhB, Comp.queries]

@[simp] theorem registerB_queries {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (registerB (Δ := Δ) st sk).queries primW primWS = 2 := by
  simp [registerB, bindV, Comp.queries]

@[simp] theorem revealSpkB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (revealSpkB (Δ := Δ) K st x).queries primW primWS = 0 := by
  simp [revealSpkB, caseOptV, Comp.queries]

@[simp] theorem sigInitPrinB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigInitPrinB (Δ := Δ) K s u).queries sigPrimW sigWS = 2 := by
  simp [sigInitPrinB, bindV, Comp.queries]

@[simp] theorem sigCorruptB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigCorruptB (Δ := Δ) K s u).queries sigPrimW sigWS = 0 := by
  simp [sigCorruptB, caseOptV, Comp.queries]

@[simp] theorem sigGenSpkB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigGenSpkB (Δ := Δ) K s x).queries sigPrimW sigWS = 4 := by
  simp [sigGenSpkB, caseOptV, bindV, Comp.queries]

@[simp] theorem sigInitiateB_true_queries (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigInitiateB (Δ := Δ) true S K opk s x).queries sigPrimW sigWS =
      13 + (min K S.N_dh) * 20 + (min K S.N_sess_tot) * 8 := by
  cases opk <;> (
    simp only [sigInitiateB, letV, bindV, queries_liftBase, extractC_queries,
      initiateOpkB_true_queries, initiateNoOpkB_true_queries, Comp.queries,
      ↓reduceIte, Bool.false_eq_true]
    omega)

@[simp] theorem sigInitiateB_false_queries (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigInitiateB (Δ := Δ) false S K opk s x).queries sigPrimW sigWS =
      14 + (min K S.N_dh) * 20 + (min K S.N_sess_tot) * 8 := by
  cases opk <;> (
    simp only [sigInitiateB, letV, bindV, queries_liftBase, extractC_queries,
      initiateOpkB_false_queries, initiateNoOpkB_false_queries, Comp.queries,
      ↓reduceIte, Bool.false_eq_true]
    omega)

@[simp] theorem shcrGenSpkB_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrGenSpkB (Δ := Δ) S K s x).queries primW primWS = 4 := by
  simp [shcrGenSpkB, caseOptV, bindV, Comp.queries]

@[simp] theorem shcrInitiateC_queries (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrInitiateC (Δ := Δ) S K opk s x).queries primW primWS =
      11 + (min K S.N_dh) * 18 + (min K S.N_sess_tot) * 8 := by
  simp only [shcrInitiateC, letV, bindV, caseOptV,
    preCheckC_queries, checkSigsC_queries, initFinishC_true_queries,
    queries_sBytes32, queries_qKemEncaps, Comp.queries]
  omega

@[simp] theorem shcrAcceptB_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K true s x).queries primW primWS = 14 + (min K S.N_dh) * 14 := by
  simp only [shcrAcceptB, bindV, caseOptV, onBase_queries, acceptOpkB_true_queries,
    queries_qKemDecaps, Comp.queries, ↓reduceIte]
  omega

@[simp] theorem shcrAcceptB_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrAcceptB (Δ := Δ) S K false s x).queries primW primWS = 13 + (min K S.N_dh) * 14 := by
  simp only [shcrAcceptB, bindV, caseOptV, onBase_queries, acceptNoOpkB_true_queries,
    queries_qKemDecaps, Comp.queries, Bool.false_eq_true, ↓reduceIte]
  omega

/- The two `useRo` branches are split to keep kernel checking within memory limits. -/

theorem sigHandleC_queries_le_false (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigHandleC (Δ := Δ) false S K s q).queries sigPrimW sigWS ≤
      (min K S.N_dh) * 20 + (min K S.N_sess_tot) * 8 + 17 := by
  simp only [sigHandleC, caseSumV, onGame_queries,
    sigInitPrinB_queries, sigCorruptB_queries, sigGenSpkB_queries, genOpkB_queries,
    sigInitiateB_false_queries, acceptOpkB_false_queries, acceptNoOpkB_false_queries,
    testB_queries, roB_queries, revealDhB_queries, revealB_queries,
    registerB_queries, revealSpkB_queries, Comp.queries]
  omega

theorem sigHandleC_queries_le_true (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigHandleC (Δ := Δ) true S K s q).queries sigPrimW sigWS ≤
      (min K S.N_dh) * 20 + (min K S.N_sess_tot) * 8 + 17 := by
  simp only [sigHandleC, caseSumV, onGame_queries,
    sigInitPrinB_queries, sigCorruptB_queries, sigGenSpkB_queries, genOpkB_queries,
    sigInitiateB_true_queries, acceptOpkB_true_queries, acceptNoOpkB_true_queries,
    testB_queries, roB_queries, revealDhB_queries, revealB_queries,
    registerB_queries, revealSpkB_queries, Comp.queries]
  omega

theorem sigHandleC_queries_le (useRo : Bool) (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ sigStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigHandleC (Δ := Δ) useRo S K s q).queries sigPrimW sigWS ≤
      (min K S.N_dh) * 20 + (min K S.N_sess_tot) * 8 + 17 := by
  cases useRo
  · exact sigHandleC_queries_le_false S K s q
  · exact sigHandleC_queries_le_true S K s q

theorem sigKeyIndProg_handle_primQueries_le (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).handle.queries sigPrimW sigWS ≤
      (min K S.N_dh) * 20 + (min K S.N_sess_tot) * 8 + 17 :=
  sigHandleC_queries_le useRo S K (Γ₁ := [sigStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [sigStTy, keyIndQueryTy]) .zero .zero

theorem sigKeyIndProg_init_primQueries (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).init.queries sigPrimW sigWS = 0 := by
  simp [sigKeyIndProg, bindV, queries_liftBase, Comp.queries]

theorem sigKeyIndProg_finish_primQueries (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).finish.queries sigPrimW sigWS = 0 := rfl

theorem sigKeyIndProg_totalPrimQueries_le (useRo : Bool) (S : Setup) (b : QueryBudget) (K : Nat) :
    (sigKeyIndProg useRo S K).totalQueries sigPrimW sigWS b.q_total ≤
      b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 17) := by
  simp only [CostedReduction.totalQueries, sigKeyIndProg_init_primQueries,
    sigKeyIndProg_finish_primQueries, Nat.zero_add, Nat.add_zero]
  have hmd := Nat.min_le_right K S.N_dh
  have hms := Nat.min_le_right K S.N_sess_tot
  exact Nat.mul_le_mul_left _ (le_trans (sigKeyIndProg_handle_primQueries_le useRo S K)
    (by omega))

theorem shcrPostC_queries_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).queries primW primWS ≤
      18 + (min K S.N_dh) * 18 + (min K S.N_sess_tot) * 8 := by
  simp only [shcrPostC, caseSumV, onBase_queries,
    initPrinB_queries, corruptB_queries, shcrGenSpkB_queries, genOpkB_queries,
    shcrInitiateC_queries, shcrAcceptB_true_queries, shcrAcceptB_false_queries,
    testB_queries, roB_queries, revealDhB_queries, revealB_queries,
    registerB_queries, revealSpkB_queries, Comp.queries]
  omega

theorem shcrKeyIndProg_handlePost_primQueries_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePost.queries primW primWS ≤
      16 * (4 * (min K S.N_dh) + (min K S.N_sess_tot) + 4) :=
  (shcrPostC_queries_le S K (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).trans (by omega)

theorem shcrPreC_queries_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPreC (Δ := Δ) S K s q).queries primW primWS ≤
      16 * (4 * (min K S.N_dh) + (min K S.N_sess_tot) + 4) := by
  simp only [shcrPreC, pauseCheckC, tryPauseC,
    preCheckC_queries, checkSigsC_queries,
    bindV, letV, caseOptV, caseSumV, Comp.queries]
  have hPost := shcrPostC_queries_le S K (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := (.opt pauseTy) :: Δ) s q
  omega

theorem shcrKeyIndProg_handlePre_primQueries_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePre.queries primW primWS ≤
      16 * (4 * (min K S.N_dh) + (min K S.N_sess_tot) + 4) :=
  shcrPreC_queries_le S K (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero

theorem shcrResumeC_queries_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (p : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (shcrResumeC (Δ := Δ) S K sc p s).queries primW primWS ≤
      16 * (4 * (min K S.N_dh) + (min K S.N_sess_tot) + 4) := by
  simp only [shcrResumeC, letV, bindV, initFinishC_true_queries, queries_sBytes32, Comp.queries]
  omega

theorem shcrKeyIndProg_resume_primQueries_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).resume.queries primW primWS ≤
      16 * (4 * (min K S.N_dh) + (min K S.N_sess_tot) + 4) :=
  shcrResumeC_queries_le S K (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₂ := [pauseTy, .prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)]) .zero .zero .zero

theorem shcrExtractC_queries (Q : Nat) {Γ₁ Γ₃ Δ : List PT}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₃ Δ] :
    (shcrExtractC (Δ := Δ) Q sc s).queries primW primWS = Q := by
  simp only [shcrExtractC, bindV, findMV, queries_qKemDecaps, Comp.queries]
  omega

theorem shcrKeyIndProg_finish_primQueries (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).finish.queries primW primWS = Q :=
  shcrExtractC_queries Q (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) .zero .zero

theorem shcrKeyIndProg_init_primQueries (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).init.queries primW primWS = 0 := by
  dsimp only [shcrKeyIndProg]
  split <;> simp [bindV, Comp.queries]

theorem shcrKeyIndProg_chDone_primQueries (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).chDone.queries primW primWS = 0 := rfl

theorem shcrKeyIndProg_totalQueries_le (S : Setup) (b : QueryBudget) (K : Nat) :
    (shcrKeyIndProg S b.q_total K).totalQueries primW primWS b.q_total ≤ primQueryBudget S b := by
  have h1 := shcrKeyIndProg_handlePre_primQueries_le S b.q_total K
  have h2 := shcrKeyIndProg_handlePost_primQueries_le S b.q_total K
  have h3 := shcrKeyIndProg_resume_primQueries_le S b.q_total K
  simp only [TwoStageCostedReduction.totalQueries, primQueryBudget,
    shcrKeyIndProg_finish_primQueries, shcrKeyIndProg_init_primQueries,
    shcrKeyIndProg_chDone_primQueries]
  have hm : max ((shcrKeyIndProg S b.q_total K).handlePre.queries primW primWS)
      ((shcrKeyIndProg S b.q_total K).handlePost.queries primW primWS) ≤
      16 * (4 * S.N_dh + S.N_sess_tot + 4) := by
    have hmd := Nat.min_le_right K S.N_dh
    have hms := Nat.min_le_right K S.N_sess_tot
    exact max_le (le_trans h1 (by omega)) (le_trans h2 (by omega))
  have hMul := Nat.mul_le_mul_left b.q_total hm
  have hResMax : max 0 ((shcrKeyIndProg S b.q_total K).resume.queries primW primWS) =
      (shcrKeyIndProg S b.q_total K).resume.queries primW primWS := Nat.zero_max _
  have h3' : (shcrKeyIndProg S b.q_total K).resume.queries primW primWS ≤
      16 * (4 * S.N_dh + S.N_sess_tot + 4) := by
    have hmd := Nat.min_le_right K S.N_dh
    have hms := Nat.min_le_right K S.N_sess_tot
    exact le_trans h3 (by omega)
  clear h1 h2 h3
  rw [hResMax]
  nlinarith

/-! ## Query-bound soundness and AST size bounds -/

section GRed2QueryBound

variable {Sg : Sig} {O : Ops Sg} {ι : Type} {T : OracleSpec ι} {I : Iface Sg T}

theorem TwoStageCostedReduction.eval1_queryBound {κ : Type} {G : OracleSpec κ} {C : GameCodec Sg G}
    {rIn aIn aOut ch rIn2 out : Ty Sg} (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g) (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote) (x : rIn.denote)
    (fuel : ℕ) (dflt : aOut.denote) :
    (R.eval1 A x fuel dflt).IsQueryBoundP P (R.totalQueries w ws fuel) :=
  (_root_.ReductionDsl.TwoStageCostedReduction.eval1_queryBound R P w ws hw hU A x fuel dflt).mono
    (by
      simp only [TwoStageCostedReduction.totalQueries]
      have := Nat.mul_le_mul_left fuel (Nat.le_max_left (R.handlePre.queries w ws) (R.handlePost.queries w ws))
      omega)

theorem TwoStageCostedReduction.eval2_queryBound {κ : Type} {G : OracleSpec κ} {C : GameCodec Sg G}
    {rIn aIn aOut ch rIn2 out : Ty Sg} (R : TwoStageCostedReduction O I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g) (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote) (y : rIn2.denote)
    (fuel : ℕ) (dflt : aOut.denote) :
    (R.eval2 m y fuel dflt).IsQueryBoundP P (R.totalQueries w ws fuel) :=
  (_root_.ReductionDsl.TwoStageCostedReduction.eval2_queryBound R P w ws hw hU m y fuel dflt).mono
    (by
      simp only [TwoStageCostedReduction.totalQueries]
      have := Nat.mul_le_mul_left fuel (Nat.le_max_right (R.handlePre.queries w ws) (R.handlePost.queries w ws))
      omega)

end GRed2QueryBound

section SizeBounds

@[local simp] private theorem size_liftBase_gen {C : ChallengerOracle}
    {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).size = c.size := by
  induction c <;> simp_all [liftBase, Comp.size, pqChalIface, pqPrimIface]

@[local simp] private theorem size_liftBase {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqxdhEufCmaIface) (liftBase c) = c.size :=
  size_liftBase_gen c

@[local simp] private theorem size_partnerC {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) :
    (partnerC (Δ := Δ) s r).size = 211 := by
  simp only [partnerC, bindV, qPow8, getDBytes, optBytesEq, eLet2, eLet, eCaseOpt,
    eqB, litB, v, Comp.size, Expr.size]
  simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
    Ops.sum, Sum.elim_inl]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1200000 in
theorem sigKeyIndProg_size_le (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).size ≤ 100 * bits K + 12000 := by
  have hInitFin : (sigKeyIndProg useRo S K).init.size + (sigKeyIndProg useRo S K).finish.size ≤
      bits K + 100 := by
    dsimp only [sigKeyIndProg]
    have hbMin : bits (min K S.N_spk_tot) ≤ bits K :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    have hbMin' : bits (K.min S.N_spk_tot) ≤ bits K :=
      _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    split <;> {
      simp only [emptyStE, stMk, sgForgery, eCaseOpt, liftBase,
        bindV, v, litB, sBool, sIndex, Comp.size, Expr.size, bits_0]
      simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
        _root_.SignalPqxdh.LegacyCosted.pqBytesOps, Ops.sum, Sum.elim_inl]
      omega
    }
  have hHandle : (sigKeyIndProg useRo S K).handle.size ≤ 99 * bits K + 11900 := by
    cases useRo <;> {
      dsimp only [sigKeyIndProg]
      simp (config := { maxSteps := 1000000 }) only [
        sigHandleC, sigInitPrinB, sigCorruptB, sigGenSpkB, sigInitiateB, onGame, extractC, widenEC,
        sgGame, sgTarget, sgPk, sgForgery, sgBudget, sgUpd,
        initPrinB, corruptB, genSpkB, genOpkB, initSidE, initFinishC, preCheckC, checkSigsC,
        initiateC, initiateOpkB, initiateNoOpkB, acceptOpkB, acceptNoOpkB,
        testB, revealB, roB, revealDhB, registerB, revealSpkB,
        findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
        resolveSigPkC, honestPeerC, checkProvC, partnerC, recordRespC, hkdfOrRoC,
        aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
        qK, qJ, qO, qHdr, qKJO,
        stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
        stMk, stUpd,
        peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
        sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
        oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
        seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
        seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
        seTested, seRevealed, seMk, seUpd,
        reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
        reTested, reRevealed, reMk, reUpd,
        buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
        hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
        rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rDh, rSpkSk,
        isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE, emptyStE,
        orE, mulRight, natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32,
        buildSecretsE, eLet2,
        liftBase,
        v, bindV, letV, caseOptV, caseSumV, findMV, anyMV,
        eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
        litB, catB, consB, widenB, lenB, eqB, u32OfNat, eqU32,
        sBool, sBytes32, sRandom64, sDrKey96, sIndex,
        qX25519, qX25519Base, qIsCanonical, qPow8,
        qSigPkGen, qSigSign, qSigVerify,
        qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96,
        qChalSign, encEC, encKEM,
        Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false,
        Bool.not_true, Bool.not_false]
      simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps,
        _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops,
        Ops.sum, Sum.elim_inl, Sum.elim_inr]
      have : bits 0 = 1 := bits_0
      have : bits 1 = 1 := bits_1
      have : bits 32 = 6 := bits_32
      have : bits (min K S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
      have : bits (K.min S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
      have : bits (min K S.N_sess_tot) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
      have : bits (K.min S.N_sess_tot) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
      have : bits (min K S.N_spk_tot) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
      have : bits (K.min S.N_spk_tot) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
      omega
    }
  unfold _root_.ReductionDsl.CostedReduction.size
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
private theorem shcrPostC_size_le_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).size ≤ 100 * bits K + 12000 := by
  simp (config := { maxSteps := 500000 }) only [shcrPostC, shcrGenSpkB, initGuardE, shcrInitiateC,
    shcrAcceptB, onBase, scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd,
    initPrinB, corruptB, genSpkB, genOpkB, initSidE, initFinishC, preCheckC, checkSigsC,
    acceptOpkB, acceptNoOpkB, testB, revealB, roB, revealDhB, registerB, revealSpkB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, checkProvC, size_partnerC, recordRespC, hkdfOrRoC,
    aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
    qK, qJ, qO, qHdr, qKJO,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stMk, stUpd, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbMk, sbUpd,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
    seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
    seTested, seRevealed, seMk, seUpd,
    reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
    reTested, reRevealed, reMk, reUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rSpkSk,
    isSomeE, isNoneRespE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE,
    orE, natEq, nat2Eq, nat3Eq, optU32Eq, sidEq, kyberEq, nonZero32,
    buildSecretsE, eLet2, shcrFinE,
    bindV, letV, caseOptV, caseSumV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap, v,
    litB, catB, consB, widenB, lenB, eqB, u32OfNat, eqU32,
    sBytes32, sRandom64, sDrKey96,
    qX25519, qX25519Base, qIsCanonical, qPow8, qSigPkGen, qSigSign, qSigVerify,
    qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96, encEC, encKEM,
    Comp.size, Expr.size, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
  simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
    _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Ops.sum, Sum.elim_inl, Sum.elim_inr]
  have : bits 0 = 1 := bits_0
  have : bits 1 = 1 := bits_1
  have : bits 32 = 6 := bits_32
  have : bits (min K S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
  have : bits (K.min S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
  have : bits (min K S.N_sess_tot) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
  have : bits (K.min S.N_sess_tot) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
  omega

private theorem shcrPreC_size_le_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPreC (Δ := Δ) S K s q).size ≤ 130 * bits K + 14500 := by
  have hPost := shcrPostC_size_le_tight S K (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := .opt pauseTy :: Δ) s q
  have hPC : (pauseCheckC (Δ := Δ) S K s q).size ≤ 30 * bits K + 2000 := by
    simp only [pauseCheckC, tryPauseC, initGuardE, initSidE, preCheckC, checkSigsC,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, resolveSigPkC,
      scBase, scCnt, scSIdx,
      stPrin, stSpks, stOpks, stSess, stAdv,
      peIkAPk, peIkSignPk, sbSpkPk, oeOpkPk, seSid,
      buIkB, buSpkB, buSpkSig, buOpkB, buPqspkB, buPqspkSig,
      isSomeE,
      orE, natEq, nat2Eq, nat3Eq, sidEq, eLet2,
      bindV, letV, caseOptV, caseSumV, findMV, anyMV, eLet, eCaseOpt, eCaseSum, eFind, eAny, v,
      consB, eqB, qPow8, qSigVerify, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      Ops.sum, Sum.elim_inl]
    have : bits (min K S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    have : bits (K.min S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    omega
  simp only [shcrPreC, bindV, caseOptV, buPqspkB, v, Comp.size, Expr.size]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem shcrKeyIndProg_size_le_tight (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).size ≤ bits Q + 265 * bits K + 29000 := by
  have hPre : (shcrKeyIndProg S Q K).handlePre.size ≤ 130 * bits K + 14500 :=
    shcrPreC_size_le_tight S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hPost : (shcrKeyIndProg S Q K).handlePost.size ≤ 100 * bits K + 12000 :=
    shcrPostC_size_le_tight S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
      (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hInit : (shcrKeyIndProg S Q K).init.size ≤ 100 := by
    dsimp only [shcrKeyIndProg]
    split <;> {
      simp only [emptyStE, stMk, scMk, bindV, v, sBool, sIndex, Comp.size, Expr.size, bits_0]
      omega
    }
  have hRest : (shcrKeyIndProg S Q K).chDone.size +
      (shcrKeyIndProg S Q K).resume.size + (shcrKeyIndProg S Q K).finish.size ≤
      bits Q + 35 * bits K + 1900 := by
    dsimp only [shcrKeyIndProg]
    simp (config := { maxSteps := 500000 }) only [
      shcrResumeC, shcrExtractC, shcrFinE,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd, rrCt,
      initFinishC, findHonestC, honestPeerC, checkProvC, size_partnerC, hkdfOrRoC,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd, peSecIKA0, peIkAPk, peCorrupted,
      sbSpkPk, sbPqspkPk, oeOpkPk,
      seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
      seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seHdr,
      seTested, seRevealed, seMk, seUpd, reDrRand,
      buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB,
      hdMk, rHdr, rInitUnfresh,
      isSomeE, getDBytes, optBytesEq, optFst, optSnd, rs,
      orE, natEq, buildSecretsE, eLet2,
      bindV, letV, caseOptV, findMV, anyMV, eLet, eCaseOpt, eFind, eAny, v,
      litB, catB, widenB, eqB,
      sBytes32, sDrKey96,
      qX25519, qX25519Base, qPow8, qKemDecaps,
      Comp.size, Expr.size, ↓reduceIte]
    simp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.SignalPqxdh.LegacyCosted.pqBytesOps,
      Ops.sum, Sum.elim_inl]
    have : bits 0 = 1 := bits_0
    have : bits 1 = 1 := bits_1
    have : bits (min K S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    have : bits (K.min S.N_dh) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    have : bits (min K S.N_sess_tot) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    have : bits (K.min S.N_sess_tot) ≤ bits K := _root_.ReductionDsl.bits_mono (Nat.min_le_left _ _)
    omega
  unfold _root_.ReductionDsl.TwoStageCostedReduction.size
  omega

theorem keyIndLoopBound_le_security_stepCostBudget (S : Setup) (b : QueryBudget) :
    keyIndLoopBound b ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by
  unfold keyIndLoopBound _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  have : 2 * b.q_total + 1 ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) := by
    have : 1 ≤ b.q_total + 1 := by omega
    have hmul := Nat.mul_le_mul_left (2 ^ 16 * (b.q_total + 1)) this
    omega
  omega

theorem sigKeyIndProg_size_le_stepCostBudget (useRo : Bool) (S : Setup) (b : QueryBudget)
    (K : Nat) (hK : K ≤ keyIndLoopBound b) :
    (sigKeyIndProg useRo S K).size ≤
      12000 + 100 * bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have h1 := sigKeyIndProg_size_le useRo S K
  have h2 : bits K ≤ bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
    _root_.ReductionDsl.bits_mono (hK.trans (keyIndLoopBound_le_security_stepCostBudget S b))
  omega

theorem shcrKeyIndProg_size_le_stepCostBudget (S : Setup) (b : QueryBudget)
    (K : Nat) (hK : K ≤ keyIndLoopBound b) :
    (shcrKeyIndProg S b.q_total K).size ≤
      29000 + 266 * bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have h1 := shcrKeyIndProg_size_le_tight S b.q_total K
  have hq : b.q_total ≤ keyIndLoopBound b := by unfold keyIndLoopBound; omega
  have hbQ : bits b.q_total ≤ bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
    _root_.ReductionDsl.bits_mono (hq.trans (keyIndLoopBound_le_security_stepCostBudget S b))
  have hbK : bits K ≤ bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
    _root_.ReductionDsl.bits_mono (hK.trans (keyIndLoopBound_le_security_stepCostBudget S b))
  omega

end SizeBounds

end SignalPqxdh.Security.ReductionDsl.KeyInd

