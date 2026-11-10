/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeSig

/-!
# Cost and Query Bounds for the `Auth` Handshake Reductions

Shared expression and computation cost/query lemmas for `AuthHs`, together with syntactic cost and
primitive-query bounds and a potential-based challenger signing-query bound for
`sigReductionAuthProg`.
-/

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

attribute [local simp] Expr.cost Comp.cost Expr.costUB Comp.costUB

/-- Polynomial step-cost budget granted to black-box reductions in `ReductionDsl`. -/
def stepCostBudget (S : Setup) (b : QueryBudget) : Nat :=
  2 ^ 16 * (b.q_total + 1) * (b.q_total + S.N_dh + S.N_sess_tot + 1) +
    2 ^ 11 * S.N_dh ^ 2 + 2 ^ 8 * S.N_dh * S.N_sess_tot

/-! ## Shared leaf cost lemmas -/

@[simp] theorem bits_0 : bits 0 = 1 := by decide
@[simp] theorem bits_1 : bits 1 = 1 := by decide
@[simp] theorem bits_2 : bits 2 = 2 := by decide
@[simp] theorem bits_3 : bits 3 = 2 := by decide
@[simp] theorem bits_32 : bits 32 = 6 := by decide
@[simp] theorem bits_33 : bits 33 = 6 := by decide

theorem F_X25519_length : F_X25519.length = 32 := by decide

@[simp] theorem cost_v {Γ Δ : List (Ty pqSig)} {τ : Ty pqSig} {_ : Ext Γ Δ} (x : Var Γ τ) :
    (v x : Expr pqxdhOps Δ τ).cost = 1 := rfl
@[simp] theorem costUB_v {Γ Δ : List (Ty pqSig)} {τ : Ty pqSig} {_ : Ext Γ Δ} (x : Var Γ τ) :
    (v x : Expr pqxdhOps Δ τ).costUB = 1 := rfl

@[simp] theorem cost_litBytes {Γ : List (Ty pqSig)} (w : ℕ+) (bs : Bytes) :
    (Expr.litBytes (Γ := Γ) w bs).cost = w.val + bs.length + 1 := by
  simp [Expr.litBytes, pqxdhOps, Ops.sum, pqBytesOps]; omega
@[simp] theorem costUB_litBytes {Γ : List (Ty pqSig)} (w : ℕ+) (bs : Bytes) :
    (Expr.litBytes (Γ := Γ) w bs).costUB = w.val + bs.length + 1 := by
  simp [Expr.litBytes, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem costUB_encEC {Γ : List (Ty pqSig)} (pk : Expr pqxdhOps Γ (B 32)) :
    (encEC pk).costUB = pk.costUB + 33 := by
  simp [encEC, Expr.bytesCons, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem costUB_encKEM {Γ : List (Ty pqSig)} (pk : Expr pqxdhOps Γ (B 1568)) :
    (encKEM pk).costUB = pk.costUB + 1569 := by
  simp [encKEM, Expr.bytesCons, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem eval_bytesWiden_33_1536 {Γ : List (Ty pqSig)}
    (a : Expr pqxdhOps Γ (B 33)) (env : Env Γ) :
    Expr.eval (t := B 1569) (.bytesWiden 33 1536 a) env = a.eval env := rfl
@[simp] theorem cost_bytesWiden_33_1536 {Γ : List (Ty pqSig)} (x : Expr pqxdhOps Γ (B 33)) :
    Expr.cost (t := B 1569) (.bytesWiden 33 1536 x) = x.cost + 1569 := rfl
@[simp] theorem costUB_bytesWiden_33_1536 {Γ : List (Ty pqSig)} (x : Expr pqxdhOps Γ (B 33)) :
    Expr.costUB (t := B 1569) (.bytesWiden 33 1536 x) = x.costUB + 1569 := rfl

@[simp] theorem costUB_bytesTakeK {w : ℕ+} (k : ℕ+) {Γ : List (Ty pqSig)} (x : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesTakeK k x).costUB = x.costUB + w.val + k.val := by
  simp [Expr.bytesTakeK, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem costUB_bytesDrop {w : ℕ+} {Γ : List (Ty pqSig)}
    (n : Expr pqxdhOps Γ .nat) (x : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesDrop n x).costUB = n.costUB + x.costUB + w.val + 2 := by
  simp [Expr.bytesDrop, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem costUB_bytesLen {w : ℕ+} {Γ : List (Ty pqSig)} (x : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesLen x).costUB = x.costUB + bits w.val := by
  simp [Expr.bytesLen, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem costUB_bytesBeq {m n : ℕ+} {Γ : List (Ty pqSig)}
    (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (Expr.bytesBeq a b).costUB = a.costUB + b.costUB + m.val + n.val + 1 := by
  simp [Expr.bytesBeq, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem costUB_u32OfNat {Γ : List (Ty pqSig)} (n : Expr pqxdhOps Γ .nat) :
    (Expr.u32OfNat n).costUB = n.costUB + 1 := by
  simp [Expr.u32OfNat, pqxdhOps, Ops.sum, pqU32Ops]

@[simp] theorem costUB_u32Beq {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ U32) :
    (Expr.u32Beq a b).costUB = a.costUB + b.costUB + 2 := by
  simp [Expr.u32Beq, pqxdhOps, Ops.sum, pqU32Ops]

@[simp] theorem cost_sampleBool {Γ : List (Ty pqSig)} :
    (Comp.sampleBool (Γ := Γ)).cost = 2 := rfl
@[simp] theorem costUB_sampleBool {Γ : List (Ty pqSig)} :
    (Comp.sampleBool (Γ := Γ)).costUB = 2 := rfl
@[simp] theorem cost_sampleBytes32 {Γ : List (Ty pqSig)} :
    (Comp.sampleBytes32 (Γ := Γ)).cost = 34 := rfl
@[simp] theorem costUB_sampleBytes32 {Γ : List (Ty pqSig)} :
    (Comp.sampleBytes32 (Γ := Γ)).costUB = 34 := rfl
@[simp] theorem cost_sampleRandom64 {Γ : List (Ty pqSig)} :
    (Comp.sampleRandom64 (Γ := Γ)).cost = 66 := rfl
@[simp] theorem costUB_sampleRandom64 {Γ : List (Ty pqSig)} :
    (Comp.sampleRandom64 (Γ := Γ)).costUB = 66 := rfl
@[simp] theorem cost_sampleDrKey96 {Γ : List (Ty pqSig)} :
    (Comp.sampleDrKey96 (Γ := Γ)).cost = 98 := rfl
@[simp] theorem costUB_sampleDrKey96 {Γ : List (Ty pqSig)} :
    (Comp.sampleDrKey96 (Γ := Γ)).costUB = 98 := rfl
@[simp] theorem costUB_sampleIndex (N : ℕ) {Γ : List (Ty pqSig)} :
    (Comp.sampleIndex (Γ := Γ) N).costUB = bits N + 2 := by
  simp [Comp.sampleIndex, pqPrimIface, pqSamplers, PSamp.cost]; omega

@[simp] theorem cost_queryPrim {Γ : List (Ty pqSig)} (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrim g e).cost = e.cost + (1 + Ty.wd g.dom + Ty.wd g.cod) := rfl
@[simp] theorem costUB_queryPrim {Γ : List (Ty pqSig)} (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrim g e).costUB = e.costUB + (1 + Ty.wd g.dom + Ty.wd g.cod) := rfl

@[simp] theorem cost_sampleBoolC {C : ChallengerOracle} {Γ : List (Ty pqSig)} :
    (Comp.sampleBoolC (C := C) (Γ := Γ)).cost = 2 := rfl
@[simp] theorem costUB_sampleBoolC {C : ChallengerOracle} {Γ : List (Ty pqSig)} :
    (Comp.sampleBoolC (C := C) (Γ := Γ)).costUB = 2 := rfl
@[simp] theorem cost_sampleBytes32C {C : ChallengerOracle} {Γ : List (Ty pqSig)} :
    (Comp.sampleBytes32C (C := C) (Γ := Γ)).cost = 34 := rfl
@[simp] theorem costUB_sampleBytes32C {C : ChallengerOracle} {Γ : List (Ty pqSig)} :
    (Comp.sampleBytes32C (C := C) (Γ := Γ)).costUB = 34 := rfl
@[simp] theorem cost_sampleRandom64C {C : ChallengerOracle} {Γ : List (Ty pqSig)} :
    (Comp.sampleRandom64C (C := C) (Γ := Γ)).cost = 66 := rfl
@[simp] theorem costUB_sampleRandom64C {C : ChallengerOracle} {Γ : List (Ty pqSig)} :
    (Comp.sampleRandom64C (C := C) (Γ := Γ)).costUB = 66 := rfl
@[simp] theorem cost_sampleDrKey96C {C : ChallengerOracle} {Γ : List (Ty pqSig)} :
    (Comp.sampleDrKey96C (C := C) (Γ := Γ)).cost = 98 := rfl
@[simp] theorem costUB_sampleDrKey96C {C : ChallengerOracle} {Γ : List (Ty pqSig)} :
    (Comp.sampleDrKey96C (C := C) (Γ := Γ)).costUB = 98 := rfl
@[simp] theorem cost_sampleIndexC {C : ChallengerOracle} (N : ℕ) {Γ : List (Ty pqSig)} :
    (Comp.sampleIndexC (C := C) (Γ := Γ) N).cost = bits N + 2 := by
  simp [Comp.sampleIndexC, pqChalIface, pqSamplers, PSamp.cost]; omega
@[simp] theorem costUB_sampleIndexC {C : ChallengerOracle} (N : ℕ) {Γ : List (Ty pqSig)} :
    (Comp.sampleIndexC (C := C) (Γ := Γ) N).costUB = bits N + 2 := by
  simp [Comp.sampleIndexC, pqChalIface, pqSamplers, PSamp.cost]; omega

@[simp] theorem cost_queryPrimC {C : ChallengerOracle} {Γ : List (Ty pqSig)}
    (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrimC (C := C) g e).cost = e.cost + (1 + Ty.wd g.dom + Ty.wd g.cod) := rfl
@[simp] theorem costUB_queryPrimC {C : ChallengerOracle} {Γ : List (Ty pqSig)}
    (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrimC (C := C) g e).costUB = e.costUB + (1 + Ty.wd g.dom + Ty.wd g.cod) := rfl

@[simp] theorem cost_queryChal {C : ChallengerOracle} {Γ : List (Ty pqSig)}
    (g : C.Tag) (e : Expr pqxdhOps Γ (C.dom g)) :
    (Comp.queryChal (C := C) g e).cost = e.cost + C.qCost g := rfl
@[simp] theorem costUB_queryChal {C : ChallengerOracle} {Γ : List (Ty pqSig)}
    (g : C.Tag) (e : Expr pqxdhOps Γ (C.dom g)) :
    (Comp.queryChal (C := C) g e).costUB = e.costUB + C.qCost g := rfl

@[simp] theorem firstMsgADE_costUB {Γ : List (Ty pqSig)} (ikA ikB eph pq : Expr pqxdhOps Γ (B 32)) :
    (firstMsgADE ikA ikB eph pq).costUB =
      ikA.costUB + ikB.costUB + eph.costUB + 3 * pq.costUB + 895 := by
  dsimp only [firstMsgADE, encEC, Expr.bytesAppend, Expr.bytesCons, Expr.litBytes,
    Expr.bytesVarint, Expr.bytesLen, Expr.costUB]
  simp only [pqxdhOps, Ops.sum, pqBytesOps, Sum.elim_inl, PNat.add_coe, PNat.val_ofNat,
    List.length_cons, List.length_nil, bits_0, bits_32, bits_33]
  omega

@[simp] theorem buildSecretsE_costUB {Γ : List (Ty pqSig)} (dh1 dh2 dh3 : Expr pqxdhOps Γ (B 32))
    (dh4? : Expr pqxdhOps Γ (.opt (B 32))) (ss : Expr pqxdhOps Γ (B 32)) :
    (buildSecretsE dh1 dh2 dh3 dh4? ss).costUB =
      dh1.costUB + dh2.costUB + dh3.costUB + dh4?.costUB + ss.costUB + 1459 := by
  dsimp only [buildSecretsE, eLet2, eLet, eCaseOpt, Expr.bytesWiden, Expr.bytesAppend,
    Expr.litBytes, v, Expr.costUB]
  simp only [pqxdhOps, Ops.sum, pqBytesOps, Sum.elim_inl, PNat.add_coe, PNat.val_ofNat, F_X25519_length]
  omega

@[simp] theorem sidEq_costUB {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ sessionIdTy) :
    (sidEq a b).costUB = a.costUB + b.costUB + 105 := by
  simp only [sidEq, eLet2, eLet, eCaseSum, nat2Eq, nat3Eq, natEq, costUB_v, Expr.costUB]

@[simp] theorem optU32Eq_costUB {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ (.opt .u32)) :
    (optU32Eq a b).costUB = a.costUB + b.costUB + 21 := by
  simp only [optU32Eq, eLet2, eLet, eCaseOpt, costUB_u32Beq, costUB_v, Expr.costUB]

@[simp] theorem optBytesEq_costUB {w : ℕ+} {Γ : List (Ty pqSig)} (a b : Expr pqxdhOps Γ (.opt (B w))) :
    (optBytesEq a b).costUB = a.costUB + b.costUB + 2 * w.val + 20 := by
  simp only [optBytesEq, eLet2, eLet, eCaseOpt, costUB_bytesBeq, costUB_v, Expr.costUB]
  omega

@[simp] theorem kyberEq_costUB {Γ : List (Ty pqSig)}
    (a b : Expr pqxdhOps Γ (.prod .nat (.prod .u32 (.prod .u32 (B 32))))) :
    (kyberEq a b).costUB = 4 * a.costUB + 4 * b.costUB + 91 := by
  simp only [kyberEq, natEq, costUB_u32Beq, costUB_bytesBeq, Expr.costUB, PNat.val_ofNat]
  omega

@[simp] theorem kyberCheckE_costUB {Γ : List (Ty pqSig)} (K : Nat)
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod .u32 (.prod .u32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod .u32 (.prod .u32 (B 32))))) :
    (kyberCheckE K used entry).costUB = used.costUB + entry.costUB + K * 100 + 19 := by
  simp only [kyberCheckE, eLet2, eLet, eAny, kyberEq_costUB, costUB_v, Expr.costUB]
  omega

@[simp] theorem bytes2Eq_costUB {w₁ w₂ : ℕ+} {Γ : List (Ty pqSig)}
    (a b : Expr pqxdhOps Γ (.prod (B w₁) (B w₂))) :
    (bytes2Eq a b).costUB = 2 * a.costUB + 2 * b.costUB + 2 * w₁.val + 2 * w₂.val + 7 := by
  simp only [bytes2Eq, costUB_bytesBeq, Expr.costUB]
  omega

@[simp] theorem findHonestC_costUB (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).costUB = ik.costUB + min K S.N_dh * 206 + 7 := by
  simp only [findHonestC, letV, findMV, bindV, stPrin, peIkAPk, Comp.costUB_letC,
    costUB_queryPrim, costUB_bytesBeq, costUB_v, Comp.costUB, Expr.costUB, Ty.wd, PNat.val_ofNat]
  omega

@[simp] theorem isAdvRegC_costUB (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).costUB = pk.costUB + K * 69 + 85 := by
  simp only [isAdvRegC, bindV, eAny, stAdv, costUB_queryPrim, costUB_bytesBeq,
    costUB_v, Comp.costUB, Expr.costUB, Ty.wd, PNat.val_ofNat]
  omega

@[simp] theorem isGameSpkC_costUB (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).costUB = pk.costUB + min K S.N_dh * 206 + 8 := by
  simp only [isGameSpkC, letV, anyMV, bindV, stSpks, sbSpkPk, Comp.costUB_letC,
    costUB_queryPrim, costUB_bytesBeq, costUB_v, Comp.costUB, Expr.costUB, Ty.wd, PNat.val_ofNat]
  omega

@[simp] theorem isGameOpkC_costUB (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).costUB = pk.costUB + min K S.N_dh * 206 + 9 := by
  simp only [isGameOpkC, letV, anyMV, bindV, stOpks, oeOpkPk, Comp.costUB_letC,
    costUB_queryPrim, costUB_bytesBeq, costUB_v, Comp.costUB, Expr.costUB, Ty.wd, PNat.val_ofNat]
  omega

@[simp] theorem koskBundleOkC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).costUB = 341 + min K S.N_dh * 618 + K * 207 := by
  simp only [koskBundleOkC, bindV, caseOptV, findHonestC_costUB, isAdvRegC_costUB,
    isGameSpkC_costUB, isGameOpkC_costUB, isSomeE, buIkB, buSpkB, buOpkB,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem koskSenderOkC_costUB (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).costUB = ik.costUB + 106 + min K S.N_dh * 206 + K * 69 := by
  simp only [koskSenderOkC, letV, bindV, findHonestC_costUB, isAdvRegC_costUB,
    isSomeE, Comp.costUB_letC, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem resolveSigPkC_costUB (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).costUB = ik.costUB + 21 + min K S.N_dh * 206 := by
  simp only [resolveSigPkC, letV, bindV, findHonestC_costUB, eCaseOpt, peIkSignPk,
    Comp.costUB_letC, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem honestPeerC_costUB (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).costUB = ik.costUB + 24 + min K S.N_dh * 206 := by
  simp only [honestPeerC, bindV, findHonestC_costUB, eCaseOpt, peCorrupted,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem hkdfOrRoC_true_costUB (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K true st sec).costUB = sec.costUB + 162 + K * 389 := by
  simp only [hkdfOrRoC, letV, caseOptV, bindV, eFind, stRo, Comp.costUB_letC,
    costUB_sampleDrKey96, costUB_bytesBeq, costUB_v, Comp.costUB, Expr.costUB,
    PNat.val_ofNat, ↓reduceIte]
  omega

@[simp] theorem rootRoC_costUB (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) :
    (rootRoC K st rk dh).costUB = rk.costUB + dh.costUB + 141 + K * 142 := by
  simp only [rootRoC, letV, caseOptV, bindV, eFind, stRoot, bytes2Eq_costUB,
    Comp.costUB_letC, costUB_sampleBytes32, costUB_v, Comp.costUB, Expr.costUB, PNat.val_ofNat]
  omega

@[simp] theorem pqChalIface_uCost (C : ChallengerOracle) : (pqChalIface C).uCost = 1 := rfl
@[simp] theorem pqPrimIface_uCost : pqPrimIface.uCost = 1 := rfl
@[simp] theorem authCodec_codecCost (S : Setup) : (authCodec S).codecCost = 32 := rfl

@[simp] theorem cost_queryChal_sigFrag {Γ : List (Ty pqSig)} (m : ℕ+) (e : Expr pqxdhOps Γ (B m)) :
    (Comp.queryChal (C := eufCmaSignOracle) m e).cost = e.cost + (1 + m.val + 64) := rfl
@[simp] theorem costUB_queryChal_sigFrag {Γ : List (Ty pqSig)} (m : ℕ+) (e : Expr pqxdhOps Γ (B m)) :
    (Comp.queryChal (C := eufCmaSignOracle) m e).costUB = e.costUB + (1 + m.val + 64) := rfl

/-! ## Syntactic cost bounds for `sigReductionAuthProg` -/

@[simp] theorem initPrinB_costUB (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrinB (Δ := Δ) K st u).costUB = 419 + 5 * K := by
  simp only [initPrinB, bindV, eAny, natEq,
    stPrin, stSecb, stHasWon, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    peMk, aNone, aInitPrin, rs, costUB_sampleBytes32, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem corruptB_costUB (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (corruptB (Δ := Δ) K st u).costUB = 212 + 38 * K := by
  simp only [corruptB, caseOptV, eFind, eMap, natEq,
    stPrin, stSecb, stHasWon, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peMk, peUpd,
    aNone, aCorr, rs, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem genSpkB_costUB (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genSpkB (Δ := Δ) K st x).costUB = 8909 + 20 * K := by
  simp only [genSpkB, bindV, caseOptV, eAny, eFind, nat2Eq, natEq,
    stPrin, stSpks, stSecb, stHasWon, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    peIkAPk, peSecIKAsign, buMk, sbMk, aNone, aBundle, rs,
    costUB_encEC, costUB_encKEM, costUB_u32OfNat,
    costUB_sampleBytes32, costUB_sampleRandom64, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem genOpkB_costUB (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genOpkB (Δ := Δ) K st x).costUB = 314 + 25 * K := by
  simp only [genOpkB, bindV, eAny, nat3Eq, nat2Eq, natEq,
    stOpks, stSecb, stHasWon, stPrin, stSpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    oeMk, aNone, aPk, rs, costUB_sampleBytes32, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem registerB_costUB {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (registerB (Δ := Δ) st sk).costUB = 350 := by
  simp only [registerB, bindV, natEq,
    stAdv, stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stMk, stUpd,
    aNone, aPk, rs, costUB_bytesLen, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, bits_32, costUB_v, Comp.costUB, Expr.costUB]

@[simp] theorem roB_costUB (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roB (Δ := Δ) K st sec).costUB = 349 + 389 * K := by
  simp only [roB, bindV, hkdfOrRoC_true_costUB,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRoot, stAdv, stMk, stUpd,
    aDrKey, rs, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem roRootB_costUB (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roRootB (Δ := Δ) K st x).costUB = 336 + 142 * K := by
  simp only [roRootB, bindV, rootRoC_costUB,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stAdv, stMk, stUpd,
    aRootKdf, rs, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem sendC_costUB (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sendC (Δ := Δ) S K opk st x).costUB =
      (if opk then 11893 else 11894) + 4093 * K + 1030 * min K S.N_dh := by
  cases opk <;>
  · simp only [sendC, koskBundleOkC_costUB, resolveSigPkC_costUB, findHonestC_costUB,
      hkdfOrRoC_true_costUB, rootRoC_costUB, firstMsgADE_costUB, buildSecretsE_costUB, sidEq_costUB,
      bindV, letV, caseOptV, eFind, eAny, eCaseOpt, Comp.costUB_letC,
      natEq, getDBytes, optFst, optSnd,
      stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
      stSOE, stSNE, stROE, stRNE, stAdv, stMk, stUpd,
      seMk, peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig,
      hdMk, aNone, aSendFresh, aSendUnfresh, rs,
      costUB_encEC, costUB_encKEM, costUB_bytesLen, costUB_bytesBeq, costUB_litBytes,
      costUB_sampleBytes32, costUB_queryPrim,
      Ty.wd, PNat.val_ofNat, List.length_nil, bits_32,
      Bool.false_eq_true, ite_true, ite_false, costUB_v, Comp.costUB, Expr.costUB]
    omega

@[simp] theorem sendB_costUB (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sendB (Δ := Δ) S K opk st x).costUB = 11912 + 4093 * K + 1030 * min K S.N_dh := by
  cases opk <;>
  · simp only [sendB, sendC_costUB, isSomeE, buOpkB, aNone, rs,
      Bool.false_eq_true, ite_true, ite_false, costUB_v, Comp.costUB, Expr.costUB]
    omega

@[simp] theorem recvTailC_true_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (recvTailC S K true st x kE bE oSk?).costUB =
      oSk?.costUB + 9147 + 671 * K + 206 * min K S.N_dh := by
  simp only [recvTailC, findHonestC_costUB, hkdfOrRoC_true_costUB, rootRoC_costUB,
    firstMsgADE_costUB, buildSecretsE_costUB, kyberCheckE_costUB,
    bindV, letV, caseOptV, eMap, eCaseOpt, Comp.costUB_letC,
    nat3Eq, nat2Eq, natEq, getDBytes,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stAdv, stMk, stUpd,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbPqspkSk,
    oeOpkSk, oeOpkPk, oeMk, oeUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdPqspkId, hdKemCt,
    aNone, aRecvHonest, aRecvUnfresh, rs,
    costUB_litBytes, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, List.length_nil, ite_true, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem recvTailC_false_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (recvTailC S K false st x kE bE oSk?).costUB =
      oSk?.costUB + 9007 + 631 * K + 206 * min K S.N_dh := by
  simp only [recvTailC, findHonestC_costUB, hkdfOrRoC_true_costUB, rootRoC_costUB,
    firstMsgADE_costUB, buildSecretsE_costUB, kyberCheckE_costUB,
    bindV, letV, caseOptV, eCaseOpt, Comp.costUB_letC,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stAdv, stMk, stUpd,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbPqspkSk,
    hdIkAPk, hdEkAPk, hdSpkId, hdPqspkId, hdKemCt,
    aNone, aRecvHonest, aRecvUnfresh, rs,
    costUB_queryPrim, Ty.wd, PNat.val_ofNat, Bool.false_eq_true, ite_false,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem recvB_true_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (recvB (Δ := Δ) S K true st x).costUB = 9474 + 817 * K + 412 * min K S.N_dh := by
  simp only [recvB, recvTailC_true_costUB, koskSenderOkC_costUB, optU32Eq_costUB,
    bindV, letV, caseOptV, eFind, eAny, Comp.costUB_letC,
    nat3Eq, nat2Eq, natEq,
    stPrin, stSpks, stOpks, stUsedO,
    pmHdr, pmEphAPk, oeOpkSk, oeConsumed,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId,
    aNone, rs, costUB_bytesLen, costUB_u32OfNat, costUB_u32Beq,
    PNat.val_ofNat, bits_32, ite_true, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem recvB_false_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (recvB (Δ := Δ) S K false st x).costUB = 9304 + 752 * K + 412 * min K S.N_dh := by
  simp only [recvB, recvTailC_false_costUB, koskSenderOkC_costUB, optU32Eq_costUB,
    bindV, letV, caseOptV, eFind, eAny, Comp.costUB_letC,
    nat3Eq, nat2Eq, natEq,
    stPrin, stSpks, stUsedN,
    pmHdr, pmEphAPk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId,
    aNone, rs, costUB_bytesLen, costUB_u32OfNat, costUB_u32Beq,
    PNat.val_ofNat, bits_32, Bool.false_eq_true, ite_false, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem wrapC_costUB {Δ : List (Ty pqSig)} (m : Comp pqxdhOps pqPrimIface Δ RS)
    (fg : Expr pqxdhOps (RS :: Δ) (.opt (.prod (B 1569) (B 64))))
    (tp : Expr pqxdhOps (RS :: Δ) .nat) (tpk : Expr pqxdhOps (RS :: Δ) (B 32)) :
    (wrapC m fg tp tpk).costUB = m.costUB + fg.costUB + tp.costUB + tpk.costUB + 11 := by
  simp only [wrapC, bindV, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem extractC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (tp : Var Γ₁ .nat) (tpk : Var Γ₂ (B 32)) (st : Var Γ₃ authStateTy)
    (bu : Var Γ₄ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (extractC (Δ := Δ) S K tp tpk st bu).costUB = 6688 + 3239 * K + 206 * min K S.N_dh := by
  simp only [extractC, bindV, eCaseOpt, eAny, natEq, honestPeerC_costUB,
    stSpks, sbSpkPk, sbPqspkPk, buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig,
    costUB_encEC, costUB_encKEM, costUB_bytesWiden_33_1536, costUB_bytesBeq, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem sigHandleDsl_cost_le (S : Setup) (K : Nat) :
    (sigHandleDsl S K).cost ≤ 76355 + 16915 * K + 3296 * S.N_dh := by
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [
    sigHandleDsl, sigStepC,
    extractC_costUB, wrapC_costUB,
    initPrinB_costUB, corruptB_costUB, genSpkB_costUB, genOpkB_costUB, registerB_costUB,
    roB_costUB, roRootB_costUB, sendB_costUB, recvB_true_costUB, recvB_false_costUB,
    bindV, letV, caseOptV, caseSumV, eFind, eAny, eMap,
    natEq, nat2Eq,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peMk, peUpd,
    sbMk, buMk, aNone, aInitPrin, aBundle,
    Comp.costUB_liftChal, Comp.costUB_letC,
    costUB_encEC, costUB_encKEM, costUB_litBytes, costUB_u32OfNat,
    costUB_sampleBytes32, costUB_sampleRandom64C,
    costUB_queryPrim, costUB_queryPrimC, costUB_queryChal_sigFrag,
    Ty.wd, PNat.val_ofNat, List.length_nil, bits_0, bits_1,
    v, Comp.costUB, Expr.costUB]
  have := Nat.min_le_right K S.N_dh
  omega

theorem sigInitDsl_cost (S : Setup) :
    (sigInitDsl S).cost = 49 + bits S.N_id + bits S.N_spk_tot := by
  simp only [sigInitDsl, emptyAuthStE, stMk, bindV,
    cost_sampleIndexC, cost_sampleBoolC, cost_v, Comp.cost, Expr.cost]
  omega

theorem sigFinishDsl_cost (S : Setup) :
    (sigFinishDsl S).cost = 1644 + bits S.N_id := by
  simp only [sigFinishDsl, eCaseOpt, natEq, cost_litBytes, cost_v,
    Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil, bits_0]
  omega

theorem sigReductionAuthProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (sigReductionAuthProg S b.q_total).totalCost b.q_total ≤ stepCostBudget S b := by
  dsimp only [CostedReduction.totalCost, sigReductionAuthProg, authCodec]
  simp only [pqChalIface_uCost, sigInitDsl_cost, sigFinishDsl_cost]
  have hH := sigHandleDsl_cost_le S b.q_total
  generalize (sigHandleDsl S b.q_total).cost = hc at hH ⊢
  have hMax : max 1 (hc + 32) = hc + 32 := by omega
  rw [hMax]
  have hbId : bits S.N_id ≤ S.N_id + 1 := by
    rcases Nat.eq_zero_or_pos S.N_id with h0 | hpos
    · simp [h0]
    · have := bits_le_self hpos; omega
  have hbSpk : bits S.N_spk_tot ≤ S.N_spk_tot + 1 := by
    rcases Nat.eq_zero_or_pos S.N_spk_tot with h0 | hpos
    · simp [h0]
    · have := bits_le_self hpos; omega
  have hIdDh : S.N_id + S.N_spk_tot ≤ S.N_dh := by
    unfold Setup.N_dh; omega
  unfold stepCostBudget
  generalize b.q_total = q at *
  have hqhc : q * (hc + 32) ≤ q * (76387 + 16915 * q + 3296 * S.N_dh) :=
    Nat.mul_le_mul_left q (by omega)
  nlinarith [Nat.zero_le (q * S.N_dh), Nat.zero_le (q * S.N_sess_tot),
    Nat.zero_le (S.N_dh * S.N_sess_tot)]

/-! ## Shared query weights and bounds -/

def primW : pqPrimIface.Tag → ℕ := fun _ => 1
def primWS : pqPrimIface.smp.Samp → ℕ := fun _ => 0

def sigPrimW : pqxdhEufCmaIface.Tag → ℕ
  | .inl _ => 1
  | .inr _ => 0

def sigChalW : pqxdhEufCmaIface.Tag → ℕ
  | .inl _ => 0
  | .inr _ => 1

def sigWS : pqxdhEufCmaIface.smp.Samp → ℕ := fun _ => 0

@[simp] theorem queries_liftChal_sigPrimW
    {Γ : List (Ty pqSig)} {t : Ty pqSig} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (c.liftChal (C := eufCmaSignOracle)).queries sigPrimW sigWS = c.queries primW primWS :=
  Comp.queries_liftChal sigPrimW sigWS c

@[simp] theorem findHonestC_queries (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).queries primW primWS = min K S.N_dh * 2 := by
  simp [findHonestC, letV, findMV, bindV, Comp.queryPrim, primW, Comp.queries]

@[simp] theorem isAdvRegC_queries (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).queries primW primWS = 1 := by
  simp [isAdvRegC, bindV, Comp.queryPrim, primW, Comp.queries]

@[simp] theorem isGameSpkC_queries (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).queries primW primWS = min K S.N_dh * 2 := by
  simp [isGameSpkC, letV, anyMV, bindV, Comp.queryPrim, primW, Comp.queries]

@[simp] theorem isGameOpkC_queries (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).queries primW primWS = min K S.N_dh * 2 := by
  simp [isGameOpkC, letV, anyMV, bindV, Comp.queryPrim, primW, Comp.queries]

@[simp] theorem koskBundleOkC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).queries primW primWS = 3 + min K S.N_dh * 6 := by
  simp only [koskBundleOkC, bindV, caseOptV, findHonestC_queries, isAdvRegC_queries,
    isGameSpkC_queries, isGameOpkC_queries, Comp.queries]
  omega

@[simp] theorem koskSenderOkC_queries (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).queries primW primWS = 1 + min K S.N_dh * 2 := by
  simp only [koskSenderOkC, letV, bindV, findHonestC_queries, isAdvRegC_queries,
    Comp.queries_letC, Comp.queries]
  omega

@[simp] theorem resolveSigPkC_queries (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).queries primW primWS = min K S.N_dh * 2 := by
  simp [resolveSigPkC, letV, bindV, findHonestC_queries, Comp.queries_letC, Comp.queries]

@[simp] theorem honestPeerC_queries (S : Setup) (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).queries primW primWS = min K S.N_dh * 2 := by
  simp [honestPeerC, bindV, findHonestC_queries, Comp.queries]

@[simp] theorem hkdfOrRoC_true_queries (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K true st sec).queries primW primWS = 0 := by
  simp [hkdfOrRoC, letV, caseOptV, bindV, Comp.sampleDrKey96, primWS, Comp.queries]

@[simp] theorem rootRoC_queries (K : Nat) {Γ Δ : List (Ty pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) :
    (rootRoC K st rk dh).queries primW primWS = 0 := by
  simp [rootRoC, letV, caseOptV, bindV, Comp.sampleBytes32, primWS, Comp.queries]

@[simp] theorem initPrinB_queries (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrinB (Δ := Δ) K st u).queries primW primWS = 2 := by
  simp [initPrinB, bindV, Comp.sampleBytes32, Comp.queryPrim, primW, primWS, Comp.queries]

@[simp] theorem corruptB_queries (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (corruptB (Δ := Δ) K st u).queries primW primWS = 0 := by
  simp [corruptB, caseOptV, Comp.queries]

@[simp] theorem genSpkB_queries (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genSpkB (Δ := Δ) K st x).queries primW primWS = 4 := by
  simp [genSpkB, bindV, caseOptV, Comp.sampleBytes32, Comp.sampleRandom64, Comp.queryPrim,
    primW, primWS, Comp.queries]

@[simp] theorem genOpkB_queries (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genOpkB (Δ := Δ) K st x).queries primW primWS = 1 := by
  simp [genOpkB, bindV, Comp.sampleBytes32, Comp.queryPrim, primW, primWS, Comp.queries]

@[simp] theorem registerB_queries {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (registerB (Δ := Δ) st sk).queries primW primWS = 2 := by
  simp [registerB, bindV, Comp.queryPrim, primW, Comp.queries]

@[simp] theorem roB_queries (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roB (Δ := Δ) K st sec).queries primW primWS = 0 := by
  simp [roB, bindV, Comp.queries]

@[simp] theorem roRootB_queries (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roRootB (Δ := Δ) K st x).queries primW primWS = 0 := by
  simp [roRootB, bindV, Comp.queries]

@[simp] theorem sendC_queries (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sendC (Δ := Δ) S K opk st x).queries primW primWS = 18 + 10 * min K S.N_dh := by
  simp only [sendC, koskBundleOkC_queries, resolveSigPkC_queries, findHonestC_queries,
    hkdfOrRoC_true_queries, rootRoC_queries, bindV, letV, caseOptV, Comp.queries_letC,
    Comp.sampleBytes32, Comp.queryPrim, primW, primWS, Comp.queries]
  omega

@[simp] theorem sendB_queries (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sendB (Δ := Δ) S K opk st x).queries primW primWS = 18 + 10 * min K S.N_dh := by
  simp only [sendB, sendC_queries, Comp.queries]
  omega

@[simp] theorem recvTailC_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (recvTailC S K true st x kE bE oSk?).queries primW primWS = 13 + 2 * min K S.N_dh := by
  simp only [recvTailC, findHonestC_queries, hkdfOrRoC_true_queries, rootRoC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, primW, Comp.queries, ite_true]
  omega

@[simp] theorem recvTailC_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (recvTailC S K false st x kE bE oSk?).queries primW primWS = 12 + 2 * min K S.N_dh := by
  simp only [recvTailC, findHonestC_queries, hkdfOrRoC_true_queries, rootRoC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrim, primW, Comp.queries,
    Bool.false_eq_true, ite_false]
  omega

@[simp] theorem recvB_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (recvB (Δ := Δ) S K true st x).queries primW primWS = 14 + 4 * min K S.N_dh := by
  simp only [recvB, recvTailC_true_queries, koskSenderOkC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queries, ite_true]
  omega

@[simp] theorem recvB_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (recvB (Δ := Δ) S K false st x).queries primW primWS = 13 + 4 * min K S.N_dh := by
  simp only [recvB, recvTailC_false_queries, koskSenderOkC_queries,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.queries, Bool.false_eq_true, ite_false]
  omega

@[simp] theorem wrapC_queries {Δ : List (Ty pqSig)} (m : Comp pqxdhOps pqPrimIface Δ RS)
    (fg : Expr pqxdhOps (RS :: Δ) (.opt (.prod (B 1569) (B 64))))
    (tp : Expr pqxdhOps (RS :: Δ) .nat) (tpk : Expr pqxdhOps (RS :: Δ) (B 32)) :
    (wrapC m fg tp tpk).queries primW primWS = m.queries primW primWS := by
  simp [wrapC, bindV, Comp.queries]

@[simp] theorem extractC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (tp : Var Γ₁ .nat) (tpk : Var Γ₂ (B 32)) (st : Var Γ₃ authStateTy)
    (bu : Var Γ₄ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (extractC (Δ := Δ) S K tp tpk st bu).queries primW primWS = 2 + 2 * min K S.N_dh := by
  simp only [extractC, bindV, honestPeerC_queries, Comp.queryPrim, primW, Comp.queries]
  omega

theorem sigHandleDsl_queries_prim_le (S : Setup) (K : Nat) :
    (sigHandleDsl S K).queries sigPrimW sigWS ≤ 79 + 32 * S.N_dh := by
  simp only [sigHandleDsl, sigStepC,
    extractC_queries, wrapC_queries,
    initPrinB_queries, corruptB_queries, genSpkB_queries, genOpkB_queries, registerB_queries,
    roB_queries, roRootB_queries, sendB_queries, recvB_true_queries, recvB_false_queries,
    bindV, letV, caseOptV, caseSumV,
    queries_liftChal_sigPrimW, Comp.queries_letC,
    Comp.sampleBytes32, Comp.sampleRandom64C,
    Comp.queryPrim, Comp.queryPrimC, Comp.queryChal,
    primW, primWS, sigPrimW, sigWS, Comp.queries]
  have := Nat.min_le_right K S.N_dh
  omega

theorem sigInitDsl_queries_prim (S : Setup) :
    (sigInitDsl S).queries sigPrimW sigWS = 0 := by
  simp [sigInitDsl, bindV, Comp.sampleIndexC, Comp.sampleBoolC, sigWS, Comp.queries]

theorem sigFinishDsl_queries_prim (S : Setup) :
    (sigFinishDsl S).queries sigPrimW sigWS = 0 := by
  simp [sigFinishDsl, Comp.queries]

theorem sigReductionAuthProg_totalQueries_prim_le (S : Setup) (K q : Nat) :
    (sigReductionAuthProg S K).totalQueries sigPrimW sigWS q ≤ q * (79 + 32 * S.N_dh) := by
  simp only [CostedReduction.totalQueries, sigReductionAuthProg,
    sigInitDsl_queries_prim, sigFinishDsl_queries_prim, Nat.zero_add, Nat.add_zero]
  exact Nat.mul_le_mul_left q (sigHandleDsl_queries_prim_le S K)

/-! ## Challenger signing-query bound -/

@[reducible] def isSigChalQ : (PrimBaseSpec + eufCmaSignOracle.spec).Domain → Prop :=
  fun q => q.isRight = true

instance : DecidablePred isSigChalQ :=
  fun q => inferInstanceAs (Decidable (q.isRight = true))

theorem hwSigChal : ∀ g x, isSigChalQ (pqxdhEufCmaIface.enc g x) → 1 ≤ sigChalW g
  | .inl _, _, h => by cases h
  | .inr _, _, _ => le_rfl

theorem hUSigChal (n : ℕ) : (pqxdhEufCmaIface.fwdU n).IsQueryBoundP isSigChalQ 0 := by
  change IsQueryBoundP
    (liftM (OracleSpec.query (spec := PrimBaseSpec + eufCmaSignOracle.spec) (.inl (.inl n))))
    isSigChalQ 0
  rw [isQueryBoundP_query_iff]
  intro h; cases h

@[simp] theorem liftChal_queries_sigChalW {Γ : List (Ty pqSig)} {τ : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (Comp.liftChal (C := eufCmaSignOracle) c).queries sigChalW sigWS = 0 := by
  induction c <;> simp [Comp.liftChal, Comp.queries, sigChalW, sigWS, *]

theorem potAux1 (n : ℕ) (_h : n ≠ 0) : 1 + (2 * n - 1) ≤ 2 * n := by omega
theorem potAux2 (n : ℕ) (_h : n ≠ 0) : 1 + (2 * n - 2) ≤ 2 * n - 1 := by omega

/-- Potential of the sig-reduction state: twice the remaining signing budget. -/
def sigPot (st : sigStTy.denote) : Nat := 2 * st.1

theorem sigHandle_potOK (S : Setup) (K : Nat) (st : sigStTy.denote) (q : authQueryTy.denote) :
    PotOK isSigChalQ (fun r : (Ty.prod authRespTy sigStTy).denote => sigPot r.2)
      ((sigHandleDsl S K).eval (.cons st (.cons q .nil))) (sigPot st) := by
  unfold sigHandleDsl letV bindV caseSumV
  refine potC_letC _ _ _ ?_
  refine potC_letC _ _ _ ?_
  refine potC_letC _ _ _ ?_
  refine potC_letC _ _ _ ?_
  refine potC_letC _ _ _ ?_
  refine potC_letC _ _ _ ?_
  refine potC_letC _ _ _ ?_
  refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := sigPot st) (fun x => ?_) (by simp)
  refine potC_caseSum _ _ _ _ (fun d _ => ?_) (fun req _ => ?_)
  · refine potC_ret _ _ ?_
    simp [sigPot, v, Ext.wk, Expr.eval, Env.get]
  · refine potC_ite _ _ _ _ (fun _ => ?_) (fun hb => ?_)
    · refine potC_ret _ _ ?_
      simp [sigPot, Expr.eval]
    · have hb' : st.1 ≠ 0 := by simpa [natEq, v, Ext.wk, Expr.eval, Env.get] using hb
      beta_reduce
      apply potC_letC
      refine potC_letC _ _ _ ?_
      refine potC_letC _ _ _ ?_
      refine potC_letC _ _ _ ?_
      refine potC_letC _ _ _ ?_
      refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := sigPot st - 1)
        (fun x => ?_)
        (by simp only [Comp.queryChal, Comp.queries, sigChalW, sigPot]; exact potAux1 _ hb')
      refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := sigPot st - 1)
        (fun x => ?_) (by simp [Comp.sampleRandom64C, Comp.queries, sigWS])
      refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := sigPot st - 1)
        (fun x => ?_) (by simp [Comp.queryPrimC, Comp.queries, sigChalW])
      refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := sigPot st - 2)
        (fun x => ?_)
        (by simp only [Comp.queryChal, Comp.queries, sigChalW, sigPot]; exact potAux2 _ hb')
      refine potC_ret _ _ ?_
      simp [sigPot, v, Ext.wk, Expr.eval, Env.get]
      omega

theorem sigInit_potOK (S : Setup) (pk : (B 32).denote) :
    PotOK isSigChalQ (fun p : (Ty.prod .unit sigStTy).denote => sigPot p.2)
      ((sigInitDsl S).eval (.cons pk .nil)) (2 * S.N_spk_tot) := by
  unfold sigInitDsl bindV
  refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := 2 * S.N_spk_tot)
    (fun x => ?_) (by simp [Comp.sampleIndexC, Comp.queries, sigWS])
  refine potC_bind sigChalW sigWS hwSigChal hUSigChal _ _ _ (r := 2 * S.N_spk_tot)
    (fun y => ?_) (by simp [Comp.sampleBoolC, Comp.queries, sigWS])
  refine potC_ret _ _ ?_
  simp [sigPot, Expr.eval]

/-- Semantic signing-query bound (`≤ 2 * S.N_spk_tot`) for `sigReductionAuthProg`. -/
theorem sigReductionAuthProg_chalBounded (S : Setup) (K : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool) (pk : Bytes) :
    ((sigReductionAuthProg S K).eval A pk).IsQueryBoundP isSigChalQ (2 * S.N_spk_tot) := by
  unfold CostedReduction.eval CostedReduction.impl
  refine PotOK.toQueryBound (B := fun _ => 0) ?_ (fun _ => rfl)
  refine PotOK.bindPot (sigInit_potOK S pk) (fun as => ?_)
  refine PotOK.bindPot (B₁ := fun x : Bool × sigStTy.denote => sigPot x.2)
    (potOK_simulateQ_handlerImpl sigPot hUSigChal (sigReductionAuthProg S K).handle
      (fun q s => sigHandle_potOK S K s q) (A as.1) as.2)
    (fun bs => ?_)
  exact potC_ret _ _ (Nat.zero_le _)

end SignalPqxdh.Security.ReductionDsl.AuthHs
