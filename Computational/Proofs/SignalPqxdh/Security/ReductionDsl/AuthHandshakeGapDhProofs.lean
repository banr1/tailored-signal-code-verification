/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs

/-!
# Cost and Query Bounds for `fgAuthGapDhProg`

Syntactic step-cost, AST-size, primitive-query, and DDH challenger-query bounds for
`fgAuthGapDhProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl

@[simp] theorem bits_64 : bits 64 = 7 := by decide
@[simp] theorem bits_96 : bits 96 = 7 := by decide
@[simp] theorem bits_128 : bits 128 = 8 := by decide
@[simp] theorem bits_160 : bits 160 = 8 := by decide
@[simp] theorem bits_192 : bits 192 = 8 := by decide

def gdhPrimW : pqGapDhIface.Tag → ℕ
  | .inl _ => 1
  | .inr _ => 0

def gdhChalW : pqGapDhIface.Tag → ℕ
  | .inl _ => 0
  | .inr _ => 1

def gdhWS : pqGapDhIface.smp.Samp → ℕ := fun _ => 0

@[simp] theorem queries_liftChal_gdhPrimW
    {Γ : List (Ty pqSig)} {t : Ty pqSig} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (c.liftChal (C := gapDhDdhOracle)).queries gdhPrimW gdhWS = c.queries primW primWS :=
  Comp.queries_liftChal gdhPrimW gdhWS c

@[simp] theorem queries_liftChal_gdhChalW
    {Γ : List (Ty pqSig)} {t : Ty pqSig} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (c.liftChal (C := gapDhDdhOracle)).queries gdhChalW gdhWS = 0 := by
  induction c <;> simp [Comp.liftChal, Comp.queries, gdhChalW, gdhWS, *]

@[simp] theorem cost_queryDdh {Γ : List (Ty pqSig)}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B 32) (B 32)))) :
    (Comp.queryDdh e).cost = e.cost + 97 := rfl

@[simp] theorem costUB_queryDdh {Γ : List (Ty pqSig)}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B 32) (B 32)))) :
    (Comp.queryDdh e).costUB = e.costUB + 97 := rfl

@[simp] theorem queries_queryDdh_prim {Γ : List (Ty pqSig)}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B 32) (B 32)))) :
    (Comp.queryDdh e).queries gdhPrimW gdhWS = 0 := rfl

@[simp] theorem queries_queryDdh_chal {Γ : List (Ty pqSig)}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B 32) (B 32)))) :
    (Comp.queryDdh e).queries gdhChalW gdhWS = 1 := rfl

theorem nSendOpkEff_le_N_dh (S : Setup) : nSendOpkEff S ≤ S.N_dh := by
  unfold nSendOpkEff Setup.N_dh Setup.N_send_tot Setup.N_send_opk_tot
  split_ifs with h0
  · omega
  · have h1 : 1 ≤ S.N_id := by omega
    have h2 : 1 * S.N_send_opk ≤ S.N_id * S.N_send_opk := Nat.mul_le_mul_right S.N_send_opk h1
    omega

theorem nSendNoOpkEff_le_N_dh (S : Setup) : nSendNoOpkEff S ≤ S.N_dh := by
  unfold nSendNoOpkEff Setup.N_dh Setup.N_send_tot Setup.N_send_no_opk_tot
  split_ifs with h0
  · omega
  · have h1 : 1 ≤ S.N_id := by omega
    have h2 : 1 * S.N_send_no_opk ≤ S.N_id * S.N_send_no_opk :=
      Nat.mul_le_mul_right S.N_send_no_opk h1
    omega

@[simp] theorem mkSecretPosC_costUB {Δ : List (Ty pqSig)} (z : Expr pqxdhOps Δ (B 32)) :
    (mkSecretPosC z).costUB = z.costUB + 42 := by
  simp only [mkSecretPosC, letV, bindV, Comp.costUB_letC, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]

@[simp] theorem mkPairPosC_costUB {Δ : List (Ty pqSig)} (pk1 pk2 : Expr pqxdhOps Δ (B 32)) :
    (mkPairPosC pk1 pk2).costUB = pk1.costUB + pk2.costUB + 150 := by
  simp only [mkPairPosC, letV, bindV, Comp.costUB_letC, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]

@[simp] theorem twoSideC_costUB {Δ : List (Ty pqSig)} (a : Expr pqxdhOps Δ quadTy) :
    (twoSideC a).costUB = a.costUB + 662 := by
  simp only [twoSideC, mkSecretPosC_costUB, mkPairPosC_costUB, bytesEmpty,
    letV, bindV, Comp.costUB_letC, costUB_bytesBeq, costUB_litBytes, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, List.length_nil, costUB_v, Comp.costUB, Expr.costUB]

@[simp] theorem twoSideOptC_costUB {Δ : List (Ty pqSig)} (o : Expr pqxdhOps Δ (.opt quadTy)) :
    (twoSideOptC o).costUB = o.costUB + 670 := by
  simp only [twoSideOptC, twoSideC_costUB, caseOptV, bindV, costUB_v, Comp.costUB, Expr.costUB]

@[simp] theorem ddhEqC_costUB {Δ : List (Ty pqSig)} (p1 p2 : Expr pqxdhOps Δ fgPosTy) :
    (ddhEqC p1 p2).costUB = p1.costUB + p2.costUB + 601 := by
  simp only [ddhEqC, letV, caseSumV, Comp.costUB_letC, costUB_bytesBeq, costUB_queryDdh,
    PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]

@[simp] theorem ddhEqOptC_costUB {Δ : List (Ty pqSig)} (p1 p2 : Expr pqxdhOps Δ (.opt fgPosTy)) :
    (ddhEqOptC p1 p2).costUB = p1.costUB + p2.costUB + 620 := by
  simp only [ddhEqOptC, ddhEqC_costUB, letV, caseOptV, eCaseOpt, Comp.costUB_letC,
    costUB_v, Comp.costUB, Expr.costUB]

@[simp] theorem entryMatchesC_costUB {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) (e : Var Γ₂ fgPatchEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (entryMatchesC (Δ := Δ) k e).costUB = 2543 := by
  simp only [entryMatchesC, ddhEqC_costUB, ddhEqOptC_costUB, bindV,
    pkP1, pkP2, pkP3, pkP4, pkSs, feP1, feP2, feP3, feP4, feSs,
    costUB_bytesBeq, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]

@[simp] theorem patchC_costUB (K : Nat) {Γ₁ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) [Ext Γ₁ Δ] (L : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (patchC K k L).costUB = L.costUB + 145 + 2544 * K := by
  simp only [patchC, entryMatchesC_costUB, letV, bindV, caseOptV, findMV, Comp.costUB_letC,
    pkP1, pkP2, pkP3, pkP4, pkSs, feDk,
    costUB_sampleDrKey96C, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem rootPatchC_costUB (K : Nat) {Δ : List (Ty pqSig)}
    (rk : Expr pqxdhOps Δ (B 32)) (pos : Expr pqxdhOps Δ fgPosTy)
    (L : Expr pqxdhOps Δ (.list rootEntryTy)) :
    (rootPatchC K rk pos L).costUB = rk.costUB + pos.costUB + L.costUB + 114 + 681 * K := by
  simp only [rootPatchC, ddhEqC_costUB, letV, bindV, caseOptV, findMV, Comp.costUB_letC,
    reRk, rePos, reRk1, reCk, costUB_bytesBeq, costUB_sampleBytes32C,
    PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem isAdvPowsC_costUB (K : Nat) {Γ Δ : List (Ty pqSig)}
    (pows : Var Γ (.list (.prod (B 32) (B 32)))) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvPowsC K pows pk).costUB = pk.costUB + 69 + 69 * K := by
  simp only [isAdvPowsC, bindV, eAny, costUB_bytesBeq, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem koskBundleOkPowsC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (bu : Var Γ₃ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (koskBundleOkPowsC (Δ := Δ) S K st pows bu).costUB = 293 + 207 * K + 618 * min K S.N_dh := by
  simp only [koskBundleOkPowsC, findHonestC_costUB, isAdvPowsC_costUB,
    isGameSpkC_costUB, isGameOpkC_costUB, bindV, caseOptV, isSomeE,
    buIkB, buSpkB, buOpkB, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem koskSenderOkPowsC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkPowsC S K st pows ik).costUB = ik.costUB + 90 + 69 * K + 206 * min K S.N_dh := by
  simp only [koskSenderOkPowsC, findHonestC_costUB, isAdvPowsC_costUB,
    letV, bindV, isSomeE, Comp.costUB_letC, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem lookupSpkSkC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (lookupSpkSkC S K st pows pk).costUB = pk.costUB + 117 + 69 * K + 139 * min K S.N_dh := by
  simp only [lookupSpkSkC, bindV, findMV, eCaseOpt, eFind,
    stSpks, sbSpkSk, sbSpkPk,
    costUB_bytesBeq, costUB_litBytes, costUB_queryPrim,
    Ty.wd, PNat.val_ofNat, List.length_nil, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem onBaseF_costUB {Γ₁ Δ : List (Ty pqSig)} (sim : Var Γ₁ fgSimTy) [Ext Γ₁ Δ]
    (br : (g : Var (authStateTy :: Δ) authStateTy) → Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS) :
    (onBaseF sim br).costUB = (br .vz).costUB + 49 := by
  simp only [onBaseF, bindV, letV, Comp.costUB_liftChal, Comp.costUB_letC,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem fgInitPrinC_costUB (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgInitPrinC (Δ := Δ) K pa sim u).costUB = 519 + 5 * K := by
  simp only [fgInitPrinC, letV, bindV, eAny, Comp.costUB_letC, natEq,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paU, paDh1, paTI, peIkAPk, peMk, aNone, aInitPrin,
    costUB_litBytes, costUB_sampleBytes32C, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, List.length_nil, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem fgGenSpkC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgGenSpkC (Δ := Δ) S K pa sim x).costUB = 9010 + 20 * K + bits (nRecvEff S) := by
  simp only [fgGenSpkC, letV, bindV, caseOptV, eAny, eFind, Comp.costUB_letC, nat2Eq, natEq,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paV, paTS, peIkAPk, peSecIKAsign, buMk, sbMk, aNone, aBundle,
    costUB_encEC, costUB_encKEM, costUB_litBytes, costUB_u32OfNat,
    costUB_sampleBytes32C, costUB_sampleRandom64C, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, List.length_nil, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem fgSendC_true_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgSendC (Δ := Δ) S K true pa sim x).costUB =
      13018 + 6856 * K + 1169 * min K S.N_dh + bits (nSendOpkEff S) := by
  simp only [fgSendC, sendGuardE, findHonestC_costUB, koskBundleOkPowsC_costUB,
    resolveSigPkC_costUB, lookupSpkSkC_costUB, twoSideC_costUB, twoSideOptC_costUB,
    patchC_costUB, mkSecretPosC_costUB, rootPatchC_costUB, firstMsgADE_costUB, sidEq_costUB,
    bindV, letV, caseOptV, eFind, eAny, eCaseOpt, Comp.costUB_liftChal, Comp.costUB_letC,
    natEq, isSomeE, optFst, optSnd, q4,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paU, paDh1, paTI, seMk, peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig,
    hdMk, aNone, aSendFresh, aSendUnfresh,
    costUB_encEC, costUB_encKEM, costUB_bytesLen, costUB_bytesBeq, costUB_litBytes,
    costUB_sampleBytes32C, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, List.length_nil, bits_32, ite_true, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem fgSendC_false_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgSendC (Δ := Δ) S K false pa sim x).costUB =
      13019 + 6856 * K + 1169 * min K S.N_dh + bits (nSendNoOpkEff S) + bits S.N_send_opk_tot := by
  simp only [fgSendC, sendGuardE, findHonestC_costUB, koskBundleOkPowsC_costUB,
    resolveSigPkC_costUB, lookupSpkSkC_costUB, twoSideC_costUB, twoSideOptC_costUB,
    patchC_costUB, mkSecretPosC_costUB, rootPatchC_costUB, firstMsgADE_costUB, sidEq_costUB,
    bindV, letV, caseOptV, eFind, eAny, eCaseOpt, Comp.costUB_liftChal, Comp.costUB_letC,
    natEq, isSomeE, optFst, optSnd, q4,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paU, paDh1, paTI, seMk, peSecIKA0, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig,
    hdMk, aNone, aSendFresh, aSendUnfresh,
    costUB_encEC, costUB_encKEM, costUB_bytesLen, costUB_bytesBeq, costUB_litBytes,
    costUB_sampleBytes32C, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, List.length_nil, bits_32, Bool.false_eq_true, ite_false,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem fgRecvC_true_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRecvC (Δ := Δ) S K true sim x).costUB = 11017 + 3511 * K + 412 * min K S.N_dh := by
  simp only [fgRecvC, findHonestC_costUB, koskSenderOkPowsC_costUB, optU32Eq_costUB,
    kyberCheckE_costUB, twoSideC_costUB, twoSideOptC_costUB, patchC_costUB, rootPatchC_costUB,
    firstMsgADE_costUB,
    bindV, letV, caseOptV, eFind, eAny, eMap, eCaseOpt, Comp.costUB_liftChal, Comp.costUB_letC,
    nat3Eq, nat2Eq, natEq, q4,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
    aNone, aRecvHonest, aRecvUnfresh,
    costUB_bytesLen, costUB_litBytes, costUB_u32OfNat, costUB_u32Beq, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, List.length_nil, bits_32, ite_true, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem fgRecvC_false_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRecvC (Δ := Δ) S K false sim x).costUB = 10988 + 3446 * K + 412 * min K S.N_dh := by
  simp only [fgRecvC, findHonestC_costUB, koskSenderOkPowsC_costUB, optU32Eq_costUB,
    kyberCheckE_costUB, twoSideC_costUB, twoSideOptC_costUB, patchC_costUB, rootPatchC_costUB,
    firstMsgADE_costUB,
    bindV, letV, caseOptV, eFind, eAny, eCaseOpt, Comp.costUB_liftChal, Comp.costUB_letC,
    nat3Eq, nat2Eq, natEq, q4,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt,
    peSecIKA0, peIkAPk, sbSpkSk, sbSpkPk, sbPqspkSk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt,
    aNone, aRecvHonest, aRecvUnfresh,
    costUB_bytesLen, costUB_litBytes, costUB_u32OfNat, costUB_u32Beq, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, List.length_nil, bits_32, Bool.false_eq_true, ite_false,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem fgRecvB_true_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRecvB (Δ := Δ) S K true sim x).costUB = 11081 + 3511 * K + 412 * min K S.N_dh := by
  simp only [fgRecvB, fgRecvC_true_costUB, letV, Comp.costUB_letC,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    pmHdr, hdIkAPk, hdEkAPk, costUB_v, Expr.costUB]
  omega

@[simp] theorem fgRecvB_false_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRecvB (Δ := Δ) S K false sim x).costUB = 11052 + 3446 * K + 412 * min K S.N_dh := by
  simp only [fgRecvB, fgRecvC_false_costUB, letV, Comp.costUB_letC,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    pmHdr, hdIkAPk, hdEkAPk, costUB_v, Expr.costUB]
  omega

@[simp] theorem fgRoC_costUB (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRoC (Δ := Δ) K sim sec).costUB = 3593 + 2933 * K := by
  simp only [fgRoC, mkSecretPosC_costUB, patchC_costUB, slice32,
    letV, bindV, caseOptV, eFind, Comp.costUB_letC, natEq,
    fsBase, fsL, fsRootL, fsRaw, fsResp, fsPows, fsMk, fsUpd,
    aDrKey, costUB_bytesTakeK, costUB_bytesDrop, costUB_bytesLen, costUB_bytesBeq,
    costUB_litBytes, costUB_sampleDrKey96C,
    PNat.val_ofNat, F_X25519_length,
    bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem fgRoRootC_costUB (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRoRootC (Δ := Δ) K sim x).costUB = 225 + 681 * K := by
  simp only [fgRoRootC, mkSecretPosC_costUB, rootPatchC_costUB, bindV,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    aRootKdf, costUB_v, Comp.costUB, Expr.costUB]
  omega

@[simp] theorem fgRegisterC_costUB {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRegisterC (Δ := Δ) sim sk).costUB = 409 := by
  simp only [fgRegisterC, bindV, natEq,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    aNone, aPk, costUB_bytesLen, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, bits_32, costUB_v, Comp.costUB, Expr.costUB]

private theorem pow_two_ge_two_mul (k : ℕ) (hk : 1 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · decide
    · have ih' := ih (by omega)
      have hEq : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      omega

private theorem two_mul_log2_le (n : ℕ) : 2 * Nat.log 2 n ≤ n := by
  by_cases hn : n < 2
  · interval_cases n <;> simp
  · have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) (by omega)
    have h1 := pow_two_ge_two_mul (Nat.log 2 n) hlog
    have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    omega

private theorem bits_le_log2_N_dh_add_one {m : ℕ} {S : Setup} (h : m ≤ S.N_dh) :
    bits m ≤ Nat.log 2 S.N_dh + 1 := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

set_option maxRecDepth 50000 in
theorem fg_handle_cost_le_clamped (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).handle.cost ≤ 63000 + 25000 * K + 9000 * min K S.N_dh := by
  dsimp only [fgAuthGapDhProg, authCodec]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [
    fg2HandleDsl, fg2StepC, fg2InitPrinC, fg2GenSpkC, fg2SendC, sendGuardE,
    fgRecvB_true_costUB, fgRecvB_false_costUB, fgRoC_costUB, fgRoRootC_costUB, fgRegisterC_costUB,
    onBaseF_costUB, corruptB_costUB, genOpkB_costUB,
    findHonestC_costUB, koskBundleOkPowsC_costUB, resolveSigPkC_costUB, lookupSpkSkC_costUB,
    twoSideC_costUB, twoSideOptC_costUB, patchC_costUB, mkSecretPosC_costUB, rootPatchC_costUB,
    firstMsgADE_costUB, sidEq_costUB,
    bindV, letV, caseOptV, caseSumV, eFind, eAny, eCaseOpt, Comp.costUB_liftChal, Comp.costUB_letC,
    nat2Eq, natEq, isSomeE, optFst, optSnd, q4,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    fg2PaU, fg2PaV, fg2PaDh1, fg2PaTI, fg2PaSendOpk, fg2PaSendIdx, fg2PaTS,
    seMk, peSecIKA0, peIkAPk, peSecIKAsign, peCorrupted, peMk, sbSpkPk, sbPqspkPk, sbMk,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdMk, aNone, aInitPrin, aBundle, aSendFresh, aSendUnfresh,
    costUB_encEC, costUB_encKEM, costUB_bytesLen, costUB_bytesBeq, costUB_litBytes, costUB_u32OfNat,
    costUB_sampleBytes32C, costUB_sampleRandom64C, costUB_queryPrimC,
    Ty.wd, PNat.val_ofNat, List.length_nil, bits_32,
    Bool.false_eq_true, ite_true, ite_false,
    costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem fg_handle_cost_le (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).handle.cost ≤ 63000 + 25000 * K + 9000 * S.N_dh := by
  have h := fg_handle_cost_le_clamped S K
  have hm : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  omega

theorem fg_finish_cost_le_clamped (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).finish.cost ≤
      1000 + 1100 * K + 1000 * min K S.N_dh + 1000 * min K S.N_sess_tot +
        200 * (K * min K S.N_dh) + 200 * (min K S.N_dh * min K S.N_dh) +
        50 * (min K S.N_dh * min K S.N_sess_tot) := by
  dsimp only [fgAuthGapDhProg]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  simp only [
    fg2FinishDsl, fg2ExtractC, fg2FindMapC, fg2LogScanC, fg2RespCandC, fg2InitDh1CandC,
    bindV, letV, caseOptV, findMV, mapMV, foldMV,
    eCaseOpt, eCaseSum, eFind, eMap,
    natEq, nat2Eq, bytesEmpty, slice32, zero32,
    stPrin, stSpks, stSess,
    seSid, sePeerSpk, seEkASk,
    peIkAPk, sbSpkSk, sbSpkPk,
    fsBase, fsLog, fsResp, fsPows,
    fg2PaU, fg2PaV, fg2PaDh1,
    Comp.costUB_letC,
    costUB_bytesTakeK, costUB_bytesDrop, costUB_bytesBeq, costUB_litBytes,
    costUB_queryPrimC, costUB_queryDdh,
    Ty.wd, costUB_v, Comp.costUB, Expr.costUB,
    PNat.val_ofNat, List.length_nil, List.length_replicate,
    bits_32, bits_96]
  generalize min K S.N_dh = md
  generalize min K S.N_sess_tot = ms
  ring_nf
  omega

theorem fg_finish_cost_le (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).finish.cost ≤
      1000 + 1100 * K + 1000 * S.N_dh + 1000 * S.N_sess_tot +
        200 * (K * S.N_dh) + 200 * (S.N_dh * S.N_dh) + 200 * (S.N_dh * S.N_sess_tot) := by
  have h := fg_finish_cost_le_clamped S K
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right K S.N_sess_tot
  have h1 : K * min K S.N_dh ≤ K * S.N_dh := Nat.mul_le_mul_left K hd
  have h2 : min K S.N_dh * min K S.N_dh ≤ S.N_dh * S.N_dh := Nat.mul_le_mul hd hd
  have h3 : min K S.N_dh * min K S.N_sess_tot ≤ S.N_dh * S.N_sess_tot := Nat.mul_le_mul hd hs
  omega

private theorem fgSampleTargetC_costUB_le (S : Setup) {Γ : List (Ty pqSig)} :
    (fgSampleTargetC S (Γ := Γ)).costUB ≤ 100 + 6 * Nat.log 2 S.N_dh := by
  unfold fgSampleTargetC
  dsimp only
  split_ifs with h0 h1 h2 h3 h4
  · simp only [Comp.costUB, Expr.costUB, bits_0]
    omega
  · have hbId : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by unfold Setup.N_dh; omega)
    have hTot : 1 + S.N_send_opk + S.N_send_no_opk ≤ S.N_dh := by
      have hpos : 1 ≤ S.N_id := by omega
      unfold Setup.N_dh Setup.N_send_tot Setup.N_send_opk_tot Setup.N_send_no_opk_tot
      nlinarith
    have hbTot : bits (1 + S.N_send_opk + S.N_send_no_opk) ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one hTot
    simp only [bindV, natEq, costUB_sampleIndexC, costUB_v, Comp.costUB, Expr.costUB, bits_0]
    omega
  · have hbId : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by unfold Setup.N_dh; omega)
    have hTot : 1 + S.N_send_opk + S.N_send_no_opk ≤ S.N_dh := by
      have hpos : 1 ≤ S.N_id := by omega
      unfold Setup.N_dh Setup.N_send_tot Setup.N_send_opk_tot Setup.N_send_no_opk_tot
      nlinarith
    have hbTot : bits (1 + S.N_send_opk + S.N_send_no_opk) ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one hTot
    have hbA : bits S.N_send_opk ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by omega)
    simp only [bindV, natEq, costUB_sampleIndexC, costUB_v, Comp.costUB, Expr.costUB, bits_0]
    omega
  · have hbId : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by unfold Setup.N_dh; omega)
    have hTot : 1 + S.N_send_opk + S.N_send_no_opk ≤ S.N_dh := by
      have hpos : 1 ≤ S.N_id := by omega
      unfold Setup.N_dh Setup.N_send_tot Setup.N_send_opk_tot Setup.N_send_no_opk_tot
      nlinarith
    have hbTot : bits (1 + S.N_send_opk + S.N_send_no_opk) ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one hTot
    have hbB : bits S.N_send_no_opk ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by omega)
    simp only [bindV, natEq, costUB_sampleIndexC, costUB_v, Comp.costUB, Expr.costUB, bits_0]
    omega
  · have hbId : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by unfold Setup.N_dh; omega)
    have hTot : 1 + S.N_send_opk + S.N_send_no_opk ≤ S.N_dh := by
      have hpos : 1 ≤ S.N_id := by omega
      unfold Setup.N_dh Setup.N_send_tot Setup.N_send_opk_tot Setup.N_send_no_opk_tot
      nlinarith
    have hbTot : bits (1 + S.N_send_opk + S.N_send_no_opk) ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one hTot
    have hbA : bits S.N_send_opk ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by omega)
    have hbB : bits S.N_send_no_opk ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by omega)
    have hbAB : bits (S.N_send_opk + S.N_send_no_opk) ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by omega)
    simp only [bindV, natEq, costUB_sampleIndexC, costUB_v, Comp.costUB, Expr.costUB,
      bits_0, bits_1, bits_2]
    omega
  · have hbId : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by unfold Setup.N_dh; omega)
    have hTot : 1 + S.N_send_opk + S.N_send_no_opk ≤ S.N_dh := by
      have hpos : 1 ≤ S.N_id := by omega
      unfold Setup.N_dh Setup.N_send_tot Setup.N_send_opk_tot Setup.N_send_no_opk_tot
      nlinarith
    have hbTot : bits (1 + S.N_send_opk + S.N_send_no_opk) ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one hTot
    have hbA : bits S.N_send_opk ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by omega)
    have hbB : bits S.N_send_no_opk ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by omega)
    have hbAB : bits (S.N_send_opk + S.N_send_no_opk) ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by omega)
    simp only [bindV, natEq, costUB_sampleIndexC, costUB_v, Comp.costUB, Expr.costUB,
      bits_0, bits_1, bits_2]
    omega

private theorem fgSampleSpkC_costUB_le (S : Setup) {Γ : List (Ty pqSig)} :
    (fgSampleSpkC S (Γ := Γ)).costUB ≤ 20 + 2 * Nat.log 2 S.N_dh := by
  unfold fgSampleSpkC
  split_ifs with h0
  · simp only [Comp.costUB, Expr.costUB]
    omega
  · have hSpkPos : 0 < S.N_id * S.N_recv := by unfold Setup.N_spk_tot at h0; omega
    have hIdPos : 1 ≤ S.N_id := by
      rcases Nat.eq_zero_or_pos S.N_id with hZ | hP
      · simp [hZ] at hSpkPos
      · omega
    have hbId : bits S.N_id ≤ Nat.log 2 S.N_dh + 1 :=
      bits_le_log2_N_dh_add_one (by unfold Setup.N_dh; omega)
    have hbRecv : bits S.N_recv ≤ Nat.log 2 S.N_dh + 1 := by
      apply bits_le_log2_N_dh_add_one
      have hm : 1 * S.N_recv ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv hIdPos
      unfold Setup.N_dh Setup.N_spk_tot
      omega
    simp only [bindV, costUB_sampleIndexC, costUB_v, Comp.costUB, Expr.costUB]
    omega

theorem fg_init_cost_le_clamped (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).init.cost ≤ 200 + 8 * Nat.log 2 S.N_dh := by
  dsimp only [fgAuthGapDhProg]
  refine Nat.le_trans (Comp.cost_le_costUB _) ?_
  have hT := fgSampleTargetC_costUB_le S (Γ := [.prod (B 32) (B 32)])
  have hS := fgSampleSpkC_costUB_le S (Γ := [targetChoiceTy, .prod (B 32) (B 32)])
  simp only [fg2InitDsl, emptySimE, emptyAuthStE, fsMk, stMk,
    bindV, costUB_sampleBoolC, costUB_v, Comp.costUB, Expr.costUB]
  omega

theorem fg_init_cost_le (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).init.cost ≤ 200 + 4 * S.N_dh := by
  have h := fg_init_cost_le_clamped S K
  have hlog := two_mul_log2_le S.N_dh
  omega

@[simp] theorem mkSecretPosC_prim {Δ : List (Ty pqSig)} (z : Expr pqxdhOps Δ (B 32)) :
    (mkSecretPosC z).queries gdhPrimW gdhWS = 1 := by
  simp [mkSecretPosC, letV, bindV, Comp.queryPrimC, gdhPrimW, Comp.queries]

@[simp] theorem mkPairPosC_prim {Δ : List (Ty pqSig)} (pk1 pk2 : Expr pqxdhOps Δ (B 32)) :
    (mkPairPosC pk1 pk2).queries gdhPrimW gdhWS = 2 := by
  simp [mkPairPosC, letV, bindV, Comp.queryPrimC, gdhPrimW, Comp.queries]

@[simp] theorem twoSideC_prim {Δ : List (Ty pqSig)} (a : Expr pqxdhOps Δ quadTy) :
    (twoSideC a).queries gdhPrimW gdhWS = 2 := by
  simp [twoSideC, letV, bindV, Comp.queryPrimC, gdhPrimW, Comp.queries]

@[simp] theorem twoSideOptC_prim {Δ : List (Ty pqSig)} (o : Expr pqxdhOps Δ (.opt quadTy)) :
    (twoSideOptC o).queries gdhPrimW gdhWS = 2 := by
  simp [twoSideOptC, caseOptV, bindV, Comp.queries]

@[simp] theorem ddhEqC_prim {Δ : List (Ty pqSig)} (p1 p2 : Expr pqxdhOps Δ fgPosTy) :
    (ddhEqC p1 p2).queries gdhPrimW gdhWS = 0 := by
  simp [ddhEqC, letV, caseSumV, Comp.queries]

@[simp] theorem ddhEqOptC_prim {Δ : List (Ty pqSig)} (p1 p2 : Expr pqxdhOps Δ (.opt fgPosTy)) :
    (ddhEqOptC p1 p2).queries gdhPrimW gdhWS = 0 := by
  simp [ddhEqOptC, letV, caseOptV, Comp.queries]

@[simp] theorem entryMatchesC_prim {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) (e : Var Γ₂ fgPatchEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (entryMatchesC (Δ := Δ) k e).queries gdhPrimW gdhWS = 0 := by
  simp [entryMatchesC, bindV, Comp.queries]

@[simp] theorem patchC_prim (K : Nat) {Γ₁ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) [Ext Γ₁ Δ] (L : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (patchC K k L).queries gdhPrimW gdhWS = 0 := by
  simp [patchC, letV, bindV, caseOptV, findMV, Comp.sampleDrKey96C, gdhWS, Comp.queries]

@[simp] theorem rootPatchC_prim (K : Nat) {Δ : List (Ty pqSig)}
    (rk : Expr pqxdhOps Δ (B 32)) (pos : Expr pqxdhOps Δ fgPosTy)
    (L : Expr pqxdhOps Δ (.list rootEntryTy)) :
    (rootPatchC K rk pos L).queries gdhPrimW gdhWS = 0 := by
  simp [rootPatchC, letV, bindV, caseOptV, findMV, Comp.sampleBytes32C, gdhWS, Comp.queries]

@[simp] theorem isAdvPowsC_prim (K : Nat) {Γ Δ : List (Ty pqSig)}
    (pows : Var Γ (.list (.prod (B 32) (B 32)))) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvPowsC K pows pk).queries primW primWS = 1 := by
  simp [isAdvPowsC, bindV, Comp.queryPrim, primW, Comp.queries]

@[simp] theorem koskBundleOkPowsC_prim (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (bu : Var Γ₃ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (koskBundleOkPowsC (Δ := Δ) S K st pows bu).queries primW primWS = 3 + 6 * min K S.N_dh := by
  simp only [koskBundleOkPowsC, findHonestC_queries, isAdvPowsC_prim,
    isGameSpkC_queries, isGameOpkC_queries, bindV, caseOptV, Comp.queries]
  omega

@[simp] theorem koskSenderOkPowsC_prim (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkPowsC S K st pows ik).queries primW primWS = 1 + 2 * min K S.N_dh := by
  simp only [koskSenderOkPowsC, findHonestC_queries, isAdvPowsC_prim,
    letV, bindV, Comp.queries_letC, Comp.queries]
  omega

@[simp] theorem lookupSpkSkC_prim (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (lookupSpkSkC S K st pows pk).queries primW primWS = 1 + min K S.N_dh := by
  simp only [lookupSpkSkC, bindV, findMV, Comp.queryPrim, primW, Comp.queries]
  omega

@[simp] theorem onBaseF_prim {Γ₁ Δ : List (Ty pqSig)} (sim : Var Γ₁ fgSimTy) [Ext Γ₁ Δ]
    (br : (g : Var (authStateTy :: Δ) authStateTy) → Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS) :
    (onBaseF sim br).queries gdhPrimW gdhWS = (br .vz).queries primW primWS := by
  simp [onBaseF, bindV, letV, Comp.queries]

@[simp] theorem fgInitPrinC_prim (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgInitPrinC (Δ := Δ) K pa sim u).queries gdhPrimW gdhWS = 2 := by
  simp [fgInitPrinC, letV, bindV, Comp.sampleBytes32C, Comp.queryPrimC, gdhPrimW, gdhWS, Comp.queries]

@[simp] theorem fgGenSpkC_prim (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgGenSpkC (Δ := Δ) S K pa sim x).queries gdhPrimW gdhWS = 4 := by
  simp [fgGenSpkC, letV, bindV, caseOptV, Comp.sampleBytes32C, Comp.sampleRandom64C,
    Comp.queryPrimC, gdhPrimW, gdhWS, Comp.queries]

@[simp] theorem fgSendC_prim (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgSendC (Δ := Δ) S K opk pa sim x).queries gdhPrimW gdhWS = 24 + 11 * min K S.N_dh := by
  simp only [fgSendC, findHonestC_queries, koskBundleOkPowsC_prim, resolveSigPkC_queries,
    lookupSpkSkC_prim, twoSideC_prim, twoSideOptC_prim, patchC_prim, mkSecretPosC_prim,
    rootPatchC_prim, queries_liftChal_gdhPrimW,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.sampleBytes32C, Comp.queryPrimC,
    gdhPrimW, gdhWS, Comp.queries]
  omega

@[simp] theorem fgRecvC_prim (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRecvC (Δ := Δ) S K opk sim x).queries gdhPrimW gdhWS = 19 + 4 * min K S.N_dh := by
  cases opk <;>
  · simp only [fgRecvC, findHonestC_queries, koskSenderOkPowsC_prim, twoSideC_prim,
      twoSideOptC_prim, patchC_prim, rootPatchC_prim, queries_liftChal_gdhPrimW,
      bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrimC,
      gdhPrimW, Comp.queries, Bool.false_eq_true, ite_true, ite_false]
    omega

@[simp] theorem fgRecvB_prim (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRecvB (Δ := Δ) S K opk sim x).queries gdhPrimW gdhWS = 19 + 4 * min K S.N_dh := by
  simp [fgRecvB, letV]

@[simp] theorem fgRoC_prim (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRoC (Δ := Δ) K sim sec).queries gdhPrimW gdhWS = 4 := by
  simp [fgRoC, letV, bindV, caseOptV, Comp.sampleDrKey96C, gdhWS, Comp.queries]

@[simp] theorem fgRoRootC_prim (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRoRootC (Δ := Δ) K sim x).queries gdhPrimW gdhWS = 1 := by
  simp [fgRoRootC, bindV, Comp.queries]

@[simp] theorem fgRegisterC_prim {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRegisterC (Δ := Δ) sim sk).queries gdhPrimW gdhWS = 2 := by
  simp [fgRegisterC, bindV, Comp.queryPrimC, gdhPrimW, Comp.queries]

private theorem fg2InitPrinC_prim (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fg2InitPrinC (Δ := Δ) K pa sim u).queries gdhPrimW gdhWS = 2 := by
  simp [fg2InitPrinC, letV, bindV, Comp.sampleBytes32C, Comp.queryPrimC, gdhPrimW, gdhWS,
    Comp.queries]

private theorem fg2GenSpkC_prim (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fg2GenSpkC (Δ := Δ) K pa sim x).queries gdhPrimW gdhWS = 4 := by
  simp [fg2GenSpkC, letV, bindV, caseOptV, Comp.sampleBytes32C, Comp.sampleRandom64C,
    Comp.queryPrimC, gdhPrimW, gdhWS, Comp.queries]

private theorem fg2SendC_prim (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fg2SendC (Δ := Δ) S K opk pa sim x).queries gdhPrimW gdhWS = 24 + 11 * min K S.N_dh := by
  simp only [fg2SendC, twoSideC_prim, twoSideOptC_prim, patchC_prim, mkSecretPosC_prim,
    rootPatchC_prim, queries_liftChal_gdhPrimW,
    findHonestC_queries, koskBundleOkPowsC_prim, resolveSigPkC_queries, lookupSpkSkC_prim,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.sampleBytes32C, Comp.queryPrimC,
    gdhPrimW, gdhWS, Comp.queries]
  omega

theorem fg_handle_prim_le_clamped (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).handle.queries gdhPrimW gdhWS ≤ 172 + min K S.N_dh * 30 := by
  dsimp only [fgAuthGapDhProg, authCodec]
  simp only [
    fg2HandleDsl, fg2StepC,
    fg2InitPrinC_prim, fg2GenSpkC_prim, fg2SendC_prim, fgRecvB_prim,
    fgRoC_prim, fgRoRootC_prim, fgRegisterC_prim,
    onBaseF_prim, corruptB_queries, genOpkB_queries,
    bindV, letV, caseSumV, Comp.queries_letC, Comp.queries]
  omega

theorem fg_handle_prim_le (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).handle.queries gdhPrimW gdhWS ≤ 172 + S.N_dh * 30 := by
  have h := fg_handle_prim_le_clamped S K
  have hm : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  omega

theorem fg_finish_prim_le_clamped (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).finish.queries gdhPrimW gdhWS ≤
      min K S.N_dh * 4 + min K S.N_sess_tot * 2 := by
  dsimp only [fgAuthGapDhProg]
  simp only [
    queries_queryDdh_prim,
    fg2FinishDsl, fg2ExtractC, fg2FindMapC, fg2LogScanC, fg2RespCandC, fg2InitDh1CandC,
    bindV, letV, caseOptV, findMV, mapMV, foldMV,
    Comp.letC, Comp.queryPrimC,
    gdhPrimW, Comp.queries]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

theorem fg_finish_prim_le (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).finish.queries gdhPrimW gdhWS ≤ S.N_dh * 4 + S.N_sess_tot * 2 := by
  have h := fg_finish_prim_le_clamped S K
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right K S.N_sess_tot
  omega

private theorem fgSampleTargetC_prim (S : Setup) {Γ : List (Ty pqSig)} :
    (fgSampleTargetC S (Γ := Γ)).queries gdhPrimW gdhWS = 0 := by
  unfold fgSampleTargetC
  dsimp only
  split_ifs <;> simp [bindV, Comp.sampleIndexC, gdhWS, Comp.queries]

private theorem fgSampleSpkC_prim (S : Setup) {Γ : List (Ty pqSig)} :
    (fgSampleSpkC S (Γ := Γ)).queries gdhPrimW gdhWS = 0 := by
  unfold fgSampleSpkC
  split_ifs <;> simp [bindV, Comp.sampleIndexC, gdhWS, Comp.queries]

theorem fg_init_prim (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).init.queries gdhPrimW gdhWS = 0 := by
  simp [fgAuthGapDhProg, fg2InitDsl, fgSampleTargetC_prim, fgSampleSpkC_prim, bindV,
    Comp.sampleBoolC, gdhWS, Comp.queries]

@[simp] theorem mkSecretPosC_chal {Δ : List (Ty pqSig)} (z : Expr pqxdhOps Δ (B 32)) :
    (mkSecretPosC z).queries gdhChalW gdhWS = 0 := by
  simp [mkSecretPosC, letV, bindV, Comp.queryPrimC, gdhChalW, Comp.queries]

@[simp] theorem mkPairPosC_chal {Δ : List (Ty pqSig)} (pk1 pk2 : Expr pqxdhOps Δ (B 32)) :
    (mkPairPosC pk1 pk2).queries gdhChalW gdhWS = 0 := by
  simp [mkPairPosC, letV, bindV, Comp.queryPrimC, gdhChalW, Comp.queries]

@[simp] theorem twoSideC_chal {Δ : List (Ty pqSig)} (a : Expr pqxdhOps Δ quadTy) :
    (twoSideC a).queries gdhChalW gdhWS = 0 := by
  simp [twoSideC, letV, bindV, Comp.queryPrimC, gdhChalW, Comp.queries]

@[simp] theorem twoSideOptC_chal {Δ : List (Ty pqSig)} (o : Expr pqxdhOps Δ (.opt quadTy)) :
    (twoSideOptC o).queries gdhChalW gdhWS = 0 := by
  simp [twoSideOptC, caseOptV, bindV, Comp.queries]

@[simp] theorem ddhEqC_chal {Δ : List (Ty pqSig)} (p1 p2 : Expr pqxdhOps Δ fgPosTy) :
    (ddhEqC p1 p2).queries gdhChalW gdhWS = 1 := by
  simp [ddhEqC, letV, caseSumV, Comp.queries]

@[simp] theorem ddhEqOptC_chal {Δ : List (Ty pqSig)} (p1 p2 : Expr pqxdhOps Δ (.opt fgPosTy)) :
    (ddhEqOptC p1 p2).queries gdhChalW gdhWS = 1 := by
  simp [ddhEqOptC, letV, caseOptV, Comp.queries]

@[simp] theorem entryMatchesC_chal {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) (e : Var Γ₂ fgPatchEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (entryMatchesC (Δ := Δ) k e).queries gdhChalW gdhWS = 4 := by
  simp [entryMatchesC, bindV, Comp.queries]

@[simp] theorem patchC_chal (K : Nat) {Γ₁ Δ : List (Ty pqSig)}
    (k : Var Γ₁ patchKeyTy) [Ext Γ₁ Δ] (L : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (patchC K k L).queries gdhChalW gdhWS = 4 * K := by
  simp only [patchC, entryMatchesC_chal, letV, bindV, caseOptV, findMV,
    Comp.queries_letC, Comp.sampleDrKey96C, gdhWS, Comp.queries]
  omega

@[simp] theorem rootPatchC_chal (K : Nat) {Δ : List (Ty pqSig)}
    (rk : Expr pqxdhOps Δ (B 32)) (pos : Expr pqxdhOps Δ fgPosTy)
    (L : Expr pqxdhOps Δ (.list rootEntryTy)) :
    (rootPatchC K rk pos L).queries gdhChalW gdhWS = K := by
  simp only [rootPatchC, ddhEqC_chal, letV, bindV, caseOptV, findMV,
    Comp.queries_letC, Comp.sampleBytes32C, gdhWS, Comp.queries]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

@[simp] theorem onBaseF_chal {Γ₁ Δ : List (Ty pqSig)} (sim : Var Γ₁ fgSimTy) [Ext Γ₁ Δ]
    (br : (g : Var (authStateTy :: Δ) authStateTy) → Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS) :
    (onBaseF sim br).queries gdhChalW gdhWS = 0 := by
  simp [onBaseF, bindV, Comp.queries]

@[simp] theorem fgInitPrinC_chal (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgInitPrinC (Δ := Δ) K pa sim u).queries gdhChalW gdhWS = 0 := by
  simp [fgInitPrinC, letV, bindV, Comp.sampleBytes32C, Comp.queryPrimC, gdhChalW, gdhWS, Comp.queries]

@[simp] theorem fgGenSpkC_chal (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgGenSpkC (Δ := Δ) S K pa sim x).queries gdhChalW gdhWS = 0 := by
  simp [fgGenSpkC, letV, bindV, caseOptV, Comp.sampleBytes32C, Comp.sampleRandom64C,
    Comp.queryPrimC, gdhChalW, gdhWS, Comp.queries]

@[simp] theorem fgSendC_chal (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fgSendC (Δ := Δ) S K opk pa sim x).queries gdhChalW gdhWS = 5 * K := by
  simp only [fgSendC, twoSideC_chal, twoSideOptC_chal, patchC_chal, mkSecretPosC_chal,
    rootPatchC_chal, queries_liftChal_gdhChalW,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.sampleBytes32C, Comp.queryPrimC,
    gdhChalW, gdhWS, Comp.queries]
  omega

@[simp] theorem fgRecvC_chal (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRecvC (Δ := Δ) S K opk sim x).queries gdhChalW gdhWS = 5 * K := by
  cases opk <;>
  · simp only [fgRecvC, twoSideC_chal, twoSideOptC_chal, patchC_chal, rootPatchC_chal,
      queries_liftChal_gdhChalW,
      bindV, letV, caseOptV, Comp.queries_letC, Comp.queryPrimC,
      gdhChalW, Comp.queries, Bool.false_eq_true, ite_true, ite_false]
    omega

@[simp] theorem fgRecvB_chal (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRecvB (Δ := Δ) S K opk sim x).queries gdhChalW gdhWS = 5 * K := by
  simp [fgRecvB, letV]

@[simp] theorem fgRoC_chal (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRoC (Δ := Δ) K sim sec).queries gdhChalW gdhWS = 4 * K := by
  simp only [fgRoC, mkSecretPosC_chal, patchC_chal, letV, bindV, caseOptV,
    Comp.queries_letC, Comp.sampleDrKey96C, gdhWS, Comp.queries]
  omega

@[simp] theorem fgRoRootC_chal (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRoRootC (Δ := Δ) K sim x).queries gdhChalW gdhWS = K := by
  simp only [fgRoRootC, mkSecretPosC_chal, rootPatchC_chal, bindV, Comp.queries]
  omega

@[simp] theorem fgRegisterC_chal {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (sim : Var Γ₁ fgSimTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (fgRegisterC (Δ := Δ) sim sk).queries gdhChalW gdhWS = 0 := by
  simp [fgRegisterC, bindV, Comp.queryPrimC, gdhChalW, Comp.queries]

private theorem fg2InitPrinC_chal (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fg2InitPrinC (Δ := Δ) K pa sim u).queries gdhChalW gdhWS = 0 := by
  simp [fg2InitPrinC, letV, bindV, Comp.sampleBytes32C, Comp.queryPrimC, gdhChalW, gdhWS,
    Comp.queries]

private theorem fg2GenSpkC_chal (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fg2GenSpkC (Δ := Δ) K pa sim x).queries gdhChalW gdhWS = 0 := by
  simp [fg2GenSpkC, letV, bindV, caseOptV, Comp.sampleBytes32C, Comp.sampleRandom64C,
    Comp.queryPrimC, gdhChalW, gdhWS, Comp.queries]

private theorem fg2SendC_chal (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fg2SendC (Δ := Δ) S K opk pa sim x).queries gdhChalW gdhWS = 5 * K := by
  simp only [fg2SendC, twoSideC_chal, twoSideOptC_chal, patchC_chal, mkSecretPosC_chal,
    rootPatchC_chal, queries_liftChal_gdhChalW,
    bindV, letV, caseOptV, Comp.queries_letC, Comp.sampleBytes32C, Comp.queryPrimC,
    gdhChalW, gdhWS, Comp.queries]
  omega

theorem fg_handle_chal_le (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).handle.queries gdhChalW gdhWS ≤ 5 * K := by
  dsimp only [fgAuthGapDhProg, authCodec]
  simp only [
    fg2HandleDsl, fg2StepC,
    fg2InitPrinC_chal, fg2GenSpkC_chal, fg2SendC_chal, fgRecvB_chal,
    fgRoC_chal, fgRoRootC_chal, fgRegisterC_chal,
    onBaseF_chal,
    bindV, letV, caseSumV, Comp.queries_letC, Comp.queries]
  omega

theorem fg_finish_chal_le_clamped (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).finish.queries gdhChalW gdhWS ≤
      K + min K S.N_dh + min K S.N_sess_tot := by
  dsimp only [fgAuthGapDhProg]
  simp only [
    queries_queryDdh_chal,
    fg2FinishDsl, fg2ExtractC, fg2FindMapC, fg2LogScanC, fg2RespCandC, fg2InitDh1CandC,
    bindV, letV, caseOptV, findMV, mapMV, foldMV,
    Comp.letC, Comp.queryPrimC,
    gdhChalW, Comp.queries]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

theorem fg_finish_chal_le (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).finish.queries gdhChalW gdhWS ≤ K + S.N_dh + S.N_sess_tot := by
  have h := fg_finish_chal_le_clamped S K
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right K S.N_sess_tot
  omega

private theorem fgSampleTargetC_chal (S : Setup) {Γ : List (Ty pqSig)} :
    (fgSampleTargetC S (Γ := Γ)).queries gdhChalW gdhWS = 0 := by
  unfold fgSampleTargetC
  dsimp only
  split_ifs <;> simp [bindV, Comp.sampleIndexC, gdhWS, Comp.queries]

private theorem fgSampleSpkC_chal (S : Setup) {Γ : List (Ty pqSig)} :
    (fgSampleSpkC S (Γ := Γ)).queries gdhChalW gdhWS = 0 := by
  unfold fgSampleSpkC
  split_ifs <;> simp [bindV, Comp.sampleIndexC, gdhWS, Comp.queries]

theorem fg_init_chal (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).init.queries gdhChalW gdhWS = 0 := by
  simp [fgAuthGapDhProg, fg2InitDsl, fgSampleTargetC_chal, fgSampleSpkC_chal, bindV,
    Comp.sampleBoolC, gdhWS, Comp.queries]

theorem fgAuthGapDhProg_totalCost_le_security (S : Setup) (b : QueryBudget) :
    (fgAuthGapDhProg S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have hH := fg_handle_cost_le_clamped S b.q_total
  have hF := fg_finish_cost_le_clamped S b.q_total
  have hI := fg_init_cost_le_clamped S b.q_total
  change (fgAuthGapDhProg S b.q_total).init.cost +
      b.q_total * max 1 ((fgAuthGapDhProg S b.q_total).handle.cost + 32) +
      (fgAuthGapDhProg S b.q_total).finish.cost ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b
  generalize (fgAuthGapDhProg S b.q_total).init.cost = cI at hI ⊢
  generalize (fgAuthGapDhProg S b.q_total).handle.cost = cH at hH ⊢
  generalize (fgAuthGapDhProg S b.q_total).finish.cost = cF at hF ⊢
  have hMax : max 1 (cH + 32) = cH + 32 := by omega
  rw [hMax]
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  generalize min b.q_total S.N_dh = md at hH hF ⊢
  generalize min b.q_total S.N_sess_tot = ms at hF ⊢
  generalize Nat.log 2 S.N_dh = ld at hI ⊢
  generalize Nat.log 2 S.N_sess_tot = ls at ⊢
  generalize b.q_total = q at *
  have hqH : q * (cH + 32) ≤ q * (63032 + 25000 * q + 9000 * md) :=
    Nat.mul_le_mul_left q (by omega)
  nlinarith [Nat.zero_le (q * md), Nat.zero_le (q * ms), Nat.zero_le (md * ms),
    Nat.zero_le (q * ld), Nat.zero_le (q * ls)]

theorem fgAuthGapDhProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (fgAuthGapDhProg S b.q_total).totalCost b.q_total ≤ stepCostBudget S b := by
  have hH := fg_handle_cost_le S b.q_total
  have hF := fg_finish_cost_le S b.q_total
  have hI := fg_init_cost_le S b.q_total
  change (fgAuthGapDhProg S b.q_total).init.cost +
      b.q_total * max 1 ((fgAuthGapDhProg S b.q_total).handle.cost + 32) +
      (fgAuthGapDhProg S b.q_total).finish.cost ≤ stepCostBudget S b
  generalize (fgAuthGapDhProg S b.q_total).init.cost = cI at hI ⊢
  generalize (fgAuthGapDhProg S b.q_total).handle.cost = cH at hH ⊢
  generalize (fgAuthGapDhProg S b.q_total).finish.cost = cF at hF ⊢
  have hMax : max 1 (cH + 32) = cH + 32 := by omega
  rw [hMax]
  unfold stepCostBudget
  generalize b.q_total = q at *
  have hqH : q * (cH + 32) ≤ q * (63032 + 25000 * q + 9000 * S.N_dh) :=
    Nat.mul_le_mul_left q (by omega)
  nlinarith [Nat.zero_le (q * S.N_dh), Nat.zero_le (q * S.N_sess_tot),
    Nat.zero_le (S.N_dh * S.N_sess_tot)]

theorem fgAuthGapDhProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (fgAuthGapDhProg S b.q_total).totalQueries gdhPrimW gdhWS b.q_total ≤ primQueryBudget S b := by
  dsimp only [CostedReduction.totalQueries]
  have hH := fg_handle_prim_le S b.q_total
  have hF := fg_finish_prim_le S b.q_total
  have hI := fg_init_prim S b.q_total
  rw [hI, Nat.zero_add]
  generalize (fgAuthGapDhProg S b.q_total).handle.queries gdhPrimW gdhWS = qH at hH ⊢
  generalize (fgAuthGapDhProg S b.q_total).finish.queries gdhPrimW gdhWS = qF at hF ⊢
  unfold primQueryBudget
  generalize b.q_total = q at *
  have h1 : q * qH ≤ q * (172 + S.N_dh * 30) := Nat.mul_le_mul_left q hH
  nlinarith

theorem fgAuthGapDhProg_totalChalQueries_le (S : Setup) (b : QueryBudget) :
    (fgAuthGapDhProg S b.q_total).totalQueries gdhChalW gdhWS b.q_total ≤
      5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  dsimp only [CostedReduction.totalQueries]
  have hH := fg_handle_chal_le S b.q_total
  have hF := fg_finish_chal_le S b.q_total
  have hI := fg_init_chal S b.q_total
  rw [hI, Nat.zero_add]
  generalize (fgAuthGapDhProg S b.q_total).handle.queries gdhChalW gdhWS = h at hH ⊢
  generalize (fgAuthGapDhProg S b.q_total).finish.queries gdhChalW gdhWS = f at hF ⊢
  generalize b.q_total = q at *
  have h1 : q * h ≤ 5 * (q * q) := by
    rw [← Nat.mul_left_comm]
    exact Nat.mul_le_mul_left q hH
  rw [pow_two]
  omega

private theorem gdh_liftChal_size {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (Comp.liftChal (C := C) c).size = c.size := by
  (induction c <;> simp_all [Comp.liftChal, Comp.size]); rfl

set_option linter.unusedSimpArgs false in
private theorem fgSampleTargetC_size_le (S : Setup) {Γ : List (Ty pqSig)} :
    (fgSampleTargetC S (Γ := Γ)).size ≤ 100 := by
  unfold fgSampleTargetC
  dsimp only
  split_ifs <;>
    (simp only [bindV, natEq, v, Comp.sampleIndexC, Expr.litBool, Expr.litNat,
      Comp.iteC, Comp.size, Expr.size, bits_0, bits_1, bits_2]; omega)

set_option linter.unusedSimpArgs false in
private theorem fgSampleSpkC_size_le (S : Setup) {Γ : List (Ty pqSig)} :
    (fgSampleSpkC S (Γ := Γ)).size ≤ 30 := by
  unfold fgSampleSpkC
  split_ifs <;>
    (simp only [bindV, v, Comp.sampleIndexC, Expr.noneE, Expr.someE, Comp.size, Expr.size]; omega)

set_option linter.unusedSimpArgs false in
private theorem fg2InitDsl_size_le (S : Setup) :
    (fg2InitDsl S).size ≤ 220 := by
  have hT := fgSampleTargetC_size_le S (Γ := [.prod (B 32) (B 32)])
  have hS := fgSampleSpkC_size_le S (Γ := [targetChoiceTy, .prod (B 32) (B 32)])
  simp only [fg2InitDsl, emptySimE, emptyAuthStE, fsMk, stMk,
    Expr.litUnit, Expr.litBool, Expr.listNil, v, bindV, Comp.sampleBoolC,
    Comp.size, Expr.size]
  omega

set_option linter.unusedSimpArgs false in
private theorem fg2FinishDsl_size_le (S : Setup) (K : Nat) :
    (fg2FinishDsl S K).size ≤ 25 * bits K + 800 := by
  have hb1 : bits (min K S.N_dh) ≤ bits K := by
    unfold bits; exact Nat.add_le_add_right (Nat.log_mono_right (Nat.min_le_left _ _)) 1
  have hb2 : bits (min K S.N_sess_tot) ≤ bits K := by
    unfold bits; exact Nat.add_le_add_right (Nat.log_mono_right (Nat.min_le_left _ _)) 1
  simp only [fg2FinishDsl, fg2ExtractC, fg2InitDh1CandC, fg2RespCandC, fg2LogScanC, fg2FindMapC,
    fg2PaDh1, fg2PaU, fg2PaV, fsLog, fsBase, fsPows, fsResp,
    stSpks, stSess, stPrin, sbSpkPk, sbSpkSk, sePeerSpk, seSid, seEkASk, peIkAPk,
    slice32, bytesEmpty, zero32, natEq, nat2Eq,
    Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Comp.iteC, Comp.caseOptC,
    Expr.findBounded, Expr.mapBounded, Comp.findBoundedM, Comp.mapBoundedM, Comp.foldBoundedM,
    v, Comp.letC, bindV, letV, caseOptV, findMV, mapMV, foldMV,
    eCaseOpt, eCaseSum, eFind, eMap,
    Expr.litBytes, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq,
    Comp.queryPrimC, Comp.queryChal, Comp.queryDdh, Comp.size, Expr.size, bits_32, bits_96]
  dsimp only [pqxdhOps, Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem fg2StepC_size_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (fg2StepC (Δ := Δ) S K pa sim q).size ≤ 155 * bits K + 18500 := by
  have hb1 : bits (min K S.N_dh) ≤ bits K := by
    unfold bits; exact Nat.add_le_add_right (Nat.log_mono_right (Nat.min_le_left _ _)) 1
  simp (config := { maxSteps := 1000000 }) only [fg2StepC, fg2InitPrinC, fg2GenSpkC, fg2SendC,
    fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF,
    isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC,
    patchC, rootPatchC, sendGuardE,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    fg2PaU, fg2PaV, fg2PaDh1, fg2PaTI, fg2PaSendOpk, fg2PaSendIdx, fg2PaTS,
    feP1, feP2, feP3, feP4, feSs, feDk,
    pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk,
    q4, bytesEmpty, slice32, zero32, emptySimE,
    corruptB, genOpkB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    gdh_liftChal_size, v, Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV, eLet, eCaseOpt, eCaseSum,
    eFind, eAny, eMap,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
    Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq,
    Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
    Comp.sampleIndex, Comp.queryPrim,
    Comp.sampleBoolC, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C,
    Comp.sampleIndexC, Comp.queryPrimC, Comp.queryChal, Comp.queryDdh,
    encEC, encKEM, Comp.size, Expr.size,
    bits_0, bits_1, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  dsimp only [pqxdhOps, Ops.sum, pqBytesOps, pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
theorem fgAuthGapDhProg_size_le_clamped (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).size ≤ 185 * bits K + 20000 := by
  have hI := fg2InitDsl_size_le S
  have hF := fg2FinishDsl_size_le S K
  have hH : (fg2HandleDsl S K).size ≤ 156 * bits K + 18600 := by
    have hS := fg2StepC_size_le S K
      (Γ₁ := fg2ParamsTy :: fg2GsTy :: [authQueryTy])
      (Γ₂ := fgSimTy :: fg2ParamsTy :: fg2GsTy :: [authQueryTy])
      (Γ₃ := [fg2GsTy, authQueryTy])
      (Δ := fgSimTy :: fg2ParamsTy :: fg2GsTy :: [authQueryTy])
      .vz .vz (.vs .vz)
    simp only [fg2HandleDsl, fg2PaDh1, fg2PaTI, fsBase, stPrin, peCorrupted, aNone, natEq,
      Expr.litUnit, Expr.litBool, Expr.boolAnd, Comp.iteC, Expr.findBounded,
      v, Comp.letC, bindV, letV, eCaseOpt, eFind,
      Comp.size, Expr.size]
    omega
  change (fg2InitDsl S).size + (fg2HandleDsl S K).size + (fg2FinishDsl S K).size ≤ _
  omega

end SignalPqxdh.Security.ReductionDsl.AuthHs
