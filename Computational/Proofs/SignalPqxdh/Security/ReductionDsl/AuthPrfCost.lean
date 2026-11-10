/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfBase
import Computational.Proofs.ReductionDsl.Soundness
import VCVio.EvalDist.Monad.Basic

@[expose] public section

set_option autoImplicit false
namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open OracleSpec OracleComp

attribute [local simp] Expr.cost Comp.cost

@[simp] theorem bits_0 : bits 0 = 1 := by decide
@[simp] theorem bits_1 : bits 1 = 1 := by decide
@[simp] theorem bits_32 : bits 32 = 6 := by decide
@[simp] theorem bits_33 : bits 33 = 6 := by decide

theorem F_X25519_length : F_X25519.length = 32 := by decide

theorem Expr.cost_pos {S : Sig} {O : Ops S} {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    1 ≤ e.cost := by
  induction e <;> simp [Expr.cost, bits] <;> omega

@[simp] theorem cost_boolOr {Γ : List PT} (a b : Expr pqxdhOps Γ .bool) :
    (boolOr a b).cost = a.cost + b.cost + 1 := by
  have := Expr.cost_pos b
  simp [boolOr, Nat.max_eq_right this]

@[simp] theorem cost_boolBeq {Γ : List PT} (a b : Expr pqxdhOps Γ .bool) :
    (boolBeq a b).cost = a.cost + b.cost + 2 := by
  simp [boolBeq]; omega

@[simp] theorem cost_litB {Γ : List PT} (w : ℕ+) (bs : Bytes) :
    (litB (Γ := Γ) w bs).cost = w.val + bs.length + 1 := by
  simp [litB, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem cost_catB {Γ : List PT} (m n : ℕ+)
    (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (catB m n a b).cost = a.cost + b.cost + m.val + n.val + 1 := by
  simp [catB, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem cost_encEC {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) :
    (encEC pk).cost = pk.cost + 33 := by
  simp [encEC, bytesCons, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem cost_encKEM {Γ : List PT} (pk : Expr pqxdhOps Γ (B 1568)) :
    (encKEM pk).cost = pk.cost + 1569 := by
  simp [encKEM, bytesCons, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem cost_takeKB {Γ : List PT} (w k : ℕ+) (x : Expr pqxdhOps Γ (B w)) :
    (takeKB w k x).cost = x.cost + w.val + k.val := by
  simp [takeKB, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem cost_bytesLen {Γ : List PT} (w : ℕ+) (x : Expr pqxdhOps Γ (B w)) :
    (bytesLen w x).cost = x.cost + bits w.val := by
  simp [bytesLen, pqxdhOps, Ops.sum, pqBytesOps]

@[simp] theorem cost_bytesBeq {Γ : List PT} (w : ℕ+) (a b : Expr pqxdhOps Γ (B w)) :
    (bytesBeq w a b).cost = a.cost + b.cost + 2 * w.val + 1 := by
  simp [bytesBeq, pqxdhOps, Ops.sum, pqBytesOps]; omega

@[simp] theorem cost_u32OfNat {Γ : List PT} (n : Expr pqxdhOps Γ .nat) :
    (u32OfNat n).cost = n.cost + 1 := by
  simp [u32OfNat, pqxdhOps, Ops.sum, pqU32Ops]

@[simp] theorem cost_u32Beq {Γ : List PT} (a b : Expr pqxdhOps Γ U32) :
    (u32Beq a b).cost = a.cost + b.cost + 2 := by
  simp [u32Beq, pqxdhOps, Ops.sum, pqU32Ops]

@[simp] theorem cost_samplePrim {Γ : List PT} (s : PSamp) :
    (samplePrim (Γ := Γ) s).cost = 1 + s.cost := rfl

@[simp] theorem cost_sampleChal {C : ChallengerOracle} {Γ : List PT} (s : PSamp) :
    (sampleChal (C := C) (Γ := Γ) s).cost = 1 + s.cost := rfl

@[simp] theorem cost_queryPrim {Γ : List PT} (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (queryPrim g e).cost = e.cost + (1 + Ty.wd g.dom + Ty.wd g.cod) := rfl

@[simp] theorem cost_queryDeriveMk {Γ : List PT} (e : Expr pqxdhOps Γ (.opt (B 32))) :
    (queryDeriveMk e).cost = e.cost + 145 := rfl

@[simp] theorem cost_letC {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (e : Expr pqxdhOps Γ a) (k : Comp pqxdhOps I (a :: Γ) b) :
    (Comp.letC e k).cost = e.cost + k.cost + 2 := by
  simp [Comp.letC]; omega

@[simp] theorem cost_liftPrimComp {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftPrimComp (C := C) c).cost = c.cost := by
  induction c with
  | ret e => rfl
  | bind m k ih1 ih2 => simp [liftPrimComp, ih1, ih2]
  | ite b t e ih1 ih2 => simp [liftPrimComp, ih1, ih2]
  | caseOpt e n s ih1 ih2 => simp [liftPrimComp, ih1, ih2]
  | caseSum e l r ih1 ih2 => simp [liftPrimComp, ih1, ih2]
  | sample sc e => rfl
  | query g e => rfl
  | iter n init body ih => simp [liftPrimComp, ih]
  | findM K l p ih => simp [liftPrimComp, ih]
  | anyM K l p ih => simp [liftPrimComp, ih]
  | mapM K l f ih => simp [liftPrimComp, ih]
  | consumeFirstM K l p mk ih => simp [liftPrimComp, ih]
  | foldM K l init step ih => simp [liftPrimComp, ih]

/-- Cost of the `Setup`-dependent constants in `sessionSlotIndexE S`. -/
def slotIdxCost (S : Setup) : Nat :=
  max (5 + bits (if S.N_id = 0 then 0 else S.N_send_opk))
    (8 + bits S.N_send_opk_tot + bits (if S.N_id = 0 then 0 else S.N_send_no_opk))

@[simp] theorem sessionSlotIndexE_cost (S : Setup) {Γ : List PT} (sid : Expr pqxdhOps Γ sessionIdTy) :
    (sessionSlotIndexE S sid).cost = sid.cost + slotIdxCost S + 1 := by
  have h1 : 1 ≤ bits S.N_send_opk_tot := by simp [bits]
  have h2 : 1 ≤ bits (if S.N_id = 0 then 0 else S.N_send_no_opk) := by simp [bits]
  simp only [sessionSlotIndexE, slotIdxCost, eCaseSum, v, Expr.cost, bits_0]
  omega

@[simp] theorem firstMsgADE_cost {Γ : List PT} (ikA ikB eph pq : Expr pqxdhOps Γ (B 32)) :
    (firstMsgADE ikA ikB eph pq).cost = ikA.cost + ikB.cost + eph.cost + 3 * pq.cost + 851 := by
  dsimp only [firstMsgADE, encEC, natEq, catB, bytesCons, litB, bytesVarint, bytesLen, Expr.cost]
  simp only [pqxdhOps, Ops.sum, pqBytesOps, Sum.elim_inl, PNat.val_ofNat,
    List.length_cons, List.length_nil, bits_0, bits_32, bits_33]
  omega

@[simp] theorem buildSecretsE_cost {Γ : List PT} (dh1 dh2 dh3 : Expr pqxdhOps Γ (B 32))
    (dh4? : Expr pqxdhOps Γ (.opt (B 32))) (ss : Expr pqxdhOps Γ (B 32)) :
    (buildSecretsE dh1 dh2 dh3 dh4? ss).cost =
      dh1.cost + dh2.cost + dh3.cost + dh4?.cost + ss.cost + 737 := by
  dsimp only [buildSecretsE, eLet2, eLet, eCaseOpt, widenB, catB, litB, v, Expr.cost]
  simp only [pqxdhOps, Ops.sum, pqBytesOps, Sum.elim_inl, PNat.val_ofNat, F_X25519_length]
  omega

@[simp] theorem sidEq_cost {Γ : List PT} (a b : Expr pqxdhOps Γ sessionIdTy) :
    (sidEq a b).cost = a.cost + b.cost + 41 := by
  simp only [sidEq, eLet2, eLet, eCaseSum, nat2Eq, nat3Eq, natEq, v, Expr.cost]
  omega

@[simp] theorem optU32Eq_cost {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt U32)) :
    (optU32Eq a b).cost = a.cost + b.cost + 16 := by
  simp only [optU32Eq, eLet2, eLet, eCaseOpt, cost_u32Beq, v, Expr.cost]
  omega

@[simp] theorem saltBytesE_cost {Γ : List PT} (o : Expr pqxdhOps Γ (.opt (B 32))) :
    (saltBytesE o).cost = o.cost + 228 := by
  dsimp only [saltBytesE, eCaseOpt, takeKB, catB, litB, v, Expr.cost]
  simp only [pqxdhOps, Ops.sum, pqBytesOps, Sum.elim_inl, PNat.val_ofNat, List.length_replicate]
  omega

@[simp] theorem sameSaltKeyE_cost {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt (B 32))) :
    (sameSaltKeyE a b).cost = a.cost + b.cost + 521 := by
  simp only [sameSaltKeyE, cost_bytesBeq, saltBytesE_cost, PNat.val_ofNat]
  omega

@[simp] theorem kyberEq_cost {Γ : List PT}
    (a b : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32))))) :
    (kyberEq a b).cost = 4 * a.cost + 4 * b.cost + 91 := by
  simp only [kyberEq, natEq, cost_u32Beq, cost_bytesBeq, Expr.cost, PNat.val_ofNat]
  omega

@[simp] theorem kyberCheckE_cost {Γ : List PT} (K : Nat)
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32))))) :
    (kyberCheckE K used entry).cost = used.cost + entry.cost + K * 100 + 16 := by
  simp only [kyberCheckE, eLet2, eLet, eAny, kyberEq_cost, v, Expr.cost]
  omega

@[simp] theorem koskBundleOkC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC S K st bu : Comp pqxdhOps pqPrimIface Δ .bool).cost =
      322 + min K S.N_dh * 618 + K * 207 := by
  simp only [koskBundleOkC, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, bindV, letV,
    caseOptV, findMV, anyMV, eAny, isSomeE, pkbIkB, pkbSpkB, pkbOpkB?, sbSpkPk, oeOpkPk, peIkAPk,
    asPrincipals, asSpkBundles, asOpkEntries, asAdvKeys, cost_letC, cost_queryPrim, cost_bytesBeq,
    cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] private theorem recvFinishTagRunC_cost_tight (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    (recvFinishTagRunC S K tag res?).cost =
      res?.cost + 350 + K * 39 + min K S.N_dh * 7786 := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC, bindV, letV,
    caseOptV, caseSumV, findMV, consumeFirstMV, eMap, natEq, nat2Eq, nat3Eq, oeMk, oeUpd, roMk,
    rnoMk, stMk, stUpd, ahsMk, ahsUpd, aNone, aRecvHonest, aRecvUnfresh, peIkAPk, peCorrupted,
    sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk, hdrIkAPk, hdrEkAPk, hdrKemCt,
    pkmHdr, soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched, snoA0, snoB0,
    snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched, roBCorr, roA0, roB0, roSb, roOb,
    roA1, roPk1, roCt, roM, rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM, asSecb,
    asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents,
    asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    cost_letC, cost_queryPrim, cost_bytesBeq, cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd,
    PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  omega

@[simp] private theorem prepareAuthHybridRecvC_true_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K true hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).cost =
      6826 + K * 246 + min K S.N_dh * 7753 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, bindV, letV, caseOptV, findMV, eFind, eAny, eCaseOpt,
    natEq, nat2Eq, nat3Eq, optU32Eq_cost, kyberCheckE_cost, buildSecretsE_cost, isSomeE, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    oeOpkSk, oeOpkPk, oeConsumed, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk,
    iasPeerPqspkPk, iasKemCt, iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asUsedRecvOPK, asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions, cost_letC, cost_queryPrim, cost_bytesBeq, cost_bytesLen, cost_u32OfNat,
    cost_u32Beq, cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat, bits_32, ite_true]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] private theorem prepareAuthHybridRecvC_false_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K false hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).cost =
      6696 + K * 221 + min K S.N_dh * 7753 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, bindV, letV, caseOptV, findMV, eFind, eAny, eCaseOpt,
    natEq, nat2Eq, nat3Eq, optU32Eq_cost, kyberCheckE_cost, buildSecretsE_cost, isSomeE, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asUsedRecvNoOPK,
    asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    cost_letC, cost_queryPrim, cost_bytesBeq, cost_bytesLen, cost_u32OfNat,
    cost_u32Beq, cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat, bits_32,
    Bool.false_eq_true, ite_false]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem recvFinishTagRunC_cost (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    (recvFinishTagRunC S K tag res?).cost =
      res?.cost + 350 + K * 39 + min K S.N_dh * 7786 :=
  recvFinishTagRunC_cost_tight S K tag res?

@[simp] theorem prepareAuthHybridRecvC_true_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K true hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).cost =
      6826 + K * 246 + min K S.N_dh * 7753 :=
  prepareAuthHybridRecvC_true_cost_tight S K hst x

@[simp] theorem prepareAuthHybridRecvC_false_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K false hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).cost =
      6696 + K * 221 + min K S.N_dh * 7753 :=
  prepareAuthHybridRecvC_false_cost_tight S K hst x

@[simp] theorem finishAuthHybridSendC_cost (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    (finishAuthHybridSendC S K hst args).cost =
      args.cost + 864 + min K S.N_dh * 920 + K * 3239 := by
  simp only [finishAuthHybridSendC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    findHonestC, bindV, letV, caseOptV, findMV, anyMV, eCaseOpt, eAny, natEq, isSomeE,
    optFst, optSnd, hdMk, pmMk, seMk, iasMk, soMk, snoMk, ikrMk, stMk, stUpd, ahsMk, ahsUpd,
    aSendFresh, aSendUnfresh, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkPk, pkbIkB, pkbSpkId,
    pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
    asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
    asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, cost_letC, cost_queryPrim,
    cost_bytesBeq, cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right, Nat.max_eq_left]
  omega

@[simp] theorem hasDuplicateBytesDsl_cost (w : ℕ+) (K : Nat) {Γ : List PT}
    (xs : Expr pqxdhOps Γ (.list (B w))) :
    (hasDuplicateBytesDsl w K xs).cost =
      xs.cost + 5 + K * 12 + K ^ 2 * (2 * w.val + 4) := by
  simp only [hasDuplicateBytesDsl, cost_boolOr, cost_bytesBeq, Expr.cost]
  ring

@[simp] theorem hasBadSigAuthDsl_cost (K : Nat) {Γ : List PT}
    (hst : Expr pqxdhOps Γ authHybridStateTy) :
    (hasBadSigAuthDsl K hst).cost = hst.cost + 8 + K * 33 := by
  simp only [hasBadSigAuthDsl, asSessions, ahsBase, aseFresh, aseSpkHonest, asePqspkHonest,
    cost_boolOr, Expr.cost]
  ring

@[simp] theorem hasKemPkCollisionAuthDsl_cost (K : Nat) {Γ : List PT}
    (hst : Expr pqxdhOps Γ authHybridStateTy) :
    (hasKemPkCollisionAuthDsl K hst).cost = hst.cost + 11 + K * 20 + K ^ 2 * 3140 := by
  simp only [hasKemPkCollisionAuthDsl, hasDuplicateBytesDsl_cost, asSpkBundles, ahsBase,
    sbPqspkPk, Expr.cost, PNat.val_ofNat]
  ring

@[simp] theorem hasBadKemShCrRecordsDsl_cost (K : Nat) {Γ : List PT}
    (hst : Expr pqxdhOps Γ authHybridStateTy) :
    (hasBadKemShCrRecordsDsl K hst).cost = hst.cost + 5 + K * 6 + K ^ 2 * 6371 := by
  simp only [hasBadKemShCrRecordsDsl, eLet, eAny, ahsInitKemRecs, ahsRecvKemRecs,
    rkrKemSs, ikrKemSs, rkrKemCt, ikrKemCt, ikrPqspkPk, rkrPqspkPk,
    cost_boolOr, cost_bytesBeq, v, Expr.cost, PNat.val_ofNat]
  ring

@[simp] theorem notAllChallengedCleanDsl_cost (K : Nat) {Γ : List PT}
    (st : Expr pqxdhOps Γ authStateTy) :
    (notAllChallengedCleanDsl K st).cost = st.cost + 9 + K * 38 := by
  simp only [notAllChallengedCleanDsl, asSessions, aseChallenged, aseFresh, asePqspkHonest,
    cost_boolOr, Expr.cost]
  ring

private theorem finalizeAuthFixedDsl_cost_tight (S : Setup) (K : Nat) {Γ : List PT} :
    (finalizeAuthFixedDsl S K (Γ := Γ)).cost =
      100 + min K S.N_dh * 413 + min K S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 := by
  have hbody : (finalizeAuthFixedBodyDsl S K (Γ := Γ)).cost =
      57 + min K S.N_dh * 48 + (4 * min K S.N_dh) ^ 2 * 68 + K * 97 + K ^ 2 * 9511 := by
    simp only [finalizeAuthFixedBodyDsl, hasDuplicateBytesDsl_cost, hasBadSigAuthDsl_cost,
      hasKemPkCollisionAuthDsl_cost, hasBadKemShCrRecordsDsl_cost, notAllChallengedCleanDsl_cost,
      asHasWonAuth, cost_boolOr, cost_boolBeq, cost_samplePrim, PSamp.cost, Ty.wd,
      Comp.cost, Expr.cost, PNat.val_ofNat]
    omega
  simp only [finalizeAuthFixedDsl, hbody, ahsBase, asPrincipals,
    asSpkBundles, asOpkEntries, asSessions, peIkAPk, sbSpkPk, oeOpkPk, aseEkASk,
    cost_letC, cost_queryPrim, Ty.wd, Comp.cost, Expr.cost, PNat.val_ofNat]
  ring

private theorem prfCkInitDslK_cost_le (S : Setup) (K : Nat) :
    (prfCkInitDslK S K).cost ≤ 80 + bits (min K S.N_sess_tot) := by
  simp only [bindV, emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE,
    ahsMk, stMk, cost_samplePrim, PSamp.cost,
    Ty.wd, v, Comp.cost, Expr.cost, bits_0]
  omega

private theorem prfCkFinishDsl_cost_tight (S : Setup) (K : Nat) :
    (prfCkFinishDsl S K).cost =
      114 + min K S.N_dh * 413 + min K S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 := by
  simp only [prfCkFinishDsl, letV, ckSecb, ckFhst, ahsfHybrid, cost_letC,
    finalizeAuthFixedDsl_cost_tight, Expr.cost]
  ring

private theorem prfMsgKeysInitDslK_cost_le (S : Setup) (K : Nat) :
    (prfMsgKeysInitDslK S K).cost ≤
      85 + bits (min K S.N_sess_tot) + bits (min K S.N_recv_tot + 1) := by
  simp only [bindV, mkcMk, emptyAuthHybridStFixedE, emptyAuthHybridStE,
    emptyAuthStE, ahsMk, stMk,
    cost_sampleChal, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost, bits_0]
  omega

private theorem prfMsgKeysFinishDsl_cost_tight (S : Setup) (K : Nat) :
    (prfMsgKeysFinishDsl S K).cost =
      118 + min K S.N_dh * 413 + min K S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 := by
  simp only [prfMsgKeysFinishDsl, letV, mkcSecb, mkcFhst, ahsfHybrid, cost_liftPrimComp,
    cost_letC, finalizeAuthFixedDsl_cost_tight, v, Expr.cost]
  ring

@[simp] theorem finalizeAuthFixedDsl_cost (S : Setup) (K : Nat) {Γ : List PT} :
    (finalizeAuthFixedDsl S K (Γ := Γ)).cost =
      100 + min K S.N_dh * 413 + min K S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 :=
  finalizeAuthFixedDsl_cost_tight S K

@[simp] private theorem lookupSendSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy) :
    (lookupSendSlotE ss sid).cost = ss.cost + sid.cost + 148 := by
  simp only [lookupSendSlotE, eLet2, eLet, eCaseSum, assSendOpk, assSendNoOpk, v, Expr.cost]
  omega

@[simp] private theorem lookupSendSlotOrZeroE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy) :
    (lookupSendSlotOrZeroE ss sid).cost = ss.cost + sid.cost + 150 := by
  simp only [lookupSendSlotOrZeroE, lookupSendSlotE_cost, eCaseOpt, v, Expr.cost, bits_0]
  omega

@[simp] private theorem allocSendSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ sessionIdTy) :
    (allocSendSlotE ss sid).cost = ss.cost + sid.cost + 436 := by
  simp only [allocSendSlotE, eLet2, eLet, eCaseSum, eCaseOpt, assMk, assNext, assSendOpk,
    assSendNoOpk, assRecv, v, Expr.cost, bits_0, bits_1]
  omega

@[simp] private theorem allocRecvSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (rc : Expr pqxdhOps Γ .nat) :
    (allocRecvSlotE ss rc).cost = ss.cost + rc.cost + 231 := by
  simp only [allocRecvSlotE, eLet2, eLet, eCaseOpt, assMk, assNext, assSendOpk,
    assSendNoOpk, assRecv, v, Expr.cost, bits_1]
  omega

theorem prfCkInitDsl_cost (S : Setup) :
    (prfCkInitDsl S).cost = 71 + bits S.N_sess_tot := by
  simp only [prfCkInitDsl, bindV, emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE,
    ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, cost_samplePrim, PSamp.cost,
    Ty.wd, v, Comp.cost, Expr.cost, bits_0]
  omega

theorem prfCkFinishDsl_cost (S : Setup) (K : Nat) :
    (prfCkFinishDsl S K).cost =
      114 + min K S.N_dh * 413 + min K S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 :=
  prfCkFinishDsl_cost_tight S K

theorem prfMsgKeysInitDsl_cost (S : Setup) :
    (prfMsgKeysInitDsl S).cost = 72 + bits S.N_sess_tot + bits (S.N_recv_tot + 1) := by
  simp only [prfMsgKeysInitDsl, bindV, mkcMk, emptyAuthHybridStFixedE, emptyAuthHybridStE,
    emptyAuthStE, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk,
    cost_sampleChal, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost, bits_0]
  omega

theorem prfMsgKeysFinishDsl_cost (S : Setup) (K : Nat) :
    (prfMsgKeysFinishDsl S K).cost =
      118 + min K S.N_dh * 413 + min K S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511 :=
  prfMsgKeysFinishDsl_cost_tight S K

@[simp] private theorem finishAuthRecvCkC_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rc' : Expr pqxdhOps Δ .nat)
    (p : Expr pqxdhOps Δ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (finishAuthRecvCkC S K msg prep drKey rk1 spqrSalt? rc' p).cost =
      drKey.cost + rk1.cost + spqrSalt?.cost + rc'.cost + p.cost +
      1827 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishAuthRecvCkC, bindV, letV, eCaseOpt, firstMsgADE_cost,
    recvFinishTagRunC_cost_tight, ahsBase, parHstDec, parFinishTag, parKEntry,
    hdrIkAPk, pkmHdr, peIkAPk, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    asRoCache, asRootRoCache, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
    cost_letC, cost_queryPrim, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat, bits_0]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem finishAuthRecvCkC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rc' : Expr pqxdhOps Δ .nat)
    (p : Expr pqxdhOps Δ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (finishAuthRecvCkC S K msg prep drKey rk1 spqrSalt? rc' p).cost =
      drKey.cost + rk1.cost + spqrSalt?.cost + rc'.cost + p.cost +
      1827 + K * 39 + min K S.N_dh * 7786 :=
  finishAuthRecvCkC_cost_tight S K msg prep drKey rk1 spqrSalt? rc' p

@[simp] private theorem finishAuthSendMkC_cost_tight (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (sid : Expr pqxdhOps Δ sessionIdTy) (uE : Expr pqxdhOps Δ principalEntryTy)
    (pp : Expr pqxdhOps Δ (.opt (.prod .nat principalEntryTy))) (isFresh : Expr pqxdhOps Δ .bool)
    (bu : Expr pqxdhOps Δ preKeyBundleTy) (m01 : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (keys6 : Expr pqxdhOps Δ keys6Ty) (drKey : Expr pqxdhOps Δ drKeyTy)
    (rk1 mkSeed ck1_1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (pqMsg msgPlain : Expr pqxdhOps Δ (B 32)) (mks : Expr pqxdhOps Δ msgKeysTy) [Ext Γ₁ Δ] :
    (finishAuthSendMkC S K fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
      spqrSalt? pqMsg msgPlain mks).cost =
      sid.cost + uE.cost + pp.cost + isFresh.cost + bu.cost + m01.cost + keys6.cost +
      drKey.cost + rk1.cost + mkSeed.cost + ck1_1.cost + spqrSalt?.cost + pqMsg.cost +
      msgPlain.cost + mks.cost + 2354 + min K S.N_dh * 920 + K * 3239 := by
  simp only [finishAuthSendMkC, bindV, letV, firstMsgADE_cost, finishAuthHybridSendC_cost,
    ahsfHybrid, ahsBase, peIkAPk, pkbIkB, asRoCache, asRootRoCache, ahsfUpd, ahsfMkSlots,
    ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    cost_letC, cost_queryPrim, cost_litB, v, Comp.cost, Expr.cost,
    Ty.wd, PNat.val_ofNat, List.length_nil]
  omega

@[simp] theorem finishAuthSendMkC_cost (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy)
    (sid : Expr pqxdhOps Δ sessionIdTy) (uE : Expr pqxdhOps Δ principalEntryTy)
    (pp : Expr pqxdhOps Δ (.opt (.prod .nat principalEntryTy))) (isFresh : Expr pqxdhOps Δ .bool)
    (bu : Expr pqxdhOps Δ preKeyBundleTy) (m01 : Expr pqxdhOps Δ (.prod (B 32) (B 32)))
    (keys6 : Expr pqxdhOps Δ keys6Ty) (drKey : Expr pqxdhOps Δ drKeyTy)
    (rk1 mkSeed ck1_1 : Expr pqxdhOps Δ (B 32)) (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32)))
    (pqMsg msgPlain : Expr pqxdhOps Δ (B 32)) (mks : Expr pqxdhOps Δ msgKeysTy) [Ext Γ₁ Δ] :
    (finishAuthSendMkC S K fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
      spqrSalt? pqMsg msgPlain mks).cost =
      sid.cost + uE.cost + pp.cost + isFresh.cost + bu.cost + m01.cost + keys6.cost +
      drKey.cost + rk1.cost + mkSeed.cost + ck1_1.cost + spqrSalt?.cost + pqMsg.cost +
      msgPlain.cost + mks.cost + 2354 + min K S.N_dh * 920 + K * 3239 :=
  finishAuthSendMkC_cost_tight S K fhst sid uE pp isFresh bu m01 keys6 drKey rk1 mkSeed ck1_1
    spqrSalt? pqMsg msgPlain mks

@[simp] private theorem finishAuthRecvMkC_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 ck1_1 : Expr pqxdhOps Δ (B 32)) (rc' : Expr pqxdhOps Δ .nat)
    (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) (mks : Expr pqxdhOps Δ msgKeysTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (finishAuthRecvMkC S K msg prep drKey rk1 ck1_1 rc' cache' mks).cost =
      drKey.cost + rk1.cost + ck1_1.cost + rc'.cost + cache'.cost + mks.cost +
      1679 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishAuthRecvMkC, bindV, letV, eCaseOpt, firstMsgADE_cost,
    recvFinishTagRunC_cost_tight, ahsBase, parHstDec, parFinishTag, parKEntry,
    hdrIkAPk, pkmHdr, peIkAPk, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    asRoCache, asRootRoCache, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk,
    cost_letC, cost_queryPrim, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat, bits_0]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem finishAuthRecvMkC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (msg : Var Γ₁ preKeyMsgTy) (prep : Var Γ₂ preparedAuthRecvTy)
    (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 ck1_1 : Expr pqxdhOps Δ (B 32)) (rc' : Expr pqxdhOps Δ .nat)
    (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) (mks : Expr pqxdhOps Δ msgKeysTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (finishAuthRecvMkC S K msg prep drKey rk1 ck1_1 rc' cache' mks).cost =
      drKey.cost + rk1.cost + ck1_1.cost + rc'.cost + cache'.cost + mks.cost +
      1679 + K * 39 + min K S.N_dh * 7786 :=
  finishAuthRecvMkC_cost_tight S K msg prep drKey rk1 ck1_1 rc' cache' mks

@[simp] private theorem finishRecvUnmatchedMkPreC_cost_tight (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (msg : Var Γ₂ preKeyMsgTy)
    (prep : Var Γ₃ preparedAuthRecvTy) (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rSlot rc' : Expr pqxdhOps Δ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (finishRecvUnmatchedMkPreC S K core msg prep drKey rk1 spqrSalt? rSlot rc').cost =
      drKey.cost + rk1.cost + spqrSalt?.cost + rSlot.cost + rc'.cost +
      2008 + K * 39 + min K S.N_dh * 7786 := by
  simp only [finishRecvUnmatchedMkPreC, bindV, letV, natEq, natLt, finishAuthRecvMkC_cost_tight,
    mkcSecb, mkcIdx, mkcSentChal, mkcFhst, ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    ahsfUpdSlots, ahsfMkSlots, mkcMk,
    cost_letC, cost_samplePrim, cost_queryPrim, PSamp.cost, Ty.wd, v,
    Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem finishRecvUnmatchedMkPreC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (msg : Var Γ₂ preKeyMsgTy)
    (prep : Var Γ₃ preparedAuthRecvTy) (drKey : Expr pqxdhOps Δ drKeyTy) (rk1 : Expr pqxdhOps Δ (B 32))
    (spqrSalt? : Expr pqxdhOps Δ (.opt (B 32))) (rSlot rc' : Expr pqxdhOps Δ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (finishRecvUnmatchedMkPreC S K core msg prep drKey rk1 spqrSalt? rSlot rc').cost =
      drKey.cost + rk1.cost + spqrSalt?.cost + rSlot.cost + rc'.cost +
      2008 + K * 39 + min K S.N_dh * 7786 :=
  finishRecvUnmatchedMkPreC_cost_tight S K core msg prep drKey rk1 spqrSalt? rSlot rc'

@[simp] theorem checkBundleProvenanceExactC_cost (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkBundleProvenanceExactC S K st bu :
      Comp pqxdhOps pqPrimIface Δ (.prod .bool (.prod .bool .bool))).cost =
      53 + min K S.N_dh * 419 + K * 3239 := by
  simp only [checkBundleProvenanceExactC, findHonestC, bindV, letV, caseOptV,
    findMV, anyMV, eAny, natEq, asPrincipals, asSpkBundles, asOpkEntries,
    peIkAPk, sbSpkPk, sbPqspkPk, oeOpkPk, pkbIkB, pkbSpkB, pkbPqspkB, pkbOpkB?,
    cost_letC, cost_queryPrim, cost_bytesBeq, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem koskSenderOkC_cost (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).cost = ik.cost + 104 + min K S.N_dh * 206 + K * 69 := by
  simp only [koskSenderOkC, findHonestC, isAdvRegC, letV, bindV, findMV, eAny, isSomeE,
    asPrincipals, asAdvKeys, peIkAPk, cost_letC, cost_queryPrim, cost_bytesBeq,
    cost_boolOr, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
  omega

@[simp] theorem matchIdealAuthHandshakeC_cost {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (ikB : Var Γ₁ (B 32)) (spkB : Var Γ₂ (B 32)) (opkB? : Var Γ₃ (.opt (B 32)))
    (pqspkB : Var Γ₄ (B 1568)) (hdr : Var Γ₅ handshakeHdrTy) (s : Var Γ₆ idealAuthSessionTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (matchIdealAuthHandshakeC ikB spkB opkB? pqspkB hdr s :
      Comp pqxdhOps pqPrimIface Δ .bool).cost = 7340 := by
  simp only [matchIdealAuthHandshakeC, bindV, caseOptV, hdrIkAPk, hdrEkAPk, hdrKemCt,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    cost_queryPrim, cost_bytesBeq, v, Comp.cost, Expr.cost, Ty.wd, PNat.val_ofNat]
  omega

@[simp] theorem hkdfRoC_cost (K : Nat) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfRoC K st sec).cost = sec.cost + 142 + K * 389 := by
  simp only [hkdfRoC, letV, caseOptV, bindV, eFind, asRoCache,
    cost_letC, cost_samplePrim, cost_bytesBeq, PSamp.cost, PSamp.ty, Ty.wd,
    v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

@[simp] theorem rootRoC_cost (K : Nat) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) :
    (rootRoC K st rk dh).cost = rk.cost + dh.cost + 120 + K * 142 := by
  simp only [rootRoC, letV, caseOptV, bindV, eFind, bytes2Eq, asRootRoCache,
    cost_letC, cost_samplePrim, cost_bytesBeq, PSamp.cost, PSamp.ty, Ty.wd,
    v, Comp.cost, Expr.cost, PNat.val_ofNat]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

theorem letV_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (e : Expr pqxdhOps Γ a)
    (k : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b)
    {N : Nat} (hk : (k .zero).cost ≤ N) :
    (letV e k).cost ≤ e.cost + N + 2 := by
  simp only [letV, cost_letC]
  omega

theorem bindV_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (m : Comp pqxdhOps I Γ a)
    (k : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b)
    {M N : Nat} (hm : m.cost ≤ M) (hk : (k .zero).cost ≤ N) :
    (bindV m k).cost ≤ M + N + 1 := by
  simp only [bindV, Comp.cost]
  omega

theorem caseOptV_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (e : Expr pqxdhOps Γ (.opt a))
    (n : Comp pqxdhOps I Γ b)
    (s : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b)
    {M N : Nat} (hn : n.cost ≤ M) (hs : (s .zero).cost ≤ N) :
    (caseOptV e n s).cost ≤ e.cost + max M N + 2 := by
  simp only [caseOptV, Comp.cost]
  omega

theorem caseSumV_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {a b c : PT} (q : Var Γ (.sum a b)) [Ext Γ Δ]
    (l : Var (a :: Δ) a → Comp pqxdhOps I (a :: Δ) c)
    (r : Var (b :: Δ) b → Comp pqxdhOps I (b :: Δ) c)
    {M N : Nat} (hl : (l .zero).cost ≤ M) (hr : (r .zero).cost ≤ N) :
    (caseSumV (v q) l r).cost ≤ max M N + 2 := by
  simp only [caseSumV, v, Comp.cost, Expr.cost]
  omega

theorem initPrinFixedB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrinFixedB K fhst u : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤ 500 + K * 20 := by
  simp only [initPrinFixedB, fhstSetBase, bindV, letV, eAny, natEq,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd,
    peMk, aNone, aInitPrin, cost_letC, cost_samplePrim, cost_queryPrim,
    PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  omega

theorem corruptFixedB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (corruptFixedB K fhst u : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤ 500 + K * 50 := by
  simp only [corruptFixedB, fhstSetBase, letV, caseOptV, eFind, eMap, natEq,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peMk, peUpd,
    aNone, aCorr, cost_letC, v, Comp.cost, Expr.cost]
  simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

theorem genSpkFixedB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genSpkFixedB K fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤ 9500 + K * 30 := by
  simp only [genSpkFixedB, fhstSetBase, bindV, letV, caseOptV, eAny, eFind, natEq, nat2Eq,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd,
    peIkAPk, peSecIKAsign, sbMk, buMk, aNone, aBundle,
    cost_encEC, cost_encKEM, cost_u32OfNat, cost_letC, cost_samplePrim, cost_queryPrim,
    PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  omega

theorem genOpkFixedB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genOpkFixedB K fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤ 500 + K * 30 := by
  simp only [genOpkFixedB, fhstSetBase, bindV, letV, eAny, natEq, nat2Eq, nat3Eq,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd,
    oeMk, aNone, aPk, cost_letC, cost_samplePrim, cost_queryPrim,
    PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat]
  omega

theorem roFixedB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roFixedB K fhst sec : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤ 600 + K * 400 := by
  simp only [roFixedB, fhstSetBase, hkdfRoC_cost, bindV, letV,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRootRoCache, asAdvKeys, stMk, stUpd,
    aNone, aDrKey, cost_letC, v, Comp.cost, Expr.cost]
  omega

theorem roRootFixedB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod (B 32) (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roRootFixedB K fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤ 600 + K * 200 := by
  simp only [roRootFixedB, fhstSetBase, rootRoC_cost, bindV, letV,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asAdvKeys, stMk, stUpd,
    aNone, aRootKdf, cost_letC, v, Comp.cost, Expr.cost]
  omega

theorem registerFixedB_cost_le {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (registerFixedB fhst sk : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤ 500 := by
  simp only [registerFixedB, fhstSetBase, bindV, letV, natEq,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfUpd,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, ahsMk, ahsUpd,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, stMk, stUpd,
    aNone, aPk, cost_letC, cost_queryPrim, cost_bytesLen,
    Ty.wd, v, Comp.cost, Expr.cost, PNat.val_ofNat, bits_32]
  omega

private theorem authCkSendB_cost_tight_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkSendB S K opk idx chalP fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      19000 + K * 14000 + min K S.N_dh * 16000 := by
  cases opk <;>
  · simp only [authCkSendB, sampAtCkC, sampCkPairC, koskBundleOkC_cost, finishAuthHybridSendC_cost,
      hkdfRoC_cost, rootRoC_cost, allocSendSlotE_cost, sidEq_cost, firstMsgADE_cost,
      buildSecretsE_cost, resolveSigPkC, checkBundleSpkHonIdealC, findHonestC, sendGuardE,
      cost_encEC, cost_encKEM, bindV, letV, caseOptV, findMV, anyMV, eFind, eAny, eCaseOpt,
      natEq, natLt, isSomeE, ahsfHybrid, ahsfRecvCount, ahsfSlots, ahsfMkSlots,
      ahsBase, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asUsedSendSessions,
      asRoCache, asRootRoCache, peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      sbSpkPk, sbPqspkPk, pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      aNone, cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesLen, cost_bytesBeq,
      cost_boolOr, cost_litB, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem authCkSendB_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkSendB S K opk idx chalP fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      19000 + slotIdxCost S + K * 14000 + S.N_dh * 28000 := by
  have h := authCkSendB_cost_tight_le S K opk (Δ := Δ) idx chalP fhst x
  have hmin : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  omega

private theorem authCkRecvB_cost_tight_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkRecvB S K opk idx chalP fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      19000 + K * 14000 + min K S.N_dh * 16000 := by
  cases opk <;>
  · simp only [authCkRecvB, sampAtCkC, sampCkPairC, recvFinishTagRunC_cost_tight,
      prepareAuthHybridRecvC_true_cost_tight, prepareAuthHybridRecvC_false_cost_tight,
      finishAuthRecvCkC_cost_tight, allocRecvSlotE_cost, hkdfRoC_cost, rootRoC_cost, firstMsgADE_cost,
      bindV, letV, caseOptV, eCaseOpt, natEq, natLt, isSomeE,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots,
      ahsfUpd, ahsfUpdSlots, ahsBase,
      peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      iasDrKey, iasRk1, iasMkSeed, iasCk1_1,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph,
      parHstDec, parFinishTag, aNone,
      cost_letC, cost_samplePrim, cost_queryPrim, cost_boolOr,
      PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, bits_1]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem authCkRecvB_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkRecvB S K opk idx chalP fhst x : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      19000 + bits S.N_send_tot + K * 14000 + S.N_dh * 28000 := by
  have h := authCkRecvB_cost_tight_le S K opk (Δ := Δ) idx chalP fhst x
  have hmin : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  omega

private theorem authCkStepC_cost_tight_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkStepC S K idx chalP fhst q : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      19500 + K * 15000 + min K S.N_dh * 16000 := by
  unfold authCkStepC
  refine le_trans
    (caseSumV_cost_le _ _ _ (initPrinFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (corruptFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (genSpkFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (genOpkFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (authCkSendB_cost_tight_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (authCkSendB_cost_tight_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (authCkRecvB_cost_tight_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (authCkRecvB_cost_tight_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (roFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (roRootFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
     registerFixedB_cost_le _ _)
    (by omega)

private theorem prfCkHandleDsl_cost_tight_le (S : Setup) (K : Nat) :
    (prfCkHandleDsl S K).cost ≤
      20000 + K * 15000 + min K S.N_dh * 16000 := by
  unfold prfCkHandleDsl
  have h := authCkStepC_cost_tight_le S K
    (Δ := authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool ::
      prfCkStTy :: [prfCkStTy, authQueryTy])
    (.zero : Var (.nat :: .bool :: prfCkStTy :: [prfCkStTy, authQueryTy]) .nat)
    (.zero : Var (.prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy :: [prfCkStTy, authQueryTy]) _)
    (.zero : Var (authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy ::
      [prfCkStTy, authQueryTy]) _)
    (.succ .zero : Var [prfCkStTy, authQueryTy] authQueryTy)
  simp only [bindV, letV, ckSecb, ckIdx, ckChal, ckFhst, cost_letC, v, Comp.cost, Expr.cost]
  omega

private theorem authCkStepC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkStepC S K idx chalP fhst q : Comp pqxdhOps pqPrimIface Δ RSF).cost ≤
      19500 + slotIdxCost S + bits S.N_send_tot + K * 15000 + S.N_dh * 30000 := by
  unfold authCkStepC
  refine le_trans
    (caseSumV_cost_le _ _ _ (initPrinFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (corruptFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (genSpkFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (genOpkFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (authCkSendB_cost_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (authCkSendB_cost_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (authCkRecvB_cost_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (authCkRecvB_cost_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (roFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (roRootFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
     registerFixedB_cost_le _ _)
    (by omega)

theorem prfCkHandleDsl_cost_le (S : Setup) (K : Nat) :
    (prfCkHandleDsl S K).cost ≤
      20000 + slotIdxCost S + bits S.N_send_tot + K * 15000 + S.N_dh * 30000 := by
  unfold prfCkHandleDsl
  have h := authCkStepC_cost_le S K
    (Δ := authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool ::
      prfCkStTy :: [prfCkStTy, authQueryTy])
    (.zero : Var (.nat :: .bool :: prfCkStTy :: [prfCkStTy, authQueryTy]) .nat)
    (.zero : Var (.prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy :: [prfCkStTy, authQueryTy]) _)
    (.zero : Var (authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy ::
      [prfCkStTy, authQueryTy]) _)
    (.succ .zero : Var [prfCkStTy, authQueryTy] authQueryTy)
  simp only [bindV, letV, ckSecb, ckIdx, ckChal, ckFhst, cost_letC, v, Comp.cost, Expr.cost]
  omega

private theorem wrapMkBase_cost_le {Γ₁ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) [Ext Γ₁ Δ] (m : Comp pqxdhOps pqPrimIface Δ RSF)
    {M : Nat} (hm : m.cost ≤ M) :
    (wrapMkBase core m).cost ≤ M + 30 := by
  simp only [wrapMkBase, bindV, mkcMk, mkcSecb, mkcIdx, mkcSentChal, v, Comp.cost, Expr.cost]
  omega

private theorem authMkSendPreB_cost_le_clamped (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkSendPreB S K opk core x : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      15000 + K * 10000 + min K S.N_dh * 20000 := by
  cases opk <;>
  · simp only [authMkSendPreB, koskBundleOkC_cost, finishAuthHybridSendC_cost,
      finishAuthSendMkC_cost_tight, hkdfRoC_cost, rootRoC_cost, allocSendSlotE_cost, sidEq_cost,
      firstMsgADE_cost, buildSecretsE_cost, resolveSigPkC, checkBundleSpkHonIdealC, findHonestC,
      sendGuardE, cost_encEC, cost_encKEM, bindV, letV, caseOptV, findMV, anyMV, eFind, eAny,
      eCaseOpt, natEq, natLt, isSomeE, mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsfUpdSlots, ahsBase,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asUsedSendSessions,
      peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      sbSpkPk, sbPqspkPk, pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      aNone, cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesLen, cost_bytesBeq,
      cost_boolOr, cost_litB, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem authMkSendPreB_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkSendPreB S K opk core x : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      15000 + slotIdxCost S + K * 10000 + S.N_dh * 20000 := by
  refine le_trans (authMkSendPreB_cost_le_clamped S K opk core x) ?_
  have hd := Nat.mul_le_mul_right 20000 (Nat.min_le_right K S.N_dh)
  omega

private theorem authMkRecvPreB_cost_le_clamped (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreB S K opk core x : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      15000 + K * 10000 + min K S.N_dh * 20000 := by
  cases opk <;>
  · simp only [authMkRecvPreB, recvFinishTagRunC_cost_tight,
      prepareAuthHybridRecvC_true_cost_tight, prepareAuthHybridRecvC_false_cost_tight,
      finishAuthRecvMkC_cost_tight, finishRecvUnmatchedMkPreC_cost_tight, hkdfRoC_cost, rootRoC_cost,
      allocRecvSlotE_cost, lookupSendSlotE_cost, sidEq_cost, sameSaltKeyE_cost, firstMsgADE_cost,
      bindV, letV, caseOptV, eFind, eCaseOpt, natEq, natLt, isSomeE,
      mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsfUpdSlots, ahsBase,
      peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      iasSid, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph,
      parHstDec, parFinishTag, aNone,
      cost_letC, cost_samplePrim, cost_queryPrim, cost_boolOr,
      PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, bits_0, bits_1]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem authMkRecvPreB_cost_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreB S K opk core x : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      15000 + slotIdxCost S + bits S.N_send_tot + K * 10000 + S.N_dh * 20000 := by
  refine le_trans (authMkRecvPreB_cost_le_clamped S K opk core x) ?_
  have hd := Nat.mul_le_mul_right 20000 (Nat.min_le_right K S.N_dh)
  omega

private theorem prfMkStepPreC_cost_le_clamped (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPreC S K core q : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      16000 + K * 11000 + min K S.N_dh * 22000 := by
  unfold prfMkStepPreC
  refine le_trans
    (letV_cost_le _ _
      (caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (initPrinFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (corruptFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (genSpkFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (genOpkFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (authMkSendPreB_cost_le_clamped S K true _ _) <|
       caseSumV_cost_le _ _ _ (authMkSendPreB_cost_le_clamped S K false _ _) <|
       caseSumV_cost_le _ _ _ (authMkRecvPreB_cost_le_clamped S K true _ _) <|
       caseSumV_cost_le _ _ _ (authMkRecvPreB_cost_le_clamped S K false _ _) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (roFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (roRootFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
       wrapMkBase_cost_le _ _ (registerFixedB_cost_le _ _)))
    ?_
  simp only [v, Expr.cost]
  omega

private theorem prfMkStepPreC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPreC S K core q : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      16000 + slotIdxCost S + bits S.N_send_tot + K * 11000 + S.N_dh * 22000 := by
  unfold prfMkStepPreC
  refine le_trans
    (letV_cost_le _ _
      (caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (initPrinFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (corruptFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (genSpkFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (genOpkFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (authMkSendPreB_cost_le S K true _ _) <|
       caseSumV_cost_le _ _ _ (authMkSendPreB_cost_le S K false _ _) <|
       caseSumV_cost_le _ _ _ (authMkRecvPreB_cost_le S K true _ _) <|
       caseSumV_cost_le _ _ _ (authMkRecvPreB_cost_le S K false _ _) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (roFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (wrapMkBase_cost_le _ _ (roRootFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
       wrapMkBase_cost_le _ _ (registerFixedB_cost_le _ _)))
    ?_
  simp only [v, Expr.cost]
  omega

private theorem prfMkStepPostC_cost_le_clamped (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (cont : Var Γ₁ prfMkChalContTy) (mk : Var Γ₂ msgKeysTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPostC S K cont mk : Comp pqxdhOps pqPrimIface Δ (.prod authRespTy prfMkCoreTy)).cost ≤
      3500 + K * 4000 + min K S.N_dh * 9000 := by
  simp only [prfMkStepPostC, finishAuthSendMkC_cost_tight, finishAuthRecvMkC_cost_tight,
    bindV, letV, caseSumV, eCaseOpt, mkcMk, ahsfUpdSlots, ahsfMkSlots,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, cost_letC, cost_litB,
    v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem prfMkStepPostC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (cont : Var Γ₁ prfMkChalContTy) (mk : Var Γ₂ msgKeysTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPostC S K cont mk : Comp pqxdhOps pqPrimIface Δ (.prod authRespTy prfMkCoreTy)).cost ≤
      3500 + K * 4000 + S.N_dh * 9000 := by
  refine le_trans (prfMkStepPostC_cost_le_clamped S K cont mk) ?_
  have hd := Nat.mul_le_mul_right 9000 (Nat.min_le_right K S.N_dh)
  omega

private theorem prfMsgKeysHandleDsl_cost_le_clamped (S : Setup) (K : Nat) :
    (prfMsgKeysHandleDsl S K).cost ≤
      25000 + K * 20000 + min K S.N_dh * 35000 := by
  unfold prfMsgKeysHandleDsl
  have hPre := prfMkStepPreC_cost_le_clamped S K
    (Δ := prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy])
    (.zero : Var (prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy]) prfMkCoreTy)
    (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy)
  have hPost := prfMkStepPostC_cost_le_clamped S K
    (Δ := msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy])
    (.zero : Var (prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy]) prfMkChalContTy)
    (.zero : Var (msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy]) msgKeysTy)
  simp only [bindV, letV, caseSumV, natEq, aNone,
    cost_liftPrimComp, cost_letC, cost_queryDeriveMk,
    v, Comp.cost, Expr.cost, bits_0, bits_1]
  omega

theorem prfMsgKeysHandleDsl_cost_le (S : Setup) (K : Nat) :
    (prfMsgKeysHandleDsl S K).cost ≤
      25000 + slotIdxCost S + bits S.N_send_tot + K * 20000 + S.N_dh * 35000 := by
  unfold prfMsgKeysHandleDsl
  have hPre := prfMkStepPreC_cost_le S K
    (Δ := prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy])
    (.zero : Var (prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy]) prfMkCoreTy)
    (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy)
  have hPost := prfMkStepPostC_cost_le S K
    (Δ := msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy])
    (.zero : Var (prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy]) prfMkChalContTy)
    (.zero : Var (msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy]) msgKeysTy)
  simp only [bindV, letV, caseSumV, natEq, aNone,
    cost_liftPrimComp, cost_letC, cost_queryDeriveMk,
    v, Comp.cost, Expr.cost, bits_0, bits_1]
  omega

/-! ## Static and semantic query bounds -/

def primW : pqPrimIface.Tag → ℕ := fun _ => 1
def primWS : pqPrimIface.smp.Samp → ℕ := fun _ => 0

def mkPrimW : pqPrfMkIface.Tag → ℕ
  | .inl _ => 1
  | .inr _ => 0

def mkWS : pqPrfMkIface.smp.Samp → ℕ := fun _ => 0

@[simp] theorem queries_letC {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) {Γ : List PT} {a b : PT}
    (e : Expr pqxdhOps Γ a) (k : Comp pqxdhOps I (a :: Γ) b) :
    (Comp.letC e k).queries w ws = k.queries w ws := by
  simp [Comp.letC, Comp.queries]

@[simp] theorem queries_liftPrimComp_mkPrim {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftPrimComp (C := msgKeyPrfOracle) c).queries mkPrimW mkWS = c.queries primW primWS := by
  induction c with
  | ret _ => rfl
  | bind _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | ite _ _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | caseOpt _ _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | caseSum _ _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | sample _ _ => rfl
  | query _ _ => rfl
  | iter _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | findM _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | anyM _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | mapM _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | consumeFirstM _ _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | foldM _ _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]

@[simp] theorem initPrinFixedB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrinFixedB K fhst u : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS = 2 := by
  simp [initPrinFixedB, bindV, letV, samplePrim, queryPrim, primW, primWS, Comp.queries]

@[simp] theorem corruptFixedB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (corruptFixedB K fhst u : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS = 0 := by
  simp [corruptFixedB, letV, caseOptV, Comp.queries]

@[simp] theorem genSpkFixedB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genSpkFixedB K fhst x : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS = 4 := by
  simp [genSpkFixedB, bindV, letV, caseOptV, samplePrim, queryPrim, primW, primWS, Comp.queries]

@[simp] theorem genOpkFixedB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (genOpkFixedB K fhst x : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS = 1 := by
  simp [genOpkFixedB, bindV, letV, samplePrim, queryPrim, primW, primWS, Comp.queries]

@[simp] theorem roFixedB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roFixedB K fhst sec : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS = 0 := by
  simp [roFixedB, hkdfRoC, bindV, letV, caseOptV, samplePrim, primWS, Comp.queries]

@[simp] theorem roRootFixedB_queries (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod (B 32) (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (roRootFixedB K fhst x : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS = 0 := by
  simp [roRootFixedB, rootRoC, bindV, letV, caseOptV, samplePrim, primWS, Comp.queries]

@[simp] theorem registerFixedB_queries {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (registerFixedB fhst sk : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS = 2 := by
  simp [registerFixedB, bindV, letV, queryPrim, primW, Comp.queries]

@[simp] theorem koskBundleOkC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC S K st bu : Comp pqxdhOps pqPrimIface Δ .bool).queries primW primWS =
      3 + min K S.N_dh * 6 := by
  simp only [koskBundleOkC, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
    bindV, letV, caseOptV, findMV, anyMV, queries_letC, queryPrim, primW, Comp.queries]
  omega

@[simp] theorem koskSenderOkC_queries (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ authStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).queries primW primWS = 1 + min K S.N_dh * 2 := by
  simp only [koskSenderOkC, findHonestC, isAdvRegC, bindV, letV, findMV,
    queries_letC, queryPrim, primW, Comp.queries]
  omega

@[simp] theorem checkBundleProvenanceExactC_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkBundleProvenanceExactC S K st bu :
      Comp pqxdhOps pqPrimIface Δ (.prod .bool (.prod .bool .bool))).queries primW primWS =
      min K S.N_dh * 4 := by
  simp only [checkBundleProvenanceExactC, findHonestC, bindV, letV, caseOptV, findMV, anyMV,
    queries_letC, queryPrim, primW, Comp.queries]
  omega

@[simp] theorem matchIdealAuthHandshakeC_queries {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (ikB : Var Γ₁ (B 32)) (spkB : Var Γ₂ (B 32)) (opkB? : Var Γ₃ (.opt (B 32)))
    (pqspkB : Var Γ₄ (B 1568)) (hdr : Var Γ₅ handshakeHdrTy) (s : Var Γ₆ idealAuthSessionTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (matchIdealAuthHandshakeC ikB spkB opkB? pqspkB hdr s :
      Comp pqxdhOps pqPrimIface Δ .bool).queries primW primWS = 10 := by
  simp only [matchIdealAuthHandshakeC, bindV, caseOptV, queryPrim, primW, Comp.queries]
  omega

@[simp] theorem recvFinishTagRunC_queries (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    (recvFinishTagRunC S K tag res?).queries primW primWS =
      min K S.N_dh * 12 := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC,
    bindV, letV, caseOptV, caseSumV, findMV, consumeFirstMV,
    queries_letC, queryPrim, primW, Comp.queries]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

@[simp] theorem finishAuthHybridSendC_queries (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    (finishAuthHybridSendC S K hst args).queries primW primWS = min K S.N_dh * 8 := by
  simp only [finishAuthHybridSendC, checkBundleProvenanceExactC_queries, checkBundleSpkHonIdealC,
    findHonestC, bindV, letV, caseOptV, findMV, anyMV, queries_letC, queryPrim, primW, Comp.queries]
  omega

@[simp] theorem prepareAuthHybridRecvC_true_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K true hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).queries primW primWS =
      11 + min K S.N_dh * 14 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC_queries, matchIdealAuthHandshakeC_queries,
    findHonestC, bindV, letV, caseOptV, findMV, queries_letC, queryPrim, primW, Comp.queries,
    ite_true]
  omega

@[simp] theorem prepareAuthHybridRecvC_false_queries (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K false hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).queries primW primWS =
      10 + min K S.N_dh * 14 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC_queries, matchIdealAuthHandshakeC_queries,
    findHonestC, bindV, letV, caseOptV, findMV, queries_letC, queryPrim, primW, Comp.queries,
    Bool.false_eq_true, ite_false]
  omega

theorem letV_queries_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ : List PT} {a b : PT} (e : Expr pqxdhOps Γ a)
    (k : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b)
    {N : Nat} (hk : (k .zero).queries w ws ≤ N) :
    (letV e k).queries w ws ≤ N := by
  simpa only [letV, queries_letC] using hk

theorem caseSumV_queries_le {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    {Γ Δ : List PT} {a b c : PT} (q : Var Γ (.sum a b)) [Ext Γ Δ]
    (l : Var (a :: Δ) a → Comp pqxdhOps I (a :: Δ) c)
    (r : Var (b :: Δ) b → Comp pqxdhOps I (b :: Δ) c)
    {M N : Nat} (hl : (l .zero).queries w ws ≤ M) (hr : (r .zero).queries w ws ≤ N) :
    (caseSumV (v q) l r).queries w ws ≤ max M N := by
  simp only [caseSumV, Comp.queries]
  omega

theorem prfCkInitDsl_queries (S : Setup) :
    (prfCkInitDsl S).queries primW primWS = 0 := by
  simp [prfCkInitDsl, bindV, samplePrim, primWS, Comp.queries]

theorem prfCkFinishDsl_queries (S : Setup) (K : Nat) :
    (prfCkFinishDsl S K).queries primW primWS = min K S.N_dh * 5 := by
  simp only [prfCkFinishDsl, finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl,
    allHonestEcPksAuthDslK, letV, queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
  omega

private theorem authCkSendB_queries_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkSendB S K opk idx chalP fhst x : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS ≤
      19 + S.N_dh * 26 := by
  cases opk <;>
  · simp only [authCkSendB, sampAtCkC, sampCkPairC, koskBundleOkC_queries,
      finishAuthHybridSendC_queries, hkdfRoC, rootRoC, resolveSigPkC, checkBundleSpkHonIdealC,
      findHonestC, bindV, letV, caseOptV, findMV, anyMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem authCkRecvB_queries_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkRecvB S K opk idx chalP fhst x : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS ≤
      19 + S.N_dh * 26 := by
  cases opk <;>
  · simp only [authCkRecvB, sampAtCkC, sampCkPairC, finishAuthRecvCkC,
      prepareAuthHybridRecvC_true_queries, prepareAuthHybridRecvC_false_queries,
      recvFinishTagRunC_queries, hkdfRoC, rootRoC, bindV, letV, caseOptV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem authCkStepC_queries_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkStepC S K idx chalP fhst q : Comp pqxdhOps pqPrimIface Δ RSF).queries primW primWS ≤
      19 + S.N_dh * 26 := by
  unfold authCkStepC
  refine le_trans
    (caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [initPrinFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [corruptFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [genSpkFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [genOpkFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (authCkSendB_queries_le S K true _ _ _ _) <|
     caseSumV_queries_le _ _ _ _ _ (authCkSendB_queries_le S K false _ _ _ _) <|
     caseSumV_queries_le _ _ _ _ _ (authCkRecvB_queries_le S K true _ _ _ _) <|
     caseSumV_queries_le _ _ _ _ _ (authCkRecvB_queries_le S K false _ _ _ _) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [roFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [roRootFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [Comp.queries]; rfl)) <|
     Nat.le_of_eq (by simp only [registerFixedB_queries]; rfl))
    (by omega)

theorem prfCkHandleDsl_queries_le (S : Setup) (K : Nat) :
    (prfCkHandleDsl S K).queries primW primWS ≤ 19 + S.N_dh * 26 := by
  unfold prfCkHandleDsl
  have h := authCkStepC_queries_le S K
    (Δ := authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool ::
      prfCkStTy :: [prfCkStTy, authQueryTy])
    (.zero : Var (.nat :: .bool :: prfCkStTy :: [prfCkStTy, authQueryTy]) .nat)
    (.zero : Var (.prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy :: [prfCkStTy, authQueryTy]) _)
    (.zero : Var (authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy ::
      [prfCkStTy, authQueryTy]) _)
    (.succ .zero : Var [prfCkStTy, authQueryTy] authQueryTy)
  simp only [bindV, letV, queries_letC, Comp.queries]
  omega

theorem prfMsgKeysInitDsl_queries_prim (S : Setup) :
    (prfMsgKeysInitDsl S).queries mkPrimW mkWS = 0 := by
  simp [prfMsgKeysInitDsl, bindV, sampleChal, mkWS, Comp.queries]

theorem prfMsgKeysFinishDsl_queries_prim (S : Setup) (K : Nat) :
    (prfMsgKeysFinishDsl S K).queries mkPrimW mkWS = min K S.N_dh * 5 := by
  simp only [prfMsgKeysFinishDsl, finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl,
    allHonestEcPksAuthDslK, letV, queries_liftPrimComp_mkPrim, queries_letC,
    samplePrim, queryPrim, primW, primWS, Comp.queries]
  omega

@[simp] private theorem wrapMkBase_queries {Γ₁ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) [Ext Γ₁ Δ] (m : Comp pqxdhOps pqPrimIface Δ RSF) :
    (wrapMkBase core m).queries primW primWS = m.queries primW primWS := by
  simp [wrapMkBase, bindV, Comp.queries]

private theorem authMkSendPreB_queries_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkSendPreB S K opk core x :
      Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).queries primW primWS ≤ 20 + S.N_dh * 26 := by
  cases opk <;>
  · simp only [authMkSendPreB, finishAuthSendMkC, koskBundleOkC_queries,
      finishAuthHybridSendC_queries, hkdfRoC, rootRoC, resolveSigPkC, checkBundleSpkHonIdealC,
      findHonestC, bindV, letV, caseOptV, findMV, anyMV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem authMkRecvPreB_queries_le (S : Setup) (K : Nat) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreB S K opk core x :
      Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).queries primW primWS ≤ 20 + S.N_dh * 26 := by
  cases opk <;>
  · simp only [authMkRecvPreB, finishAuthRecvMkC, finishRecvUnmatchedMkPreC,
      prepareAuthHybridRecvC_true_queries, prepareAuthHybridRecvC_false_queries,
      recvFinishTagRunC_queries, hkdfRoC, rootRoC, bindV, letV, caseOptV,
      queries_letC, samplePrim, queryPrim, primW, primWS, Comp.queries]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem prfMkStepPreC_queries_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPreC S K core q : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).queries primW primWS ≤
      20 + S.N_dh * 26 := by
  unfold prfMkStepPreC
  refine letV_queries_le _ _ _ _ ?_
  refine le_trans
    (caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [wrapMkBase_queries, initPrinFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [wrapMkBase_queries, corruptFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [wrapMkBase_queries, genSpkFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [wrapMkBase_queries, genOpkFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (authMkSendPreB_queries_le S K true _ _) <|
     caseSumV_queries_le _ _ _ _ _ (authMkSendPreB_queries_le S K false _ _) <|
     caseSumV_queries_le _ _ _ _ _ (authMkRecvPreB_queries_le S K true _ _) <|
     caseSumV_queries_le _ _ _ _ _ (authMkRecvPreB_queries_le S K false _ _) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [wrapMkBase_queries, roFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [wrapMkBase_queries, roRootFixedB_queries]; rfl)) <|
     caseSumV_queries_le _ _ _ _ _ (Nat.le_of_eq (by simp only [Comp.queries]; rfl)) <|
     Nat.le_of_eq (by simp only [wrapMkBase_queries, registerFixedB_queries]; rfl))
    (by omega)

private theorem prfMkStepPostC_queries_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (cont : Var Γ₁ prfMkChalContTy) (mk : Var Γ₂ msgKeysTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPostC S K cont mk :
      Comp pqxdhOps pqPrimIface Δ (.prod authRespTy prfMkCoreTy)).queries primW primWS ≤
      1 + S.N_dh * 12 := by
  simp only [prfMkStepPostC, finishAuthSendMkC, finishAuthRecvMkC,
    finishAuthHybridSendC_queries, recvFinishTagRunC_queries,
    bindV, letV, caseSumV, queries_letC, queryPrim, primW, Comp.queries]
  omega

theorem prfMsgKeysHandleDsl_queries_prim_le (S : Setup) (K : Nat) :
    (prfMsgKeysHandleDsl S K).queries mkPrimW mkWS ≤ 28 + S.N_dh * 38 := by
  unfold prfMsgKeysHandleDsl
  have hPre := prfMkStepPreC_queries_le S K
    (Δ := prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy])
    (.zero : Var (prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy]) prfMkCoreTy)
    (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy)
  have hPost := prfMkStepPostC_queries_le S K
    (Δ := msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy])
    (.zero : Var (prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy]) prfMkChalContTy)
    (.zero : Var (msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, authQueryTy]) msgKeysTy)
  simp only [bindV, letV, caseSumV, queries_liftPrimComp_mkPrim, queries_letC,
    queryDeriveMk, pqPrfMkIface, mkPrimW, Comp.queries]
  omega

/-! ## Reduction-level cost and query bounds -/

private theorem prfCkInitDslK_cost_eq (S : Setup) (K : Nat) :
    (prfCkInitDslK S K).cost = 71 + bits (min K S.N_sess_tot) := by
  simp only [prfCkInitDslK, bindV, emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE,
    ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, cost_samplePrim, PSamp.cost,
    Ty.wd, v, Comp.cost, Expr.cost, bits_0]
  omega

private theorem prfMsgKeysInitDslK_cost_eq (S : Setup) (K : Nat) :
    (prfMsgKeysInitDslK S K).cost =
      72 + bits (min K S.N_sess_tot) + bits (min K S.N_recv_tot + 1) := by
  simp only [prfMsgKeysInitDslK, bindV, mkcMk, emptyAuthHybridStFixedE, emptyAuthHybridStE,
    emptyAuthStE, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk,
    cost_sampleChal, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost, bits_0]
  omega

private theorem prfCkRedProg_totalCost_le_clamped (S : Setup) (K q : Nat) :
    (prfCkRedProg S K).totalCost q ≤
      71 + bits (min K S.N_sess_tot) +
      q * (20032 + K * 15000 + min K S.N_dh * 16000) +
      (114 + min K S.N_dh * 413 + (min K S.N_dh) ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  simp only [CostedReduction.totalCost, prfCkRedProg, authCodec,
    prfCkInitDslK_cost_eq, prfCkFinishDsl_cost_tight]
  have hH := prfCkHandleDsl_cost_tight_le S K
  have hMax : max pqPrimIface.uCost ((prfCkHandleDsl S K).cost + 32) =
      (prfCkHandleDsl S K).cost + 32 := by
    change max 1 ((prfCkHandleDsl S K).cost + 32) = (prfCkHandleDsl S K).cost + 32
    omega
  rw [hMax]
  have hMul : q * ((prfCkHandleDsl S K).cost + 32) ≤
      q * (20032 + K * 15000 + min K S.N_dh * 16000) :=
    Nat.mul_le_mul_left q (by omega)
  omega

theorem prfCkRedProg_totalCost_le (S : Setup) (K q : Nat) :
    (prfCkRedProg S K).totalCost q ≤
      71 + bits S.N_sess_tot +
      q * (20032 + slotIdxCost S + bits S.N_send_tot + K * 15000 + S.N_dh * 30000) +
      (114 + S.N_dh * 413 + S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  refine le_trans (prfCkRedProg_totalCost_le_clamped S K q) ?_
  have hb : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := by
    simp only [bits]
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.min_le_right _ _)) 1
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hd2 : (min K S.N_dh) ^ 2 ≤ S.N_dh ^ 2 := Nat.pow_le_pow_left hd 2
  have hStep : 20032 + K * 15000 + min K S.N_dh * 16000 ≤
      20032 + slotIdxCost S + bits S.N_send_tot + K * 15000 + S.N_dh * 30000 := by
    have := Nat.mul_le_mul_right 16000 hd
    omega
  have hMul := Nat.mul_le_mul_left q hStep
  have := Nat.mul_le_mul_right 413 hd
  have := Nat.mul_le_mul_right 1088 hd2
  omega

theorem prfCkRedProg_totalCost_security_le (S : Setup) (b : QueryBudget) :
    (prfCkRedProg S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine le_trans (prfCkRedProg_totalCost_le_clamped S b.q_total b.q_total) ?_
  have hbSess : bits (min b.q_total S.N_sess_tot) ≤ min b.q_total S.N_sess_tot + 1 := by
    rcases min b.q_total S.N_sess_tot with _ | n
    · simp [bits]
    · exact le_trans (bits_le_self (by omega)) (by omega)
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  generalize b.q_total = q at *
  set md := min q S.N_dh
  set ms := min q S.N_sess_tot
  set lg := Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot
  nlinarith [Nat.zero_le (q * md), Nat.zero_le (q * ms), Nat.zero_le (md * ms),
    Nat.zero_le lg, Nat.zero_le (q * lg)]

theorem prfCkRedProg_totalQueries_le (S : Setup) (K q : Nat) :
    (prfCkRedProg S K).totalQueries primW primWS q ≤
      q * (19 + S.N_dh * 26) + S.N_dh * 5 := by
  have hInit : (prfCkInitDslK S K).queries primW primWS = 0 := by
    simp [prfCkInitDslK, bindV, samplePrim, primWS, Comp.queries]
  simp only [CostedReduction.totalQueries, prfCkRedProg, authCodec,
    hInit, prfCkFinishDsl_queries]
  have hMul := Nat.mul_le_mul_left q (prfCkHandleDsl_queries_le S K)
  have hFin := Nat.mul_le_mul_right 5 (Nat.min_le_right K S.N_dh)
  omega

private theorem prfMsgKeysRedProg_totalCost_le_clamped (S : Setup) (K q : Nat) :
    (prfMsgKeysRedProg S K).totalCost q ≤
      72 + bits (min K S.N_sess_tot) + bits (min K S.N_recv_tot + 1) +
      q * (25032 + K * 20000 + min K S.N_dh * 35000) +
      (118 + min K S.N_dh * 413 + (min K S.N_dh) ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  simp only [CostedReduction.totalCost, prfMsgKeysRedProg, authCodec,
    prfMsgKeysInitDslK_cost_eq, prfMsgKeysFinishDsl_cost_tight]
  have hH := prfMsgKeysHandleDsl_cost_le_clamped S K
  have hMax : max pqPrfMkIface.uCost ((prfMsgKeysHandleDsl S K).cost + 32) =
      (prfMsgKeysHandleDsl S K).cost + 32 := by
    change max 1 ((prfMsgKeysHandleDsl S K).cost + 32) = (prfMsgKeysHandleDsl S K).cost + 32
    omega
  rw [hMax]
  have hMul : q * ((prfMsgKeysHandleDsl S K).cost + 32) ≤
      q * (25032 + K * 20000 + min K S.N_dh * 35000) :=
    Nat.mul_le_mul_left q (by omega)
  omega

theorem prfMsgKeysRedProg_totalCost_le (S : Setup) (K q : Nat) :
    (prfMsgKeysRedProg S K).totalCost q ≤
      72 + bits S.N_sess_tot + bits (S.N_recv_tot + 1) +
      q * (25032 + slotIdxCost S + bits S.N_send_tot + K * 20000 + S.N_dh * 35000) +
      (118 + S.N_dh * 413 + S.N_dh ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  refine le_trans (prfMsgKeysRedProg_totalCost_le_clamped S K q) ?_
  have hb1 : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := by
    simp only [bits]
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.min_le_right _ _)) 1
  have hb2 : bits (min K S.N_recv_tot + 1) ≤ bits (S.N_recv_tot + 1) := by
    simp only [bits]
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right (Nat.min_le_right _ _) 1)) 1
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hd2 : (min K S.N_dh) ^ 2 ≤ S.N_dh ^ 2 := Nat.pow_le_pow_left hd 2
  have hStep : 25032 + K * 20000 + min K S.N_dh * 35000 ≤
      25032 + slotIdxCost S + bits S.N_send_tot + K * 20000 + S.N_dh * 35000 := by
    have := Nat.mul_le_mul_right 35000 hd
    omega
  have hMul := Nat.mul_le_mul_left q hStep
  have := Nat.mul_le_mul_right 413 hd
  have := Nat.mul_le_mul_right 1088 hd2
  omega

theorem prfMsgKeysRedProg_totalCost_security_le (S : Setup) (b : QueryBudget) :
    (prfMsgKeysRedProg S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine le_trans (prfMsgKeysRedProg_totalCost_le_clamped S b.q_total b.q_total) ?_
  have hRecvLe : min b.q_total S.N_recv_tot ≤ min b.q_total S.N_sess_tot := by
    unfold Setup.N_sess_tot; omega
  have hbSess : bits (min b.q_total S.N_sess_tot) ≤ min b.q_total S.N_sess_tot + 1 := by
    rcases min b.q_total S.N_sess_tot with _ | n
    · simp [bits]
    · exact le_trans (bits_le_self (by omega)) (by omega)
  have hbRecv : bits (min b.q_total S.N_recv_tot + 1) ≤ min b.q_total S.N_sess_tot + 2 := by
    have h1 : bits (min b.q_total S.N_recv_tot + 1) ≤ min b.q_total S.N_recv_tot + 1 :=
      bits_le_self (by omega)
    omega
  have hMdQ : min b.q_total S.N_dh ≤ b.q_total := Nat.min_le_left _ _
  have hQMd : b.q_total * min b.q_total S.N_dh ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left b.q_total hMdQ
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  generalize b.q_total = q at *
  set md := min q S.N_dh
  set ms := min q S.N_sess_tot
  set lg := Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot
  nlinarith [Nat.zero_le (q * md), Nat.zero_le (q * ms), Nat.zero_le (md * ms),
    Nat.zero_le lg, Nat.zero_le (q * lg)]

theorem prfMsgKeysRedProg_totalQueries_prim_le (S : Setup) (K q : Nat) :
    (prfMsgKeysRedProg S K).totalQueries mkPrimW mkWS q ≤
      q * (28 + S.N_dh * 38) + S.N_dh * 5 := by
  have hInit : (prfMsgKeysInitDslK S K).queries mkPrimW mkWS = 0 := by
    simp [prfMsgKeysInitDslK, bindV, sampleChal, mkWS, Comp.queries]
  simp only [CostedReduction.totalQueries, prfMsgKeysRedProg, authCodec,
    hInit, prfMsgKeysFinishDsl_queries_prim]
  have hMul := Nat.mul_le_mul_left q (prfMsgKeysHandleDsl_queries_prim_le S K)
  have hFin := Nat.mul_le_mul_right 5 (Nat.min_le_right K S.N_dh)
  omega

@[simp] theorem eval_letC {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (e : Expr pqxdhOps Γ a) (k : Comp pqxdhOps I (a :: Γ) b) (env : Env Γ) :
    (Comp.letC e k).eval env = k.eval (.cons (e.eval env) env) := by
  simp [Comp.letC, Comp.eval]

theorem bits_le_succ (n : ℕ) : bits n ≤ n + 1 := by
  rcases n with _ | n
  · simp [bits]
  · exact le_trans (bits_le_self (by omega)) (by omega)

theorem slotIdxCost_le (S : Setup) : slotIdxCost S ≤ 10 + S.N_sess_tot := by
  unfold slotIdxCost Setup.N_sess_tot Setup.N_send_tot
    Setup.N_send_opk_tot Setup.N_send_no_opk_tot
  by_cases h : S.N_id = 0
  · simp [h, bits_0]
  · have hpos : 1 ≤ S.N_id := by omega
    have h1 : S.N_send_opk ≤ S.N_id * S.N_send_opk := by
      simpa using Nat.mul_le_mul_right S.N_send_opk hpos
    have h2 : S.N_send_no_opk ≤ S.N_id * S.N_send_no_opk := by
      simpa using Nat.mul_le_mul_right S.N_send_no_opk hpos
    have hb1 := bits_le_succ S.N_send_opk
    have hb2 := bits_le_succ (S.N_id * S.N_send_opk)
    have hb3 := bits_le_succ S.N_send_no_opk
    simp only [h, ite_false]
    omega

def chalPrimW {C : ChallengerOracle} : (pqChalIface C).Tag → ℕ
  | .inl _ => 1
  | .inr _ => 0

def chalWS {C : ChallengerOracle} : (pqChalIface C).smp.Samp → ℕ := fun _ => 0

@[simp] theorem queries_liftPrimComp_prim {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftPrimComp (C := C) c).queries chalPrimW chalWS = c.queries primW primWS := by
  induction c with
  | ret _ => rfl
  | bind _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | ite _ _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | caseOpt _ _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | caseSum _ _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | sample _ _ => rfl
  | query _ _ => rfl
  | iter _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | findM _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | anyM _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | mapM _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | consumeFirstM _ _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | foldM _ _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]

theorem pqPrimIface_hw :
    ∀ (g : pqPrimIface.Tag) (x : (pqPrimIface.dom g).denote),
      isPrimQuery₀ (pqPrimIface.enc g x) = true → 1 ≤ primW g :=
  fun _ _ _ => le_rfl

theorem pqPrimIface_hU :
    ∀ n : ℕ, (pqPrimIface.fwdU n).IsQueryBoundP (fun q => isPrimQuery₀ q = true) 0 :=
  fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec)
    (fun q => isPrimQuery₀ q = true) (Sum.inl n) 0).2 (fun h => by cases h)

theorem queryBound_eval1 {κ : Type} {G : OracleSpec κ} {C : GameCodec pqSig G}
    {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {rIn aIn aOut ch rIn2 out : PT}
    (R : TwoStageCostedReduction pqxdhOps I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (A : aIn.denote → OracleComp (unifSpec + G) aOut.denote)
    (x : rIn.denote) (fuel : ℕ) (dflt : aOut.denote) :
    (R.eval1 A x fuel dflt).IsQueryBoundP P (R.totalQueries w ws fuel) :=
  (_root_.ReductionDsl.TwoStageCostedReduction.eval1_queryBound R P w ws hw hU A x fuel dflt).mono
    (by
      simp only [TwoStageCostedReduction.totalQueries]
      have := Nat.mul_le_mul_left fuel (Nat.le_max_left (R.handlePre.queries w ws) (R.handlePost.queries w ws))
      omega)

theorem queryBound_eval2 {κ : Type} {G : OracleSpec κ} {C : GameCodec pqSig G}
    {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {rIn aIn aOut ch rIn2 out : PT}
    (R : TwoStageCostedReduction pqxdhOps I G C rIn aIn aOut ch rIn2 out)
    (P : ι → Prop) [DecidablePred P] (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hw : ∀ g x, P (I.enc g x) → 1 ≤ w g)
    (hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0)
    (m : Mid G aOut.denote R.π.denote R.σ.denote ch.denote)
    (y : rIn2.denote) (fuel : ℕ) (dflt : aOut.denote) :
    (R.eval2 m y fuel dflt).IsQueryBoundP P (R.totalQueries w ws fuel) :=
  (_root_.ReductionDsl.TwoStageCostedReduction.eval2_queryBound R P w ws hw hU m y fuel dflt).mono
    (by
      simp only [TwoStageCostedReduction.totalQueries]
      have := Nat.mul_le_mul_left fuel (Nat.le_max_right (R.handlePre.queries w ws) (R.handlePost.queries w ws))
      omega)

end SignalPqxdh.Security.ReductionDsl.AuthPrf

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

export SignalPqxdh.Security.ReductionDsl.AuthPrf
  (bits_le_succ slotIdxCost_le primW primWS chalPrimW chalWS
   pqPrimIface_hw pqPrimIface_hU queryBound_eval1 queryBound_eval2
   checkBundleProvenanceExactC_cost koskSenderOkC_cost matchIdealAuthHandshakeC_cost
   hkdfRoC_cost rootRoC_cost)

end SignalPqxdh.Security.ReductionDsl.AuthAead
