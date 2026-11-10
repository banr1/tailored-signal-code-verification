/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc
public import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.GhostStep

/-!
# Snapshot Seed Derivation, Known-Seed Decryption, and SPQR Wrappers

Defines atomic `ReductionDsl` expressions and computations over `atomicSessionOps` for chain-key
iteration, corruption-snapshot message-key derivation, known-seed decryption, wire/curve checks,
and SPQR send/receive wrappers, with evaluation, cost, and description-bit bounds.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits bits_mono iterM
  atomicSig atomicFig8Ops atomicSessionOps
  B U32 U64 BV128 BV256 BV512 PK IdKey PlainT PtT GhostStT
  AtomicPureOp AtomicSymOp AtomicGroupOp AtomicPtDecOp AtomicCurveCheckOp
  atomicPtDecOps atomicCurveCheckOps
  partyToBool boolToParty signalHdrT signalParsedT ghostPartsT ghostSplitEval
  drSenderChainT drRecvChainT
  lpubT lpubV lctT lctV wireSaltCtT wireSaltCtV wireSaltCtOfV fig8CtT fig8CtV fig8HdrT salt32V)
open CryptoGames (Party effectiveHkdfSalt32)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.HMAC (keyToBytes32 hmacWith bytesToWord64LE)
open CryptoGames.HKDF (bytesToKey32 deriveMessageKeys)
open CryptoGames.Ratchet (keyToBytesVec32 chainHmac chainKeySeed messageKeySeed
  padOrTruncatePlain)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lPubOf ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimState toGhost mkPub toWire tagBytes
  simParseRecvC simKDecryptFig8)
open CryptoGames.Ratchet.LibsignalSimC (chainKeyAfter chainSeedAt snapshotMessageKeySeed)
open CryptoGames.SM (partyEnc partyDec partyEnc_other partyDec_partyEnc partyEnc_partyDec
  boolEq boolEq_eval otherE otherE_eval sendsInE sendsInE_eval minN minN_eval pGet pGet_eval)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey PrivateKey
  GhostState SignalMessage Params ChainKey SenderChain ReceiverChain MessageKeyGenerator
  rootCreateChain aesCbcDecrypt signalWireCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchetRepr (addrBytes serviceIdParse uuidTryParse utf8)
open CryptoVerification.SpqrV1Sync.SendTotal (TopStateTight)
open CryptoVerification.E2E (Bytes paramsV1 paramsIdsWithSpqr serializedPartyAddresses
  partyAddressName partyDeviceId)
open Computational.Proofs.ReductionDsl.Fig8Atomic (bytesToKey32_keyToBytes32
  keyToBytes32_bytesToKey32 hmacWith_length toLEBytes8_length
  atomicPureOps_eval_signalMsgParse_lossless wireSaltCtOfV_wireSaltCtV
  lPubOfExpr lPubOfExpr_eval lPubOfExpr_cost)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (spqrSendAtomicC spqrSendAtomicC_eval spqrSendAtomicC_cost spqrSendAtomicC_queries
   spqrRecvAtomicC spqrRecvAtomicC_eval spqrRecvAtomicC_cost spqrRecvAtomicC_queries)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (simBaseT snapT simBaseEnc snapEnc snapDec)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (sOpPure eval_sOpPure cost_sOpPure descBits_sOpPure
   sOpSym eval_sOpSym cost_sOpSym descBits_sOpSym
   sOpGrp eval_sOpGrp cost_sOpGrp descBits_sOpGrp
   sOpPtDec eval_sOpPtDec cost_sOpPtDec descBits_sOpPtDec
   sOpCurve eval_sOpCurve cost_sOpCurve descBits_sOpCurve
   eLet eval_eLet cost_eLet descBits_eLet
   idKeyAtomLitE eval_idKeyAtomLitE cost_idKeyAtomLitE idKeyAtomLitE_descBits_le
   liftFig8Expr liftFig8Expr_eval liftFig8Expr_cost liftFig8Expr_descBits
   ssPq ssUnackA bits_zero bits_eq_of_bounds bits_le_of_lt_pow)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc
  (small_bits_bounds lPubOfExpr_descBits_le
   spqrSendAtomicC_descBits_le spqrRecvAtomicC_descBits_le)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits atomicSymOpDescBits
   atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto

/-! ## Chain-key iteration -/

section ChainIter

def chainStepFn (F : CryptoGames.LibsignalSession.ShaCompress) (k : BitVec 256) : BitVec 256 :=
  bytesToKey32 (chainHmac F k chainKeySeed)

theorem chainKeyAfter_eq_iterate (F : CryptoGames.LibsignalSession.ShaCompress) :
    ∀ (n : ℕ) (k : BitVec 256), chainKeyAfter F n k = (chainStepFn F)^[n] k
  | 0, _ => rfl
  | n + 1, k => by
    rw [Function.iterate_succ_apply]
    exact chainKeyAfter_eq_iterate F n (chainStepFn F k)

def chainCountStep (F : CryptoGames.LibsignalSession.ShaCompress) (x : BitVec 256 × ℕ) :
    BitVec 256 × ℕ :=
  if x.2 = 0 then x else (chainStepFn F x.1, x.2 - 1)

theorem chainCountStep_iterate (F : CryptoGames.LibsignalSession.ShaCompress) :
    ∀ (K d : ℕ) (k : BitVec 256), d ≤ K →
      (chainCountStep F)^[K] (k, d) = ((chainStepFn F)^[d] k, 0)
  | 0, d, k, hd => by
    have : d = 0 := by omega
    subst this; rfl
  | K + 1, 0, k, _ => by
    rw [Function.iterate_succ_apply]
    have h0 : chainCountStep F (k, 0) = (k, 0) := by simp [chainCountStep]
    rw [h0]
    exact chainCountStep_iterate F K 0 k (Nat.zero_le _)
  | K + 1, d + 1, k, hd => by
    rw [Function.iterate_succ_apply]
    have h1 : chainCountStep F (k, d + 1) = (chainStepFn F k, d) := by simp [chainCountStep]
    rw [h1, chainCountStep_iterate F K d (chainStepFn F k) (by omega),
      Function.iterate_succ_apply]

theorem iterM_pure_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (g : α → α) :
    ∀ (n : ℕ) (a : α), iterM (m := m) (fun x => pure (g x)) n a = pure (g^[n] a)
  | 0, _ => rfl
  | n + 1, a => by
    simp only [iterM, pure_bind, Function.iterate_succ_apply]
    exact iterM_pure_eq g n (g a)

end ChainIter

section ChainSeedAtomic

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem hb0 : bits 0 = 1 := bits_zero
private theorem hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)

def hmacOneE (b : BitVec 8) {Γ : List (Ty ASig)} (k : Expr AOps Γ BV256) : Expr AOps Γ BV256 :=
  sOpSym (.hmacSha256Op 1) (.pair k (sOpPure (.bytesLit 1 [b]) .unit))

@[simp] theorem eval_hmacOneE (b : BitVec 8) {Γ : List (Ty ASig)} (k : Expr AOps Γ BV256)
    (ρ : Env Γ) :
    (hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) b k).eval ρ = bytesToKey32 (chainHmac C.F (k.eval ρ) b) := rfl

theorem cost_hmacOneE (b : BitVec 8) {Γ : List (Ty ASig)} (k : Expr AOps Γ BV256) :
    (hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) b k).cost ≤ k.cost + 14 := by
  have h1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  simp only [hmacOneE, cost_sOpSym, cost_sOpPure, AtomicSymOp.cost, AtomicPureOp.cost,
    Expr.cost, h1, List.length_singleton]
  omega

theorem descBits_hmacOneE (b : BitVec 8) {Γ : List (Ty ASig)} (k : Expr AOps Γ BV256) :
    atomicExprDescBits atomicSessionOpDescBits
      (hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
        (lam := lam) b k) ≤ atomicExprDescBits atomicSessionOpDescBits k + 80 := by
  have h1 : ((1 : ℕ+) : ℕ) = 1 := rfl
  simp only [hmacOneE, descBits_sOpSym, descBits_sOpPure, atomicSymOpDescBits,
    atomicPureOpDescBits, atomicExprDescBits, h1, List.length_singleton, hb1]
  omega

def chainCountStepE {Γ : List (Ty ASig)} :
    Expr AOps (.prod BV256 .nat :: Γ) (.prod BV256 .nat) :=
  .ite (.eqN (.snd .v0) (.nat 0)) .v0
    (.pair (hmacOneE chainKeySeed (.fst .v0)) (.sub (.snd .v0) (.nat 1)))

theorem eval_chainCountStepE {Γ : List (Ty ASig)} (x : BitVec 256 × ℕ) (ρ : Env Γ) :
    (chainCountStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) (Γ := Γ)).eval (.cons x ρ) = chainCountStep C.F x := by
  rcases x with ⟨k, d⟩
  by_cases hd : d = 0
  · subst hd; simp [chainCountStepE, chainCountStep, Expr.eval, Expr.v0]
  · simp [chainCountStepE, chainCountStep, chainStepFn, Expr.eval, Expr.v0, hd]

/-- Derives the message-key seed after `d ≤ Kc` counter-guarded chain steps followed by one HMAC. -/
def chainSeedIterC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (Kc : ℕ)
    {Γ : List (Ty ASig)} (kd : Expr AOps Γ (.prod BV256 .nat)) : Comp AOps I' Γ BV256 :=
  .bind (.iter Kc kd (.ret chainCountStepE))
    (.ret (hmacOneE messageKeySeed (.fst .v0)))

theorem eval_chainSeedIterC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (Kc : ℕ)
    {Γ : List (Ty ASig)} (kd : Expr AOps Γ (.prod BV256 .nat)) (ρ : Env Γ)
    (k : BitVec 256) (d : ℕ) (hkd : kd.eval ρ = (k, d)) (hd : d ≤ Kc) :
    (chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) I' Kc kd).eval ρ =
      pure (bytesToKey32 (chainHmac C.F (chainKeyAfter C.F d k) messageKeySeed)) := by
  simp only [chainSeedIterC, Comp.eval]
  have hfun : (fun a => (pure ((chainCountStepE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).eval (.cons a ρ)) :
        OracleComp T (BitVec 256 × ℕ))) = fun a => pure (chainCountStep C.F a) := by
    funext a; rw [eval_chainCountStepE]
  rw [hfun, iterM_pure_eq, hkd, chainCountStep_iterate C.F Kc d k hd, pure_bind,
    chainKeyAfter_eq_iterate]
  rfl

theorem queries_chainSeedIterC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (Kc : ℕ)
    {Γ : List (Ty ASig)} (kd : Expr AOps Γ (.prod BV256 .nat))
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) :
    (chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) I' Kc kd).queries w ws = 0 := by
  simp [chainSeedIterC, Comp.queries]

theorem cost_chainSeedIterC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (Kc : ℕ)
    {Γ : List (Ty ASig)} (kd : Expr AOps Γ (.prod BV256 .nat)) :
    (chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) I' Kc kd).cost ≤ kd.cost + 30 * Kc + 30 := by
  have h1 := cost_hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) chainKeySeed (.fst .v0)
  have h2 := cost_hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) messageKeySeed (.fst .v0)
  unfold chainSeedIterC chainCountStepE
  generalize hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) chainKeySeed (.fst .v0) = eh1 at h1 ⊢
  generalize hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) messageKeySeed (.fst .v0) = eh2 at h2 ⊢
  simp only [Comp.cost, Expr.cost, Expr.v0, hb0, hb1] at h1 h2 ⊢
  have hmul : Kc * (eh1.cost + 4 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) ≤ 30 * Kc := by
    rw [Nat.mul_comm 30 Kc]; exact Nat.mul_le_mul_left Kc (by omega)
  have hstep : Kc * (1 + 1 + 1 + 1 + max 1 (eh1.cost + (1 + 1 + 1 + 1) + 1) + 1 + 1 + 1) ≤
      30 * Kc := by
    rw [Nat.mul_comm 30 Kc]; exact Nat.mul_le_mul_left Kc (by omega)
  omega

private theorem cost_chainSeedIterC_tight {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (Kc : ℕ)
    {Γ : List (Ty ASig)} (kd : Expr AOps Γ (.prod BV256 .nat)) :
    (chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
      (lam := lam) I' Kc kd).cost ≤ kd.cost + 28 * Kc + 30 := by
  have h1 := cost_hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) chainKeySeed (.fst .v0)
  have h2 := cost_hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) messageKeySeed (.fst .v0)
  unfold chainSeedIterC chainCountStepE
  generalize hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) chainKeySeed (.fst .v0) = eh1 at h1 ⊢
  generalize hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) messageKeySeed (.fst .v0) = eh2 at h2 ⊢
  simp only [Comp.cost, Expr.cost, Expr.v0, hb0, hb1] at h1 h2 ⊢
  have hstep : Kc * (1 + 1 + 1 + 1 + max 1 (eh1.cost + (1 + 1 + 1 + 1) + 1) + 1 + 1 + 1) ≤
      28 * Kc := by
    rw [Nat.mul_comm 28 Kc]; exact Nat.mul_le_mul_left Kc (by omega)
  omega

theorem descBits_chainSeedIterC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (Kc : ℕ)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty ASig)} (kd : Expr AOps Γ (.prod BV256 .nat)) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT)
        (lam := lam) I' Kc kd) ≤
      atomicExprDescBits atomicSessionOpDescBits kd + 2 * bits Kc + 400 := by
  have h1 := descBits_hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) chainKeySeed (.fst .v0)
  have h2 := descBits_hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) messageKeySeed (.fst .v0)
  unfold chainSeedIterC chainCountStepE
  generalize hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) chainKeySeed (.fst .v0) = eh1 at h1 ⊢
  generalize hmacOneE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := .prod BV256 .nat :: Γ) messageKeySeed (.fst .v0) = eh2 at h2 ⊢
  simp only [atomicCompDescBits, atomicExprDescBits,
    Expr.v0, varIdx, hb0, hb1] at h1 h2 ⊢
  omega

end ChainSeedAtomic

/-! ## Snapshot well-formedness and deferred candidates -/

section DeferredCandidatePure

/-- Structural well-formedness of a corruption snapshot (`≤ 5` receiver chains, `≤ 2000` stored keys per chain, 32-byte seeds). -/
def SnapWFProd {PQ : Type} (gh : GhostState PQ) : Prop :=
  gh.session.receiverChains.length ≤ 5 ∧
    ∀ rc ∈ gh.session.receiverChains,
      rc.messageKeys.length ≤ 2000 ∧
      ∀ mk ∈ rc.messageKeys, mk.seed.length = 32

abbrev SnapWF {PQ : Type} (gh : GhostState PQ) : Prop := SnapWFProd gh

theorem snapWFProd_toGhost {PQ PQC Pt : Type} {ℓ : ℕ} (P : Params PQ PQC)
    (s : SimState PQ Pt ℓ) (Q : Party) (st : Fig8St Pt)
    (hcs : (s.chains Q).length ≤ 5)
    (hsk : ∀ g ∈ s.chains Q, g.skipped.length ≤ 2000) :
    SnapWFProd (toGhost P s Q st) := by
  refine ⟨by simp [toGhost, hcs], ?_⟩
  intro rc hrc
  simp only [toGhost, List.mem_map] at hrc
  obtain ⟨gc, hgc, rfl⟩ := hrc
  cases st.vR gc.epoch with
  | none => simp
  | some v =>
    refine ⟨(List.length_filterMap_le _ _).trans (hsk gc hgc), ?_⟩
    intro mkg hmkg
    rw [List.mem_filterMap] at hmkg
    obtain ⟨j, _, hj⟩ := hmkg
    rcases hlk : v.skippedKeys.lookup j with _ | mk
    · simp [hlk] at hj
    · simp only [hlk, Option.map_some, Option.some.injEq] at hj
      subst hj
      simp [keyToBytes32]

theorem chainSeedAtB_eq {Lck : ℕ} {counter : BitVec 32} (h : counter.toNat ≤ Lck)
    (F : ShaCompress) (ck : ChainKey) :
    SanOracleCore.chainSeedAtB Lck F ck counter = chainSeedAt F ck counter := by
  unfold SanOracleCore.chainSeedAtB
  have hlt : ¬ (Lck < counter.toNat - ck.index.toNat) := by omega
  simp [hlt]

private theorem orElse_congr_eq {α : Type} {a₁ a₂ b₁ b₂ : Option α}
    (ha : a₁ = a₂) (hb : b₁ = b₂) : (a₁ <|> b₁) = (a₂ <|> b₂) := by
  rw [ha, hb]

private theorem findSome?_congr_mem {α β : Type} {xs : List α} {f g : α → Option β}
    (h : ∀ x ∈ xs, f x = g x) : xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.findSome?_cons, h x List.mem_cons_self]
    cases g x with
    | none => exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    | some _ => rfl

private theorem ite_congr_inst {α : Type} {p : Prop} (d₁ d₂ : Decidable p)
    {t₁ t₂ e₁ e₂ : α} (ht : t₁ = t₂) (he : e₁ = e₂) :
    @ite α p d₁ t₁ e₁ = @ite α p d₂ t₂ e₂ := by
  cases d₁ with
  | isFalse h₁ =>
    cases d₂ with
    | isFalse _ => exact he
    | isTrue h₂ => exact absurd h₂ h₁
  | isTrue h₁ =>
    cases d₂ with
    | isFalse h₂ => exact absurd h₁ h₂
    | isTrue _ => exact ht

/-- Invariant that snapshots for the same party and epoch `≥ 2` agree on the sender ratchet keypair and latest receiver-chain public key. -/
def SnapsCurEpochEq {PQ : Type} (snaps : List (Party × ℕ × GhostState PQ)) : Prop :=
  ∀ e₁ ∈ snaps, ∀ e₂ ∈ snaps,
    e₁.1 = e₂.1 → e₁.2.1 = e₂.2.1 → 2 ≤ e₁.2.1 →
    e₁.2.2.session.senderChain.map (·.ratchetKey) =
      e₂.2.2.session.senderChain.map (·.ratchetKey) ∧
    e₁.2.2.session.receiverChains.getLast?.map (·.senderRatchetKey) =
      e₂.2.2.session.receiverChains.getLast?.map (·.senderRatchetKey)

def candK4Cur {PQ : Type} (Q : Party) (t : ℕ) (Y : PublicKey)
    (e_cur : Party × ℕ × GhostState PQ) : Option (PublicKey × PrivateKey) :=
  if e_cur.1 = Q.other ∧ e_cur.2.1 = t then
    e_cur.2.2.session.senderChain.bind fun sc_cur =>
      if sc_cur.ratchetKey.publicKey = Y then
        e_cur.2.2.session.receiverChains.getLast?.map fun rc_last =>
          (rc_last.senderRatchetKey, sc_cur.ratchetKey.privateKey)
      else none
  else none

private theorem exists_of_findSome?_eq_some {α β : Type} {xs : List α} {f : α → Option β} {v : β}
    (h : xs.findSome? f = some v) : ∃ x ∈ xs, f x = some v := by
  induction xs with
  | nil => cases h
  | cons x tl ih =>
    simp only [List.findSome?_cons] at h
    cases hfx : f x with
    | some w =>
      rw [hfx, Option.some.injEq] at h
      exact ⟨x, List.mem_cons_self, by rw [hfx, h]⟩
    | none =>
      rw [hfx] at h
      obtain ⟨y, hy, hfy⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

private theorem findSome?_const_none {α β : Type} (xs : List α) :
    xs.findSome? (fun _ => (none : Option β)) = none := by
  induction xs with
  | nil => rfl
  | cons _ tl ih => exact ih

private theorem findSome?_bind_eq_of_subsingleton {α β γ : Type}
    (xs : List α) (f : α → Option β) (g : β → Option γ)
    (huniq : ∀ x₁ ∈ xs, ∀ x₂ ∈ xs, ∀ b₁ b₂,
      f x₁ = some b₁ → f x₂ = some b₂ → b₁ = b₂) :
    xs.findSome? (fun x => (f x).bind g) = (xs.findSome? f).bind g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    have ih' := ih (fun x₁ hx₁ x₂ hx₂ =>
      huniq x₁ (List.mem_cons_of_mem _ hx₁) x₂ (List.mem_cons_of_mem _ hx₂))
    simp only [List.findSome?_cons]
    cases hfx : f x with
    | none => exact ih'
    | some b =>
      change (match g b with
        | some v => some v
        | none => tl.findSome? (fun x => (f x).bind g)) = g b
      cases hgb : g b with
      | some _ => rfl
      | none =>
        dsimp only
        rw [ih']
        cases htl : tl.findSome? f with
        | none => rfl
        | some b' =>
          obtain ⟨y, hy, hfy⟩ := exists_of_findSome?_eq_some htl
          have hbb : b = b' :=
            huniq x List.mem_cons_self y (List.mem_cons_of_mem _ hy) b b' hfx hfy
          dsimp only [Option.bind]
          rw [← hbb, hgb]

private theorem candK4Cur_subsingleton_of_snapsCurEpochEq {PQ : Type}
    {snaps : List (Party × ℕ × GhostState PQ)} (hK4 : SnapsCurEpochEq snaps)
    (Q : Party) {t : ℕ} (ht : 2 ≤ t) (Y : PublicKey)
    {e₁ e₂ : Party × ℕ × GhostState PQ} (he₁ : e₁ ∈ snaps) (he₂ : e₂ ∈ snaps)
    {p₁ p₂ : PublicKey × PrivateKey}
    (h₁ : candK4Cur Q t Y e₁ = some p₁) (h₂ : candK4Cur Q t Y e₂ = some p₂) :
    p₁ = p₂ := by
  unfold candK4Cur at h₁ h₂
  split_ifs at h₁ h₂ with hc₁ hc₂
  have ⟨hsc_eq, hrc_eq⟩ := hK4 e₁ he₁ e₂ he₂ (hc₁.1.trans hc₂.1.symm)
    (hc₁.2.trans hc₂.2.symm) (hc₁.2.symm ▸ ht)
  rcases hsc₁ : e₁.2.2.session.senderChain with _ | sc₁ <;> rw [hsc₁] at h₁ hsc_eq
  · cases h₁
  · rcases hsc₂ : e₂.2.2.session.senderChain with _ | sc₂ <;> rw [hsc₂] at h₂ hsc_eq
    · cases h₂
    · dsimp only [Option.bind, Option.map] at h₁ h₂ hsc_eq
      injection hsc_eq with hrk_eq
      split_ifs at h₁ h₂ with hpk₁ hpk₂
      rcases hrc₁ : e₁.2.2.session.receiverChains.getLast? with _ | rc₁ <;>
        rw [hrc₁] at h₁ hrc_eq
      · cases h₁
      · rcases hrc₂ : e₂.2.2.session.receiverChains.getLast? with _ | rc₂ <;>
          rw [hrc₂] at h₂ hrc_eq
        · cases h₂
        · dsimp only [Option.map] at h₁ h₂ hrc_eq
          injection hrc_eq with hsrk_eq
          injection h₁ with hp₁
          injection h₂ with hp₂
          rw [← hp₁, ← hp₂, hsrk_eq, hrk_eq]

theorem snapshotMessageKeySeedB_eq {PQ PQC : Type} (Lck : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : List (BitVec 8))
    (hK4 : SnapsCurEpochEq snaps)
    (h : ∀ msg, SignalMessage.tryFrom P.codec w = .ok msg → msg.counter.toNat ≤ Lck) :
    SanOracleCore.snapshotMessageKeySeedB Lck P snaps Q t w =
      snapshotMessageKeySeed P snaps Q t w := by
  let _ := hK4
  unfold SanOracleCore.snapshotMessageKeySeedB snapshotMessageKeySeed
  rcases hm : SignalMessage.tryFrom P.codec w with _ | msg
  · rfl
  · simp only [chainSeedAtB_eq (h msg hm)]
    refine orElse_congr_eq ?_ (orElse_congr_eq ?_ (orElse_congr_eq ?_ ?_))
    · exact congrArg (snaps.findSome? ·) (funext fun _ => ite_congr_inst _ _ rfl rfl)
    · exact congrArg (snaps.findSome? ·) (funext fun e =>
        ite_congr_inst _ _ (congrArg (e.2.2.session.senderChain.bind ·)
          (funext fun _ => ite_congr_inst _ _ rfl rfl)) rfl)
    · exact congrArg (snaps.findSome? ·) (funext fun _ => ite_congr_inst _ _ rfl rfl)
    · exact congrArg₂ Option.bind
        (congrArg (snaps.findSome? ·) (funext fun e_cur =>
          ite_congr_inst _ _ (congrArg (e_cur.2.2.session.senderChain.bind ·)
            (funext fun _ => ite_congr_inst _ _ rfl rfl)) rfl))
        (funext fun _ => congrArg (snaps.findSome? ·)
          (funext fun _ => ite_congr_inst _ _ rfl rfl))

/-- Deferred message-key candidate: either a stored 32-byte seed or a chain key with step count. -/
abbrev CandVal := BitVec 256 ⊕ (BitVec 256 × ℕ)

def ckCand (Lck : ℕ) (ck : ChainKey) (n : BitVec 32) : Option CandVal :=
  if n.toNat < ck.index.toNat then none
  else if Lck < n.toNat - ck.index.toNat then none
  else some (.inr (ck.key, n.toNat - ck.index.toNat))

def candEval (F : ShaCompress) : CandVal → Bytes
  | .inl sd => keyToBytes32 sd
  | .inr (ckKey, steps) => chainHmac F (chainKeyAfter F steps ckKey) messageKeySeed

theorem ckCand_map_candEval (Lck : ℕ) (F : ShaCompress) (ck : ChainKey) (n : BitVec 32) :
    (ckCand Lck ck n).map (candEval F) = SanOracleCore.chainSeedAtB Lck F ck n := by
  unfold ckCand SanOracleCore.chainSeedAtB chainSeedAt
  by_cases h1 : n.toNat < ck.index.toNat
  · have h2 : n.toNat - ck.index.toNat = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h1)
    simp [h1, h2]
  · by_cases h2 : Lck < n.toNat - ck.index.toNat <;> simp [h1, h2, candEval]

theorem ckCand_steps_le {Lck : ℕ} {ck : ChainKey} {n : BitVec 32} {k : BitVec 256} {steps : ℕ}
    (h : ckCand Lck ck n = some (.inr (k, steps))) : steps ≤ Lck := by
  unfold ckCand at h
  split_ifs at h with h1 h2
  simp only [Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq] at h
  omega

theorem candEval_length_32 (F : ShaCompress) (c : CandVal) : (candEval F c).length = 32 := by
  rcases c with sd | ⟨ckKey, steps⟩
  · simp [candEval, keyToBytes32]
  · exact hmacWith_length F (keyToBytes32 (chainKeyAfter F steps ckKey)) [messageKeySeed]

def candK1Entry {PQ : Type} (Lck : ℕ) (Q : Party) (Y : PublicKey) (n : BitVec 32)
    (e : Party × ℕ × GhostState PQ) : Option CandVal :=
  if e.1 = Q then
    (e.2.2.session.receiverChains.find? (·.senderRatchetKey == Y)).bind fun rc =>
      match rc.messageKeys.find? (·.counter == n) with
      | some mkg => some (.inl (bytesToKey32 mkg.seed))
      | none => rc.chainKey.bind fun ck => ckCand Lck ck n
  else none

def candK3Entry {PQ : Type} (Lck : ℕ) (Q : Party) (Y : PublicKey) (n : BitVec 32)
    (e : Party × ℕ × GhostState PQ) : Option CandVal :=
  if e.1 = Q.other then
    e.2.2.session.senderChain.bind fun sc =>
      if sc.ratchetKey.publicKey = Y then ckCand Lck sc.chainKey n else none
  else none

def candK2Entry {PQ : Type} (Lck : ℕ) (C : Crypto) (Q : Party) (t : ℕ) (Y : PublicKey)
    (n : BitVec 32) (e : Party × ℕ × GhostState PQ) : Option CandVal :=
  if e.1 = Q ∧ Q.sendsIn e.2.1 = true ∧ t = e.2.1 + 1 then
    e.2.2.session.senderChain.bind fun sc =>
      match rootCreateChain C e.2.2.session.rootKey Y sc.ratchetKey.privateKey with
      | .ok (_, ck) => ckCand Lck ck n
      | .error _ => none
  else none

def candK4Inner {PQ : Type} (Lck : ℕ) (C : Crypto) (Q : Party) (t : ℕ)
    (rcSrk : PublicKey) (scCurPriv : PrivateKey) (n : BitVec 32)
    (e_prev : Party × ℕ × GhostState PQ) : Option CandVal :=
  if e_prev.1 = Q.other ∧ Q.other.sendsIn e_prev.2.1 = true ∧ t = e_prev.2.1 + 2 then
    e_prev.2.2.session.senderChain.bind fun sc_prev =>
      match rootCreateChain C e_prev.2.2.session.rootKey rcSrk sc_prev.ratchetKey.privateKey with
      | .ok (rk1, _) =>
        match rootCreateChain C rk1 rcSrk scCurPriv with
        | .ok (_, ck0) => ckCand Lck ck0 n
        | .error _ => none
      | .error _ => none
  else none

def candK4Entry {PQ : Type} (Lck : ℕ) (C : Crypto) (snaps : List (Party × ℕ × GhostState PQ))
    (Q : Party) (t : ℕ) (Y : PublicKey) (n : BitVec 32)
    (e_cur : Party × ℕ × GhostState PQ) : Option CandVal :=
  if e_cur.1 = Q.other ∧ e_cur.2.1 = t then
    e_cur.2.2.session.senderChain.bind fun sc_cur =>
      if sc_cur.ratchetKey.publicKey = Y then
        e_cur.2.2.session.receiverChains.getLast?.bind fun rc_last =>
          snaps.findSome? (candK4Inner Lck C Q t rc_last.senderRatchetKey
            sc_cur.ratchetKey.privateKey n)
      else none
  else none

def snapCandPure {PQ PQC : Type} (Lck : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : Bytes) :
    Option CandVal :=
  match SignalMessage.tryFrom P.codec w with
  | .error _ => none
  | .ok msg =>
    let Y := msg.senderRatchetKey
    let n := msg.counter
    snaps.findSome? (candK1Entry Lck Q Y n) <|>
      snaps.findSome? (candK3Entry Lck Q Y n) <|>
      snaps.findSome? (candK2Entry Lck P.C Q t Y n) <|>
      snaps.findSome? (candK4Entry Lck P.C snaps Q t Y n)

private theorem option_map_orElse {α β : Type} (f : α → β) (x y : Option α) :
    (x <|> y).map f = (x.map f <|> y.map f) := by
  cases x <;> rfl

private theorem findSome?_map_comm {α β γ : Type} (xs : List α) (g : α → Option β) (h : β → γ) :
    (xs.findSome? g).map h = xs.findSome? (fun x => (g x).map h) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.findSome?_cons]
    cases g x with
    | none => exact ih
    | some v => rfl

private theorem orElse_eq_some_cases {α : Type} {a b : Option α} {v : α}
    (h : (a <|> b) = some v) : a = some v ∨ b = some v := by
  cases a with
  | some _ => left; exact h
  | none => right; exact h

private theorem orElse_assoc_local {α : Type} (a b c : Option α) :
    ((a <|> b) <|> c) = (a <|> (b <|> c)) := by
  cases a <;> rfl

def snapshotMessageKeySeedBFast {PQ PQC : Type} (K : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ))
    (Q : Party) (t : ℕ) (w : List (BitVec 8)) : Option (List (BitVec 8)) :=
  match SignalMessage.tryFrom P.codec w with
  | .error _ => none
  | .ok msg =>
    let Y := msg.senderRatchetKey
    let n := msg.counter
    let k1 := snaps.findSome? fun e =>
      if e.1 = Q then
        (e.2.2.session.receiverChains.find? (·.senderRatchetKey == Y)).bind fun rc =>
          match rc.messageKeys.find? (·.counter == n) with
          | some mkg => some mkg.seed
          | none => rc.chainKey.bind fun ck => SanOracleCore.chainSeedAtB K P.C.F ck n
      else none
    let k3 := snaps.findSome? fun e =>
      if e.1 = Q.other then
        e.2.2.session.senderChain.bind fun sc =>
          if sc.ratchetKey.publicKey = Y then SanOracleCore.chainSeedAtB K P.C.F sc.chainKey n else none
      else none
    let k2 := snaps.findSome? fun e =>
      if e.1 = Q ∧ Q.sendsIn e.2.1 = true ∧ t = e.2.1 + 1 then
        e.2.2.session.senderChain.bind fun sc =>
          match rootCreateChain P.C e.2.2.session.rootKey Y sc.ratchetKey.privateKey with
          | .ok (_, ck) => SanOracleCore.chainSeedAtB K P.C.F ck n
          | .error _ => none
      else none
    let k4 := (snaps.findSome? (candK4Cur Q t Y)).bind fun p =>
      snaps.findSome? fun e_prev =>
        if e_prev.1 = Q.other ∧ Q.other.sendsIn e_prev.2.1 = true ∧
            t = e_prev.2.1 + 2 then
          e_prev.2.2.session.senderChain.bind fun sc_prev =>
            match rootCreateChain P.C e_prev.2.2.session.rootKey
                p.1 sc_prev.ratchetKey.privateKey with
            | .ok (rk1, _) =>
              match rootCreateChain P.C rk1 p.1 p.2 with
              | .ok (_, ck0) => SanOracleCore.chainSeedAtB K P.C.F ck0 n
              | .error _ => none
            | .error _ => none
        else none
    k1 <|> k3 <|> k2 <|> k4

def snapCandFastPure {PQ PQC : Type} (Lck : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : Bytes) :
    Option CandVal :=
  match SignalMessage.tryFrom P.codec w with
  | .error _ => none
  | .ok msg =>
    let Y := msg.senderRatchetKey
    let n := msg.counter
    snaps.findSome? (candK1Entry Lck Q Y n) <|>
      snaps.findSome? (candK3Entry Lck Q Y n) <|>
      snaps.findSome? (candK2Entry Lck P.C Q t Y n) <|>
      ((snaps.findSome? (candK4Cur Q t Y)).bind fun p =>
        snaps.findSome? (candK4Inner Lck P.C Q t p.1 p.2 n))

private theorem candK4Entry_eq_candK4Cur_bind {PQ : Type} (Lck : ℕ) (C : Crypto)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (Y : PublicKey)
    (n : BitVec 32) (e_cur : Party × ℕ × GhostState PQ) :
    candK4Entry Lck C snaps Q t Y n e_cur =
      (candK4Cur Q t Y e_cur).bind fun p =>
        snaps.findSome? (candK4Inner Lck C Q t p.1 p.2 n) := by
  unfold candK4Entry candK4Cur
  split_ifs with hq
  · rcases e_cur.2.2.session.senderChain with _ | sc_cur
    · rfl
    · dsimp only [Option.bind]
      split_ifs with hpk
      · rcases e_cur.2.2.session.receiverChains.getLast? with _ | rc_last <;> rfl
      · rfl
  · rfl

theorem snapCandFastPure_eq_snapCandPure {PQ PQC : Type} (Lck : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : Bytes)
    (hK4 : SnapsCurEpochEq snaps) :
    snapCandFastPure Lck P snaps Q t w = snapCandPure Lck P snaps Q t w := by
  unfold snapCandFastPure snapCandPure
  rcases SignalMessage.tryFrom P.codec w with _ | msg
  · rfl
  · dsimp only
    refine orElse_congr_eq rfl (orElse_congr_eq rfl (orElse_congr_eq rfl ?_))
    have hfun : (candK4Entry Lck P.C snaps Q t msg.senderRatchetKey msg.counter) =
        fun e_cur => (candK4Cur Q t msg.senderRatchetKey e_cur).bind fun p =>
          snaps.findSome? (candK4Inner Lck P.C Q t p.1 p.2 msg.counter) :=
      funext (candK4Entry_eq_candK4Cur_bind Lck P.C snaps Q t msg.senderRatchetKey msg.counter)
    rw [hfun]
    by_cases ht : 2 ≤ t
    · exact (findSome?_bind_eq_of_subsingleton snaps (candK4Cur Q t msg.senderRatchetKey) _
        (fun e₁ he₁ e₂ he₂ _ _ h₁ h₂ =>
          candK4Cur_subsingleton_of_snapsCurEpochEq hK4 Q ht msg.senderRatchetKey he₁ he₂ h₁ h₂)).symm
    · have hinner_none : ∀ p : PublicKey × PrivateKey,
          snaps.findSome? (candK4Inner Lck P.C Q t p.1 p.2 msg.counter) = none := by
        intro p
        have hc : candK4Inner (PQ := PQ) Lck P.C Q t p.1 p.2 msg.counter = fun _ => none := by
          funext e_prev
          unfold candK4Inner
          by_cases hp : e_prev.1 = Q.other ∧ Q.other.sendsIn e_prev.2.1 = true ∧ t = e_prev.2.1 + 2
          · omega
          · simp [hp]
        rw [hc, findSome?_const_none]
      have hbind_none : ∀ opt : Option (PublicKey × PrivateKey),
          (opt.bind fun p => snaps.findSome? (candK4Inner Lck P.C Q t p.1 p.2 msg.counter)) = none := by
        intro opt
        cases opt with
        | none => rfl
        | some p => exact hinner_none p
      rw [hbind_none]
      have hfn_none : (fun (e_cur : Party × ℕ × GhostState PQ) =>
          (candK4Cur Q t msg.senderRatchetKey e_cur).bind fun p =>
            snaps.findSome? (candK4Inner Lck P.C Q t p.1 p.2 msg.counter)) = fun _ => none :=
        funext fun _ => hbind_none _
      rw [hfn_none, findSome?_const_none]

theorem snapshotMessageKeySeedBFast_eq_snapshotMessageKeySeedB {PQ PQC : Type}
    (K : ℕ) (P : Params PQ PQC) (snaps : List (Party × ℕ × GhostState PQ))
    (Q : Party) (t : ℕ) (w : List (BitVec 8)) :
    snapshotMessageKeySeedBFast K P snaps Q t w =
      SanOracleCore.snapshotMessageKeySeedB K P snaps Q t w := by
  unfold snapshotMessageKeySeedBFast SanOracleCore.snapshotMessageKeySeedB candK4Cur
  rfl

theorem snapCandFastPure_map_candEval_eq_fast {PQ PQC : Type} (Lck : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : Bytes)
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) :
    (snapCandFastPure Lck P snaps Q t w).map (candEval P.C.F) =
      snapshotMessageKeySeedBFast Lck P snaps Q t w := by
  unfold snapCandFastPure snapshotMessageKeySeedBFast
  rcases SignalMessage.tryFrom P.codec w with _ | msg
  · rfl
  · dsimp only
    rw [option_map_orElse, option_map_orElse, option_map_orElse,
      findSome?_map_comm, findSome?_map_comm, findSome?_map_comm]
    refine orElse_congr_eq ?_ (orElse_congr_eq ?_ (orElse_congr_eq ?_ ?_))
    · refine findSome?_congr_mem fun e he => ?_
      unfold candK1Entry
      split_ifs with hq
      · rcases hrc : List.find? (fun x => x.senderRatchetKey == msg.senderRatchetKey)
            e.2.2.session.receiverChains with _ | rc
        · rw [hrc]; rfl
        · rw [hrc]; dsimp only [Option.bind]
          have hrc_mem := List.mem_of_find?_eq_some hrc
          rcases hmkg : List.find? (fun x => x.counter == msg.counter) rc.messageKeys with _ | mkg
          · rw [hmkg]; dsimp only
            rcases rc.chainKey with _ | ck
            · rfl
            · exact ckCand_map_candEval Lck P.C.F ck msg.counter
          · rw [hmkg]; dsimp only [Option.map, candEval]
            have hmkg_mem := List.mem_of_find?_eq_some hmkg
            have hlen := ((hWF e he).2 rc hrc_mem).2 mkg hmkg_mem
            rw [keyToBytes32_bytesToKey32 mkg.seed hlen]
      · rfl
    · refine findSome?_congr_mem fun e _ => ?_
      unfold candK3Entry
      split_ifs with hq
      · rcases e.2.2.session.senderChain with _ | sc
        · rfl
        · dsimp only [Option.bind]
          split_ifs with hpk
          · exact ckCand_map_candEval Lck P.C.F sc.chainKey msg.counter
          · rfl
      · rfl
    · refine findSome?_congr_mem fun e _ => ?_
      unfold candK2Entry
      split_ifs with hq
      · rcases e.2.2.session.senderChain with _ | sc
        · rfl
        · dsimp only [Option.bind]
          rcases rootCreateChain P.C e.2.2.session.rootKey msg.senderRatchetKey
              sc.ratchetKey.privateKey with _ | ⟨_, ck⟩
          · rfl
          · exact ckCand_map_candEval Lck P.C.F ck msg.counter
      · rfl
    · rcases snaps.findSome? (candK4Cur Q t msg.senderRatchetKey) with _ | ⟨rcSrk, scCurPriv⟩
      · rfl
      · dsimp only [Option.bind]
        rw [findSome?_map_comm]
        refine findSome?_congr_mem fun e_prev _ => ?_
        unfold candK4Inner
        split_ifs with hp
        · rcases e_prev.2.2.session.senderChain with _ | sc_prev
          · rfl
          · dsimp only [Option.bind]
            rcases rootCreateChain P.C e_prev.2.2.session.rootKey rcSrk
                sc_prev.ratchetKey.privateKey with _ | ⟨rk1, _⟩
            · rfl
            · dsimp only
              rcases rootCreateChain P.C rk1 rcSrk scCurPriv with _ | ⟨_, ck0⟩
              · rfl
              · exact ckCand_map_candEval Lck P.C.F ck0 msg.counter
        · rfl

theorem snapCandFastPure_map_candEval_eq {PQ PQC : Type} (Lck : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : Bytes)
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) :
    (snapCandFastPure Lck P snaps Q t w).map (candEval P.C.F) =
      SanOracleCore.snapshotMessageKeySeedB Lck P snaps Q t w := by
  rw [snapCandFastPure_map_candEval_eq_fast Lck P snaps Q t w hWF,
    snapshotMessageKeySeedBFast_eq_snapshotMessageKeySeedB]

theorem snapCandPure_map_candEval_eq {PQ PQC : Type} (Lck : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : Bytes)
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) (hK4 : SnapsCurEpochEq snaps) :
    (snapCandPure Lck P snaps Q t w).map (candEval P.C.F) =
      SanOracleCore.snapshotMessageKeySeedB Lck P snaps Q t w := by
  rw [← snapCandFastPure_eq_snapCandPure Lck P snaps Q t w hK4]
  exact snapCandFastPure_map_candEval_eq Lck P snaps Q t w hWF

theorem snapCandPure_steps_le {PQ PQC : Type} {Lck : ℕ} {P : Params PQ PQC}
    {snaps : List (Party × ℕ × GhostState PQ)} {Q : Party} {t : ℕ} {w : Bytes}
    {ckKey : BitVec 256} {steps : ℕ}
    (h : snapCandPure Lck P snaps Q t w = some (.inr (ckKey, steps))) :
    steps ≤ Lck := by
  unfold snapCandPure at h
  rcases htry : SignalMessage.tryFrom P.codec w with _ | msg <;> rw [htry] at h
  · cases h
  · dsimp only at h
    rcases orElse_eq_some_cases h with hk1 | h324
    · obtain ⟨e, _, he⟩ := exists_of_findSome?_eq_some hk1
      unfold candK1Entry at he; split_ifs at he
      rcases hrc : List.find? (fun x => x.senderRatchetKey == msg.senderRatchetKey)
          e.2.2.session.receiverChains with _ | rc
      · rw [hrc] at he; cases he
      · rw [hrc] at he; dsimp only [Option.bind] at he
        rcases hmkg : List.find? (fun x => x.counter == msg.counter) rc.messageKeys with _ | mkg
        · rw [hmkg] at he; dsimp only at he
          rcases hck : rc.chainKey with _ | ck
          · rw [hck] at he; cases he
          · rw [hck] at he; dsimp only [Option.bind] at he
            exact ckCand_steps_le he
        · rw [hmkg] at he; cases he
    · rcases orElse_eq_some_cases h324 with hk3 | h24
      · obtain ⟨e, _, he⟩ := exists_of_findSome?_eq_some hk3
        unfold candK3Entry at he; split_ifs at he
        rcases hsc : e.2.2.session.senderChain with _ | sc
        · rw [hsc] at he; cases he
        · rw [hsc] at he; dsimp only [Option.bind] at he
          split_ifs at he
          exact ckCand_steps_le he
      · rcases orElse_eq_some_cases h24 with hk2 | hk4
        · obtain ⟨e, _, he⟩ := exists_of_findSome?_eq_some hk2
          unfold candK2Entry at he; split_ifs at he
          rcases hsc : e.2.2.session.senderChain with _ | sc
          · rw [hsc] at he; cases he
          · rw [hsc] at he; dsimp only [Option.bind] at he
            rcases hrt : rootCreateChain P.C e.2.2.session.rootKey msg.senderRatchetKey
                sc.ratchetKey.privateKey with _ | ⟨_, ck⟩ <;> rw [hrt] at he
            · cases he
            · exact ckCand_steps_le he
        · obtain ⟨e_cur, _, he⟩ := exists_of_findSome?_eq_some hk4
          unfold candK4Entry at he; split_ifs at he
          rcases hsc : e_cur.2.2.session.senderChain with _ | sc_cur
          · rw [hsc] at he; cases he
          · rw [hsc] at he; dsimp only [Option.bind] at he
            split_ifs at he
            rcases hgl : e_cur.2.2.session.receiverChains.getLast? with _ | rc_last
            · rw [hgl] at he; cases he
            · rw [hgl] at he; dsimp only [Option.bind] at he
              obtain ⟨e_prev, _, hp⟩ := exists_of_findSome?_eq_some he
              unfold candK4Inner at hp; split_ifs at hp
              rcases hscp : e_prev.2.2.session.senderChain with _ | sc_prev
              · rw [hscp] at hp; cases hp
              · rw [hscp] at hp; dsimp only [Option.bind] at hp
                rcases hr1 : rootCreateChain P.C e_prev.2.2.session.rootKey rc_last.senderRatchetKey
                    sc_prev.ratchetKey.privateKey with _ | ⟨rk1, _⟩ <;> rw [hr1] at hp
                · cases hp
                · dsimp only at hp
                  rcases hr2 : rootCreateChain P.C rk1 rc_last.senderRatchetKey
                      sc_cur.ratchetKey.privateKey with _ | ⟨_, ck0⟩ <;> rw [hr2] at hp
                  · cases hp
                  · exact ckCand_steps_le hp

theorem snapCandFastPure_steps_le {PQ PQC : Type} {Lck : ℕ} {P : Params PQ PQC}
    {snaps : List (Party × ℕ × GhostState PQ)} {Q : Party} {t : ℕ} {w : Bytes}
    {ckKey : BitVec 256} {steps : ℕ}
    (h : snapCandFastPure Lck P snaps Q t w = some (.inr (ckKey, steps))) :
    steps ≤ Lck := by
  unfold snapCandFastPure at h
  rcases htry : SignalMessage.tryFrom P.codec w with _ | msg <;> rw [htry] at h
  · cases h
  · dsimp only at h
    rcases orElse_eq_some_cases h with hk1 | h324
    · obtain ⟨e, _, he⟩ := exists_of_findSome?_eq_some hk1
      unfold candK1Entry at he; split_ifs at he
      rcases hrc : List.find? (fun x => x.senderRatchetKey == msg.senderRatchetKey)
          e.2.2.session.receiverChains with _ | rc
      · rw [hrc] at he; cases he
      · rw [hrc] at he; dsimp only [Option.bind] at he
        rcases hmkg : List.find? (fun x => x.counter == msg.counter) rc.messageKeys with _ | mkg
        · rw [hmkg] at he; dsimp only at he
          rcases hck : rc.chainKey with _ | ck
          · rw [hck] at he; cases he
          · rw [hck] at he; dsimp only [Option.bind] at he
            exact ckCand_steps_le he
        · rw [hmkg] at he; cases he
    · rcases orElse_eq_some_cases h324 with hk3 | h24
      · obtain ⟨e, _, he⟩ := exists_of_findSome?_eq_some hk3
        unfold candK3Entry at he; split_ifs at he
        rcases hsc : e.2.2.session.senderChain with _ | sc
        · rw [hsc] at he; cases he
        · rw [hsc] at he; dsimp only [Option.bind] at he
          split_ifs at he
          exact ckCand_steps_le he
      · rcases orElse_eq_some_cases h24 with hk2 | hk4
        · obtain ⟨e, _, he⟩ := exists_of_findSome?_eq_some hk2
          unfold candK2Entry at he; split_ifs at he
          rcases hsc : e.2.2.session.senderChain with _ | sc
          · rw [hsc] at he; cases he
          · rw [hsc] at he; dsimp only [Option.bind] at he
            rcases hrt : rootCreateChain P.C e.2.2.session.rootKey msg.senderRatchetKey
                sc.ratchetKey.privateKey with _ | ⟨_, ck⟩ <;> rw [hrt] at he
            · cases he
            · exact ckCand_steps_le he
        · rcases hcur : snaps.findSome? (candK4Cur Q t msg.senderRatchetKey) with
            _ | ⟨rcSrk, scCurPriv⟩ <;> rw [hcur] at hk4
          · cases hk4
          · dsimp only [Option.bind] at hk4
            obtain ⟨e_prev, _, hp⟩ := exists_of_findSome?_eq_some hk4
            unfold candK4Inner at hp; split_ifs at hp
            rcases hscp : e_prev.2.2.session.senderChain with _ | sc_prev
            · rw [hscp] at hp; cases hp
            · rw [hscp] at hp; dsimp only [Option.bind] at hp
              rcases hr1 : rootCreateChain P.C e_prev.2.2.session.rootKey rcSrk
                  sc_prev.ratchetKey.privateKey with _ | ⟨rk1, _⟩ <;> rw [hr1] at hp
              · cases hp
              · dsimp only at hp
                rcases hr2 : rootCreateChain P.C rk1 rcSrk scCurPriv with
                  _ | ⟨_, ck0⟩ <;> rw [hr2] at hp
                · cases hp
                · exact ckCand_steps_le hp

theorem snapshotMessageKeySeedBFast_length_32 {PQ PQC : Type} (Lck : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : Bytes)
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) {seed : Bytes}
    (hseed : snapshotMessageKeySeedBFast Lck P snaps Q t w = some seed) :
    seed.length = 32 := by
  rw [← snapCandFastPure_map_candEval_eq_fast Lck P snaps Q t w hWF, Option.map_eq_some_iff] at hseed
  obtain ⟨cand, _, rfl⟩ := hseed
  exact candEval_length_32 P.C.F cand

theorem snapshotMessageKeySeedB_length_32 {PQ PQC : Type} (Lck : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ)) (Q : Party) (t : ℕ) (w : Bytes)
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) {seed : Bytes}
    (hseed : SanOracleCore.snapshotMessageKeySeedB Lck P snaps Q t w = some seed) :
    seed.length = 32 := by
  rw [← snapshotMessageKeySeedBFast_eq_snapshotMessageKeySeedB] at hseed
  exact snapshotMessageKeySeedBFast_length_32 Lck P snaps Q t w hWF hseed

@[simp] theorem partyToBool_eq_partyEnc (Q : Party) : partyToBool Q = partyEnc Q := by
  cases Q <;> rfl

end DeferredCandidatePure

/-! ## Atomic deferred-candidate expressions -/

private theorem eval_eLet_eq {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)}
    {Γ : List (Ty (atomicSig ℓ Pt))} {α β : Ty (atomicSig ℓ Pt)}
    {a : Expr O' Γ α} {b : Expr O' (α :: Γ) β} {ρ : Env Γ}
    {va : α.denote} :
    a.eval ρ = va →
    (eLet a b).eval ρ = b.eval (.cons va ρ)
  | rfl => eval_eLet a b ρ

private theorem eval_ite_eq {S' : Sig} {O' : Ops S'} {Γ : List (Ty S')} {α : Ty S'}
    {c : Expr O' Γ .bool} {t f : Expr O' Γ α} {ρ : Env Γ}
    {b : Bool} :
    c.eval ρ = b →
    (Expr.ite c t f).eval ρ = if b = true then t.eval ρ else f.eval ρ
  | rfl => rfl

private theorem eval_caseOpt_eq {S' : Sig} {O' : Ops S'} {Γ : List (Ty S')} {α β : Ty S'}
    {o : Expr O' Γ (.opt α)} {n : Expr O' Γ β} {s : Expr O' (α :: Γ) β} {ρ : Env Γ}
    {v? : Option α.denote} :
    o.eval ρ = v? →
    (Expr.caseOpt o n s).eval ρ =
      match v? with
      | none => n.eval ρ
      | some v => s.eval (.cons v ρ)
  | rfl => rfl

private theorem eval_pair_local {S' : Sig} {O' : Ops S'} {Γ : List (Ty S')} {α β : Ty S'}
    (a : Expr O' Γ α) (b : Expr O' Γ β) (ρ : Env Γ) :
    (Expr.pair a b).eval ρ = (a.eval ρ, b.eval ρ) := rfl

section CandidateCombinators

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[reducible] def candT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .sum (BV256 (ℓ := ℓ) (Pt := Pt)) (.prod (BV256 (ℓ := ℓ) (Pt := Pt)) .nat)

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem atomicTyDescBits_candT : atomicTyDescBits (candT ℓ Pt) = 28 := rfl

def orElseOptE {O' : Ops ASig} {Γ : List (Ty ASig)} {α : Ty ASig}
    (x y : Expr O' Γ (.opt α)) : Expr O' Γ (.opt α) :=
  .caseOpt x y (.some .v0)

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem eval_orElseOptE {O' : Ops ASig} {Γ : List (Ty ASig)} {α : Ty ASig}
    (x y : Expr O' Γ (.opt α)) (ρ : Env Γ) :
    (orElseOptE x y).eval ρ = (x.eval ρ <|> y.eval ρ) := by
  unfold orElseOptE
  simp only [Expr.eval, Expr.v0, Env.get_cons_zero]
  cases x.eval ρ <;> rfl

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_orElseOptE {O' : Ops ASig} {Γ : List (Ty ASig)} {α : Ty ASig}
    (x y : Expr O' Γ (.opt α)) :
    (orElseOptE x y).cost ≤ x.cost + y.cost + 4 := by
  simp only [orElseOptE, Expr.cost, Expr.v0]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem descBits_orElseOptE {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)} {α : Ty ASig}
    (x y : Expr O' Γ (.opt α)) :
    atomicExprDescBits opB (orElseOptE x y) ≤
      atomicExprDescBits opB x + atomicExprDescBits opB y + 20 := by
  have hbits := small_bits_bounds
  dsimp only [orElseOptE, Expr.v0, atomicExprDescBits, varIdx]
  omega

def findSomeOptB {O' : Ops ASig} {Γ : List (Ty ASig)} {α β : Ty ASig} (L : ℕ)
    (xs : Expr O' Γ (.list α)) (f : Expr O' (α :: .opt β :: Γ) (.opt β)) :
    Expr O' Γ (.opt β) :=
  .foldrB L xs .none (.caseOpt f .v1 (.some .v0))

omit [DecidableEq Pt] [Zero Pt] in
theorem eval_findSomeOptB {O' : Ops ASig} {Γ : List (Ty ASig)} {α β : Ty ASig} {γ : Type}
    (L : ℕ) (xs : Expr O' Γ (.list α)) (f : Expr O' (α :: .opt β :: Γ) (.opt β))
    (ρ : Env Γ) (ls : List γ) (enc : γ → α.denote)
    (hxs : (xs.eval ρ).take L = ls.map enc)
    (g : γ → Option β.denote)
    (hf : ∀ a ∈ ls, ∀ acc, f.eval (.cons (enc a) (.cons acc ρ)) = g a) :
    (findSomeOptB L xs f).eval ρ = ls.findSome? g := by
  simp only [findSomeOptB, Expr.eval, hxs, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  clear hxs
  induction ls with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.map_cons, List.foldr_cons, List.findSome?_cons,
      hf a List.mem_cons_self]
    cases g a with
    | none => exact ih (fun y hy acc => hf y (List.mem_cons_of_mem _ hy) acc)
    | some _ => rfl

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_findSomeOptB {O' : Ops ASig} {Γ : List (Ty ASig)} {α β : Ty ASig} (L : ℕ)
    (xs : Expr O' Γ (.list α)) (f : Expr O' (α :: .opt β :: Γ) (.opt β)) :
    (findSomeOptB L xs f).cost ≤ xs.cost + L * (f.cost + 5) + 2 := by
  simp only [findSomeOptB, Expr.cost, Expr.v0, Expr.v1,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte]
  have hmul : L * (f.cost + (1 + 1) + 1 + 1) ≤ L * (f.cost + 5) :=
    Nat.mul_le_mul_left L (by omega)
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem descBits_findSomeOptB {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    {α β : Ty ASig} (L : ℕ) (xs : Expr O' Γ (.list α))
    (f : Expr O' (α :: .opt β :: Γ) (.opt β)) :
    atomicExprDescBits opB (findSomeOptB L xs f) ≤
      atomicExprDescBits opB xs + atomicExprDescBits opB f +
        2 * bits L + atomicTyDescBits β + 50 := by
  have hbits := small_bits_bounds
  simp only [findSomeOptB, Expr.v0, Expr.v1, atomicExprDescBits, varIdx, Nat.reduceAdd]
  omega

private theorem foldr_getLast? {α : Type} :
    ∀ (xs : List α),
      xs.foldr (fun x (acc : Option α) => match acc with | none => some x | some v => some v) none =
        xs.getLast?
  | [] => rfl
  | [_] => rfl
  | _ :: y :: tl => by
    have ih := foldr_getLast? (y :: tl)
    have hne : y :: tl ≠ [] := List.cons_ne_nil y tl
    have hs : (y :: tl).getLast? = some ((y :: tl).getLast hne) := List.getLast?_eq_some_getLast hne
    rw [List.foldr_cons, ih, hs, List.getLast?_cons_cons, hs]

def getLastOptB {O' : Ops ASig} {Γ : List (Ty ASig)} {α : Ty ASig} (K_cap : ℕ)
    (xs : Expr O' Γ (.list α)) : Expr O' Γ (.opt α) :=
  .foldrB K_cap xs .none (.caseOpt .v1 (.some .v0) (.some .v0))

omit [DecidableEq Pt] [Zero Pt] in
theorem eval_getLastOptB {O' : Ops ASig} {Γ : List (Ty ASig)} {α : Ty ASig} (K_cap : ℕ)
    (xs : Expr O' Γ (.list α)) (ρ : Env Γ) :
    (getLastOptB K_cap xs).eval ρ = ((xs.eval ρ).take K_cap).getLast? := by
  unfold getLastOptB
  simp only [Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  rw [← foldr_getLast? ((xs.eval ρ).take K_cap)]
  refine congrArg (fun f => List.foldr f none ((xs.eval ρ).take K_cap)) ?_
  funext x acc
  cases acc <;> rfl

omit [DecidableEq Pt] [Zero Pt] in
theorem cost_getLastOptB {O' : Ops ASig} {Γ : List (Ty ASig)} {α : Ty ASig} (K_cap : ℕ)
    (xs : Expr O' Γ (.list α)) :
    (getLastOptB K_cap xs).cost ≤ xs.cost + 6 * K_cap + 2 := by
  simp only [getLastOptB, Expr.cost, Expr.v0, Expr.v1,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem descBits_getLastOptB {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)} {α : Ty ASig}
    (K_cap : ℕ) (xs : Expr O' Γ (.list α)) :
    atomicExprDescBits opB (getLastOptB K_cap xs) ≤
      atomicExprDescBits opB xs + 2 * bits K_cap + atomicTyDescBits α + 60 := by
  have hbits := small_bits_bounds
  simp only [getLastOptB, Expr.v0, Expr.v1, atomicExprDescBits, varIdx, Nat.reduceAdd]
  omega

def gpRootKey {O' : Ops ASig} {Γ : List (Ty ASig)}
    (gp : Expr O' Γ (ghostPartsT (ℓ := ℓ) (Pt := Pt))) : Expr O' Γ BV256 :=
  .fst (.snd (.snd (.snd (.snd gp))))

def gpSenderChain {O' : Ops ASig} {Γ : List (Ty ASig)}
    (gp : Expr O' Γ (ghostPartsT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (.opt (drSenderChainT (ℓ := ℓ) (Pt := Pt))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd gp)))))))))

def gpRecvChains {O' : Ops ASig} {Γ : List (Ty ASig)}
    (gp : Expr O' Γ (ghostPartsT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (.list (drRecvChainT (ℓ := ℓ) (Pt := Pt))) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd gp))))))))))

private theorem privKey_roundtrip (priv : PrivateKey) :
    (⟨keyToBytesVec32 (bytesToKey32 priv.bytes.toList)⟩ : PrivateKey) = priv := by
  rcases priv with ⟨⟨bs, hbs⟩⟩
  congr 1
  apply List.Vector.eq
  exact keyToBytes32_bytesToKey32 bs hbs

private theorem rootCreateChain_index_zero (rk : BitVec 256) (their : PublicKey)
    (our : PrivateKey) {rk' : BitVec 256} {ck : ChainKey}
    (h : rootCreateChain C rk their our = .ok (rk', ck)) :
    ck = ⟨ck.key, 0⟩ := by
  unfold rootCreateChain at h
  rcases hcc : CryptoGames.Ratchet.createChain C.F C.X rk their.bytes our.bytes
      with _ | ⟨rk0, ck0⟩ <;> simp [hcc] at h
  obtain ⟨_, rfl⟩ := h
  rfl

omit [DecidableEq Pt] [Zero Pt] in
private theorem sessionRootCreateChain_eval_priv (rk : BitVec 256) (their : PublicKey)
    (priv : PrivateKey) :
    AtomicSymOp.eval ℓ Pt C .sessionRootCreateChain
      (rk, (their, bytesToKey32 priv.bytes.toList)) =
      match rootCreateChain C rk their priv with
      | .ok (rk', ck) => some (rk', ck.key)
      | .error _ => none := by
  dsimp only [AtomicSymOp.eval]
  rw [privKey_roundtrip priv]
  rcases rootCreateChain C rk their priv with _ | ⟨rk', ck⟩ <;> rfl

private theorem find?_map_local {α β : Type} (xs : List α) (f : α → β) (p : β → Bool) :
    (xs.map f).find? p = (xs.find? (fun x => p (f x))).map f := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.map_cons, List.find?_cons]
    cases p (f x) with
    | true => rfl
    | false => exact ih

private theorem getLast?_map_local {α β : Type} (xs : List α) (f : α → β) :
    (xs.map f).getLast? = xs.getLast?.map f := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    cases tl with
    | nil => rfl
    | cons y tl' =>
      simp only [List.map_cons, List.getLast?_cons_cons] at ih ⊢
      exact ih

def ckCandNatE {Γ : List (Ty ASig)} (ckKeyE : Expr AOps Γ BV256)
    (ckIdxNatE nNatE lckNatE : Expr AOps Γ .nat) : Expr AOps Γ (.opt (candT ℓ Pt)) :=
  eLet (.pair ckKeyE (.pair ckIdxNatE (.pair nNatE lckNatE)))
    (let k0 : Expr AOps _ BV256 := .fst .v0
     let idx0 : Expr AOps _ .nat := .fst (.snd .v0)
     let n0 : Expr AOps _ .nat := .fst (.snd (.snd .v0))
     let lck0 : Expr AOps _ .nat := .snd (.snd (.snd .v0))
     .ite (.lt n0 idx0) .none
       (.ite (.lt lck0 (.sub n0 idx0)) .none
         (.some (.inr (.pair k0 (.sub n0 idx0))))))

theorem eval_ckCandNatE {Γ : List (Ty ASig)} (ckKeyE : Expr AOps Γ BV256)
    (ckIdxNatE nNatE lckNatE : Expr AOps Γ .nat) (ρ : Env Γ)
    (ck : ChainKey) (n : BitVec 32) (Lck : ℕ)
    (hk : ckKeyE.eval ρ = ck.key) (hidx : ckIdxNatE.eval ρ = ck.index.toNat)
    (hn : nNatE.eval ρ = n.toNat) (hlck : lckNatE.eval ρ = Lck) :
    (ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) ckKeyE ckIdxNatE nNatE lckNatE).eval ρ =
      ckCand Lck ck n := by
  unfold ckCandNatE ckCand
  simp only [eval_eLet, Expr.eval, hk, hidx, hn, hlck, Expr.v0, Env.get_cons_zero]
  by_cases h1 : n.toNat < ck.index.toNat
  · simp [h1]
  · by_cases h2 : Lck < n.toNat - ck.index.toNat <;> simp [h1, h2]

theorem cost_ckCandNatE {Γ : List (Ty ASig)} (ckKeyE : Expr AOps Γ BV256)
    (ckIdxNatE nNatE lckNatE : Expr AOps Γ .nat) :
    (ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) ckKeyE ckIdxNatE nNatE lckNatE).cost ≤
      ckKeyE.cost + ckIdxNatE.cost + nNatE.cost + lckNatE.cost + 60 := by
  simp only [ckCandNatE, cost_eLet, Expr.cost, Expr.v0,
    Nat.max_def, Nat.reduceLeDiff, ↓reduceIte]
  omega

theorem descBits_ckCandNatE {Γ : List (Ty ASig)} (ckKeyE : Expr AOps Γ BV256)
    (ckIdxNatE nNatE lckNatE : Expr AOps Γ .nat) :
    atomicExprDescBits atomicSessionOpDescBits
      (ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) ckKeyE ckIdxNatE nNatE lckNatE) ≤
      atomicExprDescBits atomicSessionOpDescBits ckKeyE +
      atomicExprDescBits atomicSessionOpDescBits ckIdxNatE +
      atomicExprDescBits atomicSessionOpDescBits nNatE +
      atomicExprDescBits atomicSessionOpDescBits lckNatE + 450 := by
  have hbits := small_bits_bounds
  simp only [ckCandNatE, descBits_eLet, candT, BV256, Expr.v0,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd]
  omega

private theorem partyEnc_beq_eq_decide (p q : Party) :
    (partyEnc p == partyEnc q) = decide (p = q) := by
  cases p <;> cases q <;> rfl

def candK1EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (yE : Expr AOps Γ PK) (nE : Expr AOps Γ U32)
    (nNatE lckNatE : Expr AOps Γ .nat) : Expr AOps Γ (.opt (candT ℓ Pt)) :=
  eLet (.pair eE (.pair qBE (.pair yE (.pair nE (.pair nNatE lckNatE)))))
    (let e0 : Expr AOps _ (snapT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     .ite (boolEq (.fst e0) q0)
       (let rcs := gpRecvChains (sOpPure .ghostStateSplit (.snd (.snd e0)))
        .caseOpt (.findB 5 rcs (sOpPure .pkEq (.pair (.fst .v0) (.fst (.snd (.snd .v1))))))
          .none
          (.caseOpt
            (.findB 2000 (.snd (.snd .v0))
              (sOpPure .u32Eq (.pair (.snd .v0) (.fst (.snd (.snd (.snd .v2)))))))
            (.caseOpt (.fst (.snd .v0)) .none
              (ckCandNatE (.fst .v0) (sOpPure .u32ToNat (.snd .v0))
                (.fst (.snd (.snd (.snd (.snd .v2)))))
                (.snd (.snd (.snd (.snd (.snd .v2)))))))
            (.some (.inl (.fst .v0)))))
       .none)

theorem eval_candK1EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (yE : Expr AOps Γ PK) (nE : Expr AOps Γ U32)
    (nNatE lckNatE : Expr AOps Γ .nat) (ρ : Env Γ)
    (e : Party × ℕ × GhostState Bytes) (Q : Party) (Y : PublicKey) (n : BitVec 32) (Lck : ℕ)
    (he : eE.eval ρ = snapEnc e) (hq : qBE.eval ρ = partyEnc Q)
    (hy : yE.eval ρ = Y) (hn : nE.eval ρ = n)
    (hnn : nNatE.eval ρ = n.toNat) (hlck : lckNatE.eval ρ = Lck)
    (hwf : SnapWFProd e.2.2) :
    (candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) eE qBE yE nE nNatE lckNatE).eval ρ =
      candK1Entry Lck Q Y n e := by
  unfold candK1EntryE candK1Entry
  refine Eq.trans (eval_eLet_eq (va := (snapEnc e, (partyEnc Q, (Y, (n, (n.toNat, Lck)))))) ?_) ?_
  · simp only [Expr.eval, he, hq, hy, hn, hnn, hlck]
  · refine Eq.trans (eval_ite_eq (b := decide (e.1 = Q)) ?_) ?_
    · simp only [boolEq_eval, Expr.eval, Expr.v0, Env.get_cons_zero, snapEnc, partyEnc_beq_eq_decide]
    · by_cases hqe : e.1 = Q
      · simp only [hqe, decide_true, ↓reduceIte]
        refine Eq.trans (eval_caseOpt_eq (α := drRecvChainT (ℓ := ℓ) (Pt := Pt)) (v? :=
            (e.2.2.session.receiverChains.find? (·.senderRatchetKey == Y)).map
              (fun rc => (rc.senderRatchetKey,
                (rc.chainKey.map (fun ck => (ck.key, ck.index)),
                 rc.messageKeys.map (fun mk => (bytesToKey32 mk.seed, mk.counter)))))) ?_) ?_
        · simp only [Expr.eval, gpRecvChains, eval_sOpPure, AtomicPureOp.eval, ghostSplitEval,
            snapEnc, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
          rw [List.take_of_length_le (by simp [hwf.1]), find?_map_local,
            List.take_of_length_le hwf.1]
        · rcases hrc : e.2.2.session.receiverChains.find? (·.senderRatchetKey == Y) with _ | rc
          · rw [hrc]; rfl
          · rw [hrc]
            dsimp only [Option.map, Option.bind]
            have hrc_mem := List.mem_of_find?_eq_some hrc
            refine Eq.trans (eval_caseOpt_eq (α := .prod BV256 U32) (v? :=
                (rc.messageKeys.find? (·.counter == n)).map
                  (fun mk => (bytesToKey32 mk.seed, mk.counter))) ?_) ?_
            · simp only [Expr.eval, eval_sOpPure, AtomicPureOp.eval, Expr.v0, Expr.v2,
                Env.get_cons_zero, Env.get_cons_succ]
              rw [List.take_of_length_le (by simp [(hwf.2 rc hrc_mem).1]), find?_map_local]
            · rcases hmk : rc.messageKeys.find? (·.counter == n) with _ | mkg
              · rw [hmk]
                dsimp only [Option.map]
                refine Eq.trans (eval_caseOpt_eq (α := .prod BV256 U32) (v? :=
                    rc.chainKey.map (fun ck => (ck.key, ck.index))) rfl) ?_
                rcases hck : rc.chainKey with _ | ck
                · rfl
                · dsimp only [Option.map, Option.bind]
                  exact eval_ckCandNatE _ _ _ _ _ ck n Lck rfl rfl rfl rfl
              · rw [hmk]; rfl
      · simp only [hqe, decide_false, Bool.false_eq_true, ↓reduceIte]
        rfl

theorem cost_candK1EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (yE : Expr AOps Γ PK) (nE : Expr AOps Γ U32)
    (nNatE lckNatE : Expr AOps Γ .nat) :
    (candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) eE qBE yE nE nNatE lckNatE).cost ≤
      eE.cost + qBE.cost + yE.cost + nE.cost + nNatE.cost + lckNatE.cost + 20300 := by
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod PK (.prod U32 (.prod .nat .nat))))
  let Γck := Ty.prod BV256 U32 :: drRecvChainT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hck := cost_ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γck)
    (.fst .v0) (sOpPure .u32ToNat (.snd .v0))
    (.fst (.snd (.snd (.snd (.snd .v2))))) (.snd (.snd (.snd (.snd (.snd .v2)))))
  unfold candK1EntryE
  generalize ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γck) _ _ _ _ = eck at hck ⊢
  simp only [cost_eLet, gpRecvChains, boolEq, Expr.cost, cost_sOpPure, AtomicPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2] at hck ⊢
  omega

theorem descBits_candK1EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (yE : Expr AOps Γ PK) (nE : Expr AOps Γ U32)
    (nNatE lckNatE : Expr AOps Γ .nat) :
    atomicExprDescBits atomicSessionOpDescBits
      (candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) eE qBE yE nE nNatE lckNatE) ≤
      atomicExprDescBits atomicSessionOpDescBits eE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits yE +
      atomicExprDescBits atomicSessionOpDescBits nE +
      atomicExprDescBits atomicSessionOpDescBits nNatE +
      atomicExprDescBits atomicSessionOpDescBits lckNatE + 1400 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod PK (.prod U32 (.prod .nat .nat))))
  let Γck := Ty.prod BV256 U32 :: drRecvChainT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hck := descBits_ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γck)
    (.fst .v0) (sOpPure .u32ToNat (.snd .v0))
    (.fst (.snd (.snd (.snd (.snd .v2))))) (.snd (.snd (.snd (.snd (.snd .v2)))))
  unfold candK1EntryE
  generalize ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γck) _ _ _ _ = eck at hck ⊢
  simp only [descBits_eLet, descBits_sOpPure, gpRecvChains, boolEq, candT, BV256, U32,
    Expr.v0, Expr.v1, Expr.v2, atomicExprDescBits, atomicPureOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hck ⊢
  omega

def candK3EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (yE : Expr AOps Γ PK) (nNatE lckNatE : Expr AOps Γ .nat) :
    Expr AOps Γ (.opt (candT ℓ Pt)) :=
  eLet (.pair eE (.pair qOtherBE (.pair yE (.pair nNatE lckNatE))))
    (let e0 : Expr AOps _ (snapT ℓ Pt) := .fst .v0
     let qo0 : Expr AOps _ .bool := .fst (.snd .v0)
     .ite (boolEq (.fst e0) qo0)
       (.caseOpt (gpSenderChain (sOpPure .ghostStateSplit (.snd (.snd e0)))) .none
         (.ite (sOpPure .pkEq (.pair (.fst (.fst .v0)) (.fst (.snd (.snd .v1)))))
           (ckCandNatE (.fst (.snd .v0)) (sOpPure .u32ToNat (.snd (.snd .v0)))
             (.fst (.snd (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1)))))
           .none))
       .none)

theorem eval_candK3EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (yE : Expr AOps Γ PK) (nNatE lckNatE : Expr AOps Γ .nat) (ρ : Env Γ)
    (e : Party × ℕ × GhostState Bytes) (Q : Party) (Y : PublicKey) (n : BitVec 32) (Lck : ℕ)
    (he : eE.eval ρ = snapEnc e) (hqo : qOtherBE.eval ρ = partyEnc Q.other)
    (hy : yE.eval ρ = Y) (hnn : nNatE.eval ρ = n.toNat) (hlck : lckNatE.eval ρ = Lck) :
    (candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) eE qOtherBE yE nNatE lckNatE).eval ρ =
      candK3Entry Lck Q Y n e := by
  unfold candK3EntryE candK3Entry
  refine Eq.trans (eval_eLet_eq (va := (snapEnc e, (partyEnc Q.other, (Y, (n.toNat, Lck))))) ?_) ?_
  · simp only [Expr.eval, he, hqo, hy, hnn, hlck]
  · refine Eq.trans (eval_ite_eq (b := decide (e.1 = Q.other)) ?_) ?_
    · simp only [boolEq_eval, Expr.eval, Expr.v0, Env.get_cons_zero, snapEnc, partyEnc_beq_eq_decide]
    · by_cases hqe : e.1 = Q.other
      · simp only [hqe, decide_true, ↓reduceIte]
        refine Eq.trans (eval_caseOpt_eq (v? := e.2.2.session.senderChain.map
            (fun sc => ((sc.ratchetKey.publicKey, bytesToKey32 sc.ratchetKey.privateKey.bytes.toList),
              (sc.chainKey.key, sc.chainKey.index)))) rfl) ?_
        rcases e.2.2.session.senderChain with _ | sc
        · rfl
        · dsimp only [Option.map, Option.bind]
          refine Eq.trans (eval_ite_eq (b := (sc.ratchetKey.publicKey == Y)) rfl) ?_
          by_cases hpk : sc.ratchetKey.publicKey = Y
          · simp only [hpk, beq_self_eq_true, ↓reduceIte]
            exact eval_ckCandNatE _ _ _ _ _ sc.chainKey n Lck rfl rfl rfl rfl
          · have hne : (sc.ratchetKey.publicKey == Y) = false := beq_eq_false_iff_ne.mpr hpk
            simp only [hpk, hne, Bool.false_eq_true, ↓reduceIte]
            rfl
      · simp only [hqe, decide_false, Bool.false_eq_true, ↓reduceIte]
        rfl

theorem cost_candK3EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (yE : Expr AOps Γ PK) (nNatE lckNatE : Expr AOps Γ .nat) :
    (candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) eE qOtherBE yE nNatE lckNatE).cost ≤
      eE.cost + qOtherBE.cost + yE.cost + nNatE.cost + lckNatE.cost + 420 := by
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod PK (.prod .nat .nat)))
  let Γsc := drSenderChainT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hck := cost_ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γsc)
    (.fst (.snd .v0)) (sOpPure .u32ToNat (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
  unfold candK3EntryE
  generalize ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γsc) _ _ _ _ = eck at hck ⊢
  simp only [cost_eLet, gpSenderChain, boolEq, Expr.cost, cost_sOpPure, AtomicPureOp.cost,
    Expr.v0, Expr.v1] at hck ⊢
  omega

theorem descBits_candK3EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (yE : Expr AOps Γ PK) (nNatE lckNatE : Expr AOps Γ .nat) :
    atomicExprDescBits atomicSessionOpDescBits
      (candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) eE qOtherBE yE nNatE lckNatE) ≤
      atomicExprDescBits atomicSessionOpDescBits eE +
      atomicExprDescBits atomicSessionOpDescBits qOtherBE +
      atomicExprDescBits atomicSessionOpDescBits yE +
      atomicExprDescBits atomicSessionOpDescBits nNatE +
      atomicExprDescBits atomicSessionOpDescBits lckNatE + 1100 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod PK (.prod .nat .nat)))
  let Γsc := drSenderChainT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hck := descBits_ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γsc)
    (.fst (.snd .v0)) (sOpPure .u32ToNat (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v1)))) (.snd (.snd (.snd (.snd .v1))))
  unfold candK3EntryE
  generalize ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γsc) _ _ _ _ = eck at hck ⊢
  simp only [descBits_eLet, descBits_sOpPure, gpSenderChain, boolEq, candT, BV256,
    Expr.v0, Expr.v1, atomicExprDescBits, atomicPureOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hck ⊢
  omega

def candK2EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK)
    (nNatE lckNatE : Expr AOps Γ .nat) : Expr AOps Γ (.opt (candT ℓ Pt)) :=
  eLet (.pair eE (.pair qBE (.pair tE (.pair yE (.pair nNatE lckNatE)))))
    (let e0 : Expr AOps _ (snapT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let t0 : Expr AOps _ .nat := .fst (.snd (.snd .v0))
     let ep0 : Expr AOps _ .nat := .fst (.snd e0)
     .ite (.and (boolEq (.fst e0) q0) (.and (sendsInE q0 ep0) (.eqN t0 (.add ep0 (.nat 1)))))
       (eLet (sOpPure .ghostStateSplit (.snd (.snd e0)))
         (.caseOpt (gpSenderChain .v0) .none
           (.caseOpt
             (sOpSym .sessionRootCreateChain
               (.pair (gpRootKey .v1) (.pair (.fst (.snd (.snd (.snd .v2)))) (.snd (.fst .v0)))))
             .none
             (ckCandNatE (.snd .v0) (.nat 0)
               (.fst (.snd (.snd (.snd (.snd .v3)))))
               (.snd (.snd (.snd (.snd (.snd .v3)))))))))
       .none)

theorem eval_candK2EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK)
    (nNatE lckNatE : Expr AOps Γ .nat) (ρ : Env Γ)
    (e : Party × ℕ × GhostState Bytes) (Q : Party) (t : ℕ) (Y : PublicKey)
    (n : BitVec 32) (Lck : ℕ)
    (he : eE.eval ρ = snapEnc e) (hq : qBE.eval ρ = partyEnc Q) (ht : tE.eval ρ = t)
    (hy : yE.eval ρ = Y) (hnn : nNatE.eval ρ = n.toNat) (hlck : lckNatE.eval ρ = Lck) :
    (candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) eE qBE tE yE nNatE lckNatE).eval ρ =
      candK2Entry Lck C Q t Y n e := by
  unfold candK2EntryE candK2Entry
  refine Eq.trans (eval_eLet_eq (va := (snapEnc e, (partyEnc Q, (t, (Y, (n.toNat, Lck)))))) ?_) ?_
  · simp only [Expr.eval, he, hq, ht, hy, hnn, hlck]
  · refine Eq.trans (eval_ite_eq
        (b := (decide (e.1 = Q) && (Q.sendsIn e.2.1 && decide (t = e.2.1 + 1)))) ?_) ?_
    · dsimp only [Expr.eval]
      rw [boolEq_eval, sendsInE_eval _ _ _ Q rfl]
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero, snapEnc, partyEnc_beq_eq_decide]
    · by_cases hc : e.1 = Q ∧ Q.sendsIn e.2.1 = true ∧ t = e.2.1 + 1
      · rcases hc with ⟨hc1, hc2, hc3⟩
        simp only [hc1, hc2, hc3, decide_true, Bool.and_self, and_self, ↓reduceIte]
        rw [eval_eLet]
        refine Eq.trans (eval_caseOpt_eq (v? := e.2.2.session.senderChain.map
            (fun sc => ((sc.ratchetKey.publicKey, bytesToKey32 sc.ratchetKey.privateKey.bytes.toList),
              (sc.chainKey.key, sc.chainKey.index)))) rfl) ?_
        rcases e.2.2.session.senderChain with _ | sc
        · rfl
        · dsimp only [Option.map, Option.bind]
          refine Eq.trans (eval_caseOpt_eq
              (sessionRootCreateChain_eval_priv (Pt := Pt)
                e.2.2.session.rootKey Y sc.ratchetKey.privateKey)) ?_
          rcases hrc : rootCreateChain C e.2.2.session.rootKey Y sc.ratchetKey.privateKey
            with _ | ⟨rk', ck⟩
          · rfl
          · dsimp only
            have hck0 := rootCreateChain_index_zero (C := C) e.2.2.session.rootKey Y
              sc.ratchetKey.privateKey hrc
            have hidx0 : ck.index.toNat = 0 := by rw [hck0]; rfl
            exact eval_ckCandNatE _ _ _ _ _ ck n Lck rfl hidx0.symm rfl rfl
      · have hcond : (decide (e.1 = Q) && (Q.sendsIn e.2.1 && decide (t = e.2.1 + 1))) = false := by
          by_cases h1 : e.1 = Q
          · by_cases h2 : Q.sendsIn e.2.1 = true
            · have h3 : t ≠ e.2.1 + 1 := fun h3 => hc ⟨h1, h2, h3⟩
              simp [h1, h2, h3]
            · simp [h1, h2]
          · simp [h1]
        simp only [hc, hcond, Bool.false_eq_true, ↓reduceIte]
        rfl

theorem cost_candK2EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK)
    (nNatE lckNatE : Expr AOps Γ .nat) :
    (candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) eE qBE tE yE nNatE lckNatE).cost ≤
      eE.cost + qBE.cost + tE.cost + yE.cost + nNatE.cost + lckNatE.cost + 320 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod .nat (.prod PK (.prod .nat .nat))))
  let Γrc := Ty.prod BV256 BV256 :: drSenderChainT (ℓ := ℓ) (Pt := Pt) ::
    ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hck := cost_ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γrc)
    (.snd .v0) (.nat 0)
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.snd (.snd (.snd (.snd (.snd .v3)))))
  unfold candK2EntryE
  generalize ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γrc) _ _ _ _ = eck at hck ⊢
  simp only [cost_eLet, gpSenderChain, gpRootKey, boolEq, sendsInE,
    Expr.cost, cost_sOpPure, cost_sOpSym, AtomicPureOp.cost, AtomicSymOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, hbits.1, hbits.2.1, hbits.2.2.1] at hck ⊢
  omega

theorem descBits_candK2EntryE {Γ : List (Ty ASig)}
    (eE : Expr AOps Γ (snapT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK)
    (nNatE lckNatE : Expr AOps Γ .nat) :
    atomicExprDescBits atomicSessionOpDescBits
      (candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) eE qBE tE yE nNatE lckNatE) ≤
      atomicExprDescBits atomicSessionOpDescBits eE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits yE +
      atomicExprDescBits atomicSessionOpDescBits nNatE +
      atomicExprDescBits atomicSessionOpDescBits lckNatE + 1400 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod .nat (.prod PK (.prod .nat .nat))))
  let Γrc := Ty.prod BV256 BV256 :: drSenderChainT (ℓ := ℓ) (Pt := Pt) ::
    ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hck := descBits_ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γrc)
    (.snd .v0) (.nat 0)
    (.fst (.snd (.snd (.snd (.snd .v3))))) (.snd (.snd (.snd (.snd (.snd .v3)))))
  unfold candK2EntryE
  generalize ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γrc) _ _ _ _ = eck at hck ⊢
  simp only [descBits_eLet, descBits_sOpPure, descBits_sOpSym,
    gpSenderChain, gpRootKey, boolEq, sendsInE, candT, BV256,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    atomicExprDescBits, atomicPureOpDescBits, atomicSymOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hck ⊢
  omega

def candK4InnerE {Γ : List (Ty ASig)}
    (ePrevE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (rcSrkE : Expr AOps Γ PK) (scCurPrivE : Expr AOps Γ BV256)
    (nNatE lckNatE : Expr AOps Γ .nat) : Expr AOps Γ (.opt (candT ℓ Pt)) :=
  eLet (.pair ePrevE (.pair qOtherBE (.pair tE (.pair rcSrkE (.pair scCurPrivE (.pair nNatE lckNatE))))))
    (let e0 : Expr AOps _ (snapT ℓ Pt) := .fst .v0
     let qo0 : Expr AOps _ .bool := .fst (.snd .v0)
     let t0 : Expr AOps _ .nat := .fst (.snd (.snd .v0))
     let ep0 : Expr AOps _ .nat := .fst (.snd e0)
     .ite (.and (boolEq (.fst e0) qo0) (.and (sendsInE qo0 ep0) (.eqN t0 (.add ep0 (.nat 2)))))
       (eLet (sOpPure .ghostStateSplit (.snd (.snd e0)))
         (.caseOpt (gpSenderChain .v0) .none
           (.caseOpt
             (sOpSym .sessionRootCreateChain
               (.pair (gpRootKey .v1) (.pair (.fst (.snd (.snd (.snd .v2)))) (.snd (.fst .v0)))))
             .none
             (.caseOpt
               (sOpSym .sessionRootCreateChain
                 (.pair (.fst .v0)
                   (.pair (.fst (.snd (.snd (.snd .v3))))
                     (.fst (.snd (.snd (.snd (.snd .v3))))))))
               .none
               (ckCandNatE (.snd .v0) (.nat 0)
                 (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))
                 (.snd (.snd (.snd (.snd (.snd (.snd .v4)))))))))))
       .none)

theorem eval_candK4InnerE {Γ : List (Ty ASig)}
    (ePrevE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (rcSrkE : Expr AOps Γ PK) (scCurPrivE : Expr AOps Γ BV256)
    (nNatE lckNatE : Expr AOps Γ .nat) (ρ : Env Γ)
    (e_prev : Party × ℕ × GhostState Bytes) (Q : Party) (t : ℕ)
    (rcSrk : PublicKey) (scCurPriv : PrivateKey) (n : BitVec 32) (Lck : ℕ)
    (he : ePrevE.eval ρ = snapEnc e_prev) (hqo : qOtherBE.eval ρ = partyEnc Q.other)
    (ht : tE.eval ρ = t) (hrc : rcSrkE.eval ρ = rcSrk)
    (hpriv : scCurPrivE.eval ρ = bytesToKey32 scCurPriv.bytes.toList)
    (hnn : nNatE.eval ρ = n.toNat) (hlck : lckNatE.eval ρ = Lck) :
    (candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) ePrevE qOtherBE tE rcSrkE scCurPrivE nNatE lckNatE).eval ρ =
      candK4Inner Lck C Q t rcSrk scCurPriv n e_prev := by
  unfold candK4InnerE candK4Inner
  refine Eq.trans (eval_eLet_eq (va :=
      (snapEnc e_prev, (partyEnc Q.other, (t, (rcSrk,
        (bytesToKey32 scCurPriv.bytes.toList, (n.toNat, Lck))))))) ?_) ?_
  · simp only [Expr.eval, he, hqo, ht, hrc, hpriv, hnn, hlck]
  · refine Eq.trans (eval_ite_eq
        (b := (decide (e_prev.1 = Q.other) &&
          (Q.other.sendsIn e_prev.2.1 && decide (t = e_prev.2.1 + 2)))) ?_) ?_
    · dsimp only [Expr.eval]
      rw [boolEq_eval, sendsInE_eval _ _ _ Q.other rfl]
      simp only [Expr.eval, Expr.v0, Env.get_cons_zero, snapEnc, partyEnc_beq_eq_decide]
    · by_cases hc : e_prev.1 = Q.other ∧ Q.other.sendsIn e_prev.2.1 = true ∧ t = e_prev.2.1 + 2
      · rcases hc with ⟨hc1, hc2, hc3⟩
        simp only [hc1, hc2, hc3, decide_true, Bool.and_self, and_self, ↓reduceIte]
        rw [eval_eLet]
        refine Eq.trans (eval_caseOpt_eq (v? := e_prev.2.2.session.senderChain.map
            (fun sc => ((sc.ratchetKey.publicKey, bytesToKey32 sc.ratchetKey.privateKey.bytes.toList),
              (sc.chainKey.key, sc.chainKey.index)))) rfl) ?_
        rcases e_prev.2.2.session.senderChain with _ | sc_prev
        · rfl
        · dsimp only [Option.map, Option.bind]
          refine Eq.trans (eval_caseOpt_eq
              (sessionRootCreateChain_eval_priv (Pt := Pt)
                e_prev.2.2.session.rootKey rcSrk sc_prev.ratchetKey.privateKey)) ?_
          rcases hr1 : rootCreateChain C e_prev.2.2.session.rootKey rcSrk sc_prev.ratchetKey.privateKey
            with _ | ⟨rk1, _⟩
          · rfl
          · dsimp only
            refine Eq.trans (eval_caseOpt_eq
                (sessionRootCreateChain_eval_priv (Pt := Pt) rk1 rcSrk scCurPriv)) ?_
            rcases hr2 : rootCreateChain C rk1 rcSrk scCurPriv with _ | ⟨_, ck0⟩
            · rfl
            · dsimp only
              have hck0 := rootCreateChain_index_zero (C := C) rk1 rcSrk scCurPriv hr2
              have hidx0 : ck0.index.toNat = 0 := by rw [hck0]; rfl
              exact eval_ckCandNatE _ _ _ _ _ ck0 n Lck rfl hidx0.symm rfl rfl
      · have hcond : (decide (e_prev.1 = Q.other) &&
            (Q.other.sendsIn e_prev.2.1 && decide (t = e_prev.2.1 + 2))) = false := by
          by_cases h1 : e_prev.1 = Q.other
          · by_cases h2 : Q.other.sendsIn e_prev.2.1 = true
            · have h3 : t ≠ e_prev.2.1 + 2 := fun h3 => hc ⟨h1, h2, h3⟩
              simp [h1, h2, h3]
            · simp [h1, h2]
          · simp [h1]
        simp only [hc, hcond, Bool.false_eq_true, ↓reduceIte]
        rfl

theorem cost_candK4InnerE {Γ : List (Ty ASig)}
    (ePrevE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (rcSrkE : Expr AOps Γ PK) (scCurPrivE : Expr AOps Γ BV256)
    (nNatE lckNatE : Expr AOps Γ .nat) :
    (candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) ePrevE qOtherBE tE rcSrkE scCurPrivE nNatE lckNatE).cost ≤
      ePrevE.cost + qOtherBE.cost + tE.cost + rcSrkE.cost + scCurPrivE.cost +
      nNatE.cost + lckNatE.cost + 380 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod .nat (.prod PK (.prod BV256 (.prod .nat .nat)))))
  let Γrc2 := Ty.prod BV256 BV256 :: Ty.prod BV256 BV256 ::
    drSenderChainT (ℓ := ℓ) (Pt := Pt) :: ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hck := cost_ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γrc2)
    (.snd .v0) (.nat 0)
    (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))
  unfold candK4InnerE
  generalize ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γrc2) _ _ _ _ = eck at hck ⊢
  simp only [cost_eLet, gpSenderChain, gpRootKey, boolEq, sendsInE,
    Expr.cost, cost_sOpPure, cost_sOpSym, AtomicPureOp.cost, AtomicSymOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hbits.1, hbits.2.1, hbits.2.2.1] at hck ⊢
  omega

theorem descBits_candK4InnerE {Γ : List (Ty ASig)}
    (ePrevE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (rcSrkE : Expr AOps Γ PK) (scCurPrivE : Expr AOps Γ BV256)
    (nNatE lckNatE : Expr AOps Γ .nat) :
    atomicExprDescBits atomicSessionOpDescBits
      (candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) ePrevE qOtherBE tE rcSrkE scCurPrivE nNatE lckNatE) ≤
      atomicExprDescBits atomicSessionOpDescBits ePrevE +
      atomicExprDescBits atomicSessionOpDescBits qOtherBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits rcSrkE +
      atomicExprDescBits atomicSessionOpDescBits scCurPrivE +
      atomicExprDescBits atomicSessionOpDescBits nNatE +
      atomicExprDescBits atomicSessionOpDescBits lckNatE + 1750 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod .nat (.prod PK (.prod BV256 (.prod .nat .nat)))))
  let Γrc2 := Ty.prod BV256 BV256 :: Ty.prod BV256 BV256 ::
    drSenderChainT (ℓ := ℓ) (Pt := Pt) :: ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hck := descBits_ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γrc2)
    (.snd .v0) (.nat 0)
    (.fst (.snd (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v4))))))
  unfold candK4InnerE
  generalize ckCandNatE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γrc2) _ _ _ _ = eck at hck ⊢
  simp only [descBits_eLet, descBits_sOpPure, descBits_sOpSym,
    gpSenderChain, gpRootKey, boolEq, sendsInE, candT, BV256,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    atomicExprDescBits, atomicPureOpDescBits, atomicSymOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hck ⊢
  omega

def candK4EntryE (Ls : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (eCurE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK)
    (nNatE lckNatE : Expr AOps Γ .nat) : Expr AOps Γ (.opt (candT ℓ Pt)) :=
  eLet (.pair snapsE (.pair eCurE (.pair qOtherBE (.pair tE (.pair yE (.pair nNatE lckNatE))))))
    (let eCur0 : Expr AOps _ (snapT ℓ Pt) := .fst (.snd .v0)
     let qo0 : Expr AOps _ .bool := .fst (.snd (.snd .v0))
     let t0 : Expr AOps _ .nat := .fst (.snd (.snd (.snd .v0)))
     .ite (.and (boolEq (.fst eCur0) qo0) (.eqN (.fst (.snd eCur0)) t0))
       (eLet (sOpPure .ghostStateSplit (.snd (.snd eCur0)))
         (.caseOpt (gpSenderChain .v0) .none
           (.ite (sOpPure .pkEq (.pair (.fst (.fst .v0)) (.fst (.snd (.snd (.snd (.snd .v2)))))))
             (.caseOpt (getLastOptB 5 (gpRecvChains .v1)) .none
               (findSomeOptB Ls (.fst .v3)
                 (candK4InnerE .v0
                   (.fst (.snd (.snd .v5)))
                   (.fst (.snd (.snd (.snd .v5))))
                   (.fst .v2)
                   (.snd (.fst .v3))
                   (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))
                   (.snd (.snd (.snd (.snd (.snd (.snd .v5)))))))))
             .none)))
       .none)

theorem eval_candK4EntryE (Ls : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (eCurE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK)
    (nNatE lckNatE : Expr AOps Γ .nat) (ρ : Env Γ)
    (snaps : List (Party × ℕ × GhostState Bytes))
    (e_cur : Party × ℕ × GhostState Bytes) (Q : Party) (t : ℕ)
    (Y : PublicKey) (n : BitVec 32) (Lck : ℕ)
    (hsnaps : snapsE.eval ρ = snaps.map snapEnc) (hlen : snaps.length ≤ Ls)
    (he : eCurE.eval ρ = snapEnc e_cur) (hqo : qOtherBE.eval ρ = partyEnc Q.other)
    (ht : tE.eval ρ = t) (hy : yE.eval ρ = Y)
    (hnn : nNatE.eval ρ = n.toNat) (hlck : lckNatE.eval ρ = Lck)
    (hwf : SnapWFProd e_cur.2.2) :
    (candK4EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) Ls snapsE eCurE qOtherBE tE yE nNatE lckNatE).eval ρ =
      candK4Entry Lck C snaps Q t Y n e_cur := by
  unfold candK4EntryE candK4Entry
  refine Eq.trans (eval_eLet_eq (va :=
      (snaps.map snapEnc, (snapEnc e_cur, (partyEnc Q.other, (t, (Y, (n.toNat, Lck))))))) ?_) ?_
  · simp only [Expr.eval, hsnaps, he, hqo, ht, hy, hnn, hlck]
  · refine Eq.trans (eval_ite_eq (b := (decide (e_cur.1 = Q.other) && decide (e_cur.2.1 = t))) ?_) ?_
    · simp only [Expr.eval, boolEq_eval, Expr.v0, Env.get_cons_zero, snapEnc, partyEnc_beq_eq_decide]
    · by_cases hc : e_cur.1 = Q.other ∧ e_cur.2.1 = t
      · rcases hc with ⟨hc1, hc2⟩
        simp only [hc1, hc2, decide_true, Bool.and_self, and_self, ↓reduceIte]
        rw [eval_eLet]
        refine Eq.trans (eval_caseOpt_eq (v? := e_cur.2.2.session.senderChain.map
            (fun sc => ((sc.ratchetKey.publicKey, bytesToKey32 sc.ratchetKey.privateKey.bytes.toList),
              (sc.chainKey.key, sc.chainKey.index)))) rfl) ?_
        rcases e_cur.2.2.session.senderChain with _ | sc_cur
        · rfl
        · dsimp only [Option.map, Option.bind]
          refine Eq.trans (eval_ite_eq (b := (sc_cur.ratchetKey.publicKey == Y)) rfl) ?_
          by_cases hpk : sc_cur.ratchetKey.publicKey = Y
          · simp only [hpk, beq_self_eq_true, ↓reduceIte]
            refine Eq.trans (eval_caseOpt_eq (α := drRecvChainT (ℓ := ℓ) (Pt := Pt)) (v? :=
                e_cur.2.2.session.receiverChains.getLast?.map
                  (fun rc => (rc.senderRatchetKey,
                    (rc.chainKey.map (fun ck => (ck.key, ck.index)),
                     rc.messageKeys.map (fun mk => (bytesToKey32 mk.seed, mk.counter)))))) ?_) ?_
            · rw [eval_getLastOptB]
              simp only [gpRecvChains, Expr.eval, eval_sOpPure, AtomicPureOp.eval, ghostSplitEval,
                snapEnc, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
              rw [List.take_of_length_le (by simp [hwf.1]), getLast?_map_local,
                List.take_of_length_le hwf.1]
            · rcases hlast : e_cur.2.2.session.receiverChains.getLast? with _ | rc_last
              · rfl
              · dsimp only [Option.map, Option.bind]
                refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun ep _ _ => ?_
                · dsimp only [Expr.eval, Expr.v3, Env.get]
                  exact List.take_of_length_le (by simpa using hlen)
                · exact eval_candK4InnerE _ _ _ _ _ _ _ _ ep Q t rc_last.senderRatchetKey
                    sc_cur.ratchetKey.privateKey n Lck rfl rfl rfl rfl rfl rfl rfl
          · have hne : (sc_cur.ratchetKey.publicKey == Y) = false := beq_eq_false_iff_ne.mpr hpk
            simp only [hpk, hne, Bool.false_eq_true, ↓reduceIte]
            rfl
      · have hcond : (decide (e_cur.1 = Q.other) && decide (e_cur.2.1 = t)) = false := by
          by_cases h1 : e_cur.1 = Q.other
          · have h2 : e_cur.2.1 ≠ t := fun h2 => hc ⟨h1, h2⟩
            simp [h1, h2]
          · simp [h1]
        simp only [hc, hcond, Bool.false_eq_true, ↓reduceIte]
        rfl

theorem cost_candK4EntryE (Ls : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (eCurE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK)
    (nNatE lckNatE : Expr AOps Γ .nat) :
    (candK4EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) Ls snapsE eCurE qOtherBE tE yE nNatE lckNatE).cost ≤
      snapsE.cost + eCurE.cost + qOtherBE.cost + tE.cost + yE.cost +
      nNatE.cost + lckNatE.cost + 420 * Ls + 320 := by
  let tB := Ty.prod (.list (snapT ℓ Pt))
    (.prod (snapT ℓ Pt) (.prod .bool (.prod .nat (.prod PK (.prod .nat .nat)))))
  let Γrc := drRecvChainT (ℓ := ℓ) (Pt := Pt) :: drSenderChainT (ℓ := ℓ) (Pt := Pt) ::
    ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  let Γin := snapT ℓ Pt :: Ty.opt (candT ℓ Pt) :: Γrc
  have hin := cost_candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γin)
    .v0 (.fst (.snd (.snd .v5))) (.fst (.snd (.snd (.snd .v5))))
    (.fst .v2) (.snd (.fst .v3))
    (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v5))))))
  have hfs := cost_findSomeOptB (O' := AOps) Ls (.fst (.v3 : Expr AOps Γrc tB))
    (candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γin)
      .v0 (.fst (.snd (.snd .v5))) (.fst (.snd (.snd (.snd .v5))))
      (.fst .v2) (.snd (.fst .v3))
      (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))
      (.snd (.snd (.snd (.snd (.snd (.snd .v5)))))))
  have hgl := cost_getLastOptB (O' := AOps) 5
    (gpRecvChains (.v1 : Expr AOps (drSenderChainT (ℓ := ℓ) (Pt := Pt) ::
      ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ) _))
  unfold candK4EntryE
  generalize findSomeOptB (O' := AOps) Ls _ _ = efs at hfs ⊢
  generalize candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γin) _ _ _ _ _ _ _ = ein at hin hfs
  generalize getLastOptB (O' := AOps) 5 _ = egl at hgl ⊢
  simp only [cost_eLet, gpSenderChain, gpRecvChains, boolEq,
    Expr.cost, cost_sOpPure, AtomicPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5] at hin hfs hgl ⊢
  have hmul : Ls * (ein.cost + 5) ≤ 420 * Ls := by
    rw [Nat.mul_comm 420 Ls]; exact Nat.mul_le_mul_left Ls (by omega)
  omega

theorem descBits_candK4EntryE (Ls : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (eCurE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK)
    (nNatE lckNatE : Expr AOps Γ .nat) :
    atomicExprDescBits atomicSessionOpDescBits
      (candK4EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) Ls snapsE eCurE qOtherBE tE yE nNatE lckNatE) ≤
      atomicExprDescBits atomicSessionOpDescBits snapsE +
      atomicExprDescBits atomicSessionOpDescBits eCurE +
      atomicExprDescBits atomicSessionOpDescBits qOtherBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits yE +
      atomicExprDescBits atomicSessionOpDescBits nNatE +
      atomicExprDescBits atomicSessionOpDescBits lckNatE +
      2 * bits Ls + 3000 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (.list (snapT ℓ Pt))
    (.prod (snapT ℓ Pt) (.prod .bool (.prod .nat (.prod PK (.prod .nat .nat)))))
  let Γrc := drRecvChainT (ℓ := ℓ) (Pt := Pt) :: drSenderChainT (ℓ := ℓ) (Pt := Pt) ::
    ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  let Γin := snapT ℓ Pt :: Ty.opt (candT ℓ Pt) :: Γrc
  have hin := descBits_candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γin)
    .v0 (.fst (.snd (.snd .v5))) (.fst (.snd (.snd (.snd .v5))))
    (.fst .v2) (.snd (.fst .v3))
    (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))
    (.snd (.snd (.snd (.snd (.snd (.snd .v5))))))
  have hfs := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v3 : Expr AOps Γrc tB))
    (candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γin)
      .v0 (.fst (.snd (.snd .v5))) (.fst (.snd (.snd (.snd .v5))))
      (.fst .v2) (.snd (.fst .v3))
      (.fst (.snd (.snd (.snd (.snd (.snd .v5))))))
      (.snd (.snd (.snd (.snd (.snd (.snd .v5)))))))
  have hgl := descBits_getLastOptB (O' := AOps) atomicSessionOpDescBits 5
    (gpRecvChains (.v1 : Expr AOps (drSenderChainT (ℓ := ℓ) (Pt := Pt) ::
      ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ) _))
  unfold candK4EntryE
  generalize findSomeOptB (O' := AOps) Ls _ _ = efs at hfs ⊢
  generalize candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γin) _ _ _ _ _ _ _ = ein at hin hfs
  generalize getLastOptB (O' := AOps) 5 _ = egl at hgl ⊢
  simp only [descBits_eLet, descBits_sOpPure, gpSenderChain, gpRecvChains, boolEq,
    candT, drRecvChainT, PK, BV256, U32,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5,
    atomicExprDescBits, atomicPureOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hin hfs hgl ⊢
  omega

def snapCandE (Ls Lck : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    Expr AOps Γ (.opt (candT ℓ Pt)) :=
  eLet (.pair snapsE (.pair qBE (.pair tE wE)))
    (.caseOpt (sOpPure .signalMsgParse (.snd (.snd (.snd .v0))))
      .none
      (let snaps0 : Expr AOps _ (.list (snapT ℓ Pt)) := .fst .v1
       let q0 : Expr AOps _ .bool := .fst (.snd .v1)
       let t0 : Expr AOps _ .nat := .fst (.snd (.snd .v1))
       let y0 : Expr AOps _ PK := .fst (.snd (.fst .v0))
       let n0 : Expr AOps _ U32 := .fst (.snd (.snd (.fst .v0)))
       eLet (.pair snaps0 (.pair q0 (.pair (otherE q0) (.pair t0 (.pair y0
           (.pair n0 (.pair (sOpPure .u32ToNat n0) (.nat Lck))))))))
         (let b : Expr AOps _ _ := .v2
          let k1E := findSomeOptB Ls (.fst .v0)
            (candK1EntryE .v0
              (.fst (.snd b))
              (.fst (.snd (.snd (.snd (.snd b)))))
              (.fst (.snd (.snd (.snd (.snd (.snd b))))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd b))))))))
          let k3E := findSomeOptB Ls (.fst .v0)
            (candK3EntryE .v0
              (.fst (.snd (.snd b)))
              (.fst (.snd (.snd (.snd (.snd b)))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd b))))))))
          let k2E := findSomeOptB Ls (.fst .v0)
            (candK2EntryE .v0
              (.fst (.snd b))
              (.fst (.snd (.snd (.snd b))))
              (.fst (.snd (.snd (.snd (.snd b)))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd b))))))))
          let k4E := findSomeOptB Ls (.fst .v0)
            (candK4EntryE Ls (.fst b) .v0
              (.fst (.snd (.snd b)))
              (.fst (.snd (.snd (.snd b))))
              (.fst (.snd (.snd (.snd (.snd b)))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd b))))))))
          orElseOptE (orElseOptE (orElseOptE k1E k3E) k2E) k4E)))

theorem eval_snapCandE (idA idB : IdentityKey) (Ls Lck : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ) (w : Bytes)
    (hsnaps : snapsE.eval ρ = snaps.map snapEnc) (hlen : snaps.length ≤ Ls)
    (hq : qBE.eval ρ = partyEnc Q) (ht : tE.eval ρ = t) (hw : wE.eval ρ = w)
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) :
    (snapCandE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) Ls Lck snapsE qBE tE wE).eval ρ =
      snapCandPure Lck (paramsV1 C K idA idB) snaps Q t w := by
  have hparse := atomicPureOps_eval_signalMsgParse_lossless ℓ Pt w
  have hcodec : (paramsV1 C K idA idB).codec = protoSignalCodec := rfl
  have hC : (paramsV1 C K idA idB).C = C := rfl
  unfold snapCandE snapCandPure
  rw [hcodec, hC]
  refine Eq.trans (eval_eLet_eq (va := (snaps.map snapEnc, (partyEnc Q, (t, w)))) ?_) ?_
  · simp only [Expr.eval, hsnaps, hq, ht, hw]
  · have hparse' :
        (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .signalMsgParse
          (Γ := Ty.prod (.list (snapT ℓ Pt)) (.prod .bool (.prod .nat (B 32))) :: Γ)
          (.snd (.snd (.snd .v0)))).eval
          (.cons (snaps.map snapEnc, (partyEnc Q, (t, w))) ρ) =
        match SignalMessage.tryFrom protoSignalCodec w with
        | .ok m => some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
            (m.ciphertext, (m.pqRatchet, m.addresses)))
        | .error _ => none := by
      rw [eval_sOpPure]
      exact hparse
    refine Eq.trans (eval_caseOpt_eq hparse') ?_
    rcases SignalMessage.tryFrom protoSignalCodec w with _ | msg
    · rfl
    · dsimp only
      refine Eq.trans (eval_eLet_eq (va :=
          (snaps.map snapEnc, (partyEnc Q, (partyEnc Q.other,
            (t, (msg.senderRatchetKey, (msg.counter, (msg.counter.toNat, Lck)))))))) ?_) ?_
      · have hqo : (!partyEnc Q) = partyEnc Q.other := (partyEnc_other Q).symm
        simp only [Expr.eval, otherE_eval, eval_sOpPure, AtomicPureOp.eval,
          Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, hqo]
      · simp only [eval_orElseOptE, orElse_assoc_local]
        have htake : (List.map (snapEnc (ℓ := ℓ) (Pt := Pt)) snaps).take Ls =
            snaps.map snapEnc :=
          List.take_of_length_le (by simpa using hlen)
        refine orElse_congr_eq ?_ (orElse_congr_eq ?_ (orElse_congr_eq ?_ ?_))
        · refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun e he _ => ?_
          · exact htake
          · exact eval_candK1EntryE _ _ _ _ _ _ _ e Q msg.senderRatchetKey msg.counter Lck
              rfl rfl rfl rfl rfl rfl (hWF e he)
        · refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun e _ _ => ?_
          · exact htake
          · exact eval_candK3EntryE _ _ _ _ _ _ e Q msg.senderRatchetKey msg.counter Lck
              rfl rfl rfl rfl rfl
        · refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun e _ _ => ?_
          · exact htake
          · exact eval_candK2EntryE _ _ _ _ _ _ _ e Q t msg.senderRatchetKey msg.counter Lck
              rfl rfl rfl rfl rfl rfl
        · refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun e he _ => ?_
          · exact htake
          · exact eval_candK4EntryE Ls _ _ _ _ _ _ _ _ snaps e Q t
              msg.senderRatchetKey msg.counter Lck
              rfl hlen rfl rfl rfl rfl rfl rfl (hWF e he)

theorem cost_snapCandE (Ls Lck : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (snapCandE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) Ls Lck snapsE qBE tE wE).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost +
        ℓ / 32 + bits Lck + 420 * (Ls * Ls) + 22000 * Ls + 1200 := by
  let tOut := Ty.prod (.list (snapT ℓ Pt)) (.prod .bool (.prod .nat (B 32)))
  let tIn := Ty.prod (.list (snapT ℓ Pt))
    (.prod .bool (.prod .bool (.prod .nat (.prod PK (.prod U32 (.prod .nat .nat))))))
  let Γin := tIn :: signalParsedT (ℓ := ℓ) (Pt := Pt) :: tOut :: Γ
  let Γf := snapT ℓ Pt :: Ty.opt (candT ℓ Pt) :: Γin
  let b : Expr AOps Γf tIn := .v2
  let eb1 := candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd (.snd b))))) (.fst (.snd (.snd (.snd (.snd (.snd b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb3 := candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb2 := candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb4 := candK4EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Ls (.fst b) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb1 := cost_candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd (.snd b))))) (.fst (.snd (.snd (.snd (.snd (.snd b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb3 := cost_candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb2 := cost_candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb4 := cost_candK4EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) Ls (.fst b) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hf1 := cost_findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb1
  have hf3 := cost_findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb3
  have hf2 := cost_findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb2
  have hf4 := cost_findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb4
  change eb1.cost ≤ _ at hb1; change eb3.cost ≤ _ at hb3
  change eb2.cost ≤ _ at hb2; change eb4.cost ≤ _ at hb4
  unfold snapCandE
  change (eLet _ (.caseOpt _ .none (eLet _ (orElseOptE (orElseOptE (orElseOptE
    (findSomeOptB Ls (.fst .v0) eb1) (findSomeOptB Ls (.fst .v0) eb3))
    (findSomeOptB Ls (.fst .v0) eb2)) (findSomeOptB Ls (.fst .v0) eb4))))).cost ≤ _
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb1 = ef1 at hf1 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb3 = ef3 at hf3 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb2 = ef2 at hf2 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb4 = ef4 at hf4 ⊢
  generalize eb1 = x1 at hb1 hf1; generalize eb3 = x3 at hb3 hf3
  generalize eb2 = x2 at hb2 hf2; generalize eb4 = x4 at hb4 hf4
  simp only [b, Expr.cost, Expr.v0, Expr.v2] at hb1 hb3 hb2 hb4 hf1 hf3 hf2 hf4
  have hm1 : Ls * (x1.cost + 5) ≤ 20400 * Ls := by
    rw [Nat.mul_comm 20400 Ls]; exact Nat.mul_le_mul_left Ls (by omega)
  have hm3 : Ls * (x3.cost + 5) ≤ 500 * Ls := by
    rw [Nat.mul_comm 500 Ls]; exact Nat.mul_le_mul_left Ls (by omega)
  have hm2 : Ls * (x2.cost + 5) ≤ 400 * Ls := by
    rw [Nat.mul_comm 400 Ls]; exact Nat.mul_le_mul_left Ls (by omega)
  have hm4 : Ls * (x4.cost + 5) ≤ 420 * (Ls * Ls) + 400 * Ls := by
    calc Ls * (x4.cost + 5) ≤ Ls * (420 * Ls + 400) := Nat.mul_le_mul_left Ls (by omega)
      _ = 420 * (Ls * Ls) + 400 * Ls := by
        rw [Nat.mul_add, Nat.mul_left_comm Ls 420 Ls, Nat.mul_comm Ls 400]
  simp only [cost_eLet, orElseOptE, otherE, Expr.cost, cost_sOpPure, AtomicPureOp.cost,
    Expr.v0, Expr.v1]
  omega

theorem descBits_snapCandE (Ls Lck : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    atomicExprDescBits atomicSessionOpDescBits
      (snapCandE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) Ls Lck snapsE qBE tE wE) ≤
      atomicExprDescBits atomicSessionOpDescBits snapsE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      10 * bits Ls + 2 * bits Lck + 10000 := by
  have hbits := small_bits_bounds
  let tOut := Ty.prod (.list (snapT ℓ Pt)) (.prod .bool (.prod .nat (B 32)))
  let tIn := Ty.prod (.list (snapT ℓ Pt))
    (.prod .bool (.prod .bool (.prod .nat (.prod PK (.prod U32 (.prod .nat .nat))))))
  let Γin := tIn :: signalParsedT (ℓ := ℓ) (Pt := Pt) :: tOut :: Γ
  let Γf := snapT ℓ Pt :: Ty.opt (candT ℓ Pt) :: Γin
  let b : Expr AOps Γf tIn := .v2
  let eb1 := candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd (.snd b))))) (.fst (.snd (.snd (.snd (.snd (.snd b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb3 := candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb2 := candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb4 := candK4EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) Ls (.fst b) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb1 := descBits_candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd (.snd b))))) (.fst (.snd (.snd (.snd (.snd (.snd b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb3 := descBits_candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb2 := descBits_candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb4 := descBits_candK4EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) Ls (.fst b) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hf1 := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v0 : Expr AOps Γin tIn)) eb1
  have hf3 := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v0 : Expr AOps Γin tIn)) eb3
  have hf2 := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v0 : Expr AOps Γin tIn)) eb2
  have hf4 := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v0 : Expr AOps Γin tIn)) eb4
  change atomicExprDescBits atomicSessionOpDescBits eb1 ≤ _ at hb1
  change atomicExprDescBits atomicSessionOpDescBits eb3 ≤ _ at hb3
  change atomicExprDescBits atomicSessionOpDescBits eb2 ≤ _ at hb2
  change atomicExprDescBits atomicSessionOpDescBits eb4 ≤ _ at hb4
  unfold snapCandE
  change atomicExprDescBits atomicSessionOpDescBits
    (eLet _ (.caseOpt _ .none (eLet _ (orElseOptE (orElseOptE (orElseOptE
      (findSomeOptB Ls (.fst .v0) eb1) (findSomeOptB Ls (.fst .v0) eb3))
      (findSomeOptB Ls (.fst .v0) eb2)) (findSomeOptB Ls (.fst .v0) eb4))))) ≤ _
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb1 = ef1 at hf1 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb3 = ef3 at hf3 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb2 = ef2 at hf2 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb4 = ef4 at hf4 ⊢
  generalize eb1 = x1 at hb1 hf1; generalize eb3 = x3 at hb3 hf3
  generalize eb2 = x2 at hb2 hf2; generalize eb4 = x4 at hb4 hf4
  simp only [b, descBits_eLet, descBits_sOpPure, orElseOptE, otherE, candT, BV256,
    Expr.v0, Expr.v1, Expr.v2, atomicExprDescBits, atomicPureOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hb1 hb3 hb2 hb4 hf1 hf3 hf2 hf4 ⊢
  omega

@[reducible] def candK4CurT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (PK (ℓ := ℓ) (Pt := Pt)) (BV256 (ℓ := ℓ) (Pt := Pt))

def candK4CurE {Γ : List (Ty ASig)}
    (eCurE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK) :
    Expr AOps Γ (.opt (candK4CurT ℓ Pt)) :=
  eLet (.pair eCurE (.pair qOtherBE (.pair tE yE)))
    (let eCur0 : Expr AOps _ (snapT ℓ Pt) := .fst .v0
     let qo0 : Expr AOps _ .bool := .fst (.snd .v0)
     let t0 : Expr AOps _ .nat := .fst (.snd (.snd .v0))
     .ite (.and (boolEq (.fst eCur0) qo0) (.eqN (.fst (.snd eCur0)) t0))
       (eLet (sOpPure .ghostStateSplit (.snd (.snd eCur0)))
         (.caseOpt (gpSenderChain .v0) .none
           (.ite (sOpPure .pkEq (.pair (.fst (.fst .v0)) (.snd (.snd (.snd .v2)))))
             (.caseOpt (getLastOptB 5 (gpRecvChains .v1)) .none
               (.some (.pair (.fst .v0) (.snd (.fst .v1)))))
             .none)))
       .none)

theorem eval_candK4CurE {Γ : List (Ty ASig)}
    (eCurE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK) (ρ : Env Γ)
    (e_cur : Party × ℕ × GhostState Bytes) (Q : Party) (t : ℕ) (Y : PublicKey)
    (he : eCurE.eval ρ = snapEnc e_cur) (hqo : qOtherBE.eval ρ = partyEnc Q.other)
    (ht : tE.eval ρ = t) (hy : yE.eval ρ = Y)
    (hwf : SnapWFProd e_cur.2.2) :
    (candK4CurE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) eCurE qOtherBE tE yE).eval ρ =
      (candK4Cur Q t Y e_cur).map (fun p => (p.1, bytesToKey32 p.2.bytes.toList)) := by
  unfold candK4CurE candK4Cur
  refine Eq.trans (eval_eLet_eq (va := (snapEnc e_cur, (partyEnc Q.other, (t, Y)))) ?_) ?_
  · simp only [Expr.eval, he, hqo, ht, hy]
  · refine Eq.trans (eval_ite_eq (b := (decide (e_cur.1 = Q.other) && decide (e_cur.2.1 = t))) ?_) ?_
    · simp only [Expr.eval, boolEq_eval, Expr.v0, Env.get_cons_zero, snapEnc, partyEnc_beq_eq_decide]
    · by_cases hc : e_cur.1 = Q.other ∧ e_cur.2.1 = t
      · rcases hc with ⟨hc1, hc2⟩
        simp only [hc1, hc2, decide_true, Bool.and_self, and_self, ↓reduceIte]
        rw [eval_eLet]
        refine Eq.trans (eval_caseOpt_eq (v? := e_cur.2.2.session.senderChain.map
            (fun sc => ((sc.ratchetKey.publicKey, bytesToKey32 sc.ratchetKey.privateKey.bytes.toList),
              (sc.chainKey.key, sc.chainKey.index)))) rfl) ?_
        rcases e_cur.2.2.session.senderChain with _ | sc_cur
        · rfl
        · dsimp only [Option.map, Option.bind]
          refine Eq.trans (eval_ite_eq (b := (sc_cur.ratchetKey.publicKey == Y)) rfl) ?_
          by_cases hpk : sc_cur.ratchetKey.publicKey = Y
          · simp only [hpk, beq_self_eq_true, ↓reduceIte]
            refine Eq.trans (eval_caseOpt_eq (α := drRecvChainT (ℓ := ℓ) (Pt := Pt)) (v? :=
                e_cur.2.2.session.receiverChains.getLast?.map
                  (fun rc => (rc.senderRatchetKey,
                    (rc.chainKey.map (fun ck => (ck.key, ck.index)),
                     rc.messageKeys.map (fun mk => (bytesToKey32 mk.seed, mk.counter)))))) ?_) ?_
            · rw [eval_getLastOptB]
              simp only [gpRecvChains, Expr.eval, eval_sOpPure, AtomicPureOp.eval, ghostSplitEval,
                snapEnc, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
              rw [List.take_of_length_le (by simp [hwf.1]), getLast?_map_local,
                List.take_of_length_le hwf.1]
            · rcases e_cur.2.2.session.receiverChains.getLast? with _ | rc_last <;> rfl
          · have hne : (sc_cur.ratchetKey.publicKey == Y) = false := beq_eq_false_iff_ne.mpr hpk
            simp only [hpk, hne, Bool.false_eq_true, ↓reduceIte]
            rfl
      · have hcond : (decide (e_cur.1 = Q.other) && decide (e_cur.2.1 = t)) = false := by
          by_cases h1 : e_cur.1 = Q.other
          · have h2 : e_cur.2.1 ≠ t := fun h2 => hc ⟨h1, h2⟩
            simp [h1, h2]
          · simp [h1]
        simp only [hc, hcond, Bool.false_eq_true, ↓reduceIte]
        rfl

theorem cost_candK4CurE {Γ : List (Ty ASig)}
    (eCurE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK) :
    (candK4CurE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) eCurE qOtherBE tE yE).cost ≤
      eCurE.cost + qOtherBE.cost + tE.cost + yE.cost + 320 := by
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod .nat PK))
  have hgl := cost_getLastOptB (O' := AOps) 5
    (gpRecvChains (.v1 : Expr AOps (drSenderChainT (ℓ := ℓ) (Pt := Pt) ::
      ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ) _))
  unfold candK4CurE
  generalize getLastOptB (O' := AOps) 5 _ = egl at hgl ⊢
  simp only [cost_eLet, gpSenderChain, gpRecvChains, boolEq,
    Expr.cost, cost_sOpPure, AtomicPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2] at hgl ⊢
  omega

theorem descBits_candK4CurE {Γ : List (Ty ASig)}
    (eCurE : Expr AOps Γ (snapT ℓ Pt)) (qOtherBE : Expr AOps Γ .bool)
    (tE : Expr AOps Γ .nat) (yE : Expr AOps Γ PK) :
    atomicExprDescBits atomicSessionOpDescBits
      (candK4CurE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) eCurE qOtherBE tE yE) ≤
      atomicExprDescBits atomicSessionOpDescBits eCurE +
      atomicExprDescBits atomicSessionOpDescBits qOtherBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits yE + 1300 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (snapT ℓ Pt) (.prod .bool (.prod .nat PK))
  have hgl := descBits_getLastOptB (O' := AOps) atomicSessionOpDescBits 5
    (gpRecvChains (.v1 : Expr AOps (drSenderChainT (ℓ := ℓ) (Pt := Pt) ::
      ghostPartsT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ) _))
  unfold candK4CurE
  generalize getLastOptB (O' := AOps) 5 _ = egl at hgl ⊢
  simp only [descBits_eLet, descBits_sOpPure, gpSenderChain, gpRecvChains, boolEq,
    candK4CurT, drRecvChainT, PK, BV256, U32,
    Expr.v0, Expr.v1, Expr.v2,
    atomicExprDescBits, atomicPureOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hgl ⊢
  omega

def snapCandFastE (Ls Lck : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    Expr AOps Γ (.opt (candT ℓ Pt)) :=
  eLet (.pair snapsE (.pair qBE (.pair tE wE)))
    (.caseOpt (sOpPure .signalMsgParse (.snd (.snd (.snd .v0))))
      .none
      (let snaps0 : Expr AOps _ (.list (snapT ℓ Pt)) := .fst .v1
       let q0 : Expr AOps _ .bool := .fst (.snd .v1)
       let t0 : Expr AOps _ .nat := .fst (.snd (.snd .v1))
       let y0 : Expr AOps _ PK := .fst (.snd (.fst .v0))
       let n0 : Expr AOps _ U32 := .fst (.snd (.snd (.fst .v0)))
       eLet (.pair snaps0 (.pair q0 (.pair (otherE q0) (.pair t0 (.pair y0
           (.pair n0 (.pair (sOpPure .u32ToNat n0) (.nat Lck))))))))
         (let b : Expr AOps _ _ := .v2
          let k1E := findSomeOptB Ls (.fst .v0)
            (candK1EntryE .v0
              (.fst (.snd b))
              (.fst (.snd (.snd (.snd (.snd b)))))
              (.fst (.snd (.snd (.snd (.snd (.snd b))))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd b))))))))
          let k3E := findSomeOptB Ls (.fst .v0)
            (candK3EntryE .v0
              (.fst (.snd (.snd b)))
              (.fst (.snd (.snd (.snd (.snd b)))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd b))))))))
          let k2E := findSomeOptB Ls (.fst .v0)
            (candK2EntryE .v0
              (.fst (.snd b))
              (.fst (.snd (.snd (.snd b))))
              (.fst (.snd (.snd (.snd (.snd b)))))
              (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
              (.snd (.snd (.snd (.snd (.snd (.snd (.snd b))))))))
          let bc : Expr AOps _ _ := .v2
          let k4CurOptE := findSomeOptB Ls (.fst .v0)
            (candK4CurE .v0
              (.fst (.snd (.snd bc)))
              (.fst (.snd (.snd (.snd bc))))
              (.fst (.snd (.snd (.snd (.snd bc))))))
          let k4E := Expr.caseOpt k4CurOptE .none
            (findSomeOptB Ls (.fst .v1)
              (candK4InnerE .v0
                (.fst (.snd (.snd .v3)))
                (.fst (.snd (.snd (.snd .v3))))
                (.fst .v2)
                (.snd .v2)
                (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
                (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))))
          orElseOptE (orElseOptE (orElseOptE k1E k3E) k2E) k4E)))

theorem eval_snapCandFastE (idA idB : IdentityKey) (Ls Lck : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ) (w : Bytes)
    (hsnaps : snapsE.eval ρ = snaps.map snapEnc) (hlen : snaps.length ≤ Ls)
    (hq : qBE.eval ρ = partyEnc Q) (ht : tE.eval ρ = t) (hw : wE.eval ρ = w)
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) :
    (snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) Ls Lck snapsE qBE tE wE).eval ρ =
      snapCandFastPure Lck (paramsV1 C K idA idB) snaps Q t w := by
  have hparse := atomicPureOps_eval_signalMsgParse_lossless ℓ Pt w
  have hcodec : (paramsV1 C K idA idB).codec = protoSignalCodec := rfl
  have hC : (paramsV1 C K idA idB).C = C := rfl
  unfold snapCandFastE snapCandFastPure
  rw [hcodec, hC]
  refine Eq.trans (eval_eLet_eq (va := (snaps.map snapEnc, (partyEnc Q, (t, w)))) ?_) ?_
  · simp only [Expr.eval, hsnaps, hq, ht, hw]
  · have hparse' :
        (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .signalMsgParse
          (Γ := Ty.prod (.list (snapT ℓ Pt)) (.prod .bool (.prod .nat (B 32))) :: Γ)
          (.snd (.snd (.snd .v0)))).eval
          (.cons (snaps.map snapEnc, (partyEnc Q, (t, w))) ρ) =
        match SignalMessage.tryFrom protoSignalCodec w with
        | .ok m => some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
            (m.ciphertext, (m.pqRatchet, m.addresses)))
        | .error _ => none := by
      rw [eval_sOpPure]
      exact hparse
    refine Eq.trans (eval_caseOpt_eq hparse') ?_
    rcases SignalMessage.tryFrom protoSignalCodec w with _ | msg
    · rfl
    · dsimp only
      refine Eq.trans (eval_eLet_eq (va :=
          (snaps.map snapEnc, (partyEnc Q, (partyEnc Q.other,
            (t, (msg.senderRatchetKey, (msg.counter, (msg.counter.toNat, Lck)))))))) ?_) ?_
      · have hqo : (!partyEnc Q) = partyEnc Q.other := (partyEnc_other Q).symm
        simp only [Expr.eval, otherE_eval, eval_sOpPure, AtomicPureOp.eval,
          Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ, hqo]
      · simp only [eval_orElseOptE, orElse_assoc_local]
        have htake : (List.map (snapEnc (ℓ := ℓ) (Pt := Pt)) snaps).take Ls =
            snaps.map snapEnc :=
          List.take_of_length_le (by simpa using hlen)
        refine orElse_congr_eq ?_ (orElse_congr_eq ?_ (orElse_congr_eq ?_ ?_))
        · refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun e he _ => ?_
          · exact htake
          · exact eval_candK1EntryE _ _ _ _ _ _ _ e Q msg.senderRatchetKey msg.counter Lck
              rfl rfl rfl rfl rfl rfl (hWF e he)
        · refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun e _ _ => ?_
          · exact htake
          · exact eval_candK3EntryE _ _ _ _ _ _ e Q msg.senderRatchetKey msg.counter Lck
              rfl rfl rfl rfl rfl
        · refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun e _ => ?_
          · exact htake
          · intro _
            exact eval_candK2EntryE _ _ _ _ _ _ _ e Q t msg.senderRatchetKey msg.counter Lck
              rfl rfl rfl rfl rfl rfl
        · refine Eq.trans (eval_caseOpt_eq (v? :=
              (snaps.findSome? (candK4Cur Q t msg.senderRatchetKey)).map
                (fun p => (p.1, bytesToKey32 p.2.bytes.toList))) ?_) ?_
          · refine Eq.trans ?_ (findSome?_map_comm snaps (candK4Cur Q t msg.senderRatchetKey)
              (fun p => (p.1, bytesToKey32 p.2.bytes.toList))).symm
            refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun e he _ => ?_
            · exact htake
            · exact eval_candK4CurE _ _ _ _ _ e Q t msg.senderRatchetKey rfl rfl rfl rfl (hWF e he)
          · rcases snaps.findSome? (candK4Cur Q t msg.senderRatchetKey) with _ | ⟨rcSrk, scCurPriv⟩
            · rfl
            · dsimp only [Option.map, Option.bind]
              refine eval_findSomeOptB Ls _ _ _ snaps snapEnc ?_ _ fun ep _ _ => ?_
              · dsimp only [Expr.eval, Expr.v1, Env.get]
                exact htake
              · exact eval_candK4InnerE _ _ _ _ _ _ _ _ ep Q t rcSrk scCurPriv msg.counter Lck
                  rfl rfl rfl rfl rfl rfl rfl

theorem cost_snapCandFastE (Ls Lck : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) Ls Lck snapsE qBE tE wE).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost +
        ℓ / 32 + bits Lck + 22200 * Ls + 1200 := by
  let tOut := Ty.prod (.list (snapT ℓ Pt)) (.prod .bool (.prod .nat (B 32)))
  let tIn := Ty.prod (.list (snapT ℓ Pt))
    (.prod .bool (.prod .bool (.prod .nat (.prod PK (.prod U32 (.prod .nat .nat))))))
  let Γin := tIn :: signalParsedT (ℓ := ℓ) (Pt := Pt) :: tOut :: Γ
  let Γf := snapT ℓ Pt :: Ty.opt (candT ℓ Pt) :: Γin
  let Γfc := snapT ℓ Pt :: Ty.opt (candK4CurT ℓ Pt) :: Γin
  let Γk4s := candK4CurT ℓ Pt :: Γin
  let Γfi := snapT ℓ Pt :: Ty.opt (candT ℓ Pt) :: Γk4s
  let b : Expr AOps Γf tIn := .v2
  let bc : Expr AOps Γfc tIn := .v2
  let eb1 := candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd (.snd b))))) (.fst (.snd (.snd (.snd (.snd (.snd b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb3 := candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb2 := candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb4c := candK4CurE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γfc) .v0 (.fst (.snd (.snd bc)))
    (.fst (.snd (.snd (.snd bc)))) (.fst (.snd (.snd (.snd (.snd bc)))))
  let eb4i := candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γfi) .v0 (.fst (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd .v3)))) (.fst .v2) (.snd .v2)
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
  have hb1 := cost_candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd (.snd b))))) (.fst (.snd (.snd (.snd (.snd (.snd b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb3 := cost_candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb2 := cost_candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb4c := cost_candK4CurE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γfc) .v0 (.fst (.snd (.snd bc)))
    (.fst (.snd (.snd (.snd bc)))) (.fst (.snd (.snd (.snd (.snd bc)))))
  have hb4i := cost_candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γfi) .v0 (.fst (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd .v3)))) (.fst .v2) (.snd .v2)
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
  have hf1 := cost_findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb1
  have hf3 := cost_findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb3
  have hf2 := cost_findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb2
  have hf4c := cost_findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb4c
  have hf4i := cost_findSomeOptB (O' := AOps) Ls (.fst (.v1 : Expr AOps Γk4s tIn)) eb4i
  change eb1.cost ≤ _ at hb1; change eb3.cost ≤ _ at hb3
  change eb2.cost ≤ _ at hb2; change eb4c.cost ≤ _ at hb4c; change eb4i.cost ≤ _ at hb4i
  unfold snapCandFastE
  change (eLet _ (.caseOpt _ .none (eLet _ (orElseOptE (orElseOptE (orElseOptE
    (findSomeOptB Ls (.fst .v0) eb1) (findSomeOptB Ls (.fst .v0) eb3))
    (findSomeOptB Ls (.fst .v0) eb2))
    (.caseOpt (findSomeOptB Ls (.fst .v0) eb4c) .none (findSomeOptB Ls (.fst .v1) eb4i)))))).cost ≤ _
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb1 = ef1 at hf1 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb3 = ef3 at hf3 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb2 = ef2 at hf2 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb4c = ef4c at hf4c ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v1 : Expr AOps Γk4s tIn)) eb4i = ef4i at hf4i ⊢
  generalize eb1 = x1 at hb1 hf1; generalize eb3 = x3 at hb3 hf3
  generalize eb2 = x2 at hb2 hf2; generalize eb4c = x4c at hb4c hf4c
  generalize eb4i = x4i at hb4i hf4i
  simp only [b, bc, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hb1 hb3 hb2 hb4c hb4i hf1 hf3 hf2 hf4c hf4i
  have hm1 : Ls * (x1.cost + 5) ≤ 20400 * Ls := by
    rw [Nat.mul_comm 20400 Ls]; exact Nat.mul_le_mul_left Ls (by omega)
  have hm3 : Ls * (x3.cost + 5) ≤ 500 * Ls := by
    rw [Nat.mul_comm 500 Ls]; exact Nat.mul_le_mul_left Ls (by omega)
  have hm2 : Ls * (x2.cost + 5) ≤ 400 * Ls := by
    rw [Nat.mul_comm 400 Ls]; exact Nat.mul_le_mul_left Ls (by omega)
  have hm4c : Ls * (x4c.cost + 5) ≤ 400 * Ls := by
    rw [Nat.mul_comm 400 Ls]; exact Nat.mul_le_mul_left Ls (by omega)
  have hm4i : Ls * (x4i.cost + 5) ≤ 450 * Ls := by
    rw [Nat.mul_comm 450 Ls]; exact Nat.mul_le_mul_left Ls (by omega)
  simp only [cost_eLet, orElseOptE, otherE, Expr.cost, cost_sOpPure, AtomicPureOp.cost,
    Expr.v0, Expr.v1]
  omega

theorem descBits_snapCandFastE (Ls Lck : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    atomicExprDescBits atomicSessionOpDescBits
      (snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) Ls Lck snapsE qBE tE wE) ≤
      atomicExprDescBits atomicSessionOpDescBits snapsE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      10 * bits Ls + 2 * bits Lck + 10000 := by
  have hbits := small_bits_bounds
  let tOut := Ty.prod (.list (snapT ℓ Pt)) (.prod .bool (.prod .nat (B 32)))
  let tIn := Ty.prod (.list (snapT ℓ Pt))
    (.prod .bool (.prod .bool (.prod .nat (.prod PK (.prod U32 (.prod .nat .nat))))))
  let Γin := tIn :: signalParsedT (ℓ := ℓ) (Pt := Pt) :: tOut :: Γ
  let Γf := snapT ℓ Pt :: Ty.opt (candT ℓ Pt) :: Γin
  let Γfc := snapT ℓ Pt :: Ty.opt (candK4CurT ℓ Pt) :: Γin
  let Γk4s := candK4CurT ℓ Pt :: Γin
  let Γfi := snapT ℓ Pt :: Ty.opt (candT ℓ Pt) :: Γk4s
  let b : Expr AOps Γf tIn := .v2
  let bc : Expr AOps Γfc tIn := .v2
  let eb1 := candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd (.snd b))))) (.fst (.snd (.snd (.snd (.snd (.snd b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb3 := candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb2 := candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  let eb4c := candK4CurE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γfc) .v0 (.fst (.snd (.snd bc)))
    (.fst (.snd (.snd (.snd bc)))) (.fst (.snd (.snd (.snd (.snd bc)))))
  let eb4i := candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γfi) .v0 (.fst (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd .v3)))) (.fst .v2) (.snd .v2)
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
  have hb1 := descBits_candK1EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd (.snd b))))) (.fst (.snd (.snd (.snd (.snd (.snd b))))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb3 := descBits_candK3EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd (.snd b)))
    (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb2 := descBits_candK2EntryE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γf) .v0 (.fst (.snd b))
    (.fst (.snd (.snd (.snd b)))) (.fst (.snd (.snd (.snd (.snd b)))))
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd b)))))))
  have hb4c := descBits_candK4CurE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γfc) .v0 (.fst (.snd (.snd bc)))
    (.fst (.snd (.snd (.snd bc)))) (.fst (.snd (.snd (.snd (.snd bc)))))
  have hb4i := descBits_candK4InnerE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γfi) .v0 (.fst (.snd (.snd .v3)))
    (.fst (.snd (.snd (.snd .v3)))) (.fst .v2) (.snd .v2)
    (.fst (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd .v3)))))))
  have hf1 := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v0 : Expr AOps Γin tIn)) eb1
  have hf3 := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v0 : Expr AOps Γin tIn)) eb3
  have hf2 := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v0 : Expr AOps Γin tIn)) eb2
  have hf4c := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v0 : Expr AOps Γin tIn)) eb4c
  have hf4i := descBits_findSomeOptB (O' := AOps) atomicSessionOpDescBits Ls
    (.fst (.v1 : Expr AOps Γk4s tIn)) eb4i
  change atomicExprDescBits atomicSessionOpDescBits eb1 ≤ _ at hb1
  change atomicExprDescBits atomicSessionOpDescBits eb3 ≤ _ at hb3
  change atomicExprDescBits atomicSessionOpDescBits eb2 ≤ _ at hb2
  change atomicExprDescBits atomicSessionOpDescBits eb4c ≤ _ at hb4c
  change atomicExprDescBits atomicSessionOpDescBits eb4i ≤ _ at hb4i
  unfold snapCandFastE
  change atomicExprDescBits atomicSessionOpDescBits
    (eLet _ (.caseOpt _ .none (eLet _ (orElseOptE (orElseOptE (orElseOptE
      (findSomeOptB Ls (.fst .v0) eb1) (findSomeOptB Ls (.fst .v0) eb3))
      (findSomeOptB Ls (.fst .v0) eb2))
      (.caseOpt (findSomeOptB Ls (.fst .v0) eb4c) .none
        (findSomeOptB Ls (.fst .v1) eb4i)))))) ≤ _
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb1 = ef1 at hf1 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb3 = ef3 at hf3 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb2 = ef2 at hf2 ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v0 : Expr AOps Γin tIn)) eb4c = ef4c at hf4c ⊢
  generalize findSomeOptB (O' := AOps) Ls (.fst (.v1 : Expr AOps Γk4s tIn)) eb4i = ef4i at hf4i ⊢
  generalize eb1 = x1 at hb1 hf1; generalize eb3 = x3 at hb3 hf3
  generalize eb2 = x2 at hb2 hf2; generalize eb4c = x4c at hb4c hf4c
  generalize eb4i = x4i at hb4i hf4i
  simp only [b, bc, descBits_eLet, descBits_sOpPure, orElseOptE, otherE, candT, candK4CurT,
    PK, BV256, Expr.v0, Expr.v1, Expr.v2, Expr.v3, atomicExprDescBits, atomicPureOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hb1 hb3 hb2 hb4c hb4i hf1 hf3 hf2 hf4c hf4i ⊢
  omega

end CandidateCombinators

/-! ## Atomic snapshot seed derivation -/

section KnownSeedAtomic

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

private theorem bits_le_succ_local (n : ℕ) : bits n ≤ n + 1 := by
  have hlt : n < 2 ^ (n + 1) :=
    Nat.lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by omega) (by omega))
  exact bits_le_of_lt_pow (by omega) hlt

private theorem eval_compCaseOpt_eq {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    {Γ : List (Ty ASig)} {α β : Ty ASig}
    {o : Expr AOps Γ (.opt α)} {n : Comp AOps I' Γ β} {s : Comp AOps I' (α :: Γ) β}
    {ρ : Env Γ} {v? : Option α.denote} :
    o.eval ρ = v? →
    (Comp.caseOpt o n s).eval ρ =
      match v? with
      | none => n.eval ρ
      | some v => s.eval (.cons v ρ)
  | rfl => by simp only [Comp.eval]; cases o.eval ρ <;> rfl

private theorem eval_compCaseSum_eq {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    {Γ : List (Ty ASig)} {α β γ : Ty ASig}
    {o : Expr AOps Γ (.sum α β)} {l : Comp AOps I' (α :: Γ) γ} {r : Comp AOps I' (β :: Γ) γ}
    {ρ : Env Γ} {v : (α.denote ⊕ β.denote)} :
    o.eval ρ = v →
    (Comp.caseSum o l r).eval ρ =
      match v with
      | .inl a => l.eval (.cons a ρ)
      | .inr b => r.eval (.cons b ρ)
  | rfl => by simp only [Comp.eval]; cases o.eval ρ <;> rfl

def candFinishIterC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (Kc : ℕ)
    {Γ : List (Ty ASig)} (candOptE : Expr AOps Γ (.opt (candT ℓ Pt))) :
    Comp AOps I' Γ (.opt (B 32)) :=
  .caseOpt candOptE
    (.ret .none)
    (.caseSum .v0
      (.ret (.some (sOpPure .bv256ToBytes32 .v0)))
      (.bind (chainSeedIterC I' Kc .v0)
        (.ret (.some (sOpPure .bv256ToBytes32 .v0)))))

theorem eval_candFinishIterC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (Kc : ℕ)
    {Γ : List (Ty ASig)} (candOptE : Expr AOps Γ (.opt (candT ℓ Pt))) (ρ : Env Γ)
    (hsteps : ∀ k s, candOptE.eval ρ = some (.inr (k, s)) → s ≤ Kc) :
    (candFinishIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' Kc candOptE).eval ρ =
      pure ((candOptE.eval ρ).map (candEval C.F)) := by
  unfold candFinishIterC
  rcases hcand : candOptE.eval ρ with _ | (sd | ⟨ckKey, steps⟩)
  · rw [eval_compCaseOpt_eq hcand]; simp [Comp.eval, Expr.eval]
  · rw [eval_compCaseOpt_eq hcand]; dsimp only
    rw [eval_compCaseSum_eq (v := .inl sd) (by simp [Expr.eval, Expr.v0])]
    simp [Comp.eval, Expr.eval, eval_sOpPure, AtomicPureOp.eval, Expr.v0, candEval]
  · rw [eval_compCaseOpt_eq hcand]; dsimp only
    rw [eval_compCaseSum_eq (v := .inr (ckKey, steps)) (by simp [Expr.eval, Expr.v0])]
    dsimp only [Comp.eval, Option.map, candEval]
    rw [eval_chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' Kc .v0
      (.cons (t := Ty.prod BV256 .nat) (ckKey, steps)
        (.cons (t := candT ℓ Pt) (Sum.inr (ckKey, steps)) ρ))
      ckKey steps (by simp [Expr.eval, Expr.v0]) (hsteps ckKey steps hcand),
      pure_bind]
    simp only [Expr.eval, eval_sOpPure, AtomicPureOp.eval, Expr.v0, Env.get_cons_zero]
    dsimp only [chainHmac]
    rw [keyToBytes32_bytesToKey32 _
      (hmacWith_length C.F (keyToBytes32 (chainKeyAfter C.F steps ckKey)) [messageKeySeed])]

def knownSeedBAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (L Kc : ℕ)
    {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    Comp AOps I' Γ (.opt (B 32)) :=
  candFinishIterC I' Kc (snapCandFastE L Kc snapsE qBE tE wE)

theorem knownSeedBAtomicC_eval_snapEnc (idA idB : IdentityKey)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (L Kc : ℕ)
    {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ) (w : Bytes)
    (hlen : snaps.length ≤ L) (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2)
    (hsnaps : snapsE.eval ρ = snaps.map snapEnc)
    (hq : qBE.eval ρ = partyEnc Q) (ht : tE.eval ρ = t) (hw : wE.eval ρ = w) :
    (knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).eval ρ =
      pure (SanOracleCore.snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w) := by
  have hcand := eval_snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB L Kc snapsE qBE tE wE ρ snaps Q t w
    hsnaps hlen hq ht hw hWF
  unfold knownSeedBAtomicC
  rw [eval_candFinishIterC I' Kc _ ρ (fun k s h => snapCandFastPure_steps_le (hcand ▸ h)), hcand]
  exact congrArg pure (snapCandFastPure_map_candEval_eq Kc (paramsV1 C K idA idB) snaps Q t w hWF)

theorem knownSeedBAtomicC_eval (idA idB : IdentityKey)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (L Kc : ℕ)
    {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ) (w : Bytes)
    (hlen : snaps.length ≤ L) (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2)
    (hsnaps : snapsE.eval ρ = snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))))
    (hq : qBE.eval ρ = partyToBool Q) (ht : tE.eval ρ = t) (hw : wE.eval ρ = w) :
    (knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).eval ρ =
      pure (SanOracleCore.snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w) := by
  have hmap : snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))) =
      snaps.map (snapEnc (ℓ := ℓ) (Pt := Pt)) := by
    refine List.map_congr_left fun e _ => ?_
    simp [snapEnc, partyToBool_eq_partyEnc]
  exact knownSeedBAtomicC_eval_snapEnc idA idB I' L Kc snapsE qBE tE wE ρ snaps Q t w
    hlen hWF (hsnaps.trans hmap) (hq.trans (partyToBool_eq_partyEnc Q)) ht hw

@[simp] theorem knownSeedBAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) (wt : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).queries wt ws = 0 := by
  simp [knownSeedBAtomicC, candFinishIterC, Comp.queries, queries_chainSeedIterC]

theorem knownSeedBAtomicC_cost_tight_linear {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost +
        ℓ / 32 + bits Kc + 28 * Kc + 22200 * L + 1400 := by
  have hcand := cost_snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L Kc snapsE qBE tE wE
  let Γr := Ty.prod BV256 .nat :: candT ℓ Pt :: Γ
  have hiter := cost_chainSeedIterC_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' Kc (.v0 : Expr AOps Γr (.prod BV256 .nat))
  unfold knownSeedBAtomicC candFinishIterC
  generalize snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L Kc snapsE qBE tE wE = ec at hcand ⊢
  generalize chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' Kc (.v0 : Expr AOps Γr (.prod BV256 .nat)) = ci at hiter ⊢
  simp only [Comp.cost, Expr.cost, cost_sOpPure, AtomicPureOp.cost, Expr.v0] at hiter ⊢
  omega

private theorem linear_cost_le_quad_cost (L : ℕ) :
    22200 * L ≤ 420 * (L * L) + 22000 * L := by
  rcases L with _ | n
  · omega
  · have hsq : n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_of_pos_left (n + 1) (Nat.succ_pos n)
    have h420 : 420 * (n + 1) ≤ 420 * ((n + 1) * (n + 1)) := Nat.mul_le_mul_left 420 hsq
    omega

theorem knownSeedBAtomicC_cost_tight {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost +
        ℓ / 32 + bits Kc + 28 * Kc + 420 * (L * L) + 22000 * L + 1400 := by
  refine Nat.le_trans (knownSeedBAtomicC_cost_tight_linear (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE) ?_
  have hL := linear_cost_le_quad_cost L
  generalize snapsE.cost + qBE.cost + tE.cost + wE.cost + ℓ / 32 + bits Kc + 28 * Kc = base
  omega

theorem knownSeedBAtomicC_cost_linear {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost +
        2 * (ℓ / 32) + 80000 * L + 30 * Kc + 50000 := by
  have ht := knownSeedBAtomicC_cost_tight_linear (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE
  have hb := bits_le_succ_local Kc
  omega

theorem knownSeedBAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost +
        2 * (ℓ / 32) + 80000 * L + 600 * (L * L) + 30 * Kc + 50000 := by
  have ht := knownSeedBAtomicC_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE
  have hb := bits_le_succ_local Kc
  omega

theorem knownSeedBAtomicC_descBits_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE) ≤
      atomicExprDescBits atomicSessionOpDescBits snapsE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      10 * bits L + 4 * bits Kc + 10600 := by
  have hbits := small_bits_bounds
  have hcand := descBits_snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L Kc snapsE qBE tE wE
  let Γr := Ty.prod BV256 .nat :: candT ℓ Pt :: Γ
  have hiter := descBits_chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' Kc sB qB (.v0 : Expr AOps Γr (.prod BV256 .nat))
  unfold knownSeedBAtomicC candFinishIterC
  generalize snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L Kc snapsE qBE tE wE = ec at hcand ⊢
  generalize chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' Kc (.v0 : Expr AOps Γr (.prod BV256 .nat)) = ci at hiter ⊢
  simp only [descBits_sOpPure, B, Expr.v0,
    atomicCompDescBits, atomicExprDescBits, atomicPureOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hiter ⊢
  omega

/-- Computes `snapshotMessageKeySeedBFast` via five non-nested bounded scans and at most one `chainSeedIterC` walk. -/
def knownSeedBAtomicFastC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (L Kc : ℕ)
    {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    Comp AOps I' Γ (.opt (B 32)) :=
  candFinishIterC I' Kc (snapCandFastE L Kc snapsE qBE tE wE)

theorem knownSeedBAtomicFastC_eval_snapEnc_fast (idA idB : IdentityKey)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (L Kc : ℕ)
    {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ) (w : Bytes)
    (hlen : snaps.length ≤ L) (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2)
    (hsnaps : snapsE.eval ρ = snaps.map snapEnc)
    (hq : qBE.eval ρ = partyEnc Q) (ht : tE.eval ρ = t) (hw : wE.eval ρ = w) :
    (knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).eval ρ =
      pure (snapshotMessageKeySeedBFast Kc (paramsV1 C K idA idB) snaps Q t w) := by
  have hcand := eval_snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB L Kc snapsE qBE tE wE ρ snaps Q t w
    hsnaps hlen hq ht hw hWF
  unfold knownSeedBAtomicFastC
  rw [eval_candFinishIterC I' Kc _ ρ (fun k s h => snapCandFastPure_steps_le (hcand ▸ h)), hcand]
  exact congrArg pure (snapCandFastPure_map_candEval_eq_fast Kc (paramsV1 C K idA idB) snaps Q t w hWF)

theorem knownSeedBAtomicFastC_eval_snapEnc (idA idB : IdentityKey)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (L Kc : ℕ)
    {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ) (w : Bytes)
    (hlen : snaps.length ≤ L) (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2)
    (hsnaps : snapsE.eval ρ = snaps.map snapEnc)
    (hq : qBE.eval ρ = partyEnc Q) (ht : tE.eval ρ = t) (hw : wE.eval ρ = w) :
    (knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).eval ρ =
      pure (SanOracleCore.snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w) := by
  rw [knownSeedBAtomicFastC_eval_snapEnc_fast idA idB I' L Kc snapsE qBE tE wE ρ snaps Q t w
    hlen hWF hsnaps hq ht hw,
    snapshotMessageKeySeedBFast_eq_snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w]

theorem knownSeedBAtomicFastC_eval_fast (idA idB : IdentityKey)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (L Kc : ℕ)
    {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ) (w : Bytes)
    (hlen : snaps.length ≤ L) (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2)
    (hsnaps : snapsE.eval ρ = snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))))
    (hq : qBE.eval ρ = partyToBool Q) (ht : tE.eval ρ = t) (hw : wE.eval ρ = w) :
    (knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).eval ρ =
      pure (snapshotMessageKeySeedBFast Kc (paramsV1 C K idA idB) snaps Q t w) := by
  have hmap : snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))) =
      snaps.map (snapEnc (ℓ := ℓ) (Pt := Pt)) := by
    refine List.map_congr_left fun e _ => ?_
    simp [snapEnc, partyToBool_eq_partyEnc]
  exact knownSeedBAtomicFastC_eval_snapEnc_fast idA idB I' L Kc snapsE qBE tE wE ρ snaps Q t w
    hlen hWF (hsnaps.trans hmap) (hq.trans (partyToBool_eq_partyEnc Q)) ht hw

theorem knownSeedBAtomicFastC_eval (idA idB : IdentityKey)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) (L Kc : ℕ)
    {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ) (w : Bytes)
    (hlen : snaps.length ≤ L) (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2)
    (hsnaps : snapsE.eval ρ = snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))))
    (hq : qBE.eval ρ = partyToBool Q) (ht : tE.eval ρ = t) (hw : wE.eval ρ = w) :
    (knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).eval ρ =
      pure (SanOracleCore.snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w) := by
  rw [knownSeedBAtomicFastC_eval_fast idA idB I' L Kc snapsE qBE tE wE ρ snaps Q t w
    hlen hWF hsnaps hq ht hw,
    snapshotMessageKeySeedBFast_eq_snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w]

@[simp] theorem knownSeedBAtomicFastC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) (wt : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).queries wt ws = 0 := by
  simp [knownSeedBAtomicFastC, candFinishIterC, Comp.queries, queries_chainSeedIterC]

theorem knownSeedBAtomicFastC_cost_tight {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost +
        ℓ / 32 + bits Kc + 28 * Kc + 22200 * L + 1400 := by
  have hcand := cost_snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L Kc snapsE qBE tE wE
  let Γr := Ty.prod BV256 .nat :: candT ℓ Pt :: Γ
  have hiter := cost_chainSeedIterC_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' Kc (.v0 : Expr AOps Γr (.prod BV256 .nat))
  unfold knownSeedBAtomicFastC candFinishIterC
  generalize snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L Kc snapsE qBE tE wE = ec at hcand ⊢
  generalize chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' Kc (.v0 : Expr AOps Γr (.prod BV256 .nat)) = ci at hiter ⊢
  simp only [Comp.cost, Expr.cost, cost_sOpPure, AtomicPureOp.cost, Expr.v0] at hiter ⊢
  omega

theorem knownSeedBAtomicFastC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    (knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost +
        2 * (ℓ / 32) + 80000 * L + 30 * Kc + 50000 := by
  have ht := knownSeedBAtomicFastC_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE
  have hb := bits_le_succ_local Kc
  omega

theorem knownSeedBAtomicFastC_descBits_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (L Kc : ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32)) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) I' L Kc snapsE qBE tE wE) ≤
      atomicExprDescBits atomicSessionOpDescBits snapsE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      10 * bits L + 4 * bits Kc + 10600 := by
  have hbits := small_bits_bounds
  have hcand := descBits_snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L Kc snapsE qBE tE wE
  let Γr := Ty.prod BV256 .nat :: candT ℓ Pt :: Γ
  have hiter := descBits_chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' Kc sB qB (.v0 : Expr AOps Γr (.prod BV256 .nat))
  unfold knownSeedBAtomicFastC candFinishIterC
  generalize snapCandFastE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) L Kc snapsE qBE tE wE = ec at hcand ⊢
  generalize chainSeedIterC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' Kc (.v0 : Expr AOps Γr (.prod BV256 .nat)) = ci at hiter ⊢
  simp only [descBits_sOpPure, B, Expr.v0,
    atomicCompDescBits, atomicExprDescBits, atomicPureOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hiter ⊢
  omega

end KnownSeedAtomic

/-! ## Known-seed decryption -/

section KDecryptAndCombined

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[reducible] def kDecOutT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod .nat (.prod .nat (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) (PlainT (ℓ := ℓ) (Pt := Pt))))

def kDecOutV (r : ℕ × (ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    (kDecOutT ℓ Pt).denote :=
  (r.1, (r.2.1, (lpubV r.2.2.1, r.2.2.2)))

private theorem addrBytes_length (sid : Bool × List.Vector (BitVec 8) 16) (dev : BitVec 8) :
    (addrBytes sid dev).length = 18 := by
  simp [addrBytes]

theorem serializedPartyAddresses_len_le_36 (s r : Party) (v : Bytes)
    (h : serializedPartyAddresses uuidTryParse s r = some v) : v.length ≤ 36 := by
  unfold serializedPartyAddresses at h
  dsimp only [Bind.bind, Option.bind, Pure.pure] at h
  rcases h1 : serviceIdParse uuidTryParse (utf8 (partyAddressName s)) with _ | sidS <;>
    rw [h1] at h
  · cases h
  · rcases h2 : serviceIdParse uuidTryParse (utf8 (partyAddressName r)) with _ | sidR <;>
      rw [h2] at h
    · cases h
    · injection h with hv
      rw [← hv]
      simp [List.length_append, addrBytes_length]

def optBytesLitE {Γ : List (Ty ASig)} : Option Bytes → Expr AOps Γ (.opt (B 32))
  | none => .none
  | some v => .some (sOpPure (.bytesLit 32 v) .unit)

@[simp] theorem eval_optBytesLitE {Γ : List (Ty ASig)} (a? : Option Bytes) (ρ : Env Γ) :
    (optBytesLitE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) a?).eval ρ = a? := by
  cases a? <;> rfl

theorem cost_optBytesLitE {Γ : List (Ty ASig)} (a? : Option Bytes)
    (ha : ∀ v, a? = some v → v.length ≤ 36) :
    (optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) a?).cost ≤ 70 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  rcases a? with _ | v
  · simp [optBytesLitE, Expr.cost]
  · have hv : v.length ≤ 36 := ha v rfl
    simp only [optBytesLitE, Expr.cost, cost_sOpPure, AtomicPureOp.cost, h32]
    omega

theorem descBits_optBytesLitE {Γ : List (Ty ASig)} (a? : Option Bytes)
    (ha : ∀ v, a? = some v → v.length ≤ 36) :
    atomicExprDescBits atomicSessionOpDescBits
      (optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) a?) ≤ 350 := by
  have hbits := small_bits_bounds
  rcases a? with _ | v
  · dsimp only [optBytesLitE, B, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits]
    omega
  · have hv : v.length ≤ 36 := ha v rfl
    have hbv : bits v.length ≤ 6 := bits_le_of_lt_pow (by omega) (by omega)
    simp only [optBytesLitE, descBits_sOpPure, atomicExprDescBits, atomicPureOpDescBits]
    omega

theorem keyToBytesVec32_salt32V (s : List.Vector (BitVec 8) 32) :
    keyToBytesVec32 (salt32V s) = s := by
  rcases s with ⟨bs, hbs⟩
  apply List.Vector.eq
  exact keyToBytes32_bytesToKey32 bs hbs

def kDecryptAtomicPE (P : Params Bytes (BitVec 512))
    (idA idB : IdentityKey) (B_cap : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (seedE : Expr AOps Γ (B 32)) :
    Expr AOps Γ (.opt (kDecOutT ℓ Pt)) :=
  eLet (.pair qBE (.pair wE (.pair c'E seedE)))
    (let w0 : Expr AOps _ (B 32) := .fst (.snd .v0)
     let c'0 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd .v0))
     let lPubOptE : Expr AOps _ (.opt (lpubT (ℓ := ℓ) (Pt := Pt))) :=
       eLet (.snd (.snd c'0)) (liftFig8Expr (lPubOfExpr ℓ Pt C Dh encPt encT lam .v0))
     let kDecOptE : Expr AOps _ (.opt (PlainT (ℓ := ℓ) (Pt := Pt))) :=
       .caseOpt (sOpPure .signalMsgParse w0) .none
         (let b1 : Expr AOps _ _ := .v1
          let c'1 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd b1))
          let seed1 : Expr AOps _ (B 32) := .snd (.snd (.snd b1))
          eLet (sOpSym .deriveMsgKeys
              (.pair (sOpPure .bytesToBv256 seed1)
                (.pair (sOpPure (.u32Lit 0#32) .unit)
                  (.some (.snd (.snd (.snd c'1)))))))
            (let b2 : Expr AOps _ _ := .v2
             let q2 : Expr AOps _ .bool := .fst b2
             let w2 : Expr AOps _ (B 32) := .fst (.snd b2)
             let expAddr := .ite q2 (optBytesLitE P.addrAB) (optBytesLitE P.addrBA)
             let idSender := .ite q2 (idKeyAtomLitE idA) (idKeyAtomLitE idB)
             let idRecv := .ite q2 (idKeyAtomLitE idB) (idKeyAtomLitE idA)
             .ite (.not (sOpSym .signalMsgVerifyMac
                 (.pair w2 (.pair expAddr (.pair idSender (.pair idRecv (.fst (.snd .v0))))))))
               .none
               (sOpSym .aes256CbcDec
                 (.pair (.fst .v0) (.pair (.fst (.snd (.snd .v0))) (.fst (.snd .v1)))))))
     eLet (.pair lPubOptE kDecOptE)
       (.caseOpt (.fst .v0) .none
         (.caseOpt (.snd .v1) .none
           (let c'3 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd (.snd .v3))
            .some (.pair (minN (.fst (.fst c'3)) (.nat B_cap))
              (.pair (minN (.fst (.snd c'3)) (.nat B_cap))
                (.pair .v1 .v0)))))))

/-- Atomic expression for `simKDecryptFig8`. -/
def kDecryptAtomicE (idA idB : IdentityKey) (B_cap : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (seedE : Expr AOps Γ (B 32)) :
    Expr AOps Γ (.opt (kDecOutT ℓ Pt)) :=
  kDecryptAtomicPE (paramsV1 C K idA idB) idA idB B_cap qBE wE c'E seedE

private def simKDecRaw (P : Params Bytes (BitVec 512)) (qB : Bool)
    (w : Bytes) (c' : Fig8C Pt) (seed : Bytes) : Option Bytes :=
  let Q := partyDec qB
  let idOf := fun R : Party => if R == Party.A then P.idA else P.idB
  match SignalMessage.tryFrom P.codec w with
  | .error _ => none
  | .ok msg =>
    let mk := deriveMessageKeys P.C.F (some c'.2.2.2) seed
    if !(msg.verifyMacWithAddresses P.C.F (P.expectedAddrs Q) (idOf Q.other) (idOf Q) mk.2) then
      none
    else aesCbcDecrypt P.C.D mk.1.1 mk.1.2 msg.ciphertext

omit [DecidableEq Pt] [Zero Pt] in
private theorem simKDecryptFig8_eq_raw (P : Params Bytes (BitVec 512)) (B_cap : ℕ)
    (qB : Bool) (w : Bytes) (c' : Fig8C Pt) (seed : Bytes) :
    simKDecryptFig8 P ℓ B_cap qB w c' seed =
      match lPubOf P.codec c'.2.2, simKDecRaw P qB w c' seed with
      | some pub, some m_raw =>
        some (min c'.1.1 B_cap, (min c'.2.1 B_cap, (pub, padOrTruncatePlain ℓ m_raw)))
      | _, _ => none := rfl

private theorem kDecryptAtomicPE_eval_bool (P : Params Bytes (BitVec 512))
    (idA idB : IdentityKey) (B_cap : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (seedE : Expr AOps Γ (B 32)) (ρ : Env Γ)
    (qB : Bool) (w : Bytes) (c' : Fig8C Pt) (seed : Bytes)
    (hC : P.C = C) (hcodec : P.codec = protoSignalCodec)
    (hidA' : P.idA = idA) (hidB' : P.idB = idB)
    (hq : qBE.eval ρ = qB) (hw : wE.eval ρ = w) (hc' : c'E.eval ρ = fig8CtV c')
    (hseed : seedE.eval ρ = seed) (hseedLen : seed.length = 32) :
    (kDecryptAtomicPE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) P idA idB B_cap qBE wE c'E seedE).eval ρ =
      (simKDecryptFig8 P ℓ B_cap qB w c' seed).map kDecOutV := by
  rw [simKDecryptFig8_eq_raw]
  unfold kDecryptAtomicPE
  refine Eq.trans (eval_eLet_eq (va := (qB, (w, (fig8CtV c', seed)))) ?_) ?_
  · simp only [Expr.eval, hq, hw, hc', hseed]
  · refine Eq.trans (eval_eLet_eq (va :=
        ((lPubOf P.codec c'.2.2).map lpubV,
         (simKDecRaw P qB w c' seed).map (padOrTruncatePlain ℓ))) ?_) ?_
    · rw [eval_pair_local]
      refine Prod.ext ?_ ?_
      · rw [eval_eLet, liftFig8Expr_eval, lPubOfExpr_eval, hcodec]
        simp [fig8CtV, lctV, wireSaltCtOfV_wireSaltCtV, Expr.eval, Expr.v0]
      · unfold simKDecRaw
        dsimp only
        have hparse' :
            (sOpPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
              (decT := decT) (lam := lam) .signalMsgParse
              (Γ := Ty.prod .bool (.prod (B 32) (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (B 32))) :: Γ)
              (.fst (.snd .v0))).eval
              (.cons (qB, (w, (fig8CtV c', seed))) ρ) =
            match SignalMessage.tryFrom protoSignalCodec w with
            | .ok m => some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
                (m.ciphertext, (m.pqRatchet, m.addresses)))
            | .error _ => none := by
          rw [eval_sOpPure]
          exact atomicPureOps_eval_signalMsgParse_lossless ℓ Pt w
        refine Eq.trans (eval_caseOpt_eq hparse') ?_
        have hAA : (Party.A == Party.A) = true := rfl
        have hBA : (Party.B == Party.A) = false := rfl
        rw [hcodec, hC, hidA', hidB']
        rcases hm : SignalMessage.tryFrom protoSignalCodec w with _ | msg
        · rfl
        · dsimp only
          have hdm : AtomicSymOp.eval ℓ Pt C .deriveMsgKeys
              (bytesToKey32 seed, (0#32, some (salt32V c'.2.2.2))) =
              let mk := deriveMessageKeys C.F (some c'.2.2.2) seed
              (mk.1.1, (mk.2, (mk.1.2, 0#32))) := by
            dsimp only [AtomicSymOp.eval, Option.map, MessageKeyGenerator.generateKeys]
            rw [keyToBytes32_bytesToKey32 seed hseedLen, keyToBytesVec32_salt32V]
          refine Eq.trans (eval_eLet_eq hdm) ?_
          cases qB with
          | false =>
            refine Eq.trans (eval_ite_eq (b := !(msg.verifyMacWithAddresses C.F
                P.addrBA idB idA
                (deriveMessageKeys C.F (some c'.2.2.2) seed).2)) ?_) ?_
            · simp only [Expr.eval, eval_sOpSym, eval_optBytesLitE, eval_idKeyAtomLitE,
                Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ,
                Bool.false_eq_true, ↓reduceIte]
              dsimp only [AtomicSymOp.eval]
              rw [hm]
            · dsimp only [partyDec, Party.other, Params.expectedAddrs]
              simp only [hAA, hBA, Bool.false_eq_true, ↓reduceIte]
              cases msg.verifyMacWithAddresses C.F P.addrBA idB idA
                (deriveMessageKeys C.F (some c'.2.2.2) seed).2 <;> rfl
          | true =>
            refine Eq.trans (eval_ite_eq (b := !(msg.verifyMacWithAddresses C.F
                P.addrAB idA idB
                (deriveMessageKeys C.F (some c'.2.2.2) seed).2)) ?_) ?_
            · simp only [Expr.eval, eval_sOpSym, eval_optBytesLitE, eval_idKeyAtomLitE,
                Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ, ↓reduceIte]
              dsimp only [AtomicSymOp.eval]
              rw [hm]
            · dsimp only [partyDec, Party.other, Params.expectedAddrs]
              simp only [hAA, hBA, Bool.false_eq_true, ↓reduceIte]
              cases msg.verifyMacWithAddresses C.F P.addrAB idA idB
                (deriveMessageKeys C.F (some c'.2.2.2) seed).2 <;> rfl
    · rcases lPubOf P.codec c'.2.2 with _ | pub
      · rfl
      · rcases simKDecRaw P qB w c' seed with _ | m_raw
        · rfl
        · dsimp only [Option.map]
          simp only [Expr.eval, minN_eval, fig8CtV, lctV, kDecOutV,
            Expr.v0, Expr.v1, Expr.v3, Env.get_cons_zero, Env.get_cons_succ]

theorem kDecryptAtomicE_eval_bool (idA idB : IdentityKey) (B_cap : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (seedE : Expr AOps Γ (B 32)) (ρ : Env Γ)
    (qB : Bool) (w : Bytes) (c' : Fig8C Pt) (seed : Bytes)
    (hq : qBE.eval ρ = qB) (hw : wE.eval ρ = w) (hc' : c'E.eval ρ = fig8CtV c')
    (hseed : seedE.eval ρ = seed) (hseedLen : seed.length = 32) :
    (kDecryptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B_cap qBE wE c'E seedE).eval ρ =
      (simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap qB w c' seed).map kDecOutV :=
  kDecryptAtomicPE_eval_bool (paramsV1 C K idA idB) idA idB B_cap qBE wE c'E seedE ρ
    qB w c' seed rfl rfl rfl rfl hq hw hc' hseed hseedLen

theorem kDecryptAtomicE_eval (idA idB : IdentityKey) (B_cap : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (seedE : Expr AOps Γ (B 32)) (ρ : Env Γ)
    (Q : Party) (w : Bytes) (c' : Fig8C Pt) (seed : Bytes)
    (hq : qBE.eval ρ = partyEnc Q) (hw : wE.eval ρ = w) (hc' : c'E.eval ρ = fig8CtV c')
    (hseed : seedE.eval ρ = seed) (hseedLen : seed.length = 32) :
    (kDecryptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B_cap qBE wE c'E seedE).eval ρ =
      (simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap (partyEnc Q) w c' seed).map kDecOutV :=
  kDecryptAtomicE_eval_bool idA idB B_cap qBE wE c'E seedE ρ (partyEnc Q) w c' seed
    hq hw hc' hseed hseedLen

theorem kDecryptAtomicE_cost (idA idB : IdentityKey) (B_cap : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (seedE : Expr AOps Γ (B 32)) :
    (kDecryptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B_cap qBE wE c'E seedE).cost ≤
      qBE.cost + wE.cost + c'E.cost + seedE.cost +
        10 * (ℓ / 32) + 2 * bits B_cap + 650 := by
  let tB := Ty.prod .bool (.prod (B 32) (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (B 32)))
  let Γlp := wireSaltCtT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  let Γm := Ty.prod BV256 (.prod BV256 (.prod BV128 U32)) ::
    signalParsedT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hlpub := lPubOfExpr_cost ℓ Pt C Dh encPt encT lam
    (.v0 : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γlp _)
  have hab := cost_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm)
    (paramsV1 C K idA idB).addrAB (serializedPartyAddresses_len_le_36 .A .B)
  have hba := cost_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm)
    (paramsV1 C K idA idB).addrBA (serializedPartyAddresses_len_le_36 .B .A)
  unfold kDecryptAtomicE kDecryptAtomicPE
  generalize lPubOfExpr ℓ Pt C Dh encPt encT lam
    (.v0 : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γlp _) = elp at hlpub ⊢
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm)
    (paramsV1 C K idA idB).addrAB = eab at hab ⊢
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm)
    (paramsV1 C K idA idB).addrBA = eba at hba ⊢
  simp only [cost_eLet, liftFig8Expr_cost, cost_idKeyAtomLitE, minN, CryptoGames.SM.leN,
    Expr.cost, cost_sOpPure, cost_sOpSym, AtomicPureOp.cost, AtomicSymOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hlpub ⊢
  omega

theorem kDecryptAtomicE_descBits_le (idA idB : IdentityKey) (B_cap : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (seedE : Expr AOps Γ (B 32)) :
    atomicExprDescBits atomicSessionOpDescBits
      (kDecryptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B_cap qBE wE c'E seedE) ≤
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      atomicExprDescBits atomicSessionOpDescBits c'E +
      atomicExprDescBits atomicSessionOpDescBits seedE +
      4 * bits B_cap + 5200 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod .bool (.prod (B 32) (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (B 32)))
  let Γlp := wireSaltCtT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  let Γm := Ty.prod BV256 (.prod BV256 (.prod BV128 U32)) ::
    signalParsedT (ℓ := ℓ) (Pt := Pt) :: tB :: Γ
  have hlpub := lPubOfExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
    (.v0 : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γlp _)
  have hab := descBits_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm)
    (paramsV1 C K idA idB).addrAB (serializedPartyAddresses_len_le_36 .A .B)
  have hba := descBits_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm)
    (paramsV1 C K idA idB).addrBA (serializedPartyAddresses_len_le_36 .B .A)
  have hidA := idKeyAtomLitE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm) idA
  have hidB := idKeyAtomLitE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm) idB
  unfold kDecryptAtomicE kDecryptAtomicPE
  generalize lPubOfExpr ℓ Pt C Dh encPt encT lam
    (.v0 : Expr (atomicFig8Ops ℓ Pt C Dh encPt encT lam) Γlp _) = elp at hlpub ⊢
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm)
    (paramsV1 C K idA idB).addrAB = eab at hab ⊢
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm)
    (paramsV1 C K idA idB).addrBA = eba at hba ⊢
  generalize idKeyAtomLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm) idA = eia at hidA ⊢
  generalize idKeyAtomLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γm) idB = eib at hidB ⊢
  simp only [descBits_eLet, liftFig8Expr_descBits, descBits_sOpPure, descBits_sOpSym,
    minN, CryptoGames.SM.leN, kDecOutT, lpubT, PlainT, PtT, U32, B, BV256,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    atomicExprDescBits, atomicPureOpDescBits, atomicSymOpDescBits,
    atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd] at hlpub ⊢
  omega

def knownSeedDecryptAtomicC (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Comp AOps I' Γ (.opt (.opt (kDecOutT ℓ Pt))) :=
  .bind (.ret (.pair snapsE (.pair qBE (.pair tE (.pair wE c'E)))))
    (.bind
      (knownSeedBAtomicC I' L Kc
        (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))
      (.ret (.caseOpt .v0 .none
        (.some (kDecryptAtomicE idA idB B_cap
          (.fst (.snd .v2))
          (.fst (.snd (.snd (.snd .v2))))
          (.snd (.snd (.snd (.snd .v2))))
          .v0)))))

theorem knownSeedDecryptAtomicC_eval_snapEnc (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ)
    (w : Bytes) (c' : Fig8C Pt)
    (hsnaps : snapsE.eval ρ = snaps.map snapEnc) (hlen : snaps.length ≤ L)
    (hq : qBE.eval ρ = partyEnc Q) (ht : tE.eval ρ = t)
    (hw : wE.eval ρ = w) (hc' : c'E.eval ρ = fig8CtV c')
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) :
    (knownSeedDecryptAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).eval ρ =
      pure (((SanOracleCore.snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w).map
        (simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap (partyEnc Q) w c')).map
          (Option.map kDecOutV)) := by
  unfold knownSeedDecryptAtomicC
  dsimp only [Comp.eval]
  rw [pure_bind]
  have hsd := knownSeedBAtomicC_eval_snapEnc (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB I' L Kc
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.cons (t := Ty.prod (.list (snapT ℓ Pt))
        (.prod .bool (.prod .nat (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt))))))
      (snapsE.eval ρ, (qBE.eval ρ, (tE.eval ρ, (wE.eval ρ, c'E.eval ρ)))) ρ)
    snaps Q t w hlen hWF
    (by simp [Expr.eval, hsnaps, Expr.v0])
    (by simp [Expr.eval, hq, Expr.v0])
    (by simp [Expr.eval, ht, Expr.v0])
    (by simp [Expr.eval, hw, Expr.v0])
  dsimp only [Expr.eval]
  rw [hsd, pure_bind]
  rcases hopt : SanOracleCore.snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w with
    _ | seed
  · rfl
  · have hlen32 := snapshotMessageKeySeedB_length_32 Kc (paramsV1 C K idA idB) snaps Q t w hWF hopt
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.map]
    rw [kDecryptAtomicE_eval idA idB B_cap _ _ _ _ _ Q w c' seed
      (by simp [Expr.eval, hq, Expr.v2])
      (by simp [Expr.eval, hw, Expr.v2])
      (by simp [Expr.eval, hc', Expr.v2])
      rfl hlen32]
    cases simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap (partyEnc Q) w c' seed <;> rfl

theorem knownSeedDecryptAtomicC_eval (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ)
    (w : Bytes) (c' : Fig8C Pt)
    (hlen : snaps.length ≤ L) (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2)
    (hsnaps : snapsE.eval ρ = snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))))
    (hq : qBE.eval ρ = partyToBool Q) (ht : tE.eval ρ = t)
    (hw : wE.eval ρ = w) (hc' : c'E.eval ρ = fig8CtV c') :
    (knownSeedDecryptAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).eval ρ =
      pure (((SanOracleCore.snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w).map
        (simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap (partyToBool Q) w c')).map
          (Option.map kDecOutV)) := by
  have hmap : snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))) =
      snaps.map (snapEnc (ℓ := ℓ) (Pt := Pt)) := by
    refine List.map_congr_left fun e _ => ?_
    simp [snapEnc, partyToBool_eq_partyEnc]
  rw [partyToBool_eq_partyEnc Q]
  exact knownSeedDecryptAtomicC_eval_snapEnc idA idB L Kc B_cap I' snapsE qBE tE wE c'E ρ
    snaps Q t w c' (hsnaps.trans hmap) hlen (hq.trans (partyToBool_eq_partyEnc Q)) ht hw hc' hWF

@[simp] theorem knownSeedDecryptAtomicC_queries (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (wt : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (knownSeedDecryptAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).queries wt ws = 0 := by
  simp [knownSeedDecryptAtomicC, Comp.queries]

theorem knownSeedDecryptAtomicC_cost_linear (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (knownSeedDecryptAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost + c'E.cost +
        11 * (ℓ / 32) + bits Kc + 2 * bits B_cap +
        30 * Kc + 22200 * L + 2200 := by
  let tB := Ty.prod (.list (snapT ℓ Pt))
    (.prod .bool (.prod .nat (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
  let Γ1 := tB :: Γ
  let Γ3 := B 32 :: Ty.opt (B 32) :: Γ1
  have hsd := knownSeedBAtomicC_cost_tight_linear (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' L Kc (Γ := Γ1)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
  have hkd := kDecryptAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B_cap (Γ := Γ3)
    (.fst (.snd .v2)) (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2)))) .v0
  unfold knownSeedDecryptAtomicC
  generalize knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' L Kc (Γ := Γ1) _ _ _ _ = esd at hsd ⊢
  generalize kDecryptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B_cap (Γ := Γ3) _ _ _ _ = ekd at hkd ⊢
  simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v2] at hsd hkd ⊢
  omega

theorem knownSeedDecryptAtomicC_cost (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (knownSeedDecryptAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost + c'E.cost +
        11 * (ℓ / 32) + bits Kc + 2 * bits B_cap +
        30 * Kc + 420 * (L * L) + 22000 * L + 2200 := by
  refine Nat.le_trans (knownSeedDecryptAtomicC_cost_linear (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E) ?_
  have hL := linear_cost_le_quad_cost L
  generalize snapsE.cost + qBE.cost + tE.cost + wE.cost + c'E.cost +
    11 * (ℓ / 32) + bits Kc + 2 * bits B_cap + 30 * Kc = base
  omega

theorem knownSeedDecryptAtomicC_descBits_le (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (knownSeedDecryptAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E) ≤
      atomicExprDescBits atomicSessionOpDescBits snapsE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      atomicExprDescBits atomicSessionOpDescBits c'E +
      10 * bits L + 4 * bits Kc + 4 * bits B_cap + 16500 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (.list (snapT ℓ Pt))
    (.prod .bool (.prod .nat (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
  let Γ1 := tB :: Γ
  let Γ3 := B 32 :: Ty.opt (B 32) :: Γ1
  have hsd := knownSeedBAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' L Kc sB qB (Γ := Γ1)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
  have hkd := kDecryptAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB B_cap (Γ := Γ3)
    (.fst (.snd .v2)) (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2)))) .v0
  unfold knownSeedDecryptAtomicC
  generalize knownSeedBAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' L Kc (Γ := Γ1) _ _ _ _ = esd at hsd ⊢
  generalize kDecryptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B_cap (Γ := Γ3) _ _ _ _ = ekd at hkd ⊢
  dsimp only [snapT, fig8CtT, fig8HdrT, lctT, wireSaltCtT, kDecOutT, lpubT, PlainT,
    GhostStT, PK, PtT, U32, U64, B, BV256]
  simp only [Expr.v0, Expr.v2,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    varIdx, Nat.reduceAdd] at hsd hkd ⊢
  omega

/-- Linear-cost atomic computation for snapshot seed lookup followed by `simKDecryptFig8`. -/
def knownSeedDecryptAtomicFastC (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Comp AOps I' Γ (.opt (.opt (kDecOutT ℓ Pt))) :=
  .bind (.ret (.pair snapsE (.pair qBE (.pair tE (.pair wE c'E)))))
    (.bind
      (knownSeedBAtomicFastC I' L Kc
        (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))
      (.ret (.caseOpt .v0 .none
        (.some (kDecryptAtomicE idA idB B_cap
          (.fst (.snd .v2))
          (.fst (.snd (.snd (.snd .v2))))
          (.snd (.snd (.snd (.snd .v2))))
          .v0)))))

theorem knownSeedDecryptAtomicFastC_eval_snapEnc_fast (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ)
    (w : Bytes) (c' : Fig8C Pt)
    (hsnaps : snapsE.eval ρ = snaps.map snapEnc) (hlen : snaps.length ≤ L)
    (hq : qBE.eval ρ = partyEnc Q) (ht : tE.eval ρ = t)
    (hw : wE.eval ρ = w) (hc' : c'E.eval ρ = fig8CtV c')
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) :
    (knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).eval ρ =
      pure (((snapshotMessageKeySeedBFast Kc (paramsV1 C K idA idB) snaps Q t w).map
        (simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap (partyEnc Q) w c')).map
          (Option.map kDecOutV)) := by
  unfold knownSeedDecryptAtomicFastC
  dsimp only [Comp.eval]
  rw [pure_bind]
  have hsd := knownSeedBAtomicFastC_eval_snapEnc_fast (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB I' L Kc
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
    (.cons (t := Ty.prod (.list (snapT ℓ Pt))
        (.prod .bool (.prod .nat (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt))))))
      (snapsE.eval ρ, (qBE.eval ρ, (tE.eval ρ, (wE.eval ρ, c'E.eval ρ)))) ρ)
    snaps Q t w hlen hWF
    (by simp [Expr.eval, hsnaps, Expr.v0])
    (by simp [Expr.eval, hq, Expr.v0])
    (by simp [Expr.eval, ht, Expr.v0])
    (by simp [Expr.eval, hw, Expr.v0])
  dsimp only [Expr.eval]
  rw [hsd, pure_bind]
  rcases hopt : snapshotMessageKeySeedBFast Kc (paramsV1 C K idA idB) snaps Q t w with
    _ | seed
  · rfl
  · have hlen32 := snapshotMessageKeySeedBFast_length_32 Kc (paramsV1 C K idA idB) snaps Q t w hWF hopt
    simp only [Expr.eval, Expr.v0, Env.get_cons_zero, Option.map]
    rw [kDecryptAtomicE_eval idA idB B_cap _ _ _ _ _ Q w c' seed
      (by simp [Expr.eval, hq, Expr.v2])
      (by simp [Expr.eval, hw, Expr.v2])
      (by simp [Expr.eval, hc', Expr.v2])
      rfl hlen32]
    cases simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap (partyEnc Q) w c' seed <;> rfl

theorem knownSeedDecryptAtomicFastC_eval_snapEnc (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ)
    (w : Bytes) (c' : Fig8C Pt)
    (hsnaps : snapsE.eval ρ = snaps.map snapEnc) (hlen : snaps.length ≤ L)
    (hq : qBE.eval ρ = partyEnc Q) (ht : tE.eval ρ = t)
    (hw : wE.eval ρ = w) (hc' : c'E.eval ρ = fig8CtV c')
    (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2) :
    (knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).eval ρ =
      pure (((SanOracleCore.snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w).map
        (simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap (partyEnc Q) w c')).map
          (Option.map kDecOutV)) := by
  rw [knownSeedDecryptAtomicFastC_eval_snapEnc_fast idA idB L Kc B_cap I' snapsE qBE tE wE c'E ρ
    snaps Q t w c' hsnaps hlen hq ht hw hc' hWF,
    snapshotMessageKeySeedBFast_eq_snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w]

theorem knownSeedDecryptAtomicFastC_eval_fast (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ)
    (w : Bytes) (c' : Fig8C Pt)
    (hlen : snaps.length ≤ L) (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2)
    (hsnaps : snapsE.eval ρ = snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))))
    (hq : qBE.eval ρ = partyToBool Q) (ht : tE.eval ρ = t)
    (hw : wE.eval ρ = w) (hc' : c'E.eval ρ = fig8CtV c') :
    (knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).eval ρ =
      pure (((snapshotMessageKeySeedBFast Kc (paramsV1 C K idA idB) snaps Q t w).map
        (simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap (partyToBool Q) w c')).map
          (Option.map kDecOutV)) := by
  have hmap : snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))) =
      snaps.map (snapEnc (ℓ := ℓ) (Pt := Pt)) := by
    refine List.map_congr_left fun e _ => ?_
    simp [snapEnc, partyToBool_eq_partyEnc]
  rw [partyToBool_eq_partyEnc Q]
  exact knownSeedDecryptAtomicFastC_eval_snapEnc_fast idA idB L Kc B_cap I' snapsE qBE tE wE c'E ρ
    snaps Q t w c' (hsnaps.trans hmap) hlen (hq.trans (partyToBool_eq_partyEnc Q)) ht hw hc' hWF

theorem knownSeedDecryptAtomicFastC_eval (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (snaps : List (Party × ℕ × GhostState Bytes)) (Q : Party) (t : ℕ)
    (w : Bytes) (c' : Fig8C Pt)
    (hlen : snaps.length ≤ L) (hWF : ∀ e ∈ snaps, SnapWFProd e.2.2)
    (hsnaps : snapsE.eval ρ = snaps.map (fun e => (partyToBool e.1, (e.2.1, e.2.2))))
    (hq : qBE.eval ρ = partyToBool Q) (ht : tE.eval ρ = t)
    (hw : wE.eval ρ = w) (hc' : c'E.eval ρ = fig8CtV c') :
    (knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).eval ρ =
      pure (((SanOracleCore.snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w).map
        (simKDecryptFig8 (paramsV1 C K idA idB) ℓ B_cap (partyToBool Q) w c')).map
          (Option.map kDecOutV)) := by
  rw [knownSeedDecryptAtomicFastC_eval_fast idA idB L Kc B_cap I' snapsE qBE tE wE c'E ρ
    snaps Q t w c' hlen hWF hsnaps hq ht hw hc',
    snapshotMessageKeySeedBFast_eq_snapshotMessageKeySeedB Kc (paramsV1 C K idA idB) snaps Q t w]

@[simp] theorem knownSeedDecryptAtomicFastC_queries (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (wt : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).queries wt ws = 0 := by
  simp [knownSeedDecryptAtomicFastC, Comp.queries]

theorem knownSeedDecryptAtomicFastC_cost (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E).cost ≤
      snapsE.cost + qBE.cost + tE.cost + wE.cost + c'E.cost +
        11 * (ℓ / 32) + bits Kc + 2 * bits B_cap +
        30 * Kc + 22200 * L + 2200 := by
  let tB := Ty.prod (.list (snapT ℓ Pt))
    (.prod .bool (.prod .nat (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
  let Γ1 := tB :: Γ
  let Γ3 := B 32 :: Ty.opt (B 32) :: Γ1
  have hsd := knownSeedBAtomicFastC_cost_tight (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' L Kc (Γ := Γ1)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
  have hkd := kDecryptAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B_cap (Γ := Γ3)
    (.fst (.snd .v2)) (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2)))) .v0
  unfold knownSeedDecryptAtomicFastC
  generalize knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' L Kc (Γ := Γ1) _ _ _ _ = esd at hsd ⊢
  generalize kDecryptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B_cap (Γ := Γ3) _ _ _ _ = ekd at hkd ⊢
  simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v2] at hsd hkd ⊢
  omega

theorem knownSeedDecryptAtomicFastC_descBits_le (idA idB : IdentityKey) (L Kc B_cap : ℕ)
    {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ) {Γ : List (Ty ASig)}
    (snapsE : Expr AOps Γ (.list (snapT ℓ Pt)))
    (qBE : Expr AOps Γ .bool) (tE : Expr AOps Γ .nat) (wE : Expr AOps Γ (B 32))
    (c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (knownSeedDecryptAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB L Kc B_cap I' snapsE qBE tE wE c'E) ≤
      atomicExprDescBits atomicSessionOpDescBits snapsE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits tE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      atomicExprDescBits atomicSessionOpDescBits c'E +
      10 * bits L + 4 * bits Kc + 4 * bits B_cap + 16500 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (.list (snapT ℓ Pt))
    (.prod .bool (.prod .nat (.prod (B 32) (fig8CtT (ℓ := ℓ) (Pt := Pt)))))
  let Γ1 := tB :: Γ
  let Γ3 := B 32 :: Ty.opt (B 32) :: Γ1
  have hsd := knownSeedBAtomicFastC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' L Kc sB qB (Γ := Γ1)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0))))
  have hkd := kDecryptAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B_cap (Γ := Γ3)
    (.fst (.snd .v2)) (.fst (.snd (.snd (.snd .v2)))) (.snd (.snd (.snd (.snd .v2)))) .v0
  unfold knownSeedDecryptAtomicFastC
  generalize knownSeedBAtomicFastC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' L Kc (Γ := Γ1) _ _ _ _ = esd at hsd ⊢
  generalize kDecryptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B_cap (Γ := Γ3) _ _ _ _ = ekd at hkd ⊢
  dsimp only [snapT, fig8CtT, fig8HdrT, lctT, wireSaltCtT, kDecOutT, lpubT, PlainT,
    GhostStT, PK, PtT, U32, U64, B, BV256]
  simp only [Expr.v0, Expr.v2,
    atomicCompDescBits, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    varIdx, Nat.reduceAdd] at hsd hkd ⊢
  omega

end KDecryptAndCombined

/-! ## Wire serialization and curve admissibility -/

theorem toLEBytes8_eq_tagBytes (t : BitVec 64) :
    ReductionDsl.toLEBytes 8 t = tagBytes t := by
  refine List.ext_getElem
    (by simp [ReductionDsl.toLEBytes, tagBytes]) fun j h1 h2 => ?_
  simp only [ReductionDsl.toLEBytes, tagBytes,
    List.getElem_ofFn, List.getElem_map, List.getElem_range]
  rfl

theorem salt32V_inj {s₁ s₂ : List.Vector (BitVec 8) 32} (h : salt32V s₁ = salt32V s₂) :
    s₁ = s₂ := by
  rw [← keyToBytesVec32_salt32V s₁, ← keyToBytesVec32_salt32V s₂, h]

theorem salt32V_beq (s₁ s₂ : List.Vector (BitVec 8) 32) :
    (salt32V s₁ == salt32V s₂) = decide (s₁ = s₂) := by
  by_cases h : s₁ = s₂
  · subst h; simp
  · have hne : salt32V s₁ ≠ salt32V s₂ := fun heq => h (salt32V_inj heq)
    simp [h, beq_eq_false_iff_ne.mpr hne]

section WireAndAdmissibility

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def toWireAtomicE {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ (B 32) :=
  eLet (.fst (.snd (.snd cE)))
    (sOpPure .bytesAppend8 (.pair (.fst .v0) (sOpPure .u64LeBytes (.snd .v0))))

theorem toWireAtomicE_eval {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (c : Fig8C Pt) (hc : cE.eval ρ = fig8CtV c) :
    (toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).eval ρ = toWire c := by
  unfold toWireAtomicE toWire
  rw [eval_eLet]
  have h1 : (Expr.fst (.snd (.snd cE))).eval ρ = c.2.2.1 := by
    simp [Expr.eval, hc, fig8CtV, lctV, wireSaltCtV]
  rw [h1]
  simp only [Expr.eval, eval_sOpPure, AtomicPureOp.eval, Expr.v0, Env.get_cons_zero]
  rw [List.take_of_length_le (Nat.le_of_eq (toLEBytes8_length _)), toLEBytes8_eq_tagBytes]

theorem toWireAtomicE_cost {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE).cost ≤ cE.cost + 20 := by
  unfold toWireAtomicE
  simp only [cost_eLet, Expr.cost, cost_sOpPure, AtomicPureOp.cost, Expr.v0]
  omega

theorem toWireAtomicE_descBits_le {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (toWireAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) cE) ≤
      atomicExprDescBits atomicSessionOpDescBits cE + 120 := by
  have hbits := small_bits_bounds
  simp only [toWireAtomicE, descBits_eLet, atomicExprDescBits, descBits_sOpPure,
    atomicPureOpDescBits, Expr.v0, varIdx]
  omega

def lctSaltEqAtomicE {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (saltE : Expr AOps Γ BV256) : Expr AOps Γ .bool :=
  sOpPure .bv256Eq (.pair (.snd (.snd (.snd cE))) saltE)

theorem lctSaltEqAtomicE_eval {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (saltE : Expr AOps Γ BV256) (ρ : Env Γ)
    (c : Fig8C Pt) (salt : List.Vector (BitVec 8) 32)
    (hc : cE.eval ρ = fig8CtV c) (hsalt : saltE.eval ρ = salt32V salt) :
    (lctSaltEqAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE saltE).eval ρ = decide (c.2.2.2 = salt) := by
  unfold lctSaltEqAtomicE
  simp only [eval_sOpPure, AtomicPureOp.eval, Expr.eval, hc, hsalt,
    fig8CtV, lctV, wireSaltCtV]
  exact salt32V_beq c.2.2.2 salt

theorem lctSaltEqAtomicE_cost {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (saltE : Expr AOps Γ BV256) :
    (lctSaltEqAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE saltE).cost ≤ cE.cost + saltE.cost + 10 := by
  unfold lctSaltEqAtomicE
  simp only [Expr.cost, cost_sOpPure, AtomicPureOp.cost]
  omega

theorem lctSaltEqAtomicE_descBits_le {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (saltE : Expr AOps Γ BV256) :
    atomicExprDescBits atomicSessionOpDescBits
      (lctSaltEqAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) cE saltE) ≤
      atomicExprDescBits atomicSessionOpDescBits cE +
      atomicExprDescBits atomicSessionOpDescBits saltE + 50 := by
  simp only [lctSaltEqAtomicE, atomicExprDescBits, descBits_sOpPure, atomicPureOpDescBits]
  omega

def lctSaltEqOfLctAtomicE {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ .bool :=
  lctSaltEqAtomicE cE (.snd (.snd lctE))

theorem lctSaltEqOfLctAtomicE_eval {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (c : Fig8C Pt) (lct : ℕ × LibsignalCiphertextWithSalt32)
    (hc : cE.eval ρ = fig8CtV c) (hlct : lctE.eval ρ = lctV lct) :
    (lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE lctE).eval ρ = decide (c.2.2.2 = lct.2.2) :=
  lctSaltEqAtomicE_eval cE (.snd (.snd lctE)) ρ c lct.2.2 hc
    (by simp [Expr.eval, hlct, lctV, wireSaltCtV])

theorem lctSaltEqOfLctAtomicE_cost {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    (lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cE lctE).cost ≤ cE.cost + lctE.cost + 15 := by
  have h := lctSaltEqAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) cE (.snd (.snd lctE))
  unfold lctSaltEqOfLctAtomicE
  simp only [Expr.cost] at h
  omega

theorem lctSaltEqOfLctAtomicE_descBits_le {Γ : List (Ty ASig)}
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (lctE : Expr AOps Γ (lctT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits atomicSessionOpDescBits
      (lctSaltEqOfLctAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) cE lctE) ≤
      atomicExprDescBits atomicSessionOpDescBits cE +
      atomicExprDescBits atomicSessionOpDescBits lctE + 70 := by
  have h := lctSaltEqAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) cE (.snd (.snd lctE))
  unfold lctSaltEqOfLctAtomicE
  simp only [atomicExprDescBits] at h
  omega

def injOKAtomicE {Γ : List (Ty ASig)} (wE : Expr AOps Γ (B 32)) : Expr AOps Γ .bool :=
  sOpCurve .checkRatchetKeyOnCurve wE

abbrev ratchetKeyAdmissibleAtomicE {Γ : List (Ty ASig)} (wE : Expr AOps Γ (B 32)) :
    Expr AOps Γ .bool :=
  injOKAtomicE wE

@[simp] theorem injOKAtomicE_eval {Γ : List (Ty ASig)}
    (wE : Expr AOps Γ (B 32)) (ρ : Env Γ) :
    (injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) wE).eval ρ =
      ratchetKeyAdmissible protoSignalCodec decT encT (wE.eval ρ) := rfl

theorem injOKAtomicE_cost {Γ : List (Ty ASig)} (wE : Expr AOps Γ (B 32)) :
    (injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) wE).cost ≤ wE.cost + ℓ / 32 + 24 := by
  unfold injOKAtomicE
  simp only [cost_sOpCurve, atomicCurveCheckOps]
  omega

theorem injOKAtomicE_descBits_le {Γ : List (Ty ASig)} (wE : Expr AOps Γ (B 32)) :
    atomicExprDescBits atomicSessionOpDescBits
      (injOKAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) wE) ≤
      atomicExprDescBits atomicSessionOpDescBits wE + 30 := by
  simp only [injOKAtomicE, descBits_sOpCurve]
  omega

def isZeroPtOptAtomicE {Γ : List (Ty ASig)}
    (tOptE : Expr AOps Γ (.opt PtT)) : Expr AOps Γ .bool :=
  .caseOpt tOptE (.bool false) (sOpGrp .ptIsZero .v0)

theorem isZeroPtOptAtomicE_eval {Γ : List (Ty ASig)}
    (tOptE : Expr AOps Γ (.opt PtT)) (ρ : Env Γ) :
    (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) tOptE).eval ρ = (tOptE.eval ρ == some 0) := by
  unfold isZeroPtOptAtomicE
  rcases h : tOptE.eval ρ with _ | x
  · simp [Expr.eval, h]
  · simp only [Expr.eval, h, eval_sOpGrp, AtomicGroupOp.eval, Expr.v0, Env.get_cons_zero]
    by_cases hx : x = 0 <;> simp [hx]

theorem isZeroPtOptAtomicE_cost {Γ : List (Ty ASig)}
    (tOptE : Expr AOps Γ (.opt PtT)) :
    (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) tOptE).cost ≤ tOptE.cost + 5 := by
  unfold isZeroPtOptAtomicE
  simp only [Expr.cost, cost_sOpGrp, AtomicGroupOp.cost, Expr.v0]
  omega

theorem isZeroPtOptAtomicE_descBits_le {Γ : List (Ty ASig)}
    (tOptE : Expr AOps Γ (.opt PtT)) :
    atomicExprDescBits atomicSessionOpDescBits
      (isZeroPtOptAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) tOptE) ≤
      atomicExprDescBits atomicSessionOpDescBits tOptE + 50 := by
  have hbits := small_bits_bounds
  simp only [isZeroPtOptAtomicE, atomicExprDescBits, descBits_sOpGrp, Expr.v0, varIdx]
  omega

end WireAndAdmissibility

/-! ## SPQR send and receive wrappers -/

theorem spqrSend_panics_guard_eq {β : Type} (F : ShaCompress) (K : MlKem) (pq : Bytes)
    (r : BitVec 512) (f : Bytes × CryptoGames.HKDF.Salt × Bytes → β) :
    (if (spqrV1SessionUniformCoins F K).sendPanics pq r then none
      else ((spqrV1SessionUniformCoins F K).send pq r).map f) =
      ((spqrV1SessionUniformCoins F K).send pq r).map f := by
  by_cases hp : (spqrV1SessionUniformCoins F K).sendPanics pq r = true
  · simp only [hp, ↓reduceIte]
    rcases hs : (spqrV1SessionUniformCoins F K).send pq r with _ | x
    · rfl
    · have h := CryptoVerification.SpqrV1Sync.SendTotal.sendPanics_eq_false_of_isSome F K pq r
        (by rw [hs]; rfl)
      rw [h] at hp; cases hp
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]

theorem salt32V_effectiveHkdfSalt32 (s : CryptoGames.HKDF.Salt) :
    salt32V (effectiveHkdfSalt32 s) =
      (s.map fun v => bytesToKey32 v.toList).getD 0 := by
  rcases s with _ | v <;> rfl

section SpqrSendWrapper

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def effSaltE {Γ : List (Ty ASig)} (s : Expr AOps Γ (.opt BV256)) : Expr AOps Γ BV256 :=
  .caseOpt s (sOpPure (.bv256Lit 0) .unit) .v0

@[simp] theorem effSaltE_eval {Γ : List (Ty ASig)} (s : Expr AOps Γ (.opt BV256)) (ρ : Env Γ) :
    (effSaltE s).eval ρ = (s.eval ρ).getD 0 := by
  unfold effSaltE
  simp only [Expr.eval]
  cases s.eval ρ <;> rfl

theorem effSaltE_cost {Γ : List (Ty ASig)} (s : Expr AOps Γ (.opt BV256)) :
    (effSaltE s).cost ≤ s.cost + 5 := by
  unfold effSaltE
  simp only [Expr.cost, cost_sOpPure, AtomicPureOp.cost, Expr.v0]
  omega

theorem effSaltE_descBits_le {Γ : List (Ty ASig)} (s : Expr AOps Γ (.opt BV256)) :
    atomicExprDescBits atomicSessionOpDescBits (effSaltE (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) s) ≤
      atomicExprDescBits atomicSessionOpDescBits s + 310 := by
  have hbits := small_bits_bounds
  simp only [effSaltE, atomicExprDescBits, descBits_sOpPure, atomicPureOpDescBits, Expr.v0, varIdx]
  omega

def mkPubRawAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32)))))) :
    Comp AOps I' Γ (.opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)))) :=
  .bind (.ret inpE)
    (.bind (spqrSendAtomicC I' (.pair (.fst .v0) (.fst (.snd .v0))))
      (.ret (.caseOpt .v0 .none
        (.some (.pair (.fst .v0)
          (.pair (.fst (.snd (.snd .v2)))
            (.pair (.snd (.snd .v0))
              (.pair (effSaltE (.fst (.snd .v0))) (.snd (.snd (.snd .v2)))))))))))

@[simp] theorem mkPubRawAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32)))))) :
    (mkPubRawAtomicC I' inpE).queries w ws = 0 := by
  simp [mkPubRawAtomicC, Comp.queries, spqrSendAtomicC_queries]

theorem mkPubRawAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32)))))) :
    (mkPubRawAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤ inpE.cost + 2144100 := by
  have h1 := spqrSendAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I'
    (Γ := (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))) :: Γ)
    (.pair (.fst .v0) (.fst (.snd .v0)))
  have h2 := effSaltE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam)
    (Γ := (.prod (B 32) (.prod (.opt BV256) (B 32))) ::
      (.opt (.prod (B 32) (.prod (.opt BV256) (B 32)))) ::
      (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))) :: Γ)
    (.fst (.snd .v0))
  unfold mkPubRawAtomicC
  generalize spqrSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' _ = cs at h1 ⊢
  generalize effSaltE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ = es at h2 ⊢
  simp only [Comp.cost, Expr.cost, Expr.v0, Expr.v2] at h1 h2 ⊢
  omega

theorem mkPubRawAtomicC_descBits_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32)))))) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (mkPubRawAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) I' inpE) ≤
      atomicExprDescBits atomicSessionOpDescBits inpE + 25700 := by
  have hbits := small_bits_bounds
  let t0 := Ty.prod (S := ASig) (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))
  let tRes := Ty.prod (S := ASig) (B 32) (.prod (.opt BV256) (B 32))
  have h1 := spqrSendAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' sB qB (Γ := t0 :: Γ)
    (.pair (.fst .v0) (.fst (.snd .v0)))
  have h2 := effSaltE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (Γ := tRes :: (.opt tRes) :: t0 :: Γ) (.fst (.snd .v0))
  unfold mkPubRawAtomicC
  generalize spqrSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' _ = cs at h1 ⊢
  generalize effSaltE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ = es at h2 ⊢
  simp only [atomicCompDescBits, atomicExprDescBits, B, U32, BV256, BV512,
    atomicTyDescBits, atomicSortDescBits, Expr.v0, Expr.v2, varIdx, Nat.reduceAdd] at h1 h2 ⊢
  omega

theorem mkPubRawAtomicC_eval {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))))
    (ρ : Env Γ) (pq : Bytes) (r : BitVec 512) (pn : BitVec 32) (addr : Option Bytes)
    (hinp : inpE.eval ρ = (pq, (r, (pn, addr)))) (htight : TopStateTight C.F K pq) :
    (mkPubRawAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).eval ρ =
      pure (((spqrV1SessionUniformCoins C.F K).send pq r).map fun x =>
        (x.1, lpubV (ℓ := ℓ) (Pt := Pt) ⟨pn, x.2.2, effectiveHkdfSalt32 x.2.1, addr⟩)) := by
  unfold mkPubRawAtomicC
  simp only [Comp.eval, pure_bind, hinp]
  rw [spqrSendAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' _ _ (by simpa [Expr.eval, Expr.v0] using htight)]
  simp only [Expr.eval, Expr.v0, Env.get, pure_bind]
  rw [spqrSend_panics_guard_eq]
  congr 1
  rcases (spqrV1SessionUniformCoins C.F K).send pq r with _ | ⟨pq', salt, msg⟩
  · rfl
  · simp only [Option.map_some, Expr.eval, effSaltE_eval, lpubV, salt32V_effectiveHkdfSalt32]
    rfl

def mkPubInpE (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sBaseE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (pnE : Expr AOps Γ U32) :
    Expr AOps Γ (.prod (B 32) (.prod BV512 (.prod U32 (.opt (B 32))))) :=
  eLet (.pair sBaseE (.pair qBE (.pair rqE pnE)))
    (let s0 : Expr AOps _ (simBaseT ℓ Pt) := .fst .v0
     let q0 : Expr AOps _ .bool := .fst (.snd .v0)
     let r0 : Expr AOps _ BV512 := .fst (.snd (.snd .v0))
     let pn0 : Expr AOps _ U32 := .snd (.snd (.snd .v0))
     let pqE : Expr AOps _ (B 32) := pGet (ssPq s0) q0
     let addrE : Expr AOps _ (.opt (B 32)) :=
       .ite (.and (.not q0) (ssUnackA s0)) (optBytesLitE (paramsV1 C K idA idB).addrAB) .none
     .pair pqE (.pair r0 (.pair pn0 addrE)))

theorem mkPubInpE_eval (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sBaseE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (pnE : Expr AOps Γ U32) (ρ : Env Γ)
    (sBase : SimState Bytes Pt ℓ) (qB : Bool) (rq : BitVec 512) (pn : BitVec 32)
    (hs : sBaseE.eval ρ = simBaseEnc sBase) (hq : qBE.eval ρ = qB)
    (hr : rqE.eval ρ = rq) (hpn : pnE.eval ρ = pn) :
    (mkPubInpE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB sBaseE qBE rqE pnE).eval ρ =
      (sBase.pq (partyDec qB),
        (rq, (pn, if partyDec qB == Party.A && sBase.unackA
                  then (paramsV1 C K idA idB).addrAB else none))) := by
  have hBA : (Party.B == Party.A) = false := rfl
  unfold mkPubInpE
  rw [eval_eLet]
  have h0 : (Expr.pair sBaseE (.pair qBE (.pair rqE pnE))).eval ρ =
      (simBaseEnc sBase, (qB, (rq, pn))) := by simp [Expr.eval, hs, hq, hr, hpn]
  rw [h0]; clear h0 hs hq hr hpn
  cases qB with
  | false =>
    rcases hun : sBase.unackA with _ | _ <;>
      simp [pGet, ssPq, ssUnackA, simBaseEnc, partyDec, hun, Expr.eval, Expr.v0]
  | true =>
    simp [pGet, ssPq, ssUnackA, simBaseEnc, partyDec, hBA, Expr.eval, Expr.v0]

theorem mkPubInpE_cost (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sBaseE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (pnE : Expr AOps Γ U32) :
    (mkPubInpE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB sBaseE qBE rqE pnE).cost ≤
      sBaseE.cost + qBE.cost + rqE.cost + pnE.cost + 120 := by
  let tB := Ty.prod (simBaseT ℓ Pt) (.prod .bool (.prod BV512 U32))
  have hab := cost_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := tB :: Γ)
    (paramsV1 C K idA idB).addrAB (serializedPartyAddresses_len_le_36 .A .B)
  unfold mkPubInpE
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := tB :: Γ)
    (paramsV1 C K idA idB).addrAB = eab at hab ⊢
  simp only [cost_eLet, pGet, ssPq, ssUnackA, Expr.cost, Expr.v0]
  omega

theorem mkPubInpE_descBits_le (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sBaseE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (pnE : Expr AOps Γ U32) :
    atomicExprDescBits atomicSessionOpDescBits
      (mkPubInpE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB sBaseE qBE rqE pnE) ≤
      atomicExprDescBits atomicSessionOpDescBits sBaseE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits rqE +
      atomicExprDescBits atomicSessionOpDescBits pnE + 750 := by
  have hbits := small_bits_bounds
  let tB := Ty.prod (simBaseT ℓ Pt) (.prod .bool (.prod BV512 U32))
  have hab := descBits_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := tB :: Γ)
    (paramsV1 C K idA idB).addrAB (serializedPartyAddresses_len_le_36 .A .B)
  unfold mkPubInpE
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := tB :: Γ)
    (paramsV1 C K idA idB).addrAB = eab at hab ⊢
  simp only [descBits_eLet, pGet, ssPq, ssUnackA, B, Expr.v0,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx]
  omega

/-- Atomic SPQR send and public header wrapper for `LibsignalSim.mkPub`. -/
def mkPubAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sBaseE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (pnE : Expr AOps Γ U32) :
    Comp AOps I' Γ (.opt (.prod (B 32) (lpubT (ℓ := ℓ) (Pt := Pt)))) :=
  mkPubRawAtomicC I' (mkPubInpE idA idB sBaseE qBE rqE pnE)

theorem mkPubAtomicC_eval {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sBaseE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (pnE : Expr AOps Γ U32) (ρ : Env Γ)
    (sBase : SimState Bytes Pt ℓ) (qB : Bool) (rq : BitVec 512) (pn : BitVec 32)
    (hs : sBaseE.eval ρ = simBaseEnc sBase) (hq : qBE.eval ρ = qB)
    (hr : rqE.eval ρ = rq) (hpn : pnE.eval ρ = pn)
    (htight : TopStateTight C.F K (sBase.pq (partyDec qB))) :
    (mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' idA idB sBaseE qBE rqE pnE).eval ρ =
      pure ((mkPub (P := paramsV1 C K idA idB) sBase (partyDec qB) rq pn).map
        fun (pq', pub) => (pq', lpubV (ℓ := ℓ) (Pt := Pt) pub)) := by
  unfold mkPubAtomicC mkPub
  have hspqr : (paramsV1 C K idA idB).spqr = spqrV1SessionUniformCoins C.F K := rfl
  rw [hspqr]
  rw [mkPubRawAtomicC_eval I' _ ρ _ _ _ _
    (mkPubInpE_eval idA idB sBaseE qBE rqE pnE ρ sBase qB rq pn hs hq hr hpn) htight]
  congr 1
  rcases (spqrV1SessionUniformCoins C.F K).send (sBase.pq (partyDec qB)) rq with
    _ | ⟨pq', salt, msg⟩ <;> rfl

@[simp] theorem mkPubAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ) {Γ : List (Ty ASig)}
    (sBaseE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (pnE : Expr AOps Γ U32) :
    (mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' idA idB sBaseE qBE rqE pnE).queries w ws = 0 :=
  mkPubRawAtomicC_queries I' w ws _

theorem mkPubAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (sBaseE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (pnE : Expr AOps Γ U32) :
    (mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' idA idB sBaseE qBE rqE pnE).cost ≤
      sBaseE.cost + qBE.cost + rqE.cost + pnE.cost + 2144300 := by
  have h1 := mkPubRawAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' (mkPubInpE idA idB sBaseE qBE rqE pnE)
  have h2 := mkPubInpE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB sBaseE qBE rqE pnE
  unfold mkPubAtomicC
  omega

theorem mkPubAtomicC_descBits_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ) {Γ : List (Ty ASig)}
    (sBaseE : Expr AOps Γ (simBaseT ℓ Pt)) (qBE : Expr AOps Γ .bool)
    (rqE : Expr AOps Γ BV512) (pnE : Expr AOps Γ U32) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (mkPubAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) I' idA idB sBaseE qBE rqE pnE) ≤
      atomicExprDescBits atomicSessionOpDescBits sBaseE +
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits rqE +
      atomicExprDescBits atomicSessionOpDescBits pnE + 26600 := by
  have h1 := mkPubRawAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' sB qB (mkPubInpE idA idB sBaseE qBE rqE pnE)
  have h2 := mkPubInpE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB sBaseE qBE rqE pnE
  unfold mkPubAtomicC
  omega

end SpqrSendWrapper

theorem parse_take_eq_tryFrom (w : Bytes) (hw : ¬ w.length < 9) :
    (signalWireCodec protoSignalCodec).parse (w.take (w.length - 8)) =
      match SignalMessage.tryFrom protoSignalCodec w with
      | .ok m => some (m.header, m.ciphertext)
      | .error _ => none := by
  rcases hp : (signalWireCodec protoSignalCodec).parse (w.take (w.length - 8)) with _ | ⟨h, body⟩
  · obtain ⟨e, he⟩ := CryptoGames.LibsignalSM.Proofs.Refinement.tryFrom_isError_of_parse_none
      protoSignalCodec w (Or.inr hp)
    rw [he]
  · rw [CryptoGames.LibsignalSM.Proofs.Refinement.tryFrom_of_parse protoSignalCodec w h body hw hp]
    rfl

section SpqrRecvWrapper

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

@[reducible] def parseOutT (ℓ : ℕ) (Pt : Type) : Ty (atomicSig ℓ Pt) :=
  .prod (B 32) (.prod .nat (.prod PK (.prod (.opt PtT) (lctT (ℓ := ℓ) (Pt := Pt)))))

def parseOutV (x : Bytes × (ℕ × (PublicKey × (Option Pt × (ℕ × LibsignalCiphertextWithSalt32))))) :
    (parseOutT ℓ Pt).denote :=
  (x.1, (x.2.1, (x.2.2.1, (x.2.2.2.1, lctV (ℓ := ℓ) (Pt := Pt) x.2.2.2.2))))

def addrCheckE (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (addrs : Expr AOps Γ (.opt (B 32))) : Expr AOps Γ .bool :=
  eLet (.pair addrs (.ite qBE (optBytesLitE (paramsV1 C K idA idB).addrAB)
      (optBytesLitE (paramsV1 C K idA idB).addrBA)))
    (.caseOpt (.fst .v0) (.bool true)
      (.caseOpt (.snd .v1) (.bool false) (sOpPure (.bytesEq 32 32) (.pair .v1 .v0))))

theorem addrCheckE_eval (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (addrs : Expr AOps Γ (.opt (B 32))) (ρ : Env Γ) :
    (addrCheckE idA idB qBE addrs).eval ρ =
      CryptoGames.LibsignalAead.addressCheckPasses (addrs.eval ρ)
        ((paramsV1 C K idA idB).expectedAddrs (partyDec (qBE.eval ρ))) := by
  unfold addrCheckE
  rcases ha : addrs.eval ρ with _ | a <;> cases hq : qBE.eval ρ <;>
    simp [eval_eLet, Expr.eval, ha, hq, CryptoGames.LibsignalAead.addressCheckPasses,
      Expr.v0, Expr.v1, partyDec, Params.expectedAddrs] <;>
    rcases (paramsV1 C K idA idB).addrAB with _ | e <;>
    rcases (paramsV1 C K idA idB).addrBA with _ | e' <;> rfl

theorem addrCheckE_cost (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (addrs : Expr AOps Γ (.opt (B 32))) :
    (addrCheckE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB qBE addrs).cost ≤ qBE.cost + addrs.cost + 300 := by
  have hab := cost_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
    (paramsV1 C K idA idB).addrAB (serializedPartyAddresses_len_le_36 .A .B)
  have hba := cost_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
    (paramsV1 C K idA idB).addrBA (serializedPartyAddresses_len_le_36 .B .A)
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  unfold addrCheckE
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
    (paramsV1 C K idA idB).addrAB = eab at hab ⊢
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
    (paramsV1 C K idA idB).addrBA = eba at hba ⊢
  simp only [cost_eLet, Expr.cost, cost_sOpPure, AtomicPureOp.cost, hp32, Expr.v0, Expr.v1]
  omega

theorem addrCheckE_descBits_le (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (addrs : Expr AOps Γ (.opt (B 32))) :
    atomicExprDescBits atomicSessionOpDescBits
      (addrCheckE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB qBE addrs) ≤
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits addrs + 900 := by
  have hbits := small_bits_bounds
  have hab := descBits_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
    (paramsV1 C K idA idB).addrAB (serializedPartyAddresses_len_le_36 .A .B)
  have hba := descBits_optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
    (paramsV1 C K idA idB).addrBA (serializedPartyAddresses_len_le_36 .B .A)
  unfold addrCheckE
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
    (paramsV1 C K idA idB).addrAB = eab at hab ⊢
  generalize optBytesLitE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
    (paramsV1 C K idA idB).addrBA = eba at hba ⊢
  simp only [descBits_eLet, atomicExprDescBits, descBits_sOpPure, atomicPureOpDescBits,
    Expr.v0, Expr.v1, varIdx, Nat.reduceAdd]
  omega

def parseBodyE (Bc : ℕ) {Γ : List (Ty ASig)} :
    Expr AOps
      ((.prod (B 32) (.opt BV256)) :: (.opt (.prod (B 32) (.opt BV256))) ::
        (signalParsedT (ℓ := ℓ) (Pt := Pt)) :: (.prod .bool (.prod (B 32) (B 32))) :: Γ)
      (parseOutT ℓ Pt) :=
  let w : Expr AOps _ (B 32) := .snd (.snd .v3)
  let n8 : Expr AOps _ .nat := .sub (sOpPure (.bytesLen 32) w) (.nat 8)
  let ctrN : Expr AOps _ .nat := .add (sOpPure .u32ToNat (.fst (.snd (.snd (.fst .v2))))) (.nat 1)
  let rk : Expr AOps _ PK := .fst (.snd (.fst .v2))
  .pair (.fst .v0)
    (.pair (.ite (.lt ctrN (.nat Bc)) ctrN (.nat Bc))
      (.pair rk
        (.pair (sOpPtDec .ptDecPk rk)
          (.pair ctrN
            (.pair
              (.pair (sOpPure (.bytesTake 32) (.pair n8 w))
                (sOpPure .bytesToU64Le
                  (sOpPure (.bytesTakeK 32 8) (sOpPure (.bytesDrop 32) (.pair n8 w)))))
              (effSaltE (.snd .v0)))))))

theorem parseBodyE_cost (Bc : ℕ) {Γ : List (Ty ASig)} :
    (parseBodyE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ) Bc).cost ≤ 2 * bits Bc + 350 := by
  have hbits := small_bits_bounds
  have hs := effSaltE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam)
    (Γ := (.prod (B 32) (.opt BV256)) :: (.opt (.prod (B 32) (.opt BV256))) ::
      (signalParsedT (ℓ := ℓ) (Pt := Pt)) :: (.prod .bool (.prod (B 32) (B 32))) :: Γ)
    (.snd .v0)
  have hp32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  have hp8 : ((8 : ℕ+) : ℕ) = 8 := rfl
  unfold parseBodyE
  generalize effSaltE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ = es at hs ⊢
  simp only [Expr.cost, cost_sOpPure, cost_sOpPtDec, AtomicPureOp.cost, hp32, hp8,
    Expr.v0, Expr.v2, Expr.v3] at hs ⊢
  omega

theorem parseBodyE_descBits_le (Bc : ℕ) {Γ : List (Ty ASig)} :
    atomicExprDescBits atomicSessionOpDescBits
      (parseBodyE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc) ≤ 4 * bits Bc + 1200 := by
  have hbits := small_bits_bounds
  have hb8p : bits ((8 : ℕ+) : ℕ) = 4 := hbits.2.2.2.2.2.2.2.1
  have hs := effSaltE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam)
    (Γ := (.prod (B 32) (.opt BV256)) :: (.opt (.prod (B 32) (.opt BV256))) ::
      (signalParsedT (ℓ := ℓ) (Pt := Pt)) :: (.prod .bool (.prod (B 32) (B 32))) :: Γ)
    (.snd .v0)
  unfold parseBodyE
  generalize effSaltE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ = es at hs ⊢
  simp only [atomicExprDescBits, descBits_sOpPure, descBits_sOpPtDec, atomicPureOpDescBits,
    Expr.v0, Expr.v2, Expr.v3, varIdx, Nat.reduceAdd, hb8p] at hs ⊢
  omega

def parseRecvRawAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32)))) :
    Comp AOps I' Γ (.opt (parseOutT ℓ Pt)) :=
  .bind (.ret inpE)
    (.ite (.lt (sOpPure (.bytesLen 32) (.snd (.snd .v0))) (.nat 9)) (.ret .none)
      (.caseOpt (sOpPure .signalMsgParse (.snd (.snd .v0))) (.ret .none)
        (.ite (.not (addrCheckE idA idB (.fst .v1) (.snd (.snd (.snd .v0))))) (.ret .none)
          (.bind (spqrRecvAtomicC I' (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v0)))))
            (.ret (.caseOpt .v0 .none (.some (parseBodyE Bc))))))))

@[simp] theorem parseRecvRawAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32)))) :
    (parseRecvRawAtomicC I' idA idB Bc inpE).queries w ws = 0 := by
  simp [parseRecvRawAtomicC, Comp.queries, spqrRecvAtomicC_queries]

theorem parseRecvRawAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32)))) :
    (parseRecvRawAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' idA idB Bc inpE).cost ≤
      inpE.cost + ℓ / 32 + 2 * bits Bc + 131201200 := by
  have hbits := small_bits_bounds
  have hb9 : bits 9 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  let t0 := Ty.prod (S := ASig) .bool (.prod (B 32) (B 32))
  let Γ1 := t0 :: Γ
  let Γ2 := signalParsedT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hac := addrCheckE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (.fst .v1) (.snd (.snd (.snd .v0)))
  have hspqr := spqrRecvAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' (Γ := Γ2) (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v0))))
  have hbody := parseBodyE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc
  unfold parseRecvRawAtomicC
  generalize addrCheckE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) _ _ = eac at hac ⊢
  generalize spqrRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' (Γ := Γ2) _ = cspqr at hspqr ⊢
  generalize parseBodyE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc = ebody at hbody ⊢
  simp only [Comp.cost, Expr.cost, cost_sOpPure, AtomicPureOp.cost, hb9,
    Expr.v0, Expr.v1] at hac hspqr hbody ⊢
  omega

theorem parseRecvRawAtomicC_descBits_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32)))) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (parseRecvRawAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) I' idA idB Bc inpE) ≤
      atomicExprDescBits atomicSessionOpDescBits inpE + 4 * bits Bc + 95000 := by
  have hbits := small_bits_bounds
  have hb9 : bits 9 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  let t0 := Ty.prod (S := ASig) .bool (.prod (B 32) (B 32))
  let Γ1 := t0 :: Γ
  let Γ2 := signalParsedT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hac := addrCheckE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (.fst .v1) (.snd (.snd (.snd .v0)))
  have hspqr := spqrRecvAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' sB qB (Γ := Γ2)
    (.pair (.fst (.snd .v1)) (.fst (.snd (.snd .v0))))
  have hbody := parseBodyE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc
  unfold parseRecvRawAtomicC
  generalize addrCheckE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) _ _ = eac at hac ⊢
  generalize spqrRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' (Γ := Γ2) _ = cspqr at hspqr ⊢
  generalize parseBodyE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) Bc = ebody at hbody ⊢
  simp only [atomicCompDescBits, atomicExprDescBits, descBits_sOpPure, atomicPureOpDescBits,
    parseOutT, lctT, wireSaltCtT, B, U64, BV256, PK, PtT, atomicTyDescBits, atomicSortDescBits,
    Expr.v0, Expr.v1, varIdx, Nat.reduceAdd, hb9] at hac hspqr hbody ⊢
  omega

private theorem ite_lt_eq_min' (a b : ℕ) : (if decide (a < b) = true then a else b) = min a b := by
  by_cases h : a < b
  · simp [h, Nat.min_eq_left (Nat.le_of_lt h)]
  · simp [h, Nat.min_eq_right (Nat.le_of_not_lt h)]

omit [DecidableEq Pt] [Zero Pt] in
private theorem signalMsgParse_eval' (body : Bytes) :
    AtomicPureOp.eval ℓ Pt .signalMsgParse body =
      match SignalMessage.tryFrom protoSignalCodec body with
      | .ok m => some ((m.messageVersion, (m.senderRatchetKey, (m.counter, m.previousCounter))),
          (m.ciphertext, (m.pqRatchet, m.addresses)))
      | .error _ => none :=
  atomicPureOps_eval_signalMsgParse_lossless ℓ Pt body

private theorem tag_take8_eq (w : Bytes) (hw : ¬ w.length < 9) :
    ReductionDsl.bytesToWordLE 64 ((w.drop (w.length - 8)).take 8) =
      bytesToWord64LE (w.drop (w.length - 8)) := by
  rw [List.take_of_length_le (by simp; omega)]
  rfl

theorem parseRecvRawAtomicC_eval {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) {Γ : List (Ty ASig)}
    (inpE : Expr AOps Γ (.prod .bool (.prod (B 32) (B 32)))) (ρ : Env Γ)
    (qB : Bool) (pq w : Bytes) (hinp : inpE.eval ρ = (qB, (pq, w)))
    (htight : TopStateTight C.F K pq) :
    (parseRecvRawAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' idA idB Bc inpE).eval ρ =
      pure ((simParseRecvC (paramsV1 C K idA idB) decT Bc qB pq w).map
        (parseOutV (ℓ := ℓ) (Pt := Pt))) := by
  unfold parseRecvRawAtomicC simParseRecvC
  simp only [Comp.eval, pure_bind, hinp, Expr.eval, Expr.v0, Env.get, eval_sOpPure]
  have hlenEval : AtomicPureOp.eval ℓ Pt (.bytesLen 32) w = w.length := rfl
  rw [hlenEval]
  by_cases hlen : w.length < 9
  · simp [hlen]
  · simp only [hlen, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hcodec : (paramsV1 C K idA idB).codec = protoSignalCodec := rfl
    rw [hcodec, parse_take_eq_tryFrom w hlen, signalMsgParse_eval']
    rcases htry : SignalMessage.tryFrom protoSignalCodec w with _ | m
    · rfl
    · simp only [addrCheckE_eval, Expr.eval, Expr.v1, Env.get, SignalMessage.header]
      by_cases haddr : CryptoGames.LibsignalAead.addressCheckPasses m.addresses
          ((paramsV1 C K idA idB).expectedAddrs (partyDec qB)) = true
      · simp only [haddr, Bool.not_true, Bool.false_eq_true, Bool.false_or, ↓reduceIte]
        rw [spqrRecvAtomicC_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) I' _ _ (by simpa [Expr.eval, Expr.v0, Expr.v1] using htight)]
        simp only [Expr.eval, Env.get, pure_bind]
        have hspqrEq : (paramsV1 C K idA idB).spqr = spqrV1SessionUniformCoins C.F K := rfl
        rw [hspqrEq]
        by_cases hp : (spqrV1SessionUniformCoins C.F K).recvPanics pq m.pqRatchet = true
        · simp [hp]
        · simp only [hp, Bool.false_eq_true, ↓reduceIte]
          rcases hrec : (spqrV1SessionUniformCoins C.F K).recv pq m.pqRatchet with
            _ | ⟨pq', salt⟩
          · rfl
          · simp only [Option.map_some, parseBodyE, parseOutV, lctV, wireSaltCtV,
              Expr.eval, eval_sOpPure, eval_sOpPtDec, effSaltE_eval,
              Expr.v0, Expr.v2, Expr.v3, Env.get]
            congr 2
            change (pq',
              ((if decide (m.counter.toNat + 1 < Bc) = true then m.counter.toNat + 1 else Bc),
                (m.senderRatchetKey, (decT m.senderRatchetKey, (m.counter.toNat + 1,
                  ((w.take (w.length - 8),
                    ReductionDsl.bytesToWordLE 64 ((w.drop (w.length - 8)).take 8)),
                  (salt.map fun v => bytesToKey32 v.toList).getD 0)))))) = _
            rw [ite_lt_eq_min', tag_take8_eq w hlen, ← salt32V_effectiveHkdfSalt32]
      · simp [haddr]

/-- Atomic computation for `simParseRecvC`. -/
def parseRecvAtomicC {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pqE : Expr AOps Γ (B 32)) (wE : Expr AOps Γ (B 32)) :
    Comp AOps I' Γ (.opt (parseOutT ℓ Pt)) :=
  parseRecvRawAtomicC I' idA idB Bc (.pair qBE (.pair pqE wE))

theorem parseRecvAtomicC_eval {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pqE : Expr AOps Γ (B 32)) (wE : Expr AOps Γ (B 32))
    (ρ : Env Γ) (qB : Bool) (pq w : Bytes)
    (hq : qBE.eval ρ = qB) (hpq : pqE.eval ρ = pq) (hw : wE.eval ρ = w)
    (htight : TopStateTight C.F K pq) :
    (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' idA idB Bc qBE pqE wE).eval ρ =
      pure ((simParseRecvC (paramsV1 C K idA idB) decT Bc qB pq w).map
        (parseOutV (ℓ := ℓ) (Pt := Pt))) :=
  parseRecvRawAtomicC_eval I' idA idB Bc _ ρ qB pq w (by simp [Expr.eval, hq, hpq, hw]) htight

@[simp] theorem parseRecvAtomicC_queries {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) (w : I'.Tag → ℕ) (ws : I'.smp.Samp → ℕ)
    {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pqE : Expr AOps Γ (B 32)) (wE : Expr AOps Γ (B 32)) :
    (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' idA idB Bc qBE pqE wE).queries w ws = 0 :=
  parseRecvRawAtomicC_queries I' idA idB Bc w ws _

theorem parseRecvAtomicC_cost {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pqE : Expr AOps Γ (B 32)) (wE : Expr AOps Γ (B 32)) :
    (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' idA idB Bc qBE pqE wE).cost ≤
      qBE.cost + pqE.cost + wE.cost + ℓ / 32 + 2 * bits Bc + 131201210 := by
  have h := parseRecvRawAtomicC_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) I' idA idB Bc (.pair qBE (.pair pqE wE))
  unfold parseRecvAtomicC
  simp only [Expr.cost] at h
  omega

theorem parseRecvAtomicC_descBits_le {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    (idA idB : IdentityKey) (Bc : ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty ASig)}
    (qBE : Expr AOps Γ .bool) (pqE : Expr AOps Γ (B 32)) (wE : Expr AOps Γ (B 32)) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (parseRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) I' idA idB Bc qBE pqE wE) ≤
      atomicExprDescBits atomicSessionOpDescBits qBE +
      atomicExprDescBits atomicSessionOpDescBits pqE +
      atomicExprDescBits atomicSessionOpDescBits wE +
      4 * bits Bc + 95050 := by
  have h := parseRecvRawAtomicC_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) I' idA idB Bc sB qB (.pair qBE (.pair pqE wE))
  unfold parseRecvAtomicC
  simp only [atomicExprDescBits] at h
  omega

end SpqrRecvWrapper

end Computational.Proofs.Game.PromotedCostedReds.SimFig8Crypto
