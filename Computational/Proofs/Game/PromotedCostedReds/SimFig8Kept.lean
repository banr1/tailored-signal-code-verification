/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
public import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc

/-!
# Atomic Figure 8 Party Operations and `Kept` Invariants

Defines the party invariants (`Fig8CkaInv`, `SkippedLenLe`, `Fig8PartyInv`, `KeptInv`), atomic
`ReductionDsl` expressions for Figure 8 party operations, read-time sanitizers, and `Kept` /
`sentEval` helpers, with evaluation, cost, and description-bit bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits bits_mono lt_two_pow_bits
  atomicSig atomicSessionOps B U32 U64 BV128 BV256 BV512 PK IdKey PlainT PtT
  AtomicPureOp AtomicSymOp AtomicGroupOp
  partyToBool boolToParty
  salt32V salt32OfV lpubT lpubV lpubOfV wireSaltCtT wireSaltCtV wireSaltCtOfV lctT lctV lctOfV
  fig8HdrT fsSendStT fsSendStV fsSendStOfV fsRecvStT fsRecvStV fsRecvStOfV
  ckaStT ckaStV ckaStOfV fig8CtT fig8CtV fig8CtOfV fig8StT fig8StV fig8StOfV
  smRrT smRrEnc smRrDec coinOnlyIface)
open CryptoGames (Party effectiveHkdfSalt32)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState skipKeys fromAEADPRG)
open CryptoGames.Ratchet (RootKey rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (Salt32 LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  dummyKey lPubOf lChainPRG lAead lFS lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C SimFig8St SimFig8C KemExtraRaw kemFailSemHook
  fig8Clamp fsClampSim)
open CryptoGames.Ratchet.LibsignalSimC (Kept sentEval)
open CryptoGames.SM (Pos Record GameState RecvResult partyEnc partyDec posTy posEnc posDec
  posSender posEpoch posIdx posEq orE boolEq maxN minN isSomeE otherE sendsInE pGet pSet
  ite_eval orE_eval boolEq_eval maxN_eval minN_eval isSomeE_eval
  otherE_eval sendsInE_eval pGet_eval pSet_eval posEq_eval)
open CryptoGames.SM.Construction (Header PartyState initParty)
open CryptoGames.LibsignalSession (Crypto ShaCompress IdentityKey PublicKey maxForwardJumps)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes toU8 paramsV1)
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB fsAtomic fsAtomicB
  fsAtomic_receive_eq fsAtomicB_send_eq fsAtomicB_receive_eq skipKeys_length
  dhSchemeFb dhSchemeFb_initA_eq dhSchemeFb_initB_eq dhSchemeFb_send_pub dhSchemeFb_receive_exp
  pkLitExpr optBytesEqExpr optPtEqExpr lPubOfExpr chainGenExpr aeadEncExpr aeadDecExpr
  appAux unitsPowExpr
  fsInitSendExpr fsInitSendExpr_eval fsInitSendExpr_cost
  fsInitRecvExpr fsInitRecvExpr_eval fsInitRecvExpr_cost
  fsSendExpr fsSendExpr_eval fsSendExpr_cost
  fsRecvExpr fsRecvExpr_eval fsRecvExpr_cost
  ckaInitAExpr ckaInitAExpr_eval ckaInitAExpr_cost
  ckaInitBExpr ckaInitBExpr_eval ckaInitBExpr_cost
  ckaSendExpr ckaSendExpr_eval ckaSendExpr_cost
  ckaRecvExpr ckaRecvExpr_eval ckaRecvExpr_cost
  prngInitExpr prngUpExpr prngUpExpr_eval prngUpExpr_cost
  lamIExpr lamIExpr_eval lamIExpr_cost
  defaultEExpr defaultEExpr_eval defaultEExpr_cost
  eqPtExpr lctEqBody lctEqBody_eval lctEqBody_cost
  smEqCtExpr smEqCtExpr_eval smEqCtExpr_cost)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (sanRS sanGamma sanAt fig8San fsSan figS fsS fig8StTruncSkB)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost
  (keptT keptEnc keptDec sentEntryT sentEntryEnc keyToBytes32_bytesToKey32)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (eLet eval_eLet cost_eLet descBits_eLet
   sOpPure eval_sOpPure cost_sOpPure descBits_sOpPure
   sOpSym eval_sOpSym cost_sOpSym descBits_sOpSym
   sOpGrp eval_sOpGrp cost_sOpGrp descBits_sOpGrp
   liftFig8Expr liftFig8Expr_cost liftFig8Expr_eval liftFig8Expr_descBits
   runFig8WithIds cost_runFig8WithIds eval_runFig8WithIds descBits_runFig8WithIds
   atomicFig8OpDescBits rename_descBits_eq bits_eq_of_bounds bits_le_of_lt_pow bits_zero
   atomicTyDescBits_posTy atomicTyDescBits_fig8CtT atomicTyDescBits_fsSendStT
   atomicTyDescBits_fsRecvStT atomicTyDescBits_fig8StT atomicTyDescBits_keptT
   atomicTyDescBits_sentEntryT)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits atomicSymOpDescBits
   atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc
  (lamIExpr_descBits_le prngUpExpr_descBits_le ckaInitAExpr_descBits_le
   ckaSendExpr_descBits_le ckaRecvExpr_descBits_le defaultEExpr_descBits_le
   fsSendExpr_descBits_le fsRecvExpr_descBits_le)

/-! ## Party invariants -/

section PartyInvariants

/-- Ping-pong CKA state invariant on `Fig8St Pt` (`.pub` before sending epochs, `.exp` before receiving epochs). -/
def Fig8CkaInv {Pt : Type} (st : Fig8St Pt) : Prop :=
  if st.id.sendsIn (st.tcur + 1) then ∃ h, st.γ = .pub h else ∃ x, st.γ = .exp x

/-- Bounds `v.skippedKeys.length` by `B0` so `fsAtomicB` agrees with `lFS`. -/
def SkippedLenLe (B0 : ℕ) (v : RatchetReceiverState (BitVec 256) (BitVec 256)) : Prop :=
  v.skippedKeys.length ≤ B0

theorem SkippedLenLe.mono {B0 B0' : ℕ} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hle : B0 ≤ B0') (hv : SkippedLenLe B0 v) : SkippedLenLe B0' v :=
  Nat.le_trans hv hle

/-- Combined `Fig8CkaInv` and `SkippedLenLe B0` invariant on `Fig8St Pt`. -/
def Fig8PartyInv {Pt : Type} (B0 : ℕ) (st : Fig8St Pt) : Prop :=
  Fig8CkaInv st ∧ ∀ t v, st.vR t = some v → SkippedLenLe B0 v

theorem Fig8PartyInv.mono {Pt : Type} {B0 B0' : ℕ} {st : Fig8St Pt}
    (hle : B0 ≤ B0') (hst : Fig8PartyInv B0 st) : Fig8PartyInv B0' st :=
  ⟨hst.1, fun t v hv => (hst.2 t v hv).mono hle⟩

/-- Combined `Fig8PartyInv B0` and `SkippedLenLe B0` invariant on `Kept Pt`. -/
def KeptInv {Pt : Type} (B0 : ℕ) (k : Kept Pt) : Prop :=
  (∀ st, k.full = some st → Fig8PartyInv B0 st) ∧
  (∀ t v, k.rs t = some v → SkippedLenLe B0 v)

theorem KeptInv.mono {Pt : Type} {B0 B0' : ℕ} {k : Kept Pt}
    (hle : B0 ≤ B0') (hk : KeptInv B0 k) : KeptInv B0' k :=
  ⟨fun st hst => (hk.1 st hst).mono hle, fun t v hv => (hk.2 t v hv).mono hle⟩

private theorem sendsIn_succ_eq_not (p : Party) (t : ℕ) :
    p.sendsIn (t + 1) = !(p.sendsIn t) := by
  by_cases h : t % 2 = 1
  · have h1 : (t + 1) % 2 = 0 := by omega
    cases p <;> simp only [Party.sendsIn, h, h1] <;> rfl
  · have h0 : t % 2 = 0 := by omega
    have h1 : (t + 1) % 2 = 1 := by omega
    cases p <;> simp only [Party.sendsIn, h0, h1] <;> rfl

theorem skippedLenLe_of_lFS_receive {Pt : Type} {C : Crypto} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {B0 : ℕ}
    {v v' : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {a : Header Pt} {c : ℕ × LibsignalCiphertextWithSalt32}
    {i : ℕ} {m : LibsignalMsgPublicPart × Plain ℓ}
    (hv : SkippedLenLe B0 v)
    (hrec : (lFS C protoSignalCodec ℓ encT idOf 25000).receive v a c = some (v', i, m)) :
    SkippedLenLe (B0 + 25000) v' := by
  rcases c with ⟨idx, wsc⟩
  dsimp only [lFS, fromAEADPRG, CryptoGames.AEADScheme.movePubPartToAD] at hrec
  rcases hlk : v.skippedKeys.lookup idx with _ | key
  · rw [hlk] at hrec
    split_ifs at hrec with hbad
    have hnot : ¬ idx ≤ v.lastIndex ∧ ¬ 25000 < idx - v.lastIndex - 1 := not_or.mp hbad
    rcases hpub : lPubOf protoSignalCodec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec
      dsimp only at hrec
      rcases hdec : (lAead C protoSignalCodec ℓ encT idOf).dec
          ((lChainPRG C.F (idx - 1)).gen
            (skipKeys (lChainPRG C.F) (idx - v.lastIndex - 1)
              v.chainKey v.lastIndex v.skippedKeys).1).2
          ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl⟩
        unfold SkippedLenLe at hv ⊢
        dsimp only
        rw [skipKeys_length]
        omega
  · rw [hlk] at hrec
    dsimp only at hrec
    rcases hpub : lPubOf protoSignalCodec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec
      dsimp only at hrec
      rcases hdec : (lAead C protoSignalCodec ℓ encT idOf).dec key ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl⟩
        unfold SkippedLenLe at hv ⊢
        exact Nat.le_trans (List.length_filter_le _ _) (by omega)

theorem fig8PartyInv_init {Pt : Type} [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (P : Party) (k : BitVec 256 × BitVec 256) :
    Fig8PartyInv 0
      (initParty (dhScheme Dh) (rootPRNG C.F encPt) (lFS C protoSignalCodec ℓ encT idOf 25000)
        lam P k) := by
  refine ⟨?_, ?_⟩
  · cases P <;> simp [Fig8CkaInv, initParty, Party.sendsIn, dhScheme]
  · intro t v hv
    cases P
    · simp only [initParty] at hv
      split_ifs at hv with ht
      · simp only [Option.some.injEq] at hv; subst hv
        simp [SkippedLenLe, lFS, fromAEADPRG]
    · simp [initParty] at hv

theorem fig8PartyInv_initA {Pt : Type} [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (k : BitVec 256 × BitVec 256) :
    Fig8PartyInv 0 ((lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam).initA k) :=
  fig8PartyInv_init Dh encPt C ℓ encT idOf lam .A k

theorem fig8PartyInv_initB {Pt : Type} [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (k : BitVec 256 × BitVec 256) :
    Fig8PartyInv 0 ((lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam).initB k) :=
  fig8PartyInv_init Dh encPt C ℓ encT idOf lam .B k

theorem fig8PartyInv_send {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {st : Fig8St Pt} (hst : Fig8PartyInv B0 st)
    (m : LibsignalMsgPublicPart × Plain ℓ) (r : BitVec 256) :
    Fig8PartyInv B0
      ((lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam).send st m r).1 := by
  rcases hst with ⟨hcka, hvr⟩
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.send]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · unfold Fig8CkaInv at hcka
    simp only [hs, ↓reduceIte] at hcka
    rcases hcka with ⟨h, hγ⟩
    simp only [hs, ↓reduceIte, hγ, dhScheme]
    have hs2 : st.id.sendsIn (st.tcur + 1 + 1) = false := by
      rw [sendsIn_succ_eq_not, hs]; rfl
    refine ⟨?_, hvr⟩
    simp [Fig8CkaInv, hs2]
  · have hs0 : st.id.sendsIn (st.tcur + 1) = false := Bool.eq_false_iff.mpr hs
    simp only [hs0, Bool.false_eq_true, ↓reduceIte]
    cases st.vS <;> exact ⟨hcka, hvr⟩

theorem fig8PartyInv_receive {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {st st' : Fig8St Pt} {c : Fig8C Pt} {t i : ℕ}
    {m : LibsignalMsgPublicPart × Plain ℓ}
    (hst : Fig8PartyInv B0 st)
    (hrec : (lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam).receive st c =
      some (st', t, i, m)) :
    Fig8PartyInv (B0 + 25000) st' := by
  rcases hst with ⟨hcka, hvr⟩
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.receive] at hrec
  by_cases hbad : (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) = true
  · simp [hbad] at hrec
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hrec
    have hbad' : st.id.sendsIn c.1.1 = false ∧ ¬ st.tcur + 1 < c.1.1 := by
      simpa [Bool.or_eq_true] using hbad
    by_cases heq : c.1.1 = st.tcur + 1
    · simp only [heq, ↓reduceIte] at hrec
      rcases hc2 : c.1.2 with _ | Tn
      · rw [hc2] at hrec; cases hrec
      · rw [hc2] at hrec
        unfold Fig8CkaInv at hcka
        have hs0 : st.id.sendsIn (st.tcur + 1) = false := by rw [← heq]; exact hbad'.1
        simp only [hs0, Bool.false_eq_true, ↓reduceIte] at hcka
        rcases hcka with ⟨x, hγ⟩
        simp only [hγ, dhScheme, Function.update_self] at hrec
        rcases hfs : (lFS C protoSignalCodec ℓ encT idOf 25000).receive
            ((lFS C protoSignalCodec ℓ encT idOf 25000).initReceiver
              ((rootPRNG C.F encPt).up st.root (Dh.dh x Tn)).2)
            c.1 c.2 with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          have hs2 : st.id.sendsIn (st.tcur + 1 + 1) = true := by
            rw [sendsIn_succ_eq_not, hs0]; rfl
          refine ⟨by simp [Fig8CkaInv, hs2], ?_⟩
          intro t' v0 hv0
          dsimp only at hv0
          by_cases ht' : t' = st.tcur + 1
          · subst ht'
            simp only [Function.update_self, Option.some.injEq] at hv0; subst hv0
            have hinit : SkippedLenLe B0
                ((lFS C protoSignalCodec ℓ encT idOf 25000).initReceiver
                  ((rootPRNG C.F encPt).up st.root (Dh.dh x Tn)).2) := by
              simp [SkippedLenLe, lFS, fromAEADPRG]
            exact skippedLenLe_of_lFS_receive hinit hfs
          · simp only [Function.update_of_ne ht'] at hv0
            exact (hvr t' v0 hv0).mono (by omega)
    · simp only [heq, ↓reduceIte] at hrec
      rcases hvt : st.vR c.1.1 with _ | v
      · rw [hvt] at hrec; cases hrec
      · rw [hvt] at hrec
        dsimp only at hrec
        rcases hfs : (lFS C protoSignalCodec ℓ encT idOf 25000).receive v c.1 c.2
            with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨hcka, ?_⟩
          intro t' v0 hv0
          dsimp only at hv0
          by_cases ht' : t' = c.1.1
          · subst ht'
            simp only [Function.update_self, Option.some.injEq] at hv0; subst hv0
            exact skippedLenLe_of_lFS_receive (hvr c.1.1 v hvt) hfs
          · simp only [Function.update_of_ne ht'] at hv0
            exact (hvr t' v0 hv0).mono (by omega)

theorem keptInv_unknown {Pt : Type} (B0 : ℕ) : KeptInv B0 (Kept.unknown (Pt := Pt)) :=
  ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem keptInv_ofSt {Pt : Type} {B0 : ℕ} {st : Fig8St Pt} (hst : Fig8PartyInv B0 st) :
    KeptInv B0 (Kept.ofSt st) :=
  ⟨fun _ h => Option.some.inj h ▸ hst, hst.2⟩

theorem keptInv_send {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {k : Kept Pt} (hk : KeptInv B0 k) :
    KeptInv B0
      (Kept.send (ℓ := ℓ) (fig := lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam) k) := by
  unfold Kept.send
  rcases hfull : k.full with _ | st
  · exact hk
  · dsimp only
    have hst := hk.1 st hfull
    split_ifs with hs
    · exact ⟨fun _ h => (nomatch h), hst.2⟩
    · exact ⟨fun _ h => Option.some.inj h ▸ fig8PartyInv_send hst _ _, hk.2⟩

theorem keptInv_recv {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {c : Fig8C Pt} {k : Kept Pt} (hk : KeptInv B0 k) :
    KeptInv (B0 + 25000)
      (Kept.recv (fig := lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam)
        (fs := lFS C protoSignalCodec ℓ encT idOf 25000) c k) := by
  unfold Kept.recv
  rcases hfull : k.full with _ | st
  · dsimp only
    refine ⟨fun _ h => (nomatch h), ?_⟩
    intro t' v0 hv0
    dsimp only at hv0
    by_cases ht' : t' = c.1.1
    · subst ht'
      simp only [Function.update_self] at hv0
      rcases hrs : k.rs c.1.1 with _ | v
      · simp [hrs] at hv0
      · rw [hrs] at hv0
        dsimp only [Option.bind] at hv0
        rcases hfs : (lFS C protoSignalCodec ℓ encT idOf 25000).receive v c.1 c.2
            with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hv0; cases hv0
        · simp only [hfs, Option.map_some, Option.some.injEq] at hv0; subst hv0
          exact skippedLenLe_of_lFS_receive (hk.2 c.1.1 v hrs) hfs
    · simp only [Function.update_of_ne ht'] at hv0
      exact (hk.2 t' v0 hv0).mono (by omega)
  · dsimp only
    have hst := hk.1 st hfull
    rcases hrec : (lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam).receive st c
        with _ | ⟨st', t, i, pm⟩
    · dsimp only
      exact ⟨fun _ h => (nomatch h), fun t' v hv => (hst.2 t' v hv).mono (by omega)⟩
    · dsimp only
      exact ⟨fun _ h => Option.some.inj h ▸ fig8PartyInv_receive hst hrec,
        fun t' v hv => (hk.2 t' v hv).mono (by omega)⟩

end PartyInvariants

/-! ## Atomic Figure 8 party operations -/

section Fig8AtomicOps

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam

def opPure {Γ : List (Ty ASig)} (o : AtomicPureOp) (a : Expr AOps Γ (o.dom ℓ Pt)) :
    Expr AOps Γ (o.cod ℓ Pt) := sOpPure o a

def opSym {Γ : List (Ty ASig)} (o : AtomicSymOp) (a : Expr AOps Γ (o.dom ℓ Pt)) :
    Expr AOps Γ (o.cod ℓ Pt) := sOpSym o a

def opGroup {Γ : List (Ty ASig)} (o : AtomicGroupOp) (a : Expr AOps Γ (o.dom ℓ Pt)) :
    Expr AOps Γ (o.cod ℓ Pt) := sOpGrp o a

@[simp] theorem eval_opPure {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (opPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt (a.eval ρ) := rfl

@[simp] theorem cost_opPure {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (opPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem descBits_opPure {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (opPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      atomicPureOpDescBits o + 4 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

@[simp] theorem eval_opSym {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (opSym (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C (a.eval ρ) := rfl

@[simp] theorem cost_opSym {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (opSym (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := rfl

@[simp] theorem descBits_opSym {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (opSym (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      atomicSymOpDescBits o + 5 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

@[simp] theorem eval_opGroup {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) (ρ : Env Γ) :
    (opGroup (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).eval ρ = o.eval ℓ Pt C Dh encPt lam (a.eval ρ) := rfl

@[simp] theorem cost_opGroup {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    (opGroup (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost := rfl

@[simp] theorem descBits_opGroup {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr AOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits atomicSessionOpDescBits
      (opGroup (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      11 + atomicExprDescBits atomicSessionOpDescBits a + 6 := rfl

def f8Id {O' : Ops ASig} {Γ} (st : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) : Expr O' Γ .bool :=
  .fst st
def f8Root {O' : Ops ASig} {Γ} (st : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) : Expr O' Γ BV256 :=
  .fst (.snd st)
def f8VS {O' : Ops ASig} {Γ} (st : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (.opt (fsSendStT (ℓ := ℓ) (Pt := Pt))) :=
  .fst (.snd (.snd st))
def f8VR {O' : Ops ASig} {Γ} (st : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (.tbl (.opt (fsRecvStT (ℓ := ℓ) (Pt := Pt)))) :=
  .fst (.snd (.snd (.snd st)))
def f8Gamma {O' : Ops ASig} {Γ} (st : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (ckaStT (ℓ := ℓ) (Pt := Pt)) :=
  .fst (.snd (.snd (.snd (.snd st))))
def f8Cur {O' : Ops ASig} {Γ} (st : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (.opt PtT) :=
  .fst (.snd (.snd (.snd (.snd (.snd st)))))
def f8Tcur {O' : Ops ASig} {Γ} (st : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) : Expr O' Γ .nat :=
  .snd (.snd (.snd (.snd (.snd (.snd st)))))

def f8Mk {O' : Ops ASig} {Γ}
    (idE : Expr O' Γ .bool) (rootE : Expr O' Γ BV256)
    (vsE : Expr O' Γ (.opt (fsSendStT (ℓ := ℓ) (Pt := Pt))))
    (vrE : Expr O' Γ (.tbl (.opt (fsRecvStT (ℓ := ℓ) (Pt := Pt)))))
    (gammaE : Expr O' Γ (ckaStT (ℓ := ℓ) (Pt := Pt)))
    (curE : Expr O' Γ (.opt PtT)) (tcurE : Expr O' Γ .nat) :
    Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt)) :=
  .pair idE (.pair rootE (.pair vsE (.pair vrE (.pair gammaE (.pair curE tcurE)))))

private theorem partyToBool_eq_partyEnc (p : Party) : partyToBool p = partyEnc p := by
  cases p <;> rfl

def optPtEqAtomicE {Γ : List (Ty ASig)} (a b : Expr AOps Γ (.opt PtT)) : Expr AOps Γ .bool :=
  eLet (.pair a b)
    (.caseOpt (.fst .v0)
      (.caseOpt (.snd .v0) (.bool true) (.bool false))
      (.caseOpt (.snd .v1) (.bool false)
        (opGroup (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .ptEq (.pair .v1 .v0))))

def sameWireFig8AtomicE {Γ : List (Ty ASig)}
    (c1 c2 : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ .bool :=
  eLet (.pair c1 c2)
    (let x : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .fst .v0
     let y : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .snd .v0
     .and (.eqN (.fst (.fst x)) (.fst (.fst y)))
       (.and (optPtEqAtomicE (.snd (.fst x)) (.snd (.fst y)))
         (.and (.eqN (.fst (.snd x)) (.fst (.snd y)))
           (.and
             (opPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) (.bytesEq 32 32)
               (.pair (.fst (.fst (.snd (.snd x)))) (.fst (.fst (.snd (.snd y))))))
             (opPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
               (decT := decT) (lam := lam) .u64Eq
               (.pair (.snd (.fst (.snd (.snd x)))) (.snd (.fst (.snd (.snd y))))))))))

def eqFig8CAtomicE {Γ : List (Ty ASig)}
    (c1 c2 : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) : Expr AOps Γ .bool :=
  eLet (.pair c1 c2)
    (let x : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .fst .v0
     let y : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .snd .v0
     .and (sameWireFig8AtomicE x y)
       (opPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
         (decT := decT) (lam := lam) .bv256Eq
         (.pair (.snd (.snd (.snd x))) (.snd (.snd (.snd y))))))

def senderToFreshVrAtomicE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (vE : Expr O' Γ (fsSendStT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt)) :=
  eLet vE (.pair (.fst .v0) (.pair (.snd .v0) .nil))

def defaultMcAtomicE {Γ : List (Ty ASig)} :
    Expr AOps Γ (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256) :=
  .pair
    (.pair
      (.pair (opPure (.u32Lit 0#32) .unit)
        (.pair (opPure (.bytesLit 32 []) .unit)
          (.pair (opPure (.bv256Lit (salt32V (effectiveHkdfSalt32 none))) .unit) .none)))
      (opPure .plainDefault .unit))
    (opPure (.bv256Lit 0#256) .unit)

def fig8InitAtomicE (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (k12E : Expr AOps Γ (.prod BV256 BV256)) :
    Expr AOps Γ (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StT (ℓ := ℓ) (Pt := Pt))) :=
  eLet k12E
    (eLet
      (runFig8WithIds idA idB (prngUpExpr ℓ Pt C Dh encPt encT lam)
        (.pair (.fst .v0) (runFig8WithIds idA idB (lamIExpr ℓ Pt C Dh encPt encT lam) .unit)))
      (let out : Expr AOps _ (.prod BV256 BV256) := .v0
       let kc : Expr AOps _ BV256 := .snd .v1
       let stA := f8Mk (.bool false) (.fst out) .none
         (.tset (.tconst .none) (.nat 0) (.some (.pair (.snd out) (.pair (.nat 0) .nil))))
         (runFig8WithIds idA idB (ckaInitAExpr ℓ Pt C Dh encPt encT lam) kc) .none (.nat 0)
       let stB := f8Mk (.bool true) (.fst out)
         (.some (.pair (.snd out) (.nat 0))) (.tconst .none) (.inr kc) .none (.nat 0)
       .pair stA stB))

def fig8SendStepAtomicE (idA idB : IdentityKey) (B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (mcOptE : Expr AOps Γ (.opt (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256))) :
    Expr AOps Γ
      (.prod .bool (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))) :=
  eLet (.pair stE (.caseOpt mcOptE defaultMcAtomicE .v0))
    (let st0 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .fst .v0
     let m0 : Expr AOps _ (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) := .fst (.snd .v0)
     let r0 : Expr AOps _ BV256 := .snd (.snd .v0)
     let sendsNext : Expr AOps _ .bool := sendsInE (f8Id st0) (.add (f8Tcur st0) (.nat 1))
     let s1E : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) :=
       .ite sendsNext
         (eLet (runFig8WithIds idA idB (ckaSendExpr ℓ Pt C Dh encPt encT lam)
             (.pair (f8Gamma st0) r0))
           (eLet (runFig8WithIds idA idB (prngUpExpr ℓ Pt C Dh encPt encT lam)
               (.pair (f8Root (.fst .v1)) (.snd (.snd .v0))))
             (let stOuter : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .fst .v2
              let cOut : Expr AOps _ (.prod ckaStT (.prod PtT PtT)) := .v1
              let pOut : Expr AOps _ (.prod BV256 BV256) := .v0
              f8Mk (f8Id stOuter) (.fst pOut) (.some (.pair (.snd pOut) (.nat 0)))
                (f8VR stOuter) (.fst cOut) (.some (.fst (.snd cOut)))
                (.add (f8Tcur stOuter) (.nat 1)))))
         st0
     eLet (.pair sendsNext (.pair s1E m0))
       (let sn1 : Expr AOps _ .bool := .fst .v0
        let s1 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd .v0)
        let hdrClamped : Expr AOps _ (fig8HdrT (ℓ := ℓ) (Pt := Pt)) :=
          .pair (.ite (.lt (f8Tcur s1) (.nat B)) (f8Tcur s1) (.nat B)) (f8Cur s1)
        .pair sn1
          (.caseOpt (f8VS s1)
            (.pair s1 (.pair hdrClamped
              (runFig8WithIds idA idB (defaultEExpr ℓ Pt C Dh encPt encT lam) .unit)))
            (eLet
              (runFig8WithIds idA idB (fsSendExpr ℓ Pt C Dh encPt encT lam)
                (.pair .v0
                  (.pair (.pair (f8Tcur (.fst (.snd .v1))) (f8Cur (.fst (.snd .v1))))
                    (.snd (.snd .v1)))))
              (let s1Inner : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .fst (.snd .v2)
               let out : Expr AOps _ (.prod fsSendStT lctT) := .v0
               let tc := f8Tcur s1Inner
               .pair
                 (f8Mk (f8Id s1Inner) (f8Root s1Inner) (.some (.fst out))
                   (f8VR s1Inner) (f8Gamma s1Inner) (f8Cur s1Inner) tc)
                 (.pair (.pair (.ite (.lt tc (.nat B)) tc (.nat B)) (f8Cur s1Inner))
                   (.snd out)))))))

def fsReceiveAtomicE (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (vE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ
      (.opt (.prod (fsRecvStT (ℓ := ℓ) (Pt := Pt))
        (.prod .nat (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT)))) :=
  runFig8WithIds idA idB (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B) (.pair vE cE)

def fig8ReceiveAtomicE (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ
      (.opt (.prod (fig8StT (ℓ := ℓ) (Pt := Pt))
        (.prod .nat (.prod .nat (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT))))) :=
  eLet (.pair stE cE)
    (let st0 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .fst .v0
     let c0 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .snd .v0
     let t0 : Expr AOps _ .nat := .fst (.fst c0)
     .ite (orE (sendsInE (f8Id st0) t0) (.lt (.add (f8Tcur st0) (.nat 1)) t0))
       .none
       (let s1Opt : Expr AOps _ (.opt (fig8StT (ℓ := ℓ) (Pt := Pt))) :=
          .ite (.eqN t0 (.add (f8Tcur st0) (.nat 1)))
            (.caseOpt (.snd (.fst c0))
              .none
              (eLet (runFig8WithIds idA idB (ckaRecvExpr ℓ Pt C Dh encPt encT lam)
                  (.pair (f8Gamma (.fst .v1)) .v0))
                (eLet (runFig8WithIds idA idB (prngUpExpr ℓ Pt C Dh encPt encT lam)
                    (.pair (f8Root (.fst .v2)) (.snd .v0)))
                  (let stOuter : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .fst .v3
                   let tOuter : Expr AOps _ .nat := .fst (.fst (.snd .v3))
                   let kOut : Expr AOps _ (.prod ckaStT PtT) := .v1
                   let pOut : Expr AOps _ (.prod BV256 BV256) := .v0
                   .some
                     (f8Mk (f8Id stOuter) (.fst pOut) (f8VS stOuter)
                       (.tset (f8VR stOuter) tOuter
                         (.some (.pair (.snd pOut) (.pair (.nat 0) .nil))))
                       (.fst kOut) (f8Cur stOuter) tOuter)))))
            (.some st0)
        .caseOpt s1Opt
          .none
          (let s1 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .v0
           let c1 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .snd .v1
           let t1 : Expr AOps _ .nat := .fst (.fst c1)
           .caseOpt (.tget (f8VR s1) t1)
             .none
             (.caseOpt (fsReceiveAtomicE idA idB B0 B .v0 (.snd .v2))
               .none
               (let s1Inner : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .v2
                let tInner : Expr AOps _ .nat := .fst (.fst (.snd .v3))
                let res : Expr AOps _ (.prod fsRecvStT (.prod .nat (.prod lpubT PlainT))) := .v0
                .some
                  (.pair
                    (f8Mk (f8Id s1Inner) (f8Root s1Inner) (f8VS s1Inner)
                      (.tset (f8VR s1Inner) tInner (.some (.fst res)))
                      (f8Gamma s1Inner) (f8Cur s1Inner) (f8Tcur s1Inner))
                    (.pair (.ite (.lt tInner (.nat B)) tInner (.nat B)) (.snd res))))))))

@[simp] theorem optPtEqAtomicE_eval {Γ : List (Ty ASig)} (a b : Expr AOps Γ (.opt PtT)) (ρ : Env Γ) :
    (optPtEqAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) a b).eval ρ = decide (a.eval ρ = b.eval ρ) := by
  dsimp only [optPtEqAtomicE, eval_eLet, Expr.eval, Expr.v0, Expr.v1]
  rcases a.eval ρ with _ | x <;> rcases b.eval ρ with _ | y
  · rfl
  · rfl
  · rfl
  · simp only [eval_opGroup, AtomicGroupOp.eval, Expr.eval,
      Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq]
    exact beq_eq_decide x y

theorem optPtEqAtomicE_cost {Γ : List (Ty ASig)} (a b : Expr AOps Γ (.opt PtT)) :
    (optPtEqAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) a b).cost ≤ a.cost + b.cost + 20 := by
  simp only [optPtEqAtomicE, cost_eLet, cost_opGroup, AtomicGroupOp.cost, Expr.cost,
    Expr.v0, Expr.v1]
  omega

theorem sameWireFig8AtomicE_eval {Γ : List (Ty ASig)}
    (c1 c2 : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) (x y : Fig8C Pt)
    (hx : c1.eval ρ = fig8CtV x) (hy : c2.eval ρ = fig8CtV y) :
    (sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c1 c2).eval ρ =
      decide (x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1) := by
  rcases x with ⟨⟨t1, T1⟩, i1, ⟨ser1, tag1⟩, s1⟩
  rcases y with ⟨⟨t2, T2⟩, i2, ⟨ser2, tag2⟩, s2⟩
  dsimp only [sameWireFig8AtomicE]
  rw [eval_eLet]
  have hp : (Expr.pair c1 c2).eval ρ = (fig8CtV ((t1, T1), i1, (ser1, tag1), s1),
      fig8CtV ((t2, T2), i2, (ser2, tag2), s2)) := by simp [Expr.eval, hx, hy]
  rw [hp]
  simp only [fig8CtV, lctV, wireSaltCtV, Expr.eval, optPtEqAtomicE_eval, eval_opPure,
    AtomicPureOp.eval, Expr.v0, Env.get_cons_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨h1, of_decide_eq_true h2⟩, h3, h4, h5⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩; exact ⟨h1, decide_eq_true h2, h3, h4, h5⟩

theorem sameWireFig8AtomicE_cost {Γ : List (Ty ASig)}
    (c1 c2 : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c1 c2).cost ≤ c1.cost + c2.cost + (ℓ / 16 + 180) := by
  let Γ1 := .prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  have hopt := optPtEqAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) (.snd (.fst (.fst .v0))) (.snd (.fst (.snd .v0)))
  simp only [Expr.cost, Expr.v0] at hopt
  simp only [sameWireFig8AtomicE, cost_eLet, cost_opPure, AtomicPureOp.cost, Expr.cost,
    Expr.v0, PNat.val_ofNat]
  omega

theorem eqFig8CAtomicE_eval {Γ : List (Ty ASig)}
    (c1 c2 : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) (x y : Fig8C Pt)
    (hx : c1.eval ρ = fig8CtV x) (hy : c2.eval ρ = fig8CtV y) :
    (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c1 c2).eval ρ = decide (x = y) := by
  rcases x with ⟨⟨t1, T1⟩, i1, ⟨ser1, tag1⟩, s1⟩
  rcases y with ⟨⟨t2, T2⟩, i2, ⟨ser2, tag2⟩, s2⟩
  have hs_iff : salt32V s1 = salt32V s2 ↔ s1 = s2 := by
    constructor
    · intro h
      rcases s1 with ⟨xs1, h1⟩; rcases s2 with ⟨xs2, h2⟩
      apply List.Vector.eq
      have h' := congrArg CryptoGames.HMAC.keyToBytes32 h
      simpa [salt32V,
        keyToBytes32_bytesToKey32 xs1 h1,
        keyToBytes32_bytesToKey32 xs2 h2]
        using h'
    · intro h; exact h ▸ rfl
  dsimp only [eqFig8CAtomicE]
  rw [eval_eLet]
  have hp : (Expr.pair c1 c2).eval ρ = (fig8CtV ((t1, T1), i1, (ser1, tag1), s1),
      fig8CtV ((t2, T2), i2, (ser2, tag2), s2)) := by simp [Expr.eval, hx, hy]
  rw [hp]
  let ρ1 := Env.cons (t := .prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (fig8CtV (ℓ := ℓ) (Pt := Pt) ((t1, T1), i1, (ser1, tag1), s1),
     fig8CtV (ℓ := ℓ) (Pt := Pt) ((t2, T2), i2, (ser2, tag2), s2)) ρ
  have hsw := sameWireFig8AtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.fst .v0) (.snd .v0) ρ1
    ((t1, T1), i1, (ser1, tag1), s1) ((t2, T2), i2, (ser2, tag2), s2) rfl rfl
  change ((sameWireFig8AtomicE (.fst .v0) (.snd .v0)).eval ρ1 &&
    (opPure .bv256Eq (.pair (.snd (.snd (.snd (.fst .v0))))
      (.snd (.snd (.snd (.snd .v0)))))).eval ρ1) = _
  rw [hsw]
  simp only [ρ1, fig8CtV, lctV, wireSaltCtV, eval_opPure, AtomicPureOp.eval, Expr.eval,
    Expr.v0, Env.get_cons_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Prod.mk.injEq, hs_iff]
  tauto

theorem eqFig8CAtomicE_cost {Γ : List (Ty ASig)}
    (c1 c2 : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c1 c2).cost ≤ c1.cost + c2.cost + (ℓ / 16 + 210) := by
  let Γ1 := .prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  have hsw := sameWireFig8AtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.snd .v0)
  simp only [Expr.cost, Expr.v0] at hsw
  simp only [eqFig8CAtomicE, cost_eLet, cost_opPure, AtomicPureOp.cost, Expr.cost, Expr.v0]
  omega

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem senderToFreshVrAtomicE_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (vE : Expr O' Γ (fsSendStT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (u : RatchetSenderState (BitVec 256)) (hv : vE.eval ρ = fsSendStV u) :
    (senderToFreshVrAtomicE vE).eval ρ = fsRecvStV ⟨u.chainKey, u.lastIndex, []⟩ := by
  simp [senderToFreshVrAtomicE, eval_eLet, hv, fsSendStV, fsRecvStV, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
theorem senderToFreshVrAtomicE_cost {O' : Ops ASig} {Γ : List (Ty ASig)}
    (vE : Expr O' Γ (fsSendStT (ℓ := ℓ) (Pt := Pt))) :
    (senderToFreshVrAtomicE vE).cost ≤ vE.cost + 10 := by
  simp only [senderToFreshVrAtomicE, cost_eLet, Expr.cost, Expr.v0]; omega

@[simp] theorem defaultMcAtomicE_eval {Γ : List (Ty ASig)} (ρ : Env Γ) :
    (defaultMcAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam)).eval ρ =
      ((lpubV ⟨0, [], effectiveHkdfSalt32 none, none⟩, (default : Plain ℓ)), (0 : BitVec 256)) := by
  simp only [defaultMcAtomicE, eval_opPure, AtomicPureOp.eval, lpubV, Expr.eval]
  have hdef : (List.Vector.replicate ℓ 0#8 : Plain ℓ) = default := by
    refine List.Vector.ext fun i => ?_
    change (List.Vector.replicate ℓ 0#8).get i = (List.Vector.ofFn default).get i
    rw [List.Vector.get_replicate, List.Vector.get_ofFn]
    rfl
  rw [hdef]
  rfl

theorem defaultMcAtomicE_cost {Γ : List (Ty ASig)} :
    (defaultMcAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)).cost ≤ ℓ / 32 + 50 := by
  simp only [defaultMcAtomicE, cost_opPure, AtomicPureOp.cost, Expr.cost, List.length_nil,
    PNat.val_ofNat]
  omega

theorem fig8InitAtomicE_eval (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (k12E : Expr AOps Γ (.prod BV256 BV256)) (ρ : Env Γ) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then idA else idB
    let fig := lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam
    (fig8InitAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB k12E).eval ρ =
      (fig8StV (fig.initA (k12E.eval ρ)), fig8StV (fig.initB (k12E.eval ρ))) := by
  intro idOf fig
  have hidA : idOf .A = idA := rfl
  have hidB : idOf .B = idB := rfl
  rcases hk : k12E.eval ρ with ⟨kr, kc⟩
  dsimp only [fig8InitAtomicE]
  rw [eval_eLet, hk]
  let ρ1 := Env.cons (t := .prod (BV256 (ℓ := ℓ) (Pt := Pt)) BV256) (kr, kc) ρ
  have hlam : (runFig8WithIds (K := K) (decT := decT) idA idB
      (lamIExpr ℓ Pt C Dh encPt encT lam) .unit).eval ρ1 = lam := by
    rw [eval_runFig8WithIds, ← hidA, ← hidB, lamIExpr_eval]
  have hup : (runFig8WithIds (K := K) (decT := decT) idA idB
      (prngUpExpr ℓ Pt C Dh encPt encT lam)
      (.pair (.fst .v0) (runFig8WithIds idA idB (lamIExpr ℓ Pt C Dh encPt encT lam) .unit))).eval
      ρ1 = (rootPRNG C.F encPt).up kr lam := by
    rw [eval_runFig8WithIds]
    change (prngUpExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons (kr, (runFig8WithIds idA idB (lamIExpr ℓ Pt C Dh encPt encT lam) .unit).eval ρ1)
        (.cons (idOf .A, idOf .B) .nil)) = _
    rw [hlam, prngUpExpr_eval]
  rw [eval_eLet, hup]
  let out := (rootPRNG C.F encPt).up kr lam
  let ρ2 := Env.cons (t := .prod (BV256 (ℓ := ℓ) (Pt := Pt)) BV256) out ρ1
  have hcka : (runFig8WithIds (K := K) (decT := decT) idA idB
      (ckaInitAExpr ℓ Pt C Dh encPt encT lam) (.snd .v1)).eval ρ2 =
      ckaStV ((dhScheme Dh).initA kc) := by
    rw [eval_runFig8WithIds]
    change (ckaInitAExpr ℓ Pt C Dh encPt encT lam).eval
      (.cons kc (.cons (idOf .A, idOf .B) .nil)) = _
    rw [ckaInitAExpr_eval, dhSchemeFb_initA_eq]
  dsimp only [f8Mk, Expr.eval]
  rw [hcka]
  dsimp only [ρ2, ρ1, out, fig, lFig8, CryptoGames.SM.Construction.scheme, initParty, rootPRNG,
    lFS, fromAEADPRG, dhScheme, fig8StV, partyToBool, fsSendStV, fsRecvStV, ckaStV,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  congr 1
  · congr 1; congr 1; congr 1; congr 1
    funext k
    by_cases hk0 : k = 0
    · subst hk0; rfl
    · simp [hk0]

theorem fig8InitAtomicE_cost (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (k12E : Expr AOps Γ (.prod BV256 BV256)) :
    (fig8InitAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB k12E).cost ≤ k12E.cost + 1000 := by
  let Γ1 := .prod (BV256 (ℓ := ℓ) (Pt := Pt)) BV256 :: Γ
  let Γ2 := .prod (BV256 (ℓ := ℓ) (Pt := Pt)) BV256 :: Γ1
  have hlam := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (lamIExpr ℓ Pt C Dh encPt encT lam) .unit
  have hup := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    (.pair (.fst .v0) (runFig8WithIds idA idB (lamIExpr ℓ Pt C Dh encPt encT lam) .unit))
  have hcka := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (ckaInitAExpr ℓ Pt C Dh encPt encT lam) (.snd .v1)
  have hc_lam := lamIExpr_cost ℓ Pt C Dh encPt encT lam
  have hc_up := prngUpExpr_cost ℓ Pt C Dh encPt encT lam
  have hc_cka := ckaInitAExpr_cost ℓ Pt C Dh encPt encT lam
  have hb0 : bits 0 = 1 := bits_zero
  dsimp only [Expr.cost, Expr.v0, Expr.v1] at hlam hup hcka
  dsimp only [fig8InitAtomicE, f8Mk, cost_eLet, Expr.cost, Expr.v0, Expr.v1]
  simp only [hb0]
  generalize (runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (lamIExpr ℓ Pt C Dh encPt encT lam)
    .unit).cost = c_lam at hlam hup ⊢
  generalize (runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    _).cost = c_up at hup ⊢
  generalize (runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (ckaInitAExpr ℓ Pt C Dh encPt encT lam)
    _).cost = c_cka at hcka ⊢
  omega

theorem fsReceiveAtomicE_eval (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (vE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (v : RatchetReceiverState (BitVec 256) (BitVec 256)) (c : Fig8C Pt)
    (hvE : vE.eval ρ = fsRecvStV v) (hcE : cE.eval ρ = fig8CtV c)
    (hsk : SkippedLenLe B0 v) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then idA else idB
    (fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B0 B vE cE).eval ρ =
      (((fsClampSim B (lFS C protoSignalCodec ℓ encT idOf 25000)).receive v c.1 c.2).map
        fun (v', idx, p, m) => (fsRecvStV v', (idx, (lpubV p, m)))) := by
  intro idOf
  have hidA : idOf .A = idA := rfl
  have hidB : idOf .B = idB := rfl
  dsimp only [fsReceiveAtomicE]
  rw [eval_runFig8WithIds]
  have hp : (Expr.pair vE cE).eval ρ = (fsRecvStV v, (c.1, lctV c.2)) := by
    simp [Expr.eval, hvE, hcE, fig8CtV]
  rw [hp, ← hidA, ← hidB, fsRecvExpr_eval, fsAtomicB_receive_eq C ℓ encT idOf B0 v c.1 c.2 hsk]
  dsimp only [fsClampSim, maxForwardJumps]
  rcases (lFS C protoSignalCodec ℓ encT idOf 25000).receive v c.1 c.2 with _ | ⟨v', idx, p, m⟩ <;>
    rfl

theorem fsReceiveAtomicE_cost (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (vE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B0 B vE cE).cost ≤
      vE.cost + cE.cost + 20 * B0 + 3 * bits B + 16 * (ℓ / 32) + 220030000 := by
  have hr := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B) (.pair vE cE)
  have hf := fsRecvExpr_cost ℓ Pt C Dh encPt encT lam B0 B
  simp only [fsReceiveAtomicE, Expr.cost] at hr ⊢
  omega

private theorem ite_lt_eq_min (a B : ℕ) : (if decide (a < B) = true then a else B) = min a B := by
  by_cases h : a < B <;> simp [h, Nat.min_def] <;> omega

theorem fig8SendStepAtomicE_eval_core (idA idB : IdentityKey) (B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (mcOptE : Expr AOps Γ (.opt (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256)))
    (ρ : Env Γ) (st : Fig8St Pt)
    (mc? : Option ((LibsignalMsgPublicPart × Plain ℓ) × BitVec 256))
    (hstE : stE.eval ρ = fig8StV st)
    (hmcE : mcOptE.eval ρ = mc?.map (fun ((p, m), r) => ((lpubV p, m), r)))
    (hcka : st.id.sendsIn (st.tcur + 1) = true → ∃ h, st.γ = .pub h)
    (hshort : ∀ x ∈ mc?, atomicShortPubB x.1.1 = true) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then idA else idB
    let fig := lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam
    let (m, coins) := mc?.getD ((⟨0, [], effectiveHkdfSalt32 none, none⟩, default), 0)
    let (st', c) := (fig8Clamp B fig).send st m coins
    (fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B stE mcOptE).eval ρ =
      (st.id.sendsIn (st.tcur + 1), (fig8StV st', fig8CtV c)) := by
  intro idOf fig
  have hidA : idOf .A = idA := rfl
  have hidB : idOf .B = idB := rfl
  set mc := mc?.getD ((⟨0, [], effectiveHkdfSalt32 none, none⟩, default), 0)
  have hmc_eval : (Expr.caseOpt mcOptE defaultMcAtomicE .v0).eval ρ =
      ((lpubV mc.1.1, mc.1.2), mc.2) := by
    rcases mc? with _ | ⟨⟨p, m⟩, r⟩ <;> simp [hmcE, mc, Expr.eval, Expr.v0]
  have hmc_short : atomicShortPubB mc.1.1 = true := by
    rcases mc? with _ | ⟨⟨p, m⟩, r⟩
    · simp [mc, atomicShortPubB]
    · exact hshort _ rfl
  dsimp only [fig8SendStepAtomicE]
  rw [eval_eLet]
  have hp0 : (Expr.pair stE (.caseOpt mcOptE defaultMcAtomicE .v0)).eval ρ =
      (fig8StV st, ((lpubV mc.1.1, mc.1.2), mc.2)) := by
    change (stE.eval ρ, (Expr.caseOpt mcOptE defaultMcAtomicE .v0).eval ρ) = _
    rw [hstE, hmc_eval]
  rw [hp0]
  let ρ1 := Env.cons
    (t := .prod (fig8StT (ℓ := ℓ) (Pt := Pt))
      (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256))
    (fig8StV (ℓ := ℓ) (Pt := Pt) st, ((lpubV mc.1.1, mc.1.2), mc.2)) ρ
  have hsn : (sendsInE (f8Id (.fst .v0)) (.add (f8Tcur (.fst .v0)) (.nat 1)) :
      Expr AOps _ .bool).eval ρ1 = st.id.sendsIn (st.tcur + 1) := by
    rw [sendsInE_eval _ _ _ st.id
      (by simp [ρ1, f8Id, fig8StV, partyToBool_eq_partyEnc, Expr.eval, Expr.v0])]
    simp [ρ1, f8Tcur, fig8StV, Expr.eval, Expr.v0]
  set s1 : Fig8St Pt :=
    if st.id.sendsIn (st.tcur + 1) = true then
      { id := st.id
        root := ((rootPRNG C.F encPt).up st.root ((dhScheme Dh).send st.γ mc.2).2.2).1
        vS := some ((lFS C protoSignalCodec ℓ encT idOf 25000).initSender
          ((rootPRNG C.F encPt).up st.root ((dhScheme Dh).send st.γ mc.2).2.2).2)
        vR := st.vR
        γ := ((dhScheme Dh).send st.γ mc.2).1
        curCkaMsg := some ((dhScheme Dh).send st.γ mc.2).2.1
        tcur := st.tcur + 1 }
    else st with hs1def
  set s1E : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) :=
    Expr.ite (sendsInE (f8Id (.fst .v0)) (.add (f8Tcur (.fst .v0)) (.nat 1)))
      (eLet (runFig8WithIds idA idB (ckaSendExpr ℓ Pt C Dh encPt encT lam)
          (.pair (f8Gamma (.fst .v0)) (.snd (.snd .v0))))
        (eLet (runFig8WithIds idA idB (prngUpExpr ℓ Pt C Dh encPt encT lam)
            (.pair (f8Root (.fst .v1)) (.snd (.snd .v0))))
          (f8Mk (f8Id (.fst .v2)) (.fst .v0) (.some (.pair (.snd .v0) (.nat 0)))
            (f8VR (.fst .v2)) (.fst .v1) (.some (.fst (.snd .v1)))
            (.add (f8Tcur (.fst .v2)) (.nat 1)))))
      (.fst .v0) with hs1E
  have hs1 : s1E.eval ρ1 = fig8StV s1 := by
    rw [hs1E]
    rw [ite_eval, hsn]
    by_cases hs : st.id.sendsIn (st.tcur + 1) = true
    · rcases hcka hs with ⟨hpt, hγ⟩
      simp only [hs, ↓reduceIte, s1, eval_eLet, eval_runFig8WithIds]
      let cOut := (ckaSendExpr ℓ Pt C Dh encPt encT lam).eval
        (.cons (ckaStV st.γ, mc.2) (.cons (idOf .A, idOf .B) .nil))
      let pOut := (prngUpExpr ℓ Pt C Dh encPt encT lam).eval
        (.cons (st.root, cOut.2.2) (.cons (idOf .A, idOf .B) .nil))
      change (partyToBool st.id, (pOut.1, (some (pOut.2, 0),
        (fun t => (st.vR t).map fsRecvStV, (cOut.1, (some cOut.2.1, st.tcur + 1)))))) = _
      dsimp only [cOut, pOut]
      rw [ckaSendExpr_eval, hγ, dhSchemeFb_send_pub, prngUpExpr_eval]
      rfl
    · have hs0 : st.id.sendsIn (st.tcur + 1) = false := Bool.eq_false_iff.mpr hs
      simp [hs0, s1, ρ1, Expr.eval, Expr.v0]
  rw [eval_eLet]
  have hp1 : (Expr.pair (O := AOps) (sendsInE (f8Id (.fst .v0)) (.add (f8Tcur (.fst .v0)) (.nat 1)))
      (.pair s1E (.fst (.snd .v0)))).eval ρ1 =
      (st.id.sendsIn (st.tcur + 1), (fig8StV s1, (lpubV mc.1.1, mc.1.2))) := by
    simp only [Expr.eval, hsn, hs1]
    rfl
  rw [hp1]
  let ρ2 := Env.cons
    (t := .prod .bool (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT)))
    (st.id.sendsIn (st.tcur + 1), (fig8StV (ℓ := ℓ) (Pt := Pt) s1, (lpubV mc.1.1, mc.1.2))) ρ1
  dsimp only [fig8Clamp, fig, lFig8, CryptoGames.SM.Construction.scheme,
    CryptoGames.SM.Construction.send]
  rw [← hs1def]
  refine Prod.ext rfl ?_
  rcases hvs : s1.vS with _ | vs
  · have hf8vs : (f8VS (O' := AOps) (.fst (.snd .v0))).eval ρ2 =
        (none : (@Ty.opt ASig fsSendStT).denote) := by
      simp [ρ2, f8VS, fig8StV, hvs, Expr.eval, Expr.v0]
    dsimp only [Expr.eval]
    rw [hf8vs]
    dsimp only [ρ2]
    simp only [f8Tcur, f8Cur, fig8StV, fig8CtV, eval_runFig8WithIds, Expr.eval, Expr.v0,
      Env.get_cons_zero]
    rw [← hidA, ← hidB, defaultEExpr_eval, ite_lt_eq_min]
  · have hf8vs : (f8VS (O' := AOps) (.fst (.snd .v0))).eval ρ2 = some (fsSendStV vs) := by
      simp [ρ2, f8VS, fig8StV, hvs, Expr.eval, Expr.v0]
    dsimp only [Expr.eval]
    rw [hf8vs]
    dsimp only [eval_eLet]
    rw [eval_runFig8WithIds]
    have harg : (Expr.pair (O := AOps) .v0 (.pair (.pair (f8Tcur (.fst (.snd .v1))) (f8Cur (.fst (.snd .v1))))
        (.snd (.snd .v1)))).eval (.cons (fsSendStV vs) ρ2) =
        (fsSendStV vs, ((s1.tcur, s1.curCkaMsg), (lpubV mc.1.1, mc.1.2))) := by
      simp [ρ2, f8Tcur, f8Cur, fig8StV, Expr.eval, Expr.v0, Expr.v1]
    rw [harg, ← hidA, ← hidB, fsSendExpr_eval,
      fsAtomicB_send_eq C ℓ encT idOf B vs (s1.tcur, s1.curCkaMsg) mc.1 hmc_short]
    dsimp only [ρ2]
    simp only [f8Mk, f8Id, f8Root, f8VR, f8Gamma, f8Cur, f8Tcur, fig8StV, fig8CtV,
      maxForwardJumps, ite_lt_eq_min, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero,
      Env.get_cons_succ, Option.map_some]

theorem fig8SendStepAtomicE_eval (idA idB : IdentityKey) {B0 : ℕ} (B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (mcOptE : Expr AOps Γ (.opt (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256)))
    (ρ : Env Γ) (st : Fig8St Pt)
    (mc? : Option ((LibsignalMsgPublicPart × Plain ℓ) × BitVec 256))
    (hstE : stE.eval ρ = fig8StV st)
    (hmcE : mcOptE.eval ρ = mc?.map (fun ((p, m), r) => ((lpubV p, m), r)))
    (hst : Fig8PartyInv B0 st)
    (hshort : ∀ x ∈ mc?, atomicShortPubB x.1.1 = true) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then idA else idB
    let fig := lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam
    let (m, coins) := mc?.getD ((⟨0, [], effectiveHkdfSalt32 none, none⟩, default), 0)
    let (st', c) := (fig8Clamp B fig).send st m coins
    (fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B stE mcOptE).eval ρ =
      (st.id.sendsIn (st.tcur + 1), (fig8StV st', fig8CtV c)) :=
  fig8SendStepAtomicE_eval_core idA idB B stE mcOptE ρ st mc? hstE hmcE
    (fun hs => by have h0 := hst.1; unfold Fig8CkaInv at h0; simpa [hs] using h0) hshort

theorem fig8SendStepAtomicE_eval_not_sendsIn (idA idB : IdentityKey) (B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (mcOptE : Expr AOps Γ (.opt (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256)))
    (ρ : Env Γ) (st : Fig8St Pt)
    (mc? : Option ((LibsignalMsgPublicPart × Plain ℓ) × BitVec 256))
    (hstE : stE.eval ρ = fig8StV st)
    (hmcE : mcOptE.eval ρ = mc?.map (fun ((p, m), r) => ((lpubV p, m), r)))
    (hnot : st.id.sendsIn (st.tcur + 1) = false)
    (hshort : ∀ x ∈ mc?, atomicShortPubB x.1.1 = true) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then idA else idB
    let fig := lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam
    let (m, coins) := mc?.getD ((⟨0, [], effectiveHkdfSalt32 none, none⟩, default), 0)
    let (st', c) := (fig8Clamp B fig).send st m coins
    (fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B stE mcOptE).eval ρ =
      (false, (fig8StV st', fig8CtV c)) := by
  have h := fig8SendStepAtomicE_eval_core idA idB B stE mcOptE ρ st mc? hstE hmcE
    (fun hs => by simp [hnot] at hs) hshort
  simpa [hnot] using h

theorem fig8SendStepAtomicE_cost (idA idB : IdentityKey) (B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (mcOptE : Expr AOps Γ (.opt (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256))) :
    (fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B stE mcOptE).cost ≤
      stE.cost + mcOptE.cost + 3 * bits B + 13 * (ℓ / 32) + 230000 := by
  have hdef := defaultMcAtomicE_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  let t0 := Ty.prod (fig8StT (ℓ := ℓ) (Pt := Pt))
    (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256)
  let Γ1 := t0 :: Γ
  let tCka := Ty.prod (ckaStT (ℓ := ℓ) (Pt := Pt)) (.prod PtT PtT)
  let Γ2 := tCka :: Γ1
  have hcka := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (ckaSendExpr ℓ Pt C Dh encPt encT lam)
    (.pair (f8Gamma (.fst .v0)) (.snd (.snd .v0)))
  have hup := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    (.pair (f8Root (.fst .v1)) (.snd (.snd .v0)))
  let t1 := Ty.prod .bool
    (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT))
  let Γ3 := t1 :: Γ1
  let Γ4 := fsSendStT (ℓ := ℓ) (Pt := Pt) :: Γ3
  have hdefE := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ3) (defaultEExpr ℓ Pt C Dh encPt encT lam) .unit
  have hfs := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ4) (fsSendExpr ℓ Pt C Dh encPt encT lam)
    (.pair .v0 (.pair (.pair (f8Tcur (.fst (.snd .v1))) (f8Cur (.fst (.snd .v1))))
      (.snd (.snd .v1))))
  have hc_cka := ckaSendExpr_cost ℓ Pt C Dh encPt encT lam
  have hc_up := prngUpExpr_cost ℓ Pt C Dh encPt encT lam
  have hc_defE := defaultEExpr_cost ℓ Pt C Dh encPt encT lam
  have hc_fs := fsSendExpr_cost ℓ Pt C Dh encPt encT lam
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2 : bits 2 ≤ 2 := bits_le_of_lt_pow (by omega) (by omega)
  unfold fig8SendStepAtomicE
  dsimp only [f8Mk, f8Id, f8Root, f8VS, f8VR, f8Gamma, f8Cur, f8Tcur, sendsInE,
    Expr.v0, Expr.v1, Expr.v2] at hcka hup hfs ⊢
  generalize defaultMcAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) = e_def at hdef ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (ckaSendExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rcka at hcka ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rup at hup ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ3) (defaultEExpr ℓ Pt C Dh encPt encT lam)
    .unit = e_rdefE at hdefE ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ4) (fsSendExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rfs at hfs ⊢
  dsimp only [cost_eLet, Expr.cost] at hcka hup hdefE hfs ⊢
  simp only [hb0, hb1] at hcka hup hdefE hfs ⊢
  omega

private theorem caseOpt_eval {S : Sig} {O' : Ops S} {Γ0 : List (Ty S)} {t u : Ty S}
    (e : Expr O' Γ0 (.opt t)) (n : Expr O' Γ0 u) (s : Expr O' (t :: Γ0) u) (ρ0 : Env Γ0) :
    (Expr.caseOpt e n s).eval ρ0 =
      match e.eval ρ0 with
      | none => n.eval ρ0
      | some x => s.eval (.cons x ρ0) := rfl

private theorem caseOpt_eval_some {S : Sig} {O' : Ops S} {Γ0 : List (Ty S)} {t u : Ty S}
    (e : Expr O' Γ0 (.opt t)) (n : Expr O' Γ0 u) (s : Expr O' (t :: Γ0) u) (ρ0 : Env Γ0)
    (x : t.denote) (hx : e.eval ρ0 = some x) :
    (Expr.caseOpt e n s).eval ρ0 = s.eval (.cons x ρ0) := by
  rw [caseOpt_eval, hx]

theorem fig8ReceiveAtomicE_eval_at (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (st : Fig8St Pt) (c : Fig8C Pt)
    (hstE : stE.eval ρ = fig8StV st) (hcE : cE.eval ρ = fig8CtV c)
    (hcka : Fig8CkaInv st) (hvr_at : ∀ v, st.vR c.1.1 = some v → SkippedLenLe B0 v) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then idA else idB
    let fig := lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam
    (fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B0 B stE cE).eval ρ =
      (((fig8Clamp B fig).receive st c).map fun (st', t, i, (p, m)) =>
        (fig8StV st', (t, (i, (lpubV p, m))))) := by
  intro idOf fig
  have hidA : idOf .A = idA := rfl
  have hidB : idOf .B = idB := rfl
  dsimp only [fig8ReceiveAtomicE]
  rw [eval_eLet]
  have hp0 : (Expr.pair stE cE).eval ρ = (fig8StV st, fig8CtV c) := by
    simp [Expr.eval, hstE, hcE]
  rw [hp0]
  let ρ1 := Env.cons
    (t := .prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (fig8StV (ℓ := ℓ) (Pt := Pt) st, fig8CtV (ℓ := ℓ) (Pt := Pt) c) ρ
  have hguard :
      (orE (sendsInE (f8Id (.fst .v0)) (.fst (.fst (.snd .v0))))
        (.lt (.add (f8Tcur (.fst .v0)) (.nat 1)) (.fst (.fst (.snd .v0)))) :
        Expr AOps _ .bool).eval ρ1 =
      (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) := by
    rw [orE_eval, sendsInE_eval _ _ _ st.id
      (by simp [ρ1, f8Id, fig8StV, partyToBool_eq_partyEnc, Expr.eval, Expr.v0])]
    simp [ρ1, f8Tcur, fig8StV, fig8CtV, Expr.eval, Expr.v0]
  dsimp only [fig8Clamp, fig, lFig8, CryptoGames.SM.Construction.scheme,
    CryptoGames.SM.Construction.receive]
  rw [ite_eval, hguard]
  by_cases hbad : (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) = true
  · simp [hbad, Expr.eval]
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    have hbad' : st.id.sendsIn c.1.1 = false ∧ ¬ st.tcur + 1 < c.1.1 := by
      simpa [Bool.or_eq_true] using hbad
    set s1Opt : Option (Fig8St Pt) :=
      if c.1.1 = st.tcur + 1 then
        match c.1.2 with
        | none => none
        | some Tn =>
          some { id := st.id
                 root := ((rootPRNG C.F encPt).up st.root ((dhScheme Dh).receive st.γ Tn).2).1
                 vS := st.vS
                 vR := Function.update st.vR c.1.1
                   (some ((lFS C protoSignalCodec ℓ encT idOf 25000).initReceiver
                     ((rootPRNG C.F encPt).up st.root ((dhScheme Dh).receive st.γ Tn).2).2))
                 γ := ((dhScheme Dh).receive st.γ Tn).1
                 curCkaMsg := st.curCkaMsg
                 tcur := c.1.1 }
      else some st
    have hs1Opt_eval :
        (Expr.ite (O := AOps) (.eqN (.fst (.fst (.snd .v0))) (.add (f8Tcur (.fst .v0)) (.nat 1)))
          (.caseOpt (.snd (.fst (.snd .v0))) .none
            (eLet (runFig8WithIds idA idB (ckaRecvExpr ℓ Pt C Dh encPt encT lam)
                (.pair (f8Gamma (.fst .v1)) .v0))
              (eLet (runFig8WithIds idA idB (prngUpExpr ℓ Pt C Dh encPt encT lam)
                  (.pair (f8Root (.fst .v2)) (.snd .v0)))
                (.some (f8Mk (f8Id (.fst .v3)) (.fst .v0) (f8VS (.fst .v3))
                  (.tset (f8VR (.fst .v3)) (.fst (.fst (.snd .v3)))
                    (.some (.pair (.snd .v0) (.pair (.nat 0) .nil))))
                  (.fst .v1) (f8Cur (.fst .v3)) (.fst (.fst (.snd .v3))))))))
          (.some (.fst .v0))).eval ρ1 = s1Opt.map fig8StV := by
      rw [ite_eval]
      have heq_eval : (Expr.eqN (.fst (.fst (.snd .v0))) (.add (f8Tcur (.fst .v0)) (.nat 1)) :
          Expr AOps _ .bool).eval ρ1 = decide (c.1.1 = st.tcur + 1) := by
        simp [ρ1, f8Tcur, fig8StV, fig8CtV, Expr.eval, Expr.v0]
      rw [heq_eval]
      by_cases heq : c.1.1 = st.tcur + 1
      · simp only [heq, decide_true, ↓reduceIte, s1Opt]
        rcases hc2 : c.1.2 with _ | Tn
        · simp [ρ1, fig8CtV, hc2, Expr.eval, Expr.v0]
        · have hcka0 := hcka; unfold Fig8CkaInv at hcka0
          have hs0 : st.id.sendsIn (st.tcur + 1) = false := by rw [← heq]; exact hbad'.1
          simp only [hs0, Bool.false_eq_true, ↓reduceIte] at hcka0
          rcases hcka0 with ⟨x, hγ⟩
          have hc2_eval : ((Expr.snd (.fst (.snd .v0)) :
              Expr AOps (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ)
                (.opt PtT))).eval ρ1 = some Tn := by
            simp [ρ1, fig8CtV, hc2, Expr.eval, Expr.v0]
          rw [caseOpt_eval, hc2_eval]
          simp only [eval_eLet, eval_runFig8WithIds, ρ1, heq, f8Gamma, f8Root, f8Mk, f8Id, f8VS,
            f8VR, f8Cur, fig8StV, fig8CtV, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
            Env.get_cons_zero, Env.get_cons_succ]
          let kOut := (ckaRecvExpr ℓ Pt C Dh encPt encT lam).eval
            (.cons (ckaStV st.γ, Tn) (.cons (idOf .A, idOf .B) .nil))
          let pOut := (prngUpExpr ℓ Pt C Dh encPt encT lam).eval
            (.cons (st.root, kOut.2) (.cons (idOf .A, idOf .B) .nil))
          change some (partyToBool st.id, (pOut.1, (st.vS.map fsSendStV,
            (fun k => if k = st.tcur + 1 then some (pOut.2, (0, []))
               else (st.vR k).map fsRecvStV,
             (kOut.1, (st.curCkaMsg, st.tcur + 1)))))) = _
          dsimp only [kOut, pOut]
          rw [ckaRecvExpr_eval, hγ, dhSchemeFb_receive_exp, prngUpExpr_eval]
          dsimp only [Option.map, fig8StV, lFS, fromAEADPRG, fsRecvStV]
          congr 1; congr 2; congr 1; congr 1
          funext k
          by_cases hk : k = st.tcur + 1
          · subst hk; simp [Function.update_self]
          · simp [hk]
      · simp [heq, s1Opt, ρ1, Expr.eval, Expr.v0]
    have hs1_sk : ∀ s1 ∈ s1Opt, ∀ v, s1.vR c.1.1 = some v → SkippedLenLe B0 v := by
      intro s1 hs1 v hv
      dsimp only [s1Opt] at hs1
      split_ifs at hs1 with heq
      · rcases hc2 : c.1.2 with _ | Tn
        · rw [hc2] at hs1; cases hs1
        · rw [hc2] at hs1
          simp only [Option.mem_def, Option.some.injEq] at hs1; subst hs1
          dsimp only at hv
          simp only [Function.update_self, Option.some.injEq] at hv; subst hv
          simp [SkippedLenLe, lFS, fromAEADPRG]
      · simp only [Option.mem_def, Option.some.injEq] at hs1; subst hs1
        exact hvr_at v hv
    rw [caseOpt_eval, hs1Opt_eval]
    rcases hs1 : s1Opt with _ | s1
    · rw [show Option.map (fig8StV (ℓ := ℓ) (Pt := Pt)) (none : Option (Fig8St Pt)) = none from rfl]
      dsimp only
      split
      · rfl
      · next s2 h =>
        exact absurd (hs1.symm.trans h) (by simp)
    · rw [show Option.map (fig8StV (ℓ := ℓ) (Pt := Pt)) (some s1) = some (fig8StV s1) from rfl]
      dsimp only
      split
      · next h => exact absurd (hs1.symm.trans h) (by simp)
      next s2 h =>
      obtain rfl : s1 = s2 := Option.some.inj (hs1.symm.trans h)
      let ρ2 := Env.cons (t := fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StV (ℓ := ℓ) (Pt := Pt) s1) ρ1
      have hvr_eval : (Expr.tget (O := AOps) (f8VR .v0) (.fst (.fst (.snd .v1)))).eval ρ2 =
          (s1.vR c.1.1).map fsRecvStV := by
        simp [ρ2, ρ1, f8VR, fig8StV, fig8CtV, Expr.eval, Expr.v0, Expr.v1]
      rw [caseOpt_eval, hvr_eval]
      rcases hvt : s1.vR c.1.1 with _ | v
      · rfl
      · dsimp only [Option.map]
        let ρ3 := Env.cons (t := fsRecvStT (ℓ := ℓ) (Pt := Pt)) (fsRecvStV (ℓ := ℓ) (Pt := Pt) v) ρ2
        have hfs_eval := fsReceiveAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) idA idB B0 B
          (Γ := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: fig8StT (ℓ := ℓ) (Pt := Pt) :: _)
          .v0 (.snd .v2) ρ3 v c rfl rfl (hs1_sk s1 hs1 v hvt)
        dsimp only [idOf] at hfs_eval ⊢
        rw [caseOpt_eval, hfs_eval]
        dsimp only [fsClampSim]
        rcases (lFS C protoSignalCodec ℓ encT idOf 25000).receive v c.1 c.2
            with _ | ⟨v', idx, p, m⟩
        · rfl
        · dsimp only [ρ3, ρ2, ρ1, Option.map]
          simp only [f8Mk, f8Id, f8Root, f8VS, f8VR, f8Gamma, f8Cur, f8Tcur,
            fig8StV, fig8CtV, ite_lt_eq_min, Expr.eval, Expr.v0, Expr.v2, Expr.v3,
            Env.get_cons_zero, Env.get_cons_succ, Option.some.injEq,
            Prod.mk.injEq]
          simp only [true_and, and_true]
          funext k
          by_cases hk : k = c.1.1
          · subst hk; simp [Function.update_self]
          · simp [hk]

theorem fig8ReceiveAtomicE_eval (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (st : Fig8St Pt) (c : Fig8C Pt)
    (hstE : stE.eval ρ = fig8StV st) (hcE : cE.eval ρ = fig8CtV c)
    (hst : Fig8PartyInv B0 st) :
    let idOf : Party → IdentityKey := fun R => if R == Party.A then idA else idB
    let fig := lFig8 Dh encPt C protoSignalCodec ℓ encT idOf 25000 lam
    (fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B0 B stE cE).eval ρ =
      (((fig8Clamp B fig).receive st c).map fun (st', t, i, (p, m)) =>
        (fig8StV st', (t, (i, (lpubV p, m))))) :=
  fig8ReceiveAtomicE_eval_at idA idB B0 B stE cE ρ st c hstE hcE hst.1 (hst.2 c.1.1)

theorem fig8ReceiveAtomicE_cost (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB B0 B stE cE).cost ≤
      stE.cost + cE.cost + 20 * B0 + 5 * bits B + 16 * (ℓ / 32) + 220150000 := by
  let t0 := Ty.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let Γ1 := t0 :: Γ
  let Γ2 := PtT (ℓ := ℓ) (Pt := Pt) :: Γ1
  let Γ3 := Ty.prod (ckaStT (ℓ := ℓ) (Pt := Pt)) PtT :: Γ2
  have hcka := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (ckaRecvExpr ℓ Pt C Dh encPt encT lam)
    (.pair (f8Gamma (.fst .v1)) .v0)
  have hup := cost_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ3) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    (.pair (f8Root (.fst .v2)) (.snd .v0))
  let Γ4 := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hfs := fsReceiveAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B0 B (Γ := Γ4) .v0 (.snd .v2)
  have hc_cka := ckaRecvExpr_cost ℓ Pt C Dh encPt encT lam
  have hc_up := prngUpExpr_cost ℓ Pt C Dh encPt encT lam
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2 : bits 2 ≤ 2 := bits_le_of_lt_pow (by omega) (by omega)
  unfold fig8ReceiveAtomicE
  dsimp only [f8Mk, f8Id, f8Root, f8VS, f8VR, f8Gamma, f8Cur, f8Tcur, orE, sendsInE,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hcka hup hfs ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (ckaRecvExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rcka at hcka ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ3) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rup at hup ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B0 B (Γ := Γ4) _ _ = e_rfs at hfs ⊢
  dsimp only [cost_eLet, Expr.cost] at hcka hup hfs ⊢
  simp only [hb0, hb1] at hcka hup hfs ⊢
  omega

/-! ## Sanitizers and `Kept` operations -/

def sanRSAtomicE (T : ℕ) {O' : Ops ASig} {Γ : List (Ty ASig)}
    (vE : Expr O' Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt)) :=
  eLet vE (.pair (.fst .v0) (.pair (.fst (.snd .v0)) (.take (.nat T) (.snd (.snd .v0)))))

omit [DecidableEq Pt] [Zero Pt] in
theorem sanRSAtomicE_eval (T : ℕ) {O' : Ops ASig} {Γ : List (Ty ASig)}
    (vE : Expr O' Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (v : RatchetReceiverState (BitVec 256) (BitVec 256))
    (hvE : vE.eval ρ = fsRecvStV v) :
    (sanRSAtomicE T vE).eval ρ = fsRecvStV (sanRS T v) := by
  rcases v with ⟨ck, li, sk⟩
  simp [sanRSAtomicE, sanRS, fsRecvStV, hvE, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
theorem sanRSAtomicE_cost (T : ℕ) {O' : Ops ASig} {Γ : List (Ty ASig)}
    (vE : Expr O' Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt))) :
    (sanRSAtomicE T vE).cost ≤ vE.cost + bits T + 15 := by
  simp only [sanRSAtomicE, cost_eLet, Expr.cost, Expr.v0]
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem skippedLenLe_sanRS (T : ℕ) (v : RatchetReceiverState (BitVec 256) (BitVec 256)) :
    SkippedLenLe T (sanRS T v) := by
  simp [SkippedLenLe, sanRS]

def sanGammaAtomicE {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (ckaStT (ℓ := ℓ) (Pt := Pt)) :=
  eLet stE
    (.ite (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)))
      (.caseSum (f8Gamma .v0)
        (.inl .v0)
        (.inl (opGroup (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) .ptLam .unit)))
      (.caseSum (f8Gamma .v0)
        (.inr (opPure (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
          (decT := decT) (lam := lam) (.bv256Lit 0#256) .unit))
        (.inr .v0)))

theorem sanGammaAtomicE_eval {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (st : Fig8St Pt) (hstE : stE.eval ρ = fig8StV st) :
    (sanGammaAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) stE).eval ρ = ckaStV (sanGamma lam st) := by
  dsimp only [sanGammaAtomicE]
  rw [eval_eLet, hstE, ite_eval]
  have hsn : (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)) :
      Expr AOps (fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ) .bool).eval (.cons (fig8StV st) ρ) =
      st.id.sendsIn (st.tcur + 1) := by
    rw [sendsInE_eval _ _ _ st.id
      (by simp [f8Id, fig8StV, partyToBool_eq_partyEnc, Expr.eval, Expr.v0])]
    simp [f8Tcur, fig8StV, Expr.eval, Expr.v0]
  rw [hsn]
  rcases hγ : st.γ with h | x <;> by_cases hs : st.id.sendsIn (st.tcur + 1) = true <;>
    simp [sanGamma, hs, hγ, f8Gamma, fig8StV, ckaStV, Expr.eval, Expr.v0,
      AtomicGroupOp.eval, AtomicPureOp.eval]

theorem sanGammaAtomicE_cost {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (sanGammaAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) stE).cost ≤ stE.cost + 50 := by
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2 : bits 2 ≤ 2 := bits_le_of_lt_pow (by omega) (by omega)
  simp only [sanGammaAtomicE, sendsInE, f8Id, f8Tcur, f8Gamma, cost_eLet, Expr.cost,
    cost_opGroup, cost_opPure, AtomicGroupOp.cost, AtomicPureOp.cost, Expr.v0, hb0, hb1]
  omega

def sanAtAtomicE (T : ℕ) {Γ : List (Ty ASig)}
    (tE : Expr AOps Γ .nat) (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)) :=
  eLet (.pair tE stE)
    (let t0 : Expr AOps _ .nat := .fst .v0
     let s0 : Expr AOps _ (fig8StT (ℓ := ℓ) (Pt := Pt)) := .snd .v0
     f8Mk (f8Id s0) (f8Root s0) (f8VS s0)
       (.tset (f8VR s0) t0
         (.caseOpt (.tget (f8VR s0) t0) .none (.some (sanRSAtomicE T .v0))))
       (sanGammaAtomicE s0) (f8Cur s0) (f8Tcur s0))

theorem sanAtAtomicE_eval (T : ℕ) {Γ : List (Ty ASig)}
    (tE : Expr AOps Γ .nat) (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ)
    (t : ℕ) (st : Fig8St Pt) (htE : tE.eval ρ = t) (hstE : stE.eval ρ = fig8StV st) :
    (sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) T tE stE).eval ρ = fig8StV (sanAt T lam t st) := by
  dsimp only [sanAtAtomicE]
  rw [eval_eLet]
  have hp : (Expr.pair tE stE).eval ρ = (t, fig8StV st) := by simp [Expr.eval, htE, hstE]
  rw [hp]
  let ρ1 := Env.cons (t := .prod .nat (fig8StT (ℓ := ℓ) (Pt := Pt))) (t, fig8StV st) ρ
  have hγ := sanGammaAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (.snd .v0) ρ1 st rfl
  dsimp only [f8Mk, Expr.eval, ρ1]
  rw [hγ]
  simp only [sanAt, f8Id, f8Root, f8VS, f8VR, f8Cur, f8Tcur, fig8StV,
    Expr.eval, Expr.v0, Env.get_cons_zero, Prod.mk.injEq, true_and, and_true]
  funext j
  by_cases hj : j = t
  · subst hj
    simp only [↓reduceIte]
    rcases hvt : st.vR j with _ | v
    · simp
    · simp only [Option.map_some]
      exact congrArg some (sanRSAtomicE_eval T .v0 (.cons (fsRecvStV v) _) v rfl)
  · simp [hj]

theorem sanAtAtomicE_cost (T : ℕ) {Γ : List (Ty ASig)}
    (tE : Expr AOps Γ .nat) (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) T tE stE).cost ≤ tE.cost + stE.cost + bits T + 320 := by
  let tP := Ty.prod .nat (fig8StT (ℓ := ℓ) (Pt := Pt))
  have hrs := sanRSAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) T
    (Γ := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tP :: Γ) .v0
  have hγ := sanGammaAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := tP :: Γ) (.snd .v0)
  dsimp only [sanAtAtomicE, f8Mk, f8Id, f8Root, f8VS, f8VR, f8Cur, f8Tcur, Expr.v0] at hrs hγ ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T _ = e_rs at hrs ⊢
  generalize sanGammaAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ = e_g at hγ ⊢
  dsimp only [cost_eLet, Expr.cost] at hrs hγ ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem fig8CkaInv_sanAt (T : ℕ) (t : ℕ) (st : Fig8St Pt) :
    Fig8CkaInv (sanAt T lam t st) := by
  unfold Fig8CkaInv sanAt sanGamma
  dsimp only
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true <;> rcases st.γ with h | x <;> simp [hs]

omit [DecidableEq Pt] [Zero Pt] in
theorem skippedLenLe_sanAt (T : ℕ) (t : ℕ) (st : Fig8St Pt) :
    ∀ v, (sanAt T lam t st).vR t = some v → SkippedLenLe T v := by
  intro v hv
  simp only [sanAt, ↓reduceIte] at hv
  rcases hvt : st.vR t with _ | v0 <;> simp [hvt] at hv
  subst hv
  exact skippedLenLe_sanRS T v0

def keptOfStAtomicE {O' : Ops ASig} {Γ : List (Ty ASig)}
    (stE : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    Expr O' Γ (keptT ℓ Pt) :=
  eLet stE (.pair (.some .v0) (f8VR .v0))

omit [DecidableEq Pt] [Zero Pt] in
theorem keptOfStAtomicE_eval {O' : Ops ASig} {Γ : List (Ty ASig)}
    (stE : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) (ρ : Env Γ) (st : Fig8St Pt)
    (hstE : stE.eval ρ = fig8StV st) :
    (keptOfStAtomicE stE).eval ρ = keptEnc (Kept.ofSt st) := by
  simp [keptOfStAtomicE, Kept.ofSt, keptEnc, f8VR, fig8StV, hstE, Expr.eval, Expr.v0]

omit [DecidableEq Pt] [Zero Pt] in
theorem keptOfStAtomicE_cost {O' : Ops ASig} {Γ : List (Ty ASig)}
    (stE : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    (keptOfStAtomicE stE).cost ≤ stE.cost + 15 := by
  simp only [keptOfStAtomicE, f8VR, cost_eLet, Expr.cost, Expr.v0]
  omega

def keptSendAtomicE (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) : Expr AOps Γ (keptT ℓ Pt) :=
  eLet kE
    (.caseOpt (.fst .v0)
      .v0
      (.ite (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)))
        (.pair .none (f8VR .v0))
        (.pair
          (.some (.fst (.snd (fig8SendStepAtomicE idA idB 0 .v0 .none))))
          (.snd .v1))))

theorem keptSendAtomicE_eval (idA idB : IdentityKey) (T : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) (ρ : Env Γ) (k : Kept Pt)
    (hkE : kE.eval ρ = keptEnc k) :
    (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB kE).eval ρ =
      keptEnc (Kept.send (ℓ := ℓ)
        (fig := figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T) k) := by
  dsimp only [keptSendAtomicE]
  rw [eval_eLet, hkE, caseOpt_eval]
  rcases k with ⟨full, rs⟩
  rcases full with _ | st
  · rfl
  · let ρ1 := Env.cons (t := fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StV (ℓ := ℓ) (Pt := Pt) st)
      (.cons (keptEnc (ℓ := ℓ) ⟨some st, rs⟩) ρ)
    change ((sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1))).ite
        (.pair .none (f8VR .v0))
        (.pair (.some (.fst (.snd (fig8SendStepAtomicE idA idB 0 .v0 .none)))) (.snd .v1))).eval ρ1 =
      keptEnc (Kept.send (ℓ := ℓ)
        (fig := figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T) ⟨some st, rs⟩)
    dsimp only [Kept.send]
    have hsn : (sendsInE (f8Id .v0) (.add (f8Tcur .v0) (.nat 1)) :
        Expr AOps _ .bool).eval ρ1 = st.id.sendsIn (st.tcur + 1) := by
      rw [sendsInE_eval _ _ _ st.id
        (by simp [ρ1, f8Id, fig8StV, partyToBool_eq_partyEnc, Expr.eval, Expr.v0])]
      simp [ρ1, f8Tcur, fig8StV, Expr.eval, Expr.v0]
    rw [ite_eval, hsn]
    by_cases hs : st.id.sendsIn (st.tcur + 1) = true
    · simp [hs, ρ1, f8VR, fig8StV, keptEnc, Expr.eval, Expr.v0]
    · have hs0 : st.id.sendsIn (st.tcur + 1) = false := Bool.eq_false_iff.mpr hs
      simp only [hs0, Bool.false_eq_true, ↓reduceIte]
      have hsend := fig8SendStepAtomicE_eval_not_sendsIn (C := C) (K := K) (Dh := Dh)
        (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB 0
        (Γ := fig8StT (ℓ := ℓ) (Pt := Pt) :: keptT ℓ Pt :: Γ)
        .v0 .none ρ1 st none rfl rfl hs0 (by intro _ h; cases h)
      dsimp only [Option.getD] at hsend
      dsimp only [Expr.eval]
      rw [hsend]
      simp [ρ1, keptEnc, figS, fig8San, fig8Clamp, paramsV1, Expr.v1, CryptoVerification.E2E.paramsIdsWithSpqr]
      rfl

theorem keptSendAtomicE_cost (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) :
    (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB kE).cost ≤
      kE.cost + 13 * (ℓ / 32) + 240000 := by
  let Γ1 := fig8StT (ℓ := ℓ) (Pt := Pt) :: keptT ℓ Pt :: Γ
  have hstep := fig8SendStepAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 (Γ := Γ1) .v0 .none
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2 : bits 2 ≤ 2 := bits_le_of_lt_pow (by omega) (by omega)
  dsimp only [keptSendAtomicE, sendsInE, f8Id, f8Tcur, f8VR, Expr.v0, Expr.v1] at hstep ⊢
  generalize fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB 0 (Γ := Γ1) _ _ = e_s at hstep ⊢
  dsimp only [cost_eLet, Expr.cost] at hstep ⊢
  simp only [hb0, hb1] at hstep ⊢
  omega

def keptRecvAtomicE (idA idB : IdentityKey) (T : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ (keptT ℓ Pt) :=
  eLet (.pair kE cE)
    (let k0 : Expr AOps _ (keptT ℓ Pt) := .fst .v0
     let c0 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .snd .v0
     .caseOpt (.fst k0)
       (let t0 : Expr AOps _ .nat := .fst (.fst c0)
        let v'E : Expr AOps _ (.opt (fsRecvStT (ℓ := ℓ) (Pt := Pt))) :=
          .caseOpt (.tget (.snd k0) t0)
            .none
            (.caseOpt (fsReceiveAtomicE idA idB T 0 (sanRSAtomicE T .v0) (.snd .v1))
              .none
              (.some (.fst .v0)))
        .pair .none (.tset (.snd k0) t0 v'E))
       (.caseOpt
         (fig8ReceiveAtomicE idA idB T 0
           (sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0)
           (.snd .v1))
         (.pair .none (f8VR .v0))
         (.pair (.some (.fst .v0)) (.snd (.fst .v2)))))

private theorem bits_le_succ_nat (n : ℕ) : bits n ≤ n + 1 := by
  have hpow : ∀ m, m < 2 ^ (m + 1) := by
    intro m; induction m with
    | zero => omega
    | succ m ih =>
      have : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by rw [Nat.pow_succ]; ring
      omega
  exact bits_le_of_lt_pow (by omega) (hpow n)

set_option linter.unusedSimpArgs false in
theorem keptRecvAtomicE_eval (idA idB : IdentityKey) (T : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (k : Kept Pt) (c : Fig8C Pt)
    (hkE : kE.eval ρ = keptEnc k) (hcE : cE.eval ρ = fig8CtV c) :
    (keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T kE cE).eval ρ =
      keptEnc (Kept.recv (ℓ := ℓ)
        (fig := figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T)
        (fs := fsS (ℓ := ℓ) (paramsV1 C K idA idB) encT T) c k) := by
  dsimp only [keptRecvAtomicE]
  rw [eval_eLet]
  have hp : (Expr.pair kE cE).eval ρ = (keptEnc k, fig8CtV c) := by simp [Expr.eval, hkE, hcE]
  rw [hp]
  let ρ1 := Env.cons (t := .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))) (keptEnc k, fig8CtV c) ρ
  rcases k with ⟨full, rs⟩
  rcases full with _ | st
  · rw [caseOpt_eval]
    change (Expr.pair .none (.tset (.snd (.fst .v0)) (.fst (.fst (.snd .v0))) _)).eval ρ1 = _
    dsimp only [Kept.recv, keptEnc, Option.map]
    simp only [ρ1, fig8CtV, keptEnc, Expr.eval, Expr.v0, Env.get_cons_zero, Prod.mk.injEq,
      true_and]
    funext j
    by_cases hj : j = c.1.1
    · subst hj
      simp only [↓reduceIte]
      rcases hrs : rs c.1.1 with _ | v
      · dsimp only [Option.map, Option.bind, Expr.eval]; simp
      · dsimp only [Option.map, Option.bind]
        let ρ2 := Env.cons (t := fsRecvStT (ℓ := ℓ) (Pt := Pt)) (fsRecvStV (ℓ := ℓ) (Pt := Pt) v) ρ1
        have hsan := sanRSAtomicE_eval (ℓ := ℓ) (Pt := Pt) (O' := AOps) T .v0 ρ2 v rfl
        have hfs := fsReceiveAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) idA idB T 0
          (Γ := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ)
          (sanRSAtomicE T .v0) (.snd .v1) ρ2 (sanRS T v) c hsan rfl (skippedLenLe_sanRS T v)
        erw [hfs]
        simp only [Function.update_self]
        dsimp only [fsS, fsSan, fsClampSim, paramsV1, CryptoVerification.E2E.paramsIdsWithSpqr]
        rcases (lFS C protoSignalCodec ℓ encT (fun R => if R == .A then idA else idB) 25000).receive
            (sanRS T v) c.1 c.2 with _ | ⟨v', idx, p, m⟩ <;> rfl
    · simp only [hj, ↓reduceIte, Function.update_of_ne hj]
      cases rs j <;> rfl
  · rw [caseOpt_eval_some _ _ _ _ (fig8StV (ℓ := ℓ) (Pt := Pt) st) rfl]
    dsimp only [Kept.recv]
    let ρ2 := Env.cons (t := fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StV (ℓ := ℓ) (Pt := Pt) st) ρ1
    have hsan := sanAtAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) T (.fst (.fst (.snd .v1))) .v0 ρ2 c.1.1 st rfl rfl
    have hrec := fig8ReceiveAtomicE_eval_at (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB T 0
      (Γ := fig8StT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ)
      (sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1) ρ2 (sanAt T lam c.1.1 st) c
      hsan rfl (fig8CkaInv_sanAt (lam := lam) T c.1.1 st) (skippedLenLe_sanAt T c.1.1 st)
    rw [caseOpt_eval, hrec]
    dsimp only [figS, fig8San, fig8Clamp, paramsV1, CryptoVerification.E2E.paramsIdsWithSpqr]
    try simp only [beq_iff_eq]
    rcases hrcv : (lFig8 Dh encPt C protoSignalCodec ℓ encT (fun R => if R = Party.A then idA else idB)
        25000 lam).receive (sanAt T lam c.1.1 st) c with _ | ⟨st', t', i', p, m⟩ <;>
      simp [hrcv, ρ2, ρ1, keptEnc, f8VR, fig8StV, Expr.eval, Expr.v0, Expr.v2,
        Env.get_cons_zero, Env.get_cons_succ]

theorem keptRecvAtomicE_cost (idA idB : IdentityKey) (T : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T kE cE).cost ≤
      kE.cost + cE.cost + 21 * T + 16 * (ℓ / 32) + 220250000 := by
  let tKC := Ty.prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let ΓN := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  let ΓS := fig8StT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  have hrs := sanRSAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓN)
    (sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓS)
    (sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  have hb0 : bits 0 = 1 := bits_zero
  have hbT : bits T ≤ T + 1 := bits_le_succ_nat T
  dsimp only [keptRecvAtomicE, f8VR, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs at hrs hfs ⊢
  generalize sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  dsimp only [cost_eLet, Expr.cost] at hrs hfs hat hf8 ⊢
  simp only [hb0] at hrs hfs hat hf8 ⊢
  omega

def keptEvalAtomicE (idA idB : IdentityKey) (T B : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ
      (.opt (.opt (.prod .nat (.prod .nat (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT))))) :=
  eLet (.pair kE cE)
    (let k0 : Expr AOps _ (keptT ℓ Pt) := .fst .v0
     let c0 : Expr AOps _ (fig8CtT (ℓ := ℓ) (Pt := Pt)) := .snd .v0
     .caseOpt (.fst k0)
       (.caseOpt (.tget (.snd k0) (.fst (.fst c0)))
         .none
         (.some
           (.caseOpt (fsReceiveAtomicE idA idB T B (sanRSAtomicE T .v0) (.snd .v1))
             .none
             (.some (.pair (.fst (.fst (.snd .v2))) (.snd .v0))))))
       (.some
         (.caseOpt
           (fig8ReceiveAtomicE idA idB T B
             (sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0)
             (.snd .v1))
           .none
           (.some (.snd .v0)))))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem keptEvalAtomicE_eval (idA idB : IdentityKey) (T B : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ) (k : Kept Pt) (c : Fig8C Pt)
    (hkE : kE.eval ρ = keptEnc k) (hcE : cE.eval ρ = fig8CtV c) :
    (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T B kE cE).eval ρ =
      (Kept.eval (ℓ := ℓ)
        (fig := fig8Clamp B (figS (ℓ := ℓ) (paramsV1 C K idA idB) Dh encPt encT lam T))
        (fs := fsClampSim B (fsS (ℓ := ℓ) (paramsV1 C K idA idB) encT T)) c k).map
        (Option.map fun (t, i, (p, m)) => (t, (i, (lpubV p, m)))) := by
  dsimp only [keptEvalAtomicE]
  rw [eval_eLet]
  have hp : (Expr.pair kE cE).eval ρ = (keptEnc k, fig8CtV c) := by simp [Expr.eval, hkE, hcE]
  rw [hp]
  let ρ1 := Env.cons (t := .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))) (keptEnc k, fig8CtV c) ρ
  rcases k with ⟨full, rs⟩
  rcases full with _ | st
  · rw [caseOpt_eval]
    change (Expr.caseOpt (.tget (.snd (.fst .v0)) (.fst (.fst (.snd .v0)))) _ _).eval ρ1 = _
    dsimp only [Kept.eval]
    have htg : (Expr.tget (O := AOps) (.snd (.fst .v0)) (.fst (.fst (.snd .v0)))).eval ρ1 =
        (rs c.1.1).map fsRecvStV := by
      simp [ρ1, keptEnc, fig8CtV, Expr.eval, Expr.v0]
    rw [caseOpt_eval, htg]
    rcases hrs : rs c.1.1 with _ | v
    · rfl
    · dsimp only [Option.map]
      let ρ2 := Env.cons (t := fsRecvStT (ℓ := ℓ) (Pt := Pt)) (fsRecvStV (ℓ := ℓ) (Pt := Pt) v) ρ1
      have hsan := sanRSAtomicE_eval (ℓ := ℓ) (Pt := Pt) (O' := AOps) T .v0 ρ2 v rfl
      have hfs := fsReceiveAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) idA idB T B
        (Γ := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ)
        (sanRSAtomicE T .v0) (.snd .v1) ρ2 (sanRS T v) c hsan rfl (skippedLenLe_sanRS T v)
      dsimp only [Expr.eval]
      congr 1
      erw [hfs]
      dsimp only [fsS, fsSan, fsClampSim, paramsV1, CryptoVerification.E2E.paramsIdsWithSpqr]
      rcases (lFS C protoSignalCodec ℓ encT (fun R => if R == .A then idA else idB) 25000).receive
          (sanRS T v) c.1 c.2 with _ | ⟨v', idx, p, m⟩ <;>
        simp [ρ2, ρ1, fig8CtV, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
  · rw [caseOpt_eval_some _ _ _ _ (fig8StV (ℓ := ℓ) (Pt := Pt) st) rfl]
    dsimp only [Kept.eval, Option.map]
    let ρ2 := Env.cons (t := fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8StV (ℓ := ℓ) (Pt := Pt) st) ρ1
    have hsan := sanAtAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) T (.fst (.fst (.snd .v1))) .v0 ρ2 c.1.1 st rfl rfl
    have hrec := fig8ReceiveAtomicE_eval_at (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB T B
      (Γ := fig8StT (ℓ := ℓ) (Pt := Pt) :: .prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ)
      (sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1) ρ2 (sanAt T lam c.1.1 st) c
      hsan rfl (fig8CkaInv_sanAt (lam := lam) T c.1.1 st) (skippedLenLe_sanAt T c.1.1 st)
    dsimp only [Expr.eval]
    congr 1
    rw [hrec]
    dsimp only [figS, fig8San, fig8Clamp, paramsV1, CryptoVerification.E2E.paramsIdsWithSpqr]
    try simp only [beq_iff_eq]
    rcases hrcv : (lFig8 Dh encPt C protoSignalCodec ℓ encT (fun R => if R = Party.A then idA else idB)
        25000 lam).receive (sanAt T lam c.1.1 st) c with _ | ⟨st', t', i', p, m⟩ <;>
      simp [hrcv, Expr.eval, Expr.v0]

theorem keptEvalAtomicE_cost (idA idB : IdentityKey) (T B : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB T B kE cE).cost ≤
      kE.cost + cE.cost + 21 * T + 5 * bits B + 16 * (ℓ / 32) + 220250000 := by
  let tKC := Ty.prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let ΓN := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  let ΓS := fig8StT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  have hrs := sanRSAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓN)
    (sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓS)
    (sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  have hbT : bits T ≤ T + 1 := bits_le_succ_nat T
  dsimp only [keptEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs at hrs hfs ⊢
  generalize sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  dsimp only [cost_eLet, Expr.cost] at hrs hfs hat hf8 ⊢
  omega

private theorem list_find?_map {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ xs : List α, (xs.map f).find? p = (xs.find? (fun x => p (f x))).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.find?_cons]
    cases p (f x) <;> simp [list_find?_map]

def sentEvalAtomicE (idA idB : IdentityKey) (L B : ℕ) {Γ : List (Ty ASig)}
    (sentE : Expr AOps Γ (.list (sentEntryT ℓ Pt)))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    Expr AOps Γ
      (.opt (.opt (.prod .nat (.prod .nat (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT))))) :=
  eLet (.pair sentE (.pair cE c'E))
    (let sent0 : Expr AOps _ (.list (sentEntryT ℓ Pt)) := .fst .v0
     .caseOpt
       (.findB L sent0 (eqFig8CAtomicE (.fst .v0) (.fst (.snd .v1))))
       .none
       (.some
         (.caseOpt
           (fsReceiveAtomicE idA idB 0 B (senderToFreshVrAtomicE (.snd .v0)) (.snd (.snd .v1)))
           .none
           (.some (.pair (.fst (.fst (.snd (.snd .v2)))) (.snd .v0))))))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem sentEvalAtomicE_eval (idA idB : IdentityKey) (L T B : ℕ) {Γ : List (Ty ASig)}
    (sentE : Expr AOps Γ (.list (sentEntryT ℓ Pt)))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt)))
    (ρ : Env Γ)
    (sent : List (Fig8C Pt × RatchetSenderState (BitVec 256)))
    (c c' : Fig8C Pt)
    (hsentE : sentE.eval ρ = sent.map sentEntryEnc)
    (hcE : cE.eval ρ = fig8CtV c) (hc'E : c'E.eval ρ = fig8CtV c')
    (hlen : sent.length ≤ L) :
    (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L B sentE cE c'E).eval ρ =
      (sentEval (ℓ := ℓ)
        (fs := fsClampSim B (fsS (ℓ := ℓ) (paramsV1 C K idA idB) encT T)) sent c c').map
        (Option.map fun (t, i, (p, m)) => (t, (i, (lpubV p, m)))) := by
  dsimp only [sentEvalAtomicE]
  rw [eval_eLet]
  have hp : (Expr.pair sentE (.pair cE c'E)).eval ρ =
      (sent.map sentEntryEnc, (fig8CtV c, fig8CtV c')) := by
    simp [Expr.eval, hsentE, hcE, hc'E]
  rw [hp]
  let t0 := Ty.prod (.list (sentEntryT ℓ Pt))
    (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))
  let ρ1 := Env.cons (t := t0) (sent.map (sentEntryEnc (ℓ := ℓ) (Pt := Pt)), (fig8CtV c, fig8CtV c')) ρ
  have htake : (sent.map (sentEntryEnc (ℓ := ℓ) (Pt := Pt))).take L =
      sent.map (sentEntryEnc (ℓ := ℓ) (Pt := Pt)) :=
    List.take_of_length_le (by simpa using hlen)
  have hfind : (Expr.findB (O := AOps) L (.fst .v0)
      (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (.fst .v0) (.fst (.snd .v1)))).eval ρ1 =
      (sent.find? fun e => decide (e.1 = c)).map sentEntryEnc := by
    dsimp only [Expr.eval]
    change (((sent.map (sentEntryEnc (ℓ := ℓ) (Pt := Pt))).take L).find? _) = _
    rw [htake, list_find?_map]
    congr 2; funext ⟨ec, ev⟩
    exact eqFig8CAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (.fst .v0) (.fst (.snd .v1))
      (.cons (sentEntryEnc (ec, ev)) ρ1) ec c rfl rfl
  rw [caseOpt_eval, hfind]
  dsimp only [sentEval]
  rcases hfd : sent.find? (fun e => decide (e.1 = c)) with _ | ⟨ec, ev⟩
  · simp [hfd, Expr.eval]
  · simp only [hfd, Option.map]
    dsimp only [Expr.eval]
    congr 1
    let ρ2 := Env.cons (t := sentEntryT ℓ Pt) (sentEntryEnc (ℓ := ℓ) (Pt := Pt) (ec, ev)) ρ1
    have hvr := senderToFreshVrAtomicE_eval (ℓ := ℓ) (Pt := Pt) (O' := AOps)
      (.snd .v0) ρ2 ev rfl
    have hsk0 : SkippedLenLe 0 ⟨ev.chainKey, ev.lastIndex, []⟩ := by simp [SkippedLenLe]
    have hfs := fsReceiveAtomicE_eval (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) idA idB 0 B
      (Γ := sentEntryT ℓ Pt :: t0 :: Γ)
      (senderToFreshVrAtomicE (.snd .v0)) (.snd (.snd .v1)) ρ2
      ⟨ev.chainKey, ev.lastIndex, []⟩ c' hvr rfl hsk0
    erw [hfs]
    have hsan0 : sanRS T ⟨ev.chainKey, ev.lastIndex, []⟩ = ⟨ev.chainKey, ev.lastIndex, []⟩ := by
      simp [sanRS]
    dsimp only [fsS, fsSan, fsClampSim, paramsV1, CryptoVerification.E2E.paramsIdsWithSpqr]
    rw [hsan0]
    rcases (lFS C protoSignalCodec ℓ encT (fun R => if R == .A then idA else idB) 25000).receive
        ⟨ev.chainKey, ev.lastIndex, []⟩ c'.1 c'.2 with _ | ⟨v', idx, p, m⟩ <;>
      simp [ρ2, ρ1, fig8CtV, Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]

theorem sentEvalAtomicE_cost (idA idB : IdentityKey) (L B : ℕ) {Γ : List (Ty ASig)}
    (sentE : Expr AOps Γ (.list (sentEntryT ℓ Pt)))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) idA idB L B sentE cE c'E).cost ≤
      sentE.cost + cE.cost + c'E.cost + L * (ℓ / 16 + 230) +
        3 * bits B + 16 * (ℓ / 32) + 220100000 := by
  let t0 := Ty.prod (.list (sentEntryT ℓ Pt))
    (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))
  let Γ1 := sentEntryT ℓ Pt :: t0 :: Γ
  have heq := eqFig8CAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.fst (.snd .v1))
  have hvr := senderToFreshVrAtomicE_cost (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) (.snd .v0)
  have hfs := fsReceiveAtomicE_cost (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 B (Γ := Γ1)
    (senderToFreshVrAtomicE (.snd .v0)) (.snd (.snd .v1))
  dsimp only [Expr.cost, Expr.v0, Expr.v1] at heq hvr
  have hmul : L * ((eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.fst (.snd .v1))).cost + 1) ≤
      L * (ℓ / 16 + 230) :=
    Nat.mul_le_mul_left L (by dsimp only [Expr.v0, Expr.v1]; omega)
  dsimp only [sentEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at heq hvr hfs hmul ⊢
  generalize eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) _ _ = e_eq at heq hmul ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 B (Γ := Γ1) _ _ = e_fs at hfs ⊢
  generalize senderToFreshVrAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ = e_vr at hvr hfs ⊢
  dsimp only [cost_eLet, Expr.cost] at hfs ⊢
  omega

end Fig8AtomicOps

/-! ## Description-bit bounds -/

section Fig8DescBits

section AtomicKeptBounds
set_option linter.unusedSimpArgs false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ADesc" => atomicSessionOpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
  (Dh := Dh) (encPt := encPt) (encT := encT) (decT := decT) (lam := lam)

@[local simp] private theorem ab_c0 : bits 0 = 1 := bits_zero
@[local simp] private theorem ab_c1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem ab_c2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem ab_c3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem ab_c32 : bits 32 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem ab_p32 : bits ((32 : ℕ+) : ℕ) = 6 := ab_c32

theorem optPtEqAtomicE_descBits_le {Γ : List (Ty ASig)} (a b : Expr AOps Γ (.opt PtT)) :
    atomicExprDescBits ADesc
      (optPtEqAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) a b) ≤
      atomicExprDescBits ADesc a + atomicExprDescBits ADesc b + 150 := by
  simp only [optPtEqAtomicE, descBits_eLet, descBits_opGroup, Expr.v0, Expr.v1, varIdx,
    atomicExprDescBits, Nat.reduceAdd, ab_c0, ab_c1]
  omega

theorem sameWireFig8AtomicE_descBits_le {Γ : List (Ty ASig)}
    (c1 c2 : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) c1 c2) ≤
      atomicExprDescBits ADesc c1 + atomicExprDescBits ADesc c2 + 800 := by
  let Γ1 := Ty.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  have hopt := optPtEqAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1)
    (.snd (.fst (.fst .v0))) (.snd (.fst (.snd .v0)))
  dsimp only [sameWireFig8AtomicE]
  generalize optPtEqAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) _ _ = e_opt at hopt ⊢
  simp only [descBits_eLet, descBits_opPure, atomicPureOpDescBits, Expr.v0, varIdx,
    atomicExprDescBits, ab_c0, ab_c32, ab_p32] at hopt ⊢
  omega

theorem eqFig8CAtomicE_descBits_le {Γ : List (Ty ASig)}
    (c1 c2 : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) c1 c2) ≤
      atomicExprDescBits ADesc c1 + atomicExprDescBits ADesc c2 + 1000 := by
  let Γ1 := Ty.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)) :: Γ
  have hsw := sameWireFig8AtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.snd .v0)
  dsimp only [eqFig8CAtomicE]
  generalize sameWireFig8AtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) (Γ := Γ1) _ _ = e_sw at hsw ⊢
  simp only [descBits_eLet, descBits_opPure, atomicPureOpDescBits, Expr.v0, varIdx,
    atomicExprDescBits, ab_c0] at hsw ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem senderToFreshVrAtomicE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (vE : Expr O' Γ (fsSendStT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits opB (senderToFreshVrAtomicE vE) ≤ atomicExprDescBits opB vE + 100 := by
  simp only [senderToFreshVrAtomicE, descBits_eLet, BV256, Expr.v0, varIdx,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, ab_c0]
  omega

theorem defaultMcAtomicE_descBits_le {Γ : List (Ty ASig)} :
    atomicExprDescBits ADesc
      (defaultMcAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)) ≤ 800 := by
  simp only [defaultMcAtomicE, descBits_opPure, atomicPureOpDescBits, B,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, List.length_nil,
    ab_c0, ab_c32, ab_p32]
  omega

theorem fig8InitAtomicE_descBits_le (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (k12E : Expr AOps Γ (.prod BV256 BV256)) :
    atomicExprDescBits ADesc
      (fig8InitAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB k12E) ≤
      atomicExprDescBits ADesc k12E + 500000 := by
  let Γ1 := Ty.prod (BV256 (ℓ := ℓ) (Pt := Pt)) BV256 :: Γ
  let Γ2 := Ty.prod (BV256 (ℓ := ℓ) (Pt := Pt)) BV256 :: Γ1
  have hlam := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ1)
    (lamIExpr ℓ Pt C Dh encPt encT lam) .unit
  have hup := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ1)
    (prngUpExpr ℓ Pt C Dh encPt encT lam)
    (.pair (.fst .v0) (runFig8WithIds idA idB (lamIExpr ℓ Pt C Dh encPt encT lam) .unit))
  have hcka := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (ckaInitAExpr ℓ Pt C Dh encPt encT lam) (.snd .v1)
  have hd_lam := lamIExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_up := prngUpExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_cka := ckaInitAExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have ht_fsS := atomicTyDescBits_fsSendStT (ℓ := ℓ) (Pt := Pt)
  have ht_fsR := atomicTyDescBits_fsRecvStT (ℓ := ℓ) (Pt := Pt)
  dsimp only [fig8InitAtomicE, f8Mk, Expr.v0, Expr.v1] at hlam hup hcka ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    _ = e_up at hup ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (lamIExpr ℓ Pt C Dh encPt encT lam)
    .unit = e_lam at hlam hup ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (ckaInitAExpr ℓ Pt C Dh encPt encT lam)
    _ = e_cka at hcka ⊢
  simp only [descBits_eLet, BV256, PtT, varIdx, atomicExprDescBits, atomicTyDescBits,
    atomicSortDescBits, Nat.reduceAdd, ab_c0, ab_c1] at hlam hup hcka ⊢
  omega

theorem fig8SendStepAtomicE_descBits_le (idA idB : IdentityKey) (B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (mcOptE : Expr AOps Γ (.opt (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256))) :
    atomicExprDescBits ADesc
      (fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B stE mcOptE) ≤
      atomicExprDescBits ADesc stE + atomicExprDescBits ADesc mcOptE +
        8 * bits B + 1500000 := by
  have hdef := defaultMcAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ)
  let t0 := Ty.prod (fig8StT (ℓ := ℓ) (Pt := Pt))
    (.prod (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT) BV256)
  let Γ1 := t0 :: Γ
  let Γ2 := Ty.prod (ckaStT (ℓ := ℓ) (Pt := Pt)) (.prod PtT PtT) :: Γ1
  let Γ3 := Ty.prod .bool
    (.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (.prod (lpubT (ℓ := ℓ) (Pt := Pt)) PlainT)) :: Γ1
  let Γ4 := fsSendStT (ℓ := ℓ) (Pt := Pt) :: Γ3
  have hcka := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ1)
    (ckaSendExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Gamma (.fst .v0)) (.snd (.snd .v0)))
  have hup := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (prngUpExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Root (.fst .v1)) (.snd (.snd .v0)))
  have hdefE := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3)
    (defaultEExpr ℓ Pt C Dh encPt encT lam) .unit
  have hfs := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ4)
    (fsSendExpr ℓ Pt C Dh encPt encT lam)
    (.pair .v0 (.pair (.pair (f8Tcur (.fst (.snd .v1))) (f8Cur (.fst (.snd .v1))))
      (.snd (.snd .v1))))
  have hd_cka := ckaSendExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_up := prngUpExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_defE := defaultEExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_fs := fsSendExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  dsimp only [fig8SendStepAtomicE, f8Mk, f8Id, f8Root, f8VS, f8VR, f8Gamma, f8Cur, f8Tcur,
    sendsInE, Expr.v0, Expr.v1, Expr.v2] at hcka hup hdefE hfs ⊢
  generalize defaultMcAtomicE (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) (Γ := Γ) = e_def at hdef ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ1) (ckaSendExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rcka at hcka ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rup at hup ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ3) (defaultEExpr ℓ Pt C Dh encPt encT lam)
    .unit = e_rdefE at hdefE ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ4) (fsSendExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rfs at hfs ⊢
  simp only [descBits_eLet, varIdx, atomicExprDescBits, Nat.reduceAdd,
    ab_c0, ab_c1, ab_c2] at hcka hup hdefE hfs ⊢
  omega

theorem fsReceiveAtomicE_descBits_le (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (vE : Expr AOps Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B0 B vE cE) ≤
      atomicExprDescBits ADesc vE + atomicExprDescBits ADesc cE +
        6 * bits B0 + 4 * bits B + 1800000 := by
  have hr := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ)
    (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B) (.pair vE cE)
  have hf := fsRecvExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam) B0 B
  simp only [fsReceiveAtomicE, atomicExprDescBits] at hr ⊢
  omega

theorem fig8ReceiveAtomicE_descBits_le (idA idB : IdentityKey) (B0 B : ℕ) {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt)))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB B0 B stE cE) ≤
      atomicExprDescBits ADesc stE + atomicExprDescBits ADesc cE +
        6 * bits B0 + 8 * bits B + 2500000 := by
  let t0 := Ty.prod (fig8StT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let Γ1 := t0 :: Γ
  let Γ2 := PtT (ℓ := ℓ) (Pt := Pt) :: Γ1
  let Γ3 := Ty.prod (ckaStT (ℓ := ℓ) (Pt := Pt)) PtT :: Γ2
  let Γ4 := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: fig8StT (ℓ := ℓ) (Pt := Pt) :: Γ1
  have hcka := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ2)
    (ckaRecvExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Gamma (.fst .v1)) .v0)
  have hup := descBits_runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB (Γ := Γ3)
    (prngUpExpr ℓ Pt C Dh encPt encT lam) (.pair (f8Root (.fst .v2)) (.snd .v0))
  have hfs := fsReceiveAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB B0 B (Γ := Γ4) .v0 (.snd .v2)
  have hd_cka := ckaRecvExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have hd_up := prngUpExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
  have ht_f8 := atomicTyDescBits_fig8StT (ℓ := ℓ) (Pt := Pt)
  dsimp only [fig8ReceiveAtomicE, f8Mk, f8Id, f8Root, f8VS, f8VR, f8Gamma, f8Cur, f8Tcur,
    orE, sendsInE, Expr.v0, Expr.v1, Expr.v2, Expr.v3] at hcka hup hfs ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ2) (ckaRecvExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rcka at hcka ⊢
  generalize runFig8WithIds (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB (Γ := Γ3) (prngUpExpr ℓ Pt C Dh encPt encT lam)
    _ = e_rup at hup ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB B0 B (Γ := Γ4) _ _ = e_rfs at hfs ⊢
  simp only [descBits_eLet, lpubT, PlainT, ReductionDsl.B, U32, BV256, varIdx,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd,
    ab_c0, ab_c1, ab_c2, ab_c3, ab_c32, ab_p32] at hcka hup hfs ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem sanRSAtomicE_descBits_le (T : ℕ) {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (vE : Expr O' Γ (fsRecvStT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits opB (sanRSAtomicE T vE) ≤
      atomicExprDescBits opB vE + 2 * bits T + 100 := by
  simp only [sanRSAtomicE, descBits_eLet, Expr.v0, varIdx, atomicExprDescBits, ab_c0]
  omega

theorem sanGammaAtomicE_descBits_le {Γ : List (Ty ASig)}
    (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (sanGammaAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) stE) ≤
      atomicExprDescBits ADesc stE + 700 := by
  simp only [sanGammaAtomicE, sendsInE, f8Id, f8Tcur, f8Gamma, descBits_eLet,
    descBits_opGroup, descBits_opPure, atomicPureOpDescBits, PtT, BV256, Expr.v0, varIdx,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, ab_c0, ab_c1, ab_c2]
  omega

theorem sanAtAtomicE_descBits_le (T : ℕ) {Γ : List (Ty ASig)}
    (tE : Expr AOps Γ .nat) (stE : Expr AOps Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) T tE stE) ≤
      atomicExprDescBits ADesc tE + atomicExprDescBits ADesc stE + 2 * bits T + 150000 := by
  let tP := Ty.prod .nat (fig8StT (ℓ := ℓ) (Pt := Pt))
  have hrs := sanRSAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) T ADesc
    (Γ := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tP :: Γ) .v0
  have hγ := sanGammaAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := tP :: Γ) (.snd .v0)
  have ht_fsR := atomicTyDescBits_fsRecvStT (ℓ := ℓ) (Pt := Pt)
  dsimp only [sanAtAtomicE, f8Mk, f8Id, f8Root, f8VS, f8VR, f8Cur, f8Tcur, Expr.v0] at hrs hγ ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T _ = e_rs at hrs ⊢
  generalize sanGammaAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) _ = e_g at hγ ⊢
  simp only [descBits_eLet, varIdx, atomicExprDescBits, ab_c0] at hrs hγ ⊢
  omega

omit [DecidableEq Pt] [Zero Pt] in
theorem keptOfStAtomicE_descBits_le {O' : Ops ASig} (opB : O'.Op → ℕ) {Γ : List (Ty ASig)}
    (stE : Expr O' Γ (fig8StT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits opB (keptOfStAtomicE stE) ≤ atomicExprDescBits opB stE + 80 := by
  simp only [keptOfStAtomicE, f8VR, descBits_eLet, Expr.v0, varIdx, atomicExprDescBits, ab_c0]
  omega

theorem keptSendAtomicE_descBits_le (idA idB : IdentityKey) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt)) :
    atomicExprDescBits ADesc
      (keptSendAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB kE) ≤
      atomicExprDescBits ADesc kE + 1650000 := by
  let Γ1 := fig8StT (ℓ := ℓ) (Pt := Pt) :: keptT ℓ Pt :: Γ
  have hstep := fig8SendStepAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 (Γ := Γ1) .v0 .none
  have ht_f8 := atomicTyDescBits_fig8StT (ℓ := ℓ) (Pt := Pt)
  dsimp only [keptSendAtomicE, sendsInE, f8Id, f8Tcur, f8VR, Expr.v0, Expr.v1] at hstep ⊢
  generalize fig8SendStepAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
    (decT := decT) (lam := lam) idA idB 0 (Γ := Γ1) _ _ = e_s at hstep ⊢
  simp only [descBits_eLet, lpubT, PlainT, ReductionDsl.B, U32, BV256, varIdx,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd,
    ab_c0, ab_c1, ab_c2, ab_c32, ab_p32] at hstep ⊢
  omega

theorem keptRecvAtomicE_descBits_le (idA idB : IdentityKey) (T : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (keptRecvAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB T kE cE) ≤
      atomicExprDescBits ADesc kE + atomicExprDescBits ADesc cE +
        16 * bits T + 5000000 := by
  let tKC := Ty.prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let ΓN := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  let ΓS := fig8StT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  have hrs := sanRSAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) T ADesc (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓN)
    (sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓS)
    (sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  have ht_f8 := atomicTyDescBits_fig8StT (ℓ := ℓ) (Pt := Pt)
  have ht_fsR := atomicTyDescBits_fsRecvStT (ℓ := ℓ) (Pt := Pt)
  dsimp only [keptRecvAtomicE, f8VR, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T 0 (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs at hrs hfs ⊢
  generalize sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  simp only [descBits_eLet, varIdx, atomicExprDescBits, Nat.reduceAdd,
    ab_c0, ab_c1, ab_c2] at hrs hfs hat hf8 ⊢
  omega

theorem keptEvalAtomicE_descBits_le (idA idB : IdentityKey) (T B : ℕ) {Γ : List (Ty ASig)}
    (kE : Expr AOps Γ (keptT ℓ Pt))
    (cE : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (keptEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB T B kE cE) ≤
      atomicExprDescBits ADesc kE + atomicExprDescBits ADesc cE +
        16 * bits T + 12 * bits B + 5000000 := by
  let tKC := Ty.prod (keptT ℓ Pt) (fig8CtT (ℓ := ℓ) (Pt := Pt))
  let ΓN := fsRecvStT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  let ΓS := fig8StT (ℓ := ℓ) (Pt := Pt) :: tKC :: Γ
  have hrs := sanRSAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) T ADesc (Γ := ΓN) .v0
  have hfs := fsReceiveAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓN)
    (sanRSAtomicE T .v0) (.snd .v1)
  have hat := sanAtAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) (.fst (.fst (.snd .v1))) .v0
  have hf8 := fig8ReceiveAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓS)
    (sanAtAtomicE T (.fst (.fst (.snd .v1))) .v0) (.snd .v1)
  dsimp only [keptEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at hrs hfs hat hf8 ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓN) _ _ = e_fs at hfs ⊢
  generalize fig8ReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB T B (Γ := ΓS) _ _ = e_f8 at hf8 ⊢
  generalize sanRSAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) T (Γ := ΓN) _ = e_rs at hrs hfs ⊢
  generalize sanAtAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) T (Γ := ΓS) _ _ = e_at at hat hf8 ⊢
  simp only [descBits_eLet, lpubT, PlainT, ReductionDsl.B, U32, BV256, varIdx,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd,
    ab_c0, ab_c1, ab_c2, ab_c32, ab_p32] at hrs hfs hat hf8 ⊢
  omega

theorem sentEvalAtomicE_descBits_le (idA idB : IdentityKey) (L B : ℕ) {Γ : List (Ty ASig)}
    (sentE : Expr AOps Γ (.list (sentEntryT ℓ Pt)))
    (cE c'E : Expr AOps Γ (fig8CtT (ℓ := ℓ) (Pt := Pt))) :
    atomicExprDescBits ADesc
      (sentEvalAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) idA idB L B sentE cE c'E) ≤
      atomicExprDescBits ADesc sentE + atomicExprDescBits ADesc cE +
        atomicExprDescBits ADesc c'E + 2 * bits L + 4 * bits B + 2200000 := by
  let t0 := Ty.prod (.list (sentEntryT ℓ Pt))
    (.prod (fig8CtT (ℓ := ℓ) (Pt := Pt)) (fig8CtT (ℓ := ℓ) (Pt := Pt)))
  let Γ1 := sentEntryT ℓ Pt :: t0 :: Γ
  have heq := eqFig8CAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) (.fst .v0) (.fst (.snd .v1))
  have hvr := senderToFreshVrAtomicE_descBits_le (ℓ := ℓ) (Pt := Pt) ADesc (Γ := Γ1) (.snd .v0)
  have hfs := fsReceiveAtomicE_descBits_le (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 B (Γ := Γ1)
    (senderToFreshVrAtomicE (.snd .v0)) (.snd (.snd .v1))
  dsimp only [sentEvalAtomicE, Expr.v0, Expr.v1, Expr.v2] at heq hvr hfs ⊢
  generalize eqFig8CAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (Γ := Γ1) _ _ = e_eq at heq ⊢
  generalize fsReceiveAtomicE (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) idA idB 0 B (Γ := Γ1) _ _ = e_fs at hfs ⊢
  generalize senderToFreshVrAtomicE (ℓ := ℓ) (Pt := Pt) (O' := AOps) (Γ := Γ1) _ = e_vr at hvr hfs ⊢
  simp only [descBits_eLet, lpubT, PlainT, ReductionDsl.B, U32, BV256, varIdx,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, Nat.reduceAdd,
    ab_c0, ab_c1, ab_c2, ab_c32, ab_p32] at heq hvr hfs ⊢
  omega

end AtomicKeptBounds

end Fig8DescBits

end Computational.Proofs.Game.PromotedCostedReds.SimFig8Kept
