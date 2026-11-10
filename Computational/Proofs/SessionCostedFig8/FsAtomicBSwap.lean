/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Fig8SchemeBridge
public import Computational.Proofs.CryptoGames.CKA.CKAProofDefs
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRNG.PRNGProofDefs
public import Computational.Proofs.E2E.SignedPrims
@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedFig8.FsAtomicBSwap

open CryptoVerification.LibsignalSession.Fig8SchemeBridge (badSendMsg_chall_false
  badSendMsg_query_bind_step badSendMsg_transmit_false ckaBranch_redCKAAuth_dhSchemeFb_eq
  ckaBranch_redCKAPriv_dhSchemeFb_eq mode_cfg_challMsg runFS_dhSchemeFb_eq runPRNG_dhSchemeFb_eq)

open OracleComp OracleSpec
open CryptoGames (Party AEADScheme CKAScheme PRFPRNG FSAEADScheme)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  lAead lPubOf lChainPRG lFS)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey maxForwardJumps)
open CryptoGames.SM (Record Config)
open CryptoGames.SM.Engine (Policy VP Ctx EState Hooks HooksVRInv SMEngineInv SMVRInv RSReach TComp
  vSend vSendStep1 vSend_eq_bind vRecv vRecvStep1 vRecv_eq_bind
  commitE abortE transmitE challE deliverE injectE corrE coinsE implE engRun
  run_liftH_bind epMgmt_st_eq implE_inv implE_vrInv)
open CryptoGames.SM.Construction (PartyState SchemeAdversary Header Mode CKAState PRNGState FSState
  FSVROkStep sampleT mkParties liftC liftF cacheC rootFS lookupF isExt extOf fsClamp
  hooksCKA hooksCKA_startRecv_rs hooksCKA_commit_vR initCKA initCKARaw initCKARaw_inv
  initCKARaw_vrInv runCKA runCKA_eq_bind_initCKARaw redCKAAuth redCKAPriv
  hooksPRNG hooksPRNG_startRecv_rs hooksPRNG_commit_vR initPRNG
  runPRNG redPRNGAuth redPRNGPriv
  hooksFS initFS initFSRaw initFSRaw_inv isQueryBoundP_initFSRaw_dec
  rootFS_ext extOf_ext vSend_ext_snd vRecvStep1_hooksFS_state implE_fsClamp_eq
  simulateQ_fsFullImpl_corruptSenderQuery simulateQ_fsFullImpl_corruptReceiverQuery
  hooksFS_vrInv_fromAEADPRG initFSRaw_vrInv_fromAEADPRG implE_ext_snd_fromAEADPRG
  receiverState_reach_of_isDecQuery_bound
  runFS runFS_eq_bind_initFSRaw redFSAuth redFSPriv redFSPrivCoin
  fsFullImpl fst_mem_support_of_mem_support_simulateQ_run simulateQ_runFS_fsClamp_fromAEADPRG)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.E2E.Signed (advAvg)
open _root_.ReductionDsl (Sig Ty Ops Iface Env Expr Comp GameCodec CostedReduction isGameQuery
  handlerImpl iterM findML anyML mapML consumeFirstML foldML
  atomicSig atomicFig8Ops BV128)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal mapEnvAux callMacroAux_eval)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv
  ckaAdvantage_congr prngAdvantage_congr fsaeadGame_evalDistEq_of_coinSimEquiv
  PureAuxBundle PureAuxAdapters sampleBoolFig8Comp
  callAdaptR_eval compilePureAuxExpr_eval compilePureAuxComp compilePureAuxRed)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb atomicShortPubB
  fsAtomicB fsAtomicB_send_eq fsAtomicB_receive_eq RSReachB)



section ExtraCKAAdv
variable {Pt KR RSt SS RS M E : Type}

theorem ckaAdvantage_redCKAAuth_dhSchemeFb_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType KR] [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka tStar qep : ℕ)
    (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    CryptoGames.CKA.advantage (dhSchemeFb Dh) Δcka tStar
      (redCKAAuth (dhSchemeFb Dh) prng fs lam Δcka qep tL t A) =
    CryptoGames.CKA.advantage (dhScheme Dh) Δcka tStar
      (redCKAAuth (dhScheme Dh) prng fs lam Δcka qep tL t A) := by
  rw [CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist,
    ckaBranch_redCKAAuth_dhSchemeFb_eq Dh prng fs lam Δcka tStar qep tL t true A,
    ckaBranch_redCKAAuth_dhSchemeFb_eq Dh prng fs lam Δcka tStar qep tL t false A]

theorem ckaAdvantage_redCKAPriv_dhSchemeFb_eq [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {K : Type} [SampleableType KR] [SampleableType K] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt K)
    (fs : FSAEADScheme K SS RS (Header Pt) M E) (lam : Pt) (Δcka tStar qep : ℕ)
    (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt SS RS M (BitVec 256) E) :
    CryptoGames.CKA.advantage (dhSchemeFb Dh) Δcka tStar
      (redCKAPriv (dhSchemeFb Dh) prng fs lam Δcka qep tL i A) =
    CryptoGames.CKA.advantage (dhScheme Dh) Δcka tStar
      (redCKAPriv (dhScheme Dh) prng fs lam Δcka qep tL i A) := by
  rw [CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist,
    ckaBranch_redCKAPriv_dhSchemeFb_eq Dh prng fs lam Δcka tStar qep tL i true A,
    ckaBranch_redCKAPriv_dhSchemeFb_eq Dh prng fs lam Δcka tStar qep tL i false A]

end ExtraCKAAdv

/-! ## FS-AEAD scheme swap -/

section FsAtomicBSwap

def SkippedLenLe {CK MK : Type} (v : CryptoGames.FSAEAD.RatchetReceiverState CK MK) : Prop :=
  v.skippedKeys.length ≤ v.lastIndex

lemma skippedLenLe_init {CK MK AD M C : Type}
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip : ℕ) (k : CK) :
    SkippedLenLe ((CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).initReceiver k) := by
  simp [SkippedLenLe, CryptoGames.FSAEAD.fromAEADPRG]

lemma skippedLenLe_receive {CK MK AD M C : Type}
    (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK))
    (maxSkip : ℕ) {v v' : CryptoGames.FSAEAD.RatchetReceiverState CK MK}
    {a : AD} {c : ℕ × C} {i : ℕ} {m : M}
    (hv : SkippedLenLe v)
    (hrec : (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).receive v a c = some (v', i, m)) :
    SkippedLenLe v' := by
  rcases c with ⟨idx, e⟩
  dsimp only [CryptoGames.FSAEAD.fromAEADPRG] at hrec
  rcases hlk : v.skippedKeys.lookup idx with _ | key
  · rw [hlk] at hrec
    split_ifs at hrec with hbad
    have hnot : ¬ idx ≤ v.lastIndex ∧ ¬ maxSkip < idx - v.lastIndex - 1 := not_or.mp hbad
    rcases hdec : ae.dec ((G (idx - 1)).gen
        (CryptoGames.FSAEAD.skipKeys G (idx - v.lastIndex - 1) v.chainKey v.lastIndex v.skippedKeys).1).2
        (idx, a) e with _ | m'
    · rw [hdec] at hrec; cases hrec
    · rw [hdec] at hrec
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl, rfl⟩
      dsimp only [SkippedLenLe] at hv ⊢
      rw [Computational.Proofs.ReductionDsl.Fig8Atomic.skipKeys_length]
      omega
  · rw [hlk] at hrec
    dsimp only at hrec
    rcases hdec : ae.dec key (idx, a) e with _ | m'
    · rw [hdec] at hrec; cases hrec
    · rw [hdec] at hrec
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
      rcases hrec with ⟨rfl, rfl, rfl⟩
      exact Nat.le_trans (List.length_filter_le _ _) hv

lemma rsReachB_len_le {CK MK : Type} {maxSkip k B0 : ℕ}
    (hB0 : (k + 1) * (maxSkip + 1) ≤ B0) {v : CryptoGames.FSAEAD.RatchetReceiverState CK MK}
    (hv : RSReachB maxSkip k v) : v.skippedKeys.length ≤ B0 := by
  have h1 := hv.1.1
  have h2 := hv.2
  have h3 : k * (maxSkip + 1) ≤ (k + 1) * (maxSkip + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_succ k)
  omega

/-- Agreement of two `Hooks` whose FS-AEAD operations agree on short headers and `≤ B0` skipped keys. -/
structure HooksLocalFsAgree {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ Pt RSt CCoins γV σV : Type} (ℓ B0 : ℕ)
    (hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)
      CCoins γV σV
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))) : Prop where
  startSend_eq : hk₁.startSend = hk₂.startSend
  startRecv_eq : hk₁.startRecv = hk₂.startRecv
  fsSend_eq : ∀ ctx P t ss hdr m pair, atomicShortPubB m.1 = true →
    hk₁.fsSend ctx P t ss hdr m pair = hk₂.fsSend ctx P t ss hdr m pair
  fsRecv_eq : ∀ ctx P t rs hdr e rec_, rs.skippedKeys.length ≤ B0 →
    hk₁.fsRecv ctx P t rs hdr e rec_ = hk₂.fsRecv ctx P t rs hdr e rec_
  commit_eq : hk₁.commit = hk₂.commit
  reveal_eq : hk₁.reveal = hk₂.reveal

lemma hooksCKA_vrInv_lFS {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (Δcka : ℕ) (mo : Mode) :
    HooksVRInv (RSReachB maxForwardJumps)
      (hooksCKA cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    hooksCKA_startRecv_rs cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo
      (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps) ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksCKA] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps _ hVR hmem.1.symm).2
  commit_vR := hooksCKA_commit_vR cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo

lemma hooksPRNG_vrInv_lFS {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (mo : Mode) :
    HooksVRInv (RSReachB maxForwardJumps)
      (hooksPRNG cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) mo) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σv Tn h :=
    hooksPRNG_startRecv_rs cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) mo
      (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps) ctx P t γ σv Tn h
  fsRecv_step _ _ _ rs hdr e _ _ res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksPRNG] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    exact (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.receive_fromAEADPRG
      ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps _ hVR hmem.1.symm).2
  commit_vR := hooksPRNG_commit_vR cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) mo

lemma hooksCKA_localFsAgree {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka : ℕ) (mo : Mode) :
    HooksLocalFsAgree ℓ B0
      (hooksCKA cka prng (fsAtomicB C ℓ encT idOf B0) Δcka mo)
      (hooksCKA cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo) where
  startSend_eq := by unfold hooksCKA fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  startRecv_eq := by unfold hooksCKA fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [hooksCKA]; rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [hooksCKA]; rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq := by unfold hooksCKA; rfl
  reveal_eq := by unfold hooksCKA; rfl

lemma hooksPRNG_localFsAgree {KC Γ CCoins Pt I KR RSt : Type}
    [DecidableEq Pt] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 : ℕ) (mo : Mode) :
    HooksLocalFsAgree ℓ B0
      (hooksPRNG cka prng (fsAtomicB C ℓ encT idOf B0) mo)
      (hooksPRNG cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) mo) where
  startSend_eq := by unfold hooksPRNG fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  startRecv_eq := by unfold hooksPRNG fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  fsSend_eq _ _ _ ss hdr m _ hm := by
    dsimp only [hooksPRNG]; rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss hdr m hm]
  fsRecv_eq _ _ _ rs hdr e _ hlen := by
    dsimp only [hooksPRNG]; rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs hdr e hlen]
  commit_eq := by unfold hooksPRNG; rfl
  reveal_eq := by unfold hooksPRNG; rfl


lemma vSend_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ Pt RSt CCoins γV σV : Type} {ℓ B0 : ℕ}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)
      CCoins γV σV
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂)
    (ctx : Ctx γV Pt σV (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (s : VP γV Pt σV (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
    (m : LibsignalMsgPublicPart × Plain ℓ)
    (pair : Option ((LibsignalMsgPublicPart × Plain ℓ) × (LibsignalMsgPublicPart × Plain ℓ)))
    (r : Option CCoins) (hm : atomicShortPubB m.1 = true) (h : HS) :
    (vSend hk₁ ctx P s m pair r).run h = (vSend hk₂ ctx P s m pair r).run h := by
  rw [vSend_eq_bind, vSend_eq_bind, StateT.run_bind, StateT.run_bind]
  have hStep1 : vSendStep1 hk₁ ctx P s r = vSendStep1 hk₂ ctx P s r := by
    unfold vSendStep1; rw [hAg.startSend_eq]
  rw [hStep1]
  refine bind_congr fun ⟨s₁?, h₁⟩ => ?_
  rcases s₁? with _ | s₁
  · rfl
  · rcases hvS : s₁.vS with _ | ss
    · simp only [hvS]
    · simp only [hvS, StateT.run_bind,
        hAg.fsSend_eq ctx P s₁.tcur ss (s₁.tcur, s₁.curCkaMsg) m pair hm]

lemma vRecv_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ Pt RSt CCoins γV σV : Type} {ℓ B0 k : ℕ}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)
      CCoins γV σV
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂)
    (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (k + 1) * (maxForwardJumps + 1) ≤ B0)
    (ctx : Ctx γV Pt σV (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (s : VP γV Pt σV (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
    (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec_ : Option (Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (h : HS)
    (hVR : ∀ t v, s.vR t = some v → RSReachB maxForwardJumps k v) :
    (vRecv hk₁ ctx P s c rec_).run h = (vRecv hk₂ ctx P s c rec_).run h := by
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1)) = true
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hStep1 : vRecvStep1 hk₁ ctx P s c = vRecvStep1 hk₂ ctx P s c := by
      unfold vRecvStep1; rw [hAg.startRecv_eq]
    rw [hStep1]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨s₁?, h₁⟩ hmem => ?_
    rcases s₁? with _ | (_ | s₁)
    · rfl
    · rfl
    · have hs₁VR : ∀ t v, s₁.vR t = some v → RSReachB maxForwardJumps k v := by
        unfold vRecvStep1 at hmem
        by_cases ht : c.1.1 = s.tcur + 1
        · simp only [ht, ↓reduceIte] at hmem
          rcases hTn : c.1.2 with _ | Tn
          · simp [hTn] at hmem
          · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem
            obtain ⟨⟨srRes, h'⟩, hsr, hmem⟩ := hmem
            rcases srRes with _ | _ | ⟨γ', σ', rs⟩
            · simp at hmem
            · simp at hmem
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq, Option.some.injEq] at hmem
              rcases hmem with ⟨rfl, rfl⟩
              intro t₀ v₀ hv₀
              by_cases ht₀ : t₀ = s.tcur + 1
              · subst ht₀
                simp only [Function.update_self, Option.some.injEq] at hv₀; subst hv₀
                exact hVRHk.mono (Nat.zero_le k)
                  (hVRHk.startRecv_step ctx P (s.tcur + 1) s.γ s.root Tn h
                    (some (some (γ', σ', rs)), h₁) hsr γ' σ' rs rfl)
              · simp only [Function.update_of_ne ht₀] at hv₀
                exact hVR t₀ v₀ hv₀
        · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, _⟩; exact hVR
      rcases hvRc : s₁.vR c.1.1 with _ | rs
      · simp [hvRc]
      · simp only [hvRc, StateT.run_bind,
          hAg.fsRecv_eq ctx P c.1.1 rs c.1 c.2 rec_ (rsReachB_len_le hB0 (hs₁VR c.1.1 rs hvRc))]

lemma implE_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ Pt RSt CCoins γV σV : Type} [DecidableEq Pt]
    {ℓ B0 B_q q' Δ qep : ℕ} {mo : Mode}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)
      CCoins γV σV
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂)
    (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP γV Pt σV (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (t : (CryptoGames.SM.spec (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (hBad : CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
      (St := PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) (.inr t) = false)
    (hVR : SMVRInv (RSReachB maxForwardJumps) B_q (q' + 1) es.g) :
    (implE hk₁ Δ qep maxForwardJumps mo.cfg mo.policy (.inr t)).run es =
      (implE hk₂ Δ qep maxForwardJumps mo.cfg mo.policy (.inr t)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (transmitE hk₁ Δ qep mo.policy (P, m, r)).run es =
      (transmitE hk₂ Δ qep mo.policy (P, m, r)).run es
    unfold transmitE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · rfl
      · by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
        · simp [hdoom]
        · have hm : atomicShortPubB m.1 = true :=
            badSendMsg_transmit_false
              (ok := fun (x : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB x.1) hBad
          simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
          exact congrArg (· >>= _) (vSend_localFs_eq hAg s₁ P (s₁.st P) m none r hm es.h)
  · change (challE hk₁ Δ qep mo.cfg mo.policy (P, m₀, m₁, r)).run es =
      (challE hk₂ Δ qep mo.cfg mo.policy (P, m₀, m₁, r)).run es
    obtain ⟨hm₀, hm₁⟩ := badSendMsg_chall_false hBad
    have hm : atomicShortPubB (if es.g.b then m₁ else m₀).1 = true := by
      cases es.g.b <;> simp [hm₀, hm₁]
    unfold challE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt Δ qep P r.isSome with _ | s₁
      · rfl
      · by_cases hch : (!(s₁.safeCh Δ P) || !((mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s₁.epoch P))) = true
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
          · simp [hdoom]
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, mode_cfg_challMsg, Option.getD_none,
              run_liftH_bind,
              vSend_localFs_eq hAg s₁ P (s₁.st P) (if es.g.b then m₁ else m₀) (some (m₀, m₁)) r hm es.h]
  · change (deliverE hk₁ maxForwardJumps mo.cfg (P, c)).run es =
      (deliverE hk₂ maxForwardJumps mo.cfg (P, c)).run es
    have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind,
          vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c (some r) es.h (hVR P), hCommit]
  · change (injectE hk₁ Δ qep mo.cfg (P, c)).run es =
      (injectE hk₂ Δ qep mo.cfg (P, c)).run es
    have hCommit : commitE hk₁ = commitE hk₂ := by unfold commitE; rw [hAg.commit_eq]
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj Δ)) = true
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        vRecv_localFs_eq hAg hVRHk hkB es.g P (es.g.st P) c none es.h (hVR P), hCommit]
  · change (corrE hk₁ mo.policy P).run es = (corrE hk₂ mo.policy P).run es
    unfold corrE; rw [hAg.reveal_eq]


lemma simulateQ_implE_localFs_eq {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {HS Γ Pt RSt CCoins γV σV α : Type} [DecidableEq Pt]
    {ℓ L B0 B_q q Δ qep : ℕ} {mo : Mode}
    {hk₁ hk₂ : Hooks TSpec HS Γ Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32)
      CCoins γV σV
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))}
    (hAg : HooksLocalFsAgree ℓ B0 hk₁ hk₂)
    (hVRHk : HooksVRInv (RSReachB maxForwardJumps) hk₂)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : OracleComp (unifSpec + CryptoGames.SM.spec
      (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) α}
    (hoa : oa.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) q)
    (hSendOk : oa.IsQueryBoundP
      (fun t => CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
        (St := PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
        (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP γV Pt σV (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)) HS)
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (RSReachB maxForwardJumps) B_q q es.g) :
    (simulateQ (implE hk₁ Δ qep maxForwardJumps mo.cfg mo.policy) oa).run es =
      (simulateQ (implE hk₂ Δ qep maxForwardJumps mo.cfg mo.policy) oa).run es := by
  induction oa using OracleComp.inductionOn generalizing q es with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ := badSendMsg_query_bind_step (fun m => atomicShortPubB m.1) qy mx hSendOk
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      have hInl1 : (implE hk₁ Δ qep maxForwardJumps mo.cfg mo.policy (.inl n)).run es =
          (coinsE n).run es := rfl
      have hInl2 : (implE hk₂ Δ qep maxForwardJumps mo.cfg mo.policy (.inl n)).run es =
          (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, _, _, rfl⟩ := hmem
      exact ih u (hmx u) (hSendMx u) _ hInv hVR
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      have hqp : 0 < q := hq0.resolve_left (by decide)
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [implE_localFs_eq hAg hVRHk hB0 es t_sm hBad hVR]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨u, es'⟩ hmem => ?_
      have hInv' := implE_inv hk₂ mo.cfg mo.policy es t_sm hInv (u, es') hmem
      have hVR' := implE_vrInv hk₂ hVRHk mo.cfg mo.policy es t_sm hInv hVR (u, es') hmem
      exact ih u (by simpa using hmx u) (hSendMx u) es' hInv' hVR'

theorem runCKA_fsAtomicB_eq_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (mo : Mode) (b : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary Γ Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    runCKA cka prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep mo b A =
      runCKA cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep mo b A := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) qAdv := by
    refine hA.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  rw [runCKA_eq_bind_initCKARaw, runCKA_eq_bind_initCKARaw]
  have hInitEq :
      initCKARaw cka prng (fsAtomicB C ℓ encT idOf B0) lam mo b =
        initCKARaw cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo b := by
    unfold initCKARaw fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  rw [hInitEq]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun es₀ hes₀ => ?_
  have hB1 : B_q + 1 ≤ B_q + 1 := le_rfl
  have hBB : B_q * B_q ≤ (B_q + 1) * (B_q + 1) :=
    Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  have ⟨hInv₀, _⟩ := initCKARaw_inv cka prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo b hqB hB1 hBB es₀ hes₀
  have hVRHk := hooksCKA_vrInv_lFS cka prng C ℓ encT idOf Δcka mo
  have hVR₀ := initCKARaw_vrInv (B := B_q) (qAdv := qAdv) cka prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo b
    (fun k => hVRHk.mono (Nat.zero_le _)
      (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
        ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps k)) es₀ hes₀
  change (simulateQ (implE _ (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) A).run es₀ >>= _ =
    (simulateQ (implE _ (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) A).run es₀ >>= _
  rw [simulateQ_implE_localFs_eq
    (hooksCKA_localFsAgree cka prng C ℓ encT idOf B0 Δcka mo)
    hVRHk hB0 hA' hSendOk es₀ hInv₀ hVR₀]

theorem runPRNG_fsAtomicB_eq_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt]
    [SampleableType KC] [SampleableType CCoins]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : I) (B0 B_q Δcka qep : ℕ) (mo : Mode) (b : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary Γ Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    runPRNG cka prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep mo b A =
      runPRNG cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka qep mo b A := by
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) qAdv := by
    refine hA.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  unfold runPRNG engRun
  have hInitEq :
      initPRNG cka prng (fsAtomicB C ℓ encT idOf B0) lam mo =
        initPRNG cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo := by
    unfold initPRNG fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  rw [hInitEq]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨vs, h⟩ hmem => ?_
  rcases vs with _ | ⟨vA, vB⟩
  · rfl
  · have hB1 : B_q + 1 ≤ B_q + 1 := le_rfl
    have hBB : B_q * B_q ≤ (B_q + 1) * (B_q + 1) :=
      Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
    let es₀ : EState (VP Γ Pt (Option RSt)
        (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ)
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
        (PRNGState Pt RSt (BitVec 256)) :=
      { g := { st := fun P => match P with | .A => vA | .B => vB, b := b }, h := h }
    have hInv₀ : SMEngineInv (B_q + 1) B_q qAdv es₀.g :=
      (CryptoGames.SM.Engine.SMEngineInv.init _ b hB1 hBB).mono hqB
    have hVRHk := hooksPRNG_vrInv_lFS cka prng C ℓ encT idOf mo
    have hVR₀ : SMVRInv (RSReachB maxForwardJumps) B_q qAdv es₀.g := by
      intro P t v hv
      unfold initPRNG at hmem
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨kc, _, ⟨rtRes, _⟩, _, hmem⟩ := hmem
      rcases rtRes with _ | ⟨σ, k⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        cases hmem.1
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
          Option.some.injEq] at hmem
        rcases Prod.mk.inj hmem.1.symm with ⟨rfl, rfl⟩
        cases P <;> simp only [es₀] at hv
        · split_ifs at hv with ht0
          · cases hv
            exact hVRHk.mono (Nat.zero_le _)
              (Computational.Proofs.ReductionDsl.Fig8Atomic.RSReachB.init
                ((lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
                (lChainPRG C.F) maxForwardJumps k)
        · cases hv
    dsimp only
    exact congrArg (· >>= fun res => pure (some res))
      (simulateQ_implE_localFs_eq
        (hooksPRNG_localFsAgree cka prng C ℓ encT idOf B0 mo)
        hVRHk hB0 hA' hSendOk es₀ hInv₀ hVR₀)


def OptSkippedLenLe {K MK : Type} : Option (CryptoGames.FSAEAD.RatchetReceiverState K MK) → Prop
  | none => True
  | some v => SkippedLenLe v

lemma fsOracleImpl_skippedLenLe {T K MK M C : Type} [DecidableEq T] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip : ℕ)
    (q : (CryptoGames.FSAEAD.spec (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C)).Domain)
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hSt : SkippedLenLe st.receiverState) :
    ∀ r ∈ support ((CryptoGames.FSAEAD.oracleImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) q).run st),
      SkippedLenLe r.2.receiverState := by
  intro r hr
  rcases q with (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | ⟨⟩) | ⟨⟩) | ⟨a, e⟩) | ⟨a, e⟩)
  · simp only [CryptoGames.FSAEAD.oracleImpl, QueryImpl.add_apply, CryptoGames.FSAEAD.transmitImpl, StateT.run_modifyGet,
      CryptoGames.FSAEAD.transmit, support_pure, Set.mem_singleton_iff] at hr
    subst hr; split <;> exact hSt
  · simp only [CryptoGames.FSAEAD.oracleImpl, QueryImpl.add_apply, CryptoGames.FSAEAD.challengeImpl, StateT.run_modifyGet,
      CryptoGames.FSAEAD.challenge, support_pure, Set.mem_singleton_iff] at hr
    subst hr; split <;> exact hSt
  · simp only [CryptoGames.FSAEAD.oracleImpl, QueryImpl.add_apply, CryptoGames.FSAEAD.corruptSenderImpl,
      StateT.run_modifyGet, CryptoGames.FSAEAD.corruptSender, support_pure, Set.mem_singleton_iff] at hr
    subst hr; split <;> exact hSt
  · simp only [CryptoGames.FSAEAD.oracleImpl, QueryImpl.add_apply, CryptoGames.FSAEAD.corruptReceiverImpl,
      StateT.run_modifyGet, CryptoGames.FSAEAD.corruptReceiver, support_pure, Set.mem_singleton_iff] at hr
    subst hr; split <;> exact hSt
  · simp only [CryptoGames.FSAEAD.oracleImpl, QueryImpl.add_apply, CryptoGames.FSAEAD.deliverImpl, StateT.run_modifyGet,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr
    change SkippedLenLe (CryptoGames.FSAEAD.deliver (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) st a e).2.receiverState
    unfold CryptoGames.FSAEAD.deliver CryptoGames.FSAEAD.State.removeFromTransit
    split
    · exact hSt
    · split
      · exact hSt
      · dsimp only
        rcases hrec : (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).receive st.receiverState a e with
          _ | ⟨rs', i', m'⟩
        · exact hSt
        · exact skippedLenLe_receive ae G maxSkip hSt hrec
  · simp only [CryptoGames.FSAEAD.oracleImpl, QueryImpl.add_apply, CryptoGames.FSAEAD.injectImpl, StateT.run_modifyGet,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr
    change SkippedLenLe (CryptoGames.FSAEAD.inject (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) st a e).2.receiverState
    unfold CryptoGames.FSAEAD.inject
    split_ifs
    · exact hSt
    · rcases hrec : (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).receive st.receiverState a e with
        _ | ⟨rs', i', m'⟩
      · exact hSt
      · exact skippedLenLe_receive ae G maxSkip hSt hrec

lemma fsFullImpl_skippedLenLe {T K MK M C α : Type} [DecidableEq T] [DecidableEq M] [DecidableEq C]
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip : ℕ)
    (oa : CryptoGames.FSAEAD.AdversaryComp (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK) (Header T) M (ℕ × C) α)
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hSt : SkippedLenLe st.receiverState) :
    ∀ r ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)) oa).run st),
      SkippedLenLe r.2.receiverState := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure _ =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hSt
  | query_bind q mx ih =>
    intro r hr
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, id_eq,
      StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    cases q with
    | inl m =>
      change u ∈ support
        ((liftM (OracleSpec.query (spec := unifSpec) m) : ProbComp _) >>=
          fun x => pure (x, st)) at hu
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hu
      obtain ⟨x, _, rfl⟩ := hu
      exact ih x st hSt r hr
    | inr oq =>
      change u ∈ support
        ((CryptoGames.FSAEAD.oracleImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) oq).run st) at hu
      exact ih u.1 u.2 (fsOracleImpl_skippedLenLe ae G maxSkip oq st hSt u hu) r hr

lemma hooksFS_vrInv_skippedLenLe
    {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka : ℕ) (mo : Mode) (j : ℕ) :
    HooksVRInv (fun _ => OptSkippedLenLe (K := K) (MK := MK))
      (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j) where
  mono _ hv := hv
  startRecv_step _ _ t γ σ Tn h res hmem γ' σ' rsv hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq; subst hEq
    unfold hooksFS at hmem; dsimp only at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    have hNonHon :
        (some (some (γ', σ', rsv)), h') ∈ support
          ((if (mo.auth && decide (t = mo.tStar)) = true then
              if (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true then pure none
              else do
                let k' ← lookupF (cka.receive γ Tn).2
                let ext ← isExt j (cka.receive γ Tn).2
                pure (some (some ((cka.receive γ Tn).1, (prng.up σ (cka.receive γ Tn).2).1,
                  if ext = true then none
                  else some ((CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).initReceiver k'))))
            else pure (some none) :
            CryptoGames.SM.Engine.HM (CryptoGames.FSAEAD.spec _ _ (Header T) M (ℕ × C)) _ _).run h) →
        OptSkippedLenLe rsv := by
      intro hmem'
      by_cases hc1 : (mo.auth && decide (t = mo.tStar)) = true
      · simp only [hc1, ↓reduceIte] at hmem'
        by_cases hc2 : (mo.tL.isSome && decide (mo.tStar = mo.tH)) = true
        · simp [hc2] at hmem'
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_pure,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some.injEq] at hmem'
          obtain ⟨⟨k', _⟩, _, ⟨ext, _⟩, _, ⟨_, _, hrsv⟩, _⟩ := hmem'
          subst hrsv
          cases ext <;> [exact skippedLenLe_init ae G maxSkip k'; trivial]
      · simp [hc1] at hmem'
    rcases hcache : h.cache t with _ | ⟨Tc, σc, k, ext⟩
    · simp only [hcache] at hmem; exact hNonHon hmem
    · by_cases hTc : Tc = Tn
      · simp only [hcache, hTc, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
        rcases hmem with ⟨⟨_, _, hrsv⟩, _⟩
        subst hrsv
        cases ext <;> [exact skippedLenLe_init ae G maxSkip k; trivial]
      · simp only [hcache, hTc, ↓reduceIte] at hmem; exact hNonHon hmem
  fsRecv_step _ _ _ rsv hdr e rec_ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq; subst hEq
    unfold hooksFS at hmem; dsimp only at hmem
    rcases rsv with _ | rs
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      rcases hext : h.ext with _ | ⟨ss, rs⟩
      · simp only [hext] at hmem
        split_ifs at hmem <;>
          (simp only [liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
             mem_support_bind_iff] at hmem;
           obtain ⟨qres, _, hmem⟩ := hmem;
           rcases qres with _ | (_ | ⟨i, mo'⟩);
           · simp at hmem;
           · simp at hmem;
           · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
             rcases mo' with _ | m;
             · rcases rec_ with _ | r;
               · simp at hmem;
               · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                   Prod.mk.injEq, Option.some.injEq] at hmem;
                 rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial;
             · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                 Prod.mk.injEq, Option.some.injEq] at hmem;
               rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial)
      · simp only [hext] at hmem
        rcases hrc : (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e with _ | ⟨rs', i, m⟩
        · simp [hrc] at hmem
        · simp only [hrc, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨⟨rfl, _, _⟩, _⟩; trivial
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at hmem
      rcases hmem with ⟨hmap, _⟩
      rcases hrc : (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e with _ | ⟨rs', i, m⟩
      · simp [hrc] at hmap
      · simp only [hrc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
        rcases hmap with ⟨rfl, rfl, rfl⟩
        exact skippedLenLe_receive ae G maxSkip hVR hrc
  commit_vR _ _ _ _ _ _ hmem _ hEq := by
    simp only [hooksFS, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; cases hEq; rfl


lemma fsFsRecv_ext_skippedLenLe
    {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M (ℕ × C))
    (P : Party) (t : ℕ) (rsv : Option (CryptoGames.FSAEAD.RatchetReceiverState K MK))
    (hdr : Header T) (e : ℕ × C) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSState T RSt K I (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C))
    (hExt : OptSkippedLenLe (h.ext.map Prod.snd)) :
    ∀ res ∈ support (((hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j).fsRecv
        ctx P t rsv hdr e rec_).run h),
      OptSkippedLenLe (res.2.ext.map Prod.snd) := by
  intro res hmem
  unfold hooksFS at hmem; dsimp only at hmem
  rcases rsv with _ | rs
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    rcases hext : h.ext with _ | ⟨ss, rs⟩
    · simp only [hext] at hmem
      split_ifs at hmem <;>
        (simp only [liftF, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
           mem_support_bind_iff] at hmem;
         obtain ⟨qres, _, hmem⟩ := hmem;
         rcases qres with _ | (_ | ⟨i, mo'⟩);
         · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
           subst hmem; simp [hext, OptSkippedLenLe];
         · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
           subst hmem; simp [hext, OptSkippedLenLe];
         · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hmem;
           rcases mo' with _ | m;
           · rcases rec_ with _ | r <;>
               (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
                subst hmem; simp [hext, OptSkippedLenLe]);
           · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem;
             subst hmem; simp [hext, OptSkippedLenLe])
    · simp only [hext] at hmem hExt
      rcases hrc : (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip).receive rs hdr e with _ | ⟨rs', i, m⟩
      · simp only [hrc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; simp [hext, OptSkippedLenLe]; exact hExt
      · simp only [hrc, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind, support_pure, Set.mem_singleton_iff] at hmem
        subst hmem; exact skippedLenLe_receive ae G maxSkip hExt hrc
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    subst hmem; exact hExt

lemma vRecv_ext_skippedLenLe
    {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M (ℕ × C))
    (P : Party)
    (s : VP Γ T RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK)))
    (c : Header T × (ℕ × C)) (rec_ : Option (Record M (Header T × (ℕ × C))))
    (h : FSState T RSt K I (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C))
    (hVR : ∀ t v, s.vR t = some v → FSVROkStep maxSkip k v)
    (hExt : OptSkippedLenLe (h.ext.map Prod.snd)) :
    ∀ res ∈ support
      ((vRecv (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          ctx P s c rec_).run h),
      OptSkippedLenLe (res.2.ext.map Prod.snd) := by
  intro ⟨vrRes, h'⟩ hmem
  rw [vRecv_eq_bind] at hmem
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hExt
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨s₁?, h₁⟩, hmem1, hmem2⟩ := hmem
    obtain ⟨hext₁, _⟩ := vRecvStep1_hooksFS_state cka prng ae G maxSkip k Δcka mo j
      ctx P s c h hVR (s₁?, h₁) hmem1
    have hExt₁ : OptSkippedLenLe (h₁.ext.map Prod.snd) := by rw [hext₁]; exact hExt
    rcases s₁? with _ | (_ | s₁)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; exact hExt₁
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
      rcases hmem2 with ⟨_, rfl⟩; exact hExt₁
    · rcases hvRc : s₁.vR c.1.1 with _ | v
      · simp only [hvRc, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem2
        rcases hmem2 with ⟨_, rfl⟩; exact hExt₁
      · simp only [hvRc, StateT.run_bind, mem_support_bind_iff] at hmem2
        obtain ⟨⟨fsRes, h₂⟩, hfs, hmem2⟩ := hmem2
        have hExt₂ := fsFsRecv_ext_skippedLenLe cka prng ae G maxSkip Δcka mo j
          ctx P c.1.1 v c.1 c.2 rec_ h₁ hExt₁ (fsRes, h₂) hfs
        rcases fsRes with _ | _ | ⟨v', i', m'⟩ <;>
          (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2;
           rcases hmem2 with ⟨_, rfl⟩; exact hExt₂)

lemma fsReveal_ext_skippedLenLe
    {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M (ℕ × C)) (P : Party)
    (vp : VP Γ T RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK)))
    (h : FSState T RSt K I (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C))
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hExt : OptSkippedLenLe (h.ext.map Prod.snd))
    (hSt : SkippedLenLe st.receiverState) :
    ∀ z ∈ support
      ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
        (((hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j).reveal ctx P vp).run
          h)).run st),
      OptSkippedLenLe (z.1.2.ext.map Prod.snd) := by
  have hcs : ∀ (st₀ : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK) (Header T) M (ℕ × C)),
      (CryptoGames.FSAEAD.corruptSender st₀).2.receiverState = st₀.receiverState := by
    intro st₀; unfold CryptoGames.FSAEAD.corruptSender; split_ifs <;> rfl
  have hcr : ∀ (st₀ : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK) (Header T) M (ℕ × C)) ss' rs',
      (CryptoGames.FSAEAD.corruptReceiver st₀).1 = some (ss', rs') → rs' = st₀.receiverState := by
    intro st₀ ss' rs'; unfold CryptoGames.FSAEAD.corruptReceiver; split_ifs <;> simp_all
  intro z hz
  simp only [hooksFS, pure_bind] at hz
  rcases hvS : vp.vS with _ | (_ | ss)
  · simp only [hvS] at hz
    rcases hvR : vp.vR mo.tStar with _ | (_ | rs')
    · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz; subst hz; exact hExt
    · simp only [hvR, StateT.run_bind, StateT.run_get, pure_bind] at hz
      rcases hext : h.ext with _ | ⟨ss₁, rs₁⟩
      · simp only [hext] at hz
        by_cases hauth : mo.auth = true
        · simp only [hauth, ↓reduceIte, StateT.run_pure, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hz; subst hz; simp [hext, OptSkippedLenLe]
        · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_fsFullImpl_corruptReceiverQuery, pure_bind] at hz
          rcases hcr_eq : (CryptoGames.FSAEAD.corruptReceiver st).1 with _ | ⟨ss', rs'⟩
          · simp only [hcr_eq, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hz; subst hz; simp [hext, OptSkippedLenLe]
          · simp only [hcr_eq, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; dsimp [OptSkippedLenLe]; rw [hcr st ss' rs' hcr_eq]; exact hSt
      · simp only [hext, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz; subst hz; exact hExt
    · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz; subst hz; exact hExt
  · simp only [hvS, StateT.run_bind, StateT.run_get, pure_bind] at hz
    rcases hext : h.ext with _ | ⟨ss₁, rs₁⟩
    · simp only [hext, StateT.run_bind, simulateQ_bind,
        simulateQ_fsFullImpl_corruptSenderQuery, pure_bind] at hz
      rcases hcs_eq : (CryptoGames.FSAEAD.corruptSender st).1 with _ | ss'
      · simp only [hcs_eq, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz; subst hz; simp [hext, OptSkippedLenLe]
      · simp only [hcs_eq, StateT.run_bind, StateT.run_modify, pure_bind] at hz
        rcases hvR : vp.vR mo.tStar with _ | (_ | rs')
        · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz; subst hz; simp [hext, OptSkippedLenLe]
        · simp only [hvR, hext, StateT.run_bind, StateT.run_get, pure_bind] at hz
          by_cases hauth : mo.auth = true
          · simp only [hauth, ↓reduceIte, StateT.run_pure, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hz; subst hz; simp [OptSkippedLenLe]
          · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
              simulateQ_fsFullImpl_corruptReceiverQuery, pure_bind] at hz
            rcases hcr_eq : (CryptoGames.FSAEAD.corruptReceiver (CryptoGames.FSAEAD.corruptSender st).2).1 with
              _ | ⟨ss'', rs''⟩
            · simp only [hcr_eq, StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hz; subst hz; simp [OptSkippedLenLe]
            · simp only [hcr_eq, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz; dsimp [OptSkippedLenLe]
              rw [hcr (CryptoGames.FSAEAD.corruptSender st).2 ss'' rs'' hcr_eq, hcs st]; exact hSt
        · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
            Set.mem_singleton_iff] at hz; subst hz; simp [hext, OptSkippedLenLe]
    · simp only [hext] at hz
      rcases hvR : vp.vR mo.tStar with _ | (_ | rs')
      · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz; subst hz; exact hExt
      · simp only [hvR, hext, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hExt
      · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz; subst hz; exact hExt
  · simp only [hvS] at hz
    rcases hvR : vp.vR mo.tStar with _ | (_ | rs')
    · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz; subst hz; exact hExt
    · simp only [hvR, StateT.run_bind, StateT.run_get, pure_bind] at hz
      rcases hext : h.ext with _ | ⟨ss₁, rs₁⟩
      · simp only [hext] at hz
        by_cases hauth : mo.auth = true
        · simp only [hauth, ↓reduceIte, StateT.run_pure, simulateQ_pure,
            support_pure, Set.mem_singleton_iff] at hz; subst hz; simp [hext, OptSkippedLenLe]
        · simp only [hauth, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, simulateQ_bind,
            simulateQ_fsFullImpl_corruptReceiverQuery, pure_bind] at hz
          rcases hcr_eq : (CryptoGames.FSAEAD.corruptReceiver st).1 with _ | ⟨ss', rs'⟩
          · simp only [hcr_eq, StateT.run_pure, simulateQ_pure, support_pure,
              Set.mem_singleton_iff] at hz; subst hz; simp [hext, OptSkippedLenLe]
          · simp only [hcr_eq, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz; dsimp [OptSkippedLenLe]; rw [hcr st ss' rs' hcr_eq]; exact hSt
      · simp only [hext, StateT.run_pure, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz; subst hz; exact hExt
    · simp only [hvR, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz; subst hz; exact hExt


lemma implE_hooksFS_ext_skippedLenLe
    {KC Γ CCoins T I KR RSt K MK M C : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip k Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (CryptoGames.FSAEAD.RatchetSenderState K))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (CryptoGames.FSAEAD.RatchetSenderState K)
        (CryptoGames.FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (q : (CryptoGames.SM.spec (PartyState Γ T RSt (CryptoGames.FSAEAD.RatchetSenderState K)
      (CryptoGames.FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState K) (CryptoGames.FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : OptSkippedLenLe (es.h.ext.map Prod.snd))
    (hSt : SkippedLenLe st.receiverState) :
    ∀ z ∈ support
      ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
        ((implE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (2 + Δcka) qep maxSkip mo.cfg mo.policy (.inr q)).run es)).run st),
      OptSkippedLenLe (z.1.2.h.ext.map Prod.snd) := by
  have hCommitEq : ∀ s₀ P₀ old₀ new₀ pos₀ (es₀ : EState _ M (Header T × (ℕ × C)) _),
      (commitE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        s₀ P₀ old₀ new₀ pos₀).run es₀ =
      pure (some (s₀.accept P₀ new₀ pos₀), es₀) := by
    intros; unfold commitE CryptoGames.SM.Engine.liftH hooksFS; simp [StateT.run]; rfl
  intro z hz
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((transmitE _ _ _ _ (P, m, r)).run es) at hmem
    unfold transmitE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
      · simp only [hep] at hmem
        by_cases hdoom : mo.policy.leakDoom es.g s₁
        · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt
        · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
            mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hext' := vSend_ext_snd cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
            Δcka mo j s₁ P (s₁.st P) m none r es.h (vsRes, h') hvs
          rcases vsRes with _ | ⟨stP, ct⟩ <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt)
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((challE _ _ _ _ _ (P, m₀, m₁, r)).run es) at hmem
    unfold challE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
      · simp only [hep] at hmem
        by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !((CryptoGames.SM.Construction.Mode.cfg (M := M) mo).challAllowedIn (s₁.epoch P)))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hdoom : mo.policy.leakDoom es.g s₁
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
            have hext' := vSend_ext_snd cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r es.h (vsRes, h') hvs
            rcases vsRes with _ | ⟨stP, ct⟩ <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
               rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt)
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((deliverE _ maxSkip _ (P, c)).run es) at hmem
    unfold deliverE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win)
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
      · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hExt' := vRecv_ext_skippedLenLe cka prng ae G maxSkip k Δcka mo j
          es.g P (es.g.st P) c (some r) es.h (hVR P) hExt (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨stP, t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · split_ifs at hmem <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; exact hExt')
        · simp only [StateT.run_bind, hCommitEq, pure_bind, StateT.run_modify,
            StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    rcases z with ⟨⟨out, es'⟩, st'⟩
    change (out, es') ∈ support ((injectE _ (2 + Δcka) qep _ (P, c)).run es) at hmem
    unfold injectE abortE at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases href :
        (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !(es.g.safeInj (2 + Δcka)))
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
      have hExt' := vRecv_ext_skippedLenLe cka prng ae G maxSkip k Δcka mo j
        es.g P (es.g.st P) c none es.h (hVR P) hExt (vrRes, h') hvr
      rcases vrRes with _ | _ | ⟨stP, t', i', m'⟩
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt'
      · by_cases hqep : qep + 1 < t'
        · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
        · simp only [hqep, ↓reduceIte] at hmem
          by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
          · simp only [htriv, ↓reduceIte, StateT.run_bind, hCommitEq, pure_bind,
              StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
          · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
            split_ifs at hmem <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
               rcases hmem with ⟨_, rfl⟩; exact hExt')
  · change z ∈ support ((simulateQ (fsFullImpl (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip))
      ((corrE (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        mo.policy P).run es)).run st) at hz
    unfold corrE abortE at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases href : (es.abort || es.g.win || !(es.g.corrAllowed P))
    · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hz; subst hz; exact hExt
    · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
      by_cases hdoom : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P)
      · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hExt
      · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind] at hz
        simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
        obtain ⟨⟨⟨revRes, h'⟩, st'⟩, hrev, hz⟩ := hz
        have hExt' := fsReveal_ext_skippedLenLe cka prng ae G maxSkip Δcka mo j
          es.g P (es.g.st P) es.h st hExt hSt ((revRes, h'), st') hrev
        rcases revRes with _ | stP <;>
          (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
             simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz;
           subst hz; exact hExt')


lemma vSend_hooksFS_fsClamp_fsAtomicB_eq
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B B0 Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (s : VP Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))))
    (m : LibsignalMsgPublicPart × Plain ℓ)
    (pair : Option ((LibsignalMsgPublicPart × Plain ℓ) × (LibsignalMsgPublicPart × Plain ℓ)))
    (r : Option CCoins) (hm : atomicShortPubB m.1 = true)
    (h : FSState Pt RSt (BitVec 256) I (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (ℕ × LibsignalCiphertextWithSalt32)) :
    (vSend (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        ctx P s m pair r).run h =
      (vSend (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        Δcka mo j) ctx P s m pair r).run h := by
  rw [vSend_eq_bind, vSend_eq_bind, StateT.run_bind, StateT.run_bind]
  have hStep1 :
      vSendStep1 (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        ctx P s r =
      vSendStep1 (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        Δcka mo j) ctx P s r := by
    unfold vSendStep1 hooksFS fsClamp fsAtomicB lFS CryptoGames.FSAEAD.fromAEADPRG; rfl
  rw [hStep1]
  refine bind_congr fun ⟨s₁?, h₁⟩ => ?_
  rcases s₁? with _ | s₁
  · rfl
  · rcases hvS : s₁.vS with _ | v
    · simp only [hvS]
    · simp only [hvS, StateT.run_bind]
      have hFsSend :
          ((hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j).fsSend
              ctx P s₁.tcur v (s₁.tcur, s₁.curCkaMsg) m pair).run h₁ =
            ((hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
              Δcka mo j).fsSend ctx P s₁.tcur v (s₁.tcur, s₁.curCkaMsg) m pair).run h₁ := by
        dsimp only [hooksFS, fsClamp]
        rcases v with _ | ss
        · simp only [StateT.run_bind, StateT.run_get, pure_bind]
          rcases h₁.ext with _ | ⟨ss', rs'⟩
          · rfl
          · dsimp only
            rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss' (s₁.tcur, s₁.curCkaMsg) m hm]
        · dsimp only
          rw [fsAtomicB_send_eq C ℓ encT idOf B0 ss (s₁.tcur, s₁.curCkaMsg) m hm]
      rw [hFsSend]

lemma vRecv_hooksFS_fsClamp_fsAtomicB_eq
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B B0 k Δcka : ℕ) (mo : Mode) (j : ℕ)
    (hB0 : (k + 1) * (maxForwardJumps + 1) ≤ B0)
    (ctx : Ctx Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (P : Party)
    (s : VP Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))))
    (c : Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
    (rec_ : Option (Record (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))))
    (h : FSState Pt RSt (BitVec 256) I (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (ℕ × LibsignalCiphertextWithSalt32))
    (hVR : ∀ t v, s.vR t = some v → FSVROkStep maxForwardJumps k v)
    (hLen : ∀ t v, s.vR t = some v → OptSkippedLenLe v)
    (hExt : FSVROkStep maxForwardJumps k (h.ext.map Prod.snd))
    (hExtLen : OptSkippedLenLe (h.ext.map Prod.snd)) :
    (vRecv (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        ctx P s c rec_).run h =
      (vRecv (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        Δcka mo j) ctx P s c rec_).run h := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  rw [vRecv_eq_bind, vRecv_eq_bind]
  by_cases href : (s.id.sendsIn c.1.1 || decide (s.tcur + 1 < c.1.1))
  · simp [href]
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    have hStep1 :
        vRecvStep1 (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
          ctx P s c =
        vRecvStep1 (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
          ctx P s c := by
      unfold vRecvStep1 hooksFS fsClamp fsAtomicB; rfl
    have hStep2 :
        vRecvStep1 (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
          Δcka mo j) ctx P s c =
        vRecvStep1 (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
          ctx P s c := by
      unfold vRecvStep1 hooksFS fsClamp lFS; rfl
    rw [hStep1, hStep2]
    refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨s₁?, h₁⟩ hmem => ?_
    obtain ⟨hext₁, hVR₁⟩ := vRecvStep1_hooksFS_state cka prng ae G maxForwardJumps k Δcka mo j
      ctx P s c h hVR (s₁?, h₁) hmem
    rcases s₁? with _ | (_ | s₁)
    · rfl
    · rfl
    · have hs₁Len : ∀ t v, s₁.vR t = some v → OptSkippedLenLe v := by
        unfold vRecvStep1 at hmem
        by_cases ht : c.1.1 = s.tcur + 1
        · simp only [ht, ↓reduceIte] at hmem
          rcases hTn : c.1.2 with _ | Tn
          · simp [hTn] at hmem
          · simp only [hTn, StateT.run_bind, mem_support_bind_iff] at hmem
            obtain ⟨⟨srRes, h'⟩, hsr, hmem⟩ := hmem
            rcases srRes with _ | _ | ⟨γ', σ', rs⟩
            · simp at hmem
            · simp at hmem
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq, Option.some.injEq] at hmem
              rcases hmem with ⟨rfl, rfl⟩
              intro t₀ v₀ hv₀
              by_cases ht₀ : t₀ = s.tcur + 1
              · subst ht₀
                simp only [Function.update_self, Option.some.injEq] at hv₀; subst hv₀
                exact (hooksFS_vrInv_skippedLenLe cka prng ae G maxForwardJumps Δcka mo j).startRecv_step
                  ctx P (s.tcur + 1) s.γ s.root Tn h (some (some (γ', σ', rs)), h₁) hsr γ' σ' rs rfl
              · simp only [Function.update_of_ne ht₀] at hv₀; exact hLen t₀ v₀ hv₀
        · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hmem
          rcases hmem with ⟨rfl, _⟩; exact hLen
      rcases hvRc : s₁.vR c.1.1 with _ | v
      · simp [hvRc]
      · simp only [hvRc, StateT.run_bind]
        have hFsRecv :
            ((hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j).fsRecv
                ctx P c.1.1 v c.1 c.2 rec_).run h₁ =
              ((hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
                Δcka mo j).fsRecv ctx P c.1.1 v c.1 c.2 rec_).run h₁ := by
          dsimp only [hooksFS, fsClamp]
          rcases v with _ | rs
          · simp only [StateT.run_bind, StateT.run_get, pure_bind]
            rcases hext₁' : h₁.ext with _ | ⟨ss', rs'⟩
            · rfl
            · have hE1 : FSVROkStep maxForwardJumps k (h₁.ext.map Prod.snd) := hext₁ ▸ hExt
              have hE2 : OptSkippedLenLe (h₁.ext.map Prod.snd) := hext₁ ▸ hExtLen
              rw [hext₁'] at hE1 hE2
              have hlen : rs'.skippedKeys.length ≤ B0 := rsReachB_len_le hB0 ⟨hE1, hE2⟩
              dsimp only
              rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs' c.1 c.2 hlen]
          · have hR1 := hVR₁ s₁ rfl c.1.1 (some rs) hvRc
            have hR2 := hs₁Len c.1.1 (some rs) hvRc
            have hlen : rs.skippedKeys.length ≤ B0 := rsReachB_len_le hB0 ⟨hR1, hR2⟩
            dsimp only
            rw [fsAtomicB_receive_eq C ℓ encT idOf B0 rs c.1 c.2 hlen]
        rw [hFsRecv]


lemma implE_hooksFS_fsClamp_fsAtomicB_eq
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B B0 B_q q' Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (es : EState (VP Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))))
      (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSState Pt RSt (BitVec 256) I (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (ℕ × LibsignalCiphertextWithSalt32)))
    (t : (CryptoGames.SM.spec (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))).Domain)
    (hBad : CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
      (St := PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (fun m => atomicShortPubB m.1) (.inr t) = false)
    (hVR : SMVRInv (FSVROkStep maxForwardJumps) B_q (q' + 1) es.g)
    (hLen : SMVRInv (fun _ => OptSkippedLenLe) B_q (q' + 1) es.g)
    (hExt : FSVROkStep maxForwardJumps (B_q - (q' + 1)) (es.h.ext.map Prod.snd))
    (hExtLen : OptSkippedLenLe (es.h.ext.map Prod.snd)) :
    (implE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr t)).run es =
      (implE (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
        Δcka mo j) (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr t)).run es := by
  have hkB : (B_q - (q' + 1) + 1) * (maxForwardJumps + 1) ≤ B0 :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB0
  rcases t with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change (transmitE _ _ _ _ (P, m, r)).run es = (transmitE _ _ _ _ (P, m, r)).run es
    unfold transmitE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · rfl
      · by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
        · simp [hdoom]
        · have hm : atomicShortPubB m.1 = true :=
            badSendMsg_transmit_false
              (ok := fun (x : LibsignalMsgPublicPart × Plain ℓ) => atomicShortPubB x.1) hBad
          simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind]
          exact congrArg (· >>= _)
            (vSend_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 Δcka mo j
              s₁ P (s₁.st P) m none r hm es.h)
  · change (challE _ _ _ _ _ (P, m₀, m₁, r)).run es = (challE _ _ _ _ _ (P, m₀, m₁, r)).run es
    obtain ⟨hm₀, hm₁⟩ := badSendMsg_chall_false hBad
    have hm : atomicShortPubB (if es.g.b then m₁ else m₀).1 = true := by
      cases es.g.b <;> simp [hm₀, hm₁]
    unfold challE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · rfl
      · by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !((mo.cfg (M := LibsignalMsgPublicPart × Plain ℓ)).challAllowedIn (s₁.epoch P))) = true
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ↓reduceIte]
          by_cases hdoom : mo.policy.leakDoom es.g s₁ = true
          · simp [hdoom]
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, mode_cfg_challMsg, Option.getD_none,
              run_liftH_bind,
              vSend_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 Δcka mo j
                s₁ P (s₁.st P) (if es.g.b then m₁ else m₀) (some (m₀, m₁)) r hm es.h]
  · change (deliverE _ maxForwardJumps mo.cfg (P, c)).run es =
      (deliverE _ maxForwardJumps mo.cfg (P, c)).run es
    have hCommit :
        commitE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j) =
          commitE (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j) := by
      unfold commitE hooksFS; rfl
    unfold deliverE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hab : (es.abort || es.g.win) = true
    · simp [hab]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · rfl
      · simp only [run_liftH_bind,
          vRecv_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 (B_q - (q' + 1))
            Δcka mo j hkB es.g P (es.g.st P) c (some r) es.h (hVR P) (hLen P) hExt hExtLen, hCommit]
  · change (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es =
      (injectE _ (2 + Δcka) qep mo.cfg (P, c)).run es
    have hCommit :
        commitE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j) =
          commitE (hooksFS cka prng (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j) := by
      unfold commitE hooksFS; rfl
    unfold injectE
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases href : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
        !(es.g.safeInj (2 + Δcka))) = true
    · simp [href]
    · simp only [href, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
        vRecv_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf B B0 (B_q - (q' + 1))
          Δcka mo j hkB es.g P (es.g.st P) c none es.h (hVR P) (hLen P) hExt hExtLen, hCommit]
  · change (corrE _ mo.policy P).run es = (corrE _ mo.policy P).run es
    unfold corrE hooksFS; rfl

lemma simulateQ_implE_fsClamp_fsAtomicB_eq
    {KC Γ CCoins Pt I KR RSt α : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (L B B0 B_q q Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    {oa : OracleComp (unifSpec + CryptoGames.SM.spec
      (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))) α}
    (hoa : oa.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) q)
    (hSendOk : oa.IsQueryBoundP
      (fun t => CryptoGames.LibsignalSM.Proofs.SessionShort.badSendMsg
        (St := PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (Coins := CCoins) (C := Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
        (fun m => atomicShortPubB m.1) t = true) 0)
    (es : EState (VP Γ Pt RSt (Option (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256)))
      (Option (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))))
      (LibsignalMsgPublicPart × Plain ℓ)
      (Header Pt × (ℕ × LibsignalCiphertextWithSalt32))
      (FSState Pt RSt (BitVec 256) I (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
        (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
        (ℕ × LibsignalCiphertextWithSalt32)))
    (st : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (FSVROkStep maxForwardJumps) B_q q es.g)
    (hLen : SMVRInv (fun _ => OptSkippedLenLe) B_q q es.g)
    (hExt : FSVROkStep maxForwardJumps (B_q - q) (es.h.ext.map Prod.snd))
    (hExtLen : OptSkippedLenLe (es.h.ext.map Prod.snd))
    (hSt : RSReach maxForwardJumps (B_q - q) st.receiverState)
    (hStLen : SkippedLenLe st.receiverState) :
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      ((simulateQ (implE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) oa).run es)).run st =
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      ((simulateQ (implE (hooksFS cka prng
        (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
        (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy) oa).run es)).run st := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  induction oa using OracleComp.inductionOn generalizing q es st with
  | pure _ => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    rcases hoa with ⟨hq0, hmx⟩
    obtain ⟨hBad, hSendMx⟩ := badSendMsg_query_bind_step (fun m => atomicShortPubB m.1) qy mx hSendOk
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]
    simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hmx
      have hInl1 :
          (implE (hooksFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inl n)).run es =
            (coinsE n).run es := rfl
      have hInl2 :
          (implE (hooksFS cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inl n)).run es =
            (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      obtain ⟨_, _, _, rfl⟩ := hmem1
      have hQbCoins := CryptoGames.SM.Construction.ReductionsQueries.qb_coinsE
        (CryptoGames.SM.Construction.ReductionsQueries.hQu_QFSDec (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) n es'
      have hSt' : RSReach maxForwardJumps (B_q - q) st'.receiverState := by
        simpa using receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps
          hQbCoins st hSt ((u, es'), st') hmem
      have hStLen' : SkippedLenLe st'.receiverState :=
        fsFullImpl_skippedLenLe ae G maxForwardJumps ((coinsE n).run es') st hStLen
          ((u, es'), st') hmem
      exact ih u q (hmx u) (hSendMx u) es' st' hInv hVR hLen hExt hExtLen hSt' hStLen'
    · simp only [ReductionDsl.isGameQuery, ↓reduceIte] at hq0 hmx
      have hqp : 0 < q := hq0.resolve_left (by decide)
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hStep1 := implE_hooksFS_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf
        B B0 B_q q' Δcka qep mo j hB0 es t_sm hBad hVR hLen hExt hExtLen
      have hStep2 :
          (implE (hooksFS cka prng
              (fsClamp B (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr t_sm)).run es =
            (implE (hooksFS cka prng
              (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) Δcka mo j)
              (2 + Δcka) qep maxForwardJumps mo.cfg mo.policy (.inr t_sm)).run es :=
        implE_fsClamp_eq cka prng ae G maxForwardJumps B B_q q' Δcka qep mo j hB es t_sm hVR hExt
      rw [hStep1, hStep2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      have hInv' := implE_inv
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
        mo.cfg mo.policy es t_sm hInv (u, es') hmem1
      have hVR' := implE_vrInv
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
        (hooksFS_vrInv_fromAEADPRG cka prng ae G maxForwardJumps Δcka mo j)
        mo.cfg mo.policy es t_sm hInv hVR (u, es') hmem1
      have hLen' := implE_vrInv
        (hooksFS cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka mo j)
        (hooksFS_vrInv_skippedLenLe cka prng ae G maxForwardJumps Δcka mo j)
        mo.cfg mo.policy es t_sm hInv hLen (u, es') hmem1
      have hBq : B_q - (q' + 1) + 1 ≤ B_q - q' := by have := hInv.1; omega
      have hExt' := (implE_ext_snd_fromAEADPRG cka prng ae G maxForwardJumps (B_q - (q' + 1))
        Δcka qep mo j es t_sm st (fun P _ _ hv => hVR P _ _ hv) hExt hSt
        ((u, es'), st') hmem).mono hBq
      have hExtLen' := implE_hooksFS_ext_skippedLenLe cka prng ae G maxForwardJumps
        (B_q - (q' + 1)) Δcka qep mo j es t_sm st (fun P _ _ hv => hVR P _ _ hv)
        hExtLen hStLen ((u, es'), st') hmem
      have hQbStep := CryptoGames.SM.Construction.ReductionsQueries.qb_implE_inr_one
        (CryptoGames.SM.Construction.ReductionsQueries.hQu_QFSDec (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) Pt
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (CryptoGames.SM.Construction.ReductionsQueries.hQt_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQch_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQcs_QFSDec _ _ Pt _ _)
        (CryptoGames.SM.Construction.ReductionsQueries.hQcr_QFSDec _ _ Pt _ _)
        cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) Δcka qep mo j t_sm es
      have hSt' := (receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps hQbStep st hSt
        ((u, es'), st') hmem).mono hBq
      have hStLen' := fsFullImpl_skippedLenLe ae G maxForwardJumps _ st hStLen ((u, es'), st') hmem
      exact ih u q' (by simpa using hmx u) (hSendMx u) es' st'
        hInv' hVR' hLen' hExt' hExtLen' hSt' hStLen'


lemma initFSRaw_skippedLenLe
    {KC Γ CCoins T I KR RSt K MK M C : Type} [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C)
    (G : ℕ → PRGScheme K (K × MK)) (maxSkip : ℕ)
    (lam : I) (mo : Mode) (j : ℕ) (b : Bool) (B_q qAdv : ℕ) :
    ∀ es₀ ∈ support (initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxSkip) lam mo j b),
      SMVRInv (fun _ => OptSkippedLenLe) B_q qAdv es₀.g := by
  intro es₀ hmem
  unfold initFSRaw at hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kr, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨kc, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨⟨σ, k, sid⟩, h₁⟩, _, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem; obtain ⟨⟨ext, h₂⟩, _, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hmem; subst hmem
  intro P t v hv
  cases P <;> simp only [mkParties] at hv
  · by_cases ht0 : t = 0
    · simp only [ht0, ↓reduceIte, Option.some.injEq] at hv; subst hv
      cases ext <;> [exact skippedLenLe_init ae G maxSkip k; trivial]
    · simp [ht0] at hv
  · cases hv

theorem simulateQ_runFS_fsClamp_fsAtomicB_eq_lFS
    {KC Γ CCoins Pt I KR RSt : Type} [DecidableEq Pt] [DecidableEq I]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    (cka : CKAScheme KC Γ CCoins Pt I) (prng : PRFPRNG KR RSt I (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B B0 B_q Δcka qep : ℕ) (lam : I) (mo : Mode) (j : ℕ) (b : Bool)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary Γ Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) CCoins
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A)
    (st₀ : CryptoGames.FSAEAD.State (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (hSt₀ : RSReach maxForwardJumps 0 st₀.receiverState)
    (hStLen₀ : SkippedLenLe st₀.receiverState) :
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      (runFS cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam Δcka qep mo j b A)).run st₀ =
    (simulateQ (fsFullImpl (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps))
      (runFS cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep mo j b A)).run st₀ := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  have hA' : A.IsQueryBoundP
      (ReductionDsl.isGameQuery (G := CryptoGames.SM.spec
        (PartyState Γ Pt RSt (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
          (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)))
        (LibsignalMsgPublicPart × Plain ℓ) CCoins
        (Header Pt × (ℕ × LibsignalCiphertextWithSalt32)))) qAdv := by
    refine hA.of_imp fun x hx => ?_
    rcases x with _ | _ <;> simp_all [ReductionDsl.isGameQuery]
  rw [runFS_eq_bind_initFSRaw, runFS_eq_bind_initFSRaw]
  have hInitEq :
      initFSRaw cka prng (fsClamp B (fsAtomicB C ℓ encT idOf B0)) lam mo j b =
        initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b := by
    unfold initFSRaw fsClamp fsAtomicB; rfl
  have hInitEq2 :
      initFSRaw cka prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam mo j b =
        initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b := by
    unfold initFSRaw lFS; rfl
  rw [hInitEq, hInitEq2, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨es₀, st₁⟩ hmem₀ => ?_
  have hes₀ := fst_mem_support_of_mem_support_simulateQ_run _ _ st₀ hmem₀
  have hB1 : B_q + 1 ≤ B_q + 1 := le_rfl
  have hBB : B_q * B_q ≤ (B_q + 1) * (B_q + 1) :=
    Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b
    hqB hB1 hBB es₀ hes₀
  have ⟨hVR₀, hext₀⟩ := initFSRaw_vrInv_fromAEADPRG cka prng ae G maxForwardJumps lam mo j b
    B_q qAdv es₀ hes₀
  have hLen₀ := initFSRaw_skippedLenLe cka prng ae G maxForwardJumps lam mo j b B_q qAdv es₀ hes₀
  have hExt₀ : FSVROkStep maxForwardJumps (B_q - qAdv) (es₀.h.ext.map Prod.snd) := by
    simp [hext₀, FSVROkStep]
  have hExtLen₀ : OptSkippedLenLe (es₀.h.ext.map Prod.snd) := by simp [hext₀, OptSkippedLenLe]
  have hSt₁ : RSReach maxForwardJumps (B_q - qAdv) st₁.receiverState :=
    (receiverState_reach_of_isDecQuery_bound ae G maxForwardJumps
      (isQueryBoundP_initFSRaw_dec cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b)
      st₀ hSt₀ (es₀, st₁) hmem₀).mono (Nat.zero_le _)
  have hStLen₁ : SkippedLenLe st₁.receiverState :=
    fsFullImpl_skippedLenLe ae G maxForwardJumps
      (initFSRaw cka prng (CryptoGames.FSAEAD.fromAEADPRG ae G maxForwardJumps) lam mo j b) st₀ hStLen₀
      (es₀, st₁) hmem₀
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  have hSim := simulateQ_implE_fsClamp_fsAtomicB_eq cka prng C ℓ encT idOf
    (B_q + 1) B B0 B_q qAdv Δcka qep mo j hB hB0 hA' hSendOk es₀ st₁
    hInv₀.sm hVR₀ hLen₀ hExt₀ hExtLen₀ hSt₁ hStLen₁
  have hms1 : (fsClamp B (fsAtomicB C ℓ encT idOf B0)).maxSkip = maxForwardJumps := rfl
  have hms2 : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).maxSkip = maxForwardJumps := rfl
  rw [hms1, hms2, hSim]

end FsAtomicBSwap

/-! ## Combined CKA and FS-AEAD scheme swap -/

section CombinedAtomicSwap

variable {Pt KR RSt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] [SampleableType KR]

theorem ckaBranch_redCKAAuth_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka tStar qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.CKA.branch (dhSchemeFb Dh) Δcka tStar b
      (redCKAAuth (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A) =
    CryptoGames.CKA.branch (dhScheme Dh) Δcka tStar b
      (redCKAAuth (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A) := by
  have hFs :
      redCKAAuth (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A =
        redCKAAuth (dhSchemeFb Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          lam Δcka qep tL t A := by
    unfold redCKAAuth
    rw [runCKA_fsAtomicB_eq_lFS (dhSchemeFb Dh) prng C ℓ encT idOf lam B0 B_q Δcka qep
      ⟨true, tL, t⟩ false hB0 A qAdv hA hqB hSendOk]
  rw [hFs]
  exact ckaBranch_redCKAAuth_dhSchemeFb_eq Dh prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka tStar qep tL t b A

theorem ckaAdvantage_redCKAAuth_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka tStar qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.CKA.advantage (dhSchemeFb Dh) Δcka tStar
      (redCKAAuth (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A) =
    CryptoGames.CKA.advantage (dhScheme Dh) Δcka tStar
      (redCKAAuth (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A) := by
  rw [CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist,
    ckaBranch_redCKAAuth_atomic_eq Dh prng C ℓ encT idOf lam B0 B_q Δcka tStar qep
      tL t true hB0 A qAdv hA hqB hSendOk,
    ckaBranch_redCKAAuth_atomic_eq Dh prng C ℓ encT idOf lam B0 B_q Δcka tStar qep
      tL t false hB0 A qAdv hA hqB hSendOk]

theorem ckaBranch_redCKAPriv_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka tStar qep : ℕ) (tL : Option ℕ) (i : ℕ) (b : Bool)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.CKA.branch (dhSchemeFb Dh) Δcka tStar b
      (redCKAPriv (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL i A) =
    CryptoGames.CKA.branch (dhScheme Dh) Δcka tStar b
      (redCKAPriv (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL i A) := by
  have hFs :
      redCKAPriv (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL i A =
        redCKAPriv (dhSchemeFb Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
          lam Δcka qep tL i A := by
    unfold redCKAPriv
    refine bind_congr fun bSM => ?_
    rw [runCKA_fsAtomicB_eq_lFS (dhSchemeFb Dh) prng C ℓ encT idOf lam B0 B_q Δcka qep
      ⟨false, tL, i⟩ bSM hB0 A qAdv hA hqB hSendOk]
  rw [hFs]
  exact ckaBranch_redCKAPriv_dhSchemeFb_eq Dh prng
    (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) lam Δcka tStar qep tL i b A

theorem ckaAdvantage_redCKAPriv_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka tStar qep : ℕ) (tL : Option ℕ) (i : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.CKA.advantage (dhSchemeFb Dh) Δcka tStar
      (redCKAPriv (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL i A) =
    CryptoGames.CKA.advantage (dhScheme Dh) Δcka tStar
      (redCKAPriv (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL i A) := by
  rw [CryptoGames.CKA.advantage_eq_boolDist, CryptoGames.CKA.advantage_eq_boolDist,
    ckaBranch_redCKAPriv_atomic_eq Dh prng C ℓ encT idOf lam B0 B_q Δcka tStar qep
      tL i true hB0 A qAdv hA hqB hSendOk,
    ckaBranch_redCKAPriv_atomic_eq Dh prng C ℓ encT idOf lam B0 B_q Δcka tStar qep
      tL i false hB0 A qAdv hA hqB hSendOk]


omit [SampleableType Pt] in
theorem redPRNGAuth_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    redPRNGAuth (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A =
      redPRNGAuth (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A := by
  unfold redPRNGAuth
  rw [runPRNG_dhSchemeFb_eq Dh prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep
    ⟨true, tL, t⟩ false A,
    runPRNG_fsAtomicB_eq_lFS (dhScheme Dh) prng C ℓ encT idOf lam B0 B_q Δcka qep
      ⟨true, tL, t⟩ false hB0 A qAdv hA hqB hSendOk]


theorem prngAdvantage_redPRNGAuth_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.PRFPRNG.advantage prng
      (redPRNGAuth (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL t A) =
    CryptoGames.PRFPRNG.advantage prng
      (redPRNGAuth (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A) := by
  rw [redPRNGAuth_atomic_eq Dh prng C ℓ encT idOf lam B0 B_q Δcka qep tL t hB0 A qAdv hA hqB hSendOk]

omit [SampleableType Pt] in
theorem redPRNGPriv_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (i : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    redPRNGPriv (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL i A =
      redPRNGPriv (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL i A := by
  unfold redPRNGPriv
  refine bind_congr fun b => ?_
  rw [runPRNG_dhSchemeFb_eq Dh prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep ⟨false, tL, i⟩ b A,
    runPRNG_fsAtomicB_eq_lFS (dhScheme Dh) prng C ℓ encT idOf lam B0 B_q Δcka qep
      ⟨false, tL, i⟩ b hB0 A qAdv hA hqB hSendOk]


theorem prngAdvantage_redPRNGPriv_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (i : ℕ)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.PRFPRNG.advantage prng
      (redPRNGPriv (dhSchemeFb Dh) prng (fsAtomicB C ℓ encT idOf B0) lam Δcka qep tL i A) =
    CryptoGames.PRFPRNG.advantage prng
      (redPRNGPriv (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL i A) := by
  rw [redPRNGPriv_atomic_eq Dh prng C ℓ encT idOf lam B0 B_q Δcka qep tL i hB0 A qAdv hA hqB hSendOk]

theorem fsaeadGame_redFSAuth_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSAuth (dhSchemeFb Dh) prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep j tL t A) =
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSAuth (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep j tL t A) := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  unfold CryptoGames.FSAEAD.game redFSAuth
  refine bind_congr fun b => bind_congr fun k => ?_
  rw [runFS_dhSchemeFb_eq Dh prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
    lam Δcka qep ⟨true, tL, t⟩ j false A]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_runFS_fsClamp_fsAtomicB_eq_lFS (dhScheme Dh) prng C ℓ encT idOf
    B B0 B_q Δcka qep lam ⟨true, tL, t⟩ j false hB hB0 A qAdv hA hqB hSendOk
    (CryptoGames.FSAEAD.initState (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) k b)
    (CryptoGames.SM.Engine.RSReach.init ae G maxForwardJumps k) (skippedLenLe_init ae G maxForwardJumps k)]

theorem fsaeadAdvantage_redFSAuth_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.advantage (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSAuth (dhSchemeFb Dh) prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep j tL t A) =
    CryptoGames.FSAEAD.advantage (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSAuth (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep j tL t A) := by
  simp only [CryptoGames.FSAEAD.advantage,
    fsaeadGame_redFSAuth_atomic_eq Dh prng C ℓ encT idOf lam B B0 B_q Δcka qep j tL t
      hB hB0 A qAdv hA hqB hSendOk]

theorem fsaeadGame_redFSPriv_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPriv (dhSchemeFb Dh) prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep tL t A) =
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPriv (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A) := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  unfold CryptoGames.FSAEAD.game redFSPriv
  refine bind_congr fun b => bind_congr fun k => ?_
  rw [runFS_dhSchemeFb_eq Dh prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
    lam Δcka qep ⟨false, tL, t⟩ 0 false A]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_runFS_fsClamp_fsAtomicB_eq_lFS (dhScheme Dh) prng C ℓ encT idOf
    B B0 B_q Δcka qep lam ⟨false, tL, t⟩ 0 false hB hB0 A qAdv hA hqB hSendOk
    (CryptoGames.FSAEAD.initState (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) k b)
    (CryptoGames.SM.Engine.RSReach.init ae G maxForwardJumps k) (skippedLenLe_init ae G maxForwardJumps k)]

theorem fsaeadAdvantage_redFSPriv_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.advantage (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPriv (dhSchemeFb Dh) prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep tL t A) =
    CryptoGames.FSAEAD.advantage (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPriv (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A) := by
  simp only [CryptoGames.FSAEAD.advantage,
    fsaeadGame_redFSPriv_atomic_eq Dh prng C ℓ encT idOf lam B B0 B_q Δcka qep tL t
      hB hB0 A qAdv hA hqB hSendOk]

theorem fsaeadGame_redFSPrivCoin_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPrivCoin (dhSchemeFb Dh) prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep tL t A) =
    CryptoGames.FSAEAD.game (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPrivCoin (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A) := by
  let ae := (lAead C protoSignalCodec ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec)
  let G := lChainPRG C.F
  unfold CryptoGames.FSAEAD.game redFSPrivCoin
  refine bind_congr fun b => bind_congr fun k => ?_
  rw [runFS_dhSchemeFb_eq Dh prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
    lam Δcka qep ⟨false, tL, t⟩ 0 false A]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [simulateQ_runFS_fsClamp_fsAtomicB_eq_lFS (dhScheme Dh) prng C ℓ encT idOf
    B B0 B_q Δcka qep lam ⟨false, tL, t⟩ 0 false hB hB0 A qAdv hA hqB hSendOk
    (CryptoGames.FSAEAD.initState (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps) k b)
    (CryptoGames.SM.Engine.RSReach.init ae G maxForwardJumps k) (skippedLenLe_init ae G maxForwardJumps k)]

theorem fsaeadAdvantage_redFSPrivCoin_atomic_eq
    (Dh : DHFun (BitVec 256) Pt) (prng : PRFPRNG KR RSt Pt (BitVec 256))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (B B0 B_q Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (hB : (B_q + 1) * (maxForwardJumps + 1) ≤ B)
    (hB0 : (B_q + 1) * (maxForwardJumps + 1) ≤ B0)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt RSt
      (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qAdv : ℕ) (hA : CryptoGames.SM.MakesAtMostQueries A qAdv) (hqB : qAdv ≤ B_q)
    (hSendOk : CryptoGames.LibsignalSM.Proofs.SessionShort.SendMsgsOk (fun m => atomicShortPubB m.1) A) :
    CryptoGames.FSAEAD.advantage (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPrivCoin (dhSchemeFb Dh) prng (fsClamp B (fsAtomicB C ℓ encT idOf B0))
        lam Δcka qep tL t A) =
    CryptoGames.FSAEAD.advantage (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
      (redFSPrivCoin (dhScheme Dh) prng (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps)
        lam Δcka qep tL t A) := by
  simp only [CryptoGames.FSAEAD.advantage,
    fsaeadGame_redFSPrivCoin_atomic_eq Dh prng C ℓ encT idOf lam B B0 B_q Δcka qep tL t
      hB hB0 A qAdv hA hqB hSendOk]

end CombinedAtomicSwap

end Computational.Proofs.SessionCostedFig8.FsAtomicBSwap
