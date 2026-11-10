/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds2
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperSim
public import Computational.Proofs.SessionCostedDF
public import Computational.Proofs.HeadlineV1.DeliverForgePaperChallSim
public import Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper
import Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper
import Computational.Proofs.SignalWireRoundTrip
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.HeadlineV1.DeliverForgePaperUnshiftedPotOK

/-!
# Paper-Semantics Session Reductions and Cell-Sum Bridge

Defines the paper-semantics `DeliverForge` session reduction package `v1SessionRedsPaper` from
3-way case-split CKA, PRF-PRNG, and FS-AEAD reductions, proves `sessionCostedReductionsBounded`,
and bounds the per-cell and summed advantage terms by `hiddenSaltBoundV1`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators ENNReal
open ReductionDsl ReductionDsl.Comp OracleSpec OracleComp ENNReal
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Engine.RedPRNG CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge
namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.SM.Thm1 CryptoVerification.LibsignalSession
open CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst CryptoGames.LibsignalSession
open CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

/-- Paper-engine CKA reduction for cell `(tL, t)` on `challSimDF'Paper (2 + 1) (qep + 1) dfAdv`. -/
def redCKAHiddenSaltPaperDF {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    DeliverForge.redCKAAuthDFShiftedDir2Paper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam (qep + 1) (t - 1) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else if 3 ≤ t ∧ tL = some (t - 3) then
    DeliverForge.redCKAAuthDFShiftedPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) (t - 2) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else
    DeliverForge.redCKAAuthDFPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) tL t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)

/-- Paper-engine PRF-PRNG reduction for cell `(tL, t)` on
`challSimDF'Paper (2 + 1) (qep + 1) dfAdv`. -/
def redPRNGHiddenSaltPaperDF {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    DeliverForge.redPRNGAuthDFShiftedDir2Paper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam (qep + 1) (t - 1) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else if 3 ≤ t ∧ tL = some (t - 3) then
    DeliverForge.redPRNGAuthDFShiftedPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) (t - 2) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else
    DeliverForge.redPRNGAuthDFPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) tL t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)

/-- Paper-engine FS-AEAD reduction for cell `(tL, t)` and session `j` on
`challSimDF'Paper (2 + 1) (qep + 1) dfAdv`. -/
def redFSHiddenSaltPaperDF {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep j : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    DeliverForge.redFSAuthDFShiftedDir2Paper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam (qep + 1) j (t - 1) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else if 3 ≤ t ∧ tL = some (t - 3) then
    DeliverForge.redFSAuthDFShiftedPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) j (t - 2) t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
  else
    DeliverForge.redFSAuthDFPaper (dhScheme Dh) (Ratchet.rootPRNG P.C.F encPt)
      (lFS P.C P.codec ℓ encT idOf 25000) lam 1 (qep + 1) j tL t
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)

/-- Concrete per-cell advantage term for cell `(tL, t)` under the paper engine on `dfAdv`. -/
noncomputable def hiddenSaltCellTermPaperDF {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] [SampleableType PQC]
    (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    ℝ≥0∞ :=
  CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
    (redCKAHiddenSaltPaperDF P ℓ Dh encPt encT idOf lam qep tL t dfAdv) +
  PRFPRNG.advantage (Ratchet.rootPRNG P.C.F encPt)
    (redPRNGHiddenSaltPaperDF P ℓ Dh encPt encT idOf lam qep tL t dfAdv) +
  ∑ j ∈ Finset.range q,
    FSAEAD.advantage (lFS P.C P.codec ℓ encT idOf 25000)
      (redFSHiddenSaltPaperDF P ℓ Dh encPt encT idOf lam qep j tL t dfAdv)

end CryptoGames.LibsignalSM.Proofs.Refinement

namespace CryptoVerification.LibsignalSession

open ReductionDsl OracleSpec OracleComp CryptoGames CryptoGames.SM CryptoGames.SM.Construction
  CryptoGames.Ratchet CryptoGames.LibsignalSM CryptoGames.LibsignalSession
open Computational.Proofs.ReductionDsl.Fig8SourceCosts (HooksCostBounded bits_succ_le
  bits_le_bits_qep_add cInTransitE_cost_le cCompContainsE_cost_le vRecvC_cost_le
  cTrivialE_cost_le commitEC_cost_le modeCfgEC_injectFullE_cost_le esG_cost esH_cost esSetH_cost
  esSetG_cost esAbort_cost pGet_cost cGsSt_cost cGsSetWin_cost cRecPos_cost otherE_cost
  v0_cost v1_cost v2_cost v3_cost v4_cost implEC_cost_le authOutE_cost_le
  initPRNGEStateC_cost_le initFSEStateC_cost_le hooksPRNGC_costBounded hooksFSC_costBounded
  hooksFSC_costBounded_linear)

section ShiftedPaperDeliverForgeCost

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

local notation "OO_cka" =>
  CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "S_cka" => CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "hkCKAShiftedC" =>
  SM.Construction.hooksCKAShiftedC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "hkPRNGC" =>
  SM.Construction.hooksPRNGC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "hkFSC" =>
  SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redCKADir2P" =>
  SM.Construction.redCKAAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redCKAShiftedP" =>
  SM.Construction.redCKAAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redCKAP" =>
  SM.Construction.redCKAAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redPRNGDir2P" =>
  SM.Construction.redPRNGAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redPRNGShiftedP" =>
  SM.Construction.redPRNGAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redPRNGP" =>
  SM.Construction.redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redFSDir2P" =>
  SM.Construction.redFSAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redFSShiftedP" =>
  SM.Construction.redFSAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redFSP" =>
  SM.Construction.redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)

/-- Case-split `B_cka` paper reduction program (3-way dispatch). -/
def redCKAAuthDFCasePaperProg (L B qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction OO_cka
      (CKA.ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (SM.specDF (SM.Construction.PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then redCKADir2P L B qep maxSkip (t - 1) t
  else if 3 ≤ t ∧ tL = some (t - 3) then redCKAShiftedP L B 1 qep maxSkip (t - 2) t
  else redCKAP L B 1 qep maxSkip tL t

/-- Case-split `B_prng` paper reduction program (3-way dispatch). -/
def redPRNGAuthDFCasePaperProg (L B qep maxSkip : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (PRFPRNG.prngIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (SM.specDF (SM.Construction.PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (PRFPRNG.prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then redPRNGDir2P L B qep maxSkip (t - 1) t
  else if 3 ≤ t ∧ tL = some (t - 3) then redPRNGShiftedP L B 1 qep maxSkip (t - 2) t
  else redPRNGP L B 1 qep maxSkip tL t

/-- Case-split `B_fs` paper reduction program (3-way dispatch). -/
def redFSAuthDFCasePaperProg (L B qep maxSkip j : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (PRFPRNG.prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
        fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE)
      (PRFPRNG.fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK)
      (SM.specDF (SM.Construction.PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (PRFPRNG.prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  if 2 ≤ t ∧ tL = some (t - 2) then redFSDir2P L B qep maxSkip j (t - 1) t
  else if 3 ≤ t ∧ tL = some (t - 3) then redFSShiftedP L B 1 qep maxSkip j (t - 2) t
  else redFSP L B 1 qep maxSkip j tL t

local notation "redCKACaseP" =>
  redCKAAuthDFCasePaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redPRNGCaseP" =>
  redPRNGAuthDFCasePaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "redFSCaseP" =>
  redFSAuthDFCasePaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)

private lemma hdrEqE_cost_le {Γ'}
    (c₁ c₂ : Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.hdrEqE c₁ c₂).cost ≤ c₁.cost + c₂.cost + 40 := by
  have hmax11 : max 1 1 = 1 := rfl
  have hmax14 : max 1 4 = 4 := rfl
  simp only [SM.Engine.hdrEqE, SM.Engine.optTEqE, CKA.ckaOps, Expr.cost,
    v0_cost, v1_cost, hmax11, hmax14, Nat.reduceAdd]; omega

private lemma deliverForgeEC_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep : ℕ)
    (mo : SM.Construction.Mode) (hhk : HooksCostBounded hk H) {Γ'}
    (es : Expr OO_cka Γ' (SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO_cka Γ' (.prod .bool (.prod (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
      (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))) :
    (SM.Engine.deliverForgeEC hk L 3 qep (SM.Engine.modeCfgEC OO_cka mo) es arg).cost ≤
      es.cost + arg.cost + 3 * H + 650 * L +
        ReductionDsl.bits qep + ReductionDsl.bits mo.tStar + 4210 := by
  have hqep1 := bits_succ_le qep
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ0 := .prod (SM.Engine.esTy vpT hsT) (.prod .bool (.prod hdrCtT hdrCtT)) :: Γ'
  let Γ1 : List (Ty S_cka) := SM.Engine.cRecTy :: Γ0
  let Γ2 : List (Ty S_cka) := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ1
  have hit0 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ0)
    (SM.Engine.esG (O' := OO_cka) (.fst .v0)) (SM.otherE (.fst (.snd .v0))) (.fst (.snd (.snd .v0)))
  have hit1 := cInTransitE_cost_le (vpT := vpT) L (Γ' := Γ1)
    (SM.Engine.esG (O' := OO_cka) (.fst .v1)) (SM.otherE (.fst (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hcc1 := cCompContainsE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ1)
    (SM.Engine.esG (.fst .v1)) (SM.Engine.cRecPos .v0)
  have hhe1 := hdrEqE_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (Γ' := Γ1) (.fst (.snd (.snd .v1))) (.snd (.snd (.snd .v1)))
  have hvr := vRecvC_cost_le hk H hhk (Γ' := Γ1) (SM.Engine.esH (.fst .v1))
    (SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd (.snd .v1))) .none
  have htr := cTrivialE_cost_le (O' := OO_cka) (vpT := vpT) L (Γ' := Γ2) (SM.Engine.esG (.fst .v4))
    (.pair (SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hcm := commitEC_cost_le hk H L hhk (Γ' := Γ2) (SM.Engine.esSetH (.fst .v4) (.snd .v2))
    (SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v4))) (.fst (.snd .v4))) (.fst .v0)
    (.pair (SM.otherE (.fst (.snd .v4))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij := modeCfgEC_injectFullE_cost_le (O' := OO_cka) mo (Γ' := Γ2) (.fst (.snd .v0))
  simp only [esG_cost, esH_cost, esSetH_cost, pGet_cost, cGsSt_cost, cRecPos_cost, otherE_cost,
    Expr.cost, v0_cost, v1_cost, v2_cost, v4_cost, Nat.reduceAdd]
    at hit0 hit1 hcc1 hhe1 hvr htr hcm hij
  simp only [SM.Engine.deliverForgeEC, SM.orE, SM.isSomeE, SM.Engine.cGsWin, SM.Engine.esMk,
    SM.posEpoch, cRecPos_cost, esG_cost, esAbort_cost, esSetH_cost, esSetG_cost, cGsSetWin_cost,
    Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, Nat.reduceAdd]; omega

private lemma implECDF_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (H L qep maxSkip : ℕ)
    (mo : SM.Construction.Mode) (hhk : HooksCostBounded hk H) {Γ'}
    (es : Expr OO_cka Γ' (SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.implECDF hk L 3 qep maxSkip (SM.Engine.modeCfgEC OO_cka mo) mo.policy es q).cost ≤
      es.cost + q.cost + 18650 * L +
        L * (ReductionDsl.bits (mo.tL.getD 0) + 2 * ReductionDsl.bits mo.tStar + 40) +
        3 * H + 6 * ReductionDsl.bits qep + (ReductionDsl.bits (mo.tL.getD 0) + 3) +
        6 * ReductionDsl.bits mo.tStar +
        (maxSkip + 1) + 22300 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let esT := SM.Engine.esTy vpT hsT
  let smqT := CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let dfqT : Ty S_cka := .prod .bool (.prod hdrCtT hdrCtT)
  let smqDFT := CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod esT smqDFT :: Γ'
  have himpl := implEC_cost_le hk H L qep maxSkip mo hhk (Γ' := smqT :: Γ0) (.fst .v1) .v0
  have hdf := deliverForgeEC_cost_le hk H L qep mo hhk (Γ' := dfqT :: Γ0) (.fst .v1) .v0
  simp only [v0_cost, v1_cost, Expr.cost, Nat.reduceAdd] at himpl hdf
  simp only [SM.Engine.implECDF, Comp.cost, Expr.cost, v0_cost, Nat.reduceAdd]; omega

private lemma cAfterCorrShiftedE_cost_le_cAfterCorrE {O' : Ops S_cka} {vpT : Ty S_cka}
    (L l : ℕ) {Γ'} (s : Expr O' Γ' (SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (SM.Engine.cAfterCorrShiftedE L l s p).cost ≤
      (SM.Engine.cAfterCorrE L s p).cost + 36 * ReductionDsl.bits l + 650 := by
  have hl1 := ReductionDsl.bits_mono (Nat.sub_le l 1)
  have hb1 : ReductionDsl.bits 1 = 1 := rfl
  simp only [SM.Engine.cAfterCorrShiftedE, SM.Engine.cAfterCorrE, SM.Engine.cGsMk, SM.Engine.cLeakE,
    SM.maxOptE, SM.maxN, SM.leN, SM.boolEq, SM.otherE, SM.pGet, SM.Engine.cRecPos, SM.posSender,
    SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch, SM.Engine.cGsIdx,
    SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    Expr.cost, v0_cost, v1_cost, v2_cost, hb1, Nat.reduceAdd]; omega

private lemma leakDoomE_cost_le_add {O' : Ops S_cka} {vpT : Ty S_cka}
    (L : ℕ) (π : SM.Engine.Policy) {Γ'} (g g₁ g₂ : Expr O' Γ' (SM.Engine.cGsTy vpT)) {d : ℕ}
    (h : g₁.cost ≤ g₂.cost + d) :
    (SM.Engine.leakDoomE L π g g₁).cost ≤ (SM.Engine.leakDoomE L π g g₂).cost + d := by
  simp only [SM.Engine.leakDoomE, Expr.cost]; omega

private lemma corrECShifted_cost_le_corrEC {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (L l : ℕ) (π : SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO_cka Γ' .bool) :
    (SM.Engine.corrECShifted hk L l π es p).cost ≤
      (SM.Engine.corrEC hk L π es p).cost + 72 * ReductionDsl.bits l + 1300 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let psT := CKA.ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) := .prod (SM.Engine.esTy vpT hsT) .bool :: Γ'
  let Γ1 : List (Ty S_cka) := psT :: .prod (.opt psT) hsT :: Γ0
  have hac0 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hld := leakDoomE_cost_le_add (O' := OO_cka) (vpT := vpT) L π (Γ' := Γ0)
    (SM.Engine.esG (.fst .v0))
    (SM.Engine.cAfterCorrShiftedE L l (SM.Engine.esG (.fst .v0)) (.snd .v0))
    (SM.Engine.cAfterCorrE L (SM.Engine.esG (.fst .v0)) (.snd .v0)) (Nat.add_assoc _ _ _ ▸ hac0)
  have hac1 := cAfterCorrShiftedE_cost_le_cAfterCorrE (O' := OO_cka) (vpT := vpT) L l (Γ' := Γ1)
    (SM.Engine.esG (.fst .v2)) (.snd .v2)
  simp only [SM.Engine.corrECShifted, SM.Engine.corrEC, SM.orE, SM.Engine.esMk,
    Comp.cost, Expr.cost]; omega

private lemma implECDFShifted_cost_le_implECDF {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT)
    (L l Δ qep maxSkip : ℕ) (cfg : SM.Engine.ConfigEC OO_cka) (π : SM.Engine.Policy) {Γ'}
    (es : Expr OO_cka Γ' (SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (SM.Engine.implECDFShifted hk L l Δ qep maxSkip cfg π es q).cost ≤
      (SM.Engine.implECDF hk L Δ qep maxSkip cfg π es q).cost + 72 * ReductionDsl.bits l + 1300 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := SM.Engine.esTy vpT hsT
  let smqT := CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smqDFT := CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ_cr : List (Ty S_cka) := .bool :: .prod esT smqT :: smqT :: .prod esT smqDFT :: Γ'
  have hcr := corrECShifted_cost_le_corrEC hk L l π (Γ' := Γ_cr) (.fst .v1) .v0
  simp only [SM.Engine.implECDFShifted, SM.Engine.implECDF, SM.Engine.implECShifted,
    SM.Engine.implEC, Comp.cost, Expr.cost]; omega

private lemma hooksCKAShiftedC_costBounded (B l tStar : ℕ) :
    HooksCostBounded (hkCKAShiftedC B l tStar)
      (5 * ReductionDsl.bits l + ReductionDsl.bits tStar + (B + 1) + 530) where
  startSend_le h ctx p t γv σ r := by
    have hl1 := bits_succ_le l
    have hl2 : ReductionDsl.bits (l + 2) ≤ ReductionDsl.bits (l + 1) + 1 := bits_succ_le (l + 1)
    have hb1 : ReductionDsl.bits 1 = 1 := rfl
    simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedStartSendC,
      SM.Construction.ckaShiftedSetCache, SM.Construction.ckaShiftedSetΓPre, SM.pSet, SM.leN,
      CKA.ckaIface, CKA.ckaSamplers, CKA.ckaOps, Comp.cost, Expr.cost,
      v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, hb1, Nat.reduceAdd]; omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedStartRecvC,
      SM.Construction.ckaStartRecvAnsE, CKA.ckaOps, Comp.cost, Expr.cost,
      v0_cost, v1_cost, v2_cost, Nat.reduceAdd]; omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedFsSendC, CKA.ckaOps,
      Comp.cost, Expr.cost]; omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    have hB := ReductionDsl.bits_le_succ B
    simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedFsRecvC, CKA.ckaOps,
      Comp.cost, Expr.cost]; omega
  commit_le h ctx p old new := by
    have hl1 := bits_succ_le l
    have hl2 : ReductionDsl.bits (l + 2) ≤ ReductionDsl.bits (l + 1) + 1 := bits_succ_le (l + 1)
    have hb1 : ReductionDsl.bits 1 = 1 := rfl
    simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedCommitC,
      SM.Construction.ckaShiftedSetΓPre, SM.pSet, SM.isSomeE, SM.leN, SM.Engine.vpTcurNat,
      SM.Engine.vpΓ, SM.Engine.vpSetΓ, SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpRoot,
      SM.Engine.vpVS, SM.Engine.vpVR, SM.Engine.vpTcur, CKA.ckaIface, Comp.cost, Expr.cost,
      v0_cost, v1_cost, v2_cost, v3_cost, v4_cost, hb1, Nat.reduceAdd]; omega
  reveal_le h ctx p vp := by
    have hb1 : ReductionDsl.bits 1 = 1 := rfl
    simp only [SM.Construction.hooksCKAShiftedC, SM.Construction.ckaShiftedRevealC,
      SM.Engine.realPartyE, SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS,
      SM.Engine.vpVR, SM.Engine.vpΓ, SM.Engine.vpTcur, SM.Engine.vpTcurNat, SM.leN, SM.pGet,
      CKA.ckaIface, Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, hb1, Nat.reduceAdd]; omega

private lemma initCKAShiftedEStateC_cost_le (l : ℕ) {Γ'} (bE : Expr OO_cka Γ' .bool) :
    (SM.Construction.initCKAShiftedEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) l bE).cost ≤ bE.cost + 800 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  simp only [SM.Construction.initCKAShiftedEStateC, SM.Engine.mkPartiesE, SM.Engine.cGsInitE,
    SM.Engine.cGsMk, SM.Engine.vpMk, SM.Engine.esMk, CKA.ckaIface, CKA.ckaSamplers, CKA.ckaOps,
    Comp.cost, Expr.cost, v0_cost, v1_cost, v2_cost, hb0, Nat.reduceAdd]; omega

private abbrev dfStepBound (q qep : ℕ) : ℕ :=
  let L := q + 1
  let B := (q + 1) * (maxForwardJumps + 1)
  24000 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
    200 * ReductionDsl.bits qep + 350000

private lemma df_poly_le_ratchetCostBudget (q qep : ℕ) :
    (q + 1) * dfStepBound q qep ≤ ratchetCostBudget q qep := by
  unfold ratchetCostBudget dfStepBound; dsimp only
  set M := maxForwardJumps + ReductionDsl.bits qep
  set L := q + 1
  set B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbq : 1 ≤ ReductionDsl.bits qep := ReductionDsl.one_le_bits qep
  have hL_pos : 1 ≤ L := by omega
  have hM_lb : 25001 ≤ M := by omega
  have hm_le : maxForwardJumps + 1 ≤ M := by omega
  have hB_le : B ≤ L * M := Nat.mul_le_mul_left L hm_le
  have h24000L : 24000 * L ≤ L * M := by
    calc 24000 * L = L * 24000 := Nat.mul_comm _ _
      _ ≤ L * M := Nat.mul_le_mul_left L (by omega)
  have h3b : 3 * ReductionDsl.bits qep + 60 ≤ 4 * M := by omega
  have hL3b : L * (3 * ReductionDsl.bits qep + 60) ≤ 4 * (L * M) :=
    (Nat.mul_le_mul_left L h3b).trans_eq (by ring)
  have hb_LM : ReductionDsl.bits qep ≤ L * M := by
    calc ReductionDsl.bits qep ≤ M := by omega
      _ = 1 * M := (Nat.one_mul M).symm
      _ ≤ L * M := Nat.mul_le_mul_right M hL_pos
  have h1_LM : 25001 ≤ L * M := by
    calc 25001 = 1 * 25001 := (Nat.one_mul _).symm
      _ ≤ L * M := Nat.mul_le_mul hL_pos hM_lb
  have hsum :
      24000 * L + L * (3 * ReductionDsl.bits qep + 60) + 3 * B +
        200 * ReductionDsl.bits qep + 350000 ≤
        2 ^ 12 * (L * M) := by
    omega
  calc (q + 1) * (24000 * L + L * (3 * ReductionDsl.bits qep + 60) +
          3 * B + 200 * ReductionDsl.bits qep + 350000)
      ≤ (q + 1) * (2 ^ 12 * (L * M)) := Nat.mul_le_mul_left (q + 1) hsum
    _ = 2 ^ 12 * (q + 1) ^ 2 * M := by
      change (q + 1) * (2 ^ 12 * ((q + 1) * M)) = 2 ^ 12 * (q + 1) ^ 2 * M
      ring

private lemma add_mul_add_le_ratchetCostBudget_df {q qep a b c : ℕ}
    (ha : a ≤ dfStepBound q qep) (hb : b + c ≤ dfStepBound q qep) :
    a + q * b + q * c ≤ ratchetCostBudget q qep := by
  have hmul : q * (b + c) ≤ q * dfStepBound q qep := Nat.mul_le_mul_left q hb
  have hring : (q + 1) * dfStepBound q qep = q * dfStepBound q qep + dfStepBound q qep := by
    rw [Nat.add_mul, Nat.one_mul]
  have h1 : a + q * b + q * c ≤ (q + 1) * dfStepBound q qep := by
    have : q * b + q * c = q * (b + c) := by ring
    omega
  exact h1.trans (df_poly_le_ratchetCostBudget q qep)

private lemma implECDFShifted_step_add_le_dfStepBound {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (q qep l : ℕ)
    (mo : SM.Construction.Mode) (htStar : mo.tStar < qep + 2) (htL : mo.tL.getD 0 ≤ mo.tStar)
    (hl : l ≤ mo.tStar)
    (hhk : HooksCostBounded hk
      (let L := q + 1
       let B := (q + 1) * (maxForwardJumps + 1)
       320 * L + 10 * ReductionDsl.bits qep + B + 2500)) :
    (SM.Engine.implECDFShifted
      (Γ' := [SM.Engine.esTy
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
        CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E])
      hk (q + 1) l 3 qep maxForwardJumps
      (SM.Engine.modeCfgEC OO_cka mo) mo.policy .v0 .v1).cost + 13 +
        (ReductionDsl.bits mo.tStar + 81) ≤
      dfStepBound q qep := by
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  have hmfj : maxForwardJumps = 25000 := rfl
  have htStar_bits := bits_le_bits_qep_add (x := mo.tStar) (qep := qep) (by omega)
  have htL_bits := bits_le_bits_qep_add (x := mo.tL.getD 0) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hsh := implECDFShifted_cost_le_implECDF hk L l 3 qep maxForwardJumps
    (SM.Engine.modeCfgEC OO_cka mo) mo.policy
    (Γ' := [SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  have himpl := implECDF_cost_le hk
    (320 * L + 10 * ReductionDsl.bits qep + B + 2500) L qep maxForwardJumps
    mo hhk (Γ' := [SM.Engine.esTy
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT,
      CKA.ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  simp only [v0_cost, v1_cost] at himpl
  have hmul :
      L * (ReductionDsl.bits (mo.tL.getD 0) + 2 * ReductionDsl.bits mo.tStar + 40) ≤
        L * (3 * ReductionDsl.bits qep + 60) :=
    Nat.mul_le_mul_left L (by omega)
  dsimp only [L, B, dfStepBound] at hsh himpl hmul ⊢; omega

theorem redCKAAuthDFShiftedProg_add_totalCost_le
    (q qep l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) :
    (SM.Construction.redCKAAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) qep maxForwardJumps l t).totalCost q +
      q * (ReductionDsl.bits t + 81) ≤ ratchetCostBudget q qep := by
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hmo_tL : mo.tL.getD 0 ≤ mo.tStar := by dsimp [mo]; omega
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add (x := l - 1) (qep := qep) (by omega)
  have hhk := (hooksCKAShiftedC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B l t).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B]; omega)
  have hstep := implECDFShifted_step_add_le_dfStepBound _ q qep l mo ht hmo_tL hl hhk
  have hinit := initCKAShiftedEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) l (Γ' := [.unit]) (.bool false)
  have hout := authOutE_cost_le (O' := OO_cka)
    (vpT := @SM.Construction.ckaVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (hsT := @SM.Construction.ckaShiftedHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    L mo.policy (Γ' := [SM.Construction.ckaShiftedEsTy, .bool]) .v0
  simp only [v0_cost, Expr.cost] at hinit hout
  rw [SM.Construction.redCKAAuthDFShiftedProg_totalCost, add_right_comm _ (q * _)]
  refine add_mul_add_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, SM.Construction.Mode.policy, dfStepBound]
    at hinit hout ⊢
  simp only [Option.getD_some, Nat.reduceAdd] at hinit hout ⊢; omega

theorem redPRNGAuthDFShiftedProg_add_totalCost_le
    (q qep l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) :
    (SM.Construction.redPRNGAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps l t).totalCost q +
      q * (ReductionDsl.bits t + 81) ≤ ratchetCostBudget q qep := by
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hmo_tL : mo.tL.getD 0 ≤ mo.tStar := by dsimp [mo]; omega
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add (x := l - 1) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch (some (l - 1))) (qep := qep)
    (by dsimp [healEpoch]; omega)
  have hhk := (hooksPRNGC_costBounded (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B mo).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B, mo, SM.Construction.Mode.tH]; omega)
  have hstep := implECDFShifted_step_add_le_dfStepBound _ q qep l mo ht hmo_tL hl hhk
  have hinit := initPRNGEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) mo (Γ' := [.unit]) (.bool false)
  have hout := authOutE_cost_le (O' := OO_cka)
    (vpT := @SM.Construction.prngVpTy KC Γ CCoins T I KR RSt K SS RS M E)
    (hsT := @SM.Construction.prngHsTy KC Γ CCoins T I KR RSt K SS RS M E)
    L mo.policy (Γ' := [SM.Construction.prngEsTy, .bool]) .v0
  simp only [v0_cost, Expr.cost] at hinit hout
  rw [SM.Construction.redPRNGAuthDFShiftedProg_totalCost, add_right_comm _ (q * _)]
  refine add_mul_add_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, SM.Construction.Mode.policy, dfStepBound]
    at hinit hout ⊢
  simp only [Option.getD_some, Nat.reduceAdd] at hinit hout ⊢; omega

theorem redFSAuthDFShiftedProg_add_totalCost_le
    (q qep j l t : ℕ) (ht : t < qep + 2) (hl : l ≤ t) (hj : j < q) :
    (SM.Construction.redFSAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK)
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps j l t).totalCost q +
      q * (ReductionDsl.bits t + 81) ≤ ratchetCostBudget q qep := by
  let L := q + 1; let B := (q + 1) * (maxForwardJumps + 1)
  let mo : SM.Construction.Mode := ⟨true, some (l - 1), t⟩
  have hmfj : maxForwardJumps = 25000 := rfl
  have hmo_tL : mo.tL.getD 0 ≤ mo.tStar := by dsimp [mo]; omega
  have ht_bits := bits_le_bits_qep_add (x := t) (qep := qep) (by omega)
  have hl_bits := bits_le_bits_qep_add (x := l) (qep := qep) (by omega)
  have hl1_bits := bits_le_bits_qep_add (x := l - 1) (qep := qep) (by omega)
  have htH_bits := bits_le_bits_qep_add (x := healEpoch (some (l - 1))) (qep := qep)
    (by dsimp [healEpoch]; omega)
  have hhk := (hooksFSC_costBounded_linear (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B mo j).mono
    (H' := 320 * L + 10 * ReductionDsl.bits qep + B + 2500)
    (by dsimp only [L, B, mo, SM.Construction.Mode.tH]; omega)
  have hstep := implECDFShifted_step_add_le_dfStepBound _ q qep l mo ht hmo_tL hl hhk
  have hinit := initFSEStateC_cost_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L mo j (Γ' := [.unit]) (.bool false)
  simp only [Expr.cost] at hinit
  rw [SM.Construction.redFSAuthDFShiftedProg_totalCost]
  refine add_mul_add_le_ratchetCostBudget_df ?_ hstep
  dsimp only [L, B, mo, SM.Construction.Mode.tH, dfStepBound] at hinit ⊢; omega

theorem redCKAAuthDFCasePaperProg_totalCost_le
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) :
    (redCKACaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
      qep maxForwardJumps tL t).totalCost q ≤ ratchetCostBudget q qep := by
  unfold redCKAAuthDFCasePaperProg; split_ifs with h2 h3
  · exact (SM.Construction.redCKAAuthDFShiftedDir2PaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) (t - 1) t qep maxForwardJumps q).trans
      (redCKAAuthDFShiftedProg_add_totalCost_le q qep (t - 1) t ht (by omega))
  · exact (SM.Construction.redCKAAuthDFShiftedPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) (t - 2) t qep maxForwardJumps q).trans
      (redCKAAuthDFShiftedProg_totalCost_le q qep (t - 2) t ht (by omega))
  · exact (SM.Construction.redCKAAuthDFPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL t q).trans
      (redCKAAuthDFProg_totalCost_le q qep t tL ht htL)

theorem redPRNGAuthDFCasePaperProg_totalCost_le
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) :
    (redPRNGCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
      qep maxForwardJumps tL t).totalCost q ≤ ratchetCostBudget q qep := by
  unfold redPRNGAuthDFCasePaperProg; split_ifs with h2 h3
  · exact (SM.Construction.redPRNGAuthDFShiftedDir2PaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) (t - 1) t qep maxForwardJumps q).trans
      (redPRNGAuthDFShiftedProg_add_totalCost_le q qep (t - 1) t ht (by omega))
  · exact (SM.Construction.redPRNGAuthDFShiftedPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) (t - 2) t qep maxForwardJumps q).trans
      (redPRNGAuthDFShiftedProg_totalCost_le q qep (t - 2) t ht (by omega))
  · exact (SM.Construction.redPRNGAuthDFPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps tL t q).trans
      (redPRNGAuthDFProg_totalCost_le q qep t tL ht htL)

theorem redFSAuthDFCasePaperProg_totalCost_le
    (q qep j t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) (hj : j < q) :
    (redFSCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
      qep maxForwardJumps j tL t).totalCost q ≤ ratchetCostBudget q qep := by
  unfold redFSAuthDFCasePaperProg; split_ifs with h2 h3
  · exact (SM.Construction.redFSAuthDFShiftedDir2PaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) j (t - 1) t qep maxForwardJumps q).trans
      (redFSAuthDFShiftedProg_add_totalCost_le q qep j (t - 1) t ht (by omega) hj)
  · exact (SM.Construction.redFSAuthDFShiftedPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) j (t - 2) t qep maxForwardJumps q).trans
      (redFSAuthDFShiftedProg_totalCost_le q qep j (t - 2) t ht (by omega) hj)
  · exact (SM.Construction.redFSAuthDFPaperProg_totalCost_le_nonPaper
      (q + 1) ((q + 1) * (maxForwardJumps + 1)) 1 qep maxForwardJumps j tL t q).trans
      (redFSAuthDFProg_totalCost_le q qep j t tL ht htL hj)

theorem redCKAAuthDFCasePaperProg_totalQueries_le
    (L B qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redCKACaseP L B qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q ≤ 2 + 2 * q := by
  unfold redCKAAuthDFCasePaperProg; split_ifs
  · have h : (redCKADir2P L B qep maxSkip (t - 1) t).totalQueries (fun _ => 1) (fun _ => 0) q =
        2 + q * 2 := by
      simp [CostedReduction.totalQueries, SM.Construction.redCKAAuthDFShiftedDir2PaperProg,
        SM.Construction.redCKAAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    omega
  · have h : (redCKAShiftedP L B 1 qep maxSkip (t - 2) t).totalQueries (fun _ => 1) (fun _ => 0) q =
        2 + q * 2 := by
      simp [CostedReduction.totalQueries, SM.Construction.redCKAAuthDFShiftedPaperProg,
        SM.Construction.redCKAAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    omega
  · rw [SM.Construction.redCKAAuthDFPaperProg_totalQueries]; omega

theorem redPRNGAuthDFCasePaperProg_totalQueries
    (L B qep maxSkip : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redPRNGCaseP L B qep maxSkip tL t).totalQueries (fun _ => 1) (fun _ => 0) q = 2 + q * 2 := by
  unfold redPRNGAuthDFCasePaperProg; split_ifs
  · dsimp only [CostedReduction.totalQueries, SM.Construction.redPRNGAuthDFShiftedDir2PaperProg,
      SM.Construction.redPRNGAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    rw [SM.Construction.initPRNGEStateC_queries,
      SM.Construction.implECDFShiftedPaper_hooksPRNGC_queries]; omega
  · dsimp only [CostedReduction.totalQueries, SM.Construction.redPRNGAuthDFShiftedPaperProg,
      SM.Construction.redPRNGAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    rw [SM.Construction.initPRNGEStateC_queries,
      SM.Construction.implECDFShiftedPaper_hooksPRNGC_queries]; omega
  · exact SM.Construction.redPRNGAuthDFPaperProg_totalQueries _ _ _ _ _ _ _ _

theorem redFSAuthDFCasePaperProg_totalQueries
    (L B qep maxSkip j : ℕ) (tL : Option ℕ) (t q : ℕ) :
    (redFSCaseP L B qep maxSkip j tL t).totalQueries (fun _ => 1) (fun _ => 0) q = q * 2 := by
  unfold redFSAuthDFCasePaperProg; split_ifs
  · dsimp only [CostedReduction.totalQueries, SM.Construction.redFSAuthDFShiftedDir2PaperProg,
      SM.Construction.redFSAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    rw [SM.Construction.initFSEStateC_queries,
      SM.Construction.implECDFShiftedPaper_hooksFSC_queries]; omega
  · dsimp only [CostedReduction.totalQueries, SM.Construction.redFSAuthDFShiftedPaperProg,
      SM.Construction.redFSAuthDFShiftedPaperGenProg, ReductionDsl.Comp.queries]
    rw [SM.Construction.initFSEStateC_queries,
      SM.Construction.implECDFShiftedPaper_hooksFSC_queries]; omega
  · exact SM.Construction.redFSAuthDFPaperProg_totalQueries _ _ _ _ _ _ _ _ _

theorem redCKAAuthDFCasePaperProg_gredBounded
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hsize : (redCKACaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps tL t).size ≤ ReductionDsl.reductionSizeBudget) :
    GRedBounded (redCKACaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) :=
  CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ q (2 + 2 * q) (ratchetCostBudget q qep)
    (redCKAAuthDFCasePaperProg_totalCost_le q qep t tL ht htL)
    hsize
    (redCKAAuthDFCasePaperProg_totalQueries_le _ _ _ _ _ _ _)
    (CKA.ckaOps_sizeHonest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (CKA.ckaSamplers_sizeHonest _ _ _ _ _)

theorem redPRNGAuthDFCasePaperProg_gredBounded
    (q qep t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t)
    (hsize : (redPRNGCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps tL t).size ≤ ReductionDsl.reductionSizeBudget) :
    GRedBounded (redPRNGCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps tL t)
      (fun _ => 1) (fun _ => 0) q (2 + 2 * q) (ratchetCostBudget q qep) :=
  CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ q (2 + 2 * q) (ratchetCostBudget q qep)
    (redPRNGAuthDFCasePaperProg_totalCost_le q qep t tL ht htL)
    hsize
    (by rw [redPRNGAuthDFCasePaperProg_totalQueries]; omega)
    (PRFPRNG.prngOps_sizeHonest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (PRFPRNG.prngSamplers_sizeHonest _ _ _ _ _)

theorem redFSAuthDFCasePaperProg_gredBounded
    (q qep j t : ℕ) (tL : Option ℕ) (ht : t < qep + 2) (htL : tL.getD 0 ≤ t) (hj : j < q)
    (hsize : (redFSCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps j tL t).size ≤ ReductionDsl.reductionSizeBudget) :
    GRedBounded (redFSCaseP (q + 1) ((q + 1) * (maxForwardJumps + 1))
        qep maxForwardJumps j tL t)
      (fun _ => 1) (fun _ => 0) q (2 * q) (ratchetCostBudget q qep) :=
  CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ q (2 * q) (ratchetCostBudget q qep)
    (redFSAuthDFCasePaperProg_totalCost_le q qep j t tL ht htL hj)
    hsize
    (by rw [redFSAuthDFCasePaperProg_totalQueries]; omega)
    (PRFPRNG.prngOps_sizeHonest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (PRFPRNG.prngSamplers_sizeHonest _ _ _ _ _)

end ShiftedPaperDeliverForgeCost
end CryptoVerification.LibsignalSession

namespace CryptoVerification.E2E

open ReductionDsl OracleSpec OracleComp ENNReal MeasureTheory
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.ThmB
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.LibsignalSM.Proofs
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total)
open CryptoVerification.LibsignalSession.HeadlineV1
open CryptoVerification.E2E.Signed
open CryptoGames.SM.Construction.AuthL11
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

/-- Paper-engine `SessionCostedReductions` instance sharing the first 7 projections with
`v1SessionReds` and replacing the 4 `DeliverForge` reductions with compiled atomic paper programs. -/
noncomputable def v1SessionRedsPaper {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam :=
  { v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q with
    challSimDF :=
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.challSimDF'PaperAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q
    B_cka := fun tL t =>
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redCKAAuthDFCasePaperAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t
    B_prng := fun tL t =>
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redPRNGAuthDFCasePaperAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q tL t
    B_fs := fun j tL t =>
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redFSAuthDFCasePaperAtomicProg
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q j tL t }

private lemma targetsL_getD_le {Δ t : ℕ} {tL : Option ℕ} (htL : tL ∈ admissibleLastLeakGuesses Δ t) :
    tL.getD 0 ≤ t := by
  simp only [admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at htL
  rcases htL with rfl | ⟨l, hl, rfl⟩ <;> (simp; try omega)

/-- `v1SessionRedsPaper` satisfies `sessionCostedReductionsBounded` when `qep ≤ q + 10`. -/
theorem v1SessionRedsPaper_bounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (hqep : qep ≤ q + 10) :
    sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
      (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q) := by
  have hb := v1SessionReds_bounded ℓ C K idA idB Dh encPt encT decT lam qep q hqep
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.1,
    Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.challSimDF'PaperAtomicProg_gRedBounded
      Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q,
    fun t ht tL htL =>
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redCKAAuthDFCasePaperAtomicProg_gRedBounded
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t tL ht (targetsL_getD_le htL),
    fun t ht tL htL =>
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redPRNGAuthDFCasePaperAtomicProg_gRedBounded
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q t tL ht (targetsL_getD_le htL),
    fun t ht tL htL j hj =>
      Computational.Proofs.SessionCostedFig8.DFProgBoundsPaper.redFSAuthDFCasePaperAtomicProg_gRedBounded
        Dh encPt C ℓ encT (idsOf idA idB) lam (qep + 1) q j t tL ht (targetsL_getD_le htL) hj,
    fun t _ht tL _htL A hA =>
      Computational.Proofs.HeadlineV1.DeliverForgePaperUnshiftedPotOK.redPRNGAuthDFCasePaperAtomicProg_makesAtMostQueries
        ℓ C Dh encPt encT (idsOf idA idB) lam (qep + 1) q tL t A hA,
    fun t _ht tL _htL j _hj A hA =>
      Computational.Proofs.HeadlineV1.DeliverForgePaperUnshiftedPotOK.redFSAuthDFCasePaperAtomicProg_makesAtMostQueries
        ℓ C Dh encPt encT (idsOf idA idB) lam (qep + 1) q j tL t A hA⟩

section PaperEvalBridges

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession.HeadlineV1 CryptoVerification.E2E.Signed
open CryptoGames.SM.Construction.AuthL11
open Computational.Proofs.ReductionDsl.Fig8Atomic (atomicShortPubB)

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

@[simp] theorem v1SessionRedsPaper_spk (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).spk =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).spk := rfl

@[simp] theorem v1SessionRedsPaper_fig8 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).fig8 =
      fig8RedsInst Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam (qep + 1) q := rfl

@[simp] theorem v1SessionRedsPaper_fs (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).fs =
      fsCostedRedsInst C protoSignalCodec ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)) := rfl

@[simp] theorem v1SessionRedsPaper_simFig8 (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simFig8 := rfl

@[simp] theorem v1SessionRedsPaper_simDeliverForge (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).simDeliverForge =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).simDeliverForge := rfl

@[simp] theorem v1SessionRedsPaper_epoch0Red (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).epoch0Red := rfl

@[simp] theorem v1SessionRedsPaper_uniformStartRed (ℓ : ℕ) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed =
      (v1SessionReds ℓ C K idA idB Dh encPt encT decT lam qep q).uniformStartRed := rfl

theorem v1SessionRedsPaper_challSimDF_eval (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (C : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (B_adv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hqB : DeliverForge.MakesAtMostQueriesDF B_adv q) :
    (v1SessionRedsPaper ℓ C K idA idB Dh encPt encT decT lam qep q).challSimDF.eval
      (fun _ => B_adv) () =
    DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) B_adv :=
  Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper.compileSmDFAtomic_challSimDF'PaperProg_eval
    Dh encPt C ℓ hℓ encT (idsOf idA idB) lam (qep + 1) q B_adv hqB

theorem v1SessionRedsPaper_B_cka_advantage_df (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (Z : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tStar : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q)
    (hsh_df : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv) :
    let P := paramsV1 Z K idA idB
    let challAdvDF := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    CKA.advantage (dhScheme Dh) 1 tStar
      (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q).B_cka
        tL t).eval (fun _ => challAdvDF) ()) =
    CKA.advantage (dhScheme Dh) 1 tStar
      (Proofs.Refinement.redCKAHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
        tL t dfAdv) :=
  Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper.compileCkaDFAtomic_casePaper_advantage
    Dh encPt Z ℓ hℓ encT (idsOf idA idB) lam 1 tStar (qep + 1) q tL t
    (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
    (challSimDF'Paper_queries (2 + 1) (qep + 1) dfAdv hq_df)
    (challSimDF'Paper_sendOk (2 + 1) (qep + 1) _ dfAdv hsh_df)

theorem v1SessionRedsPaper_B_prng_advantage_df (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (Z : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q)
    (hsh_df : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv) :
    let P := paramsV1 Z K idA idB
    let challAdvDF := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    PRFPRNG.advantage (rootPRNG Z.F encPt)
      (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT
        lam qep q).B_prng tL t).eval (fun _ => challAdvDF) ()) =
    PRFPRNG.advantage (rootPRNG Z.F encPt)
      (Proofs.Refinement.redPRNGHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
        tL t dfAdv) :=
  Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper.compilePrngDFAtomic_casePaper_advantage
    Dh encPt Z ℓ hℓ encT (idsOf idA idB) lam (qep + 1) q tL t
    (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
    (challSimDF'Paper_queries (2 + 1) (qep + 1) dfAdv hq_df)
    (challSimDF'Paper_sendOk (2 + 1) (qep + 1) _ dfAdv hsh_df)

theorem v1SessionRedsPaper_B_fs_advantage_df (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (Z : Crypto) (K : MlKem)
    (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q j : ℕ)
    (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q)
    (hsh_df : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv) :
    let P := paramsV1 Z K idA idB
    let challAdvDF := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) maxForwardJumps)
      (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT
        lam qep q).B_fs j tL t).eval (fun _ => challAdvDF) ()) =
    FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) maxForwardJumps)
      (Proofs.Refinement.redFSHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
        j tL t dfAdv) :=
  Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper.compileFsDFAtomic_casePaper_advantage
    Dh encPt Z ℓ hℓ encT (idsOf idA idB) lam (qep + 1) q j tL t
    (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv)
    (challSimDF'Paper_queries (2 + 1) (qep + 1) dfAdv hq_df)
    (challSimDF'Paper_sendOk (2 + 1) (qep + 1) _ dfAdv hsh_df)

theorem v1SessionRedsPaper_B_fs_fsOk_df (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (Z : Crypto) (K : MlKem) (idA idB : IdentityKey) (Dh : CKA.DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q j : ℕ) (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q)
    (hsh_df : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv)
    (hg_df : GuardedSMDFShort dfAdv) :
    let challAdvDF := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    FsOk ℓ (min (2 * q) (q + 2)) q
      (((v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT
        lam qep q).B_fs j tL t).eval (fun _ => challAdvDF) ()) := by
  intro challAdvDF
  have hq_ch : challAdvDF.IsQueryBoundP (· matches .inr _) q :=
    (challSimDF'Paper_queries (2 + 1) (qep + 1) dfAdv hq_df).of_imp (by rintro (_ | _) <;> simp)
  exact
    ⟨Computational.Proofs.HeadlineV1.DeliverForgePaperUnshiftedPotOK.redFSAuthDFCasePaperAtomicProg_makesAtMostQueries
        ℓ Z Dh encPt encT (idsOf idA idB) lam (qep + 1) q j tL t challAdvDF hq_ch,
     (Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper.compileFsDFAtomic_casePaper_challSimDF'Paper_fsOk_and_encAtomicShort
        Dh encPt Z ℓ hℓ encT (idsOf idA idB) lam (qep + 1) q j tL t dfAdv hq_df hsh_df hg_df).1.2⟩

/-- Bounds `hiddenSaltCellTermPaperDF` at `(tL, t)` by the corresponding cell of
`hiddenSaltBoundV1` evaluated on `v1SessionRedsPaper`. -/
theorem hiddenSaltCellTermPaperDF_le_v1SessionRedsPaper
    (Z : Crypto) (K : MlKem) (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (_hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
    (tL : Option ℕ) (t : ℕ)
    (dfAdv : DeliverForge.AdversaryDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q)
    (hsh_df : SendMsgsOkDF (fun m : LibsignalMsgPublicPart × Plain ℓ => atomicShortPubB m.1) dfAdv)
    (hg_df : GuardedSMDFShort dfAdv) :
    let P := paramsV1 Z K idA idB
    let R := v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q
    let challAdvDF := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv
    Proofs.Refinement.hiddenSaltCellTermPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep q
        tL t dfAdv ≤
      CKA.advantage (dhScheme Dh) 1 (healEpoch tL) ((R.B_cka tL t).eval (fun _ => challAdvDF) ()) +
        PRFPRNG.advantage (rootPRNG Z.F encPt) (((R.B_prng tL t).eval (fun _ => challAdvDF) ())) +
        (∑ j ∈ Finset.range q, CryptoVerification.E2E.fsAeadSlotSumBound Z (min (2 * q) (q + 2)) R.fs
          (((R.B_fs j tL t).eval (fun _ => challAdvDF) ()))) +
        4 * (q : ℝ≥0∞) * CryptoVerification.LibsignalSession.macForgeryTerm Z q := by
  intro P R challAdvDF
  have hL : LengthsOk P ℓ := lengthsOk_paramsIdsWithSpqr_v1 Z K idA idB ℓ hℓ
  have hcka := v1SessionRedsPaper_B_cka_advantage_df ℓ hℓ Z K idA idB Dh encPt encT decT
    lam qep q (healEpoch tL) tL t dfAdv hq_df hsh_df
  have hprng := v1SessionRedsPaper_B_prng_advantage_df ℓ hℓ Z K idA idB Dh encPt encT
    decT lam qep q tL t dfAdv hq_df hsh_df
  unfold Proofs.Refinement.hiddenSaltCellTermPaperDF
  change CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (Proofs.Refinement.redCKAHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
          tL t dfAdv) +
      PRFPRNG.advantage (rootPRNG Z.F encPt)
        (Proofs.Refinement.redPRNGHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
          tL t dfAdv) +
      (∑ j ∈ Finset.range q, FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000)
        (Proofs.Refinement.redFSHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
          j tL t dfAdv)) ≤ _
  rw [← hcka, ← hprng, add_assoc (_ + _)]; refine add_le_add le_rfl ?_
  calc ∑ j ∈ Finset.range q, FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) 25000)
        (Proofs.Refinement.redFSHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
          j tL t dfAdv)
      ≤ ∑ j ∈ Finset.range q,
          (CryptoVerification.E2E.fsAeadSlotSumBound Z (min (2 * q) (q + 2)) R.fs
            (((R.B_fs j tL t).eval (fun _ => challAdvDF) ())) +
            4 * CryptoVerification.LibsignalSession.macForgeryTerm Z q) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hfs_adv := v1SessionRedsPaper_B_fs_advantage_df ℓ hℓ Z K idA idB Dh encPt
          encT decT lam qep q j tL t dfAdv hq_df hsh_df
        have hfsOk := v1SessionRedsPaper_B_fs_fsOk_df ℓ hℓ Z K idA idB Dh encPt
          encT decT lam qep q j tL t dfAdv hq_df hsh_df hg_df
        have hshort :=
          (Computational.Proofs.SessionCostedFig8.DFFsAtomicBSwapPaper.compileFsDFAtomic_casePaper_challSimDF'Paper_fsOk_and_encAtomicShort
            Dh encPt Z ℓ hℓ encT (idsOf idA idB) lam (qep + 1) q j tL t dfAdv hq_df hsh_df hg_df).2
        change FSAEAD.advantage (lFS Z protoSignalCodec ℓ encT (idsOf idA idB) maxForwardJumps)
            (Proofs.Refinement.redFSHiddenSaltPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep
              j tL t dfAdv) ≤ _
        rw [← hfs_adv, v1SessionRedsPaper_fs,
          deliverForgeFSCompBoundWith_inst_eq Z ℓ encT (idsOf idA idB) (min (2 * q) (q + 2)) hℓ hinj
            _ hfsOk.1 hshort, ← fsShortBound_eq_deliverForgeFSCompBound_add]
        exact fs_le_fsShortBound Z hD protoSignalCodec rfl ℓ hL.1 encT hinj hdum (idsOf idA idB)
          (min (2 * q) (q + 2)) q (by omega) _ hfsOk
    _ = (∑ j ∈ Finset.range q, CryptoVerification.E2E.fsAeadSlotSumBound Z (min (2 * q) (q + 2)) R.fs
          (((R.B_fs j tL t).eval (fun _ => challAdvDF) ()))) +
          4 * (q : ℝ≥0∞) * CryptoVerification.LibsignalSession.macForgeryTerm Z q := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

section SimDeliverForgeGuarded

set_option linter.unusedSectionVars false

open GuardedSafe
open CryptoGames.LibsignalSM.Proofs.SessionShort.SimAndSM
  (SimShortInv simShortInv_initSim smRespShort smRecvLong SimSafeS guardedSafeS_simSend
   inTransit_mem_and_ct mem_accept_trans)

private theorem guardedSafePost_fig8ToDFImpl_step {ℓ : ℕ}
    (t : (QueryBounds.FSpec Pt ℓ).Domain)
    (ht : ¬ smRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt) t)
    (sent : List (LibsignalSim.Fig8C Pt)) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun r => smRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt) t r.1)
      ((Proofs.Refinement.fig8ToDFImpl Pt ℓ t).run sent) := by
  have hQt : ¬ smDFRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt)
      (toDFDom t) := by
    rcases t with _ | _
    · exact not_false
    · exact ht
  have hq := GuardedSafePost.query
    (RespOk := smDFRespShort (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    hQt
  rcases t with (n | ((((⟨R, m, r⟩ | ⟨R, m₀, m₁, r⟩) | ⟨R, c⟩) | ⟨R, c⟩) | R))
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ) (toDFDom (.inl n)) >>=
      fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial
  · unfold Proofs.Refinement.fig8ToDFImpl DeliverForge.transmitQueryDF
    rw [StateT.run_bind]
    have hlift : GuardedSafePost
        (smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (fun p : Option (LibsignalSim.Fig8C Pt) × List (LibsignalSim.Fig8C Pt) =>
          smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt)
            (.inr (.inl (.inl (.inl (.inl (R, m, r)))))) p.1)
        ((StateT.lift (query (spec := DFSpec Pt ℓ)
            (toDFDom (.inr (.inl (.inl (.inl (.inl (R, m, r)))))))) :
          Proofs.Refinement.DeliverForgeM Pt ℓ _).run sent) := by
      dsimp only [StateT.lift, StateT.run]
      exact hq.bind fun _ ha => GuardedSafePost.pure ha
    refine hlift.bind fun ⟨res, sent'⟩ hres => ?_
    cases res <;>
      (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind];
       exact GuardedSafePost.pure hres)
  · unfold Proofs.Refinement.fig8ToDFImpl DeliverForge.challQueryDF
    rw [StateT.run_bind]
    have hlift : GuardedSafePost
        (smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (fun p : Option (LibsignalSim.Fig8C Pt) × List (LibsignalSim.Fig8C Pt) =>
          smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt)
            (.inr (.inl (.inl (.inl (.inr (R, m₀, m₁, r)))))) p.1)
        ((StateT.lift (query (spec := DFSpec Pt ℓ)
            (toDFDom (.inr (.inl (.inl (.inl (.inr (R, m₀, m₁, r)))))))) :
          Proofs.Refinement.DeliverForgeM Pt ℓ _).run sent) := by
      dsimp only [StateT.lift, StateT.run]
      exact hq.bind fun _ ha => GuardedSafePost.pure ha
    refine hlift.bind fun ⟨res, sent'⟩ hres => ?_
    cases res <;>
      (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind];
       exact GuardedSafePost.pure hres)
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inl (.inl (.inr (R, c)))))) >>= fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inl (.inr (R, c))))) >>= fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial
  · show GuardedSafePost _ _ _ (query (spec := DFSpec Pt ℓ)
      (toDFDom (.inr (.inr R))) >>= fun a => pure (a, sent))
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial

private theorem guardedSafePost_deliverForgeHook_lift {ℓ : ℕ} {α : Type} {P : α → Prop}
    {x : LibsignalSim.Fig8Comp Pt ℓ α}
    (hx : GuardedSafePost
      (smRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      P x)
    (sent : List (LibsignalSim.Fig8C Pt)) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun r => P r.1)
      (((Proofs.Refinement.deliverForgeHook Pt ℓ).lift x).run sent) := by
  dsimp only [Proofs.Refinement.deliverForgeHook]
  induction hx generalizing sent with
  | pure h =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact GuardedSafePost.pure (P := fun r : α × List (LibsignalSim.Fig8C Pt) => P r.1) h
  | @query_bind t mx hQt _ ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    have hlift : GuardedSafePost
        (smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (fun r : (QueryBounds.FSpec Pt ℓ).Range t × List (LibsignalSim.Fig8C Pt) =>
          smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt) t r.1)
        ((liftM (Proofs.Refinement.fig8ToDFImpl Pt ℓ t) :
          Proofs.Refinement.DeliverForgeM Pt ℓ _).run sent) := by
      simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using
        guardedSafePost_fig8ToDFImpl_step t hQt sent
    exact hlift.bind fun pu hpu => ih pu.1 hpu pu.2

private abbrev DFSafePost (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (oa : DeliverForge.AdversaryCompDF (LibsignalSim.Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt)
      (α × (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ × List (LibsignalSim.Fig8C Pt)))) :
    Prop :=
  GuardedSafePost
    (smDFRespShort (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (fun r => True ∧ SimShortInv r.2.1.base) oa

private def dfSafeC (PQ Pt : Type) (ℓ : ℕ) {α : Type}
    (x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (sent : List (LibsignalSim.Fig8C Pt)),
    SimShortInv sC.base →
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun p => SimShortInv p.1.2.base) ((x.run sC).run sent)

private theorem dfSafePost_runDFM {PQ : Type} {ℓ : ℕ} {α : Type}
    {x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    (hx : dfSafeC PQ Pt ℓ x)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base) :
    DFSafePost PQ Pt ℓ (LibsignalSim.runDFM x sC ex) := by
  unfold LibsignalSim.runDFM
  exact (hx sC ex hs).bind fun _ hp => GuardedSafePost.pure ⟨trivial, hp⟩

private theorem dfSafeC_pure {PQ : Type} {ℓ : ℕ} {α : Type} (a : α) :
    dfSafeC PQ Pt ℓ (pure a) := fun sC sent hs => by
  simp only [StateT.run_pure]
  exact GuardedSafePost.pure
    (P := fun p : (α × LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
        List (LibsignalSim.Fig8C Pt) => SimShortInv p.1.2.base)
    hs

private theorem dfSafeC_bind {PQ : Type} {ℓ : ℕ} {α β : Type}
    {x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    {f : α → StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) β}
    (hx : dfSafeC PQ Pt ℓ x) (hf : ∀ a, dfSafeC PQ Pt ℓ (f a)) :
    dfSafeC PQ Pt ℓ (x >>= f) := fun sC sent hs => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (hx sC sent hs).bind fun p hp => hf p.1.1 p.1.2 p.2 hp

private theorem dfSafeC_get_bind {PQ : Type} {ℓ : ℕ} {α : Type}
    {f : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ →
      StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
        (Proofs.Refinement.DeliverForgeM Pt ℓ) α}
    (hf : ∀ sC, SimShortInv sC.base → dfSafeC PQ Pt ℓ (f sC)) :
    dfSafeC PQ Pt ℓ (get >>= f) := fun sC sent hs => by
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  exact hf sC hs sC sent hs

private theorem dfSafeC_set {PQ : Type} {ℓ : ℕ}
    (sC' : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (h : SimShortInv sC'.base) :
    dfSafeC PQ Pt ℓ (set sC') := fun _ _ _ => by
  simp only [StateT.run_set, StateT.run_pure]
  exact GuardedSafePost.pure
    (P := fun p : (PUnit × LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
        List (LibsignalSim.Fig8C Pt) => SimShortInv p.1.2.base)
    h

private theorem dfSafeC_guardC {PQ : Type} {ℓ : ℕ} {α : Type}
    {x : StateT (LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
      (Proofs.Refinement.DeliverForgeM Pt ℓ) (Option α)}
    (hx : dfSafeC PQ Pt ℓ x) :
    dfSafeC PQ Pt ℓ (LibsignalSimC.guardC x) := by
  unfold LibsignalSimC.guardC
  refine dfSafeC_get_bind fun _ _ => ?_
  split
  · exact dfSafeC_pure none
  · exact hx

private theorem dfSafeC_zoomB {PQ : Type} {ℓ : ℕ} {α : Type}
    {x : StateT (LibsignalSim.SimState PQ Pt ℓ) (LibsignalSim.Fig8Comp Pt ℓ) α}
    (hx : SimSafeS PQ Pt ℓ x) :
    dfSafeC PQ Pt ℓ
      (LibsignalSimC.runOnBaseState (Proofs.Refinement.deliverForgeHook Pt ℓ) x) :=
  fun sC sent hs => by
    show GuardedSafePost _ _ _
      (((Proofs.Refinement.deliverForgeHook Pt ℓ).lift (x.run sC.base) >>=
        fun p => pure (p.1, { sC with base := p.2 })).run sent)
    rw [StateT.run_bind]
    exact (guardedSafePost_deliverForgeHook_lift (hx sC.base hs) sent).bind fun p hp => by
      simp only [StateT.run_pure]
      exact GuardedSafePost.pure
        (P := fun r : (α × LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
            List (LibsignalSim.Fig8C Pt) => SimShortInv r.1.2.base)
        hp

private theorem dfSafeC_simSendC {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]
    (P : Params PQ PQC) {ℓ : ℕ} (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (LibsignalSim.Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    dfSafeC PQ Pt ℓ
      (LibsignalSimC.simSendC P qep fig (Proofs.Refinement.deliverForgeHook Pt ℓ) Q m₀ chal r) := by
  unfold LibsignalSimC.simSendC
  refine dfSafeC_bind (dfSafeC_zoomB (guardedSafeS_simSend P qep Q m₀ chal r)) fun res => ?_
  cases res with
  | none => exact dfSafeC_pure none
  | some w =>
    refine dfSafeC_get_bind fun _ hsC => ?_
    exact dfSafeC_bind (dfSafeC_set _ hsC) fun _ => dfSafeC_pure (some w)

private theorem dfSafeC_simCorrC {PQ PQC : Type} (P : Params PQ PQC) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encT : Pt → PublicKey) (Q : Party) :
    dfSafeC PQ Pt ℓ
      (LibsignalSimC.simCorrC P encT (Proofs.Refinement.deliverForgeHook Pt ℓ) Dh Q) := by
  unfold LibsignalSimC.simCorrC
  refine dfSafeC_get_bind fun sC hsC => ?_
  dsimp only
  split
  · exact dfSafeC_pure none
  · have hcorr : dfSafeC PQ Pt ℓ
        (LibsignalSimC.liftC (Proofs.Refinement.deliverForgeHook Pt ℓ)
          (SM.corrQuery (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256)
            (C := LibsignalSim.Fig8C Pt) Q)) := fun sC₁ sent hs₁ => by
      show GuardedSafePost _ _ _
        (((Proofs.Refinement.deliverForgeHook Pt ℓ).lift (SM.corrQuery Q) >>=
          fun a => pure (a, sC₁)).run sent)
      rw [StateT.run_bind]
      have hq : GuardedSafePost
          (smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
          (smRecvLong (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
          (fun _ => True) (SM.corrQuery Q) := by
        unfold SM.corrQuery
        exact GuardedSafePost.query
          (spec := QueryBounds.FSpec Pt ℓ)
          (RespOk := smRespShort (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
          (Q := smRecvLong (St := LibsignalSim.Fig8St Pt)
            (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
          (t := Sum.inr (Sum.inr Q))
          not_false
      exact (guardedSafePost_deliverForgeHook_lift hq sent).bind fun _ _ => by
        simp only [StateT.run_pure]
        exact GuardedSafePost.pure
          (P := fun r : (Option (LibsignalSim.Fig8St Pt) ×
                LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ) ×
              List (LibsignalSim.Fig8C Pt) => SimShortInv r.1.2.base)
          hs₁
    refine dfSafeC_bind hcorr fun res => ?_
    cases res with
    | none => exact dfSafeC_pure none
    | some _ => exact dfSafeC_bind (dfSafeC_set _ ⟨hsC.1, hsC.2⟩) fun _ => dfSafeC_pure _

private theorem simShortInv_onAcceptPure {PQ : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (s : LibsignalSim.SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (LibsignalSim.onAcceptPure qep Q w isDel t i m ci? T pq' s).2 := by
  unfold LibsignalSim.onAcceptPure
  dsimp only
  split_ifs
  · rcases s.mir.inTransit Q.other w with _ | r
    · exact hs
    · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact hs
  · exact ⟨fun rec hrec => hs.1 rec (mem_accept_trans hrec), hs.2⟩
  · exact ⟨hs.1, hs.2⟩

private theorem simShortInv_onAnswerPure {PQ : Type} {ℓ : ℕ} (qep : ℕ) (Q : Party)
    (w : Bytes) (isDel : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (res : Option (SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)))
    (s : LibsignalSim.SimState PQ Pt ℓ) (hs : SimShortInv s) :
    SimShortInv (LibsignalSim.onAnswerPure qep Q w isDel ci? T pq' res s).2 := by
  unfold LibsignalSim.onAnswerPure
  rcases res with _ | (_ | ⟨t, i, pm⟩)
  · exact hs
  · exact hs
  · exact simShortInv_onAcceptPure qep Q w isDel t i _ ci? T pq' s hs

private theorem guardedSafePost_deliverQueryDF {ℓ : ℕ} (Q : Party)
    (c : LibsignalSim.Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun _ => True)
      (DeliverForge.deliverQueryDF
        (St := LibsignalSim.Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := LibsignalSim.Fig8C Pt) Q c) := by
  unfold DeliverForge.deliverQueryDF
  exact GuardedSafePost.query
    (spec := DFSpec Pt ℓ)
    (RespOk := smDFRespShort (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (Q := smDFRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (t := Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Q, c))))))
    (fun h => h hc)

private theorem guardedSafePost_injectQueryDF {ℓ : ℕ} (Q : Party)
    (c : LibsignalSim.Fig8C Pt) (hc : c.2.2.1.1.length < 2 ^ 32) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun _ => True)
      (DeliverForge.injectQueryDF
        (St := LibsignalSim.Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
        (Coins := BitVec 256) (C := LibsignalSim.Fig8C Pt) Q c) := by
  unfold DeliverForge.injectQueryDF
  exact GuardedSafePost.query
    (spec := DFSpec Pt ℓ)
    (RespOk := smDFRespShort (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (Q := smDFRecvLong (St := LibsignalSim.Fig8St Pt)
      (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
    (t := Sum.inr (Sum.inl (Sum.inl (Sum.inr (Q, c)))))
    (fun h => h hc)

private theorem guardedSafePost_deliverForgeSemHook_onProbe {PQC : Type} [SampleableType PQC]
    {ℓ : ℕ} (Q : Party) (c' : LibsignalSim.Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32)
    (ex : List (LibsignalSim.Fig8C Pt)) :
    GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun _ => True)
      ((LibsignalSim.deliverForgeSemHook (PQC := PQC) (Pt := Pt) (ℓ := ℓ)).onProbe Q c' ex) := by
  unfold LibsignalSim.deliverForgeSemHook
  dsimp only
  rcases ex.find? (fun c => Proofs.Refinement.sameWireFig8 c c') with _ | c
  · exact GuardedSafePost.pure trivial
  · have hq : GuardedSafePost
        (smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (fun _ => True)
        (DeliverForge.deliverForgeQuery
          (St := LibsignalSim.Fig8St Pt) (Msg := LibsignalMsgPublicPart × Plain ℓ)
          (Coins := BitVec 256) (C := LibsignalSim.Fig8C Pt) Q c c') := by
      unfold DeliverForge.deliverForgeQuery
      exact GuardedSafePost.query
        (spec := DFSpec Pt ℓ)
        (RespOk := smDFRespShort (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (Q := smDFRecvLong (St := LibsignalSim.Fig8St Pt)
          (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (T := Pt))
        (t := Sum.inr (Sum.inr (Q, c, c')))
        (fun h => h hc')
    exact hq.bind fun _ _ => GuardedSafePost.pure trivial

private theorem dfSafePost_semFwdAnswerHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : LibsignalSim.Fig8C Pt)
    (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semFwdAnswerHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w isDel ci? Tpk pq' c') := by
  unfold LibsignalSim.semFwdAnswerHook LibsignalSim.deliverForgeSemHook
  dsimp only
  refine GuardedSafePost.bind (P := fun _ => True) ?_ fun ⟨res, ex₁⟩ _ =>
    GuardedSafePost.pure ⟨trivial, simShortInv_onAnswerPure qep Q w isDel ci? Tpk pq' res sC.base hs⟩
  split_ifs
  · exact (guardedSafePost_deliverQueryDF Q c' hc').bind fun _ _ => GuardedSafePost.pure trivial
  · exact (guardedSafePost_injectQueryDF Q c' hc').bind fun _ _ => GuardedSafePost.pure trivial

private theorem dfSafePost_semResyncHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : LibsignalSim.Fig8C Pt)
    (hc : c.2.2.1.1.length < 2 ^ 32)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semResyncHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w ci? Tpk pq' c r) := by
  unfold LibsignalSim.semResyncHook LibsignalSim.deliverForgeSemHook
  rcases r with _ | ⟨t, i, _, m'⟩
  · exact GuardedSafePost.pure ⟨trivial, hs⟩
  · dsimp only
    refine GuardedSafePost.bind (P := fun _ => True)
      ((guardedSafePost_deliverQueryDF Q c hc).bind fun _ _ => GuardedSafePost.pure trivial)
      fun ⟨res, ex₁⟩ _ => ?_
    rcases res with _ | (_ | _)
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · exact GuardedSafePost.pure
        ⟨trivial, simShortInv_onAcceptPure qep Q w true t i m' ci? Tpk pq' sC.base hs⟩

private theorem dfSafePost_semFwdEvictHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : LibsignalSim.Fig8C Pt)
    (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semFwdEvictHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep sC ex Q w isDel Tpk pq' c') := by
  unfold LibsignalSim.semFwdEvictHook
  split_ifs
  · exact (guardedSafePost_deliverForgeSemHook_onProbe (PQC := PQC) Q c' hc' ex).bind
      fun _ _ => GuardedSafePost.pure ⟨trivial, hs⟩
  · exact dfSafePost_semFwdAnswerHook P Dh encPt encT lam qep sC ex hs Q w isDel none Tpk pq' c' hc'

private theorem dfSafePost_semFwdHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt) (qep B : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (honestC : Option (LibsignalSim.Fig8C Pt))
    (hhon : ∀ c, honestC = some c → c.2.2.1.1.length < 2 ^ 32)
    (c' : LibsignalSim.Fig8C Pt) (hc' : c'.2.2.1.1.length < 2 ^ 32) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semFwdHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
        qep B sC ex Q w isDel ci? Tpk pq' honestC c') := by
  unfold LibsignalSim.semFwdHook
  rcases honestC with _ | c
  · exact dfSafePost_semFwdAnswerHook P Dh encPt encT lam qep sC ex hs Q w isDel ci? Tpk pq' c' hc'
  · dsimp only
    split_ifs
    · rcases LibsignalSim.evalCKClamp P Dh encPt encT lam B sC Q w c c' with _ | r
      · exact (guardedSafePost_deliverForgeSemHook_onProbe (PQC := PQC) Q c' hc' ex).bind
          fun _ _ => GuardedSafePost.pure ⟨trivial, hs⟩
      · exact dfSafePost_semResyncHook P Dh encPt encT lam qep sC ex hs Q w ci? Tpk pq' c
          (hhon c rfl) r
    · exact dfSafePost_semFwdAnswerHook P Dh encPt encT lam qep sC ex hs Q w isDel ci? Tpk pq' c' hc'

private theorem simParseRecvC_ser_eq {PQ PQC : Type} (P : Params PQ PQC)
    (decT : PublicKey → Option Pt) (B : ℕ) (qB : Bool) (pq : PQ) (w : Bytes)
    {pq' : PQ} {i : ℕ} {pk : PublicKey} {T? : Option Pt} {lct : ℕ × LibsignalCiphertextWithSalt32}
    (hp : LibsignalSim.simParseRecvC P decT B qB pq w = some (pq', (i, (pk, (T?, lct))))) :
    lct.2.1.1 = w.take (w.length - 8) := by
  unfold LibsignalSim.simParseRecvC at hp
  split_ifs at hp
  dsimp only [] at hp
  rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
  · rw [hparse] at hp; cases hp
  · rw [hparse] at hp; dsimp only [] at hp
    split_ifs at hp
    rcases hspqr : P.spqr.recv pq h.pqRatchet with _ | ⟨pq1, salt⟩
    · rw [hspqr] at hp; cases hp
    · rw [hspqr] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      exact congrArg (fun x : ℕ × LibsignalCiphertextWithSalt32 => x.2.1.1) hp.2.2.2.2.symm

private theorem dfSafePost_semRecvHook {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] {ℓ : ℕ} (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep B : ℕ)
    (sC : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ)
    (ex : List (LibsignalSim.Fig8C Pt)) (hs : SimShortInv sC.base)
    (Q : Party) (w : Bytes) (isDel : Bool) :
    DFSafePost PQ Pt ℓ
      (LibsignalSim.semRecvHook P Dh encPt encT decT lam LibsignalSim.deliverForgeSemHook
        qep B sC ex Q w isDel) := by
  unfold LibsignalSim.semRecvHook
  dsimp only []
  cases href :
    (sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w))))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hp : LibsignalSim.simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w
      with _ | ⟨pq', i, pk, T?, lct⟩
    · exact GuardedSafePost.pure ⟨trivial, hs⟩
    · have hwlen : w.length < 2 ^ 32 := by
        cases isDel with
        | true =>
          rcases htr : sC.base.mir.inTransit Q.other w with _ | rec'
          · simp [htr] at href
          · obtain ⟨hmem, rfl⟩ := inTransit_mem_and_ct htr
            exact hs.1 rec' hmem
        | false =>
          by_cases hw9 : w.length < 9
          · omega
          · have hadm : ratchetKeyAdmissible P.codec decT encT w = true := by
              revert href
              cases ratchetKeyAdmissible P.codec decT encT w <;> simp
            unfold ratchetKeyAdmissible at hadm
            simp only [hw9, ↓reduceIte] at hadm
            have hp0 := hp
            unfold LibsignalSim.simParseRecvC at hp0
            split_ifs at hp0
            dsimp only [] at hp0
            rcases hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
            · rw [hparse] at hp0; cases hp0
            · simp only [hparse, Bool.and_eq_true, decide_eq_true_eq] at hadm
              exact hadm.1
      have hlct : lct.2.1.1.length < 2 ^ 32 := by
        rw [simParseRecvC_ser_eq P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w hp,
          List.length_take]
        omega
      have hhon : ∀ c : LibsignalSim.Fig8C Pt,
          (sC.base.honest.find? fun (wc : Bytes × LibsignalSim.Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
              (fun (wc : Bytes × LibsignalSim.Fig8C Pt) => wc.2) = some c →
          c.2.2.1.1.length < 2 ^ 32 := by
        intro c hc_eq
        rcases Option.mem_map.mp hc_eq with ⟨wc, hfind, rfl⟩
        exact hs.2 wc (List.mem_of_find?_eq_some hfind)
      have hmkC : ∀ (t : ℕ) (To : Option Pt),
          (match (sC.base.honest.find? fun (wc : Bytes × LibsignalSim.Fig8C Pt) =>
               wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map
                 (fun (wc : Bytes × LibsignalSim.Fig8C Pt) => wc.2) with
           | some (c : LibsignalSim.Fig8C Pt) =>
             if c.2.2.2 = lct.2.2 then c else ((t, To), lct)
           | none => ((t, To), lct)).2.2.1.1.length < 2 ^ 32 := by
        intro t To
        rcases hfind : sC.base.honest.find? (fun (wc : Bytes × LibsignalSim.Fig8C Pt) =>
            wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with _ | wc
        · exact hlct
        · simp only [Option.map]
          split
          · exact hs.2 wc (List.mem_of_find?_eq_some hfind)
          · exact hlct
      rcases hidx : (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx]
      · have hsAmb : SimShortInv
            ({ sC with base :=
                if inReceiveOnlyEpoch sC.base.mir Q ||
                    (Q == Party.A && (sC.base.chains Q).any (·.key.isNone)) then
                  { sC.base with amb := sC.base.amb + 1 }
                else sC.base }).base := by
          dsimp only
          split_ifs <;> exact ⟨hs.1, hs.2⟩
        cases h1 :
          (((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) ==
            some true &&
          ((Option.map (fun x => x.2)
              (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                sC.base.honest)).map fun c => decide (c.2.2.2 = lct.2.2)) ==
            some true)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases h2 : (T? == some 0)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases h3 : (inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i))
            · simp only [Bool.false_eq_true, ↓reduceIte]
              rcases T? with _ | T
              · exact GuardedSafePost.pure ⟨trivial, hsAmb⟩
              · cases h4 :
                  (((Option.map (fun x => x.2)
                      (List.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other)
                        sC.base.honest)).map fun c =>
                    decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true)
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  exact dfSafePost_semFwdHook P Dh encPt encT lam qep B _ ex hsAmb
                    Q w isDel none pk pq' _ hhon _ (hmkC _ _)
                · simp only [↓reduceIte]
                  exact dfSafePost_semFwdEvictHook P Dh encPt encT lam qep _ ex hsAmb
                    Q w isDel pk pq' _ hlct
            · simp only [↓reduceIte]
              exact GuardedSafePost.pure ⟨trivial, hsAmb⟩
          · simp only [↓reduceIte]
            exact GuardedSafePost.pure ⟨trivial, hs⟩
        · simp only [↓reduceIte]
          exact GuardedSafePost.pure ⟨trivial, hs⟩
      · cases h5 :
          ((sC.base.chains Q).getD ci { key := none, epoch := 0, last := 0, skipped := [] }).rejects
            i
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact dfSafePost_semFwdHook P Dh encPt encT lam qep B sC ex hs
            Q w isDel (some ci) pk pq' _ hhon _ (hmkC _ _)
        · simp only [↓reduceIte]
          exact GuardedSafePost.pure ⟨trivial, hs⟩
  · simp only [↓reduceIte]
    exact GuardedSafePost.pure ⟨trivial, hs⟩

theorem simDeliverForgeClamp_guardedSMDFShort {PQ PQC : Type} [Inhabited PQ]
    [SampleableType PQC] (P : Params PQ PQC) {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep B : ℕ)
    (A : SM.Adversary (GhostState PQ) (CBC.Plain ℓ) PQC Bytes) :
    GuardedSMDFShort (LibsignalSim.simDeliverForgeClamp P Dh encPt encT decT lam qep B A) := by
  unfold GuardedSMDFShort LibsignalSim.simDeliverForgeClamp
  refine (GuardedSafePost.liftComp_unif hQu_smDFRecvLong ($ᵗ BitVec 256)).bind fun pqrKey _ => ?_
  rw [StateT.run'_eq]
  have hsim : GuardedSafePost
      (smDFRespShort (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (smDFRecvLong (St := LibsignalSim.Fig8St Pt)
        (Msg := LibsignalMsgPublicPart × CBC.Plain ℓ) (Coins := BitVec 256) (T := Pt))
      (fun r => SimShortInv r.2.1.base)
      ((simulateQ (LibsignalSim.simDeliverForgeOracle P Dh encPt encT decT lam qep B) A).run
        (LibsignalSimC.initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey), [])) := by
    refine GuardedSafePost.simulateQ_run
      (I := fun p : LibsignalSimC.LibsignalToModularSchemeSimState PQ Pt ℓ ×
          List (LibsignalSim.Fig8C Pt) => SimShortInv p.1.base)
      (GuardedSafePost.true_of_false A) ?_ (simShortInv_initSim _ _)
    rintro (n | ((((⟨Q, m, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)) _ ⟨sC, ex⟩ hs
    · show DFSafePost PQ Pt ℓ
        (query (spec := DFSpec Pt ℓ) (.inl n) >>= fun a => pure (a, (sC, ex)))
      exact (GuardedSafePost.query (hQu_smDFRecvLong n)).bind fun _ _ =>
        GuardedSafePost.pure ⟨trivial, hs⟩
    · change DFSafePost PQ Pt ℓ
        (LibsignalSim.semSendHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
          qep sC ex Q m none r)
      rw [LibsignalSim.semSendHook_deliverForge_eq]
      exact dfSafePost_runDFM (dfSafeC_guardC (dfSafeC_simSendC P qep _ Q m none r)) sC ex hs
    · change DFSafePost PQ Pt ℓ
        (LibsignalSim.semSendHook P Dh encPt encT lam LibsignalSim.deliverForgeSemHook
          qep sC ex Q m₀ (some m₁) r)
      rw [LibsignalSim.semSendHook_deliverForge_eq]
      exact dfSafePost_runDFM (dfSafeC_guardC (dfSafeC_simSendC P qep _ Q m₀ (some m₁) r)) sC ex hs
    · change DFSafePost PQ Pt ℓ
        (LibsignalSim.semRecvHook P Dh encPt encT decT lam LibsignalSim.deliverForgeSemHook
          qep B sC ex Q w true >>= fun ⟨rr, sC₁, ex₁⟩ =>
            (LibsignalSim.deliverForgeSemHook (PQC := PQC)).onDeliverPost Q none rr ex₁ >>=
              fun ex₂ => pure (rr, (sC₁, ex₂)))
      exact (dfSafePost_semRecvHook P Dh encPt encT decT lam qep B sC ex hs Q w true).bind
        fun ⟨rr, sC₁, ex₁⟩ ⟨_, hs₁⟩ => by
          dsimp only [LibsignalSim.deliverForgeSemHook]
          rw [pure_bind]
          exact GuardedSafePost.pure ⟨trivial, hs₁⟩
    · exact dfSafePost_semRecvHook P Dh encPt encT decT lam qep B sC ex hs Q w false
    · change DFSafePost PQ Pt ℓ
        (LibsignalSim.semCorrHook P Dh encT LibsignalSim.deliverForgeSemHook sC ex Q)
      rw [LibsignalSim.semCorrHook_deliverForge_eq]
      exact dfSafePost_runDFM (dfSafeC_guardC (dfSafeC_simCorrC P Dh encT Q)) sC ex hs
  exact hsim.map (R := fun _ => True) Prod.fst fun _ _ => trivial

end SimDeliverForgeGuarded

/-- Bounds the `admissibleLastLeakGuesses 2` cell sum of `hiddenSaltCellTermPaperDF` plus the
spurious and ratchet-key collision terms by `hiddenSaltBoundV1` on `v1SessionRedsPaper`. -/
theorem sum_hiddenSaltCellTermPaperDF_le_hiddenSaltBoundV1_paper
    (Z : Crypto) (K : MlKem) (hD : ∀ k x, Z.D k (Z.E k x) = x)
    {ℓ : ℕ} (hℓ : ℓ < 10 ^ 6) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idA idB : IdentityKey) (lam : Pt) (qep q : ℕ) (hq32 : 2 * (q + 1) + 25002 < 2 ^ 32)
    (δ : ℝ≥0∞)
    (A : SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
    (hq : SM.MakesAtMostQueries A q) :
    let P := paramsV1 Z K idA idB
    let R := v1SessionRedsPaper ℓ Z K idA idB Dh encPt encT decT lam qep q
    let dfAdv := R.simDeliverForge.eval (fun _ => A) ()
    (∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
      Proofs.Refinement.hiddenSaltCellTermPaperDF P ℓ Dh encPt encT (idsOf idA idB) lam qep q
        tL t dfAdv) +
      spuriousStepTerm Z.F encPt Dh q qep + (qep + 1) * (qep + 2) * δ ≤
    hiddenSaltBoundV1 Z K ℓ Dh encPt encT decT idA idB lam qep q δ R A := by
  intro P R dfAdv
  have hq_df : DeliverForge.MakesAtMostQueriesDF dfAdv q :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg_makesAtMostQueriesDF
      ℓ Z K idA idB Dh encPt encT decT lam qep q A hq
  have hsh_df : SendMsgsOkDF
      (fun m : LibsignalMsgPublicPart × CBC.Plain ℓ => atomicShortPubB m.1) dfAdv :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg_sendAtomicShortDF
      hℓ Z K idA idB Dh encPt encT decT lam qep q A hq
  have hg_df : GuardedSMDFShort dfAdv :=
    Computational.Proofs.Game.PromotedCostedReds.SimDeliverForgeProg.simDeliverForgeRedProg_guardedSMDFShort
      hℓ Z K idA idB Dh encPt encT decT lam qep q A hq
  have hchall : R.challSimDF.eval (fun _ => dfAdv) () =
      DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv :=
    v1SessionRedsPaper_challSimDF_eval ℓ hℓ Z K idA idB Dh encPt encT decT
      lam qep q dfAdv hq_df
  unfold hiddenSaltBoundV1; dsimp only
  rw [show R.challSimDF.eval (fun _ => R.simDeliverForge.eval (fun _ => A) ()) () =
        DeliverForge.challSimDF'Paper (2 + 1) (qep + 1) dfAdv from hchall]
  gcongr with t _ tL _
  exact hiddenSaltCellTermPaperDF_le_v1SessionRedsPaper Z K hD hℓ Dh encPt encT decT hinj hdum
    idA idB lam qep q hq32 tL t dfAdv hq_df hsh_df hg_df

end PaperEvalBridges
end CryptoVerification.E2E
