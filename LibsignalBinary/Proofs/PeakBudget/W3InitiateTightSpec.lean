/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.CallSiteFacts
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges
public import LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget

/-!
# Tight `fineCostModel` Spec for W3 `process_prekey_bundle`

Tightens `W3InitiatePeakSpec` on `fineCostModel` using per-size-class `SerCloneStorePeakSpec` store
poll deltas and `0`-prev Fresh-Alice / `aliceInitiatedSession` `SessionRecord::serialize` bounds,
yielding closed numerical caps at `sessionCapBytes` (`2 MiB`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ReceiverChain SenderChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SenderChainGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open VerifiedLibraries.Mallocng.Proofs (sizeToClassUnits)
open LibsignalBinary.Heap (AllocEvent BudgetLimits FitsEnv)
open LibsignalBinary.Heap.Fine (MmapThresholdReq fineCostModel fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_largeCost_eq fineCostModel_largeMetaCost_eq fineCostModel_smallMaxReq_eq
   reqMinOfClass smallAllocCost_eq_188_of_le_12)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps addressText_length_le dirDomainCaps_opened_own
   dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (fineDirPutCum fineDirPutLive fineReadFileCum fineReadFileLive fineReadFileMaxReq
   fineReadFilePeak optLargeCost optLargeCost_fine_of_gt optLargeCost_fine_of_le
   sessLoadPollTightDeltaCum sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak
   sessLoadPollTightMaxReq sessLoadPoll_phaseCredit_tight
   sessStorePollMaxReq sessStorePollTightDeltaCum sessStorePollTightDeltaLive
   sessStorePollTightDeltaPeak sessStorePoll_phaseCredit_tight
   smallStorePollTightDeltaCum smallStorePollTightDeltaLive smallStorePollTightDeltaPeak
   smallStorePollTightMaxReq smallStorePoll_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (chainCloneMaxReq chainCloneTightCum classBounds_of_le_mmap fineAllocClassWt
   optTailCloneLen rustAllocTightCum rustAllocTightCum_fine_32
   segCloneMaxReq segCloneTightCum tryCloneSmallDelta tryCloneSmallDelta_fine_le_738)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak recordSerializeTightCum
   serializeSomeMaxReq serializeSomeTightCum)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges
  (mkW3InitiateSlotParams peer_name_length_le_of_initCallSite
   recordSerializeOutLarge_le_peak recordSerializePeak_eq_zero_of_maxReq_le)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
  (W3InitiateSlotEnv W3InitiateSlotParams W3SessLoadStepEnv W3SessStoreStepEnv
   W3SmallStoreStepEnv w3BoxedStepCum w3BoxedStepLive w3BoxedStepMaxReq w3BoxedStepPeak
   w3BoxedStoreStep_phaseCredit w3SpqrInit32_phaseCredit w3SpqrInitCum w3SpqrInitLive
   w3SpqrInitPeak)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (phaseCreditSpec_w3InitiateFull_small w3InitiateNativeSmallCum)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.CallSiteFacts (InitCallSite)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (senderChainAsProtoGhost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineDynIvsOfCum fineStepReserveOfCum)

/-! ## 1. Size-Class Point and Range Lemmas on `fineCostModel` -/

private def fineW3PointPairs : List (Nat × Nat) :=
  [(104, 1997), (1568, 2792), (1569, 2792), (3700, 4218), (3820, 4218)]

private def checkFineW3Points : Bool :=
  fineW3PointPairs.all fun (req, expected) =>
    fineSmallAllocCost req == expected

private theorem checkFineW3Points_true : checkFineW3Points = true := by
  decide +kernel

private theorem extractFineW3Point {req expected : Nat}
    (hmem : (req, expected) ∈ fineW3PointPairs) :
    HasFineReallocCredit.smallAllocCost fineCostModel req = expected := by
  change fineSmallAllocCost req = expected
  have hcell := List.all_eq_true.mp checkFineW3Points_true (req, expected) hmem
  exact of_decide_eq_true hcell

theorem fineSmallAllocCost_104 : HasFineReallocCredit.smallAllocCost fineCostModel 104 = 1997 :=
  extractFineW3Point (by decide)

theorem fineSmallAllocCost_1568 : HasFineReallocCredit.smallAllocCost fineCostModel 1568 = 2792 :=
  extractFineW3Point (by decide)

theorem fineSmallAllocCost_3700 : HasFineReallocCredit.smallAllocCost fineCostModel 3700 = 4218 :=
  extractFineW3Point (by decide)

theorem fineSmallAllocCost_3820 : HasFineReallocCredit.smallAllocCost fineCostModel 3820 = 4218 :=
  extractFineW3Point (by decide)

theorem rustAllocTightCum_fine_104 : rustAllocTightCum fineCostModel 104 = 1997 := by
  unfold rustAllocTightCum
  rw [fineCostModel_smallMaxReq_eq]
  simp [fineSmallAllocCost_104]

theorem rustAllocTightCum_fine_1568 : rustAllocTightCum fineCostModel 1568 = 2792 := by
  unfold rustAllocTightCum
  rw [fineCostModel_smallMaxReq_eq]
  simp [fineSmallAllocCost_1568]

theorem rustAllocTightCum_fine_3700 : rustAllocTightCum fineCostModel 3700 = 4218 := by
  unfold rustAllocTightCum
  rw [fineCostModel_smallMaxReq_eq]
  simp [fineSmallAllocCost_3700]

theorem rustAllocTightCum_fine_3820 : rustAllocTightCum fineCostModel 3820 = 4218 := by
  unfold rustAllocTightCum
  rw [fineCostModel_smallMaxReq_eq]
  simp [fineSmallAllocCost_3820]

private def checkFineAllocCap3820 : Bool :=
  (List.range 48).all fun sc =>
    decide (reqMinOfClass sc ≤ 3820 → fineAllocClassWt sc ≤ 9789)

private theorem checkFineAllocCap3820_true : checkFineAllocCap3820 = true := by
  decide +kernel

/-- Upper bound `smallAllocCost fineCostModel req ≤ 9,789` across `req ≤ 3,820`. -/
theorem fineSmallAllocCost_le_9789_of_le_3820 {req : Nat} (hreq : req ≤ 3820) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  change fineSmallAllocCost req ≤ 9789
  unfold fineSmallAllocCost
  simp only [hm, ↓reduceIte]
  obtain ⟨hsc, hrmin, _⟩ := classBounds_of_le_mmap hm
  have hcell := List.all_eq_true.mp checkFineAllocCap3820_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell) (Nat.le_trans hrmin hreq)

theorem rustAllocTightCum_fine_le_9789_of_le_3820 {req : Nat} (hreq : req ≤ 3820) :
    rustAllocTightCum fineCostModel req ≤ 9789 := by
  unfold rustAllocTightCum
  have hsm : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact Nat.le_trans hreq (by decide)
  simp only [hsm, ↓reduceIte]
  exact fineSmallAllocCost_le_9789_of_le_3820 hreq

theorem tryCloneSmallDelta_fine_le_9789_of_le_3820 {len : Nat} (hlen : len ≤ 3820) :
    tryCloneSmallDelta fineCostModel len ≤ 9789 := by
  unfold tryCloneSmallDelta
  split
  · exact Nat.zero_le 9789
  · exact rustAllocTightCum_fine_le_9789_of_le_3820 hlen

theorem tryCloneSmallDelta_fine_kyber_w3_le_2792 {len : Nat}
    (h : len = 0 ∨ len = 1568 ∨ len = 1569) :
    tryCloneSmallDelta fineCostModel len ≤ 2792 := by
  rcases h with rfl | rfl | rfl
  · simp [tryCloneSmallDelta]
  · simp [tryCloneSmallDelta, rustAllocTightCum_fine_1568]
  · have h1569 : rustAllocTightCum fineCostModel 1569 = 2792 := by
      unfold rustAllocTightCum
      rw [fineCostModel_smallMaxReq_eq]
      simp [extractFineW3Point (req := 1569) (expected := 2792) (by decide)]
    simp [tryCloneSmallDelta, h1569]

theorem tryCloneSmallDelta_fine_pq3700_le_4218 {len : Nat}
    (h : len = 0 ∨ len = 3700) :
    tryCloneSmallDelta fineCostModel len ≤ 4218 := by
  rcases h with rfl | rfl
  · simp [tryCloneSmallDelta]
  · simp [tryCloneSmallDelta, rustAllocTightCum_fine_3700]

theorem rustAllocTightCum_fine_enc3820_le_4218 {req : Nat}
    (h : req = 0 ∨ req = 3820) :
    rustAllocTightCum fineCostModel req ≤ 4218 := by
  rcases h with rfl | rfl
  · unfold rustAllocTightCum
    rw [fineCostModel_smallMaxReq_eq]
    have h0 := smallAllocCost_eq_188_of_le_12 (req := 0) (by decide)
    simp [h0]
  · rw [rustAllocTightCum_fine_3820]

/-! ## 2. Fresh-Alice and `aliceInitiatedSession` `serialize` Bounds -/

private theorem senderChainCloneTight_le_2214 {gs : SenderChainGhost} (sc : SenderChain)
    (hsrk : gs.srk.bytes.length ≤ 44) (hpriv : gs.priv.bytes.length ≤ 44) :
    chainCloneTightCum fineCostModel (senderChainAsProtoGhost gs sc) ≤ 2214 := by
  unfold senderChainAsProtoGhost chainCloneTightCum
  dsimp only
  simp only [↓reduceIte, Nat.add_zero]
  have h1 := tryCloneSmallDelta_fine_le_738 hsrk
  have h2 := tryCloneSmallDelta_fine_le_738 hpriv
  rw [rustAllocTightCum_fine_32]
  omega

private theorem senderChainMaxReq_le_44 {gs : SenderChainGhost} (sc : SenderChain)
    (hsrk : gs.srk.bytes.length ≤ 44) (hpriv : gs.priv.bytes.length ≤ 44) :
    chainCloneMaxReq (senderChainAsProtoGhost gs sc) ≤ 44 := by
  unfold senderChainAsProtoGhost chainCloneMaxReq
  simp only [List.length_nil, List.map_nil, List.foldr_nil, Nat.mul_zero]
  omega

private theorem recvChainCloneTight_none_le_1476 {gc : ChainGhost} {rc : ReceiverChain}
    (hsrk : gc.srk.bytes.length ≤ 44) (hpriv : gc.priv.bytes.length ≤ 44)
    (hck : rc.chainKey = none) (hmks : rc.messageKeys = []) :
    chainCloneTightCum fineCostModel (gc, rc) ≤ 1476 := by
  unfold chainCloneTightCum
  dsimp only
  simp only [hck, hmks, ↓reduceIte, Nat.add_zero]
  have h1 := tryCloneSmallDelta_fine_le_738 hsrk
  have h2 := tryCloneSmallDelta_fine_le_738 hpriv
  omega

private theorem recvChainCloneTight_anyCk_le_2214 {gc : ChainGhost} {rc : ReceiverChain}
    (hsrk : gc.srk.bytes.length ≤ 44) (hpriv : gc.priv.bytes.length ≤ 44)
    (hmks : rc.messageKeys = []) :
    chainCloneTightCum fineCostModel (gc, rc) ≤ 2214 := by
  unfold chainCloneTightCum
  dsimp only
  simp only [hmks, ↓reduceIte, Nat.add_zero]
  have h1 := tryCloneSmallDelta_fine_le_738 hsrk
  have h2 := tryCloneSmallDelta_fine_le_738 hpriv
  cases rc.chainKey with
  | none =>
    dsimp only
    omega
  | some _ =>
    dsimp only
    rw [rustAllocTightCum_fine_32]
    omega

private theorem recvChainMaxReq_emptyMks_le_44 {gc : ChainGhost} {rc : ReceiverChain}
    (hsrk : gc.srk.bytes.length ≤ 44) (hpriv : gc.priv.bytes.length ≤ 44)
    (hmks : rc.messageKeys = []) :
    chainCloneMaxReq (gc, rc) ≤ 44 := by
  unfold chainCloneMaxReq
  dsimp only
  simp only [hmks, List.length_nil, List.map_nil, List.foldr_nil, Nat.mul_zero]
  omega

/-- `0`-recv-chain Fresh-Alice session bounds (`≤ 17,132` B). -/
structure FreshAlice0RecvBounds (G : SessionGhost) (sess : Session (List (BitVec 8))) : Prop where
  localIk_le : G.localIk.bytes.length ≤ 44
  remoteIk_le : G.remoteIk.bytes.length ≤ 44
  sender_le : ∀ gs, G.sender = some gs → gs.srk.bytes.length ≤ 44 ∧ gs.priv.bytes.length ≤ 44
  recv_nil : sess.state.receiverChains = []
  pending_le : optTailCloneLen G.pending ≤ 44
  kyber_eq : optTailCloneLen G.kyber = 0 ∨ optTailCloneLen G.kyber = 1568 ∨
    optTailCloneLen G.kyber = 1569
  alice_le : G.alice.bytes.length ≤ 44
  pq_eq : sess.state.pqRatchetState.length = 0 ∨ sess.state.pqRatchetState.length = 3700
  enc_eq : (lenField 1 (encSessionMem G sess)).length = 0 ∨
    (lenField 1 (encSessionMem G sess)).length = 3820

theorem segCloneTightCum_freshAlice0Recv_le_12914
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : FreshAlice0RecvBounds G sess) :
    segCloneTightCum fineCostModel G sess.state ≤ 12914 := by
  unfold segCloneTightCum
  have hloc := tryCloneSmallDelta_fine_le_738 hb.localIk_le
  have hrem := tryCloneSmallDelta_fine_le_738 hb.remoteIk_le
  have hroot := rustAllocTightCum_fine_32
  have hpend := tryCloneSmallDelta_fine_le_738 hb.pending_le
  have hkyb := tryCloneSmallDelta_fine_kyber_w3_le_2792 hb.kyber_eq
  have halice := tryCloneSmallDelta_fine_le_738 hb.alice_le
  have hpq := tryCloneSmallDelta_fine_pq3700_le_4218 hb.pq_eq
  simp only [hb.recv_nil, ↓reduceIte]
  cases hgs : G.sender <;> cases sess.state.senderChain <;> dsimp only
  · omega
  · omega
  · omega
  · rename_i gs sc
    obtain ⟨hsrk, hpriv⟩ := hb.sender_le gs hgs
    have hsnd := senderChainCloneTight_le_2214 sc hsrk hpriv
    omega

theorem serializeSomeTightCum_freshAlice0Recv_le_17132
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : FreshAlice0RecvBounds G sess) :
    serializeSomeTightCum fineCostModel G sess ≤ 17132 := by
  unfold serializeSomeTightCum
  have hcl := segCloneTightCum_freshAlice0Recv_le_12914 hb
  have henc := rustAllocTightCum_fine_enc3820_le_4218 hb.enc_eq
  omega

theorem serializeSomeMaxReq_freshAlice0Recv_le_3820
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : FreshAlice0RecvBounds G sess) :
    serializeSomeMaxReq G sess ≤ 3820 := by
  unfold serializeSomeMaxReq segCloneMaxReq
  have hkyb : optTailCloneLen G.kyber ≤ 1569 := by
    rcases hb.kyber_eq with h | h | h <;> omega
  have hpq : sess.state.pqRatchetState.length ≤ 3700 := by
    rcases hb.pq_eq with h | h <;> omega
  have henc : (lenField 1 (encSessionMem G sess)).length ≤ 3820 := by
    rcases hb.enc_eq with h | h <;> omega
  have hloc := hb.localIk_le
  have hrem := hb.remoteIk_le
  have hpend := hb.pending_le
  have halice := hb.alice_le
  simp only [hb.recv_nil, List.length_nil, List.zip_nil_right, List.map_nil, List.foldr_nil,
    Nat.mul_zero]
  cases hgs : G.sender <;> cases sess.state.senderChain <;> dsimp only
  · omega
  · omega
  · omega
  · rename_i gs sc
    obtain ⟨hsrk, hpriv⟩ := hb.sender_le gs hgs
    have hsnd := senderChainMaxReq_le_44 sc hsrk hpriv
    omega

/-- Restricted `0`-or-`1` empty-receiver-chain bounds (`rc0.chainKey = none`, `rc0.messageKeys = []`, `encLen ≤ 3,820`, `≤ 31,747` B).
-/
structure AliceInitiatedBounds (G : SessionGhost) (sess : Session (List (BitVec 8))) : Prop where
  localIk_le : G.localIk.bytes.length ≤ 44
  remoteIk_le : G.remoteIk.bytes.length ≤ 44
  sender_le : ∀ gs, G.sender = some gs → gs.srk.bytes.length ≤ 44 ∧ gs.priv.bytes.length ≤ 44
  recv_shape : sess.state.receiverChains = [] ∨
    ∃ rc0, sess.state.receiverChains = [rc0] ∧ rc0.chainKey = none ∧ rc0.messageKeys = []
  recv_ghost_le : ∀ gc ∈ G.chains.zip sess.state.receiverChains,
    gc.1.srk.bytes.length ≤ 44 ∧ gc.1.priv.bytes.length ≤ 44
  pending_le : optTailCloneLen G.pending ≤ 44
  kyber_eq : optTailCloneLen G.kyber = 0 ∨ optTailCloneLen G.kyber = 1568 ∨
    optTailCloneLen G.kyber = 1569
  alice_le : G.alice.bytes.length ≤ 44
  pq_le : sess.state.pqRatchetState.length ≤ 3820
  enc_le : (lenField 1 (encSessionMem G sess)).length ≤ 3820

theorem segCloneTightCum_aliceInitiated_le_21958
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : AliceInitiatedBounds G sess) :
    segCloneTightCum fineCostModel G sess.state ≤ 21958 := by
  unfold segCloneTightCum
  have hloc := tryCloneSmallDelta_fine_le_738 hb.localIk_le
  have hrem := tryCloneSmallDelta_fine_le_738 hb.remoteIk_le
  have hroot := rustAllocTightCum_fine_32
  have hrc : (if sess.state.receiverChains = [] then 0
      else rustAllocTightCum fineCostModel (104 * sess.state.receiverChains.length) +
        ((G.chains.zip sess.state.receiverChains).map
          (chainCloneTightCum fineCostModel)).sum) ≤ 3473 := by
    rcases hb.recv_shape with hnil | ⟨rc0, hrc1, hck, hmks⟩
    · simp [hnil]
    · have hrg := hb.recv_ghost_le
      rw [hrc1] at hrg ⊢
      simp only [List.cons_ne_self, ↓reduceIte, List.length_singleton, Nat.mul_one,
        rustAllocTightCum_fine_104]
      cases hgc : G.chains with
      | nil => simp
      | cons gc0 gcs =>
        rw [hgc] at hrg
        simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero]
        obtain ⟨hsrk, hpriv⟩ := hrg (gc0, rc0) (by simp)
        have hc0 := recvChainCloneTight_none_le_1476 (gc := gc0) hsrk hpriv hck hmks
        omega
  have hpend := tryCloneSmallDelta_fine_le_738 hb.pending_le
  have hkyb := tryCloneSmallDelta_fine_kyber_w3_le_2792 hb.kyber_eq
  have halice := tryCloneSmallDelta_fine_le_738 hb.alice_le
  have hpq := tryCloneSmallDelta_fine_le_9789_of_le_3820 hb.pq_le
  cases hgs : G.sender <;> cases sess.state.senderChain <;> dsimp only
  · omega
  · omega
  · omega
  · rename_i gs sc
    obtain ⟨hsrk, hpriv⟩ := hb.sender_le gs hgs
    have hsnd := senderChainCloneTight_le_2214 sc hsrk hpriv
    omega

theorem serializeSomeTightCum_aliceInitiated_le_31747
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : AliceInitiatedBounds G sess) :
    serializeSomeTightCum fineCostModel G sess ≤ 31747 := by
  unfold serializeSomeTightCum
  have hcl := segCloneTightCum_aliceInitiated_le_21958 hb
  have henc := rustAllocTightCum_fine_le_9789_of_le_3820 hb.enc_le
  omega

theorem serializeSomeMaxReq_aliceInitiated_le_3820
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : AliceInitiatedBounds G sess) :
    serializeSomeMaxReq G sess ≤ 3820 := by
  unfold serializeSomeMaxReq segCloneMaxReq
  have hrc : max (104 * sess.state.receiverChains.length)
      (((G.chains.zip sess.state.receiverChains).map chainCloneMaxReq).foldr max 0) ≤ 104 := by
    rcases hb.recv_shape with hnil | ⟨rc0, hrc1, _, hmks⟩
    · simp [hnil]
    · have hrg := hb.recv_ghost_le
      rw [hrc1] at hrg ⊢
      simp only [List.length_singleton, Nat.mul_one]
      cases hgc : G.chains with
      | nil => simp
      | cons gc0 gcs =>
        rw [hgc] at hrg
        simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil]
        obtain ⟨hsrk, hpriv⟩ := hrg (gc0, rc0) (by simp)
        have hc0 := recvChainMaxReq_emptyMks_le_44 (gc := gc0) hsrk hpriv hmks
        omega
  have hkyb : optTailCloneLen G.kyber ≤ 1569 := by
    rcases hb.kyber_eq with h | h | h <;> omega
  have hloc := hb.localIk_le
  have hrem := hb.remoteIk_le
  have hpend := hb.pending_le
  have halice := hb.alice_le
  have hpq := hb.pq_le
  have henc := hb.enc_le
  cases hgs : G.sender <;> cases sess.state.senderChain <;> dsimp only
  · omega
  · omega
  · omega
  · rename_i gs sc
    obtain ⟨hsrk, hpriv⟩ := hb.sender_le gs hgs
    have hsnd := senderChainMaxReq_le_44 sc hsrk hpriv
    omega

/-- `AliceInitiatedBounds` variant allowing an arbitrary `rc0.chainKey` (`≤ 32,485` B). -/
structure AliceInitiatedAnyCkBounds (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    Prop where
  localIk_le : G.localIk.bytes.length ≤ 44
  remoteIk_le : G.remoteIk.bytes.length ≤ 44
  sender_le : ∀ gs, G.sender = some gs → gs.srk.bytes.length ≤ 44 ∧ gs.priv.bytes.length ≤ 44
  recv_shape : sess.state.receiverChains = [] ∨
    ∃ rc0, sess.state.receiverChains = [rc0] ∧ rc0.messageKeys = []
  recv_ghost_le : ∀ gc ∈ G.chains.zip sess.state.receiverChains,
    gc.1.srk.bytes.length ≤ 44 ∧ gc.1.priv.bytes.length ≤ 44
  pending_le : optTailCloneLen G.pending ≤ 44
  kyber_eq : optTailCloneLen G.kyber = 0 ∨ optTailCloneLen G.kyber = 1568 ∨
    optTailCloneLen G.kyber = 1569
  alice_le : G.alice.bytes.length ≤ 44
  pq_le : sess.state.pqRatchetState.length ≤ 3820
  enc_le : (lenField 1 (encSessionMem G sess)).length ≤ 3820

theorem serializeSomeTightCum_aliceInitiatedAnyCk_le_32485
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : AliceInitiatedAnyCkBounds G sess) :
    serializeSomeTightCum fineCostModel G sess ≤ 32485 := by
  unfold serializeSomeTightCum segCloneTightCum
  have hloc := tryCloneSmallDelta_fine_le_738 hb.localIk_le
  have hrem := tryCloneSmallDelta_fine_le_738 hb.remoteIk_le
  have hroot := rustAllocTightCum_fine_32
  have hrc : (if sess.state.receiverChains = [] then 0
      else rustAllocTightCum fineCostModel (104 * sess.state.receiverChains.length) +
        ((G.chains.zip sess.state.receiverChains).map
          (chainCloneTightCum fineCostModel)).sum) ≤ 4211 := by
    rcases hb.recv_shape with hnil | ⟨rc0, hrc1, hmks⟩
    · simp [hnil]
    · have hrg := hb.recv_ghost_le
      rw [hrc1] at hrg ⊢
      simp only [List.cons_ne_self, ↓reduceIte, List.length_singleton, Nat.mul_one,
        rustAllocTightCum_fine_104]
      cases hgc : G.chains with
      | nil => simp
      | cons gc0 gcs =>
        rw [hgc] at hrg
        simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero]
        obtain ⟨hsrk, hpriv⟩ := hrg (gc0, rc0) (by simp)
        have hc0 := recvChainCloneTight_anyCk_le_2214 (gc := gc0) hsrk hpriv hmks
        omega
  have hpend := tryCloneSmallDelta_fine_le_738 hb.pending_le
  have hkyb := tryCloneSmallDelta_fine_kyber_w3_le_2792 hb.kyber_eq
  have halice := tryCloneSmallDelta_fine_le_738 hb.alice_le
  have hpq := tryCloneSmallDelta_fine_le_9789_of_le_3820 hb.pq_le
  have henc := rustAllocTightCum_fine_le_9789_of_le_3820 hb.enc_le
  cases hgs : G.sender <;> cases sess.state.senderChain <;> dsimp only
  · omega
  · omega
  · omega
  · rename_i gs sc
    obtain ⟨hsrk, hpriv⟩ := hb.sender_le gs hgs
    have hsnd := senderChainCloneTight_le_2214 sc hsrk hpriv
    omega

theorem serializeSomeMaxReq_aliceInitiatedAnyCk_le_3820
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : AliceInitiatedAnyCkBounds G sess) :
    serializeSomeMaxReq G sess ≤ 3820 := by
  unfold serializeSomeMaxReq segCloneMaxReq
  have hrc : max (104 * sess.state.receiverChains.length)
      (((G.chains.zip sess.state.receiverChains).map chainCloneMaxReq).foldr max 0) ≤ 104 := by
    rcases hb.recv_shape with hnil | ⟨rc0, hrc1, hmks⟩
    · simp [hnil]
    · have hrg := hb.recv_ghost_le
      rw [hrc1] at hrg ⊢
      simp only [List.length_singleton, Nat.mul_one]
      cases hgc : G.chains with
      | nil => simp
      | cons gc0 gcs =>
        rw [hgc] at hrg
        simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil]
        obtain ⟨hsrk, hpriv⟩ := hrg (gc0, rc0) (by simp)
        have hc0 := recvChainMaxReq_emptyMks_le_44 (gc := gc0) hsrk hpriv hmks
        omega
  have hkyb : optTailCloneLen G.kyber ≤ 1569 := by
    rcases hb.kyber_eq with h | h | h <;> omega
  have hloc := hb.localIk_le
  have hrem := hb.remoteIk_le
  have hpend := hb.pending_le
  have halice := hb.alice_le
  have hpq := hb.pq_le
  have henc := hb.enc_le
  cases hgs : G.sender <;> cases sess.state.senderChain <;> dsimp only
  · omega
  · omega
  · omega
  · rename_i gs sc
    obtain ⟨hsrk, hpriv⟩ := hb.sender_le gs hgs
    have hsnd := senderChainMaxReq_le_44 sc hsrk hpriv
    omega

def RecordFreshAlice0RecvBounds (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ G sess, g.cur = some G → r.currentSession = some sess → FreshAlice0RecvBounds G sess

theorem recordSerializeTightCum_freshAlice0Recv_le_17132
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hb : RecordFreshAlice0RecvBounds g r) :
    recordSerializeTightCum fineCostModel g r ≤ 17132 := by
  unfold recordSerializeTightCum
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rename_i G sess
    exact serializeSomeTightCum_freshAlice0Recv_le_17132 (hb G sess hg hr)

theorem recordSerializeMaxReq_freshAlice0Recv_le_3820
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hb : RecordFreshAlice0RecvBounds g r) :
    recordSerializeMaxReq g r ≤ 3820 := by
  unfold recordSerializeMaxReq
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rename_i G sess
    exact serializeSomeMaxReq_freshAlice0Recv_le_3820 (hb G sess hg hr)

def RecordAliceInitiatedBounds (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ G sess, g.cur = some G → r.currentSession = some sess → AliceInitiatedBounds G sess

theorem recordSerializeTightCum_aliceInitiated_le_31747
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hb : RecordAliceInitiatedBounds g r) :
    recordSerializeTightCum fineCostModel g r ≤ 31747 := by
  unfold recordSerializeTightCum
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rename_i G sess
    exact serializeSomeTightCum_aliceInitiated_le_31747 (hb G sess hg hr)

theorem recordSerializeMaxReq_aliceInitiated_le_3820
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hb : RecordAliceInitiatedBounds g r) :
    recordSerializeMaxReq g r ≤ 3820 := by
  unfold recordSerializeMaxReq
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rename_i G sess
    exact serializeSomeMaxReq_aliceInitiated_le_3820 (hb G sess hg hr)

/-- Record-level `0`-prev `AliceInitiatedAnyCkBounds` (`≤ 32,485` B, `maxReq ≤ 3,820`). -/
def RecordAliceInitiatedAnyCkBounds (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ G sess, g.cur = some G → r.currentSession = some sess → AliceInitiatedAnyCkBounds G sess

theorem recordSerializeTightCum_aliceInitiatedAnyCk_le_32485
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hb : RecordAliceInitiatedAnyCkBounds g r) :
    recordSerializeTightCum fineCostModel g r ≤ 32485 := by
  unfold recordSerializeTightCum
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rename_i G sess
    exact serializeSomeTightCum_aliceInitiatedAnyCk_le_32485 (hb G sess hg hr)

theorem recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hb : RecordAliceInitiatedAnyCkBounds g r) :
    recordSerializeMaxReq g r ≤ 3820 := by
  unfold recordSerializeMaxReq
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · rename_i G sess
    exact serializeSomeMaxReq_aliceInitiatedAnyCk_le_3820 (hb G sess hg hr)

/-! ## 3. Tight CLI Boxed-Future Async Store-Step Specs -/

theorem w3SmallStoreStep_phaseCredit_tight
    (boxSz : Nat) {rd : ReadRule} {files : FsFiles}
    {dir : DirGhost} {name : List (BitVec 8)}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel (W3SmallStoreStepEnv boxSz rd files dir name)
      (w3BoxedStepCum boxSz (smallStorePollTightDeltaCum (max maxVal fileCap) maxEntries))
      (w3BoxedStepLive boxSz (smallStorePollTightDeltaLive (max maxVal fileCap) maxEntries))
      (w3BoxedStepPeak boxSz (smallStorePollTightDeltaPeak (max maxVal fileCap) maxEntries))
      (w3BoxedStepMaxReq boxSz (smallStorePollTightMaxReq (max maxVal fileCap) maxEntries)) :=
  w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps boxSz
    (smallStorePoll_phaseCredit_tight hdc hdir hname hcap)

theorem w3SessLoadStep_phaseCredit_tight
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf sessDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec fineCostModel (W3SessLoadStepEnv rd DeserEnv files sessDir peer)
      (w3BoxedStepCum 24 (sessLoadPollTightDeltaCum (max maxVal fileCap) deserCum))
      (w3BoxedStepLive 24 (sessLoadPollTightDeltaLive (max maxVal fileCap) deserLive))
      (w3BoxedStepPeak 24 (sessLoadPollTightDeltaPeak (max maxVal fileCap) deserPeak))
      (w3BoxedStepMaxReq 24 (sessLoadPollTightMaxReq (max maxVal fileCap) deserMaxReq)) :=
  w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 24
    (sessLoadPoll_phaseCredit_tight hdc hdir hpeer hcap hdeser)

theorem w3SessStoreStep_phaseCredit_tight
    {sessDir : DirGhost} {peer : AddrGhost}
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W3SessStoreStepEnv sessDir peer g_rec r_rec)
      (w3BoxedStepCum 32
        (sessStorePollTightDeltaCum (recordSerializeTightCum fineCostModel g_rec r_rec) maxEntries))
      (w3BoxedStepLive 32
        (sessStorePollTightDeltaLive (recordSerializeOutLarge fineCostModel g_rec r_rec) maxEntries))
      (w3BoxedStepPeak 32
        (sessStorePollTightDeltaPeak (recordSerializePeak fineCostModel g_rec r_rec) maxEntries))
      (w3BoxedStepMaxReq 32
        (sessStorePollMaxReq (recordSerializeMaxReq g_rec r_rec) maxEntries)) :=
  w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 32
    (sessStorePoll_phaseCredit_tight hdc hpeer)

/-! ## 4. End-to-End Tight `W3InitiateSlotEnv` `PhaseCreditSpec` -/

def w3InitiateSlotTightDeltaCum (fileCap maxEntries deserCum serCum : Nat) : Nat :=
  w3InitiateNativeSmallCum +
  w3BoxedStepCum 32 (smallStorePollTightDeltaCum fileCap maxEntries) +
  w3BoxedStepCum 24 (sessLoadPollTightDeltaCum fileCap deserCum) +
  w3BoxedStepCum 16 (smallStorePollTightDeltaCum fileCap maxEntries) +
  w3SpqrInitCum 32 +
  w3BoxedStepCum 16 (smallStorePollTightDeltaCum fileCap maxEntries) +
  w3BoxedStepCum 32 (smallStorePollTightDeltaCum fileCap maxEntries) +
  w3BoxedStepCum 32 (sessStorePollTightDeltaCum serCum maxEntries)

def w3InitiateSlotTightDeltaLive (fileCap maxEntries deserLive serLive : Nat) : Nat :=
  w3BoxedStepLive 32 (smallStorePollTightDeltaLive fileCap maxEntries) +
  w3BoxedStepLive 24 (sessLoadPollTightDeltaLive fileCap deserLive) +
  w3BoxedStepLive 16 (smallStorePollTightDeltaLive fileCap maxEntries) +
  w3SpqrInitLive 32 +
  w3BoxedStepLive 16 (smallStorePollTightDeltaLive fileCap maxEntries) +
  w3BoxedStepLive 32 (smallStorePollTightDeltaLive fileCap maxEntries) +
  w3BoxedStepLive 32 (sessStorePollTightDeltaLive serLive maxEntries)

def w3InitiateSlotTightDeltaPeak
    (fileCap maxEntries deserLive deserPeak serPeak : Nat) : Nat :=
  let l_t := w3BoxedStepLive 32 (smallStorePollTightDeltaLive fileCap maxEntries)
  let p_t := w3BoxedStepPeak 32 (smallStorePollTightDeltaPeak fileCap maxEntries)
  let l_sl := w3BoxedStepLive 24 (sessLoadPollTightDeltaLive fileCap deserLive)
  let p_sl := w3BoxedStepPeak 24 (sessLoadPollTightDeltaPeak fileCap deserPeak)
  let l_k := w3BoxedStepLive 16 (smallStorePollTightDeltaLive fileCap maxEntries)
  let p_k := w3BoxedStepPeak 16 (smallStorePollTightDeltaPeak fileCap maxEntries)
  let l_q := w3SpqrInitLive 32
  let p_q := w3SpqrInitPeak 32
  let l_r := w3BoxedStepLive 16 (smallStorePollTightDeltaLive fileCap maxEntries)
  let p_r := w3BoxedStepPeak 16 (smallStorePollTightDeltaPeak fileCap maxEntries)
  let l_i := w3BoxedStepLive 32 (smallStorePollTightDeltaLive fileCap maxEntries)
  let p_i := w3BoxedStepPeak 32 (smallStorePollTightDeltaPeak fileCap maxEntries)
  let p_ss := w3BoxedStepPeak 32 (sessStorePollTightDeltaPeak serPeak maxEntries)
  let l12 := l_t + l_sl + l_k
  let l14 := l12 + l_q
  max
    (max
      (max (max p_t (l_t + p_sl)) (l_t + l_sl + max p_k l_k))
      (max l12 (l12 + max p_q l_q)))
    (l14 + max p_r (l_r + max p_i (l_i + p_ss)))

def w3InitiateSlotTightMaxReq (fileCap maxEntries deserMaxReq serMaxReq : Nat) : Nat :=
  let r_sm32 := w3BoxedStepMaxReq 32 (smallStorePollTightMaxReq fileCap maxEntries)
  let r_sm16 := w3BoxedStepMaxReq 16 (smallStorePollTightMaxReq fileCap maxEntries)
  let r_sl := w3BoxedStepMaxReq 24 (sessLoadPollTightMaxReq fileCap deserMaxReq)
  let r_ss := w3BoxedStepMaxReq 32 (sessStorePollMaxReq serMaxReq maxEntries)
  max 1569 (max r_sm32 (max r_sl (max r_sm16 (max 4224 (max r_sm16 (max r_sm32 r_ss))))))

theorem w3InitiateSlotTightDeltaCum_mono {fileCap maxEntries d₁ d₂ s₁ s₂ : Nat}
    (hd : d₁ ≤ d₂) (hs : s₁ ≤ s₂) :
    w3InitiateSlotTightDeltaCum fileCap maxEntries d₁ s₁ ≤
      w3InitiateSlotTightDeltaCum fileCap maxEntries d₂ s₂ := by
  unfold w3InitiateSlotTightDeltaCum w3BoxedStepCum
    sessLoadPollTightDeltaCum sessStorePollTightDeltaCum
  omega

private theorem nat_max_mono {a₁ a₂ b₁ b₂ : Nat} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    max a₁ b₁ ≤ max a₂ b₂ := by
  omega

theorem w3InitiateSlotTightMaxReq_mono {fileCap maxEntries d₁ d₂ s₁ s₂ : Nat}
    (hd : d₁ ≤ d₂) (hs : s₁ ≤ s₂) :
    w3InitiateSlotTightMaxReq fileCap maxEntries d₁ s₁ ≤
      w3InitiateSlotTightMaxReq fileCap maxEntries d₂ s₂ := by
  have hsl :
      w3BoxedStepMaxReq 24 (sessLoadPollTightMaxReq fileCap d₁) ≤
        w3BoxedStepMaxReq 24 (sessLoadPollTightMaxReq fileCap d₂) := by
    unfold w3BoxedStepMaxReq sessLoadPollTightMaxReq
    exact nat_max_mono (Nat.le_refl _) (nat_max_mono (Nat.le_refl _) hd)
  have hss :
      w3BoxedStepMaxReq 32 (sessStorePollMaxReq s₁ maxEntries) ≤
        w3BoxedStepMaxReq 32 (sessStorePollMaxReq s₂ maxEntries) := by
    unfold w3BoxedStepMaxReq sessStorePollMaxReq
    exact nat_max_mono (Nat.le_refl _) (nat_max_mono hs (Nat.le_refl _))
  unfold w3InitiateSlotTightMaxReq
  dsimp only
  exact nat_max_mono (Nat.le_refl _)
    (nat_max_mono (Nat.le_refl _)
      (nat_max_mono hsl
        (nat_max_mono (Nat.le_refl _)
          (nat_max_mono (Nat.le_refl _)
            (nat_max_mono (Nat.le_refl _)
              (nat_max_mono (Nat.le_refl _) hss))))))

theorem w3InitiateSlotTightDeltaCum_add_eq (fileCap maxEntries deserCum serCum : Nat) :
    w3InitiateSlotTightDeltaCum fileCap maxEntries deserCum serCum =
      w3InitiateSlotTightDeltaCum fileCap maxEntries 0 0 + deserCum + serCum := by
  unfold w3InitiateSlotTightDeltaCum w3BoxedStepCum
    sessLoadPollTightDeltaCum sessStorePollTightDeltaCum
  omega

theorem w3InitiateSlot_tight_live_le_peak
    {fileCap maxEntries deserLive deserPeak serLive serPeak : Nat}
    (hser : serLive ≤ serPeak) :
    w3InitiateSlotTightDeltaLive fileCap maxEntries deserLive serLive ≤
      w3InitiateSlotTightDeltaPeak fileCap maxEntries deserLive deserPeak serPeak := by
  unfold w3InitiateSlotTightDeltaLive w3InitiateSlotTightDeltaPeak
  dsimp only
  have hss :
      w3BoxedStepLive 32 (sessStorePollTightDeltaLive serLive maxEntries) ≤
        w3BoxedStepPeak 32 (sessStorePollTightDeltaPeak serPeak maxEntries) :=
    Nat.add_le_add_left (Nat.add_le_add_right hser _) _
  have hi :
      w3BoxedStepLive 32 (smallStorePollTightDeltaLive fileCap maxEntries) +
        w3BoxedStepLive 32 (sessStorePollTightDeltaLive serLive maxEntries) ≤
      max (w3BoxedStepPeak 32 (smallStorePollTightDeltaPeak fileCap maxEntries))
        (w3BoxedStepLive 32 (smallStorePollTightDeltaLive fileCap maxEntries) +
          w3BoxedStepPeak 32 (sessStorePollTightDeltaPeak serPeak maxEntries)) :=
    Nat.le_trans (Nat.add_le_add_left hss _) (Nat.le_max_right _ _)
  have hr :
      w3BoxedStepLive 16 (smallStorePollTightDeltaLive fileCap maxEntries) +
        (w3BoxedStepLive 32 (smallStorePollTightDeltaLive fileCap maxEntries) +
          w3BoxedStepLive 32 (sessStorePollTightDeltaLive serLive maxEntries)) ≤
      max (w3BoxedStepPeak 16 (smallStorePollTightDeltaPeak fileCap maxEntries))
        (w3BoxedStepLive 16 (smallStorePollTightDeltaLive fileCap maxEntries) +
          max (w3BoxedStepPeak 32 (smallStorePollTightDeltaPeak fileCap maxEntries))
            (w3BoxedStepLive 32 (smallStorePollTightDeltaLive fileCap maxEntries) +
              w3BoxedStepPeak 32 (sessStorePollTightDeltaPeak serPeak maxEntries))) :=
    Nat.le_trans (Nat.add_le_add_left hi _) (Nat.le_max_right _ _)
  refine Nat.le_trans ?_ (Nat.le_max_right _ _)
  rw [Nat.add_assoc _ (w3BoxedStepLive 16 _) (w3BoxedStepLive 32 _),
      Nat.add_assoc _ (w3BoxedStepLive 16 _ + _) (w3BoxedStepLive 32 _),
      Nat.add_assoc (w3BoxedStepLive 16 _) (w3BoxedStepLive 32 _) _]
  exact Nat.add_le_add_left hr _

/-- Tight 5-stage W3 `process_prekey_bundle` (`W3InitiateSlotEnv`) `PhaseCreditSpec` on `fineCostModel`.
-/
theorem w3InitiateSlot_tight_phaseCredit
    (P : W3InitiateSlotParams)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let cap := max maxVal fileCap
    PhaseCreditSpec fineCostModel (W3InitiateSlotEnv P)
      (w3InitiateSlotTightDeltaCum cap maxEntries deserCum
        (recordSerializeTightCum fineCostModel P.g_rec P.r_rec))
      (w3InitiateSlotTightDeltaLive cap maxEntries deserLive
        (recordSerializeOutLarge fineCostModel P.g_rec P.r_rec))
      (w3InitiateSlotTightDeltaPeak cap maxEntries deserLive deserPeak
        (recordSerializePeak fineCostModel P.g_rec P.r_rec))
      (w3InitiateSlotTightMaxReq cap maxEntries deserMaxReq
        (recordSerializeMaxReq P.g_rec P.r_rec)) := by
  intro cap
  have hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have haddrLen : (addressText P.peer.val).length ≤ 64 := by
    have h51 := addressText_length_le P.peer.val
    rw [show P.peer.val.name = P.peer.name.bytes from rfl] at h51
    omega
  have htrust := w3SmallStoreStep_phaseCredit_tight 32 hdcPeers hdir haddrLen
    (fun bs hr => hfileCap _ bs hr)
  have hload := w3SessLoadStep_phaseCredit_tight hdcSess hdir hpeer
    (fun bs hr => hfileCap _ bs hr) hdeser
  have hkp := w3SmallStoreStep_phaseCredit_tight 16 hdcOwn hdir hkeyName
    (fun bs hr => hfileCap _ bs hr)
  have hspqr := w3SpqrInit32_phaseCredit fineCostModel_modelHyps P.F P.x_spqr hspqrKey
  have hreg := w3SmallStoreStep_phaseCredit_tight 16 hdcOwn hdir hregName
    (fun bs hr => hfileCap _ bs hr)
  have hsave := w3SmallStoreStep_phaseCredit_tight 32 hdcPeers hdir haddrLen
    (fun bs hr => hfileCap _ bs hr)
  have hstore := w3SessStoreStep_phaseCredit_tight P.g_rec P.r_rec hdcSess hpeer
  exact phaseCreditSpec_w3InitiateFull_small fineCostModel_modelHyps hpeer hsmall
    htrust hload hkp hspqr hreg hsave hstore

/-- Specialization of `w3InitiateSlot_tight_phaseCredit` under explicit `serCumCap` and `serMaxReqCap ≤ 135,167` caps.
-/
theorem w3InitiateSlot_tight_phaseCredit_of_serCaps
    (P : W3InitiateSlotParams)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq
     serCumCap serMaxReqCap : Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hserCum : recordSerializeTightCum fineCostModel P.g_rec P.r_rec ≤ serCumCap)
    (hserReq : recordSerializeMaxReq P.g_rec P.r_rec ≤ serMaxReqCap)
    (hserSmall : serMaxReqCap ≤ 135167) :
    let cap := max maxVal fileCap
    PhaseCreditSpec fineCostModel (W3InitiateSlotEnv P)
      (w3InitiateSlotTightDeltaCum cap maxEntries deserCum serCumCap)
      (w3InitiateSlotTightDeltaLive cap maxEntries deserLive 0)
      (w3InitiateSlotTightDeltaPeak cap maxEntries deserLive deserPeak 0)
      (w3InitiateSlotTightMaxReq cap maxEntries deserMaxReq serMaxReqCap) := by
  intro cap
  have hbase := w3InitiateSlot_tight_phaseCredit P hdcOwn hdcPeers hdcSess hdir
    hpeer hkeyName hregName hspqrKey hfileCap hdeser
  have hsm : recordSerializeMaxReq P.g_rec P.r_rec ≤
      HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact Nat.le_trans hserReq hserSmall
  obtain ⟨hpeak0, hout0⟩ := recordSerializePeak_eq_zero_of_maxReq_le fineCostModel hsm
  rw [hout0, hpeak0] at hbase
  exact hbase.mono
    (w3InitiateSlotTightDeltaCum_mono (Nat.le_refl _) hserCum)
    (Nat.le_refl _)
    (Nat.le_refl _)
    (w3InitiateSlotTightMaxReq_mono (Nat.le_refl _) hserReq)

/-- Parametric-`DeserEnv` constructor for `W3InitiateSlotParams` at `StoresGhost.opened`. -/
def mkW3InitiateSlotParamsDeser
    (rd : ReadRule)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (x : InitGhost)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_spqr : InitialStateGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8))) :
    W3InitiateSlotParams where
  rd := rd
  DeserEnv := DeserEnv
  files := x.F
  ownDir := StoresGhost.opened.identity.own
  peersDir := StoresGhost.opened.identity.peers
  sessDir := StoresGhost.opened.sessions
  peer := x.peer
  ownKeyName := ownKeyName
  ownRegName := ownRegName
  F := F
  x_spqr := x_spqr
  g_rec := g_rec
  r_rec := r_rec

theorem mkW3InitiateSlotParamsDeser_nil_eq
    (rd : ReadRule) (x : InitGhost) (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_spqr : InitialStateGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8))) :
    mkW3InitiateSlotParamsDeser rd (fun _ => (· = [])) x ownKeyName ownRegName F x_spqr g_rec r_rec =
      mkW3InitiateSlotParams rd x ownKeyName ownRegName F x_spqr g_rec r_rec :=
  rfl

theorem w3InitiateSlot_opened_tight_phaseCredit
    (P : W3InitiateSlotParams)
    {fileCap deserCum deserLive deserPeak deserMaxReq serCumCap serMaxReqCap : Nat}
    (hOwn : P.ownDir = StoresGhost.opened.identity.own)
    (hPeers : P.peersDir = StoresGhost.opened.identity.peers)
    (hSess : P.sessDir = StoresGhost.opened.sessions)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hserCum : recordSerializeTightCum fineCostModel P.g_rec P.r_rec ≤ serCumCap)
    (hserReq : recordSerializeMaxReq P.g_rec P.r_rec ≤ serMaxReqCap)
    (hserSmall : serMaxReqCap ≤ 135167) :
    PhaseCreditSpec fineCostModel (W3InitiateSlotEnv P)
      (w3InitiateSlotTightDeltaCum fileCap 0 deserCum serCumCap)
      (w3InitiateSlotTightDeltaLive fileCap 0 deserLive 0)
      (w3InitiateSlotTightDeltaPeak fileCap 0 deserLive deserPeak 0)
      (w3InitiateSlotTightMaxReq fileCap 0 deserMaxReq serMaxReqCap) := by
  have hdcOwn : DirDomainCaps 26 0 0 P.ownDir := hOwn ▸ dirDomainCaps_opened_own
  have hdcPeers : DirDomainCaps 26 0 0 P.peersDir := hPeers ▸ dirDomainCaps_opened_peers
  have hdcSess : DirDomainCaps 26 0 0 P.sessDir := hSess ▸ dirDomainCaps_opened_sess
  have h := w3InitiateSlot_tight_phaseCredit_of_serCaps P hdcOwn hdcPeers hdcSess (by decide)
    hpeer hkeyName hregName hspqrKey hfileCap hdeser hserCum hserReq hserSmall
  simpa only [Nat.zero_max] using h

/-- `InitCallSite` specialization of `w3InitiateSlot_opened_tight_phaseCredit` for an arbitrary `DeserEnv`.
-/
theorem w3InitiateSlot_at_initCallSite_deser_tight_phaseCredit
    {img : Obj.Image} {S : RunSem} {g : RunCall} {x : InitGhost}
    (hsite : InitCallSite img S g x)
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {fileCap deserCum deserLive deserPeak deserMaxReq serCumCap serMaxReqCap : Nat}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hserCum : recordSerializeTightCum fineCostModel g_rec r_rec ≤ serCumCap)
    (hserReq : recordSerializeMaxReq g_rec r_rec ≤ serMaxReqCap)
    (hserSmall : serMaxReqCap ≤ 135167) :
    let P := mkW3InitiateSlotParamsDeser rd DeserEnv x ownKeyName ownRegName F x_spqr g_rec r_rec
    PhaseCreditSpec fineCostModel (W3InitiateSlotEnv P)
      (w3InitiateSlotTightDeltaCum fileCap 0 deserCum serCumCap)
      (w3InitiateSlotTightDeltaLive fileCap 0 deserLive 0)
      (w3InitiateSlotTightDeltaPeak fileCap 0 deserLive deserPeak 0)
      (w3InitiateSlotTightMaxReq fileCap 0 deserMaxReq serMaxReqCap) :=
  w3InitiateSlot_opened_tight_phaseCredit
    (mkW3InitiateSlotParamsDeser rd DeserEnv x ownKeyName ownRegName F x_spqr g_rec r_rec)
    rfl rfl rfl (peer_name_length_le_of_initCallSite hsite)
    hkeyName hregName hspqrKey hfileCap hdeser hserCum hserReq hserSmall

theorem w3InitiateSlot_at_initCallSite_tight_phaseCredit
    {img : Obj.Image} {S : RunSem} {g : RunCall} {x : InitGhost}
    (hsite : InitCallSite img S g x)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {fileCap serCumCap serMaxReqCap : Nat}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ fileCap)
    (hserCum : recordSerializeTightCum fineCostModel g_rec r_rec ≤ serCumCap)
    (hserReq : recordSerializeMaxReq g_rec r_rec ≤ serMaxReqCap)
    (hserSmall : serMaxReqCap ≤ 135167) :
    let P := mkW3InitiateSlotParams rd x ownKeyName ownRegName F x_spqr g_rec r_rec
    PhaseCreditSpec fineCostModel (W3InitiateSlotEnv P)
      (w3InitiateSlotTightDeltaCum fileCap 0 0 serCumCap)
      (w3InitiateSlotTightDeltaLive fileCap 0 0 0)
      (w3InitiateSlotTightDeltaPeak fileCap 0 0 0 0)
      (w3InitiateSlotTightMaxReq fileCap 0 0 serMaxReqCap) :=
  w3InitiateSlot_at_initCallSite_deser_tight_phaseCredit hsite hkeyName hregName hspqrKey hfileCap
    (fun _ _ => PhaseCreditSpec.nil fineCostModel) hserCum hserReq hserSmall

/-- `FitsEnv fineCostModel` discharge for `W3InitiateSlotEnv P` using `w3InitiateSlotTightDelta*`.
-/
theorem w3InitiateSlot_tight_fitsEnv_fineCostModel
    {lim : BudgetLimits} (P : W3InitiateSlotParams)
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcOwn : DirDomainCaps maxDir maxEntries maxVal P.ownDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal P.peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal P.sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : P.peer.name.bytes.length ≤ 40)
    (hkeyName : P.ownKeyName.length ≤ 64)
    (hregName : P.ownRegName.length ≤ 64)
    (hspqrKey : P.x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, P.rd P.files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (P.DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (henf : lim.enforced = true)
    (hram :
      let cap := max maxVal fileCap
      let cumB := w3InitiateSlotTightDeltaCum cap maxEntries deserCum
        (recordSerializeTightCum fineCostModel P.g_rec P.r_rec)
      let peakB := w3InitiateSlotTightDeltaPeak cap maxEntries deserLive deserPeak
        (recordSerializePeak fineCostModel P.g_rec P.r_rec)
      let maxReq := w3InitiateSlotTightMaxReq cap maxEntries deserMaxReq
        (recordSerializeMaxReq P.g_rec P.r_rec)
      lim.staticBytes + (18686152 + cumB + peakB) +
        2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva :
      let cap := max maxVal fileCap
      let cumB := w3InitiateSlotTightDeltaCum cap maxEntries deserCum
        (recordSerializeTightCum fineCostModel P.g_rec P.r_rec)
      let peakB := w3InitiateSlotTightDeltaPeak cap maxEntries deserLive deserPeak
        (recordSerializePeak fineCostModel P.g_rec P.r_rec)
      let maxReq := w3InitiateSlotTightMaxReq cap maxEntries deserMaxReq
        (recordSerializeMaxReq P.g_rec P.r_rec)
      MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
        fineStepReserveOfCum maxReq 16 cumB +
        (lim.staticCount + fineDynIvsOfCum cumB + 16) *
          (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
        fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init (W3InitiateSlotEnv P) := by
  have hSpec := w3InitiateSlot_tight_phaseCredit P hdcOwn hdcPeers hdcSess hdir
    hpeer hkeyName hregName hspqrKey hfileCap hdeser
  have hlp := w3InitiateSlot_tight_live_le_peak
    (fileCap := max maxVal fileCap) (maxEntries := maxEntries)
    (deserLive := deserLive) (deserPeak := deserPeak)
    (recordSerializeOutLarge_le_peak fineCostModel P.g_rec P.r_rec)
  exact fitsEnv_fineCostModel_of_phaseCredit hSpec hlp henf hram hva

/-! ## 5. Closed Numerical Evaluations and Cap Inequalities at `sessionCapBytes` -/

theorem fineReadFileLive_sessionCap :
    fineReadFileLive sessionCapBytes = 2105347 := by
  unfold fineReadFileLive sessionCapBytes
  have hgt : 135167 < 2 ^ 21 := by decide
  have hle : ¬ (2 ^ 21 ≤ 4096) := by decide
  simp only [hle, ↓reduceIte, optLargeCost_fine_of_gt hgt, fineCostModel_largeCost_eq]
  decide

theorem fineReadFilePeak_sessionCap :
    fineReadFilePeak sessionCapBytes = 3162118 := by
  unfold fineReadFilePeak sessionCapBytes
  have hgt : 135167 < 2 ^ 21 := by decide
  have hle : ¬ (2 ^ 21 ≤ 4096) := by decide
  simp only [hle, ↓reduceIte, optLargeCost_fine_of_gt hgt, fineCostModel_largeCost_eq]
  decide

theorem fineDirPutLive_zero :
    fineDirPutLive 0 = 0 := by
  unfold fineDirPutLive
  exact optLargeCost_fine_of_le (by decide)

theorem w3InitiateSlotTightDeltaCum_zero_eq :
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 0 0 = 7841925 := by
  decide

theorem w3InitiateSlotTightDeltaCum_sessionCap_eq (deserCum serCum : Nat) :
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 deserCum serCum =
      7841925 + deserCum + serCum := by
  rw [w3InitiateSlotTightDeltaCum_add_eq, w3InitiateSlotTightDeltaCum_zero_eq]

theorem w3InitiateSlotTight_d0_17132_eq :
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 0 17132 = 7859057 ∧
    w3InitiateSlotTightDeltaLive sessionCapBytes 0 0 0 = 12165689 ∧
    w3InitiateSlotTightDeltaPeak sessionCapBytes 0 0 0 0 = 13214233 ∧
    w3InitiateSlotTightMaxReq sessionCapBytes 0 0 3820 = 2097152 := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · unfold w3InitiateSlotTightDeltaLive smallStorePollTightDeltaLive
      sessLoadPollTightDeltaLive sessStorePollTightDeltaLive
    rw [fineReadFileLive_sessionCap, fineDirPutLive_zero]
    decide
  · unfold w3InitiateSlotTightDeltaPeak smallStorePollTightDeltaLive smallStorePollTightDeltaPeak
      sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak sessStorePollTightDeltaPeak
    dsimp only
    rw [fineReadFileLive_sessionCap, fineReadFilePeak_sessionCap, fineDirPutLive_zero]
    decide

theorem w3InitiateSlotTight_d0_31747_eq :
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 0 31747 = 7873672 ∧
    w3InitiateSlotTightDeltaLive sessionCapBytes 0 0 0 = 12165689 ∧
    w3InitiateSlotTightDeltaPeak sessionCapBytes 0 0 0 0 = 13214233 ∧
    w3InitiateSlotTightMaxReq sessionCapBytes 0 0 3820 = 2097152 :=
  ⟨by decide, w3InitiateSlotTight_d0_17132_eq.2.1,
    w3InitiateSlotTight_d0_17132_eq.2.2.1, w3InitiateSlotTight_d0_17132_eq.2.2.2⟩

theorem w3InitiateSlotTight_real192_eq :
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 20638720 17132 = 28497777 ∧
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 20638720 31747 = 28512392 ∧
    w3InitiateSlotTightDeltaLive sessionCapBytes 0 3211282 0 = 15376971 ∧
    w3InitiateSlotTightDeltaPeak sessionCapBytes 0 3211282 5316629 0 = 16425515 ∧
    w3InitiateSlotTightMaxReq sessionCapBytes 0 2097152 3820 = 2097152 ∧
    w3InitiateSlotTightMaxReq sessionCapBytes 0 4194304 3820 = 4194304 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide⟩
  · unfold w3InitiateSlotTightDeltaLive smallStorePollTightDeltaLive
      sessLoadPollTightDeltaLive sessStorePollTightDeltaLive
    rw [fineReadFileLive_sessionCap, fineDirPutLive_zero]
    decide
  · unfold w3InitiateSlotTightDeltaPeak smallStorePollTightDeltaLive smallStorePollTightDeltaPeak
      sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak sessStorePollTightDeltaPeak
    dsimp only
    rw [fineReadFileLive_sessionCap, fineReadFilePeak_sessionCap, fineDirPutLive_zero]
    decide

theorem w3InitiateSlotTight_real64_eq :
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 19417728 17132 = 27276785 ∧
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 19417728 31747 = 27291400 :=
  ⟨by decide, by decide⟩

/-- Numerical check against `cliInitSlot*Cap` ceilings. -/
theorem w3InitiateSlotTight_le_setA_and_train_caps :
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 20638720 31747 ≤ 29000000 ∧
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 20638720 31747 ≤ 48708660 ∧
    w3InitiateSlotTightDeltaCum sessionCapBytes 0 19417728 31747 ≤ 29000000 ∧
    w3InitiateSlotTightDeltaLive sessionCapBytes 0 3211282 0 ≤ 16000000 ∧
    w3InitiateSlotTightDeltaPeak sessionCapBytes 0 3211282 5316629 0 ≤ 17000000 ∧
    w3InitiateSlotTightMaxReq sessionCapBytes 0 4194304 3820 ≤ 4194304 := by
  obtain ⟨_, hc192, hlive, hpeak, _, hreq⟩ := w3InitiateSlotTight_real192_eq
  obtain ⟨_, hc64⟩ := w3InitiateSlotTight_real64_eq
  rw [hc192, hc64, hlive, hpeak, hreq]
  decide

/-- `InitCallSite` corollary on `RecordAliceInitiatedBounds` (`serCum ≤ 31,747`). -/
theorem w3InitiateSlot_at_initCallSite_aliceInitiated_phaseCredit
    {img : Obj.Image} {S : RunSem} {g : RunCall} {x : InitGhost}
    (hsite : InitCallSite img S g x)
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {deserCum deserLive deserPeak deserMaxReq : Nat}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ sessionCapBytes)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (halice : RecordAliceInitiatedBounds g_rec r_rec) :
    let P := mkW3InitiateSlotParamsDeser rd DeserEnv x ownKeyName ownRegName F x_spqr g_rec r_rec
    PhaseCreditSpec fineCostModel (W3InitiateSlotEnv P)
      (7873672 + deserCum)
      (w3InitiateSlotTightDeltaLive sessionCapBytes 0 deserLive 0)
      (w3InitiateSlotTightDeltaPeak sessionCapBytes 0 deserLive deserPeak 0)
      (w3InitiateSlotTightMaxReq sessionCapBytes 0 deserMaxReq 3820) := by
  intro P
  have h := w3InitiateSlot_at_initCallSite_deser_tight_phaseCredit (F := F) hsite
    hkeyName hregName hspqrKey hfileCap hdeser
    (recordSerializeTightCum_aliceInitiated_le_31747 halice)
    (recordSerializeMaxReq_aliceInitiated_le_3820 halice)
    (by decide)
  refine h.mono ?_ (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  rw [w3InitiateSlotTightDeltaCum_sessionCap_eq]
  omega

/-- `InitCallSite` corollary on `RecordFreshAlice0RecvBounds` (`serCum ≤ 17,132`). -/
theorem w3InitiateSlot_at_initCallSite_freshAlice0Recv_phaseCredit
    {img : Obj.Image} {S : RunSem} {g : RunCall} {x : InitGhost}
    (hsite : InitCallSite img S g x)
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {deserCum deserLive deserPeak deserMaxReq : Nat}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ sessionCapBytes)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hfresh : RecordFreshAlice0RecvBounds g_rec r_rec) :
    let P := mkW3InitiateSlotParamsDeser rd DeserEnv x ownKeyName ownRegName F x_spqr g_rec r_rec
    PhaseCreditSpec fineCostModel (W3InitiateSlotEnv P)
      (7859057 + deserCum)
      (w3InitiateSlotTightDeltaLive sessionCapBytes 0 deserLive 0)
      (w3InitiateSlotTightDeltaPeak sessionCapBytes 0 deserLive deserPeak 0)
      (w3InitiateSlotTightMaxReq sessionCapBytes 0 deserMaxReq 3820) := by
  intro P
  have h := w3InitiateSlot_at_initCallSite_deser_tight_phaseCredit (F := F) hsite
    hkeyName hregName hspqrKey hfileCap hdeser
    (recordSerializeTightCum_freshAlice0Recv_le_17132 hfresh)
    (recordSerializeMaxReq_freshAlice0Recv_le_3820 hfresh)
    (by decide)
  refine h.mono ?_ (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  rw [w3InitiateSlotTightDeltaCum_sessionCap_eq]
  omega

/-- `InitCallSite` corollary on `RecordAliceInitiatedAnyCkBounds` (`serCum ≤ 32,485`). -/
theorem w3InitiateSlot_at_initCallSite_aliceInitiatedAnyCk_phaseCredit
    {img : Obj.Image} {S : RunSem} {g : RunCall} {x : InitGhost}
    (hsite : InitCallSite img S g x)
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {deserCum deserLive deserPeak deserMaxReq : Nat}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ sessionCapBytes)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (halice : RecordAliceInitiatedAnyCkBounds g_rec r_rec) :
    let P := mkW3InitiateSlotParamsDeser rd DeserEnv x ownKeyName ownRegName F x_spqr g_rec r_rec
    PhaseCreditSpec fineCostModel (W3InitiateSlotEnv P)
      (7874410 + deserCum)
      (w3InitiateSlotTightDeltaLive sessionCapBytes 0 deserLive 0)
      (w3InitiateSlotTightDeltaPeak sessionCapBytes 0 deserLive deserPeak 0)
      (w3InitiateSlotTightMaxReq sessionCapBytes 0 deserMaxReq 3820) := by
  intro P
  have h := w3InitiateSlot_at_initCallSite_deser_tight_phaseCredit (F := F) hsite
    hkeyName hregName hspqrKey hfileCap hdeser
    (recordSerializeTightCum_aliceInitiatedAnyCk_le_32485 halice)
    (recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820 halice)
    (by decide)
  refine h.mono ?_ (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  rw [w3InitiateSlotTightDeltaCum_sessionCap_eq]
  omega

end LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
