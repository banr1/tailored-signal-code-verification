/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefs
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Record
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Tie
public import LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget

/-!
# Post-Decrypt Arm-4 `prev1` Domain & Canonical Slot Envelopes

Post-`try_decrypt` Path-C Arm-4 `prev1` output domain (`PostBobPrev1Dom`) and canonical `decrypt_prekey`
slot envelopes:
- `postBobTotalPrev1Cap286K = 2,469,364` B (`= postBobRecordCapOf 286196 [= 372,207] + (1 + 4 + 2,097,152)`)
  bounds `(encodeRecordPrev1Mem G ses enc).length` for a post-`try_decrypt` Bob session with
  `ses.state.receiverChains.length ≤ 1`, `≤ 2,000` skipped message keys (`SessionGhostValid`),
  `pqRatchetState.length ≤ 286,196` (`SessionCloneDom 286196`), and `enc.length ≤ 2,097,152`.
- `w4PostBobCloneTightCum = 2,373,456` B (`= 897,456 + 738 * 2,000`) bounds the separate small-pool
  cumulative clone credit `segCloneTightCum fineCostModel G ses.state`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (Crypto ReceiverChain SenderChain ShaCompress maxMessageKeys)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost SessionGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks Inputs)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost addrValOf runFiles)
open LibsignalBinary.Heap (AllocEvent rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (chainCloneDomFineGrpS chainCloneEnv_dom_fine_groupSpec optTailCloneEvents_groupSpec
   phaseGroupSpec_append_eq senderChainCloneDomFineGrpS senderChainCloneEnv_dom_fine_groupSpec
   vecCloneEvents_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
  (m2rg_StatesRecvEnvFam
   m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
   m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
   m2rg_verNePrev1P3PathCEnvOf')
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (CliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (optLargeCost)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (chainCloneLarge optTailCloneLen segCloneLarge segCloneMaxReq segCloneTightCum vecCloneLarge)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (serializePrev1MaxReq serializePrev1OutLarge serializePrev1Peak serializePrev1TightCum
   serializePrev1TightCum_fine_le_of_clone vecVecClone1Large vecVecClone1MaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (SessionCloneDom ghostCloneValid_of_sessionGhostValid segCloneMaxReq_le_of_dom
   segCloneTightCum_fine_keys_le_of_dom)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (W4DecryptPrekeySlotParams)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (FreshBobPrev1Dom fineOptLarge fineOptLarge_mono fineOptLarge_of_le optLargeCost_fine_eq)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (VerNeTightTopEnv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
  (W4BinaryCallSiteDomCmk0 W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
   realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed
   realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixedOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
  (W4StatesRecvEnv w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4ArchivedTrialCmk W4ArchivedTrialDomCmkOf W4BinaryCallSiteDomCmk W4BinaryRecvPrekeyParamsCmk
   W4FailedTdDomCmkOf W4FailedTryDecryptCallCmk W4LoopAdvEnv W4RecvPrekeyRealParamsCmk
   W4TryDecryptCallCmk W4TryDecryptCallDomCmkOf W4TryDecryptPathACDomCmkOf w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Record (RecordStructure)
open LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec (segCloneFreshBobFineGrpS)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (chainCloneEvents senderChainAsProtoGhost senderChainCloneEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv segCloneEvents)

/-! ## `PostBobPrev1Dom` & Named Per-Field Protobuf Cap Definitions -/

/-- Pure `Nat` protobuf varint byte length for `n < 2 ^ 64` (mirrors `EncodedLen.varintLenBV`). -/
def varintMaxLen (n : Nat) : Nat :=
  if n < 2 ^ 7 then 1
  else if n < 2 ^ 14 then 2
  else if n < 2 ^ 21 then 3
  else if n < 2 ^ 28 then 4
  else if n < 2 ^ 35 then 5
  else if n < 2 ^ 42 then 6
  else if n < 2 ^ 49 then 7
  else if n < 2 ^ 56 then 8
  else if n < 2 ^ 63 then 9
  else 10

/-- Tight length-delimited field cap for tag `1 ≤ tag ≤ 15` (`1`-byte key + `varintMaxLen` + payload). -/
def lenFieldCap1_15 (payloadCap : Nat) : Nat :=
  1 + varintMaxLen payloadCap + payloadCap

/-- Tight reachable SPQR v1 `pqRatchetState` byte cap (`TopStateTight.topStateTight_length_le`). -/
def w4PostBobPqCap : Nat := 286196

/-- Maximum skipped message keys per receiver chain (`CryptoGames.LibsignalSession.maxMessageKeys`). -/
def w4PostBobMaxSkippedKeys : Nat := 2000

/-- Tight `ChainKey` message cap (`uint32Field 1 ≤ 6` + `bytesField 2 (32 B) = 34` = `40` B). -/
def w4PostBobChainKeyBytes : Nat := 6 + lenFieldCap1_15 32

/-- Tight `lenField 4 (encMessageKey mk)` cap for `32`-B seed (`42` B). -/
def w4PostBobMsgKeyFieldBytes : Nat :=
  lenFieldCap1_15 (6 + lenFieldCap1_15 32)

/-- Tight `encReceiverChain c` payload cap for `≤ 2,000` skipped keys (`35 + 42 + 84,000 = 84,077` B). -/
def w4PostBobEncReceiverChainBytes : Nat :=
  lenFieldCap1_15 33 + lenFieldCap1_15 w4PostBobChainKeyBytes +
    w4PostBobMaxSkippedKeys * w4PostBobMsgKeyFieldBytes

/-- Tight `lenField 7 (encReceiverChain c)` cap for `≤ 1` receiver chain (`84,081` B). -/
def w4PostBobOneChainBytes : Nat :=
  lenFieldCap1_15 w4PostBobEncReceiverChainBytes

/-- Tight `msgField 6 (encSenderChain)` cap (`113` B). -/
def w4PostBobSenderChainFieldBytes : Nat :=
  lenFieldCap1_15 (lenFieldCap1_15 33 + lenFieldCap1_15 32 + lenFieldCap1_15 w4PostBobChainKeyBytes)

/-- Tight `msgField 9 (pendingPreKey)` cap (`65` B). -/
def w4PostBobPendingPreKeyFieldBytes : Nat :=
  lenFieldCap1_15 (6 + lenFieldCap1_15 33 + 11 + 11)

/-- Tight `msgField 14 (pendingKyberPreKey)` cap under `SessionCloneDom` (`1,581` B). -/
def w4PostBobPendingKyberFieldBytes : Nat :=
  lenFieldCap1_15 (6 + lenFieldCap1_15 1569)

/-- Tight cap on fixed-bound fields `1..6, 9..11, 13, 14` of `Record.encSession` (`1,922` B). -/
def w4PostBobFixedNonChainBytes : Nat :=
  6 + lenFieldCap1_15 33 + lenFieldCap1_15 33 + lenFieldCap1_15 32 + 6 +
    w4PostBobSenderChainFieldBytes + w4PostBobPendingPreKeyFieldBytes +
    6 + 6 + lenFieldCap1_15 33 + w4PostBobPendingKyberFieldBytes

/-- Tight cap on `(Record.encSession ses').length` for `receiverChains.length ≤ 1` (`372,203` B at `286,196`). -/
def postBobSessionCapOf (bobPqCap : Nat) : Nat :=
  w4PostBobFixedNonChainBytes + w4PostBobOneChainBytes + lenFieldCap1_15 bobPqCap

/-- Tight cap on `(Record.encodeRecord ⟨some ses'⟩).length` (`372,207` B at `bobPqCap = 286,196`). -/
def postBobRecordCapOf (bobPqCap : Nat) : Nat :=
  lenFieldCap1_15 (postBobSessionCapOf bobPqCap)

/-- Cap on `(encodeRecordPrev1Mem G ses' enc).length`:
`postBobRecordCapOf bobPqCap + lenFieldCap1_15 prevEncCap`. -/
def postBobTotalPrev1CapOf (bobPqCap prevEncCap : Nat) : Nat :=
  postBobRecordCapOf bobPqCap + lenFieldCap1_15 prevEncCap

/-- Overhead `postBobTotalPrev1CapOf 286196 2097152 - 2097152` (`= 372,212` B). -/
def postBobPrev1Overhead286K : Nat :=
  postBobRecordCapOf w4PostBobPqCap + (1 + varintMaxLen 2097152)

/-- Cap `postBobTotalPrev1CapOf` instantiated at `(bobPqCap := 286196, prevEncCap := 2097152)`
(`= 2,469,364` B). -/
def postBobTotalPrev1Cap286K : Nat :=
  postBobTotalPrev1CapOf w4PostBobPqCap 2097152

/-- Separate small-pool cumulative Rust clone credit (`897,456 + 738 * 2,000 = 2,373,456` B) for
`segCloneTightCum fineCostModel G ses.state` at `receiverChains.length ≤ 1` (NOT `total_len`). -/
def w4PostBobCloneTightCum : Nat :=
  897456 + 738 * w4PostBobMaxSkippedKeys

/-- Single receiver-chain large-pool peak/live buffer cost on `fineCostModel` (`216,195` B). -/
def w4PostBobOneChainLarge : Nat := 216195

/-- Tight `serializePrev1TightCum fineCostModel` cap for `≤ 1` receiver chain (`2,660,912` B). -/
def w4PostBobSerializePrev1TightCum : Nat :=
  w4PostBobCloneTightCum + 287456

/-- Scaled group bound for `SegCloneEnv` under `PostBobPrev1Dom` (`≤ 1` receiver chain). -/
def segClonePostBob1FineGrpS : Nat :=
  segCloneFreshBobFineGrpS + (3 * FineScale + chainCloneDomFineGrpS)

theorem w4PostBobMaxSkippedKeys_eq : w4PostBobMaxSkippedKeys = maxMessageKeys := rfl
theorem w4PostBobOneChainBytes_eq : w4PostBobOneChainBytes = 84081 := rfl
theorem w4PostBobFixedNonChainBytes_eq : w4PostBobFixedNonChainBytes = 1922 := rfl
theorem postBobRecordCapOf_286K_eq : postBobRecordCapOf w4PostBobPqCap = 372207 := rfl
theorem postBobPrev1Overhead286K_eq : postBobPrev1Overhead286K = 372212 := rfl
theorem postBobTotalPrev1Cap286K_eq : postBobTotalPrev1Cap286K = 2469364 := rfl
theorem postBobTotalPrev1Cap286K_decomp :
    postBobTotalPrev1Cap286K = 2097152 + postBobPrev1Overhead286K := rfl

/-- Post-`try_decrypt` Path-C Arm-4 `prev1` output domain bundle on `out1`:
- `rc_len1`: `ses.state.receiverChains.length ≤ 1` (`0` on unused default witness, `1` after Arm-4
  `try_decrypt` pushes Bob's initial receiver chain);
- `gv`: `SessionGhostValid G ses` (yielding `rc.messageKeys.length ≤ maxMessageKeys = 2000`);
- `dom`: `SessionCloneDom bobPqCap ses` (`bobPqCap = 286,196`);
- `prev_len`: `enc.length ≤ prevEncCap` (`prevEncCap = 2,097,152`);
- `total_len`: `(encodeRecordPrev1Mem G ses enc).length ≤ totalPrev1Cap` (`2,469,364` B). -/
structure PostBobPrev1Dom (bobPqCap prevEncCap totalPrev1Cap : Nat)
    (G : SessionGhost) (ses : Session (List (BitVec 8))) (enc : List (BitVec 8)) : Prop where
  rc_len1 : ses.state.receiverChains.length ≤ 1
  gv : SessionGhostValid G ses
  dom : SessionCloneDom bobPqCap ses
  prev_len : enc.length ≤ prevEncCap
  total_len : (encodeRecordPrev1Mem G ses enc).length ≤ totalPrev1Cap

private theorem g1fr_map_sum_le {α : Type} (f : α → Nat) (c : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, f x ≤ c) → (xs.map f).sum ≤ xs.length * c
  | [], _ => by simp
  | x :: xs, h => by
    have hx : f x ≤ c := h x (List.Mem.head xs)
    have hxs : (xs.map f).sum ≤ xs.length * c :=
      g1fr_map_sum_le f c xs (fun y hy => h y (List.Mem.tail x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

private theorem g1fr_zip_length_le_right {α β : Type} :
    ∀ (xs : List α) (ys : List β), (xs.zip ys).length ≤ ys.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | _ :: xs, _ :: ys => by
    simp only [List.zip_cons_cons, List.length_cons]
    exact Nat.succ_le_succ (g1fr_zip_length_le_right xs ys)

private theorem g1fr_snd_mem_of_mem_zip {α β : Type} {a : α} {b : β} :
    ∀ {xs : List α} {ys : List β}, (a, b) ∈ xs.zip ys → b ∈ ys
  | [], _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: xs, _ :: ys, h => by
    simp only [List.zip_cons_cons, List.mem_cons] at h ⊢
    rcases h with ⟨_, rfl⟩ | htl
    · exact Or.inl rfl
    · exact Or.inr (g1fr_snd_mem_of_mem_zip htl)

private theorem g1fr_vecCloneLarge_fine_of_le {n : Nat} (h : n ≤ 135167) :
    vecCloneLarge fineCostModel n = 0 := by
  unfold vecCloneLarge
  split
  · rfl
  · rw [optLargeCost_fine_eq]
    exact fineOptLarge_of_le h

private theorem g1fr_senderChainLarge_fine_eq_zero {gs : SenderChainGhost} {sc : SenderChain}
    (hsrk : gs.srk.bytes.length = 33) (hpriv : gs.priv.bytes.length = 32) :
    chainCloneLarge fineCostModel (senderChainAsProtoGhost gs sc) = 0 := by
  unfold chainCloneLarge senderChainAsProtoGhost
  dsimp only
  rw [g1fr_vecCloneLarge_fine_of_le (by omega),
      g1fr_vecCloneLarge_fine_of_le (by omega),
      optLargeCost_fine_eq 32, fineOptLarge_of_le (by decide)]
  rfl

private theorem g1fr_chainCloneLarge_fine_recv_le {gc : ChainGhost × ReceiverChain}
    (hsrk : gc.1.srk.bytes.length = 33) (hpriv : gc.1.priv.bytes.length = 0)
    (hmk : gc.2.messageKeys.length ≤ 2000)
    (hseeds : ∀ k ∈ gc.2.messageKeys, k.seed.length = 32) :
    chainCloneLarge fineCostModel gc ≤ w4PostBobOneChainLarge := by
  unfold chainCloneLarge w4PostBobOneChainLarge
  have h1 : vecCloneLarge fineCostModel gc.1.srk.bytes.length = 0 :=
    g1fr_vecCloneLarge_fine_of_le (by omega)
  have h2 : vecCloneLarge fineCostModel gc.1.priv.bytes.length = 0 :=
    g1fr_vecCloneLarge_fine_of_le (by omega)
  have h4 : (if gc.2.messageKeys = [] then 0
      else optLargeCost fineCostModel (104 * gc.2.messageKeys.length) +
        (gc.2.messageKeys.map fun mkg => optLargeCost fineCostModel mkg.seed.length).sum) ≤
      216195 := by
    split
    · exact Nat.zero_le 216195
    · have hbuf : optLargeCost fineCostModel (104 * gc.2.messageKeys.length) ≤ 216195 := by
        rw [optLargeCost_fine_eq]
        exact Nat.le_trans (fineOptLarge_mono (by omega : 104 * gc.2.messageKeys.length ≤ 208000))
          (by decide)
      have hseeds0 :
          (gc.2.messageKeys.map fun mkg => optLargeCost fineCostModel mkg.seed.length).sum ≤ 0 := by
        have hle := g1fr_map_sum_le
          (fun mkg => optLargeCost fineCostModel mkg.seed.length) 0 gc.2.messageKeys
          (fun mkg hm => by
            rw [hseeds mkg hm, optLargeCost_fine_eq 32, fineOptLarge_of_le (by decide)])
        omega
      omega
  rw [h1, h2]
  cases gc.2.chainKey
  · dsimp only; omega
  · dsimp only
    rw [optLargeCost_fine_eq 32, fineOptLarge_of_le (by decide)]
    omega

private theorem g1fr_flatMap_eq_groupSpec {α : Type} (f : α → List AllocEvent) (g : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, PhaseGroupSpec fineCostModel (· = f x) g) →
      PhaseGroupSpec fineCostModel (· = xs.flatMap f) (xs.length * g)
  | [], _ => by
    simpa only [List.flatMap_nil, List.length_nil, Nat.zero_mul] using
      PhaseGroupSpec.nil fineCostModel
  | x :: xs, h => by
    have hx := h x (List.Mem.head xs)
    have hxs := g1fr_flatMap_eq_groupSpec f g xs (fun y hy => h y (List.Mem.tail x hy))
    have happ := phaseGroupSpec_append_eq fineCostModel hx hxs
    simp only [List.flatMap_cons, List.length_cons, Nat.succ_mul]
    exact happ.mono (by omega)

/-- Monotone lift from `FreshBobPrev1Dom` (`rc = []`) to `PostBobPrev1Dom` (`rc.length ≤ 1`). -/
theorem FreshBobPrev1Dom.toPostBobPrev1Dom
    {bobPqCap bobPqCap' prevEncCap prevEncCap' totalPrev1Cap totalPrev1Cap' : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hpq : bobPqCap ≤ bobPqCap')
    (hprev : prevEncCap ≤ prevEncCap')
    (htot : totalPrev1Cap ≤ totalPrev1Cap')
    (h : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    PostBobPrev1Dom bobPqCap' prevEncCap' totalPrev1Cap' G ses enc := by
  refine
    { rc_len1 := by rw [h.rc_nil]; decide
      gv := h.gv
      dom := { h.dom with pq_len := Nat.le_trans h.dom.pq_len hpq }
      prev_len := Nat.le_trans h.prev_len hprev
      total_len := Nat.le_trans h.total_len htot }

/-- 1-chain `segCloneTightCum` bound (`≤ 2,373,456` B) under `PostBobPrev1Dom`. -/
theorem segCloneTightCum_fine_postBob_le {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : PostBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    segCloneTightCum fineCostModel G ses.state ≤ w4PostBobCloneTightCum := by
  have hgv := ghostCloneValid_of_sessionGhostValid h.gv
  have hzlen : (G.chains.zip ses.state.receiverChains).length ≤ 1 :=
    Nat.le_trans (g1fr_zip_length_le_right _ _) h.rc_len1
  have hsum := g1fr_map_sum_le
    (fun gc : ChainGhost × ReceiverChain => gc.2.messageKeys.length) 2000
    (G.chains.zip ses.state.receiverChains)
    (fun gc hmem => (hgv.chains_ok gc hmem).2.2)
  have hkeys : ((G.chains.zip ses.state.receiverChains).map
      (fun gc => gc.2.messageKeys.length)).sum ≤ 2000 := by
    omega
  simpa only [w4PostBobCloneTightCum, w4PostBobMaxSkippedKeys] using
    segCloneTightCum_fine_keys_le_of_dom h.gv h.dom hkeys

/-- 1-chain `segCloneLarge` bound (`≤ 216,195 + fineOptLarge bobPqCap` B) under `PostBobPrev1Dom`. -/
theorem segCloneLarge_fine_postBob_le {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : PostBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    segCloneLarge fineCostModel G ses.state ≤ w4PostBobOneChainLarge + fineOptLarge bobPqCap := by
  obtain ⟨hloc_len, hrem_len, _, hch_ok, hsend_ok, hpend_len, hkyb_len, halice_eq, _⟩ :=
    ghostCloneValid_of_sessionGhostValid h.gv
  have hdom := h.dom
  have hrc_len1 := h.rc_len1
  unfold segCloneLarge
  have hloc : vecCloneLarge fineCostModel G.localIk.bytes.length = 0 :=
    g1fr_vecCloneLarge_fine_of_le (by omega)
  have hrem : vecCloneLarge fineCostModel G.remoteIk.bytes.length = 0 :=
    g1fr_vecCloneLarge_fine_of_le (by omega)
  have hroot : optLargeCost fineCostModel 32 = 0 := by
    rw [optLargeCost_fine_eq]; exact fineOptLarge_of_le (by decide)
  have hrc : (if ses.state.receiverChains = [] then 0
      else optLargeCost fineCostModel (104 * ses.state.receiverChains.length) +
        ((G.chains.zip ses.state.receiverChains).map (chainCloneLarge fineCostModel)).sum) ≤
      w4PostBobOneChainLarge := by
    split
    · exact Nat.zero_le _
    · have hout : optLargeCost fineCostModel (104 * ses.state.receiverChains.length) = 0 := by
        rw [optLargeCost_fine_eq]
        exact fineOptLarge_of_le (by omega)
      have hzlen : (G.chains.zip ses.state.receiverChains).length ≤ 1 :=
        Nat.le_trans (g1fr_zip_length_le_right _ _) hrc_len1
      have hsum := g1fr_map_sum_le (chainCloneLarge fineCostModel) w4PostBobOneChainLarge
        (G.chains.zip ses.state.receiverChains)
        (fun gc hmem => by
          obtain ⟨hsrk, hpriv, hmk⟩ := hch_ok gc hmem
          exact g1fr_chainCloneLarge_fine_recv_le hsrk hpriv hmk
            (hdom.seeds32 gc.2 (g1fr_snd_mem_of_mem_zip hmem)))
      have hle1 : (G.chains.zip ses.state.receiverChains).length * w4PostBobOneChainLarge ≤
          1 * w4PostBobOneChainLarge :=
        Nat.mul_le_mul_right w4PostBobOneChainLarge hzlen
      omega
  have hpend : vecCloneLarge fineCostModel (optTailCloneLen G.pending) = 0 :=
    g1fr_vecCloneLarge_fine_of_le (by omega)
  have hkyb_le : optTailCloneLen G.kyber ≤ 1569 := by
    rw [hkyb_len]
    cases hk : ses.pendingKyberPreKey with
    | none => simp
    | some k => exact hdom.kyber_cap k hk
  have hkyb : vecCloneLarge fineCostModel (optTailCloneLen G.kyber) = 0 :=
    g1fr_vecCloneLarge_fine_of_le (Nat.le_trans hkyb_le (by decide))
  have halice : vecCloneLarge fineCostModel G.alice.bytes.length = 0 :=
    g1fr_vecCloneLarge_fine_of_le
      (by rw [halice_eq]; exact Nat.le_trans hdom.alice_len (by decide))
  have hpq : vecCloneLarge fineCostModel ses.state.pqRatchetState.length ≤
      fineOptLarge bobPqCap := by
    unfold vecCloneLarge
    split
    · exact Nat.zero_le _
    · rw [optLargeCost_fine_eq]
      exact fineOptLarge_mono hdom.pq_len
  rw [hloc, hrem, hroot, hpend, hkyb, halice]
  rcases hsend_ok with ⟨h1, h2⟩ | ⟨gs, sc, h1, h2, hsrk, hpriv⟩
  · rw [h1, h2]; dsimp only; omega
  · rw [h1, h2]; dsimp only
    rw [g1fr_senderChainLarge_fine_eq_zero hsrk hpriv]
    omega

/-- 1-chain `serializePrev1TightCum` bound (`≤ 2,660,912` B) under `PostBobPrev1Dom`. -/
theorem serializePrev1TightCum_fine_postBob_le {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : PostBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    serializePrev1TightCum fineCostModel G ses enc ≤ w4PostBobSerializePrev1TightCum := by
  exact serializePrev1TightCum_fine_le_of_clone (segCloneTightCum_fine_postBob_le h)

/-- `serializePrev1OutLarge` bound (`≤ fineOptLarge totalPrev1Cap`) under `PostBobPrev1Dom`. -/
theorem serializePrev1OutLarge_fine_postBob_le {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : PostBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    serializePrev1OutLarge fineCostModel G ses enc ≤ fineOptLarge totalPrev1Cap := by
  unfold serializePrev1OutLarge
  rw [optLargeCost_fine_eq]
  exact fineOptLarge_mono h.total_len

/-- `serializePrev1Peak` bound under `PostBobPrev1Dom` (sum form mirroring
`W4OuterTightSpecAux.serializePrev1Peak_fine_freshBob_le`, since `serializePrev1Peak` is
`segCloneLarge + vecVecClone1Large enc + optLargeCost (encodeRecordPrev1Mem ...).length`). -/
theorem serializePrev1Peak_fine_postBob_le {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : PostBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    serializePrev1Peak fineCostModel G ses enc ≤
      (w4PostBobOneChainLarge + fineOptLarge bobPqCap) +
        fineOptLarge prevEncCap + fineOptLarge totalPrev1Cap := by
  unfold serializePrev1Peak
  have hcl := segCloneLarge_fine_postBob_le h
  have hvv : vecVecClone1Large fineCostModel enc ≤ fineOptLarge prevEncCap := by
    unfold vecVecClone1Large
    rw [optLargeCost_fine_eq 24, fineOptLarge_of_le (by decide), Nat.zero_add]
    unfold vecCloneLarge
    split
    · exact Nat.zero_le _
    · rw [optLargeCost_fine_eq]
      exact fineOptLarge_mono h.prev_len
  have hout : optLargeCost fineCostModel (encodeRecordPrev1Mem G ses enc).length ≤
      fineOptLarge totalPrev1Cap := by
    rw [optLargeCost_fine_eq]
    exact fineOptLarge_mono h.total_len
  exact Nat.add_le_add (Nat.add_le_add hcl hvv) hout

/-- `serializePrev1MaxReq` bound under `PostBobPrev1Dom`. -/
theorem serializePrev1MaxReq_postBob_le {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : PostBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc)
    (hpq : bobPqCap ≤ totalPrev1Cap) (hprev : prevEncCap ≤ totalPrev1Cap)
    (h104 : 208000 ≤ totalPrev1Cap) :
    serializePrev1MaxReq G ses enc ≤ totalPrev1Cap := by
  unfold serializePrev1MaxReq vecVecClone1MaxReq
  have hcl : segCloneMaxReq G ses.state ≤ totalPrev1Cap :=
    Nat.le_trans (segCloneMaxReq_le_of_dom h.gv h.dom) (Nat.max_le.mpr ⟨h104, hpq⟩)
  have h24 : 24 ≤ totalPrev1Cap := Nat.le_trans (by decide : 24 ≤ 208000) h104
  have hvv : max 24 enc.length ≤ totalPrev1Cap :=
    Nat.max_le.mpr ⟨h24, Nat.le_trans h.prev_len hprev⟩
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hcl, hvv⟩, h.total_len⟩

/-- `PhaseGroupSpec` for `SegCloneEnv` under `PostBobPrev1Dom` (`segClonePostBob1FineGrpS`). -/
theorem segCloneEnv_postBobPrev1Dom_fine_groupSpec {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (h : PostBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G ses.state) segClonePostBob1FineGrpS := by
  have hgv := ghostCloneValid_of_sessionGhostValid h.gv
  have hdom := h.dom
  have hloc := vecCloneEvents_groupSpec fineCostModel G.localIk
  have hrem := vecCloneEvents_groupSpec fineCostModel G.remoteIk
  have hroot := PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
  have hsnd : PhaseGroupSpec fineCostModel
      (· = match G.sender, ses.state.senderChain with
           | some gs, some sc => senderChainCloneEvents gs sc
           | _, _ => [])
      senderChainCloneDomFineGrpS := by
    rcases hgv.sender_ok with ⟨hn1, hn2⟩ | ⟨gs, sc, hgs, hsc, hsrk, hpriv⟩
    · rw [hn1, hn2]
      exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rw [hgs, hsc]
      exact senderChainCloneEnv_dom_fine_groupSpec sc (by omega) (by omega)
  have hrc : PhaseGroupSpec fineCostModel
      (· = if ses.state.receiverChains = [] then []
           else rustAllocEvents (104 * ses.state.receiverChains.length) 8 ++
             (G.chains.zip ses.state.receiverChains).flatMap chainCloneEvents)
      (3 * FineScale + chainCloneDomFineGrpS) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · have hbuf := PhaseGroupSpec.rustAlloc_any fineCostModel
        (104 * ses.state.receiverChains.length) 8
      have hch := g1fr_flatMap_eq_groupSpec chainCloneEvents chainCloneDomFineGrpS
        (G.chains.zip ses.state.receiverChains)
        (fun gc hmem => by
          obtain ⟨hsrk, hpriv, hmk⟩ := hgv.chains_ok gc hmem
          have hs32 := hdom.seeds32 gc.2 (g1fr_snd_mem_of_mem_zip hmem)
          exact chainCloneEnv_dom_fine_groupSpec (by omega) hpriv hmk
            (fun k hk => by rw [hs32 k hk]; omega))
      have hzlen : (G.chains.zip ses.state.receiverChains).length ≤ 1 :=
        Nat.le_trans (g1fr_zip_length_le_right _ _) h.rc_len1
      have hmul : (G.chains.zip ses.state.receiverChains).length * chainCloneDomFineGrpS ≤
          chainCloneDomFineGrpS := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right chainCloneDomFineGrpS hzlen
      exact (phaseGroupSpec_append_eq fineCostModel hbuf hch).mono (Nat.add_le_add_left hmul _)
  have hpend := optTailCloneEvents_groupSpec fineCostModel G.pending
  have hkyb := optTailCloneEvents_groupSpec fineCostModel G.kyber
  have halice := vecCloneEvents_groupSpec fineCostModel G.alice
  have hpq : PhaseGroupSpec fineCostModel
      (· = if ses.state.pqRatchetState.length = 0 then []
           else rustAllocEvents ses.state.pqRatchetState.length 1)
      (3 * FineScale) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel ses.state.pqRatchetState.length 1
  have s1 := phaseGroupSpec_append_eq fineCostModel hloc hrem
  have s2 := phaseGroupSpec_append_eq fineCostModel s1 hroot
  have s3 := phaseGroupSpec_append_eq fineCostModel s2 hsnd
  have s4 := phaseGroupSpec_append_eq fineCostModel s3 hrc
  have s5 := phaseGroupSpec_append_eq fineCostModel s4 hpend
  have s6 := phaseGroupSpec_append_eq fineCostModel s5 hkyb
  have s7 := phaseGroupSpec_append_eq fineCostModel s6 halice
  have s8 := phaseGroupSpec_append_eq fineCostModel s7 hpq
  unfold SegCloneEnv segCloneEvents segClonePostBob1FineGrpS segCloneFreshBobFineGrpS
  exact s8.mono (by decide)

/-! ## Outer, Real, Call-Site, & `Dom0'` Domain Bundles + `FreshBob → PostBob` Lifts -/

/-- Outer `W4DecryptPrekeyTightDom` twin replacing `out1_freshBob` with `out1_postBob`. -/
structure W4DecryptPrekeyTightDom' {α : Type} (P : W4DecryptPrekeySlotParams α)
    (sessFileCap smallFileCap curPqCap archPqCap archEncCap out0PqCap out0EncCap
     bobPqCap prevEncCap totalPrev1Cap ikmCap : Nat) : Prop where
  peer_len : P.peer.name.bytes.length ≤ 40
  ownKey_len : P.ownKeyName.length ≤ 64
  ownReg_len : P.ownRegName.length ≤ 64
  kpkMark_len : P.kpkMarkName.length ≤ 64
  res_old : P.x_res.cap.toNat ≤ ikmCap
  res_new : reserveCap P.x_res.cap.toNat P.x_res.bs.length P.x_res.additional ≤ ikmCap
  ikm_small : max ikmCap 1569 ≤ 135167
  spqr_key : P.x_spqr.p.authKey.length ≤ 32
  sess_cap : ∀ bs, P.rd P.files (pathOf P.sessDir.path (addressText P.peer.val)) = .ok bs →
    bs.length ≤ sessFileCap
  small_cap : ∀ d ∈ [P.ownDir, P.peersDir, P.spkDir, P.kpkDir, P.opkDir],
    ∀ n bs, P.rd P.files (pathOf d.path n) = .ok bs → bs.length ≤ smallFileCap
  cur_dom : (∀ evs, ¬ P.CurTrialFailEnv evs) ∨
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = P.st_cur ∧ SessionGhostValid P.G_cur ses_cur ∧
        SessionCloneDom curPqCap ses_cur
  arch_valid : ∀ G ses, P.g_arch.cur = some G → P.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom archPqCap ses
  arch_enc : (encodeRecord P.r_arch).length ≤ archEncCap
  out0_valid : ∀ G ses, P.g_out0.cur = some G → P.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom out0PqCap ses
  out0_enc : (encodeRecord P.r_out0).length ≤ out0EncCap
  out1_postBob : PostBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap P.G_out1 P.sess_out1 P.enc_prev1
  trials_len4 : P.archivedTrials.length ≤ 4

/-- Post-Bob call-site domain bundle replacing `out1_freshBob` in `W4BinaryCallSiteDomCmk` with
`out1_postBob : PostBobPrev1Dom 286196 2097152 postBobTotalPrev1Cap286K R.G_out1 R.sess_out1 R.enc_prev1`. -/
structure W4BinaryCallSiteDomCmk' (C : Crypto) (K : MlKem) (maxCt : Nat)
    (peerVal : AddrVal) (files : FsFiles) (R : W4RecvPrekeyRealParamsCmk) : Prop where
  eq_C : R.C = C
  eq_K : R.K = K
  eq_rd : R.rd = cliIo.rd
  eq_files : R.files = files
  eq_peerVal : R.peer.val = peerVal
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  ownKey_len : R.ownKeyName.length ≤ 64
  ownReg_len : R.ownRegName.length ≤ 64
  kpkMark_len : R.kpkMarkName.length ≤ 64
  res_old : R.x_res.cap.toNat ≤ 4096
  res_new : reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096
  spqr_key : R.x_spqr.p.authKey.length ≤ 32
  cur_dom : R.hasCurSession = false ∨
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
        SessionCloneDom 286196 ses_cur
  arch_valid : ∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses
  arch_enc : (encodeRecord R.r_arch).length ≤ 2097152
  out0_valid : ∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses
  out0_enc : (encodeRecord R.r_out0).length ≤ 2097152
  out1_postBob : PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K
    R.G_out1 R.sess_out1 R.enc_prev1
  trials_len4 : R.archivedTrials.length ≤ 4
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomCmkOf R.C.F R.K maxCt R.fc_cur
  trials_dom : ∀ y ∈ R.archivedTrials, W4ArchivedTrialDomCmkOf R.C.F R.K maxCt y
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomCmkOf R.C.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomCmkOf R.C.F R.K maxCt R.td_AC

/-- Monotone call-site domain lift `W4BinaryCallSiteDomCmk → W4BinaryCallSiteDomCmk'` from
`FreshBobPrev1Dom` (`receiverChains = []`) to `PostBobPrev1Dom` (`receiverChains.length ≤ 1`). -/
theorem w4BinaryCallSiteDomCmk_toPostBob {C : Crypto} {K : MlKem} {maxCt : Nat}
    {peerVal : AddrVal} {files : FsFiles} {R : W4RecvPrekeyRealParamsCmk}
    (h : W4BinaryCallSiteDomCmk C K maxCt peerVal files R) :
    W4BinaryCallSiteDomCmk' C K maxCt peerVal files R := by
  refine
    { eq_C := h.eq_C
      eq_K := h.eq_K
      eq_rd := h.eq_rd
      eq_files := h.eq_files
      eq_peerVal := h.eq_peerVal
      kpk_dir := h.kpk_dir
      ownKey_len := h.ownKey_len
      ownReg_len := h.ownReg_len
      kpkMark_len := h.kpkMark_len
      res_old := h.res_old
      res_new := h.res_new
      spqr_key := h.spqr_key
      cur_dom := h.cur_dom
      arch_valid := h.arch_valid
      arch_enc := h.arch_enc
      out0_valid := h.out0_valid
      out0_enc := h.out0_enc
      out1_postBob :=
        FreshBobPrev1Dom.toPostBobPrev1Dom (by decide) (Nat.le_refl 2097152) (by decide)
          h.out1_freshBob
      trials_len4 := h.trials_len4
      cur_fail_dom := h.cur_fail_dom
      trials_dom := h.trials_dom
      tdB_dom := h.tdB_dom
      tdAC_dom := h.tdAC_dom }

/-- `SR`-parametric real domain bundle twin over `W4DecryptPrekeyTightDom'` at
`(w4PostBobPqCap = 286196, 2097152, postBobTotalPrev1Cap286K = 2469364)`. -/
structure W4RecvPrekeyRealDomCmkSrOf' (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps smallFileCap maxCt : Nat)
    (R : W4RecvPrekeyRealParamsCmk) : Prop where
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  outer_dom : W4DecryptPrekeyTightDom'
    (W4RecvPrekeyCmkDom0.mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps R)
    2097152 smallFileCap 286196 286196 2097152 286196 2097152
    w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K 4096
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomCmkOf R.C.F R.K maxCt R.fc_cur
  trials_dom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDomCmkOf R.C.F R.K maxCt x
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomCmkOf R.C.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomCmkOf R.C.F R.K maxCt R.td_AC

/-- `Dom0'` (`archivedTrials = []`) twin of `W4RecvPrekeyCmkDom0Of`. -/
def W4RecvPrekeyCmkDom0Of' (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps smallFileCap maxCt : Nat)
    (R : W4RecvPrekeyRealParamsCmk) : Prop :=
  W4RecvPrekeyRealDomCmkSrOf' SR LoopAdvEnv maxOps smallFileCap maxCt R ∧ R.archivedTrials = []

/-- Default `(CmkLoopAdvanceEvs, maxOps, sessionCapBytes, msgCapBytes)` `Dom0'` predicate. -/
abbrev W4RecvPrekeyCmkDom0' (SR : W4StatesRecvEnv) (maxOps : Nat)
    (R : W4RecvPrekeyRealParamsCmk) : Prop :=
  W4RecvPrekeyCmkDom0Of' SR CmkLoopAdvanceEvs maxOps sessionCapBytes msgCapBytes R

/-- Call-site `Dom0'` guard `W4BinaryCallSiteDomCmk' ∧ R.archivedTrials = []`. -/
def W4BinaryCallSiteDomCmk0' (C : Crypto) (K : MlKem)
    (maxCt : Nat) (peerVal : AddrVal) (files : FsFiles) (R : W4RecvPrekeyRealParamsCmk) : Prop :=
  W4BinaryCallSiteDomCmk' C K maxCt peerVal files R ∧ R.archivedTrials = []

/-- Monotone lift `W4BinaryCallSiteDomCmk0 → W4BinaryCallSiteDomCmk0'`. -/
theorem w4BinaryCallSiteDomCmk0_toPostBob {C : Crypto} {K : MlKem} {maxCt : Nat}
    {peerVal : AddrVal} {files : FsFiles} {R : W4RecvPrekeyRealParamsCmk}
    (h : W4BinaryCallSiteDomCmk0 C K maxCt peerVal files R) :
    W4BinaryCallSiteDomCmk0' C K maxCt peerVal files R :=
  ⟨w4BinaryCallSiteDomCmk_toPostBob h.1, h.2⟩

private theorem g1fr_tryDecryptCallDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4TryDecryptCallCmk}
    (h : W4TryDecryptCallDomCmkOf F K c₁ td) :
    W4TryDecryptCallDomCmkOf F K c₂ td :=
  { h with ct_le := Nat.le_trans h.ct_le hc }

private theorem g1fr_failedTdDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {fc : W4FailedTryDecryptCallCmk}
    (h : W4FailedTdDomCmkOf F K c₁ fc) :
    W4FailedTdDomCmkOf F K c₂ fc :=
  ⟨g1fr_tryDecryptCallDomCmkOf_mono hc h.td_dom, h.align_le, h.cancel_live⟩

private theorem g1fr_archivedTrialDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {tr : W4ArchivedTrialCmk}
    (h : W4ArchivedTrialDomCmkOf F K c₁ tr) :
    W4ArchivedTrialDomCmkOf F K c₂ tr :=
  ⟨h.enc_le, h.live_le_peak, h.live_le_drop, h.drop_caps, h.tr_gv, h.tr_dom,
    g1fr_failedTdDomCmkOf_mono hc h.tr_fail⟩

private theorem g1fr_tryDecryptPathACDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4TryDecryptCallCmk}
    (h : W4TryDecryptPathACDomCmkOf F K c₁ td) :
    W4TryDecryptPathACDomCmkOf F K c₂ td :=
  ⟨g1fr_tryDecryptCallDomCmkOf_mono hc h.base, h.rc_nil⟩

/-- Call-site lift `W4BinaryCallSiteDomCmk' → W4RecvPrekeyRealDomCmkSrOf'`. -/
theorem W4BinaryCallSiteDomCmk'.toRealDomCmkSrOf' (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    {C : Crypto} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peerV : AddrV} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (hcs : W4BinaryCallSiteDomCmk' C K maxCt (addrValOf peerV) files R)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hct : maxCt ≤ msgCapBytes) :
    W4RecvPrekeyRealDomCmkSrOf' SR LoopAdvEnv maxOps sessionCapBytes msgCapBytes R := by
  have hpeer40 : R.peer.name.bytes.length ≤ 40 := by
    have hp40 := parseArgs_peer_name_length_le hparse
    change R.peer.val.name.length ≤ 40
    rw [hcs.eq_peerVal]
    exact hp40
  have hsess2M : sessionCapBytes ≤ 2097152 := by
    unfold sessionCapBytes
    decide
  have hcur :
      (∀ evs, ¬ (W4RecvPrekeyCmkDom0.mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps R).CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
          SessionCloneDom 286196 ses_cur := by
    rcases hcs.cur_dom with hfalse | hses
    · refine Or.inl fun evs hev => ?_
      dsimp only [W4RecvPrekeyCmkDom0.mkW4RecvPrekeyWideCmkSrSlotParamsOf] at hev
      rw [hfalse] at hev
      exact nomatch hev
    · exact Or.inr hses
  refine
    { kpk_dir := hcs.kpk_dir
      outer_dom :=
        { peer_len := hpeer40
          ownKey_len := hcs.ownKey_len
          ownReg_len := hcs.ownReg_len
          kpkMark_len := hcs.kpkMark_len
          res_old := hcs.res_old
          res_new := hcs.res_new
          ikm_small := by decide
          spqr_key := hcs.spqr_key
          sess_cap := fun bs hr => by
            dsimp only [W4RecvPrekeyCmkDom0.mkW4RecvPrekeyWideCmkSrSlotParamsOf] at hr
            rw [hcs.eq_rd] at hr
            exact Nat.le_trans (cliIo_rd_ok_length_le_sessionCapBytes R.files _ bs hr) hsess2M
          small_cap := fun d _ n bs hr => by
            dsimp only [W4RecvPrekeyCmkDom0.mkW4RecvPrekeyWideCmkSrSlotParamsOf] at hr
            rw [hcs.eq_rd] at hr
            exact cliIo_rd_ok_length_le_sessionCapBytes R.files (pathOf d.path n) bs hr
          cur_dom := hcur
          arch_valid := hcs.arch_valid
          arch_enc := hcs.arch_enc
          out0_valid := hcs.out0_valid
          out0_enc := hcs.out0_enc
          out1_postBob := hcs.out1_postBob
          trials_len4 := hcs.trials_len4 }
      cur_fail_dom := fun hcur' => g1fr_failedTdDomCmkOf_mono hct (hcs.cur_fail_dom hcur')
      trials_dom := fun y hy => g1fr_archivedTrialDomCmkOf_mono hct (hcs.trials_dom y hy)
      tdB_dom := fun hb => g1fr_tryDecryptCallDomCmkOf_mono hct (hcs.tdB_dom hb)
      tdAC_dom := fun hac => g1fr_tryDecryptPathACDomCmkOf_mono hct (hcs.tdAC_dom hac) }

/-- Direct call-site lift `W4BinaryCallSiteDomCmk0' → W4RecvPrekeyCmkDom0Of'`. -/
theorem W4BinaryCallSiteDomCmk0'.toCmkDom0Of' (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    {C : Crypto} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peerV : AddrV} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (hcs0 : W4BinaryCallSiteDomCmk0' C K maxCt (addrValOf peerV) files R)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hct : maxCt ≤ msgCapBytes) :
    W4RecvPrekeyCmkDom0Of' SR LoopAdvEnv maxOps sessionCapBytes msgCapBytes R :=
  ⟨W4BinaryCallSiteDomCmk'.toRealDomCmkSrOf' SR LoopAdvEnv maxOps hcs0.1 hparse hct, hcs0.2⟩

/-- Binary-kit call-dispatched `Dom0'` guard on `W4BinaryRecvPrekeyParamsCmk`. -/
def W4BinaryRecvPrekeyDomCmk0' (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (c : CallV) (i : Inputs) (w : W4BinaryRecvPrekeyParamsCmk) : Prop :=
  ∀ peerAddr, c = .recv peerAddr →
    w.base.peer.val = addrValOf peerAddr ∧
    w.base.peer.name.bytes.length ≤ 40 ∧
    w.base.files = runFiles i ∧
    w.base.rd = cliIo.rd ∧
    W4RecvPrekeyCmkDom0Of' SR LoopAdvEnv maxOps sessionCapBytes msgCapBytes w.base

/-- Honest `deserializeTie` `Dom0'` lift on `CliPqOrD3RecvDom`. -/
theorem w4RecvPrekeyCmkDom0'Of_of_cliPqOrD3RecvDom_deserializeTie {W : PEParams}
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps smallFileCap maxCt : Nat}
    {i : Inputs} {peer : AddrV} {R : W4RecvPrekeyRealParamsCmk}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hfiles : R.files = runFiles i) (hpeer : R.peer.val = addrValOf peer)
    (hDom : W4RecvPrekeyRealDomCmkSrOf' SR LoopAdvEnv maxOps smallFileCap maxCt R)
    (hTie : ∀ bs orec,
      StoresGhost.opened.sessions.get cliIo.rd R.files (addressText R.peer.val) = .ok bs →
      RecordStructure.deserialize bs = .ok orec →
      R.archivedTrials.length ≤ (orec.map (·.previousSessions.length)).getD 0) :
    W4RecvPrekeyCmkDom0Of' SR LoopAdvEnv maxOps smallFileCap maxCt R := by
  exact ⟨hDom, W4RecvPrekeyDom0Tie.list_eq_nil_of_cliPqOrD3RecvDom_deserializeTie hi hparse
    (fun bs orec hget hdes => hTie bs orec (hfiles.symm ▸ hpeer.symm ▸ hget) hdes)⟩

/-- Honest `deserializeTie` `W4BinaryCallSiteDomCmk0'` lift on `CliPqOrD3RecvDom`. -/
theorem w4BinaryCallSiteDomCmk0'_of_cliPqOrD3RecvDom_deserializeTie {W : PEParams}
    {C : Crypto} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peer : AddrV} {R : W4RecvPrekeyRealParamsCmk}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hcs : W4BinaryCallSiteDomCmk' C K maxCt (addrValOf peer) (runFiles i) R)
    (hTie : ∀ bs orec,
      StoresGhost.opened.sessions.get cliIo.rd R.files (addressText R.peer.val) = .ok bs →
      RecordStructure.deserialize bs = .ok orec →
      R.archivedTrials.length ≤ (orec.map (·.previousSessions.length)).getD 0) :
    W4BinaryCallSiteDomCmk0' C K maxCt (addrValOf peer) (runFiles i) R := by
  exact ⟨hcs, W4RecvPrekeyDom0Tie.list_eq_nil_of_cliPqOrD3RecvDom_deserializeTie hi hparse
    (fun bs orec hget hdes => hTie bs orec (hcs.eq_files.symm ▸ hcs.eq_peerVal.symm ▸ hget) hdes)⟩

/-! ## Slot Envelopes, `cliDecPkCanonSlotEnvExact'`, & Inclusions -/

/-- Binary-kit slot envelope reusing `m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'`
with call-site domain witness `W4BinaryCallSiteDomCmk'`. -/
def m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf'' [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    W4BinaryCallSiteDomCmk' W.C W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
        LoopAdvEnv maxOps StatesRecvFK P3PathCEnv w4 evs

/-- Un-narrowed `VerNe`-instantiated binary-kit slot envelope over `W4BinaryCallSiteDomCmk'`. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf'' [LibsignalPlacement]
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf''
    LoopAdvEnv maxOps StatesRecvFK
    (m2rg_verNePrev1P3PathCEnvOf' verNeEnv LoopAdvEnv maxOps StatesRecvFK)
    X W x evs

/-- Default `(VerNeTightTopEnv, CmkLoopAdvanceEvs, 109)` un-narrowed slot envelope. -/
abbrev m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'' [LibsignalPlacement]
    (StatesRecvFK : m2rg_StatesRecvEnvFam)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixedOf''
    VerNeTightTopEnv CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps StatesRecvFK X W x evs

/-- Unguarded `Dom0'` (`archivedTrials = []`) binary-kit W4 slot envelope reusing
`W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf` unchanged. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    W4BinaryCallSiteDomCmk0' W.C W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w4 evs

/-- Default `(CmkLoopAdvanceEvs, 109)` unguarded `Dom0'` binary-kit W4 slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf
    SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x evs

/-- Session-store reachability guard: raw `sessions.get` succeeds and prost
`RecordStructure.deserialize` yields `0` previous sessions. Discharged at `main` level from
`CliPqOrD3RecvDom` by `W4RecvPrekeyDom0Tie.sessions_get_deserialize_prev0_of_cliPqOrD3RecvDom`. -/
def SessionGetPrev0Guard (files : FsFiles) (peerVal : AddrVal) : Prop :=
  ∃ bs orec,
    StoresGhost.opened.sessions.get cliIo.rd files (addressText peerVal) = .ok bs ∧
    RecordStructure.deserialize bs = .ok orec ∧
    (orec.map (·.previousSessions.length)).getD 0 = 0

/-- Discharger for `SessionGetPrev0Guard` on `CliPqOrD3RecvDom` via
`W4RecvPrekeyDom0Tie.sessions_get_deserialize_prev0_of_cliPqOrD3RecvDom`. -/
theorem sessionGetPrev0Guard_of_cliPqOrD3RecvDom {W : PEParams}
    {i : Inputs} {peer : AddrV}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    SessionGetPrev0Guard (runFiles i) (addrValOf peer) :=
  W4RecvPrekeyDom0Tie.sessions_get_deserialize_prev0_of_cliPqOrD3RecvDom hi hparse

/-- `PeerSpqrStateTight640`-guarded `Dom0'` binary-kit W4 slot envelope (single-guard companion). -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0'GuardedFixedOf [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf SR LoopAdvEnv maxOps X W x evs

/-- Default `(CmkLoopAdvanceEvs, 109)` `PeerSpqrStateTight640`-guarded `Dom0'` slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0'GuardedFixed [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkDom0'GuardedFixedOf
    SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x evs

/-- `(SR, LoopAdvEnv, maxOps)`-parametric `Dom0'` slot envelope guarded by
`PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val` and `SessionGetPrev0Guard x.F x.peer.val`.

When either guard is false, the envelope reduces to `fun _ => True` (`⊤`), for which
`FitsEnv M lim st (fun _ => True)` is unsatisfiable at finite `lim` (`IfaceBudgetLemmas.lean:378`);
outer `MainOk` consumers discharge both guards from `CliPqOrD3RecvDom`. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0'Prev0GuardedFixedOf [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    SessionGetPrev0Guard x.F x.peer.val →
      realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf SR LoopAdvEnv maxOps X W x evs

/-- Default `(CmkLoopAdvanceEvs, 109)` double-guarded `Dom0'` slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0'Prev0GuardedFixed [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkDom0'Prev0GuardedFixedOf
    SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x evs

/-- Canonical `decryptPrekey` slot envelope over `PostBobPrev1Dom` (`W4BinaryCallSiteDomCmk0'`) at
`w4c_repairedStatesRecvEnvFam` (`StatesRecvProtoEnv'`), guarded by `PeerSpqrStateTight640` and
`SessionGetPrev0Guard`.

When either guard is false, `cliDecPkCanonSlotEnvExact' X W x` reduces to `fun _ => True` (`⊤`),
whose `FitsEnv M lim st` precondition is unsatisfiable at finite `lim`; both guards are discharged
at `main` level from `CliPqOrD3RecvDom`. -/
noncomputable def cliDecPkCanonSlotEnvExact' [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    SessionGetPrev0Guard x.F x.peer.val →
      realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W x evs

theorem cliDecPkCanonSlotEnvExact'_eq_dom0'Prev0GuardedFixed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    cliDecPkCanonSlotEnvExact' X W =
      realCliDecPkBinaryWideSlotEnvCmkDom0'Prev0GuardedFixed w4c_repairedStatesRecvEnvFam X W :=
  rfl

/-- Un-narrowed companion to `cliDecPkCanonSlotEnvExact'` (`archivedTrials.length ≤ 4`,
without `SessionGetPrev0Guard`). -/
noncomputable def cliDecPkCanonSlotEnvExactF2' [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeFixed'' w4c_repairedStatesRecvEnvFam X W x evs

theorem realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf_ghost_congr [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores) (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (_hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf SR LoopAdvEnv maxOps X W x =
      realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf SR LoopAdvEnv maxOps X W y := by
  funext evs
  simp only [realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf, hp, hf, hmsg]

theorem cliDecPkCanonSlotEnvExact'_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    cliDecPkCanonSlotEnvExact' X W x = cliDecPkCanonSlotEnvExact' X W y := by
  funext evs
  unfold cliDecPkCanonSlotEnvExact' SessionGetPrev0Guard realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed
  rw [hf, hp,
    realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf_ghost_congr _ _ _ X W x y hp hm hs hcp hf hc hmsg]

/-- Inclusion lifting `realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed'` traces into
`cliDecPkCanonSlotEnvExact'` via `w4BinaryCallSiteDomCmk0_toPostBob`. -/
theorem realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed_sub_canon' [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed w4c_repairedStatesRecvEnvFam X W x evs) :
    cliDecPkCanonSlotEnvExact' X W x evs := by
  intro hTight _hPrev0
  obtain ⟨w4, hw4, hrem, hbase, henv⟩ := h hTight
  exact ⟨w4, w4BinaryCallSiteDomCmk0_toPostBob hw4, hrem, hbase, henv⟩

/-- Inclusion lifting `m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'` traces into
`cliDecPkCanonSlotEnvExactF2'` via `w4BinaryCallSiteDomCmk_toPostBob`. -/
theorem m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'_sub_canonF2' [LibsignalPlacement]
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
      w4c_repairedStatesRecvEnvFam X W x evs) :
    cliDecPkCanonSlotEnvExactF2' X W x evs := by
  intro hTight
  obtain ⟨w4, hw4, hrem, hbase, henv⟩ := h hTight
  exact ⟨w4, w4BinaryCallSiteDomCmk_toPostBob hw4, hrem, hbase, henv⟩

end LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
