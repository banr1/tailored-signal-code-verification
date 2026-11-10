/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1TrapPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegClonePlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecryptPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegTailPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegExitPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.DropsPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.ClonePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetState
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightModel
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch

/-!
# Relocatable `try_decrypt_from_record` Region on CLI Block `463`

Proves `recordDecryptV1_placed_region_vregs_ok_PTight_cli` (and `[LibsignalFullPlacement]`
corollaries) on `lsProg_463` against `recordDecryptPlacedSpecTPTight` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record hiding
  LibsignalCodeRoLoaded ls_externAt?_226 ls_hook_ok_226 recEntryPlaced recVPCPlaced recMPCPlaced
  recFPCPlaced recJPCPlaced recExitPlaced recMetaPlaced recFramePlaced tryDecryptPlacedSpec
  recordDecryptPlacedSpec VStatePlaced MStatePlaced FStatePlaced JStatePlaced SegClonePlacedSpec
  SegDecryptPlacedSpec SegMismatchPlacedSpec SegTailPlacedSpec SegExitPlacedSpec
  rootStack_le_of_recordPlacedPre recordDecrypt_placed_region_ok_of_seams segMismatch_placed_ok
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts hiding seg_of_sepWPp_F_placed
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps hiding
  clonePanicPostPlaced segClone_assemble_1_placed segClone_assemble_2_placed
  segClone_fields_10_to_11_placed
open CryptoVerification.Cli.LibsignalTripleRatchet.Record
open CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees
  (drop_session_structure_local2_placed_ok)
open CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone
  (chain_clone_placed_ok senderChain_clone_placed_ok)
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.Cli.CoinsTape
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalSpqrV1
open CryptoVerification.Cli.SpqrV1.M4
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
  (recordDecryptPlacedSpecP recordDecryptPlacedSpecTPTight)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `VStatePPlaced` and `segClone_placed_ok_P` -/

/-- Relocatable `VStatePlaced` with weakened pure precondition `VStateP`. -/
def VStatePPlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (x : RecordDecryptGhost)
    (G₁ : SessionGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = recVPCPlaced ∧ recMetaPlaced s0 s ∧
  ((x.st.remoteIdentity ≠ some x.st.localIdentity ∨
      CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid parse x.loc.name.bytes x.rem.name.bytes) ∧
    SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32) ∧
  CloneRel x.G G₁ ∧
  x.st.version.toNat = x.msg.messageVersion.toNat ∧
  (s.mem ⊨ recFramePlaced A x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    sessionStateAt A (sp + 0xca0#64) G₁ x.st ∗ errsAt A (sp + 0x5d8#64) [] ∗
    memRegion (sp + 0x4b0#64) 48 ∗ cliTapeAt ctl x.cur x.rest ∗ R)

theorem rootStack_le_of_recordPlacedPreP [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {x : RecordDecryptGhost}
    {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (recordDecryptPlacedSpecP C A ctl parse S).pre x s0 ∗ R) :
    rootStack ≤ s0.sp.toNat := by
  simp only [recordDecryptPlacedSpecP, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2.1.2.2.2.2.2.2.2.2

private theorem segClone_setWidth_64_truncate_32 (w : BitVec 32) :
    (w.setWidth 64).truncate 32 = w := by bv_kernel

private theorem segClone_fields_5_to_9_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec A)))
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v00 v08 v18 v30 : BitVec 64} {v14 v24 v28 v2c v3c : BitVec 32}
    {w288 w28c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.st.receiverChains = []
      then (blkPl_463).base + 0x544#64 else (blkPl_463).base + 0x300#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = x.st.sessionVersion.setWidth 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.st.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
      (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32)
      (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32) (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (blkPl_463).base + 0x594#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' → s1.readReg64 .x20 = pqCap' → s1.readReg64 .x21 = w288.setWidth 64 →
      s1.readReg64 .x22 = pqPtr' → s1.readReg64 .x23 = w28c.setWidth 64 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = alice'.cap → s1.readReg64 .x26 = pendCap' → s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = chainsPtr' → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      chains'.length = x.st.receiverChains.length → chainsCap' = BitVec.ofNat 64 x.st.receiverChains.length →
      alice'.bytes = x.G.alice.bytes → alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s1
        (A.pool ∗ vecAt A 104 8 (chainAt A) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
          vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗ vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
          ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗ vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
          OptPendClone A x.G.pending pendCap' pendPtr' ∗ OptKybClone A x.G.kyber kybCap' kybPtr' ∗
          (s.sp ↦₆₄ kybPtr') ∗ ((s.sp + 0x08#64) ↦₆₄ v08') ∗ ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗ ((s.sp + 0x24#64) ↦₃₂ v24') ∗ ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s.sp + 0x30#64) ↦₆₄ chainsCap') ∗ ((s.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
        Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0)) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H) ret s
      (A.pool ∗ vecAt A 104 8 (chainAt A) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗ vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        (s.sp ↦₆₄ v00) ∗ ((s.sp + 0x08#64) ↦₆₄ v08) ∗ ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₆₄ v30) ∗ ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
      Q (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  rw [segClone_vecAt_0x180_chains_eq A s.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains hchains_len]
  refine SepWPpCl.weaken_pre
    (P' := A.pool ∗ ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
      vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
      memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗
      (((s.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗ ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗ vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        (s.sp ↦₆₄ v00) ∗ ((s.sp + 0x08#64) ↦₆₄ v08) ∗ ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₆₄ v30) ∗ ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_receiverChains_placed hA hchainClone x R s0 s ret Q _
    hpc hrun hsp hx26 htr hchains_len
    fun s1 chainsCap' chainsPtr' chains' hchains_l hchains_c hpc1 hrun1 hsp1 hspA1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
  rw [← hsp1]
  refine SepWPpCl.weaken_pre
    (P' := A.pool ∗ optTailVecAt A 48 (s1.sp + 0x230#64) x.G.pending ∗
      ((s1.sp + 0x08#64) ↦₆₄ v08) ∗ ((s1.sp + 0x18#64) ↦₆₄ v18) ∗ ((s1.sp + 0x24#64) ↦₃₂ v24) ∗
      ((s1.sp + 0x28#64) ↦₃₂ v28) ∗ ((s1.sp + 0x2c#64) ↦₃₂ v2c) ∗ stackAt s1.sp allocHookStack ∗
      (vecAt A 104 8 (chainAt A) (s1.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (s1.sp + 0x198#64) ∗ vecU8At A (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optTailVecAt A 32 (s1.sp + 0x260#64) x.G.kyber ∗ ((s1.sp + 0x288#64) ↦₃₂ w288) ∗ ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
        (s1.sp ↦₆₄ v00) ∗ ((s1.sp + 0x14#64) ↦₃₂ v14) ∗ ((s1.sp + 0x30#64) ↦₆₄ v30) ∗
        ((s1.sp + 0x3c#64) ↦₃₂ v3c) ∗ memRegion (s1.sp + 0x5f0#64) 104 ∗
        memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecAt_0x180_chains_eq A s1.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains hchains_len,
            stackAt_chainClone_eq_alloc s1.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine segClone_pendingPreKey_placed hA hpc1 hrun1 hspA1 htr1
    fun s2 pendCap' pendPtr' v08' v24' v28' v2c' hpc2 hrun2 hsp2 hspA2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
  rw [← hsp2]
  refine SepWPpCl.weaken_pre
    (P' := A.pool ∗ optTailVecAt A 32 (s2.sp + 0x260#64) x.G.kyber ∗
      (s2.sp ↦₆₄ v00) ∗ ((s2.sp + 0x14#64) ↦₃₂ v14) ∗ ((s2.sp + 0x3c#64) ↦₃₂ v3c) ∗ stackAt s2.sp allocHookStack ∗
      (vecAt A 104 8 (chainAt A) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
        optTailVecAt A 48 (s2.sp + 0x230#64) x.G.pending ∗ OptPendClone A x.G.pending pendCap' pendPtr' ∗
        vecGhostAt A x.G.alice (s2.sp + 0x198#64) ∗ vecU8At A (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        ((s2.sp + 0x288#64) ↦₃₂ w288) ∗ ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
        ((s2.sp + 0x08#64) ↦₆₄ v08') ∗ ((s2.sp + 0x18#64) ↦₆₄ pendPtr') ∗ ((s2.sp + 0x24#64) ↦₃₂ v24') ∗
        ((s2.sp + 0x28#64) ↦₃₂ v28') ∗ ((s2.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s2.sp + 0x30#64) ↦₆₄ v30) ∗
        memRegion (s2.sp + 0x5f0#64) 104 ∗ memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_pendingKyber_placed hA hpc2 hrun2 hspA2 htr2
    fun s3 kybCap' kybPtr' v14' hpc3 hrun3 hsp3 hspA3 hx19_3 hx22_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 htr3 => ?_
  have hx25_2' : (s2.readReg64 .x25).truncate 32 = x.st.sessionVersion := by
    rw [hx25_2, hx25_1, hx25, segClone_setWidth_64_truncate_32]
  rw [hx25_2', ← hsp3]
  refine SepWPpCl.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.alice (s3.sp + 0x198#64) ∗ ((s3.sp + 0x288#64) ↦₃₂ w288) ∗ ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗
      ((s3.sp + 0x30#64) ↦₆₄ v30) ∗ stackAt s3.sp allocHookStack ∗
      (vecAt A 104 8 (chainAt A) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
        optTailVecAt A 48 (s3.sp + 0x230#64) x.G.pending ∗ OptPendClone A x.G.pending pendCap' pendPtr' ∗
        optTailVecAt A 32 (s3.sp + 0x260#64) x.G.kyber ∗ OptKybClone A x.G.kyber kybCap' kybPtr' ∗
        vecU8At A (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        (s3.sp ↦₆₄ kybPtr') ∗ ((s3.sp + 0x08#64) ↦₆₄ v08') ∗ ((s3.sp + 0x14#64) ↦₃₂ v14') ∗
        ((s3.sp + 0x18#64) ↦₆₄ pendPtr') ∗ ((s3.sp + 0x24#64) ↦₃₂ v24') ∗ ((s3.sp + 0x28#64) ↦₃₂ v28') ∗
        ((s3.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s3.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
        memRegion (s3.sp + 0x5f0#64) 104 ∗ memRegion (s3.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_aliceBaseKey_placed hA hpc3 hrun3 hspA3 htr3
    fun s4 alice' hpc4 hrun4 hsp4 hspA4 hx19_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4 halice_b halice_c => ?_
  have hx26_3' : s3.readReg64 .x26 = chainsCap' := by reg_chain
  rw [hx26_3', ← hsp4]
  refine SepWPpCl.weaken_pre
    (P' := A.pool ∗ vecU8At A (s4.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ stackAt s4.sp allocHookStack ∗
      (vecAt A 104 8 (chainAt A) (s4.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (s4.sp + 0x198#64) ∗ optTailVecAt A 48 (s4.sp + 0x230#64) x.G.pending ∗
        optTailVecAt A 32 (s4.sp + 0x260#64) x.G.kyber ∗ ((s4.sp + 0x288#64) ↦₃₂ w288) ∗ ((s4.sp + 0x28c#64) ↦₃₂ w28c) ∗
        vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
        vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
        OptPendClone A x.G.pending pendCap' pendPtr' ∗ OptKybClone A x.G.kyber kybCap' kybPtr' ∗
        (s4.sp ↦₆₄ kybPtr') ∗ ((s4.sp + 0x08#64) ↦₆₄ v08') ∗ ((s4.sp + 0x14#64) ↦₃₂ v14') ∗
        ((s4.sp + 0x18#64) ↦₆₄ pendPtr') ∗ ((s4.sp + 0x24#64) ↦₃₂ v24') ∗ ((s4.sp + 0x28#64) ↦₃₂ v28') ∗
        ((s4.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s4.sp + 0x30#64) ↦₆₄ chainsCap') ∗ ((s4.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
        memRegion (s4.sp + 0x5f0#64) 104 ∗ memRegion (s4.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  have hx24_4' : s4.readReg64 .x24 = s4.sp + 0xca0#64 := by reg_chain
  refine segClone_pqRatchet_placed hA hpc4 hrun4 hspA4 hx24_4' htr4
    fun s5 pqCap' pqPtr' hpc5 hrun5 hsp5 hspA5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5 htr5 hpq_c => ?_
  have hsp_eq : s4.sp = s.sp := by reg_chain
  rw [hsp_eq] at hx24_5 ⊢
  refine SepWPpCl.weaken_pre
    (by rw [stackAt_chainClone_eq_alloc s.sp]; exact Entails.of_eq (by ac_rfl))
    (hnext s5 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr'
      hpc5 hrun5 (by reg_chain) hspA5 (by reg_chain) hx20_5 (by reg_chain) hx22_5 (by reg_chain)
      hx24_5 (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
      htr5 hchains_l hchains_c halice_b halice_c hpq_c)

private theorem segClone_wp_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hA : SegCloneHooks A H)
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec A)))
    (hsenderClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec A)))
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_463).base + 0x1a8#64)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (h27 : s0.readReg64 .x27 = x.sret) (h19 : s0.readReg64 .x19 = x.remA)
    (h23 : s0.readReg64 .x23 = s0.sp + 0x5f0#64) (h24 : s0.readReg64 .x24 = s0.sp + 0xca0#64)
    (hrc32 : x.st.receiverChains.length < 2 ^ 32) :
    SepWPpCl ((blkPC_463).rebase (blkPl_463).base H)
      (if x.st.version.toNat = x.msg.messageVersion.toNat then
         (blkPl_463).base + 0x69c#64 else (blkPl_463).base + 0x7e4#64)
      s0
      (memRegion s0.sp 0xa0 ∗ ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗ memRegion (s0.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool)
      (segClone_clonePostPlaced A ctl x s0)
      (clonePanicPostPlaced C A ctl uuidTryParse S x R s0) := by
  have hrc_lt : x.st.receiverChains.length < 2 ^ 63 := by omega
  rw [segClone_sessionStateAt_0x138_eq A s0.sp x.G x.st]
  refine SepWPpCl.weaken_pre
    (P' := ⌜PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey ∧
            (match x.st.remoteIdentity with
             | none => x.G.remoteIk.bytes = []
             | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey) ∧
            x.G.chains.length = x.st.receiverChains.length ∧
            x.G.pending.isSome = x.st.pendingPreKey ∧ x.G.regIds.length = 8 ∧
            x.G.localIk.bytes.length = 33 ∧
            (x.st.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)⌝ ∗
          (memRegion s0.sp 0xa0 ∗ ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
            vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗ vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦ₛ x.G.regIds) ∗ memRegion (s0.sp + 0x4b0#64) 0x950 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPpCl.pure_elim fun ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  obtain ⟨w288, w28c, _, h_reg_pts⟩ := exists_unpack32_pair_of_length_8 h_reg_len
  have h28c : s0.sp + 0x288#64 + 4#64 = s0.sp + 0x28c#64 := by bv_arith
  rw [h_reg_pts (s0.sp + 0x288#64), h28c]
  refine SepWPpCl.weaken_pre
    (P' := memRegion s0.sp 0xa0 ∗ ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
      ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
      vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗ memRegion (s0.sp + 0x4b0#64) 0x950 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
      cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗
      (A.pool ∗ vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
        vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗ vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
        ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        ((s0.sp + 0x288#64) ↦₃₂ w288) ∗ ((s0.sp + 0x28c#64) ↦₃₂ w28c)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_entry_combined_placed hpc hrun hsp h19 h27 h23 h24 ⟨rfl, rfl⟩
    fun s1 sv dv bq0 bq1 bq2 bq3 bq4 bq5 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1 => ?_
  rw [← hsp1] at hx23_1 hx24_1 ⊢
  refine SepWPpCl.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.localIk (s1.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s1.sp + 0x150#64) ∗
      vecU8At A (s1.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
      optSenderChainAt A (s1.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
      chunks96_6QAt (s1.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s1.sp + 0x5f0#64) 104 ∗
      ((s1.sp + 0x40#64) ↦₆₄ sv.v40) ∗ ((s1.sp + 0x48#64) ↦₆₄ sv.v48) ∗ ((s1.sp + 0x54#64) ↦₃₂ sv.v54) ∗
      ((s1.sp + 0x58#64) ↦₆₄ sv.v58) ∗ ((s1.sp + 0x60#64) ↦₆₄ sv.v60) ∗ ((s1.sp + 0x68#64) ↦₆₄ sv.v68) ∗
      ((s1.sp + 0x70#64) ↦₆₄ sv.v70) ∗ ((s1.sp + 0x78#64) ↦₆₄ sv.v78) ∗
      ((s1.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
      ((s1.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s1.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
      stackAt s1.sp chainCloneStack ∗
      (((s1.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗ ((s1.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (s1.sp + 0x198#64) ∗ vecU8At A (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optTailVecAt A 48 (s1.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s1.sp + 0x260#64) x.G.kyber ∗
        ((s1.sp + 0x288#64) ↦₃₂ w288) ∗ ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
        (s1.sp ↦₆₄ sv.v00) ∗ ((s1.sp + 0x08#64) ↦₆₄ sv.v08) ∗ ((s1.sp + 0x14#64) ↦₃₂ sv.v14) ∗
        ((s1.sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((s1.sp + 0x24#64) ↦₃₂ sv.v24) ∗ ((s1.sp + 0x28#64) ↦₃₂ sv.v28) ∗
        ((s1.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗ ((s1.sp + 0x30#64) ↦₆₄ sv.v30) ∗ ((s1.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
        memRegion (s1.sp + 0x10#64) 4 ∗ memRegion (s1.sp + 0x20#64) 4 ∗ memRegion (s1.sp + 0x38#64) 4 ∗
        memRegion (s1.sp + 0x50#64) 4 ∗ dstSlotsAt s1.sp dv ∗ ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
        segClone_fixedRestPlaced A ctl x s1.sp))
    (by unfold spillSlotsAt
        rw [segClone_vecAt_0x180_chains_eq A s1.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains h_chains_len,
            stackAt_chainClone_eq_alloc s1.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine segClone_fields_1_to_4_placed hA hsenderClone hpc1 hrun1 hspA1 hx23_1 htr1 hrc_lt
    fun s2 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc2 hrun2 hsp2 hspA2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 htr2 hloc_b hloc_c hrem_b hrem_c hinl => ?_
  rw [← hsp2] at hx23_2 ⊢
  have hx24_2' : s2.readReg64 .x24 = s2.sp + 0xca0#64 := by reg_chain
  refine SepWPpCl.weaken_pre
    (P' := A.pool ∗ vecAt A 104 8 (chainAt A) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
      vecGhostAt A x.G.alice (s2.sp + 0x198#64) ∗ vecU8At A (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
      optTailVecAt A 48 (s2.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s2.sp + 0x260#64) x.G.kyber ∗
      ((s2.sp + 0x288#64) ↦₃₂ w288) ∗ ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
      (s2.sp ↦₆₄ sv.v00) ∗ ((s2.sp + 0x08#64) ↦₆₄ sv.v08) ∗ ((s2.sp + 0x14#64) ↦₃₂ sv.v14) ∗
      ((s2.sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((s2.sp + 0x24#64) ↦₃₂ sv.v24) ∗ ((s2.sp + 0x28#64) ↦₃₂ sv.v28) ∗
      ((s2.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗ ((s2.sp + 0x30#64) ↦₆₄ sv.v30) ∗ ((s2.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
      memRegion (s2.sp + 0x5f0#64) 104 ∗ stackAt s2.sp chainCloneStack ∗
      (vecGhostAt A x.G.localIk (s2.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s2.sp + 0x150#64) ∗
        vecU8At A (s2.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        optSenderChainAt A (s2.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗ vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
        vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗ optSenderChainHeap A sender' x.st.senderChain ∗
        chunks96_6QAt (s2.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        ((s2.sp + 0x40#64) ↦₆₄ scCap') ∗ ((s2.sp + 0x48#64) ↦₆₄ rootPtr') ∗
        ((s2.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗ ((s2.sp + 0x58#64) ↦₆₄ 32#64) ∗
        ((s2.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗ ((s2.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
        ((s2.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗ ((s2.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
        ((s2.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
        ((s2.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗ memRegion (s2.sp + 0x10#64) 4 ∗
        memRegion (s2.sp + 0x20#64) 4 ∗ memRegion (s2.sp + 0x38#64) 4 ∗
        memRegion (s2.sp + 0x50#64) 4 ∗ dstSlotsAt s2.sp dv ∗
        ((s2.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
        segClone_fixedRestPlaced A ctl x s2.sp))
    (by rw [segClone_vecAt_0x180_chains_eq A s2.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains h_chains_len]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine segClone_fields_5_to_9_placed hA hchainClone hpc2 hrun2 hspA2 hx24_2' hx25_2 hx26_2 htr2 h_chains_len
    fun s3 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr'
      hpc3 hrun3 hsp3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 htr3
      hchains_l hchains_c halice_b halice_c hpq_c => ?_
  rw [← hsp3] at hx24_3 ⊢
  refine SepWPpCl.weaken_pre
    (P' := dstSlotsAt s3.sp dv ∗ chunks96_6QAt (s3.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
      spillSlotsAt s3.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
        scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap localIk'.ptr localIk'.cap ∗
      ((s3.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
      (A.pool ∗ vecGhostAt A x.G.localIk (s3.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s3.sp + 0x150#64) ∗
        vecU8At A (s3.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (s3.sp + 0x198#64) ∗ vecU8At A (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optSenderChainAt A (s3.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        optTailVecAt A 48 (s3.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s3.sp + 0x260#64) x.G.kyber ∗
        ((s3.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s3.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        ((s3.sp + 0x288#64) ↦₃₂ w288) ∗ ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗
        vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗ vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
        vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
        vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
        vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗ vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
        optSenderChainHeap A sender' x.st.senderChain ∗
        OptPendClone A x.G.pending pendCap' pendPtr' ∗ OptKybClone A x.G.kyber kybCap' kybPtr' ∗
        memRegion (s3.sp + 0x5f0#64) 104 ∗ stackAt s3.sp chainCloneStack ∗ segClone_fixedRestPlaced A ctl x s3.sp))
    (by unfold spillSlotsAt; exact Entails.of_eq (by ac_rfl)) ?_
  apply SepWPpCl.of_sepWPp
  refine segClone_fields_10_to_11_placed dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08' v14' pendCap' pendPtr'
    v24' v28' v2c' w288 w28c _
    hpc3 hrun3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3
    fun s4 hpc4 hrun4 hsp4 hspA4 hx9_4 hx29_4 htr4 => ?_
  have hsp_eq : s3.sp = s0.sp := by reg_chain
  rw [hsp_eq]
  refine SepWPp.done hpc4 hrun4 ⟨by reg_chain, hspA4, by reg_chain, htr4, hx9_4, ?_⟩
  have hdst :=
    segClone_dstSlotsWrittenAt_entails_sessionStateAt A s0.sp x localIk' remoteIk' rootPtr'
      chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap'
      sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24' kybCap' kybPtr' v14' w288 w28c
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
      hloc_b hloc_c hrem_b hrem_c hchains_l hchains_c halice_b halice_c hpq_c hinl
  have hsrc :=
    segClone_srcSessionState_reassemble A s0.sp x w288 w28c
      h_loc_deser h_rem_deser h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
  have hrest :=
    segClone_fixedRest_reassemble_placed A ctl x s0.sp sq0 sq1 sq2 sq3 sq4 sq5
      kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
      scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap localIk'.ptr localIk'.cap
  rw [stackAt_chainClone_eq_alloc s0.sp]
  refine Entails.trans
    (Q := (segClone_dstSlotsWrittenAt s0.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
              pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24'
              kybCap' kybPtr' v14' x.st.sessionVersion x.st.previousCounter w288 w28c ∗
            vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗ vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
            vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
            vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗ vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
            optSenderChainHeap A sender' x.st.senderChain ∗
            OptPendClone A x.G.pending pendCap' pendPtr' ∗ OptKybClone A x.G.kyber kybCap' kybPtr') ∗
          (vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗ vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦₃₂ w288) ∗ ((s0.sp + 0x28c#64) ↦₃₂ w28c)) ∗
          (spillSlotsAt s0.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
              scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap localIk'.ptr localIk'.cap ∗
            chunks96_6QAt (s0.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ memRegion (s0.sp + 0x5f0#64) 104 ∗
            ((s0.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            memRegion (s0.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
            stackAt s0.sp allocHookStack ∗ A.pool ∗ segClone_fixedRestPlaced A ctl x s0.sp))
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hdst (sepConj_mono hsrc hrest)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G₁
  refine Entails.sepExists_right G₁ ?_
  exact Entails.of_eq (by ac_rfl)

/-- `segClone_placed_ok_P` under the weakened `(x.st.remoteIdentity ≠ ... ∨ DistinctSid ...)`
precondition (`segClone_wp_placed` never touches `x.st.remoteIdentity`). -/
theorem segClone_placed_ok_P [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (_hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hchainClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec A)))
    (hsenderClone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec A)))
    (_hdrop1 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec A)))
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = recEntryPlaced) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0 ∗ R)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s0.mem) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s0 s' ∧
      ((∃ G₁, VStatePPlaced A ctl uuidTryParse x G₁ R s0 s') ∨
       (∃ G₁, MStatePlaced A ctl x G₁ R s0 s') ∨
       regionOutcome (recordDecryptPlacedSpec C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  have hA : SegCloneHooks A H := ⟨hshim, halloc, hmemcpy, hpanic⟩
  dsimp only [recEntryPlaced] at hpc
  dsimp only [recordDecryptPlacedSpecP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfl, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hsp, h27, h19, h23, h24, hrem_ne, hseeds, hrc32, _⟩, hm⟩ := hpre
  have hwp :=
    segClone_wp_placed (C := C) (ctl := ctl) (S := S)
      hA hchainClone hsenderClone x R s0
      hpc hrun hsp h27 h19 h23 h24 hrc32
  obtain ⟨sf, hsteps, hout⟩ := hwp hfl.1 R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hspf, hspAf, hx29f, ⟨htrf, hvrf⟩, hx9f, hent⟩ |
      ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · have hmeta : recMetaPlaced s0 sf :=
      ⟨hrunf, hspf, hspAf, hx29f, htrf,
       Record.LibsignalCodeRoLoaded.of_keepsFrozen hfl hsteps.keepsFrozen, hvrf⟩
    have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf'
    obtain ⟨G₁, hmf'⟩ := hmf'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf'
    obtain ⟨hclone, hmf'⟩ := hmf'
    simp only [sepConj_assoc] at hmf'
    by_cases hver : x.st.version.toNat = x.msg.messageVersion.toNat
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcV : sf.pc = recVPCPlaced := by simpa [recVPCPlaced] using hpcf
      refine ⟨sf, hsteps, Or.inl ⟨G₁, hpcV, hmeta, ⟨hrem_ne, hseeds, hrc32⟩, hclone, hver, ?_⟩⟩
      simpa only [sepConj_assoc] using hmf'
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcM : sf.pc = recMPCPlaced := by simpa [recMPCPlaced] using hpcf
      refine ⟨sf, hsteps, Or.inr (Or.inl ⟨G₁, hpcM, hmeta, hver, hx9f, ?_⟩)⟩
      simpa only [sepConj_assoc] using hmf'
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Model & Outcome Bridges for Tight `onPanic` -/

abbrev rdpTryPlacedSpecTrap [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost where
  pre := fun x s =>
    ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
      (⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
        s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
        (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
        (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
          CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidParse x.loc.name.bytes x.rem.name.bytes) ∧
        SeedsLen32 x.st ∧
        x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
      memRegion x.ret 48 ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
      stackAt s.sp rootStack ∗ A.pool) ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s.mem⌝
  post := fun x s0 sf =>
    (tryDecryptPlacedSpec C A ctl uuidParse S).post x s0 sf ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt
  onPanic := CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight C S uuidParse

private theorem rdp_tryDecryptSpecTPTightAt_eq [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTPTightAt C A ctl uuidParse S =
      rdpTryPlacedSpecTrap C A ctl uuidParse S := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTPTightAt,
    withLsCodeRoLoaded,
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptRawSpecTPTightAt,
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight,
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP,
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight,
    rdpTryPlacedSpecTrap]
  congr 1
  · funext x s; ac_rfl
  · funext x s0 sf; ac_rfl

private theorem rdp_tryDecrypt_onPanic_entails_tight_placed {C : Crypto} {S : SpqrModel}
    {x : RecordDecryptGhost} {G₁ : SessionGhost}
    {s0 s sf : State} {F : SepProp} {sp : BitVec 64}
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat)
    (htr : s.trace = s0.trace) :
    CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight C S uuidTryParse
        (mkTryDecryptGhost sp x G₁) s sf ∗ F ⊢
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight C S uuidTryParse x s0 sf := by
  dsimp only [CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight,
    CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hpan, hpref⟩ => ?_
  unfold allocFailedIn at hpan ⊢
  rw [htr] at hpan hpref
  refine Entails.pure_right ⟨?_, hpref⟩ (entails_anyHeap _)
  rcases hpan with hmod | halloc
  · exact Or.inl (model_panic_of_tryDecrypt_panic C S sp x G₁ heq hmod)
  · exact Or.inr halloc

private theorem rdp_grow_onPanic_entails_tight_placed {P1 : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P1 ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  unfold allocFailedIn at halloc ⊢
  rw [htr] at halloc hpref
  exact Entails.pure_right ⟨Or.inr halloc, hpref⟩ (entails_anyHeap _)

private theorem rdp_seg_of_sepWPp_JF_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_463).rebase (blkPl_463).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        JStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 sf ∨
          FStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight C S uuidTryParse x s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
      (JStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s' ∨
        FStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s' ∨
        regionOutcome (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hJF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · rcases hJF hmf with hJ | hF
    · exact ⟨sf, hsteps, Or.inl hJ⟩
    · exact ⟨sf, hsteps, Or.inr (Or.inl hF)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private def rdpNoPanicPlaced (S : SpqrModel) : SpqrModel :=
  { S with recvPanics := fun _ _ => false }

private theorem rdp_tryModel_noPanic_or_panic_placed (C : Crypto) (S : SpqrModel)
    (y : TryDecryptGhost) :
    y.model C (rdpNoPanicPlaced S) uuidTryParse = y.model C S uuidTryParse ∨
      (y.model C S uuidTryParse).1 = .error .panic := by
  rcases htr : Mut.exec TripleRatchet.fromSessionState y.st with ⟨e | tr, st1⟩
  · left
    rw [(Decrypt.Model.model_of_fromSessionState_error (S := rdpNoPanicPlaced S) htr).1,
      (Decrypt.Model.model_of_fromSessionState_error (S := S) htr).1]
  · rcases herc :
        Mut.exec (RatchetState.ensureReceiverChain C y.msg.senderRatchetKey (coinsOf y.rest))
          tr.ratchet with ⟨e | ck, r1⟩
    · left
      rw [Decrypt.Model.model_of_ensureReceiverChain_error (S := rdpNoPanicPlaced S) htr herc,
        Decrypt.Model.model_of_ensureReceiverChain_error (S := S) htr herc]
    · rcases hcmk :
          Mut.exec
            (RatchetState.consumeMessageKey C.F y.msg.senderRatchetKey ck y.msg.counter y.msgType)
            r1 with ⟨e | mkg, r2⟩
      · left
        rw [Decrypt.Model.model_of_cmk_error (S := rdpNoPanicPlaced S) htr herc hcmk,
          Decrypt.Model.model_of_cmk_error (S := S) htr herc hcmk]
      · have hpq : tr.pqrState = y.st.pqRatchetState :=
          (Decrypt.Model.fromSessionState_ok_inv htr).2.2.1
        cases hp : S.recvPanics y.st.pqRatchetState y.msg.pqRatchet
        · left
          have hnp : S.recvPanics tr.pqrState y.msg.pqRatchet = false := hpq ▸ hp
          have hnp' : (rdpNoPanicPlaced S).recvPanics tr.pqrState y.msg.pqRatchet = false := rfl
          rcases hspqr : S.recv tr.pqrState y.msg.pqRatchet with sd | ⟨newPqrState, pqrKey⟩
          · rw [Decrypt.Model.model_of_spqr_error (S := rdpNoPanicPlaced S) htr herc hcmk hspqr hnp',
              Decrypt.Model.model_of_spqr_error (S := S) htr herc hcmk hspqr hnp]
          · cases hmac :
                y.msg.verifyMacWithAddresses C.F
                  (serializeAddresses (serviceIdParse uuidTryParse) y.rem y.loc)
                  tr.remoteIdentityKey tr.localIdentityKey
                  (mkg.generateKeys C.F pqrKey).macKey
            · rw [Decrypt.Model.model_of_verifyMac_false (S := rdpNoPanicPlaced S)
                  htr herc hcmk hspqr hmac hnp',
                Decrypt.Model.model_of_verifyMac_false (S := S) htr herc hcmk hspqr hmac hnp]
            · cases haes :
                  aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                    (mkg.generateKeys C.F pqrKey).iv y.msg.ciphertext
              · rw [Decrypt.Model.model_of_aesDec_none (S := rdpNoPanicPlaced S)
                    htr herc hcmk hspqr hmac haes hnp',
                  Decrypt.Model.model_of_aesDec_none (S := S) htr herc hcmk hspqr hmac haes hnp]
              · rw [Decrypt.Model.model_of_aesDec_some (S := rdpNoPanicPlaced S)
                    htr herc hcmk hspqr hmac haes hnp',
                  Decrypt.Model.model_of_aesDec_some (S := S) htr herc hcmk hspqr hmac haes hnp]
        · right
          exact Decrypt.Model.model_of_recvPanics htr herc hcmk hp

private theorem rdp_model_noPanic_or_panic_placed (C : Crypto) (S : SpqrModel)
    (x : RecordDecryptGhost) :
    x.model C (rdpNoPanicPlaced S) uuidTryParse = x.model C S uuidTryParse ∨
      (x.model C S uuidTryParse).1 = .error .panic := by
  by_cases heq : x.st.version.toNat = x.msg.messageVersion.toNat
  · rw [model_eq_of_version_eq C (rdpNoPanicPlaced S) 0#64 x x.G heq]
    rcases rdp_tryModel_noPanic_or_panic_placed C S (mkTryDecryptGhost 0#64 x x.G) with h | hpan
    · left
      rw [h, ← model_eq_of_version_eq C S 0#64 x x.G heq]
    · right
      exact model_panic_of_tryDecrypt_panic C S 0#64 x x.G heq hpan
  · left
    dsimp [RecordDecryptGhost.model, SessionState.tryDecryptFromRecord, Mut.exec, StateT.run,
      ExceptT.run, ExceptT.mk, pure, Except.pure, Bind.bind, Monad.toBind, ExceptT.bind,
      ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, StateT.lift, throw, throwThe, MonadExceptOf.throw]
    simp [heq]

private theorem rdp_spec_S_exists_placed (C : Crypto) (S : SpqrModel) (x : RecordDecryptGhost) :
    ∃ S' : SpqrModel,
      x.model C S' uuidTryParse = x.model C S uuidTryParse ∧
      (∀ (s0 sf : State),
        (x.model C S' uuidTryParse).1 = .error .panic ∨
          (x.st.version.toNat = x.msg.messageVersion.toNat ∧
            S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
          allocFailedIn s0 sf →
        (x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 sf) := by
  rcases rdp_model_noPanic_or_panic_placed C S x with hmod_eq | hmod_pan
  · refine ⟨rdpNoPanicPlaced S, hmod_eq, fun s0 sf h => ?_⟩
    rcases h with hp | ⟨_, hpan⟩ | halloc
    · exact Or.inl (hmod_eq ▸ hp)
    · exact nomatch hpan
    · exact Or.inr halloc
  · exact ⟨S, rfl, fun _ _ _ => Or.inl hmod_pan⟩

private theorem rdp_JStatePlaced_eq_of_model_eq [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S' S : SpqrModel} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    JStatePlaced C A ctl uuidTryParse S' x R s0 s =
      JStatePlaced C A ctl uuidTryParse S x R s0 s := by
  dsimp only [JStatePlaced]
  rw [hmod]

private theorem rdp_FStatePlaced_eq_of_model_eq [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S' S : SpqrModel} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    FStatePlaced C A ctl uuidTryParse S' x R s0 s =
      FStatePlaced C A ctl uuidTryParse S x R s0 s := by
  dsimp only [FStatePlaced]
  rw [hmod]

private theorem rdp_post_eq_of_model_eq_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S' S : SpqrModel} {x : RecordDecryptGhost} {s0 sf : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    (recordDecryptPlacedSpec C A ctl uuidTryParse S').post x s0 sf =
      (recordDecryptPlacedSpec C A ctl uuidTryParse S).post x s0 sf := by
  dsimp only [recordDecryptPlacedSpec]
  rw [hmod]

private theorem rdp_regionOutcome_of_tokenFrame_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S' S : SpqrModel} {x : RecordDecryptGhost} {R : SepProp} {s0 sf : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse)
    (hpan_imp : ∀ (s0 sf : State),
      (x.model C S' uuidTryParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧ S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
        allocFailedIn s0 sf →
      (x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 sf)
    (hout : regionOutcome (recordDecryptPlacedSpec C A ctl uuidTryParse S')
      recExitPlaced x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 sf) :
    regionOutcome (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S) recExitPlaced x R s0 sf := by
  rcases hout with ⟨hpc, hrun, hvregs, hpost⟩ | ⟨hpan, hpost⟩
  · left; refine ⟨hpc, hrun, hvregs, ?_⟩
    rw [rdp_post_eq_of_model_eq_placed hmod] at hpost
    dsimp only [recordDecryptPlacedSpecTPTight,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.recordDecryptPlacedSpecTF]
    have heq : (recordDecryptPlacedSpec C A ctl uuidTryParse S).post x s0 sf ∗
        (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) =
      (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (recordDecryptPlacedSpec C A ctl uuidTryParse S).post x s0 sf) ∗ R := by ac_rfl
    exact heq ▸ hpost
  · right; refine ⟨hpan, ?_⟩
    dsimp only [recordDecryptPlacedSpec] at hpost
    dsimp only [recordDecryptPlacedSpecTPTight, CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight]
    have hent :
        (⌜((x.model C S' uuidTryParse).1 = .error .panic ∨
            (x.st.version.toNat = x.msg.messageVersion.toNat ∧ S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet = true) ∨
            allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) ⊢
        (⌜((x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap) ∗ R := by
      have hassoc1 :
          (⌜((x.model C S' uuidTryParse).1 = .error .panic ∨
              (x.st.version.toNat = x.msg.messageVersion.toNat ∧ S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet = true) ∨
              allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
            (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) =
          (⌜((x.model C S' uuidTryParse).1 = .error .panic ∨
              (x.st.version.toNat = x.msg.messageVersion.toNat ∧ S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet = true) ∨
              allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
            (anyHeap ∗ SpqrV1.GF.Mul2U16.tokenInitPlacedAt)) ∗ R := by ac_rfl
      rw [hassoc1]; refine sepConj_mono_left (Entails.pure_left fun ⟨hp, htr⟩ => ?_)
      exact Entails.pure_right ⟨hpan_imp s0 sf hp, htr⟩ (entails_anyHeap _)
    exact Satisfies.mono hent hpost

/-! ## 3. `rdp_segDecrypt_placed_ok_TPTight` (Block `463`) -/

open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts.SegDecryptRegReadSimp

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

private theorem rdp_cli_tapeAfter_tryDecrypt_entails [LibsignalPlacement] (C : Crypto) (ctl sp : BitVec 64)
    (x : RecordDecryptGhost) (G₁ : SessionGhost)
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat) :
    cliTapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ⊢
      cliTapeAfter ctl x.cur x.rest (x.draws C) := by
  rw [draws_eq_tryDecrypt_of_version_eq C sp x G₁ heq]
  exact Entails.refl _

set_option maxHeartbeats 1200000 in
theorem rdp_segDecrypt_placed_ok_TPTight [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hmemcpy_sat : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (htry_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (rdpTryPlacedSpecTrap C A ctl uuidTryParse S)))
    (hset_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec A)))
    (hdrop_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hgrow_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (hclosure_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl logClosurePlacedSpec))
    (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State)
    (_hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hV : VStatePPlaced A ctl uuidTryParse x G₁ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s)
    (hsp_bound : rootStack ≤ s0.sp.toNat)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
      (JStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s' ∨
       FStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s' ∨
       regionOutcome (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  rcases hV with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hfl, hvregs⟩,
    ⟨hrem_or_dist, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  dsimp only [recVPCPlaced] at hpc
  have hmemcpy_rel := ls_hook_ok_226 (by decide) hmemcpy_sat
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  rw [hsp0] at hsp_bound hmem
  unfold recFramePlaced at hmem
  simp only [← sepConj_assoc] at hmem
  apply rdp_seg_of_sepWPp_JF_placed hmem hL
    (target := decryptTarget (blkPl_463).base ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_placed hfl (mid := lsmpl.base 434)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) ((blkPl_463).base + bv% (1720)) |>.setPC
      (lsmpl.base 434)).sp.toNat := hsp_bound
  cli_segDecrypt_wpp_call_placed htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }) hF1
    (rdp_tryDecrypt_onPanic_entails_tight_placed heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hnpan hdec ⊢
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 462)
      refine segDecrypt_replace_pre
        (speAt_decomp6 A (LibsignalTripleRatchetRepr.utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H_spe hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_placed hclosure_rel () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 42)
      segDecrypt_wp_extract_exists
      rename_i htr_cl
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      cli_segDecrypt_wpp_call_placed hgrow_rel (s.sp + 0x5d8#64, 0#64, 8#64, []) hF3
        (rdp_grow_onPanic_entails_tight_placed (by simp only [wp_norm, arm64_norm, htr_cl, htr_sf, htr]))
      apply segDecrypt_of_sepWP_placed hF_sf_2 (mid := (blkPl_463).base + 2128#64)
      segDecrypt_wp_extract_exists
      rename_i p' hp'
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      wp_steps
      rw [hsp_sf_1, hsp_sf]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A s.sp p' e tag w1 w2 w3 w4 w5 H_spe hp'.2 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (rdp_cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4
      apply segDecrypt_of_sepWP_ret_placed hF4
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro _ hmf
      right
      refine ⟨by dsimp only [recFPCPlaced]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hp'.1, htr_cl, htr_sf, htr],
                hF4,
                by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFramePlaced
        rw [hsp0]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
    · obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 442)
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_placed hdrop_rel
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost })
        hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_placed hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i htr_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (rdp_cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, h_17, hsp0],
        by simp only [wp_norm, arm64_norm, h_18],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, htr_drop, htr_sf, htr],
                hF3,
                by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFramePlaced
        rw [hsp0, hmodel_dup1]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
  · dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.ρ "memcpy")
    rw [sessionStateAt_eq_inline_sep_heap A (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp]
    unfold FromRecordCallees.lsLogOff
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    cli_segDecrypt_wpp_call_placed hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 48)
    segDecrypt_wp_extract_exists
    rename_i hmc
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    cli_segDecrypt_wpp_call_placed hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost }) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_placed hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i htr_set
    wp_steps
    rw [hsp_sf_1, hsp_sf]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (rdp_cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, h_27, h_17, hsp0],
      by simp only [wp_norm, arm64_norm, h_28, h_18],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, htr_set, hmc.2, htr_sf, htr],
              hF4,
              by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
    · unfold recFramePlaced FromRecordCallees.lsLogOff
      rw [hsp0, hmodel_ok1, hmodel_ok2]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

set_option maxHeartbeats 1200000 in
theorem rdp_segDecrypt_full_placed_ok_TPTight [LibsignalFullPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (hmemcpy_sat : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (htry_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (rdpTryPlacedSpecTrap C A ctl uuidTryParse S)))
    (hset_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec A)))
    (hdrop_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hgrow_rel : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State)
    (_hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hV : VStatePPlaced A ctl uuidTryParse x G₁ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s)
    (hsp_bound : rootStack ≤ s0.sp.toNat)
    (hFroz : LibsignalFrozen lsmpl s.mem)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
      (JStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s' ∨
       FStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s' ∨
       regionOutcome (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  have _ := CryptoVerification.CliRatchet.DecPlaced.instIsLsBlockProg_463 H
  have hclosure_rel :=
    log_closure_coins_frozen_placed_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
  rcases hV with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, _hfl, hvregs⟩,
    ⟨hrem_or_dist, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  dsimp only [recVPCPlaced] at hpc
  have hmemcpy_rel := ls_hook_ok_226 (by decide) hmemcpy_sat
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  rw [hsp0] at hsp_bound hmem
  unfold recFramePlaced at hmem
  simp only [← sepConj_assoc] at hmem
  apply rdp_seg_of_sepWPp_JF_placed hmem hL
    (target := decryptTarget (blkPl_463).base ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_lsfull hFroz (mid := lsmpl.base 434)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) ((blkPl_463).base + bv% (1720)) |>.setPC
      (lsmpl.base 434)).sp.toNat := hsp_bound
  cli_segDecrypt_wpp_call_lsfull htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }) hF1
    (rdp_tryDecrypt_onPanic_entails_tight_placed heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hnpan hdec ⊢
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.base 462)
      refine segDecrypt_replace_pre
        (speAt_decomp6 A (LibsignalTripleRatchetRepr.utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H_spe hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_lsfull hclosure_rel () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_lsfull hF_sf_1 (mid := lsmpl.base 42)
      segDecrypt_wp_extract_exists
      rename_i htr_cl
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      cli_segDecrypt_wpp_call_lsfull hgrow_rel (s.sp + 0x5d8#64, 0#64, 8#64, []) hF3
        (rdp_grow_onPanic_entails_tight_placed (by simp only [wp_norm, arm64_norm, htr_cl, htr_sf, htr]))
      apply segDecrypt_of_sepWP_lsfull hF_sf_2 (mid := (blkPl_463).base + 2128#64)
      segDecrypt_wp_extract_exists
      rename_i p' hp'
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      wp_steps
      rw [hsp_sf_1, hsp_sf]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A s.sp p' e tag w1 w2 w3 w4 w5 H_spe hp'.2 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (rdp_cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4
      apply segDecrypt_of_sepWP_ret_lsfull hF4
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro _ hmf
      right
      refine ⟨by dsimp only [recFPCPlaced]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hp'.1, htr_cl, htr_sf, htr],
                Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF4,
                by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFramePlaced
        rw [hsp0]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
    · obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.base 442)
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      cli_segDecrypt_wpp_call_lsfull hdrop_rel
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost })
        hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_lsfull hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i htr_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (rdp_cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, h_17, hsp0],
        by simp only [wp_norm, arm64_norm, h_18],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, htr_drop, htr_sf, htr],
                Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF3,
                by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFramePlaced
        rw [hsp0, hmodel_dup1]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
  · dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.ρ "memcpy")
    rw [sessionStateAt_eq_inline_sep_heap A (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp]
    unfold FromRecordCallees.lsLogOff
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    cli_segDecrypt_wpp_call_lsfull hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_lsfull hF_sf_1 (mid := lsmpl.base 48)
    segDecrypt_wp_extract_exists
    rename_i hmc
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    cli_segDecrypt_wpp_call_lsfull hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost }) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_lsfull hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i htr_set
    wp_steps
    rw [hsp_sf_1, hsp_sf]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (rdp_cli_tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, h_27, h_17, hsp0],
      by simp only [wp_norm, arm64_norm, h_28, h_18],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, htr_set, hmc.2, htr_sf, htr],
              Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF4,
              by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
    · unfold recFramePlaced FromRecordCallees.lsLogOff
      rw [hsp0, hmodel_ok1, hmodel_ok2]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

/-! ## 4. Top-Level Placed Region Assembly (`recordDecryptV1_placed_region_vregs_ok_PTight_cli`) -/

private theorem rdp_region_reaches_placed_TPTight [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((Decrypt.blkPC_434).rebase (Decrypt.blkPl_434).base H) (lsmpl.base 434)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTPTightAt
        C A ctl uuidTryParse S))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl logClosurePlacedSpec)) :
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = recEntryPlaced →
      s0.status = .Running →
      (s0.mem ⊨ (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S).pre x s0 ∗ R) →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S)
        recExitPlaced x R s0 s0 := by
  have _ := CryptoVerification.CliRatchet.DecPlaced.instIsLsBlockProg_463 H
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434 H
  have hchainClone :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chain_clone_placed_ok
          hshim halloc hmemcpy hpanic))
  have hsenderClone :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.senderChain_clone_placed_ok
          hshim halloc hmemcpy hpanic))
  have hdrop1 :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (FromRecordCallees.drop_session_structure_local1_placed_ok hdealloc)
  have hdropLocal2 :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure_local2_placed_ok hdealloc)
  have hsetState :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (FromRecordCallees.set_session_state_placed_ok hmemcpy
        (FromRecordCallees.drop_session_structure_local1_placed_ok hdealloc))
  have hgrowSpe :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (FromRecordCallees.grow_one_spe_placed_ok hshim halloc hrealloc hpanic)
  have htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (rdpTryPlacedSpecTrap C A ctl uuidTryParse S)) :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H) (j := 434)
      (subroutine_ok_withLsCodeLoaded_of_plain (rdp_tryDecryptSpecTPTightAt_eq C A ctl uuidTryParse S ▸ hTry))
  intro x R s0 hpc hst hpre hL
  obtain ⟨S', hmod, hpan_imp⟩ := rdp_spec_S_exists_placed C S x
  dsimp only [recordDecryptPlacedSpecTPTight, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.recordDecryptPlacedSpecTPTightF, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.recordDecryptPlacedSpecTF] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  have hpre' : s0.mem ⊨
      (recordDecryptPlacedSpecP C A ctl uuidTryParse S').pre x s0 ∗
      (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) := by
    change s0.mem ⊨
      (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0 ∗
      (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R)
    have heq :
        (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0) ∗ R =
        (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0 ∗
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) := by ac_rfl
    exact heq ▸ hpre
  have hstk := rootStack_le_of_recordPlacedPreP hpre'
  have hJ : ∀ s,
      JStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S)
        recExitPlaced x R s0 s := by
    intro s hs hLs
    rw [← rdp_JStatePlaced_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hout⟩ :=
      segExit_placed_ok (C := C) (A := A) (ctl := ctl) (S := S') (H := H)
        hdealloc x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s hs hLs
    exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  have hF : ∀ s,
      FStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S)
        recExitPlaced x R s0 s := by
    intro s hs hLs
    rw [← rdp_FStatePlaced_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hnext⟩ :=
      segTail_placed_ok (C := C) (A := A) (ctl := ctl) (S := S') (H := H)
        hshim halloc hpanic hdropLocal2
        x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s hs hLs
    rcases hnext with hj | hout
    · rw [rdp_JStatePlaced_eq_of_model_eq hmod] at hj
      exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    segClone_placed_ok_P (C := C) (A := A) (ctl := ctl) (S := S')
      hshim halloc hdealloc hmemcpy hpanic hchainClone hsenderClone hdrop1
      x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 hpc hst hpre' hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ :=
      rdp_segDecrypt_placed_ok_TPTight hmemcpy htd
        hsetState hdropLocal2 hgrowSpe hclosure x G₁ R s0 s' hQ hv hstk (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ :=
      segMismatch_placed_ok (C := C) (A := A) (ctl := ctl) (S := S') (H := H)
        hgrowSpe hclosure x G₁ (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s' hm (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · rw [rdp_FStatePlaced_eq_of_model_eq hmod] at hf
      exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩

/-- Parametric `[LibsignalPlacement]` `region_ok` for `recordDecryptPlacedSpecTPTight` on Block `463`. -/
theorem recordDecrypt_placed_region_ok_TPTight [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((Decrypt.blkPC_434).rebase (Decrypt.blkPl_434).base H) (lsmpl.base 434)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTPTightAt
        C A ctl uuidTryParse S))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl logClosurePlacedSpec)) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S) :=
  CryptoVerification.LibsignalTripleRatchet.Record.region_ok_of_reaches
    (rdp_region_reaches_placed_TPTight C A ctl S H hshim halloc hrealloc hdealloc hmemcpy hpanic hTry hclosure)

/-- Parametric `[LibsignalPlacement]` `region_ok` with `Spec.withVRegs` on Block `463`. -/
theorem recordDecrypt_placed_region_vregs_ok_TPTight [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((Decrypt.blkPC_434).rebase (Decrypt.blkPl_434).base H) (lsmpl.base 434)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTPTightAt
        C A ctl uuidTryParse S))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl logClosurePlacedSpec)) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S).withVRegs := by
  intro x R s0 hpc hst hpre hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', hvregs, hpost⟩ | hpan⟩ :=
    rdp_region_reaches_placed_TPTight C A ctl S H hshim halloc hrealloc hdealloc hmemcpy hpanic hTry hclosure
      x R s0 hpc hst hpre hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', ?_⟩⟩
    dsimp only [Spec.withVRegs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvregs, hpost⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Concrete placed CLI `region_ok` with `Spec.withVRegs` on
`lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))` at `S := spqrV1 W.C.F W.Q.K`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_placed_region_vregs_ok_PTight_cli
    [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks)
    (W : CliHooks) (ctl : BitVec 64)
    (hG : Slots.CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hAesDec : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D CryptoVerification.E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hclosure : subroutine_ok
      (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 462) (withLsCodeLoaded lsmpl logClosurePlacedSpec)) :
    region_ok
      (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTight W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)).withVRegs :=
  recordDecrypt_placed_region_vregs_ok_TPTight
    W.C CryptoVerification.E2E.HooksE.A0 ctl (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Slots.cliExternsPlaced_shim_sat mmpl gh W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_realloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (tryDecryptV1_placed_ok_PTight_cli mmpl gh W ctl hG hAesDec hSpqr)
    hclosure

private theorem rdp_region_reaches_full_placed_TPTight [LibsignalFullPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((Decrypt.blkPC_434).rebase (Decrypt.blkPl_434).base H) (lsmpl.base 434)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTPTightAt
        C A ctl uuidTryParse S)) :
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = recEntryPlaced →
      s0.status = .Running →
      (s0.mem ⊨ (withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S)).pre x s0 ∗ R) →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S))
        recExitPlaced x R s0 s0 := by
  have _ := CryptoVerification.CliRatchet.DecPlaced.instIsLsBlockProg_463 H
  have _ := CryptoVerification.LibsignalTripleRatchet.Decrypt.instIsLsBlockProg_434 H
  have hchainClone :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chain_clone_placed_ok
          hshim halloc hmemcpy hpanic))
  have hsenderClone :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.senderChain_clone_placed_ok
          hshim halloc hmemcpy hpanic))
  have hdrop1 :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (FromRecordCallees.drop_session_structure_local1_placed_ok hdealloc)
  have hdropLocal2 :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure_local2_placed_ok hdealloc)
  have hsetState :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (FromRecordCallees.set_session_state_placed_ok hmemcpy
        (FromRecordCallees.drop_session_structure_local1_placed_ok hdealloc))
  have hgrowSpe :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
      (FromRecordCallees.grow_one_spe_placed_ok hshim halloc hrealloc hpanic)
  have htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (rdpTryPlacedSpecTrap C A ctl uuidTryParse S)) :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H) (j := 434)
      (subroutine_ok_withLsCodeLoaded_of_plain (rdp_tryDecryptSpecTPTightAt_eq C A ctl uuidTryParse S ▸ hTry))
  intro x R s0 hpc hst hpre0 hL
  have ⟨hFroz0, hpre⟩ := extract_withLsFrozen hpre0
  obtain ⟨S', hmod, hpan_imp⟩ := rdp_spec_S_exists_placed C S x
  dsimp only [recordDecryptPlacedSpecTPTight, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.recordDecryptPlacedSpecTPTightF, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT.recordDecryptPlacedSpecTF] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  have hpre' : s0.mem ⊨
      (recordDecryptPlacedSpecP C A ctl uuidTryParse S').pre x s0 ∗
      (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) := by
    change s0.mem ⊨
      (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0 ∗
      (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R)
    have heq :
        (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0) ∗ R =
        (recordDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0 ∗
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) := by ac_rfl
    exact heq ▸ hpre
  have hstk := rootStack_le_of_recordPlacedPreP hpre'
  have hJ : ∀ s,
      JStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S))
        recExitPlaced x R s0 s := by
    intro s hs hLs
    rw [← rdp_JStatePlaced_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hout⟩ :=
      segExit_placed_ok (C := C) (A := A) (ctl := ctl) (S := S') (H := H)
        hdealloc x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s hs hLs
    exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  have hF : ∀ s,
      FStatePlaced C A ctl uuidTryParse S x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S))
        recExitPlaced x R s0 s := by
    intro s hs hLs
    rw [← rdp_FStatePlaced_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hnext⟩ :=
      segTail_placed_ok (C := C) (A := A) (ctl := ctl) (S := S') (H := H)
        hshim halloc hpanic hdropLocal2
        x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 s hs hLs
    rcases hnext with hj | hout
    · rw [rdp_JStatePlaced_eq_of_model_eq hmod] at hj
      exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    segClone_placed_ok_P (C := C) (A := A) (ctl := ctl) (S := S')
      hshim halloc hdealloc hmemcpy hpanic hchainClone hsenderClone hdrop1
      x (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ R) s0 hpc hst hpre' hL
  have hFroz' := libsignalFrozen_of_keepsFrozen hFroz0 hst'.keepsFrozen
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ :=
      rdp_segDecrypt_full_placed_ok_TPTight hmemcpy htd
        hsetState hdropLocal2 hgrowSpe x G₁ R s0 s' hQ hv hstk hFroz' (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ :=
      segMismatch_full_placed_ok (C := C) (A := A) (ctl := ctl) (S := S') (H := H)
        hgrowSpe hm hFroz' (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · rw [rdp_FStatePlaced_eq_of_model_eq hmod] at hf
      exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩
  · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_placed hmod hpan_imp hout⟩

/-- Parametric `[LibsignalFullPlacement]` `region_ok` for
`withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight ...)` on Block `463` (`0` `hclosure` premise). -/
theorem recordDecrypt_full_placed_region_ok_TPTight [LibsignalFullPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((Decrypt.blkPC_434).rebase (Decrypt.blkPl_434).base H) (lsmpl.base 434)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTPTightAt
        C A ctl uuidTryParse S)) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S)) :=
  CryptoVerification.LibsignalTripleRatchet.Record.region_ok_of_reaches
    (rdp_region_reaches_full_placed_TPTight C A ctl S H hshim halloc hrealloc hdealloc hmemcpy hpanic hTry)

/-- Parametric `[LibsignalFullPlacement]` `region_ok` with `Spec.withVRegs` on Block `463`
(`0` `hclosure` premise). -/
theorem recordDecrypt_full_placed_region_vregs_ok_TPTight [LibsignalFullPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTry : subroutine_ok ((Decrypt.blkPC_434).rebase (Decrypt.blkPl_434).base H) (lsmpl.base 434)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTPTightAt
        C A ctl uuidTryParse S)) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight C A ctl uuidTryParse S)).withVRegs := by
  intro x R s0 hpc hst hpre hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', hvregs, hpost⟩ | hpan⟩ :=
    rdp_region_reaches_full_placed_TPTight C A ctl S H hshim halloc hrealloc hdealloc hmemcpy hpanic hTry
      x R s0 hpc hst hpre hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', ?_⟩⟩
    dsimp only [Spec.withVRegs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvregs, hpost⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Concrete `[LibsignalFullPlacement]` CLI `region_ok` with `Spec.withVRegs` on
`lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))` at `S := spqrV1 W.C.F W.Q.K`
(`0` `hclosure` premise). -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_full_placed_region_vregs_ok_PTight_cli
    [LibsignalFullPlacement] (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks)
    (W : CliHooks) (ctl : BitVec 64)
    (hG : Slots.CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hAesDec : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D CryptoVerification.E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W) :
    region_ok
      (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      (withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K))).withVRegs :=
  recordDecrypt_full_placed_region_vregs_ok_TPTight
    W.C CryptoVerification.E2E.HooksE.A0 ctl (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K)
    (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
    (Slots.cliExternsPlaced_shim_sat mmpl gh W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_realloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (tryDecryptV1_placed_ok_PTight_cli mmpl gh W ctl hG hAesDec hSpqr)

end CryptoVerification.Cli.LibsignalSpqrV1.M4
