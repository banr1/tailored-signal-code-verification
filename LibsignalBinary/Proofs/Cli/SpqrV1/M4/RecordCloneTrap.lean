/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordClonePV1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneAssemble
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChains
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeys
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import ProofLib.RegChain

/-!
# Allocator-Only `SegClone` under `recordDecryptSpecP`

Specializes `segClone_ok_ext_P` to depend only on `AllocContracts img.base A ext` rather than
`Stage2Contracts` (which carries `ctl`), enabling reuse on `trTrapProgAt img.base C abs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem rct_setWidth_64_truncate_32 (w : BitVec 32) :
    (w.setWidth 64).truncate 32 = w := by bv_kernel

private theorem rct_segClone_fields_5_to_9 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hchainClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v00 v08 v18 v30 : BitVec 64} {v14 v24 v28 v2c v3c : BitVec 32}
    {w288 w28c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.st.receiverChains = []
      then (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x544#64
      else (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x300#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = x.st.sessionVersion.setWidth 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.st.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
      (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32)
      (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32)
      (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x594#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' →
      s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = w288.setWidth 64 →
      s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = w28c.setWidth 64 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = pendCap' →
      s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = chainsPtr' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      chains'.length = x.st.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.st.receiverChains.length →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecAt A 104 8 (chainAt A) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
            (x.G.chains.zip x.st.receiverChains) ∗
          vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
          vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
          optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
          ((s.sp + 0x288#64) ↦₃₂ w288) ∗
          ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
          OptPendClone A x.G.pending pendCap' pendPtr' ∗
          OptKybClone A x.G.kyber kybCap' kybPtr' ∗
          (s.sp ↦₆₄ kybPtr') ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗
          ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          ((s.sp + 0x30#64) ↦₆₄ chainsCap') ∗
          ((s.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecAt A 104 8 (chainAt A) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
        vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
        optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗
        ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        (s.sp ↦₆₄ v00) ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗
        ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗
        ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  rw [segClone_vecAt_0x180_chains_eq A s.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains hchains_len]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
            vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
            memRegion (s.sp + 0x5f0#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            (((s.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗
              ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
              vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
              ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s.sp ↦₆₄ v00) ∗ ((s.sp + 0x08#64) ↦₆₄ v08) ∗
              ((s.sp + 0x14#64) ↦₃₂ v14) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗
              ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗
              ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₆₄ v30) ∗
              ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_receiverChains hA hchainClone x R s0 s ret Q _
    hpc hrun hsp hx26 htr hchains_len
    fun s1 chainsCap' chainsPtr' chains' hchains_l hchains_c hpc1 hrun1 hsp1 hspA1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
  rw [← hsp1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            optTailVecAt A 48 (s1.sp + 0x230#64) x.G.pending ∗
            ((s1.sp + 0x08#64) ↦₆₄ v08) ∗
            ((s1.sp + 0x18#64) ↦₆₄ v18) ∗
            ((s1.sp + 0x24#64) ↦₃₂ v24) ∗
            ((s1.sp + 0x28#64) ↦₃₂ v28) ∗
            ((s1.sp + 0x2c#64) ↦₃₂ v2c) ∗
            stackAt s1.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s1.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s1.sp + 0x198#64) ∗
              vecU8At A (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A 32 (s1.sp + 0x260#64) x.G.kyber ∗
              ((s1.sp + 0x288#64) ↦₃₂ w288) ∗ ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s1.sp ↦₆₄ v00) ∗ ((s1.sp + 0x14#64) ↦₃₂ v14) ∗
              ((s1.sp + 0x30#64) ↦₆₄ v30) ∗ ((s1.sp + 0x3c#64) ↦₃₂ v3c) ∗
              memRegion (s1.sp + 0x5f0#64) 104 ∗
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecAt_0x180_chains_eq A s1.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains hchains_len,
            stackAt_chainClone_eq_alloc s1.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_pendingPreKey hA hpc1 hrun1 hspA1 htr1
    fun s2 pendCap' pendPtr' v08' v24' v28' v2c' hpc2 hrun2 hsp2 hspA2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
  rw [← hsp2]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            optTailVecAt A 32 (s2.sp + 0x260#64) x.G.kyber ∗
            (s2.sp ↦₆₄ v00) ∗
            ((s2.sp + 0x14#64) ↦₃₂ v14) ∗
            ((s2.sp + 0x3c#64) ↦₃₂ v3c) ∗
            stackAt s2.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              optTailVecAt A 48 (s2.sp + 0x230#64) x.G.pending ∗
              OptPendClone A x.G.pending pendCap' pendPtr' ∗
              vecGhostAt A x.G.alice (s2.sp + 0x198#64) ∗
              vecU8At A (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              ((s2.sp + 0x288#64) ↦₃₂ w288) ∗ ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
              ((s2.sp + 0x08#64) ↦₆₄ v08') ∗ ((s2.sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((s2.sp + 0x24#64) ↦₃₂ v24') ∗ ((s2.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s2.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s2.sp + 0x30#64) ↦₆₄ v30) ∗
              memRegion (s2.sp + 0x5f0#64) 104 ∗
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_pendingKyber hA hpc2 hrun2 hspA2 htr2
    fun s3 kybCap' kybPtr' v14' hpc3 hrun3 hsp3 hspA3 hx19_3 hx22_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 htr3 => ?_
  have hx25_2' : (s2.readReg64 .x25).truncate 32 = x.st.sessionVersion := by
    rw [hx25_2, hx25_1, hx25, rct_setWidth_64_truncate_32]
  rw [hx25_2', ← hsp3]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecGhostAt A x.G.alice (s3.sp + 0x198#64) ∗
            ((s3.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗
            ((s3.sp + 0x30#64) ↦₆₄ v30) ∗
            stackAt s3.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              optTailVecAt A 48 (s3.sp + 0x230#64) x.G.pending ∗
              OptPendClone A x.G.pending pendCap' pendPtr' ∗
              optTailVecAt A 32 (s3.sp + 0x260#64) x.G.kyber ∗
              OptKybClone A x.G.kyber kybCap' kybPtr' ∗
              vecU8At A (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              (s3.sp ↦₆₄ kybPtr') ∗ ((s3.sp + 0x08#64) ↦₆₄ v08') ∗
              ((s3.sp + 0x14#64) ↦₃₂ v14') ∗ ((s3.sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((s3.sp + 0x24#64) ↦₃₂ v24') ∗ ((s3.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s3.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s3.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
              memRegion (s3.sp + 0x5f0#64) 104 ∗
              memRegion (s3.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_aliceBaseKey hA hpc3 hrun3 hspA3 htr3
    fun s4 alice' hpc4 hrun4 hsp4 hspA4 hx19_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4 halice_b halice_c => ?_
  have hx26_3' : s3.readReg64 .x26 = chainsCap' := by reg_chain
  rw [hx26_3', ← hsp4]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecU8At A (s4.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            stackAt s4.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s4.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s4.sp + 0x198#64) ∗
              optTailVecAt A 48 (s4.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s4.sp + 0x260#64) x.G.kyber ∗
              ((s4.sp + 0x288#64) ↦₃₂ w288) ∗ ((s4.sp + 0x28c#64) ↦₃₂ w28c) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
              OptPendClone A x.G.pending pendCap' pendPtr' ∗
              OptKybClone A x.G.kyber kybCap' kybPtr' ∗
              (s4.sp ↦₆₄ kybPtr') ∗ ((s4.sp + 0x08#64) ↦₆₄ v08') ∗
              ((s4.sp + 0x14#64) ↦₃₂ v14') ∗ ((s4.sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((s4.sp + 0x24#64) ↦₃₂ v24') ∗ ((s4.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s4.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s4.sp + 0x30#64) ↦₆₄ chainsCap') ∗
              ((s4.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
              memRegion (s4.sp + 0x5f0#64) 104 ∗
              memRegion (s4.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  have hx24_4' : s4.readReg64 .x24 = s4.sp + 0xca0#64 := by reg_chain
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_pqRatchet hA hpc4 hrun4 hspA4 hx24_4' htr4
    fun s5 pqCap' pqPtr' hpc5 hrun5 hsp5 hspA5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5 htr5 hpq_c => ?_
  have hsp_eq : s4.sp = s.sp := by reg_chain
  rw [hsp_eq] at hx24_5 ⊢
  refine SepWPp.weaken_pre
    (by rw [stackAt_chainClone_eq_alloc s.sp]; exact Entails.of_eq (by ac_rfl))
    (hnext s5 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr'
      hpc5 hrun5 (by reg_chain) hspA5
      (by reg_chain) hx20_5 (by reg_chain) hx22_5 (by reg_chain) hx24_5
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
      htr5 hchains_l hchains_c halice_b halice_c hpq_c)

set_option linter.unusedVariables false in
private def rct_clonePost (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : RecordDecryptGhost) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ sf.spAligned = true ∧
    sf.readReg64 .x29 = s0.readReg64 .x29 ∧
    (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
    sf.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
    (P_f ⊢ ∃∗ G₁ : SessionGhost,
      ⌜CloneRel x.G G₁⌝ ∗
      recFrame A img x s0.sp ∗
      sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗
      sessionStateAt A (s0.sp + 0xca0#64) G₁ x.st ∗
      errsAt A (s0.sp + 0x5d8#64) [] ∗
      memRegion (s0.sp + 0x4b0#64) 48 ∗
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest)

private theorem rct_segClone_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hchainClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt img.base A ext)
    (hsenderClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1a8#64)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (h27 : s0.readReg64 .x27 = x.sret) (h19 : s0.readReg64 .x19 = x.remA)
    (h23 : s0.readReg64 .x23 = s0.sp + 0x5f0#64) (h24 : s0.readReg64 .x24 = s0.sp + 0xca0#64)
    (hrc32 : x.st.receiverChains.length < 2 ^ 32) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (if x.st.version.toNat = x.msg.messageVersion.toNat then
         (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x69c#64
       else
         (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x7e4#64)
      s0
      (memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗
        memRegion (s0.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool)
      (rct_clonePost A ctl img x s0)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hrc_lt : x.st.receiverChains.length < 2 ^ 63 := by omega
  rw [segClone_sessionStateAt_0x138_eq A s0.sp x.G x.st]
  refine SepWPp.weaken_pre
    (P' := ⌜PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey ∧
            (match x.st.remoteIdentity with
             | none => x.G.remoteIk.bytes = []
             | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey) ∧
            x.G.chains.length = x.st.receiverChains.length ∧
            x.G.pending.isSome = x.st.pendingPreKey ∧ x.G.regIds.length = 8 ∧
            x.G.localIk.bytes.length = 33 ∧
            (x.st.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)⌝ ∗
          (memRegion s0.sp 0xa0 ∗
            ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
            vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗
            vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗
            vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗
            optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦ₛ x.G.regIds) ∗
            memRegion (s0.sp + 0x4b0#64) 0x950 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  obtain ⟨w288, w28c, _, h_reg_pts⟩ := exists_unpack32_pair_of_length_8 h_reg_len
  have h28c : s0.sp + 0x288#64 + 4#64 = s0.sp + 0x28c#64 := by bv_arith
  rw [h_reg_pts (s0.sp + 0x288#64), h28c]
  refine SepWPp.weaken_pre
    (P' := memRegion s0.sp 0xa0 ∗
            ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
            vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗
            memRegion (s0.sp + 0x4b0#64) 0x950 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗
            (A.pool ∗
              vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
              vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗
              vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
              ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              ((s0.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s0.sp + 0x28c#64) ↦₃₂ w28c)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_entry_combined hpc hrun hsp h19 h27 h23 h24 ⟨rfl, rfl⟩
    fun s1 sv dv bq0 bq1 bq2 bq3 bq4 bq5 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1 => ?_
  rw [← hsp1] at hx23_1 hx24_1 ⊢
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecGhostAt A x.G.localIk (s1.sp + 0x138#64) ∗
            vecGhostAt A x.G.remoteIk (s1.sp + 0x150#64) ∗
            vecU8At A (s1.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            optSenderChainAt A (s1.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            chunks96_6QAt (s1.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s1.sp + 0x5f0#64) 104 ∗
            ((s1.sp + 0x40#64) ↦₆₄ sv.v40) ∗
            ((s1.sp + 0x48#64) ↦₆₄ sv.v48) ∗
            ((s1.sp + 0x54#64) ↦₃₂ sv.v54) ∗
            ((s1.sp + 0x58#64) ↦₆₄ sv.v58) ∗
            ((s1.sp + 0x60#64) ↦₆₄ sv.v60) ∗
            ((s1.sp + 0x68#64) ↦₆₄ sv.v68) ∗
            ((s1.sp + 0x70#64) ↦₆₄ sv.v70) ∗
            ((s1.sp + 0x78#64) ↦₆₄ sv.v78) ∗
            ((s1.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s1.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            ((s1.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            stackAt s1.sp chainCloneStack ∗
            (((s1.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗
              ((s1.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s1.sp + 0x198#64) ∗
              vecU8At A (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A 48 (s1.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s1.sp + 0x260#64) x.G.kyber ∗
              ((s1.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s1.sp ↦₆₄ sv.v00) ∗
              ((s1.sp + 0x08#64) ↦₆₄ sv.v08) ∗
              ((s1.sp + 0x14#64) ↦₃₂ sv.v14) ∗
              ((s1.sp + 0x18#64) ↦₆₄ sv.v18) ∗
              ((s1.sp + 0x24#64) ↦₃₂ sv.v24) ∗
              ((s1.sp + 0x28#64) ↦₃₂ sv.v28) ∗
              ((s1.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
              ((s1.sp + 0x30#64) ↦₆₄ sv.v30) ∗
              ((s1.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
              memRegion (s1.sp + 0x10#64) 4 ∗
              memRegion (s1.sp + 0x20#64) 4 ∗
              memRegion (s1.sp + 0x38#64) 4 ∗
              memRegion (s1.sp + 0x50#64) 4 ∗
              dstSlotsAt s1.sp dv ∗
              ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
              CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x s1.sp))
    (by unfold spillSlotsAt
        rw [segClone_vecAt_0x180_chains_eq A s1.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains h_chains_len,
            stackAt_chainClone_eq_alloc s1.sp]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fields_1_to_4 hA hsenderClone hpc1 hrun1 hspA1 hx23_1 htr1 hrc_lt
    fun s2 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc2 hrun2 hsp2 hspA2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 htr2
      hloc_b hloc_c hrem_b hrem_c hinl => ?_
  rw [← hsp2] at hx23_2 ⊢
  have hx24_2' : s2.readReg64 .x24 = s2.sp + 0xca0#64 := by reg_chain
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecAt A 104 8 (chainAt A) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s2.sp + 0x198#64) ∗
            vecU8At A (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optTailVecAt A 48 (s2.sp + 0x230#64) x.G.pending ∗
            optTailVecAt A 32 (s2.sp + 0x260#64) x.G.kyber ∗
            ((s2.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
            (s2.sp ↦₆₄ sv.v00) ∗
            ((s2.sp + 0x08#64) ↦₆₄ sv.v08) ∗
            ((s2.sp + 0x14#64) ↦₃₂ sv.v14) ∗
            ((s2.sp + 0x18#64) ↦₆₄ sv.v18) ∗
            ((s2.sp + 0x24#64) ↦₃₂ sv.v24) ∗
            ((s2.sp + 0x28#64) ↦₃₂ sv.v28) ∗
            ((s2.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
            ((s2.sp + 0x30#64) ↦₆₄ sv.v30) ∗
            ((s2.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
            memRegion (s2.sp + 0x5f0#64) 104 ∗
            stackAt s2.sp chainCloneStack ∗
            (vecGhostAt A x.G.localIk (s2.sp + 0x138#64) ∗
              vecGhostAt A x.G.remoteIk (s2.sp + 0x150#64) ∗
              vecU8At A (s2.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A (s2.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              optSenderChainHeap A sender' x.st.senderChain ∗
              chunks96_6QAt (s2.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((s2.sp + 0x40#64) ↦₆₄ scCap') ∗
              ((s2.sp + 0x48#64) ↦₆₄ rootPtr') ∗
              ((s2.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
              ((s2.sp + 0x58#64) ↦₆₄ 32#64) ∗
              ((s2.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
              ((s2.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
              ((s2.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗
              ((s2.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
              ((s2.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s2.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s2.sp + 0x10#64) 4 ∗
              memRegion (s2.sp + 0x20#64) 4 ∗
              memRegion (s2.sp + 0x38#64) 4 ∗
              memRegion (s2.sp + 0x50#64) 4 ∗
              dstSlotsAt s2.sp dv ∗
              ((s2.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
              CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x s2.sp))
    (by rw [segClone_vecAt_0x180_chains_eq A s2.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains h_chains_len]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine rct_segClone_fields_5_to_9 hA hchainClone hpc2 hrun2 hspA2 hx24_2' hx25_2 hx26_2 htr2 h_chains_len
    fun s3 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr'
      hpc3 hrun3 hsp3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 htr3
      hchains_l hchains_c halice_b halice_c hpq_c => ?_
  rw [← hsp3] at hx24_3 ⊢
  refine SepWPp.weaken_pre
    (P' := dstSlotsAt s3.sp dv ∗
            chunks96_6QAt (s3.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            spillSlotsAt s3.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
              scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
              localIk'.ptr localIk'.cap ∗
            ((s3.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            (A.pool ∗
              vecGhostAt A x.G.localIk (s3.sp + 0x138#64) ∗
              vecGhostAt A x.G.remoteIk (s3.sp + 0x150#64) ∗
              vecU8At A (s3.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              vecAt A 104 8 (chainAt A) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s3.sp + 0x198#64) ∗
              vecU8At A (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optSenderChainAt A (s3.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              optTailVecAt A 48 (s3.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s3.sp + 0x260#64) x.G.kyber ∗
              ((s3.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s3.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              ((s3.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
              vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
              optSenderChainHeap A sender' x.st.senderChain ∗
              OptPendClone A x.G.pending pendCap' pendPtr' ∗
              OptKybClone A x.G.kyber kybCap' kybPtr' ∗
              memRegion (s3.sp + 0x5f0#64) 104 ∗
              stackAt s3.sp chainCloneStack ∗
              CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x s3.sp))
    (by unfold spillSlotsAt; exact Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fields_10_to_11 dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08' v14' pendCap' pendPtr'
    v24' v28' v2c' w288 w28c _
    hpc3 hrun3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3
    fun s4 hpc4 hrun4 hsp4 hspA4 hx9_4 hx29_4 htr4 => ?_
  have hsp_eq : s3.sp = s0.sp := by reg_chain
  rw [hsp_eq]
  refine SepWPp.done hpc4 hrun4
    ⟨by reg_chain, hspA4, by reg_chain, htr4, hx9_4, ?_⟩
  have hdst :=
    segClone_dstSlotsWrittenAt_entails_sessionStateAt A s0.sp x localIk' remoteIk' rootPtr'
      chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap'
      sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24'
      kybCap' kybPtr' v14' w288 w28c
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
      hloc_b hloc_c hrem_b hrem_c hchains_l hchains_c halice_b halice_c hpq_c hinl
  have hsrc :=
    segClone_srcSessionState_reassemble A s0.sp x w288 w28c
      h_loc_deser h_rem_deser h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
  have hrest :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest_reassemble A ctl img x s0.sp sq0 sq1 sq2 sq3 sq4 sq5
      kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
      scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
      localIk'.ptr localIk'.cap
  rw [stackAt_chainClone_eq_alloc s0.sp]
  refine Entails.trans
    (Q := (segClone_dstSlotsWrittenAt s0.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
              pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24'
              kybCap' kybPtr' v14' x.st.sessionVersion x.st.previousCounter w288 w28c ∗
            vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
            vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
            vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
            vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
            vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
            optSenderChainHeap A sender' x.st.senderChain ∗
            OptPendClone A x.G.pending pendCap' pendPtr' ∗
            OptKybClone A x.G.kyber kybCap' kybPtr') ∗
          (vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗
            vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗
            vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗
            optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s0.sp + 0x28c#64) ↦₃₂ w28c)) ∗
          (spillSlotsAt s0.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
              scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
              localIk'.ptr localIk'.cap ∗
            chunks96_6QAt (s0.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            memRegion (s0.sp + 0x5f0#64) 104 ∗
            ((s0.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            memRegion (s0.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
            stackAt s0.sp allocHookStack ∗ A.pool ∗
            CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x s0.sp))
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hdst (sepConj_mono hsrc hrest)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G₁
  refine Entails.sepExists_right G₁ ?_
  exact Entails.of_eq (by ac_rfl)

/-- `segClone_ok_ext_P` specialized to `AllocContracts` (no `Stage2Contracts` dependency). -/
theorem segClone_ok_alloc_P
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hchainClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt img.base A ext)
    (hsenderClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s0.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s0 s' ∧
      ((∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ R s0 s') ∨
       (∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s') ∨
       regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img)
         (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s') := by
  have hentry_eq :
      entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
        (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName :=
    entryOf_eq_tripleRatchetProgAtExt ext hloads CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
  have hpc' : s0.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1a8#64 := by
    simpa [CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry, hentry_eq] using hpc
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hF, hsym⟩, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hsp, h27, h19, h23, h24, hrem_or_dist, hseeds, hrc32, _⟩, hm⟩ := hpre
  have hwp :=
    rct_segClone_wp (C := C) (ctl := ctl) (S := S)
      hA hchainClone hsenderClone x R s0
      hpc' hrun hsp h27 h19 h23 h24 hrc32
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hspf, hspAf, hx29f, ⟨htrf, hvrf⟩, hx9f, hent⟩ |
      ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · have hmeta : recMeta img s0 sf :=
      ⟨hrunf, hspf, hspAf, hx29f, htrf, hF.of_keepsFrozen hsteps.keepsFrozen,
        hsteps.symtab_eq.trans hsym, hvrf⟩
    have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf'
    obtain ⟨G₁, hmf'⟩ := hmf'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf'
    obtain ⟨hclone, hmf'⟩ := hmf'
    simp only [sepConj_assoc] at hmf'
    by_cases hver : x.st.version.toNat = x.msg.messageVersion.toNat
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcV : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recVPC img := by
        simpa [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recVPC, hentry_eq] using hpcf
      refine ⟨sf, hsteps, Or.inl ⟨G₁, hpcV, hmeta, ⟨hrem_or_dist, hseeds, hrc32⟩, hclone, hver, ?_⟩⟩
      simpa only [sepConj_assoc] using hmf'
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcM : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recMPC img := by
        simpa [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recMPC, hentry_eq] using hpcf
      refine ⟨sf, hsteps, Or.inr (Or.inl ⟨G₁, hpcM, hmeta, hver, hx9f, ?_⟩)⟩
      simpa only [sepConj_assoc] using hmf'
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.Cli.LibsignalSpqrV1.M4
