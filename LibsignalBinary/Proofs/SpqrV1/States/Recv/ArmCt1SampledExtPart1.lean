/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1

/-!
# `<States>::recv` — `.ct1Sampled` Arm (`AllocContractsX`, Part 1)

**Checked by Lean.** Extended-stack (`statesRecvStackXExt` = `40176` B,
`statesRecvCalleeStackXExt` = `35936` B) wrappers for `ct1Sampled_epilogue_19324`,
`ct1Sampled_prologue`, and `ct1Sampled_drop_epochOutOfRange`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop

/-- Extended-stack (`40176` B) shared direct epilogue at `+19324` (`0x59fd0 -> 0x59ff0`). -/
theorem ct1Sampled_epilogue_19324_ext
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ Rest ∗ stackAt s0.sp statesRecvStackXExt) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hpre :
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest ⊢
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        (memRegion (s0.sp - 40176#64) 16384 ∗ Rest) := by
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_19324 s0 s1 (memRegion (s0.sp - 40176#64) 16384 ∗ Rest)
      hsp0_align hpc1 hrun1 hsp1 htr1) ?_
  intro sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩
  refine ⟨Entails.trans hPf ?_, hspf, hcsf, htrf⟩
  rw [stackAt_statesRecvStackXExt_eq_X s0.sp]
  exact Entails.of_eq (by ac_rfl)

/-- Extended-stack (`40176` B) prologue of `States::recv` (`+0 -> +36`, `0x55454 -> 0x55478`). -/
theorem ct1Sampled_prologue_ext
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc0 : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
    (hrun0 : s0.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36#64)
      s0
      (stackAt s0.sp statesRecvStackXExt ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗
          Rest) ∧
        s1.sp = s0.sp - 4240#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        TraceCalleeSaved s1 s0) := by
  have hpre :
      stackAt s0.sp statesRecvStackXExt ∗ Rest ⊢
      stackAt s0.sp statesRecvStackX ∗ (memRegion (s0.sp - 40176#64) 16384 ∗ Rest) := by
    rw [stackAt_statesRecvStackXExt_eq_X s0.sp]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  refine SepWP.mono
    (ct1Sampled_prologue s0 (memRegion (s0.sp - 40176#64) 16384 ∗ Rest) hsp0_align hpc0 hrun0) ?_
  intro s1 P1 _ _ ⟨hP1, hsp1, hx0, hx1, hx2, hx3, hx29, htr⟩
  refine ⟨Entails.trans hP1 ?_, hsp1, hx0, hx1, hx2, hx3, hx29, htr⟩
  rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
  exact Entails.of_eq (by ac_rfl)

/-- Extended-stack (`40176` B) `EpochOutOfRange` tail (`+1564 -> s0.x30`, `0x55a70 -> 0x55b58`). -/
theorem ct1Sampled_drop_epochOutOfRange_ext
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s3 : State) (outA selfA msg_ep : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1564#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 4240#64)
    (hx1 : s3.readReg64 .x1 = selfA)
    (hx19 : s3.readReg64 .x19 = outA)
    (hx20 : s3.readReg64 .x20 = msg_ep)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s3
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ct1Sampled st) ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          memRegion selfA chunkedStatesSize ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackXExt ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hpre :
      memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ct1Sampled st) ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackXExt ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest ⊢
      memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ct1Sampled st) ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        (memRegion (s0.sp - 40176#64) 16384 ∗ Rest) := by
    rw [stackAt_statesRecvCalleeExt_eq_X s0.sp]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  refine SepWP.mono
    (ct1Sampled_drop_epochOutOfRange hdealloc s0 s3 outA selfA msg_ep st
      (memRegion (s0.sp - 40176#64) 16384 ∗ Rest)
      hsp0_align hpc3 hrun3 hsp3 hx1 hx19 hx20 htr3) ?_
  intro sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩
  refine ⟨Entails.trans hPf ?_, hspf, hcsf, htrf⟩
  rw [stackAt_statesRecvStackXExt_eq_X s0.sp]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.Recv
