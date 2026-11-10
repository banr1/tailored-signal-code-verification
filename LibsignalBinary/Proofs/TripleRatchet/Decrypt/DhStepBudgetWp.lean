/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepMain
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepTightTargets
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import ProofLib.ProgramReflection -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain

/-!
# `VmPreserved` Basic-Block `SepWP` Bundle for `DhStep`

Defines `DhStepBlockVmWp` and proves `dhStepBlockVmWp_159` (block `130`) and `dhStepBlockVmWp_549`
(block `433`) via `sepWP_seg_ls_vm` and `hooksException`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement LibsignalRoLoaded lsmpl)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (invalidSessionStructureStr speWord)
open CryptoVerification.LibsignalTripleRatchet (TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkLib_131 blkLib_434 blkLib_eq_131 blkLib_eq_434 blkPC_131 blkPC_434 blkPl_131 blkPl_434
  speTag
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep (
  DhStepBlockWp clamp_byte0 clamp_byte31 dhStepBlockWp_159 dhStepBlockWp_549
  reassoc_4_8_8_to_8_8_4
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open scoped ProofLib.ProgramReflection
open VerifiedLibraries.RustStd (checkBlockNoSvc0)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Bundle of relocatable basic-block `SepWP` obligations for `DhStep` (`+0x500 → +0x8ac / +0x30c`). -/
structure DhStepBlockVmWp [LibsignalPlacement] (prog : Program)
    (entry rngFillEntry : BitVec 64) where
  missingScAddr : BitVec 64
  hro_missingSc : ∀ {m : Memory} {P : SepProp},
    LibsignalRoLoaded lsmpl m → (m ⊨ P) → (m ⊨ (missingScAddr ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗ P)
  wpp_2dc_to_30c :
    ∀ (s0 s : State) (w2c0 w2c8 : BitVec 64)
      (u34c u344 u338 u330 u2b8 u2b0 u180 u178 u170 u168 : BitVec 64)
      (u340 u2d0 u18c u188 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x2dc#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x12 = sp + 0x2c0#64 →
      s.readReg64 .x20 = sp + 0x140#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 780#64) s
        ((memRegion (sp + 0x140#64) 0x28 ∗ (sp + 0x168#64) ↦₆₄ u168 ∗ (sp + 0x170#64) ↦₆₄ u170 ∗
          (sp + 0x178#64) ↦₆₄ u178 ∗ (sp + 0x180#64) ↦₆₄ u180 ∗ (sp + 0x188#64) ↦₃₂ u188 ∗
          (sp + 0x18c#64) ↦₃₂ u18c ∗ memRegion (sp + 0x190#64) 0x120 ∗ (sp + 0x2b0#64) ↦₆₄ u2b0 ∗
          (sp + 0x2b8#64) ↦₆₄ u2b8) ∗ (sp + 0x2c0#64) ↦₆₄ w2c0 ∗ (sp + 0x2c8#64) ↦₆₄ w2c8 ∗
         ((sp + 0x2d0#64) ↦₃₂ u2d0 ∗ memRegion (sp + 0x2d4#64) 0x5c ∗ (sp + 0x330#64) ↦₆₄ u330 ∗
          (sp + 0x338#64) ↦₆₄ u338 ∗ (sp + 0x340#64) ↦₃₂ u340 ∗ (sp + 0x344#64) ↦₆₄ u344 ∗
          (sp + 0x34c#64) ↦₆₄ u34c ∗ memRegion (sp + 0x354#64) 0x22c))
        (fun sf P_f => VmPreserved s sf ∧
          sf.sp = sp ∧ sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = sp + 0x140#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_f ∗ R) →
            (m ⊨ (memRegion (sp + 0x140#64) 0x28 ∗ ((sp + 0x168#64) ↦₆₄ w2c0) ∗
                  ((sp + 0x170#64) ↦₆₄ w2c8) ∗ memRegion (sp + 0x178#64) 24 ∗
                  memRegion (sp + 0x190#64) 0x3f0) ∗ R)))
  wpp_7f8_to_2dc :
    ∀ (s0 s : State) (u508 u500 u2c8 u2c0 u2b8 u2b0 : BitVec 64) (u2d0 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x7f8#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 732#64) s
        (memRegion (sp + 0x140#64) 0x58 ∗ ((sp + 0x198#64) ↦₆₄ speWord 10) ∗
         memRegion (sp + 0x1a0#64) 0x110 ∗ ((sp + 0x2b0#64) ↦₆₄ u2b0) ∗
         ((sp + 0x2b8#64) ↦₆₄ u2b8) ∗ ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗
         ((sp + 0x2c8#64) ↦₆₄ u2c8) ∗ ((sp + 0x2d0#64) ↦₃₂ u2d0) ∗
         memRegion (sp + 0x2d4#64) 0x22c ∗ ((sp + 0x500#64) ↦₆₄ u500) ∗
         ((sp + 0x508#64) ↦₆₄ u508) ∗ memRegion (sp + 0x510#64) 0x70)
        (fun sm P_m => VmPreserved s sm ∧
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x12 = sp + 0x2c0#64 ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = sp + 0x140#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧ sm.readReg64 .x26 = speTag .invalidKeyAgreement ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ memRegion (sp + 0x140#64) 0x440 ∗ R)))
  wpp_missing_sc :
    ∀ (s0 s : State) (x : TryDecryptGhost) (u2c0 u2c8 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x500#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x12 = sp + 0x2c0#64 →
      s.readReg64 .x19 = x.ret → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = sp + 0x38#64 →
      s.readReg64 .x28 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 732#64) s
        (((sp + 0x50#64) ↦₃₂ 0#32) ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
         ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗
         ((sp + 0x30#64) ↦₆₄ x.remA) ∗ ((sp + 0x2c0#64) ↦₆₄ u2c0) ∗ ((sp + 0x2c8#64) ↦₆₄ u2c8))
        (fun sm P_m => VmPreserved s sm ∧
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x12 = sp + 0x2c0#64 ∧
          sm.readReg64 .x19 = x.ret ∧ sm.readReg64 .x20 = sp + 0x140#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧
          sm.readReg64 .x26 = speTag (.invalidSessionStructure .missingSenderChain) ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) →
            (m ⊨ (((sp + 0x50#64) ↦₃₂ 0#32) ∗ memRegion sp 0x38 ∗
                  ((sp + 0x2c0#64) ↦₆₄ missingScAddr) ∗ ((sp + 0x2c8#64) ↦₆₄ 20#64)) ∗ R)))
  wpp_cc1_err :
    ∀ (s0 s : State) (u1bc u1b4 u1a8 u1a0 : BitVec 64) (u1c4 u1b0 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1352#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 2040#64) s
        (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
         ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗ ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
         ((sp + 0x1c4#64) ↦₃₂ u1c4))
        (fun sm P_m => VmPreserved s sm ∧
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = sp + 0x140#64 ∧ sm.readReg64 .x23 = sp + 0x500#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧ sm.readReg64 .x26 = sp + 0x2c0#64 ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₃₂ 1#32) ∗ ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗
                  ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗ ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗
                  ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗ ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗
                  ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗ R)))
  wpp_cc1_ok :
    ∀ (s0 s : State),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1352#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      SepWP prog (entry + 1804#64) s ((sp + 0x190#64) ↦₃₂ 0#32)
        (fun sm P_m => VmPreserved s sm ∧
          sm.sp = sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ R)))
  wpp_pre_cc1 :
    ∀ (s0 s : State) (x : TryDecryptGhost)
      (p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x500#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x12 = sp + 0x2c0#64 →
      s.readReg64 .x19 = x.ret → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x21 = x.ss → s.readReg64 .x22 = x.msgA →
      s.readReg64 .x23 = sp + 0x500#64 → (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x27 = sp + 0x38#64 →
      s.readReg64 .x28 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (lsmpl.base 40) s
        (((sp + 0x50#64) ↦₃₂ 1#32) ∗
         ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
         ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3) ∗
         ((sp + 0xb8#64) ↦₆₄ k0) ∗ ((sp + 0xc0#64) ↦₆₄ k1) ∗
         ((sp + 0xc8#64) ↦₆₄ k2) ∗ ((sp + 0xd0#64) ↦₆₄ k3) ∗
         ((sp + 0x390#64) ↦₆₄ u390) ∗ ((sp + 0x398#64) ↦₆₄ u398) ∗
         ((sp + 0x3a0#64) ↦₆₄ u3a0) ∗ ((sp + 0x3a8#64) ↦₆₄ u3a8) ∗
         ((sp + 0x3b0#64) ↦₆₄ u3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u3b8) ∗
         ((sp + 0x3c0#64) ↦₆₄ u3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u3c8))
        (fun sc1 P_c1 => VmPreserved s sc1 ∧
          sc1.sp = sp ∧ sc1.readReg64 .x0 = sp + 0x3b0#64 ∧
          sc1.readReg64 .x1 = x.msgA + 56#64 ∧ sc1.readReg64 .x2 = sp + 0x390#64 ∧
          sc1.readReg64 .x8 = sp + 0x190#64 ∧ sc1.readReg64 .x19 = x.ret ∧
          sc1.readReg64 .x20 = sp + 0x140#64 ∧ sc1.readReg64 .x21 = x.ss ∧
          sc1.readReg64 .x22 = x.msgA ∧ sc1.readReg64 .x23 = sp + 0x500#64 ∧
          (sc1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
          sc1.readReg64 .x25 = sp + 0x190#64 ∧ sc1.readReg64 .x26 = sp + 0x2c0#64 ∧
          sc1.readReg64 .x27 = sp + 0x38#64 ∧ sc1.readReg64 .x28 = sp + 0x2c0#64 ∧
          sc1.readReg64 .x29 = s0.sp - 96#64 ∧ sc1.readReg64 .x30 = entry + 1352#64 ∧
          sc1.trace = s0.trace ∧ calleeSavedVRegs sc1 = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_c1 ∗ R) →
            (m ⊨ (((sp + 0x50#64) ↦₃₂ 1#32) ∗
                  ((sp + 0x74#64) ↦₆₄ p0) ∗ ((sp + 0x7c#64) ↦₆₄ p1) ∗
                  ((sp + 0x84#64) ↦₆₄ p2) ∗ ((sp + 0x8c#64) ↦₆₄ p3) ∗
                  ((sp + 0xb8#64) ↦₆₄ 0#64) ∗ ((sp + 0xc0#64) ↦₆₄ 0#64) ∗
                  ((sp + 0xc8#64) ↦₆₄ 0#64) ∗ ((sp + 0xd0#64) ↦₆₄ 0#64) ∗
                  ((sp + 0x390#64) ↦₆₄ p0) ∗ ((sp + 0x398#64) ↦₆₄ p1) ∗
                  ((sp + 0x3a0#64) ↦₆₄ p2) ∗ ((sp + 0x3a8#64) ↦₆₄ p3) ∗
                  ((sp + 0x3b0#64) ↦₆₄ k0) ∗ ((sp + 0x3b8#64) ↦₆₄ k1) ∗
                  ((sp + 0x3c0#64) ↦₆₄ k2) ∗ ((sp + 0x3c8#64) ↦₆₄ k3)) ∗ R)))
  wpp_cc2_ok :
    ∀ (s0 s : State),
      let sp := s0.sp - 1504#64
      s.pc = entry + 2008#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      SepWP prog (entry + 2220#64) s ((sp + 0x190#64) ↦₃₂ 0#32)
        (fun sm P_m => VmPreserved s sm ∧
          sm.sp = sp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_m ∗ R) → (m ⊨ ((sp + 0x190#64) ↦₃₂ 0#32) ∗ R)))
  wpp_cc2_err :
    ∀ (s0 s : State) (msgW : BitVec 32) (u1bc u1b4 u1a8 u1a0 : BitVec 64) (u1c4 u1b0 : BitVec 32),
      let sp := s0.sp - 1504#64
      s.pc = entry + 2008#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x20 = sp + 0x140#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = sp + 0x2c0#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 2040#64) s
        (((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
         ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
         ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
         ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗ ((sp + 0x1c4#64) ↦₃₂ u1c4))
        (fun sm P_m => VmPreserved s sm ∧
          sm.sp = sp ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = sp + 0x140#64 ∧ sm.readReg64 .x23 = sp + 0x500#64 ∧
          sm.readReg64 .x25 = sp + 0x190#64 ∧ sm.readReg64 .x26 = sp + 0x2c0#64 ∧
          sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P_m ∗ R) →
            (m ⊨ (((sp + 0x1c#64) ↦₃₂ msgW) ∗ ((sp + 0x190#64) ↦₃₂ 1#32) ∗
                  ((sp + 0x1a0#64) ↦₆₄ u1a0) ∗ ((sp + 0x1a8#64) ↦₆₄ u1a8) ∗
                  ((sp + 0x1b0#64) ↦₃₂ u1b0) ∗ ((sp + 0x1b4#64) ↦₆₄ u1b4) ∗
                  ((sp + 0x1bc#64) ↦₆₄ u1bc) ∗ ((sp + 0x1c4#64) ↦₃₂ u1c4)) ∗ R)))
  wpp_70c_to_778 :
    ∀ (s0 s : State)
      (r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510 : BitVec 32)
      (r1 r2 r3 c0 c1 c3 c4 u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448
       u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 0x70c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x23 = sp + 0x500#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readReg64 .x26 = sp + 0x2c0#64 →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 1912#64) s
        (((sp + 0x10#64) ↦₃₂ u10) ∗ ((sp + 0x1c#64) ↦₃₂ u1c) ∗
         ((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
         ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗ ((sp + 0x1b0#64) ↦₃₂ r4) ∗
         ((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗ ((sp + 0x1c4#64) ↦₃₂ c2) ∗
         ((sp + 0x1c8#64) ↦₆₄ c3) ∗ ((sp + 0x1d0#64) ↦₆₄ c4) ∗
         ((sp + 0x3d0#64) ↦₆₄ u3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u3d8) ∗ ((sp + 0x3e0#64) ↦₃₂ u3e0) ∗
         ((sp + 0x3e4#64) ↦₆₄ u3e4) ∗ ((sp + 0x3ec#64) ↦₆₄ u3ec) ∗
         ((sp + 0x400#64) ↦₆₄ u400) ∗ ((sp + 0x408#64) ↦₆₄ u408) ∗
         ((sp + 0x440#64) ↦₆₄ u440) ∗ ((sp + 0x448#64) ↦₆₄ u448) ∗
         ((sp + 0x4a0#64) ↦₃₂ u4a0) ∗ ((sp + 0x4a4#64) ↦₆₄ u4a4) ∗
         ((sp + 0x4ac#64) ↦₆₄ u4ac) ∗ ((sp + 0x4b4#64) ↦₆₄ u4b4) ∗ ((sp + 0x4bc#64) ↦₃₂ u4bc) ∗
         ((sp + 0x4c0#64) ↦₆₄ u4c0) ∗ ((sp + 0x4c8#64) ↦₆₄ u4c8) ∗
         ((sp + 0x4d0#64) ↦₆₄ u4d0) ∗ ((sp + 0x4d8#64) ↦₆₄ u4d8) ∗
         ((sp + 0x500#64) ↦₆₄ u500) ∗ ((sp + 0x508#64) ↦₆₄ u508) ∗ ((sp + 0x510#64) ↦₃₂ u510))
        (fun s1 P1 => VmPreserved s s1 ∧
          s1.sp = sp ∧ s1.readReg64 .x0 = sp + 0x190#64 ∧ s1.readReg64 .x1 = 32#64 ∧
          s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
          s1.readReg64 .x21 = s.readReg64 .x21 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = sp + 0x500#64 ∧ s1.readReg64 .x25 = sp + 0x190#64 ∧
          s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = sp + 0x3d0#64 ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
          s1.readVReg128 0#5 = 0#128 ∧ s1.trace = s0.trace ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P1 ∗ R) →
            (m ⊨ (((sp + 0x10#64) ↦₃₂ c2) ∗
                  ((sp + 0x1c#64) ↦₃₂ (s.readReg64 .x24).setWidth 32) ∗
                  ((sp + 0x194#64) ↦₃₂ r0) ∗ ((sp + 0x198#64) ↦₆₄ r1) ∗
                  ((sp + 0x1a0#64) ↦₆₄ r2) ∗ ((sp + 0x1a8#64) ↦₆₄ r3) ∗ ((sp + 0x1b0#64) ↦₃₂ r4) ∗
                  ((sp + 0x1b4#64) ↦₆₄ c0) ∗ ((sp + 0x1bc#64) ↦₆₄ c1) ∗ ((sp + 0x1c4#64) ↦₃₂ c2) ∗
                  ((sp + 0x1c8#64) ↦₆₄ c3) ∗ ((sp + 0x1d0#64) ↦₆₄ c4) ∗
                  ((sp + 0x3d0#64) ↦₆₄ c0) ∗ ((sp + 0x3d8#64) ↦₆₄ c1) ∗ ((sp + 0x3e0#64) ↦₃₂ c2) ∗
                  ((sp + 0x3e4#64) ↦₆₄ c3) ∗ ((sp + 0x3ec#64) ↦₆₄ c4) ∗
                  ((sp + 0x400#64) ↦₆₄ c0) ∗ ((sp + 0x408#64) ↦₆₄ c1) ∗
                  ((sp + 0x440#64) ↦₆₄ c3) ∗ ((sp + 0x448#64) ↦₆₄ c4) ∗
                  ((sp + 0x4a0#64) ↦₃₂ r0) ∗ ((sp + 0x4a4#64) ↦₆₄ r1) ∗
                  ((sp + 0x4ac#64) ↦₆₄ r2) ∗ ((sp + 0x4b4#64) ↦₆₄ r3) ∗ ((sp + 0x4bc#64) ↦₃₂ r4) ∗
                  ((sp + 0x4c0#64) ↦₆₄ c3) ∗ ((sp + 0x4c8#64) ↦₆₄ c4) ∗
                  ((sp + 0x4d0#64) ↦₆₄ c0) ∗ ((sp + 0x4d8#64) ↦₆₄ c1) ∗
                  ((sp + 0x500#64) ↦₆₄ r2) ∗ ((sp + 0x508#64) ↦₆₄ r3) ∗
                  ((sp + 0x510#64) ↦₃₂ r4)) ∗ R)))
  wpp_778_to_rng :
    ∀ (s0 s : State) (u0 u1 u2 u3 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1912#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x0 = sp + 0x190#64 → s.readReg64 .x1 = 32#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.readVReg128 0#5 = 0#128 → s.trace = s0.trace →
      SepWP prog rngFillEntry s
        (((sp + 0x190#64) ↦₆₄ u0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ u1) ∗
         ((sp + 0x190#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ u3))
        (fun sc P_c => VmPreserved s sc ∧
          sc.sp = sp ∧ sc.readReg64 .x0 = sp + 0x190#64 ∧ sc.readReg64 .x1 = 32#64 ∧
          sc.readReg64 .x30 = entry + 1920#64 ∧ CalleeSavedPreserved s sc ∧ sc.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_c ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₆₄ 0#64) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ 0#64) ∗
                  ((sp + 0x190#64 + 16#64) ↦₆₄ 0#64) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ 0#64)) ∗ R)))
  wpp_780_to_7a8 :
    ∀ (s0 s : State) (b0 b31 : BitVec 8),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1920#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 → s.readReg64 .x23 = sp + 0x500#64 →
      s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWP prog (entry + 1960#64) s (((sp + 0x190#64) ↦₈ b0) ∗ ((sp + 0x1af#64) ↦₈ b31))
        (fun s' P' => VmPreserved s s' ∧
          s'.sp = sp ∧ s'.readReg64 .x0 = sp + 0x500#64 ∧ s'.readReg64 .x8 = sp + 0x400#64 ∧
          s'.readReg64 .x19 = s.readReg64 .x19 ∧ s'.readReg64 .x20 = s.readReg64 .x20 ∧
          s'.readReg64 .x21 = s.readReg64 .x21 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
          s'.readReg64 .x23 = s.readReg64 .x23 ∧ s'.readReg64 .x24 = sp + 0x400#64 ∧
          s'.readReg64 .x25 = s.readReg64 .x25 ∧ s'.readReg64 .x26 = s.readReg64 .x26 ∧
          s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
          s'.readReg64 .x29 = s0.sp - 96#64 ∧ s'.trace = s0.trace ∧
          calleeSavedVRegs s' = calleeSavedVRegs s0 ∧
          (∀ m R, (m ⊨ P' ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₈ (b0 &&& 0xf8#8)) ∗
                  ((sp + 0x1af#64) ↦₈ ((b31 &&& 0x7f#8) ||| 0x40#8))) ∗ R)))
  wpp_7a8_to_dpk :
    ∀ (s0 s : State) (p0 p1 p2 p3 u0 u1 u2 u3 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1960#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x0 = sp + 0x500#64 → s.readReg64 .x8 = sp + 0x400#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x25 = sp + 0x190#64 → s.trace = s0.trace →
      SepWP prog (lsmpl.base 200) s
        (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
         ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3) ∗
         ((sp + 0x500#64) ↦₆₄ u0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ u1) ∗
         ((sp + 0x500#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ u3))
        (fun sc P_c => VmPreserved s sc ∧
          sc.sp = sp ∧ sc.readReg64 .x0 = sp + 0x500#64 ∧ sc.readReg64 .x8 = sp + 0x400#64 ∧
          sc.readReg64 .x30 = entry + 1972#64 ∧ CalleeSavedPreserved s sc ∧ sc.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_c ∗ R) →
            (m ⊨ (((sp + 0x190#64) ↦₆₄ p0) ∗ ((sp + 0x190#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x190#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x190#64 + 24#64) ↦₆₄ p3) ∗
                  ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) ∗ R)))
  wpp_7b4_to_sd :
    ∀ (s0 s : State) (p0 p1 p2 p3 u0 u1 u2 u3 : BitVec 64),
      let sp := s0.sp - 1504#64
      s.pc = entry + 1972#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x29 = s0.sp - 96#64 →
      s.readReg64 .x23 = sp + 0x500#64 → s.readReg64 .x28 = sp + 0x3d0#64 → s.trace = s0.trace →
      SepWP prog (lsmpl.ρ "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop") s
        (((sp + 0x420#64) ↦₆₄ u0) ∗ ((sp + 0x420#64 + 8#64) ↦₆₄ u1) ∗
         ((sp + 0x420#64 + 16#64) ↦₆₄ u2) ∗ ((sp + 0x420#64 + 24#64) ↦₆₄ u3) ∗
         ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
         ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3))
        (fun sc P_c => VmPreserved s sc ∧
          sc.sp = sp ∧ sc.readReg64 .x0 = sp + 0x500#64 ∧ sc.readReg64 .x30 = entry + 1988#64 ∧
          CalleeSavedPreserved s sc ∧ sc.trace = s0.trace ∧
          (∀ m R, (m ⊨ P_c ∗ R) →
            (m ⊨ (((sp + 0x420#64) ↦₆₄ p0) ∗ ((sp + 0x420#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x420#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x420#64 + 24#64) ↦₆₄ p3) ∗
                  ((sp + 0x500#64) ↦₆₄ p0) ∗ ((sp + 0x500#64 + 8#64) ↦₆₄ p1) ∗
                  ((sp + 0x500#64 + 16#64) ↦₆₄ p2) ∗ ((sp + 0x500#64 + 24#64) ↦₆₄ p3)) ∗ R)))
  wpp_7c4_to_cc2 :
    ∀ (s0 s2 : State) (msgA : BitVec 64),
      let sp := s0.sp - 1504#64
      s2.pc = entry + 1988#64 → s2.status = .Running → s2.sp = sp → s2.spAligned = true →
      s2.readReg64 .x22 = msgA → s2.readReg64 .x24 = sp + 0x400#64 →
      s2.readReg64 .x29 = s0.sp - 96#64 → s2.trace = s0.trace →
      SepWP prog (lsmpl.base 40) s2 emp
        (fun s' P' => VmPreserved s2 s' ∧
          s'.sp = sp ∧ s'.readReg64 .x0 = sp + 0x4a0#64 ∧ s'.readReg64 .x1 = msgA + 56#64 ∧
          s'.readReg64 .x2 = sp + 0x420#64 ∧ s'.readReg64 .x8 = sp + 0x190#64 ∧
          s'.readReg64 .x30 = entry + 2008#64 ∧ CalleeSavedPreserved s2 s' ∧ s'.trace = s0.trace ∧
          (∀ m R, (m ⊨ P' ∗ R) → (m ⊨ R)))


private theorem hchk_130 : checkBlockNoSvc0 blkLib_131.text = true := by rfl_kernel

private theorem hchk_433 : checkBlockNoSvc0 blkLib_434.text = true := by rfl_kernel

set_option maxHeartbeats 1600000 in
def dhStepBlockVmWp_159 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhStepBlockVmWp ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      (lsmpl.ρ "libsignal_session_rng_fill") where
  missingScAddr := (dhStepBlockWp_159 H).missingScAddr
  hro_missingSc := (dhStepBlockWp_159 H).hro_missingSc
  wpp_2dc_to_30c := by
    intro s0 s w2c0 w2c8 u34c u344 u338 u330 u2b8 u2b0 u180 u178 u170 u168 u340 u2d0 u18c u188
      sp hpc hrun hsp hsp_al hx29 hx12 hx20 hx25 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := (blkPl_131).base + 780#64)
    intro _m_strip
    wp_steps
    have hre : ((sp + 832#64) ↦₃₂ u2d0 ∗ (sp + 836#64) ↦₆₄ u2b0 ∗ (sp + 844#64) ↦₆₄ u2b8 ∗ memRegion (sp + 852#64) 556) =
        ((sp + 832#64) ↦₆₄ (u2b0.extractLsb' 0 32 ++ u2d0) ∗
         (sp + 840#64) ↦₆₄ (u2b8.extractLsb' 0 32 ++ u2b0.extractLsb' 32 32) ∗
         (sp + 848#64) ↦₃₂ u2b8.extractLsb' 32 32 ∗
         memRegion (sp + 852#64) 556) := by
      have := congrArg (· ∗ memRegion (sp + 852#64) 556) (reassoc_4_8_8_to_8_8_4 (sp + 832#64) u2d0 u2b0 u2b8)
      have h1 : sp + 832#64 + 4#64 = sp + 836#64 := by bv_arith
      have h2 : sp + 832#64 + 12#64 = sp + 844#64 := by bv_arith
      have h3 : sp + 832#64 + 8#64 = sp + 840#64 := by bv_arith
      have h4 : sp + 832#64 + 16#64 = sp + 848#64 := by bv_arith
      rw [h1, h2, h3, h4] at this
      exact Eq.trans (by sep_ac_rfl) (Eq.trans this (by sep_ac_rfl))
    rw [hre]
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], by simp, by simp [hx20, sp], by simp, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have h178_fold : memRegion (sp + 0x178#64) 24 =
        memRegion (sp + 376#64) 8 ∗ memRegion (sp + 384#64) 8 ∗
        memRegion (sp + 392#64) 4 ∗ memRegion (sp + 396#64) 4 := by
      rw [show sp + 0x178#64 = sp + 376#64 from rfl,
          memRegion_split' (b := sp + 376#64) (b' := sp + 384#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 384#64) (b' := sp + 392#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 392#64) (b' := sp + 396#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    have h190_fold : memRegion (sp + 0x190#64) 0x3f0 =
        memRegion (sp + 400#64) 288 ∗ memRegion (sp + 688#64) 8 ∗ memRegion (sp + 696#64) 8 ∗
        memRegion (sp + 704#64) 8 ∗ memRegion (sp + 712#64) 8 ∗ memRegion (sp + 720#64) 4 ∗
        memRegion (sp + 724#64) 92 ∗ memRegion (sp + 816#64) 8 ∗ memRegion (sp + 824#64) 8 ∗
        memRegion (sp + 832#64) 8 ∗ memRegion (sp + 840#64) 8 ∗ memRegion (sp + 848#64) 4 ∗
        memRegion (sp + 852#64) 556 := by
      rw [show sp + 0x190#64 = sp + 400#64 from rfl,
          memRegion_split' (b := sp + 400#64) (b' := sp + 688#64) (n := 288) (k := 720) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 688#64) (b' := sp + 696#64) (n := 8) (k := 712) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 696#64) (b' := sp + 704#64) (n := 8) (k := 704) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 704#64) (b' := sp + 712#64) (n := 8) (k := 696) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 712#64) (b' := sp + 720#64) (n := 8) (k := 688) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 720#64) (b' := sp + 724#64) (n := 4) (k := 684) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 724#64) (b' := sp + 816#64) (n := 92) (k := 592) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 816#64) (b' := sp + 824#64) (n := 8) (k := 584) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 824#64) (b' := sp + 832#64) (n := 8) (k := 576) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 832#64) (b' := sp + 840#64) (n := 8) (k := 568) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 840#64) (b' := sp + 848#64) (n := 8) (k := 560) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 848#64) (b' := sp + 852#64) (n := 4) (k := 556) rfl (by bv_arith) (by decide)]
    rw [h178_fold, h190_fold]
    change m ⊨ _
    arm64_sep_close
  wpp_7f8_to_2dc := by
    intro s0 s u508 u500 u2c8 u2c0 u2b8 u2b0 u2d0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := (blkPl_131).base + 732#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], by simp [sp], by simp, by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have h140_fold : memRegion (sp + 0x140#64) 0x440 =
        memRegion (sp + 320#64) 88 ∗ memRegion (sp + 408#64) 8 ∗ memRegion (sp + 416#64) 272 ∗
        memRegion (sp + 688#64) 8 ∗ memRegion (sp + 696#64) 8 ∗ memRegion (sp + 704#64) 8 ∗
        memRegion (sp + 712#64) 8 ∗ memRegion (sp + 720#64) 4 ∗ memRegion (sp + 724#64) 556 ∗
        memRegion (sp + 1280#64) 8 ∗ memRegion (sp + 1288#64) 8 ∗ memRegion (sp + 1296#64) 112 := by
      rw [show sp + 0x140#64 = sp + 320#64 from rfl,
          memRegion_split' (b := sp + 320#64) (b' := sp + 408#64) (n := 88) (k := 1000) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 408#64) (b' := sp + 416#64) (n := 8) (k := 992) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 416#64) (b' := sp + 688#64) (n := 272) (k := 720) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 688#64) (b' := sp + 696#64) (n := 8) (k := 712) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 696#64) (b' := sp + 704#64) (n := 8) (k := 704) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 704#64) (b' := sp + 712#64) (n := 8) (k := 696) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 712#64) (b' := sp + 720#64) (n := 8) (k := 688) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 720#64) (b' := sp + 724#64) (n := 4) (k := 684) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 724#64) (b' := sp + 1280#64) (n := 556) (k := 128) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 1280#64) (b' := sp + 1288#64) (n := 8) (k := 120) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 1288#64) (b' := sp + 1296#64) (n := 8) (k := 112) rfl (by bv_arith) (by decide)]
    rw [h140_fold]
    change m ⊨ _
    arm64_sep_close
  wpp_missing_sc := by
    intro s0 s x u2c0 u2c8 sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx25 hx27 hx28 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := (blkPl_131).base + 732#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], by simp [hx12, sp], by simp [hx19], by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have hsp38_fold : memRegion sp 0x38 =
        memRegion sp 0x20 ∗ memRegion (sp + 0x20#64) 8 ∗ memRegion (sp + 0x28#64) 4 ∗
        memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x30#64) 8 := by
      rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k := 0x18) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k := 0x10) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k := 0xc) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k := 0x8) rfl (by bv_arith) (by decide)]
    rw [hsp38_fold]
    change m ⊨ _
    arm64_sep_close
  wpp_cc1_err := by
    intro s0 s u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := (blkPl_131).base + 2040#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc1_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := (blkPl_131).base + 1804#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_pre_cc1 := by
    intro s0 s x p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8
      sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := lsmpl.base 40)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [sp], by simp, by simp [sp], by simp [sp],
       by simp [hx19], by simp [hx20, sp], by simp [hx21], by simp [hx22], by simp [hx23, sp],
       by simp [hx24], by simp [hx25, sp], by simp [sp], by simp [hx27, sp],
       by simp [hx28, sp], by simp [hx29], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := (blkPl_131).base + 2220#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_err := by
    intro s0 s msgW u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := (blkPl_131).base + 2040#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_70c_to_778 := by
    intro s0 s r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510
      r1 r2 r3 c0 c1 c3 c4 u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448
      u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508
      sp hpc hrun hsp hsp_al hx29 hx23 hx25 hx26 htrace hvregs
    rw [show s0.sp - 96#64 = sp + 0x580#64 by dsimp only [sp]; bv_arith] at hx29
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := (blkPl_131).base + 1912#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [sp], rfl, rfl, rfl, rfl, rfl,
       by simp [hx23, sp], by simp [hx25, sp], rfl, rfl, by simp [sp],
       by simp [hx29, sp]; bv_arith, rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_778_to_rng := by
    intro s0 s u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx1 hx25 hv0 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := lsmpl.ρ "libsignal_session_rng_fill")
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx0, sp], by simp [hx1], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_780_to_7a8 := by
    intro s0 s b0 b31 sp hpc hrun hsp hsp_al hx29 hx23 hx25 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := (blkPl_131).base + 1960#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [sp]; bv_arith, by simp [sp],
       rfl, rfl, rfl, rfl, rfl, by simp [sp], rfl, rfl, rfl, rfl,
       by simp [hx29], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    rw [clamp_byte0 b0, clamp_byte31 b31] at hm
    arm64_sep_close
  wpp_7a8_to_dpk := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx8 hx23 hx25 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := lsmpl.base 200)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx0, sp], by simp [hx8, sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7b4_to_sd := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx29 hx23 hx28 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := lsmpl.ρ "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop")
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [sp]; bv_arith, rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7c4_to_cc2 := by
    intro s0 s2 msgA sp hpc2 hrun2 hsp2 hsp_al2 hx22_2 hx24_2 hx29_2 htrace2
    apply sepWP_seg_ls_vm
      (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H))
      blkLib_eq_131 hchk_130 (mid := lsmpl.base 40)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun2]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun2])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp2], by simp [sp]; bv_arith, by simp,
       by simp [sp], by simp [sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace2], fun m R hm => ?_⟩
    simpa [emp_sepConj] using hm

set_option maxHeartbeats 1600000 in
def dhStepBlockVmWp_549 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhStepBlockVmWp ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      (lsmpl.base 618) where
  missingScAddr := (dhStepBlockWp_549 H).missingScAddr
  hro_missingSc := (dhStepBlockWp_549 H).hro_missingSc
  wpp_2dc_to_30c := by
    intro s0 s w2c0 w2c8 u34c u344 u338 u330 u2b8 u2b0 u180 u178 u170 u168 u340 u2d0 u18c u188
      sp hpc hrun hsp hsp_al hx29 hx12 hx20 hx25 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := (blkPl_434).base + 780#64)
    intro _m_strip
    wp_steps
    have hre : ((sp + 832#64) ↦₃₂ u2d0 ∗ (sp + 836#64) ↦₆₄ u2b0 ∗ (sp + 844#64) ↦₆₄ u2b8 ∗ memRegion (sp + 852#64) 556) =
        ((sp + 832#64) ↦₆₄ (u2b0.extractLsb' 0 32 ++ u2d0) ∗
         (sp + 840#64) ↦₆₄ (u2b8.extractLsb' 0 32 ++ u2b0.extractLsb' 32 32) ∗
         (sp + 848#64) ↦₃₂ u2b8.extractLsb' 32 32 ∗
         memRegion (sp + 852#64) 556) := by
      have := congrArg (· ∗ memRegion (sp + 852#64) 556) (reassoc_4_8_8_to_8_8_4 (sp + 832#64) u2d0 u2b0 u2b8)
      have h1 : sp + 832#64 + 4#64 = sp + 836#64 := by bv_arith
      have h2 : sp + 832#64 + 12#64 = sp + 844#64 := by bv_arith
      have h3 : sp + 832#64 + 8#64 = sp + 840#64 := by bv_arith
      have h4 : sp + 832#64 + 16#64 = sp + 848#64 := by bv_arith
      rw [h1, h2, h3, h4] at this
      exact Eq.trans (by sep_ac_rfl) (Eq.trans this (by sep_ac_rfl))
    rw [hre]
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], by simp, by simp [hx20, sp], by simp, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have h178_fold : memRegion (sp + 0x178#64) 24 =
        memRegion (sp + 376#64) 8 ∗ memRegion (sp + 384#64) 8 ∗
        memRegion (sp + 392#64) 4 ∗ memRegion (sp + 396#64) 4 := by
      rw [show sp + 0x178#64 = sp + 376#64 from rfl,
          memRegion_split' (b := sp + 376#64) (b' := sp + 384#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 384#64) (b' := sp + 392#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 392#64) (b' := sp + 396#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    have h190_fold : memRegion (sp + 0x190#64) 0x3f0 =
        memRegion (sp + 400#64) 288 ∗ memRegion (sp + 688#64) 8 ∗ memRegion (sp + 696#64) 8 ∗
        memRegion (sp + 704#64) 8 ∗ memRegion (sp + 712#64) 8 ∗ memRegion (sp + 720#64) 4 ∗
        memRegion (sp + 724#64) 92 ∗ memRegion (sp + 816#64) 8 ∗ memRegion (sp + 824#64) 8 ∗
        memRegion (sp + 832#64) 8 ∗ memRegion (sp + 840#64) 8 ∗ memRegion (sp + 848#64) 4 ∗
        memRegion (sp + 852#64) 556 := by
      rw [show sp + 0x190#64 = sp + 400#64 from rfl,
          memRegion_split' (b := sp + 400#64) (b' := sp + 688#64) (n := 288) (k := 720) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 688#64) (b' := sp + 696#64) (n := 8) (k := 712) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 696#64) (b' := sp + 704#64) (n := 8) (k := 704) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 704#64) (b' := sp + 712#64) (n := 8) (k := 696) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 712#64) (b' := sp + 720#64) (n := 8) (k := 688) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 720#64) (b' := sp + 724#64) (n := 4) (k := 684) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 724#64) (b' := sp + 816#64) (n := 92) (k := 592) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 816#64) (b' := sp + 824#64) (n := 8) (k := 584) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 824#64) (b' := sp + 832#64) (n := 8) (k := 576) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 832#64) (b' := sp + 840#64) (n := 8) (k := 568) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 840#64) (b' := sp + 848#64) (n := 8) (k := 560) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 848#64) (b' := sp + 852#64) (n := 4) (k := 556) rfl (by bv_arith) (by decide)]
    rw [h178_fold, h190_fold]
    change m ⊨ _
    arm64_sep_close
  wpp_7f8_to_2dc := by
    intro s0 s u508 u500 u2c8 u2c0 u2b8 u2b0 u2d0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := (blkPl_434).base + 732#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], by simp [sp], by simp, by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have h140_fold : memRegion (sp + 0x140#64) 0x440 =
        memRegion (sp + 320#64) 88 ∗ memRegion (sp + 408#64) 8 ∗ memRegion (sp + 416#64) 272 ∗
        memRegion (sp + 688#64) 8 ∗ memRegion (sp + 696#64) 8 ∗ memRegion (sp + 704#64) 8 ∗
        memRegion (sp + 712#64) 8 ∗ memRegion (sp + 720#64) 4 ∗ memRegion (sp + 724#64) 556 ∗
        memRegion (sp + 1280#64) 8 ∗ memRegion (sp + 1288#64) 8 ∗ memRegion (sp + 1296#64) 112 := by
      rw [show sp + 0x140#64 = sp + 320#64 from rfl,
          memRegion_split' (b := sp + 320#64) (b' := sp + 408#64) (n := 88) (k := 1000) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 408#64) (b' := sp + 416#64) (n := 8) (k := 992) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 416#64) (b' := sp + 688#64) (n := 272) (k := 720) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 688#64) (b' := sp + 696#64) (n := 8) (k := 712) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 696#64) (b' := sp + 704#64) (n := 8) (k := 704) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 704#64) (b' := sp + 712#64) (n := 8) (k := 696) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 712#64) (b' := sp + 720#64) (n := 8) (k := 688) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 720#64) (b' := sp + 724#64) (n := 4) (k := 684) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 724#64) (b' := sp + 1280#64) (n := 556) (k := 128) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 1280#64) (b' := sp + 1288#64) (n := 8) (k := 120) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 1288#64) (b' := sp + 1296#64) (n := 8) (k := 112) rfl (by bv_arith) (by decide)]
    rw [h140_fold]
    change m ⊨ _
    arm64_sep_close
  wpp_missing_sc := by
    intro s0 s x u2c0 u2c8 sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx25 hx27 hx28 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := (blkPl_434).base + 732#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], by simp [hx12, sp], by simp [hx19], by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have hsp38_fold : memRegion sp 0x38 =
        memRegion sp 0x20 ∗ memRegion (sp + 0x20#64) 8 ∗ memRegion (sp + 0x28#64) 4 ∗
        memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x30#64) 8 := by
      rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 0x20) (k := 0x18) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 0x8) (k := 0x10) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 0x4) (k := 0xc) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 0x4) (k := 0x8) rfl (by bv_arith) (by decide)]
    rw [hsp38_fold]
    change m ⊨ _
    arm64_sep_close
  wpp_cc1_err := by
    intro s0 s u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := (blkPl_434).base + 2040#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc1_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := (blkPl_434).base + 1804#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_pre_cc1 := by
    intro s0 s x p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8
      sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := lsmpl.base 40)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [sp], by simp, by simp [sp], by simp [sp],
       by simp [hx19], by simp [hx20, sp], by simp [hx21], by simp [hx22], by simp [hx23, sp],
       by simp [hx24], by simp [hx25, sp], by simp [sp], by simp [hx27, sp],
       by simp [hx28, sp], by simp [hx29], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := (blkPl_434).base + 2220#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_err := by
    intro s0 s msgW u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := (blkPl_434).base + 2040#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_70c_to_778 := by
    intro s0 s r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510
      r1 r2 r3 c0 c1 c3 c4 u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448
      u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508
      sp hpc hrun hsp hsp_al hx29 hx23 hx25 hx26 htrace hvregs
    rw [show s0.sp - 96#64 = sp + 0x580#64 by dsimp only [sp]; bv_arith] at hx29
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := (blkPl_434).base + 1912#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [sp], rfl, rfl, rfl, rfl, rfl,
       by simp [hx23, sp], by simp [hx25, sp], rfl, rfl, by simp [sp],
       by simp [hx29, sp]; bv_arith, rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_778_to_rng := by
    intro s0 s u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx1 hx25 hv0 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := lsmpl.base 618)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx0, sp], by simp [hx1], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_780_to_7a8 := by
    intro s0 s b0 b31 sp hpc hrun hsp hsp_al hx29 hx23 hx25 htrace hvregs
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := (blkPl_434).base + 1960#64)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [sp]; bv_arith, by simp [sp],
       rfl, rfl, rfl, rfl, rfl, by simp [sp], rfl, rfl, rfl, rfl,
       by simp [hx29], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    rw [clamp_byte0 b0, clamp_byte31 b31] at hm
    arm64_sep_close
  wpp_7a8_to_dpk := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx8 hx23 hx25 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := lsmpl.base 200)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [hx0, sp], by simp [hx8, sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7b4_to_sd := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx29 hx23 hx28 htrace
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := lsmpl.ρ "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop")
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp, sp], by simp [sp]; bv_arith, rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7c4_to_cc2 := by
    intro s0 s2 msgA sp hpc2 hrun2 hsp2 hsp_al2 hx22_2 hx24_2 hx29_2 htrace2
    apply sepWP_seg_ls_vm
      (Q := (blkPC_434).rebase (blkPl_434).base (hooksException H))
      blkLib_eq_434 hchk_433 (mid := lsmpl.base 40)
    intro _m_strip
    wp_steps
    refine SepWP.done rfl (by simp [hrun2]) fun _m_real _hnsp => ?_
    refine SepWP.done rfl (by simp [hrun2])
      ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]), by simp [hsp2], by simp [sp]; bv_arith, by simp,
       by simp [sp], by simp [sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace2], fun m R hm => ?_⟩
    simpa [emp_sepConj] using hm
end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetWp
