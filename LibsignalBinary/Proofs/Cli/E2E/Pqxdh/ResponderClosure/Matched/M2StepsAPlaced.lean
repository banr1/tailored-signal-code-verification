/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Relocatable Stage P2 Matched-Session Basic Blocks: Part A

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2StepsA` on Block `518`
(`lsProg_518 ext`, `(blkPl_518).base = lsmpl.base 518`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-- `(blkPl_518).base + 0x0868 → PublicKey::serialize` under `[LibsignalPlacement]`. -/
theorem p2_seg1a_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (msgVerByte b_4f1 : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xf0#64) ↦₈ msgVerByte))
      (fun s1 P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xf0#64) ↦₈ msgVerByte)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x8a0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx8' : s.readReg64 (Reg.gpr 8#5) = kyberStorePtr := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgPtr := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = kyberStoreVt := hx10
  have hx11' : s.readReg64 (Reg.gpr 11#5) = preKeyStorePtr := hx11
  have hx12' : s.readReg64 (Reg.gpr 12#5) = remoteAddrPtr := hx12
  have hx13' : s.readReg64 (Reg.gpr 13#5) = preKeyStoreVt := hx13
  have hx14' : s.readReg64 (Reg.gpr 14#5) = localAddrPtr := hx14
  have hx15' : s.readReg64 (Reg.gpr 15#5) = idStorePtr := hx15
  have hx16' : s.readReg64 (Reg.gpr 16#5) = idStoreVt := hx16
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    rfl⟩
  dsimp only [processPrekeyActive10At]
  sep_frame

/-- `(blkPl_518).base + 0x08a0 → lsmpl.base 50` under `[LibsignalPlacement]`. -/
theorem p2_seg1b_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr serPtr spkStorePtr spkStoreVt : BitVec 64) (msgVerByte : BitVec 8)
    (hpc : s.pc = (blkPl_518).base + 0x8a0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx25 : s.readReg64 .x25 = msgVerByte.zeroExtend 64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 50) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x2 = serPtr ∧
        s1.readReg64 .x3 = 33#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x8c0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = serPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = 33#64 := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = msgVerByte.zeroExtend 64 := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], rfl⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
