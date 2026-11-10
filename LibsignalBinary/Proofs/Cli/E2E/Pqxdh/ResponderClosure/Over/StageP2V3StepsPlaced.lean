/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V3Steps
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsEPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import all Init.Data.String.Defs

/-!
# Placed Stage P2 Over-Path Outer `v3` Reject Basic Blocks

Proves `[LibsignalPlacement]` basic-block specifications for the outer `v3` reject path from
`+0x0868` to `dropProcessPrekeyImplName` on `stageP1ProgPlaced ext`.
-/

@[expose] public section

set_option autoImplicit false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## Placed Outer `v3` Basic Blocks (`+0x0868 → dropProcessPrekeyImplName`) -/

set_option maxHeartbeats 800000 in
theorem p2_over_seg1a_v3_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
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
    SepWP (stageP1ProgPlaced ext) (lsmpl.base 205) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xf0#64) ↦₈ 3#8))
      (fun s1 P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xf0#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 3#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x8a0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
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
    by simp_all [arm64_norm]⟩
  dsimp only [processPrekeyActive10At]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem p2_over_seg1b_v3_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr serPtr spkStorePtr spkStoreVt : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x8a0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx25 : s.readReg64 .x25 = 3#64) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = 3#64 ∧
        s1.readReg64 .x2 = serPtr ∧
        s1.readReg64 .x3 = 33#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 3#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x8c0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = serPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = 33#64 := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 3#64 := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1000000 in
/-- Placed outer `v3` step `+0x0a44 → dropProcessPrekeyImplName` on `stageP1ProgPlaced ext`. -/
theorem p2_over_seg1d_v3_to_drop_ext_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr cap ptr len u_a8 u_d0 : BitVec 64)
    (b_4f2 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0xa44#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl
        "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") s
      (((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ len))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3#64) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ len) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ len)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0x8000000000000018#64 ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = ptr ∧
        s1.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x24 = cap ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x1698#64) := by
  have hcond : ConditionHolds CondCode.NE (addsPState64 0x8000000000000018#64 3#64) = true :=
    p2_cond_ne_adds64_of_ne_neg3 (by decide)
  have hsplit_cap :
      ((s.sp + 0x3e0#64) ↦₆₄ cap) =
        ((s.sp + 0x3e0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
        ((s.sp + 0x3e4#64) ↦₃₂ cap.extractLsb' 32 32) := by
    rw [pointsTo64_split32 (s.sp + 0x3e0#64) cap]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  apply SepWP.fold (Entails.of_eq hsplit_cap) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq hsplit_cap.symm) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

abbrev x3dhUnsupportedSym : String := "libsignal_cli_handshake:.rodata..Lanon.83"

/-- Byte encoding of the 24-byte `"X3DH no longer supported"` `.rodata` message. -/
def x3dhUnsupportedBytes : List (BitVec 8) :=
  ("X3DH no longer supported".toUTF8.toList).map UInt8.toBitVec

theorem x3dhUnsupportedBytes_length : x3dhUnsupportedBytes.length = 24 := by decide +kernel

theorem rodata_x3dhUnsupported_intro_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (lsρ x3dhUnsupportedSym ↦ᵣ x3dhUnsupportedBytes) ∗ P :=
  lsro_intro_chk hro (sym := x3dhUnsupportedSym) (bs := x3dhUnsupportedBytes) (by decide +kernel) hP

theorem p2_intro_rodata_x3dhUnsupported_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s
      ((lsρ x3dhUnsupportedSym ↦ᵣ x3dhUnsupportedBytes) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ ((lsρ x3dhUnsupportedSym ↦ᵣ x3dhUnsupportedBytes) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact rodata_x3dhUnsupported_intro_placed hcrl.2 hm
  exact h R hm' hL

set_option maxHeartbeats 1200000 in
/-- Placed outer `v3` step `+0x08c0 → strToOwnedLocal2Name` under `StageP2ClosureHooksPlaced`. -/
theorem p2_over_seg1c_v3_hooks_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext)
    (s : State) (coroPtr msgPtr serPtr : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl Matched.strToOwnedLocal2Name) s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
       A.live serPtr 33 1 ∗
       memRegion serPtr 33 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xf0#64) ↦₈ 3#8))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xf0#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = lsρ x3dhUnsupportedSym ∧
        s1.readReg64 .x2 = 24#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xa44#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, Matched.strToOwnedLocal2Name] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = serPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 33#64 := hx26
  wp_steps
  wp_call hdealloc (serPtr, 33, 1)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
