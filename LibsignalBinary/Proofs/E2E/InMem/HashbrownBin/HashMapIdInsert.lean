/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.FallibleWithCapacity
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.HashOne
import ProofLib.SepLogic.WPp

/-!
# Helpers for `<HashMap<ProtocolAddress, IdentityKey>>::insert` (`0x14ee0`)

64-bit SIMD load/store step rules, NEON bitvector lemmas, and separation-logic framing helpers for
`hashMapIdInsertEmpty_ok` and `hashMapIdInsertSingleHit_ok`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel

namespace HashMapIdInsert

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  Arm64.State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : Arm64.State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

/-! ## 64-Bit SIMD (`D64`) Load/Store Step Rules -/

theorem step_ldrSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .D64 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt (v.zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .D64 vt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read64 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 8 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldrSimd .D64 vt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      Arm64.State.advancePC, Arm64.State.setPC, hsp, haddr, hread, hcan,
      SimdMemSize.bytes, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem step_ldpSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldpSimd .D64 vt1 vt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 ea = v1 := hload1.load hm
  have hread2 : s.mem.read64 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 8 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 8 = true := hload2.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldpSimd .D64 vt1 vt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      Arm64.State.advancePC, Arm64.State.setPC, hsp, haddr, hea2,
      hread1, hread2, hcan1, hcan2, SimdMemSize.bytes, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

theorem step_stpSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P P1 P2 : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .D64 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : (s.readVReg128 vt1).setWidth 64 = v1)
    (hv2 : (s.readVReg128 vt2).setWidth 64 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at hnext ⊢
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stpSimd .D64 vt1 vt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.stpSimd .D64 vt1 vt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      Arm64.State.advancePC, Arm64.State.setPC, Arm64.State.setMem, Arm64.State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, SimdMemSize.bytes, hpc, m1, m2]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  exact hnext m2 R hm2

theorem step_stpSimd64_sp {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {P P1 P2 : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hstore1 : SepStore64 ea ((s.readVReg128 vt1).setWidth 64) P P1)
    (hstore2 : SepStore64 ea2 ((s.readVReg128 vt2).setWidth 64) P1 P2)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setPC (pc + 4#64)).setMem m') P2 post) :
    SepWP prog target_pc s P post :=
  step_stpSimd64 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 rfl rfl hstore1 hstore2 rfl hnext

theorem step_ldpSimd64_sp' {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((s.writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64)) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post :=
  step_ldpSimd64 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 hload1 hload2 hexec hnext

/-! ## NEON and Bitvector Lemmas for `0x14ee0` -/

theorem shr57_toNat_lt_128 (h : BitVec 64) : (h >>> 57).toNat < 128 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := h.isLt
  omega

theorem shr57_eq_ofNat (h : BitVec 64) :
    h >>> 57 = BitVec.ofNat 64 (h >>> 57).toNat := by
  apply BitVec.eq_of_toNat_eq
  have hlt := shr57_toNat_lt_128 h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem h2Tag_eq_ofNat_shr57 (h : BitVec 64) :
    h2Tag h = BitVec.ofNat 8 (h >>> 57).toNat := by
  have hlt := shr57_toNat_lt_128 h
  apply BitVec.eq_of_toNat_eq
  unfold h2Tag
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  change (h >>> 57).toNat % 256 &&& (2 ^ 7 - 1) = (h >>> 57).toNat % 256
  rw [Nat.mod_eq_of_lt (by omega), Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]

theorem truncate8_shr57_eq_h2Tag (h : BitVec 64) :
    (h >>> 57).truncate 8 = h2Tag h := by
  have hlt := shr57_toNat_lt_128 h
  rw [h2Tag_eq_ofNat_shr57]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

def rawMatchTagMask (w h : BitVec 64) : BitVec 64 :=
  BitVec.truncate 64
    (0#128 |||
      ((if (BitVec.zeroExtend 128 w >>> 0 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 0 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 0 |||
      ((if (BitVec.zeroExtend 128 w >>> 8 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 8 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 8 |||
      ((if (BitVec.zeroExtend 128 w >>> 16 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 16 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 16 |||
      ((if (BitVec.zeroExtend 128 w >>> 24 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 24 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 24 |||
      ((if (BitVec.zeroExtend 128 w >>> 32 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 32 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 32 |||
      ((if (BitVec.zeroExtend 128 w >>> 40 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 40 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 40 |||
      ((if (BitVec.zeroExtend 128 w >>> 48 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 48 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 48 |||
      ((if (BitVec.zeroExtend 128 w >>> 56 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 56 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
    9259542123273814144#64

private def rawMatchTagMaskByNat (w : BitVec 64) (n : Nat) : BitVec 64 :=
  let v := BitVec.ofNat 64 n
  BitVec.truncate 64
    (0#128 |||
      ((if (BitVec.zeroExtend 128 w >>> 0 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 56) >>> 0 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 0 |||
      ((if (BitVec.zeroExtend 128 w >>> 8 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 56) >>> 8 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 8 |||
      ((if (BitVec.zeroExtend 128 w >>> 16 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 56) >>> 16 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 16 |||
      ((if (BitVec.zeroExtend 128 w >>> 24 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 56) >>> 24 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 24 |||
      ((if (BitVec.zeroExtend 128 w >>> 32 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 56) >>> 32 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 32 |||
      ((if (BitVec.zeroExtend 128 w >>> 40 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 56) >>> 40 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 40 |||
      ((if (BitVec.zeroExtend 128 w >>> 48 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 56) >>> 48 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 48 |||
      ((if (BitVec.zeroExtend 128 w >>> 56 &&& 255#128 ==
            (0#128 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 0 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 8 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 16 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 24 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 32 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 40 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 48 |||
              (BitVec.zeroExtend 128 v &&& 255#128 &&& 255#128) <<< 56) >>> 56 &&& 255#128) = true
        then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
    9259542123273814144#64

private theorem rawMatchTagMask_eq_byNat (w h : BitVec 64) :
    rawMatchTagMask w h = rawMatchTagMaskByNat w (h >>> 57).toNat := by
  unfold rawMatchTagMask rawMatchTagMaskByNat
  rw [← shr57_eq_ofNat h]

private theorem rawMatchTagMaskByNat_allOnes :
    ∀ n : Fin 128, rawMatchTagMaskByNat 0xffffffffffffffff#64 n.val = 0#64 := by
  decide +kernel

theorem rawMatchTagMask_allOnes (h : BitVec 64) :
    rawMatchTagMask 0xffffffffffffffff#64 h = 0#64 := by
  rw [rawMatchTagMask_eq_byNat]
  exact rawMatchTagMaskByNat_allOnes ⟨(h >>> 57).toNat, shr57_toNat_lt_128 h⟩

private theorem rawMatchTagMaskByNat_singleCtrl4_same :
    ∀ (k pos : Fin 4) (n : Fin 128),
      rawMatchTagMaskByNat (loadGroupAt (singleCtrl4 k.val (BitVec.ofNat 8 n.val)) pos.val) n.val =
        laneBit (laneOfBucket4 pos.val k.val) := by
  decide +kernel

theorem rawMatchTagMask_singleCtrl4_same (k pos : Nat) (hk : k < 4) (hpos : pos < 4) (h : BitVec 64) :
    rawMatchTagMask (loadGroupAt (singleCtrl4 k (h2Tag h)) pos) h =
      laneBit (laneOfBucket4 pos k) := by
  rw [rawMatchTagMask_eq_byNat, h2Tag_eq_ofNat_shr57]
  exact rawMatchTagMaskByNat_singleCtrl4_same ⟨k, hk⟩ ⟨pos, hpos⟩ ⟨(h >>> 57).toNat, shr57_toNat_lt_128 h⟩

theorem laneBit_laneOfBucket4_ne_zero (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    laneBit (laneOfBucket4 pos k) ≠ 0#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem eval_probeBucket_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (BitVec.ofNat 64 pos +
      (laneBit (laneOfBucket4 pos k)).reverse.clz >>> 3) &&&
      3#64 = BitVec.ofNat 64 k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem mirror_offset_eq_self (pos : Nat) (hpos : pos < 4) :
    (BitVec.ofNat 64 pos - 8#64) &&& 3#64 = BitVec.ofNat 64 pos := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem loadGroupAt_emptyCtrl4_eq (pos : Nat) (hpos : pos < 4) :
    loadGroupAt emptyCtrl4 pos = 0xffffffffffffffff#64 := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl

/-! ## Separation-Logic Framing Helpers for `0x14ee0` -/

theorem sepWP_exists_elim {α : Sort _} {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : α → SepProp} {post : Arm64.State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post :=
  SipHashBin.HashOne.sepWP_exists_elim h

theorem sepWP_pure_left_elim {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q : SepProp} {post : Arm64.State → SepProp → Prop}
    (h : P → SepWP prog pc s Q post) :
    SepWP prog pc s (⌜P⌝ ∗ Q) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hp, hm⟩ := hm
  exact h hp R hm

theorem sepWP_extract_pure {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q F : SepProp} {post : Arm64.State → SepProp → Prop}
    (heq : Q = ⌜P⌝ ∗ F)
    (h : P → SepWP prog pc s F post) :
    SepWP prog pc s Q post := by
  rw [heq]
  exact sepWP_pure_left_elim h

theorem pack64_eq_packGroupWord (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    pack64 b0 b1 b2 b3 b4 b5 b6 b7 = packGroupWord b0 b1 b2 b3 b4 b5 b6 b7 :=
  SipHashBin.pack64_eq_or_shifts b0 b1 b2 b3 b4 b5 b6 b7

theorem getD_default_of_lt {α : Type} (xs : List α) (i : Nat) (d1 d2 : α)
    (hi : i < xs.length) :
    xs.getD i d1 = xs.getD i d2 := by
  simp [List.getD, List.getElem?_eq_getElem hi]

theorem loadGroupAt_eq_pack64 (cbs : List (BitVec 8)) (pos : Nat)
    (h : pos + 8 ≤ cbs.length) :
    loadGroupAt cbs pos =
      pack64 (cbs.getD pos 0#8) (cbs.getD (pos + 1) 0#8)
        (cbs.getD (pos + 2) 0#8) (cbs.getD (pos + 3) 0#8)
        (cbs.getD (pos + 4) 0#8) (cbs.getD (pos + 5) 0#8)
        (cbs.getD (pos + 6) 0#8) (cbs.getD (pos + 7) 0#8) := by
  rw [pack64_eq_packGroupWord]
  unfold loadGroupAt
  rw [Nat.add_zero,
      getD_default_of_lt cbs pos emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 1) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 2) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 3) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 4) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 5) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 6) emptyTag 0#8 (by omega),
      getD_default_of_lt cbs (pos + 7) emptyTag 0#8 (by omega)]

theorem pointsToBytes_ctrl12_split_at (ctrl : BitVec 64) (cbs : List (BitVec 8))
    (hlen : cbs.length = 12) (pos : Nat) (hpos : pos < 4) :
    (ctrl ↦ₛ cbs) =
      ((ctrl + BitVec.ofNat 64 pos) ↦₆₄ loadGroupAt cbs pos) ∗
      (ctrl ↦ₛ cbs.take pos) ∗
      ((ctrl + BitVec.ofNat 64 (pos + 8)) ↦ₛ cbs.drop (pos + 8)) := by
  have h1 : pos ≤ cbs.length := by omega
  have h2 : 8 ≤ (cbs.drop pos).length := by simp [List.length_drop, hlen]; omega
  have h3 : pos + 8 ≤ cbs.length := by omega
  rw [pointsToBytes_take_drop ctrl pos cbs h1,
      pointsToBytes_take_drop (ctrl + BitVec.ofNat 64 pos) 8 (cbs.drop pos) h2,
      List.drop_drop,
      pointsToBytes_take8_eq_pointsTo64 (ctrl + BitVec.ofNat 64 pos) cbs pos h3,
      ← loadGroupAt_eq_pack64 cbs pos h3,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  ac_rfl

def ctrl12RestAt (ctrl : BitVec 64) (pos : Nat) : SepProp :=
  (ctrl ↦ₛ emptyCtrl4.take pos) ∗
  ((ctrl + BitVec.ofNat 64 pos + 1#64) ↦ₛ List.replicate 7 0xff#8) ∗
  ((ctrl + BitVec.ofNat 64 pos + 8#64 + 1#64) ↦ₛ emptyCtrl4.drop (pos + 9))

private theorem singleCtrl4_take_eq (pos : Nat) (hpos : pos < 4) (tag : BitVec 8) :
    (singleCtrl4 pos tag).take pos = emptyCtrl4.take pos := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl

private theorem singleCtrl4_drop_eq (pos : Nat) (hpos : pos < 4) (tag : BitVec 8) :
    (singleCtrl4 pos tag).drop pos =
      tag :: (List.replicate 7 0xff#8 ++ (tag :: emptyCtrl4.drop (pos + 9))) := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem pointsToBytes_singleCtrl4_split (ctrl : BitVec 64) (pos : Nat) (hpos : pos < 4)
    (tag : BitVec 8) :
    (ctrl ↦ₛ singleCtrl4 pos tag) =
      ((ctrl + BitVec.ofNat 64 pos) ↦₈ tag) ∗
      ((ctrl + BitVec.ofNat 64 pos + 8#64) ↦₈ tag) ∗
      ctrl12RestAt ctrl pos := by
  have hlen : pos ≤ (singleCtrl4 pos tag).length := by simp; omega
  rw [pointsToBytes_take_drop ctrl pos (singleCtrl4 pos tag) hlen,
      singleCtrl4_take_eq pos hpos tag,
      singleCtrl4_drop_eq pos hpos tag,
      pointsToBytes_cons,
      pointsToBytes_append,
      pointsToBytes_cons]
  have hrep : (List.replicate 7 0xff#8).length = 7 := rfl
  have hadd8 : ctrl + BitVec.ofNat 64 pos + 1#64 + BitVec.ofNat 64 7 =
      ctrl + BitVec.ofNat 64 pos + 8#64 := by
    rw [BitVec.add_assoc (ctrl + BitVec.ofNat 64 pos)]
    rfl
  rw [hrep, hadd8]
  unfold ctrl12RestAt
  ac_rfl

theorem pointsToBytes_emptyCtrl4_split (ctrl : BitVec 64) (pos : Nat) (hpos : pos < 4) :
    (ctrl ↦ₛ emptyCtrl4) =
      ((ctrl + BitVec.ofNat 64 pos) ↦₈ 0xff#8) ∗
      ((ctrl + BitVec.ofNat 64 pos + 8#64) ↦₈ 0xff#8) ∗
      ctrl12RestAt ctrl pos := by
  have heq : emptyCtrl4 = singleCtrl4 pos 0xff#8 := by
    rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;> rfl
  rw [heq]
  exact pointsToBytes_singleCtrl4_split ctrl pos hpos 0xff#8

theorem pointsToBytes_32_eq_cells (a : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₆₄ loadGroupAt bs 0) ∗
      ((a + 8#64) ↦₆₄ loadGroupAt bs 8) ∗
      ((a + 16#64) ↦₆₄ loadGroupAt bs 16) ∗
      ((a + 24#64) ↦₆₄ loadGroupAt bs 24) := by
  have h0 : 0 + 8 ≤ bs.length := by omega
  have h8 : 8 + 8 ≤ bs.length := by omega
  have h16 : 16 + 8 ≤ bs.length := by omega
  have h24 : 24 + 8 ≤ bs.length := by omega
  have hd8 : (bs.drop 8).length = 24 := by simp [List.length_drop, hlen]
  have hd16 : (bs.drop 16).length = 16 := by simp [List.length_drop, hlen]
  have hd24 : (bs.drop 24).length = 8 := by simp [List.length_drop, hlen]
  rw [pointsToBytes_take_drop a 8 bs (by omega),
      pointsToBytes_take_drop (a + 8#64) 8 (bs.drop 8) (by omega),
      List.drop_drop,
      pointsToBytes_take_drop (a + 8#64 + 8#64) 8 (bs.drop 16) (by omega),
      List.drop_drop,
      pointsToBytes_take_drop (a + 8#64 + 8#64 + 8#64) 8 (bs.drop 24) (by omega),
      List.drop_drop]
  have hdrop32 : bs.drop 32 = [] := List.drop_eq_nil_of_le (by omega)
  have h0_eq := pointsToBytes_take8_eq_pointsTo64 a bs 0 h0
  simp only [List.drop_zero] at h0_eq
  have h8_eq := pointsToBytes_take8_eq_pointsTo64 (a + 8#64) bs 8 h8
  have h16_eq := pointsToBytes_take8_eq_pointsTo64 (a + 16#64) bs 16 h16
  have h24_eq := pointsToBytes_take8_eq_pointsTo64 (a + 24#64) bs 24 h24
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  simp only [Nat.reduceAdd, ha16, ha24, hdrop32, pointsToBytes_nil, sepConj_emp]
  rw [h0_eq, h8_eq, h16_eq, h24_eq,
      ← loadGroupAt_eq_pack64 bs 0 h0,
      ← loadGroupAt_eq_pack64 bs 8 h8,
      ← loadGroupAt_eq_pack64 bs 16 h16,
      ← loadGroupAt_eq_pack64 bs 24 h24]

theorem pointsTo8_pad7_eq_pointsTo64 (addr : BitVec 64) (b0 : BitVec 8)
    (pad : List (BitVec 8)) (hpad : pad.length = 7) :
    ((addr + 24#64) ↦₈ b0) ∗ ((addr + 25#64) ↦ₛ pad) =
      (addr + 24#64) ↦₆₄ loadGroupAt (b0 :: pad) 0 := by
  have hcons : ((addr + 24#64) ↦₈ b0) ∗ ((addr + 25#64) ↦ₛ pad) =
      ((addr + 24#64) ↦ₛ (b0 :: pad)) := by
    rw [pointsToBytes_cons, BitVec.add_assoc]
    rfl
  rw [hcons]
  have h8 : 0 + 8 ≤ (b0 :: pad).length := by simp [hpad]
  have htake : (b0 :: pad).take 8 = b0 :: pad := List.take_of_length_le (by simp [hpad])
  have h := pointsToBytes_take8_eq_pointsTo64 (addr + 24#64) (b0 :: pad) 0 h8
  simp only [List.drop_zero, htake] at h
  rw [h, ← loadGroupAt_eq_pack64 (b0 :: pad) 0 h8]

theorem pointsTo8_memRegion7_eq_pointsTo64 (a : BitVec 64) (dev : BitVec 8) :
    ((a + 24#64) ↦₈ dev) ∗ memRegion (a + 25#64) 7 =
      ∃∗ w : BitVec 64, ⌜w.truncate 8 = dev⌝ ∗ ((a + 24#64) ↦₆₄ w) := by
  have hL : IsBlock (((a + 24#64) ↦₈ dev) ∗ memRegion (a + 25#64) 7) (a + 24#64) 8
      (fun m => m.read8 (a + 24#64) = dev ∧ True) :=
    ((IsBlock.pointsTo8 (a + 24#64) dev).sepConj (IsBlock.memRegion (a + 25#64) 7)
      (by bv_arith) (by decide))
  have hR : IsBlock (∃∗ w : BitVec 64, ⌜w.truncate 8 = dev⌝ ∗ ((a + 24#64) ↦₆₄ w)) (a + 24#64) 8
      (fun m => ∃ w : BitVec 64, w.truncate 8 = dev ∧ m.read64 (a + 24#64) = w) :=
    IsBlock.sepExists fun w => IsBlock.pure_sepConj fun _ => IsBlock.pointsTo64 (a + 24#64) w
  refine IsBlock.eq hL hR fun m => ?_
  have htr : (m.read64 (a + 24#64)).truncate 8 = m.read8 (a + 24#64) := by
    simp only [Memory.read64]
    have h0 : a + 24#64 + 0#64 = a + 24#64 := by bv_omega
    rw [h0]
    generalize m.read8 (a + 24#64) = x0
    generalize m.read8 (a + 24#64 + 1#64) = x1
    generalize m.read8 (a + 24#64 + 2#64) = x2
    generalize m.read8 (a + 24#64 + 3#64) = x3
    generalize m.read8 (a + 24#64 + 4#64) = x4
    generalize m.read8 (a + 24#64 + 5#64) = x5
    generalize m.read8 (a + 24#64 + 6#64) = x6
    generalize m.read8 (a + 24#64 + 7#64) = x7
    bv_bits
  constructor
  · rintro ⟨h, -⟩
    exact ⟨m.read64 (a + 24#64), htr.trans h, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨htr.symm.trans hw, trivial⟩

def addrHeapAt (A : RustAlloc) (g : AddrGhost) : SepProp :=
  ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
  (g.name.ptr ↦ₛ g.name.bytes) ∗
  A.live g.name.ptr g.name.cap.toNat 1 ∗
  memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
    (g.name.cap.toNat - g.name.bytes.length)

theorem protocolAddressAt_eq_of_len36 (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64)
    (hlen36 : g.name.bytes.length = 36) :
    protocolAddressAt A g addr =
      (addr ↦₆₄ g.name.cap) ∗
      ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
      ((addr + 16#64) ↦₆₄ 36#64) ∗
      ((addr + 24#64) ↦₈ g.device) ∗
      memRegion (addr + 25#64) 7 ∗
      addrHeapAt A g := by
  have hvec :
      vecGhostAt A g.name addr =
        ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
        ((addr + 16#64) ↦₆₄ 36#64) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) := by
    unfold vecGhostAt vecU8At vecHeader
    have h1 :
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) ⊢
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) := by
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      simp only [hne, ↓reduceIte, hlen36] at hlen ⊢
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      exact Entails.of_eq (by ac_rfl)
    have h2 :
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) ⊢
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) := by
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      rw [sepConj_pure_left_comm]
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      simp only [hne, ↓reduceIte, hlen36]
      exact Entails.of_eq (by ac_rfl)
    exact ProofLib.sepProp_eq_of_entails h1 h2
  unfold protocolAddressAt addrHeapAt
  rw [hvec]
  ac_rfl

/-- The 3 inactive 64-byte buckets in a 4-bucket identity table when bucket `k < 4` is selected. -/
def buckets4OtherAt (ctrl : BitVec 64) (k : Nat) : SepProp :=
  match k with
  | 0 =>
    memRegion (bucketAddr ctrl 64 3) 64 ∗
    memRegion (bucketAddr ctrl 64 2) 64 ∗
    memRegion (bucketAddr ctrl 64 1) 64
  | 1 =>
    memRegion (bucketAddr ctrl 64 3) 64 ∗
    memRegion (bucketAddr ctrl 64 2) 64 ∗
    memRegion (bucketAddr ctrl 64 0) 64
  | 2 =>
    memRegion (bucketAddr ctrl 64 3) 64 ∗
    memRegion (bucketAddr ctrl 64 1) 64 ∗
    memRegion (bucketAddr ctrl 64 0) 64
  | _ =>
    memRegion (bucketAddr ctrl 64 2) 64 ∗
    memRegion (bucketAddr ctrl 64 1) 64 ∗
    memRegion (bucketAddr ctrl 64 0) 64

private theorem bucketAddr_64_3 (ctrl : BitVec 64) :
    ctrl - BitVec.ofNat 64 (4 * identityBucketStride) = bucketAddr ctrl 64 3 := rfl

private theorem bucketAddr_64_2 (ctrl : BitVec 64) :
    bucketAddr ctrl 64 3 + 64#64 = bucketAddr ctrl 64 2 := by
  unfold bucketAddr; bv_omega

private theorem bucketAddr_64_1 (ctrl : BitVec 64) :
    bucketAddr ctrl 64 2 + 64#64 = bucketAddr ctrl 64 1 := by
  unfold bucketAddr; bv_omega

private theorem bucketAddr_64_0 (ctrl : BitVec 64) :
    bucketAddr ctrl 64 1 + 64#64 = bucketAddr ctrl 64 0 := by
  unfold bucketAddr; bv_omega

theorem arrayAt_empty4_split_at (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    arrayAt (fun _ a => memRegion a identityBucketStride) identityBucketStride
      (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) (List.range 4).reverse =
      memRegion (bucketAddr ctrl 64 k) 64 ∗ buckets4OtherAt ctrl k := by
  change
    memRegion (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) 64 ∗
      (memRegion (ctrl - BitVec.ofNat 64 (4 * identityBucketStride) + 64#64) 64 ∗
        (memRegion (ctrl - BitVec.ofNat 64 (4 * identityBucketStride) + 64#64 + 64#64) 64 ∗
          (memRegion (ctrl - BitVec.ofNat 64 (4 * identityBucketStride) + 64#64 + 64#64 + 64#64) 64 ∗ emp))) = _
  rw [bucketAddr_64_3, bucketAddr_64_2, bucketAddr_64_1, bucketAddr_64_0, sepConj_emp]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    (simp only [buckets4OtherAt]; try ac_rfl)

theorem arrayAt_single4_split_at (ctrl : BitVec 64) (k : Nat) (hk : k < 4)
    (entryAt : BitVec 64 → SepProp) :
    arrayAt (fun i a => if i ∈ [k] then entryAt a else memRegion a identityBucketStride)
      identityBucketStride (ctrl - BitVec.ofNat 64 (4 * identityBucketStride))
      (List.range 4).reverse =
      entryAt (bucketAddr ctrl 64 k) ∗ buckets4OtherAt ctrl k := by
  change
    (if 3 ∈ [k] then entryAt (ctrl - BitVec.ofNat 64 (4 * identityBucketStride))
     else memRegion (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) 64) ∗
      ((if 2 ∈ [k] then entryAt (ctrl - BitVec.ofNat 64 (4 * identityBucketStride) + 64#64)
        else memRegion (ctrl - BitVec.ofNat 64 (4 * identityBucketStride) + 64#64) 64) ∗
        ((if 1 ∈ [k] then entryAt (ctrl - BitVec.ofNat 64 (4 * identityBucketStride) + 64#64 + 64#64)
          else memRegion (ctrl - BitVec.ofNat 64 (4 * identityBucketStride) + 64#64 + 64#64) 64) ∗
          ((if 0 ∈ [k] then entryAt (ctrl - BitVec.ofNat 64 (4 * identityBucketStride) + 64#64 + 64#64 + 64#64)
            else memRegion (ctrl - BitVec.ofNat 64 (4 * identityBucketStride) + 64#64 + 64#64 + 64#64) 64) ∗ emp))) = _
  rw [bucketAddr_64_3, bucketAddr_64_2, bucketAddr_64_1, bucketAddr_64_0, sepConj_emp]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    (simp only [List.mem_singleton, reduceCtorEq, ↓reduceIte, buckets4OtherAt]; try ac_rfl)

theorem ctrl_sub_lsl6_eq_bucketAddr_add_64 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - (BitVec.ofNat 64 k <<< 6) = bucketAddr ctrl 64 k + 64#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    (unfold bucketAddr; bv_omega)

theorem memRegion_32_of_cells (a : BitVec 64) (u0 u1 u2 u3 : BitVec 64) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) ⊢
      memRegion a 32 := by
  rw [FallibleWithCapacity.memRegion_32_cells a]
  exact Entails.sepExists_right u3 (Entails.sepExists_right u2
    (Entails.sepExists_right u1 (Entails.sepExists_right u0 (Entails.of_eq (by ac_rfl)))))

theorem pointsTo64_entails_pointsTo8_memRegion7 (a : BitVec 64) (w : BitVec 64) (dev : BitVec 8)
    (hw : w.truncate 8 = dev) :
    ((a + 24#64) ↦₆₄ w) ⊢ ((a + 24#64) ↦₈ dev) ∗ memRegion (a + 25#64) 7 := by
  rw [pointsTo8_memRegion7_eq_pointsTo64 a dev]
  exact Entails.sepExists_right w (Entails.pure_right hw (Entails.refl _))

theorem pointsTo8_memRegion7_entails_memRegion8 (a : BitVec 64) (dev : BitVec 8) :
    ((a + 24#64) ↦₈ dev) ∗ memRegion (a + 25#64) 7 ⊢ memRegion (a + 24#64) 8 := by
  have h := memRegion_split (a + 24#64) 1 7 (by decide)
  have h1 : (a + 24#64) + 1#64 = a + 25#64 := by bv_omega
  rw [show (1 : Nat) + 7 = 8 from rfl, show BitVec.ofNat 64 1 = 1#64 from rfl, h1, memRegion_one] at h
  rw [h]
  exact sepConj_mono_left (Entails.sepExists_right dev (Entails.refl _))

theorem memRegion_32_of_addr_cells (a : BitVec 64) (u0 u1 u2 : BitVec 64) (dev : BitVec 8) :
    (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
    ((a + 24#64) ↦₈ dev) ∗ memRegion (a + 25#64) 7 ⊢
      memRegion a 32 := by
  rw [memRegion_split a 24 8 (by decide),
      memRegion_split a 8 16 (by decide),
      memRegion_split (a + 8#64) 8 8 (by decide),
      memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h0 : (a ↦₆₄ u0) ⊢ (∃∗ v : BitVec 64, a ↦₆₄ v) := Entails.sepExists_right u0 (Entails.refl _)
  have h1 : ((a + 8#64) ↦₆₄ u1) ⊢ (∃∗ v : BitVec 64, (a + 8#64) ↦₆₄ v) :=
    Entails.sepExists_right u1 (Entails.refl _)
  have h2 : ((a + 16#64) ↦₆₄ u2) ⊢ (∃∗ v : BitVec 64, (a + 16#64) ↦₆₄ v) :=
    Entails.sepExists_right u2 (Entails.refl _)
  have h3 := pointsTo8_memRegion7_entails_memRegion8 a dev
  exact Entails.trans
    (sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 h3)))
    (Entails.of_eq (by ac_rfl))

theorem memRegion_33_split_for_none (sret : BitVec 64) :
    memRegion sret 33 =
      (∃∗ b0 : BitVec 8, (sret ↦₈ b0)) ∗ memRegion (sret + 1#64) 32 := by
  rw [memRegion_split sret 1 32 (by decide), memRegion_one]

theorem fold_optIdentityKeyAt_some (sret : BitVec 64) (keyBytes : List (BitVec 8))
    (hlen : keyBytes.length = 32) :
    (sret ↦₈ 1#8) ∗
    ((sret + 1#64) ↦₆₄ loadGroupAt keyBytes 0) ∗
    ((sret + 9#64) ↦₆₄ loadGroupAt keyBytes 8) ∗
    ((sret + 17#64) ↦₆₄ loadGroupAt keyBytes 16) ∗
    ((sret + 25#64) ↦₆₄ loadGroupAt keyBytes 24) ⊢
    optIdentityKeyAt sret (some keyBytes) := by
  unfold optIdentityKeyAt
  refine Entails.pure_right hlen ?_
  rw [pointsToBytes_32_eq_cells (sret + 1#64) keyBytes hlen]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem identityBucketEntryAt_eq_of_len36_32 (A : RustAlloc) (g : AddrGhost)
    (hlen36 : g.name.bytes.length = 36) (keyBytes : List (BitVec 8)) (hkey : keyBytes.length = 32)
    (a : BitVec 64) :
    identityBucketEntryAt A g keyBytes a =
      (a ↦₆₄ g.name.cap) ∗
      ((a + 8#64) ↦₆₄ g.name.ptr) ∗
      ((a + 16#64) ↦₆₄ 36#64) ∗
      ((a + 24#64) ↦₈ g.device) ∗
      memRegion (a + 25#64) 7 ∗
      addrHeapAt A g ∗
      ((a + 32#64) ↦₆₄ loadGroupAt keyBytes 0) ∗
      ((a + 40#64) ↦₆₄ loadGroupAt keyBytes 8) ∗
      ((a + 48#64) ↦₆₄ loadGroupAt keyBytes 16) ∗
      ((a + 56#64) ↦₆₄ loadGroupAt keyBytes 24) := by
  unfold identityBucketEntryAt
  rw [pure_sepConj_of_true hkey,
      protocolAddressAt_eq_of_len36 A g a hlen36,
      pointsToBytes_32_eq_cells (a + 32#64) keyBytes hkey]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem fold_table4SingleAt_of_empty (A : RustAlloc) (mp k0 k1 ctrl : BitVec 64)
    (pos : Nat) (hpos : pos < 4)
    (g : AddrGhost) (hlen36 : g.name.bytes.length = 36)
    (keyBytes : List (BitVec 8)) (hkey : keyBytes.length = 32)
    (hc0 : ctrl ≠ 0#64) (hc8 : ctrl.toNat % 8 = 0)
    (hcle : 4 * identityBucketStride ≤ ctrl.toNat) (hclt : ctrl.toNat + 12 < 2 ^ 64) :
    let hash := hashAddrBv k0 k1 g.name.bytes g.device
    let tag := h2Tag hash
    let bkt := bucketAddr ctrl 64 pos
    (mp ↦₆₄ ctrl) ∗
    ((mp + 8#64) ↦₆₄ 3#64) ∗
    ((mp + 16#64) ↦₆₄ 2#64) ∗
    ((mp + 24#64) ↦₆₄ 1#64) ∗
    ((mp + 32#64) ↦₆₄ k0) ∗
    ((mp + 40#64) ↦₆₄ k1) ∗
    A.live (ctrl - BitVec.ofNat 64 (4 * identityBucketStride))
      (tableAllocSize 4 identityBucketStride) (asm% hashbrownTableAlign) ∗
    ((ctrl + BitVec.ofNat 64 pos) ↦₈ tag) ∗
    ((ctrl + BitVec.ofNat 64 pos + 8#64) ↦₈ tag) ∗
    ctrl12RestAt ctrl pos ∗
    (bkt ↦₆₄ g.name.cap) ∗
    ((bkt + 8#64) ↦₆₄ g.name.ptr) ∗
    ((bkt + 16#64) ↦₆₄ 36#64) ∗
    ((bkt + 24#64) ↦₈ g.device) ∗
    memRegion (bkt + 25#64) 7 ∗
    addrHeapAt A g ∗
    ((bkt + 32#64) ↦₆₄ loadGroupAt keyBytes 0) ∗
    ((bkt + 40#64) ↦₆₄ loadGroupAt keyBytes 8) ∗
    ((bkt + 48#64) ↦₆₄ loadGroupAt keyBytes 16) ∗
    ((bkt + 56#64) ↦₆₄ loadGroupAt keyBytes 24) ∗
    buckets4OtherAt ctrl pos ⊢
    table4SingleAt A identityBucketStride mp k0 k1 pos
      g.name.bytes g.device (identityBucketEntryAt A g keyBytes) := by
  intro hash tag bkt
  unfold table4SingleAt table4At
  refine Entails.pure_right hpos ?_
  refine Entails.sepExists_right ctrl ?_
  have hlen : ([pos] : List Nat).length = 4 → (2#64 : BitVec 64) = 0#64 := nofun
  have hmir := ctrlMirrorInv_singleCtrl4 pos tag
  have hfull := fullBucketsInv_singleCtrl4 pos hpos tag (h2Tag_msb hash)
  refine Entails.pure_right ⟨hc0, hc8, hcle, hclt, hlen, hmir, hfull⟩ ?_
  have h40 : mp + asm64% tableHasherOff + 8#64 = mp + 40#64 := by bv_omega
  rw [h40,
      pointsToBytes_singleCtrl4_split ctrl pos hpos tag,
      arrayAt_single4_split_at ctrl pos hpos (identityBucketEntryAt A g keyBytes),
      identityBucketEntryAt_eq_of_len36_32 A g hlen36 keyBytes hkey bkt]
  exact Entails.of_eq (by ac_rfl)

theorem fold_table4SingleAt_of_hit (A : RustAlloc) (mp k0 k1 ctrl : BitVec 64)
    (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (oldG : AddrGhost) (hlen36 : oldG.name.bytes.length = 36)
    (newKeyBytes : List (BitVec 8)) (hkey : newKeyBytes.length = 32)
    (hc0 : ctrl ≠ 0#64) (hc8 : ctrl.toNat % 8 = 0)
    (hcle : 4 * identityBucketStride ≤ ctrl.toNat) (hclt : ctrl.toNat + 12 < 2 ^ 64) :
    let hash := hashAddrBv k0 k1 oldG.name.bytes oldG.device
    let cbs := singleCtrl4 k (h2Tag hash)
    let bkt := bucketAddr ctrl 64 k
    (mp ↦₆₄ ctrl) ∗
    ((mp + 8#64) ↦₆₄ 3#64) ∗
    ((mp + 16#64) ↦₆₄ 2#64) ∗
    ((mp + 24#64) ↦₆₄ 1#64) ∗
    ((mp + 32#64) ↦₆₄ k0) ∗
    ((mp + 40#64) ↦₆₄ k1) ∗
    A.live (ctrl - BitVec.ofNat 64 (4 * identityBucketStride))
      (tableAllocSize 4 identityBucketStride) (asm% hashbrownTableAlign) ∗
    ((ctrl + BitVec.ofNat 64 pos) ↦₆₄ loadGroupAt cbs pos) ∗
    (ctrl ↦ₛ cbs.take pos) ∗
    ((ctrl + BitVec.ofNat 64 (pos + 8)) ↦ₛ cbs.drop (pos + 8)) ∗
    (bkt ↦₆₄ oldG.name.cap) ∗
    ((bkt + 8#64) ↦₆₄ oldG.name.ptr) ∗
    ((bkt + 16#64) ↦₆₄ 36#64) ∗
    ((bkt + 24#64) ↦₈ oldG.device) ∗
    memRegion (bkt + 25#64) 7 ∗
    addrHeapAt A oldG ∗
    ((bkt + 32#64) ↦₆₄ loadGroupAt newKeyBytes 0) ∗
    ((bkt + 40#64) ↦₆₄ loadGroupAt newKeyBytes 8) ∗
    ((bkt + 48#64) ↦₆₄ loadGroupAt newKeyBytes 16) ∗
    ((bkt + 56#64) ↦₆₄ loadGroupAt newKeyBytes 24) ∗
    buckets4OtherAt ctrl k ⊢
    table4SingleAt A identityBucketStride mp k0 k1 k
      oldG.name.bytes oldG.device (identityBucketEntryAt A oldG newKeyBytes) := by
  intro hash cbs bkt
  unfold table4SingleAt table4At
  refine Entails.pure_right hk ?_
  refine Entails.sepExists_right ctrl ?_
  have hlen : ([k] : List Nat).length = 4 → (2#64 : BitVec 64) = 0#64 := nofun
  have hmir := ctrlMirrorInv_singleCtrl4 k (h2Tag hash)
  have hfull := fullBucketsInv_singleCtrl4 k hk (h2Tag hash) (h2Tag_msb hash)
  refine Entails.pure_right ⟨hc0, hc8, hcle, hclt, hlen, hmir, hfull⟩ ?_
  have h40 : mp + asm64% tableHasherOff + 8#64 = mp + 40#64 := by bv_omega
  have hcbs_len : cbs.length = 12 := by simp [cbs]
  rw [h40,
      pointsToBytes_ctrl12_split_at ctrl cbs hcbs_len pos hpos,
      arrayAt_single4_split_at ctrl k hk (identityBucketEntryAt A oldG newKeyBytes),
      identityBucketEntryAt_eq_of_len36_32 A oldG hlen36 newKeyBytes hkey bkt]
  exact Entails.of_eq (by ac_rfl)

theorem stackAt_hashMapIdInsert (sp : BitVec 64) :
    stackAt sp hashMapIdInsertStack =
      stackAt (sp - 224#64) 16704 ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 224#64) ↦₆₄ s0) ∗ ((sp - 216#64) ↦₆₄ s1) ∗
        ((sp - 208#64) ↦₆₄ s2) ∗ ((sp - 200#64) ↦₆₄ s3) ∗
        ((sp - 192#64) ↦₆₄ s4) ∗ ((sp - 184#64) ↦₆₄ s5)) ∗
      memRegion (sp - 176#64) 64 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64,
        ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗
        ((sp - 96#64) ↦₆₄ v2) ∗ ((sp - 88#64) ↦₆₄ v3) ∗
        ((sp - 80#64) ↦₆₄ v4) ∗ ((sp - 72#64) ↦₆₄ v5) ∗
        ((sp - 64#64) ↦₆₄ v6) ∗ ((sp - 56#64) ↦₆₄ v7) ∗
        ((sp - 48#64) ↦₆₄ v8) ∗ ((sp - 40#64) ↦₆₄ v9) ∗
        ((sp - 32#64) ↦₆₄ v10) ∗ ((sp - 24#64) ↦₆₄ v11) ∗
        ((sp - 16#64) ↦₆₄ v12) ∗ ((sp - 8#64) ↦₆₄ v13)) := by
  have htop := stackAt_split_cells sp 16816 14 (by decide)
  change stackAt sp hashMapIdInsertStack = stackAt (sp - 112#64) 16816 ∗ cells (sp - 112#64) 14 at htop
  have hmid : stackAt (sp - 112#64) 16816 =
      stackAt (sp - 176#64) 16752 ∗ memRegion (sp - 176#64) 64 := by
    change memRegion (sp - 112#64 - 16816#64) 16816 =
      memRegion (sp - 176#64 - 16752#64) 16752 ∗ memRegion (sp - 176#64) 64
    have ha1 : sp - 112#64 - 16816#64 = sp - 176#64 - 16752#64 := by bv_omega
    have ha2 : (sp - 176#64 - 16752#64) + 16752#64 = sp - 176#64 := by bv_omega
    have hsp := memRegion_split (sp - 176#64 - 16752#64) 16752 64 (by decide)
    rw [show (16752 : Nat) + 64 = 16816 by decide,
        show BitVec.ofNat 64 16752 = 16752#64 from rfl, ha2] at hsp
    rw [ha1, hsp]
  have hbot := stackAt_split_cells (sp - 176#64) 16704 6 (by decide)
  have ha3 : sp - 176#64 - BitVec.ofNat 64 (8 * 6) = sp - 224#64 := by bv_omega
  rw [show 16704 + 8 * 6 = 16752 by decide, ha3] at hbot
  have hc6 : cells (sp - 224#64) 6 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 224#64) ↦₆₄ s0) ∗ ((sp - 216#64) ↦₆₄ s1) ∗
        ((sp - 208#64) ↦₆₄ s2) ∗ ((sp - 200#64) ↦₆₄ s3) ∗
        ((sp - 192#64) ↦₆₄ s4) ∗ ((sp - 184#64) ↦₆₄ s5)) := by
    cells_unfold
  have hc14 : cells (sp - 112#64) 14 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64,
        ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗
        ((sp - 96#64) ↦₆₄ v2) ∗ ((sp - 88#64) ↦₆₄ v3) ∗
        ((sp - 80#64) ↦₆₄ v4) ∗ ((sp - 72#64) ↦₆₄ v5) ∗
        ((sp - 64#64) ↦₆₄ v6) ∗ ((sp - 56#64) ↦₆₄ v7) ∗
        ((sp - 48#64) ↦₆₄ v8) ∗ ((sp - 40#64) ↦₆₄ v9) ∗
        ((sp - 32#64) ↦₆₄ v10) ∗ ((sp - 24#64) ↦₆₄ v11) ∗
        ((sp - 16#64) ↦₆₄ v12) ∗ ((sp - 8#64) ↦₆₄ v13)) := by
    cells_unfold
  rw [htop, hmid, hbot, hc6, hc14]
  ac_rfl

theorem fold_stackAt_hashMapIdInsert (sp : BitVec 64)
    (s0 s1 s2 s3 s4 s5 : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : BitVec 64) :
    stackAt (sp - 224#64) 16704 ∗
    ((sp - 224#64) ↦₆₄ s0) ∗ ((sp - 216#64) ↦₆₄ s1) ∗
    ((sp - 208#64) ↦₆₄ s2) ∗ ((sp - 200#64) ↦₆₄ s3) ∗
    ((sp - 192#64) ↦₆₄ s4) ∗ ((sp - 184#64) ↦₆₄ s5) ∗
    memRegion (sp - 176#64) 64 ∗
    ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗
    ((sp - 96#64) ↦₆₄ v2) ∗ ((sp - 88#64) ↦₆₄ v3) ∗
    ((sp - 80#64) ↦₆₄ v4) ∗ ((sp - 72#64) ↦₆₄ v5) ∗
    ((sp - 64#64) ↦₆₄ v6) ∗ ((sp - 56#64) ↦₆₄ v7) ∗
    ((sp - 48#64) ↦₆₄ v8) ∗ ((sp - 40#64) ↦₆₄ v9) ∗
    ((sp - 32#64) ↦₆₄ v10) ∗ ((sp - 24#64) ↦₆₄ v11) ∗
    ((sp - 16#64) ↦₆₄ v12) ∗ ((sp - 8#64) ↦₆₄ v13) ⊢
    stackAt sp hashMapIdInsertStack := by
  rw [stackAt_hashMapIdInsert sp]
  have hs :
      (((sp - 224#64) ↦₆₄ s0) ∗ ((sp - 216#64) ↦₆₄ s1) ∗
       ((sp - 208#64) ↦₆₄ s2) ∗ ((sp - 200#64) ↦₆₄ s3) ∗
       ((sp - 192#64) ↦₆₄ s4) ∗ ((sp - 184#64) ↦₆₄ s5)) ⊢
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 224#64) ↦₆₄ s0) ∗ ((sp - 216#64) ↦₆₄ s1) ∗
        ((sp - 208#64) ↦₆₄ s2) ∗ ((sp - 200#64) ↦₆₄ s3) ∗
        ((sp - 192#64) ↦₆₄ s4) ∗ ((sp - 184#64) ↦₆₄ s5)) :=
    Entails.sepExists_right s0 (Entails.sepExists_right s1 (Entails.sepExists_right s2
      (Entails.sepExists_right s3 (Entails.sepExists_right s4 (Entails.sepExists_right s5 (Entails.refl _))))))
  have hv :
      (((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗
       ((sp - 96#64) ↦₆₄ v2) ∗ ((sp - 88#64) ↦₆₄ v3) ∗
       ((sp - 80#64) ↦₆₄ v4) ∗ ((sp - 72#64) ↦₆₄ v5) ∗
       ((sp - 64#64) ↦₆₄ v6) ∗ ((sp - 56#64) ↦₆₄ v7) ∗
       ((sp - 48#64) ↦₆₄ v8) ∗ ((sp - 40#64) ↦₆₄ v9) ∗
       ((sp - 32#64) ↦₆₄ v10) ∗ ((sp - 24#64) ↦₆₄ v11) ∗
       ((sp - 16#64) ↦₆₄ v12) ∗ ((sp - 8#64) ↦₆₄ v13)) ⊢
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64,
        ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₆₄ v1) ∗
        ((sp - 96#64) ↦₆₄ v2) ∗ ((sp - 88#64) ↦₆₄ v3) ∗
        ((sp - 80#64) ↦₆₄ v4) ∗ ((sp - 72#64) ↦₆₄ v5) ∗
        ((sp - 64#64) ↦₆₄ v6) ∗ ((sp - 56#64) ↦₆₄ v7) ∗
        ((sp - 48#64) ↦₆₄ v8) ∗ ((sp - 40#64) ↦₆₄ v9) ∗
        ((sp - 32#64) ↦₆₄ v10) ∗ ((sp - 24#64) ↦₆₄ v11) ∗
        ((sp - 16#64) ↦₆₄ v12) ∗ ((sp - 8#64) ↦₆₄ v13)) :=
    Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
        (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
          (Entails.sepExists_right v9 (Entails.sepExists_right v10 (Entails.sepExists_right v11
            (Entails.sepExists_right v12 (Entails.sepExists_right v13 (Entails.refl _))))))))))))))
  have h1 := sepConj_mono (Entails.refl (stackAt (sp - 224#64) 16704))
    (sepConj_mono hs (sepConj_mono (Entails.refl (memRegion (sp - 176#64) 64)) hv))
  exact Entails.trans (Entails.of_eq (by ac_rfl)) h1

theorem hashbrown_bcmp_ok_at {A : RustAlloc} {b : BitVec 64} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "bcmp")) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr name + BitVec.ofNat 64 k)
      e2eBcmpSpec :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "bcmp")
    hHooks.bcmp

theorem hashbrown_dealloc_ok_at {A : RustAlloc} {b : BitVec 64} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "__rustc::__rust_dealloc")) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_dealloc")
    hHooks.alloc.dealloc

end HashMapIdInsert

end CryptoVerification.E2E.InMem.HashbrownBin
