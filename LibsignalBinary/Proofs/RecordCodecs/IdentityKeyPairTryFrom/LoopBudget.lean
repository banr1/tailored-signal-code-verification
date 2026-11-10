/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Loop
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopError
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMerge
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMergeBudget
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopVarint
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopVarintBudget
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded `IdentityKeyPair::try_from` Decode Loop

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` proof of the
`IdentityKeyPairStructure` protobuf decode loop (`+108 .. +728`) and prologue on Block `84`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
  hiding rustDeallocExternSpecWithStack decodeErrorFromSpecWithStack
    decodeErrorPushExternSpecWithStack decodeVarintSlowSpecWithStack
open CryptoVerification.LibsignalTripleRatchet.Prost
  hiding dropDecodeErrorSpecGen dropDecodeErrorSpecX decodeVarintSliceSpecGen decodeVarintSliceSpecX memRegion_split
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWP.done -> sepWPDoneWire
open scoped CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary (DecodeGhost sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
  hiding ikpLoopCommonPlaced ikpExitPostPlaced decodeErrorFrom_600_placed_wp
    decodeVarintSlice_168_placed_cps decodeVarintSlow_304_placed_cps
open scoped CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PortDepsPlaced RecordCodecLoopEnv noPanicQp)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget
  (ikpExitPostPlaced ikpLoopCommonPlaced)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopMergeBudget
  (decodeErrorFrom_600_placed_wp decodeVarintSlice_168_placed_cps)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopVarintBudget
  (decodeVarintSlow_304_placed_cps)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section LoopStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_lp (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_lp (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem pc_setMem_lp (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem status_setMem_lp (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setMem_lp (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPState_lp (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_advancePC_lp (s : State) : s.advancePC.sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg64_gpr_lp (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg32_gpr_lp (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg_gpr_lp (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by
  cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_lp (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_lp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPState_lp (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_lp (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_lp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPState_lp (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_lp (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_lp (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPState_lp (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end LoopStateSimp

theorem decodeVarintMulti_148_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 148#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64) (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hne : bs ≠ []) (hlen : bs.length < 2 ^ 63)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_84).base + 220#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 → s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x20 = key →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s1)
        (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr bs
          (IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hnone : decodeVarint bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr bs ∗
        ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s)
      (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr bs
        (IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned
  have _hx1' : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have _hx2' : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have _hlen_pos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hlen64 : bs.length < 2 ^ 64 := by omega
  by_cases hlen11 : 11 ≤ bs.length
  · have _hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_true_eq]; omega
    refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (168)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    refine SepWPp.mono_pre ?_
      (decodeVarintSlice_168_placed_cps d (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
          (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
          (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
          (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
          (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        hlen (Or.inl hlen11) hFit hcont hnone)
    apply entails_of_eq; unfold ikpLoopCommonPlaced
    simp only [arm64_norm]
  · have _hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_false_iff_not]; omega
    have hlast_addr :
        ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) = ptr + BitVec.ofNat 64 (bs.length - 1) := by
      have heq : bs.length = (bs.length - 1) + 1 := by omega
      have h1_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (bs.length - 1) + 1#64 := by
        conv_lhs => rw [heq]; exact BitVec.ofNat_add (bs.length - 1) 1
      rw [h1_eq]; bv_omega
    by_cases hlast : (bs.getLast hne).toNat ≤ 0x7F
    · have _hbit31 := (signExtend32_bit31_eq_false_iff (bs.getLast hne)).mpr hlast
      unfold sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (168)) ?_; wp_steps
      refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
      refine SepWPp.mono_pre ?_
        (decodeVarintSlice_168_placed_cps d (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
            (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
            (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
            (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
            (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          hlen (Or.inr ⟨hne, hlast⟩) hFit hcont hnone)
      apply entails_of_eq; unfold sliceCursorAt ikpLoopCommonPlaced
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [arm64_norm, sepConj_assoc]
    · have _hbit31 := (signExtend32_bit31_eq_true_iff (bs.getLast hne)).mpr (by omega)
      unfold sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (304)) ?_; wp_steps
      refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
      refine SepWPp.mono_pre ?_
        (decodeVarintSlow_304_placed_cps d (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
            (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
            (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
            (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
            (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) hlen hFit hcont hnone)
      apply entails_of_eq; unfold sliceCursorAt ikpLoopCommonPlaced
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [arm64_norm, sepConj_assoc]

theorem decodeVarint_124_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 124#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64) (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint (b0 :: bs1) = some (key, rest) →
      s1.pc = (blkPl_84).base + 220#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      s1.readReg64 .x23 = sp' + 32#64 → s1.readReg64 .x22 = sp' + 40#64 →
      s1.readReg64 .x20 = key →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr (b0 :: bs1) rest ∗
          ikpLoopCommonPlaced A lim st sp' x.ret (b0 :: bs1).length m s1)
        (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr (b0 :: bs1)
          (IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hnone : decodeVarint (b0 :: bs1) = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommonPlaced A lim st sp' x.ret (b0 :: bs1).length m s)
      (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr (b0 :: bs1)
        (IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned
  have _hx23' : s.readReg64 (Reg.gpr 23#5) = sp' + 32#64 := hx23
  have _hx22' : s.readReg64 (Reg.gpr 22#5) = sp' + 40#64 := hx22
  have _hx2' : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (b0 :: bs1).length := hx2
  by_cases hb0 : b0.toNat ≤ 0x7F
  · have _hbit63 := (signExtend64_bit63_eq_false_iff b0).mpr hb0
    have hd := decodeVarint_cons_of_le b0 bs1 hb0
    have hsub1 : BitVec.ofNat 64 (bs1.length + 1) - 1#64 = BitVec.ofNat 64 bs1.length := by
      have h1_eq : BitVec.ofNat 64 (bs1.length + 1) = BitVec.ofNat 64 bs1.length + 1#64 :=
        BitVec.ofNat_add bs1.length 1
      rw [h1_eq]; bv_omega
    unfold sliceCursorAt ikpLoopCommonPlaced; rw [pointsToBytes_cons ptr b0 bs1]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (220)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (220))
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    have hse := signExtend64_eq_zeroExtend64_of_le b0 hb0
    refine SepWPp.mono_pre ?_
      (hcont (b0.zeroExtend 64) bs1 _ hd (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
          (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
          (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
          (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
          (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) (by simp [*, arm64_norm]))
    apply entails_of_eq; unfold sliceCursorAfter ikpLoopCommonPlaced
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [List.length_cons, Nat.add_sub_cancel_left, hsub1, arm64_norm, sepConj_assoc]
    sep_ac_rfl
  · have _hbit63 := (signExtend64_bit63_eq_true_iff b0).mpr (by omega)
    unfold sliceCursorAt; rw [pointsToBytes_cons ptr b0 bs1]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (148)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    refine SepWPp.mono_pre ?_
      (decodeVarintMulti_148_placed_cps d (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
          (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
          (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
          (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
          (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (List.cons_ne_nil b0 bs1) hlen hFit hcont hnone)
    apply entails_of_eq; unfold sliceCursorAt ikpLoopCommonPlaced
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [arm64_norm, sepConj_assoc]

theorem decodeKey_220_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {key : BitVec 64} {bs rest : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (blkPl_84).base + 220#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s) (hx20 : s.readReg64 .x20 = key)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (tag : Nat) (wt : WireType) (s1 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (blkPl_84).base + 248#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
          ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s1)
        (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr bs
          (IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hnone : decodeKey bs = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗
        ikpLoopCommonPlaced A lim st sp' x.ret bs.length m s)
      (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr bs
        (IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have _hsp_eq := hregs.base.sp; have _hsp_align := hregs.base.spAligned
  have _hx20' : s.readReg64 (Reg.gpr 20#5) = key := hx20
  have _hx29' : s.readReg64 (Reg.gpr 29#5) = sp' + 144#64 := hregs.x29
  have _hx24' : s.readReg64 (Reg.gpr 24#5) = speWord 9 := hregs.x24
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte]
    have _hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    unfold ikpLoopCommonPlaced; rw [ikpMem48_split_96_104_112 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (600)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (600))
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    have hcur := sliceCursorAfter_entails_memRegion (sp' + 32#64) ptr bs rest
    have hm40 := ikpPointsTo64_104_mem32_entails_mem40 sp' key
    refine SepWPp.mono_pre ?_
      (decodeErrorFrom_600_placed_wp d (x := x) (st := st) (fuel := fuel) (maxLen := maxLen)
        (mErr := m) (w0 := w0)
        (hnone hdk)
        (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
          (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
          (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
          (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
          (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, KindNoHeap, speWord, arm64_norm]) hFit)
    refine Entails.trans ?_
      (show memRegion sp' 32 ∗ (memRegion (sp' + 32#64) 16 ∗ (ptr ↦ₛ bs)) ∗
          ikpStructOf A.repAlloc (sp' + 48#64) m ∗ ((sp' + 96#64) ↦₆₄ w0) ∗
          memRegion (sp' + 104#64) 40 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
          memRegion x.ret 72 ∗ lsLogOff ∗ A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100) ⊢ _
        by apply entails_of_eq; sep_ac_rfl)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono hcur
        (sepConj_mono (ikpStructLoopOf_entails_of A.repAlloc (sp' + 48#64) bs.length m)
          (sepConj_mono_right (sepConj_mono_left hm40)))))
    apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have _hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by
        unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt]
      have hge6 : 6 ≤ key.toNat % 8 :=
        (WireType.ofNat?_eq_none_iff (key.toNat % 8) (by omega)).mp hwt
      have _hbcs := key_and7_ule6_of_ge key hge6
      unfold ikpLoopCommonPlaced; rw [ikpMem48_split_96_104_112 sp']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
      refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (600)) ?_
      wp_steps_sync_pool ((blkPl_84).base + bv% (600))
      refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
      have hcur := sliceCursorAfter_entails_memRegion (sp' + 32#64) ptr bs rest
      have hm40 := ikpPointsTo64_104_mem32_entails_mem40 sp' (key &&& 7#64)
      refine SepWPp.mono_pre ?_
        (decodeErrorFrom_600_placed_wp d (x := x) (st := st) (fuel := fuel) (maxLen := maxLen)
          (mErr := m) (w0 := w0)
          (hnone hdk)
          (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
            (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
            (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
            (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
            (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, KindNoHeap, arm64_norm]) hFit)
      refine Entails.trans ?_
        (show memRegion sp' 32 ∗ (memRegion (sp' + 32#64) 16 ∗ (ptr ↦ₛ bs)) ∗
            ikpStructOf A.repAlloc (sp' + 48#64) m ∗ ((sp' + 96#64) ↦₆₄ w0) ∗
            memRegion (sp' + 104#64) 40 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
            memRegion x.ret 72 ∗ lsLogOff ∗ A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100) ⊢ _
          by apply entails_of_eq; sep_ac_rfl)
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono hcur
          (sepConj_mono (ikpStructLoopOf_entails_of A.repAlloc (sp' + 48#64) bs.length m)
            (sepConj_mono_right (sepConj_mono_left hm40)))))
      apply entails_of_eq; simp only [arm64_norm]; sep_ac_rfl
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := WireType.lt_six_of_ofNat?_eq_some hwt
      have _hbcs := key_and7_ule6_of_lt key hlt6
      by_cases htag0 : key.toNat / 8 < 1
      · have hdk : decodeKey bs = none := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have _hcbz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
        unfold ikpLoopCommonPlaced
        rw [ikpMem48_split8 sp', ProofLib.memRegion_eight (sp' + 96#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_pre fun w0 => ?_
        refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (600)) ?_
        wp_steps_sync_pool ((blkPl_84).base + bv% (600))
        refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
        have hcur := sliceCursorAfter_entails_memRegion (sp' + 32#64) ptr bs rest
        refine SepWPp.mono_pre ?_
          (decodeErrorFrom_600_placed_wp d (x := x) (st := st) (fuel := fuel) (maxLen := maxLen)
            (mErr := m) (w0 := w0)
            (hnone hdk)
            (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
              (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
              (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
              (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
              (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
            (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (by simp [*, KindNoHeap, speWord, arm64_norm]) hFit)
        refine Entails.trans ?_
          (show memRegion sp' 32 ∗ (memRegion (sp' + 32#64) 16 ∗ (ptr ↦ₛ bs)) ∗
              ikpStructOf A.repAlloc (sp' + 48#64) m ∗ ((sp' + 96#64) ↦₆₄ w0) ∗
              memRegion (sp' + 104#64) 40 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
              memRegion x.ret 72 ∗ lsLogOff ∗ A.pool lim st _ ∗ stackAt sp' (skipFieldStackX 100) ⊢ _
            by apply entails_of_eq; sep_ac_rfl)
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono hcur
            (sepConj_mono_left (ikpStructLoopOf_entails_of A.repAlloc (sp' + 48#64) bs.length m))))
        apply entails_of_eq; sep_ac_rfl
      · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have _hcbz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
        refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := (blkPl_84).base + bv% (248)) ?_; wp_steps
        refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
        have htag_eq := key_tag32_zeroExtend64_eq key hkey_lt
        have hand7_eq := key_and7_eq_wt key hwt
        refine SepWPp.mono_pre ?_
          (hcont (key.toNat / 8) wt _ hdk (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
            (hregs.of_steps hcrl1 (by simp [*, hregs.base.sp, arm64_norm])
              (by simp [*, hregs.base.trace, arm64_norm]) (by simp [*, hregs.base.x26, arm64_norm])
              (by simp [*, hregs.base.x27, arm64_norm]) (by simp [*, hregs.base.x28, arm64_norm])
              (by simp [*, hregs.x29, arm64_norm]) (by simp [*, hregs.x19, arm64_norm])
              (by simp [*, hregs.x21, arm64_norm]) (by simp [*, hregs.x24, arm64_norm]))
            (by simp [*, arm64_norm]) (by simpa [arm64_norm] using htag_eq))
        apply entails_of_eq; unfold ikpLoopCommonPlaced
        simp only [arm64_norm]

theorem decodeKey_124_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 124#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64) (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hFit : FitsEnv M lim st (RecordCodecLoopEnv (fuel + 1) maxLen))
    (hcont : ∀ (tag : Nat) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) →
      s1.pc = (blkPl_84).base + 248#64 → s1.status = .Running →
      IkpLoopRegsPlaced s0 sp' x.ret s1 →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s1
        (sliceCursorAfter (sp' + 32#64) ptr (b0 :: bs1) rest ∗
          ikpLoopCommonPlaced A lim st sp' x.ret (b0 :: bs1).length m s1)
        (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr (b0 :: bs1)
          (IdentityKeyPair.tryFrom x.bytes))
        (noPanicQp s0))
    (hnone : decodeKey (b0 :: bs1) = none →
      IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding) :
    SepWPp (lsProg_84 H) ((blkPl_84).base + 812#64) s
      (sliceCursorAt (sp' + 32#64) ptr (b0 :: bs1) ∗
        ikpLoopCommonPlaced A lim st sp' x.ret (b0 :: bs1).length m s)
      (ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' x.ret ptr (b0 :: bs1)
        (IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) :=
  decodeVarint_124_placed_cps d hpc hrun hregs hx23 hx22 hx2 hlen hFit
    (fun _key rest s1 hdv hpc1 hrun1 hregs1 _hx23_1 _hx22_1 hx20_1 =>
      decodeKey_220_placed_cps d hdv hpc1 hrun1 hregs1 hx20_1 hFit
        (fun tag wt s2 hdk => hcont tag wt rest s2 hdk)
        hnone)
    (fun hdv_none => hnone (by simp [decodeKey, hdv_none]))

end LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopBudget
