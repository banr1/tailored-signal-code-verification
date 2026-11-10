/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.Layout
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace CliKpkGetPollNorm

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_append_lo (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem extractLsb_append_hi (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[local arm64_norm ↓, local wp_norm ↓]
theorem zext32_trunc32 (u : BitVec 32) :
    (u.zeroExtend 64).truncate 32 = u := by
  bv_bits

end CliKpkGetPollNorm

open CliKpkGetPollNorm

theorem bind_sepWPp_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : let st := s; SepWPp prog ret st P Q Qp) :
    SepWPp prog ret s P Q Qp := h

theorem bind_sepWP_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

/-! ## Branch & arithmetic discharge lemmas -/

theorem sp_sub_432_spAligned {s0 s : State} (hal0 : s0.spAligned = true)
    (hsp : s.sp = s0.sp - 432#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp] at hal0 ⊢
  revert hal0
  generalize s0.sp = p
  bv_bits

theorem ofNat_len_ne_zero {n : Nat} (h0 : 0 < n) (hhi : n < 2 ^ 32) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  simp at ht
  omega

private theorem addWithCarry64_z_false {w0 : BitVec 64} (hw0 : w0.toNat < 2 ^ 63) :
    (AddWithCarry64 w0 1#64 false).2.z = false := by
  dsimp only [AddWithCarry64]
  apply beq_eq_false_iff_ne.mpr
  intro h
  have ht := congrArg BitVec.toNat h
  simp at ht
  omega

theorem cmn_lt63_eq_false {w0 : BitVec 64} (hw0 : w0.toNat < 2 ^ 63) :
    ConditionHolds CondCode.EQ (AddWithCarry64 w0 1#64 false).2 = false := by
  simp only [ConditionHolds, addWithCarry64_z_false hw0]

theorem cmn_lt63_ne_true {w0 : BitVec 64} (hw0 : w0.toNat < 2 ^ 63) :
    ConditionHolds CondCode.NE (AddWithCarry64 w0 1#64 false).2 = true := by
  simp only [ConditionHolds, addWithCarry64_z_false hw0, Bool.not_false]

theorem add1_lt63_beq_zero {w0 : BitVec 64} (hw0 : w0.toNat < 2 ^ 63) :
    (w0 + 1#64 == 0#64) = false := by
  apply beq_eq_false_iff_ne.mpr
  bv_omega

theorem add1_lt63_bne_zero {w0 : BitVec 64} (hw0 : w0.toNat < 2 ^ 63) :
    (w0 + 1#64 != 0#64) = true := by
  apply bne_iff_ne.mpr
  bv_omega

/-! ## `SepWPp` panic predicate and `Spec.inImage` call combinator -/

def KpkPanicAllow (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R

theorem kpkPanicAllow_of_eq {s0 sf : State} {P_f : SepProp}
    (h : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    KpkPanicAllow s0 sf P_f :=
  fun _ hm => allowPanic_panicked h hm

theorem kpk_panic_of_trace {s0 s sf : State} {R' : SepProp}
    (htr : s.trace = s0.trace)
    (hp : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R') :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp.1 with ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

theorem kpk_call_inImage {prog : Program} {img : Obj.Image} {ret : BitVec 64}
    {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {α : Type} {callee_pc ret_pc : BitVec 64} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hnext : ∀ sf : State,
      ImgCallInv img sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (KpkPanicAllow s0)) :
    SepWPp prog ret s P Q (KpkPanicAllow s0) := by
  refine SepWPp.call_wpp_frozen hcall (x := x) (F := F) hinv.1 hinv.2 hpc hrun hsp hlr ?_ ?_ ?_ ?_ ?_
  · intro R hm
    have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
      Satisfies.mono (sepConj_mono_left hP) hm
    dsimp only [Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, by simpa only [sepConj_assoc] using hm_pre⟩
  · intro sf code R' hex he
    exact hexit sf code R' hex he
  · rintro sf hpan ⟨R', hp⟩
    exact kpkPanicAllow_of_eq (hpanic sf R' hpan hp)
  · intro sf hpcm hrunm hspm hcsm hfz' hsym'
    exact hnext sf ⟨hfz', hsym'⟩ hpcm hrunm hspm hcsm
  · intro sf R' hoom_s ho
    exact (hoom sf (F ∗ R') hoom_s (by simpa only [Spec.inImage, sepConj_assoc] using ho)).elim

/-! ## Exact 54-cell (`0x1b0`-byte) stack frame partition -/

def kpkSlack3 (sp0 : BitVec 64) : SepProp :=
  cells (sp0 - 432#64) 1 ∗ cells (sp0 - 272#64) 1 ∗ cells (sp0 - 104#64) 1

def kpkSavedRegs (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

structure KpkScratch where
  sp08   : BitVec 64
  sp10_0 : BitVec 64
  sp10_1 : BitVec 64
  sp10_2 : BitVec 64
  sp10_3 : BitVec 64
  sp10_4 : BitVec 64
  sp10_5 : BitVec 64
  sp40_0 : BitVec 64
  sp40_1 : BitVec 64
  sp40_2 : BitVec 64
  sp40_3 : BitVec 64
  sp40_4 : BitVec 64
  sp40_5 : BitVec 64
  sp70_0 : BitVec 64
  sp70_1 : BitVec 64
  sp70_2 : BitVec 64
  sp70_3 : BitVec 64
  sp70_4 : BitVec 64
  sp70_5 : BitVec 64
  dec0   : BitVec 64
  dec1   : BitVec 64
  dec2   : BitVec 64
  fp90_0 : BitVec 64
  fp90_1 : BitVec 64
  fp90_2 : BitVec 64
  fp90_3 : BitVec 64
  fp90_4 : BitVec 64
  fp90_5 : BitVec 64
  ret0   : BitVec 64
  ret1   : BitVec 64
  ret2   : BitVec 64
  ret3   : BitVec 64
  ret4   : BitVec 64
  ret5   : BitVec 64
  ret6   : BitVec 64
  ret7   : BitVec 64
  ret8   : BitVec 64
  ret9   : BitVec 64
  ret10  : BitVec 64

def slot7At (sp0 : BitVec 64) (sc : KpkScratch) : SepProp :=
  ((sp0 - 424#64) ↦₆₄ sc.sp08) ∗
  ((sp0 - 416#64) ↦₆₄ sc.sp10_0) ∗ ((sp0 - 408#64) ↦₆₄ sc.sp10_1) ∗
  ((sp0 - 400#64) ↦₆₄ sc.sp10_2) ∗ ((sp0 - 392#64) ↦₆₄ sc.sp10_3) ∗
  ((sp0 - 384#64) ↦₆₄ sc.sp10_4) ∗ ((sp0 - 376#64) ↦₆₄ sc.sp10_5)

def slotSp40At (sp0 : BitVec 64) (sc : KpkScratch) : SepProp :=
  ((sp0 - 368#64) ↦₆₄ sc.sp40_0) ∗ ((sp0 - 360#64) ↦₆₄ sc.sp40_1) ∗
  ((sp0 - 352#64) ↦₆₄ sc.sp40_2) ∗ ((sp0 - 344#64) ↦₆₄ sc.sp40_3) ∗
  ((sp0 - 336#64) ↦₆₄ sc.sp40_4) ∗ ((sp0 - 328#64) ↦₆₄ sc.sp40_5)

def slotSp70At (sp0 : BitVec 64) (sc : KpkScratch) : SepProp :=
  ((sp0 - 320#64) ↦₆₄ sc.sp70_0) ∗ ((sp0 - 312#64) ↦₆₄ sc.sp70_1) ∗
  ((sp0 - 304#64) ↦₆₄ sc.sp70_2) ∗ ((sp0 - 296#64) ↦₆₄ sc.sp70_3) ∗
  ((sp0 - 288#64) ↦₆₄ sc.sp70_4) ∗ ((sp0 - 280#64) ↦₆₄ sc.sp70_5)

def slotDecAt (sp0 : BitVec 64) (sc : KpkScratch) : SepProp :=
  ((sp0 - 264#64) ↦₆₄ sc.dec0) ∗ ((sp0 - 256#64) ↦₆₄ sc.dec1) ∗ ((sp0 - 248#64) ↦₆₄ sc.dec2)

def slotFp90At (sp0 : BitVec 64) (sc : KpkScratch) : SepProp :=
  ((sp0 - 240#64) ↦₆₄ sc.fp90_0) ∗ ((sp0 - 232#64) ↦₆₄ sc.fp90_1) ∗
  ((sp0 - 224#64) ↦₆₄ sc.fp90_2) ∗ ((sp0 - 216#64) ↦₆₄ sc.fp90_3) ∗
  ((sp0 - 208#64) ↦₆₄ sc.fp90_4) ∗ ((sp0 - 200#64) ↦₆₄ sc.fp90_5)

def slotRetHeadAt (sp0 : BitVec 64) (sc : KpkScratch) : SepProp :=
  ((sp0 - 192#64) ↦₆₄ sc.ret0) ∗ ((sp0 - 184#64) ↦₆₄ sc.ret1) ∗
  ((sp0 - 176#64) ↦₆₄ sc.ret2) ∗ ((sp0 - 168#64) ↦₆₄ sc.ret3) ∗
  ((sp0 - 160#64) ↦₆₄ sc.ret4) ∗ ((sp0 - 152#64) ↦₆₄ sc.ret5)

def slotRetTailAt (sp0 : BitVec 64) (sc : KpkScratch) : SepProp :=
  ((sp0 - 144#64) ↦₆₄ sc.ret6) ∗ ((sp0 - 136#64) ↦₆₄ sc.ret7) ∗
  ((sp0 - 128#64) ↦₆₄ sc.ret8) ∗ ((sp0 - 120#64) ↦₆₄ sc.ret9) ∗
  ((sp0 - 112#64) ↦₆₄ sc.ret10)

def kpkScratchAt (sp0 : BitVec 64) (sc : KpkScratch) : SepProp :=
  slot7At sp0 sc ∗ slotSp40At sp0 sc ∗ slotSp70At sp0 sc ∗
  slotDecAt sp0 sc ∗ slotFp90At sp0 sc ∗ slotRetHeadAt sp0 sc ∗ slotRetTailAt sp0 sc

private def savedHi6At (sp0 g96 g88 g80 g72 g64 g56 : BitVec 64) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ g96) ∗ ((sp0 - 88#64) ↦₆₄ g88) ∗
  ((sp0 - 80#64) ↦₆₄ g80) ∗ ((sp0 - 72#64) ↦₆₄ g72) ∗
  ((sp0 - 64#64) ↦₆₄ g64) ∗ ((sp0 - 56#64) ↦₆₄ g56)

private def savedLo6At (sp0 g48 g40 g32 g24 g16 g8 : BitVec 64) : SepProp :=
  ((sp0 - 48#64) ↦₆₄ g48) ∗ ((sp0 - 40#64) ↦₆₄ g40) ∗
  ((sp0 - 32#64) ↦₆₄ g32) ∗ ((sp0 - 24#64) ↦₆₄ g24) ∗
  ((sp0 - 16#64) ↦₆₄ g16) ∗ ((sp0 - 8#64) ↦₆₄ g8)

private theorem kpkSavedRegs_eq (s0 : State) :
    kpkSavedRegs s0 =
      savedHi6At s0.sp
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
        (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25) ∗
      savedLo6At s0.sp
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
        (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) := by
  dsimp only [kpkSavedRegs, savedHi6At, savedLo6At]
  ac_rfl

private theorem sub_add_eq (sp0 : BitVec 64) {a b c : Nat} (h : a = b + c) :
    (sp0 - BitVec.ofNat 64 a) + BitVec.ofNat 64 b = sp0 - BitVec.ofNat 64 c := by
  subst h; bv_omega

theorem words6At_retSlot (sp0 w0 w1 w2 w3 w4 w5 : BitVec 64) :
    words6At (sp0 - 192#64) w0 w1 w2 w3 w4 w5 =
      ((sp0 - 192#64) ↦₆₄ w0) ∗ ((sp0 - 184#64) ↦₆₄ w1) ∗ ((sp0 - 176#64) ↦₆₄ w2) ∗
      ((sp0 - 168#64) ↦₆₄ w3) ∗ ((sp0 - 160#64) ↦₆₄ w4) ∗ ((sp0 - 152#64) ↦₆₄ w5) := by
  dsimp only [words6At]
  exact congrArg₂ sepConj rfl
    (congrArg₂ sepConj (congrArg (· ↦₆₄ w1) (sub_add_eq sp0 rfl))
      (congrArg₂ sepConj (congrArg (· ↦₆₄ w2) (sub_add_eq sp0 rfl))
        (congrArg₂ sepConj (congrArg (· ↦₆₄ w3) (sub_add_eq sp0 rfl))
          (congrArg₂ sepConj (congrArg (· ↦₆₄ w4) (sub_add_eq sp0 rfl))
            (congrArg (· ↦₆₄ w5) (sub_add_eq sp0 rfl))))))

theorem words11At_retSlot (sp0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    words11At (sp0 - 192#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 =
      ((sp0 - 192#64) ↦₆₄ w0) ∗ ((sp0 - 184#64) ↦₆₄ w1) ∗ ((sp0 - 176#64) ↦₆₄ w2) ∗
      ((sp0 - 168#64) ↦₆₄ w3) ∗ ((sp0 - 160#64) ↦₆₄ w4) ∗ ((sp0 - 152#64) ↦₆₄ w5) ∗
      ((sp0 - 144#64) ↦₆₄ w6) ∗ ((sp0 - 136#64) ↦₆₄ w7) ∗ ((sp0 - 128#64) ↦₆₄ w8) ∗
      ((sp0 - 120#64) ↦₆₄ w9) ∗ ((sp0 - 112#64) ↦₆₄ w10) := by
  dsimp only [words11At]
  exact congrArg₂ sepConj rfl
    (congrArg₂ sepConj (congrArg (· ↦₆₄ w1) (sub_add_eq sp0 rfl))
      (congrArg₂ sepConj (congrArg (· ↦₆₄ w2) (sub_add_eq sp0 rfl))
        (congrArg₂ sepConj (congrArg (· ↦₆₄ w3) (sub_add_eq sp0 rfl))
          (congrArg₂ sepConj (congrArg (· ↦₆₄ w4) (sub_add_eq sp0 rfl))
            (congrArg₂ sepConj (congrArg (· ↦₆₄ w5) (sub_add_eq sp0 rfl))
              (congrArg₂ sepConj (congrArg (· ↦₆₄ w6) (sub_add_eq sp0 rfl))
                (congrArg₂ sepConj (congrArg (· ↦₆₄ w7) (sub_add_eq sp0 rfl))
                  (congrArg₂ sepConj (congrArg (· ↦₆₄ w8) (sub_add_eq sp0 rfl))
                    (congrArg₂ sepConj (congrArg (· ↦₆₄ w9) (sub_add_eq sp0 rfl))
                      (congrArg (· ↦₆₄ w10) (sub_add_eq sp0 rfl)))))))))))

theorem decSlot_eq (sp0 c p l : BitVec 64) :
    ((sp0 - 264#64) ↦₆₄ c) ∗ (((sp0 - 264#64) + 8#64) ↦₆₄ p) ∗ (((sp0 - 264#64) + 16#64) ↦₆₄ l) =
      ((sp0 - 264#64) ↦₆₄ c) ∗ ((sp0 - 256#64) ↦₆₄ p) ∗ ((sp0 - 248#64) ↦₆₄ l) :=
  congrArg₂ sepConj rfl
    (congrArg₂ sepConj (congrArg (· ↦₆₄ p) (sub_add_eq sp0 rfl))
      (congrArg (· ↦₆₄ l) (sub_add_eq sp0 rfl)))

theorem satisfies_open_words11 {m : Memory} {a : BitVec 64} {R : SepProp}
    (hm : m ⊨ memRegion a 88 ∗ R) :
    ∃ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10,
      m ⊨ words11At a u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗ R := by
  rw [memRegion_88_words11 a] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨u10, u9, u8, u7, u6, u5, u4, u3, u2, u1, u0, hm⟩
  exact ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, hm⟩

private theorem cells_54_chunks (sp : BitVec 64) :
    cells (sp - 432#64) 54 =
      kpkSlack3 sp ∗
        (cells (sp - 424#64) 7 ∗ cells (sp - 368#64) 6 ∗ cells (sp - 320#64) 6 ∗
         cells (sp - 264#64) 3 ∗ cells (sp - 240#64) 6 ∗ cells (sp - 192#64) 6 ∗
         cells (sp - 144#64) 5 ∗ cells (sp - 96#64) 6 ∗ cells (sp - 48#64) 6) := by
  rw [show (54 : Nat) = 1 + 53 from rfl, cells_split_sub sp 432 424 1 53,
    show (53 : Nat) = 7 + 46 from rfl, cells_split_sub sp 424 368 7 46,
    show (46 : Nat) = 6 + 40 from rfl, cells_split_sub sp 368 320 6 40,
    show (40 : Nat) = 6 + 34 from rfl, cells_split_sub sp 320 272 6 34,
    show (34 : Nat) = 1 + 33 from rfl, cells_split_sub sp 272 264 1 33,
    show (33 : Nat) = 3 + 30 from rfl, cells_split_sub sp 264 240 3 30,
    show (30 : Nat) = 6 + 24 from rfl, cells_split_sub sp 240 192 6 24,
    show (24 : Nat) = 6 + 18 from rfl, cells_split_sub sp 192 144 6 18,
    show (18 : Nat) = 5 + 13 from rfl, cells_split_sub sp 144 104 5 13,
    show (13 : Nat) = 1 + 12 from rfl, cells_split_sub sp 104 96 1 12,
    show (12 : Nat) = 6 + 6 from rfl, cells_split_sub sp 96 48 6 6]
  dsimp only [kpkSlack3]
  ac_rfl

private theorem pack_cell_step {p p' v : BitVec 64} {n : Nat} {Q : SepProp}
    (hQ : Q ⊢ cells p' n) (hp : p + 8#64 = p' := by bv_omega) :
    (p ↦₆₄ v) ∗ Q ⊢ cells p (n + 1) := by
  have hc : cells p (n + 1) = (∃∗ w : BitVec 64, (p ↦₆₄ w) ∗ cells p' n) := by
    rw [← hp]; rfl
  rw [hc]
  exact Entails.trans (sepConj_mono_right hQ) (Entails.sepExists_right v (Entails.refl _))

private theorem pack_cell_last {p v : BitVec 64} :
    (p ↦₆₄ v) ⊢ cells p 1 := by
  have hc : cells p 1 = (∃∗ w : BitVec 64, (p ↦₆₄ w) ∗ emp) := rfl
  rw [hc]
  exact Entails.trans (Entails.of_eq (sepConj_emp _).symm)
    (Entails.sepExists_right v (Entails.refl _))

private theorem pack_chunk7 (sp : BitVec 64) (sc : KpkScratch) :
    slot7At sp sc ⊢ cells (sp - 424#64) 7 := by
  dsimp only [slot7At]
  exact pack_cell_step <| pack_cell_step <| pack_cell_step <|
    pack_cell_step <| pack_cell_step <| pack_cell_step <| pack_cell_last

private theorem pack_chunk6_368 (sp : BitVec 64) (sc : KpkScratch) :
    slotSp40At sp sc ⊢ cells (sp - 368#64) 6 := by
  dsimp only [slotSp40At]
  exact pack_cell_step <| pack_cell_step <| pack_cell_step <|
    pack_cell_step <| pack_cell_step <| pack_cell_last

private theorem pack_chunk6_320 (sp : BitVec 64) (sc : KpkScratch) :
    slotSp70At sp sc ⊢ cells (sp - 320#64) 6 := by
  dsimp only [slotSp70At]
  exact pack_cell_step <| pack_cell_step <| pack_cell_step <|
    pack_cell_step <| pack_cell_step <| pack_cell_last

private theorem pack_chunk3_264 (sp : BitVec 64) (sc : KpkScratch) :
    slotDecAt sp sc ⊢ cells (sp - 264#64) 3 := by
  dsimp only [slotDecAt]
  exact pack_cell_step <| pack_cell_step <| pack_cell_last

private theorem pack_chunk6_240 (sp : BitVec 64) (sc : KpkScratch) :
    slotFp90At sp sc ⊢ cells (sp - 240#64) 6 := by
  dsimp only [slotFp90At]
  exact pack_cell_step <| pack_cell_step <| pack_cell_step <|
    pack_cell_step <| pack_cell_step <| pack_cell_last

private theorem pack_chunk6_192 (sp : BitVec 64) (sc : KpkScratch) :
    slotRetHeadAt sp sc ⊢ cells (sp - 192#64) 6 := by
  dsimp only [slotRetHeadAt]
  exact pack_cell_step <| pack_cell_step <| pack_cell_step <|
    pack_cell_step <| pack_cell_step <| pack_cell_last

private theorem pack_chunk5_144 (sp : BitVec 64) (sc : KpkScratch) :
    slotRetTailAt sp sc ⊢ cells (sp - 144#64) 5 := by
  dsimp only [slotRetTailAt]
  exact pack_cell_step <| pack_cell_step <| pack_cell_step <|
    pack_cell_step <| pack_cell_last

private theorem pack_chunk6_96 (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    savedHi6At sp a0 a1 a2 a3 a4 a5 ⊢ cells (sp - 96#64) 6 := by
  dsimp only [savedHi6At]
  exact pack_cell_step <| pack_cell_step <| pack_cell_step <|
    pack_cell_step <| pack_cell_step <| pack_cell_last

private theorem pack_chunk6_48 (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    savedLo6At sp a0 a1 a2 a3 a4 a5 ⊢ cells (sp - 48#64) 6 := by
  dsimp only [savedLo6At]
  exact pack_cell_step <| pack_cell_step <| pack_cell_step <|
    pack_cell_step <| pack_cell_step <| pack_cell_last

theorem kpkFrame_entails_cells54 (s0 : State) (sc : KpkScratch) :
    kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0 ⊢ cells (s0.sp - 432#64) 54 := by
  rw [cells_54_chunks s0.sp, kpkSavedRegs_eq s0]
  dsimp only [kpkScratchAt]
  have hbody := sepConj_mono (pack_chunk7 s0.sp sc)
    (sepConj_mono (pack_chunk6_368 s0.sp sc)
      (sepConj_mono (pack_chunk6_320 s0.sp sc)
        (sepConj_mono (pack_chunk3_264 s0.sp sc)
          (sepConj_mono (pack_chunk6_240 s0.sp sc)
            (sepConj_mono (pack_chunk6_192 s0.sp sc)
              (sepConj_mono (pack_chunk5_144 s0.sp sc)
                (sepConj_mono
                  (pack_chunk6_96 s0.sp
                    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
                    (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25))
                  (pack_chunk6_48 s0.sp
                    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
                    (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)))))))))
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right hbody)

private theorem open_cell_step {m : Memory} {p p' : BitVec 64} {n : Nat} {R : SepProp}
    (hp : p + 8#64 = p')
    (hm : m ⊨ cells p (n + 1) ∗ R) :
    ∃ v : BitVec 64, m ⊨ cells p' n ∗ ((p ↦₆₄ v) ∗ R) := by
  have hc : cells p (n + 1) = (∃∗ v : BitVec 64, (p ↦₆₄ v) ∗ cells p' n) := by
    rw [← hp]; rfl
  rw [hc, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact ⟨v, by convert hv using 1; ac_rfl⟩

private theorem open_cell_last {m : Memory} {p : BitVec 64} {R : SepProp}
    (hm : m ⊨ cells p 1 ∗ R) :
    ∃ v : BitVec 64, m ⊨ (p ↦₆₄ v) ∗ R := by
  have hc : cells p 1 = (∃∗ v : BitVec 64, (p ↦₆₄ v) ∗ emp) := rfl
  rw [hc, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  rw [sepConj_emp] at hv
  exact ⟨v, hv⟩

private theorem open_chunk7 {m : Memory} {sp0 : BitVec 64} {R : SepProp}
    (hm : m ⊨ cells (sp0 - 424#64) 7 ∗ R) :
    ∃ a0 a1 a2 a3 a4 a5 a6,
      m ⊨ (((sp0 - 424#64) ↦₆₄ a0) ∗ ((sp0 - 416#64) ↦₆₄ a1) ∗ ((sp0 - 408#64) ↦₆₄ a2) ∗
           ((sp0 - 400#64) ↦₆₄ a3) ∗ ((sp0 - 392#64) ↦₆₄ a4) ∗ ((sp0 - 384#64) ↦₆₄ a5) ∗
           ((sp0 - 376#64) ↦₆₄ a6)) ∗ R := by
  obtain ⟨a0, hm⟩ := open_cell_step (p' := sp0 - 416#64) (by bv_omega) hm
  obtain ⟨a1, hm⟩ := open_cell_step (p' := sp0 - 408#64) (by bv_omega) hm
  obtain ⟨a2, hm⟩ := open_cell_step (p' := sp0 - 400#64) (by bv_omega) hm
  obtain ⟨a3, hm⟩ := open_cell_step (p' := sp0 - 392#64) (by bv_omega) hm
  obtain ⟨a4, hm⟩ := open_cell_step (p' := sp0 - 384#64) (by bv_omega) hm
  obtain ⟨a5, hm⟩ := open_cell_step (p' := sp0 - 376#64) (by bv_omega) hm
  obtain ⟨a6, hm⟩ := open_cell_last hm
  exact ⟨a0, a1, a2, a3, a4, a5, a6, by convert hm using 1; ac_rfl⟩

private theorem open_chunk6_at {m : Memory} {k0 : BitVec 64}
    (k1 k2 k3 k4 k5 : BitVec 64) {R : SepProp}
    (hm : m ⊨ cells k0 6 ∗ R)
    (h1 : k0 + 8#64 = k1 := by bv_omega) (h2 : k1 + 8#64 = k2 := by bv_omega)
    (h3 : k2 + 8#64 = k3 := by bv_omega) (h4 : k3 + 8#64 = k4 := by bv_omega)
    (h5 : k4 + 8#64 = k5 := by bv_omega) :
    ∃ a0 a1 a2 a3 a4 a5,
      m ⊨ ((k0 ↦₆₄ a0) ∗ (k1 ↦₆₄ a1) ∗ (k2 ↦₆₄ a2) ∗
           (k3 ↦₆₄ a3) ∗ (k4 ↦₆₄ a4) ∗ (k5 ↦₆₄ a5)) ∗ R := by
  obtain ⟨a0, hm⟩ := open_cell_step h1 hm
  obtain ⟨a1, hm⟩ := open_cell_step h2 hm
  obtain ⟨a2, hm⟩ := open_cell_step h3 hm
  obtain ⟨a3, hm⟩ := open_cell_step h4 hm
  obtain ⟨a4, hm⟩ := open_cell_step h5 hm
  obtain ⟨a5, hm⟩ := open_cell_last hm
  exact ⟨a0, a1, a2, a3, a4, a5, by convert hm using 1; ac_rfl⟩

private theorem open_chunk3 {m : Memory} {sp0 : BitVec 64} {R : SepProp}
    (hm : m ⊨ cells (sp0 - 264#64) 3 ∗ R) :
    ∃ a0 a1 a2,
      m ⊨ (((sp0 - 264#64) ↦₆₄ a0) ∗ ((sp0 - 256#64) ↦₆₄ a1) ∗ ((sp0 - 248#64) ↦₆₄ a2)) ∗ R := by
  obtain ⟨a0, hm⟩ := open_cell_step (p' := sp0 - 256#64) (by bv_omega) hm
  obtain ⟨a1, hm⟩ := open_cell_step (p' := sp0 - 248#64) (by bv_omega) hm
  obtain ⟨a2, hm⟩ := open_cell_last hm
  exact ⟨a0, a1, a2, by convert hm using 1; ac_rfl⟩

private theorem open_chunk5 {m : Memory} {sp0 : BitVec 64} {R : SepProp}
    (hm : m ⊨ cells (sp0 - 144#64) 5 ∗ R) :
    ∃ a0 a1 a2 a3 a4,
      m ⊨ (((sp0 - 144#64) ↦₆₄ a0) ∗ ((sp0 - 136#64) ↦₆₄ a1) ∗ ((sp0 - 128#64) ↦₆₄ a2) ∗
           ((sp0 - 120#64) ↦₆₄ a3) ∗ ((sp0 - 112#64) ↦₆₄ a4)) ∗ R := by
  obtain ⟨a0, hm⟩ := open_cell_step (p' := sp0 - 136#64) (by bv_omega) hm
  obtain ⟨a1, hm⟩ := open_cell_step (p' := sp0 - 128#64) (by bv_omega) hm
  obtain ⟨a2, hm⟩ := open_cell_step (p' := sp0 - 120#64) (by bv_omega) hm
  obtain ⟨a3, hm⟩ := open_cell_step (p' := sp0 - 112#64) (by bv_omega) hm
  obtain ⟨a4, hm⟩ := open_cell_last hm
  exact ⟨a0, a1, a2, a3, a4, by convert hm using 1; ac_rfl⟩

private theorem rot_front {m : Memory} {A B R : SepProp} (h : m ⊨ (A ∗ B) ∗ R) :
    m ⊨ B ∗ (A ∗ R) := by
  convert h using 1; ac_rfl

theorem satisfies_open_frame {m : Memory} {sp0 : BitVec 64} {R : SepProp}
    (hm : m ⊨ cells (sp0 - 432#64) 54 ∗ R) :
    ∃ (sc : KpkScratch) (g96 g88 g80 g72 g64 g56 g48 g40 g32 g24 g16 g8 : BitVec 64),
      m ⊨ (kpkSlack3 sp0 ∗ kpkScratchAt sp0 sc ∗
        (((sp0 - 96#64) ↦₆₄ g96) ∗ ((sp0 - 88#64) ↦₆₄ g88) ∗
         ((sp0 - 80#64) ↦₆₄ g80) ∗ ((sp0 - 72#64) ↦₆₄ g72) ∗
         ((sp0 - 64#64) ↦₆₄ g64) ∗ ((sp0 - 56#64) ↦₆₄ g56) ∗
         ((sp0 - 48#64) ↦₆₄ g48) ∗ ((sp0 - 40#64) ↦₆₄ g40) ∗
         ((sp0 - 32#64) ↦₆₄ g32) ∗ ((sp0 - 24#64) ↦₆₄ g24) ∗
         ((sp0 - 16#64) ↦₆₄ g16) ∗ ((sp0 - 8#64) ↦₆₄ g8))) ∗ R := by
  rw [cells_54_chunks sp0] at hm
  have hm := rot_front hm
  rw [sepConj_assoc] at hm
  obtain ⟨p08, p10_0, p10_1, p10_2, p10_3, p10_4, p10_5, hm⟩ := open_chunk7 hm
  let c1 : SepProp :=
    ((sp0 - 424#64) ↦₆₄ p08) ∗ ((sp0 - 416#64) ↦₆₄ p10_0) ∗ ((sp0 - 408#64) ↦₆₄ p10_1) ∗
    ((sp0 - 400#64) ↦₆₄ p10_2) ∗ ((sp0 - 392#64) ↦₆₄ p10_3) ∗ ((sp0 - 384#64) ↦₆₄ p10_4) ∗
    ((sp0 - 376#64) ↦₆₄ p10_5)
  change m ⊨ c1 ∗ _ at hm; rw [← sepConj_assoc] at hm; have hm := rot_front hm
  rw [sepConj_assoc] at hm
  obtain ⟨p40_0, p40_1, p40_2, p40_3, p40_4, p40_5, hm⟩ :=
    open_chunk6_at (sp0 - 360#64) (sp0 - 352#64) (sp0 - 344#64) (sp0 - 336#64) (sp0 - 328#64) hm
  let c2 : SepProp :=
    ((sp0 - 368#64) ↦₆₄ p40_0) ∗ ((sp0 - 360#64) ↦₆₄ p40_1) ∗
    ((sp0 - 352#64) ↦₆₄ p40_2) ∗ ((sp0 - 344#64) ↦₆₄ p40_3) ∗
    ((sp0 - 336#64) ↦₆₄ p40_4) ∗ ((sp0 - 328#64) ↦₆₄ p40_5)
  change m ⊨ c2 ∗ _ at hm; rw [← sepConj_assoc] at hm; have hm := rot_front hm
  rw [sepConj_assoc] at hm
  obtain ⟨p70_0, p70_1, p70_2, p70_3, p70_4, p70_5, hm⟩ :=
    open_chunk6_at (sp0 - 312#64) (sp0 - 304#64) (sp0 - 296#64) (sp0 - 288#64) (sp0 - 280#64) hm
  let c3 : SepProp :=
    ((sp0 - 320#64) ↦₆₄ p70_0) ∗ ((sp0 - 312#64) ↦₆₄ p70_1) ∗
    ((sp0 - 304#64) ↦₆₄ p70_2) ∗ ((sp0 - 296#64) ↦₆₄ p70_3) ∗
    ((sp0 - 288#64) ↦₆₄ p70_4) ∗ ((sp0 - 280#64) ↦₆₄ p70_5)
  change m ⊨ c3 ∗ _ at hm; rw [← sepConj_assoc] at hm; have hm := rot_front hm
  rw [sepConj_assoc] at hm
  obtain ⟨d0, d1, d2, hm⟩ := open_chunk3 hm
  let c4 : SepProp :=
    ((sp0 - 264#64) ↦₆₄ d0) ∗ ((sp0 - 256#64) ↦₆₄ d1) ∗ ((sp0 - 248#64) ↦₆₄ d2)
  change m ⊨ c4 ∗ _ at hm; rw [← sepConj_assoc] at hm; have hm := rot_front hm
  rw [sepConj_assoc] at hm
  obtain ⟨f0, f1, f2, f3, f4, f5, hm⟩ :=
    open_chunk6_at (sp0 - 232#64) (sp0 - 224#64) (sp0 - 216#64) (sp0 - 208#64) (sp0 - 200#64) hm
  let c5 : SepProp :=
    ((sp0 - 240#64) ↦₆₄ f0) ∗ ((sp0 - 232#64) ↦₆₄ f1) ∗
    ((sp0 - 224#64) ↦₆₄ f2) ∗ ((sp0 - 216#64) ↦₆₄ f3) ∗
    ((sp0 - 208#64) ↦₆₄ f4) ∗ ((sp0 - 200#64) ↦₆₄ f5)
  change m ⊨ c5 ∗ _ at hm; rw [← sepConj_assoc] at hm; have hm := rot_front hm
  rw [sepConj_assoc] at hm
  obtain ⟨r0, r1, r2, r3, r4, r5, hm⟩ :=
    open_chunk6_at (sp0 - 184#64) (sp0 - 176#64) (sp0 - 168#64) (sp0 - 160#64) (sp0 - 152#64) hm
  let c6 : SepProp :=
    ((sp0 - 192#64) ↦₆₄ r0) ∗ ((sp0 - 184#64) ↦₆₄ r1) ∗
    ((sp0 - 176#64) ↦₆₄ r2) ∗ ((sp0 - 168#64) ↦₆₄ r3) ∗
    ((sp0 - 160#64) ↦₆₄ r4) ∗ ((sp0 - 152#64) ↦₆₄ r5)
  change m ⊨ c6 ∗ _ at hm; rw [← sepConj_assoc] at hm; have hm := rot_front hm
  rw [sepConj_assoc] at hm
  obtain ⟨r6, r7, r8, r9, r10, hm⟩ := open_chunk5 hm
  let c7 : SepProp :=
    ((sp0 - 144#64) ↦₆₄ r6) ∗ ((sp0 - 136#64) ↦₆₄ r7) ∗
    ((sp0 - 128#64) ↦₆₄ r8) ∗ ((sp0 - 120#64) ↦₆₄ r9) ∗ ((sp0 - 112#64) ↦₆₄ r10)
  change m ⊨ c7 ∗ _ at hm; rw [← sepConj_assoc] at hm; have hm := rot_front hm
  rw [sepConj_assoc] at hm
  obtain ⟨g96, g88, g80, g72, g64, g56, hm⟩ :=
    open_chunk6_at (sp0 - 88#64) (sp0 - 80#64) (sp0 - 72#64) (sp0 - 64#64) (sp0 - 56#64) hm
  let c8 : SepProp := savedHi6At sp0 g96 g88 g80 g72 g64 g56
  change m ⊨ c8 ∗ _ at hm; rw [← sepConj_assoc] at hm; have hm := rot_front hm
  obtain ⟨g48, g40, g32, g24, g16, g8, hm⟩ :=
    open_chunk6_at (sp0 - 40#64) (sp0 - 32#64) (sp0 - 24#64) (sp0 - 16#64) (sp0 - 8#64) hm
  let c9 : SepProp := savedLo6At sp0 g48 g40 g32 g24 g16 g8
  change m ⊨ c9 ∗ _ at hm
  let sc : KpkScratch :=
    { sp08 := p08, sp10_0 := p10_0, sp10_1 := p10_1, sp10_2 := p10_2,
      sp10_3 := p10_3, sp10_4 := p10_4, sp10_5 := p10_5,
      sp40_0 := p40_0, sp40_1 := p40_1, sp40_2 := p40_2,
      sp40_3 := p40_3, sp40_4 := p40_4, sp40_5 := p40_5,
      sp70_0 := p70_0, sp70_1 := p70_1, sp70_2 := p70_2,
      sp70_3 := p70_3, sp70_4 := p70_4, sp70_5 := p70_5,
      dec0 := d0, dec1 := d1, dec2 := d2,
      fp90_0 := f0, fp90_1 := f1, fp90_2 := f2,
      fp90_3 := f3, fp90_4 := f4, fp90_5 := f5,
      ret0 := r0, ret1 := r1, ret2 := r2, ret3 := r3, ret4 := r4, ret5 := r5,
      ret6 := r6, ret7 := r7, ret8 := r8, ret9 := r9, ret10 := r10 }
  refine ⟨sc, g96, g88, g80, g72, g64, g56, g48, g40, g32, g24, g16, g8, ?_⟩
  have hgoal :
      ((sp0 - 96#64) ↦₆₄ g96) ∗ ((sp0 - 88#64) ↦₆₄ g88) ∗
      ((sp0 - 80#64) ↦₆₄ g80) ∗ ((sp0 - 72#64) ↦₆₄ g72) ∗
      ((sp0 - 64#64) ↦₆₄ g64) ∗ ((sp0 - 56#64) ↦₆₄ g56) ∗
      ((sp0 - 48#64) ↦₆₄ g48) ∗ ((sp0 - 40#64) ↦₆₄ g40) ∗
      ((sp0 - 32#64) ↦₆₄ g32) ∗ ((sp0 - 24#64) ↦₆₄ g24) ∗
      ((sp0 - 16#64) ↦₆₄ g16) ∗ ((sp0 - 8#64) ↦₆₄ g8) = c8 ∗ c9 := by
    dsimp only [c8, c9, savedHi6At, savedLo6At]; ac_rfl
  rw [hgoal]
  have hsc : kpkScratchAt sp0 sc = c1 ∗ c2 ∗ c3 ∗ c4 ∗ c5 ∗ c6 ∗ c7 := rfl
  rw [hsc]
  convert hm using 1
  ac_rfl

/-! ## Shared exit blocks (`+500`, `+480`, `+412`, `+440`, `+216`) -/


end CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
