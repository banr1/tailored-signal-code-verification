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
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopVarint
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopError
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded `IdentityKeyPair::try_from` Tag Varint Decode

`RustCliAllocBudget`-threaded relocatable proof of the inline/slow-path tag varint decode step in
`IdentityKeyPair::try_from` (Block `84`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopVarintBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
  hiding rustDeallocExternSpecWithStack decodeErrorFromSpecWithStack
    decodeErrorPushExternSpecWithStack decodeVarintSlowSpecWithStack
open CryptoVerification.LibsignalTripleRatchet.Prost
  hiding dropDecodeErrorSpecGen dropDecodeErrorSpecX decodeVarintSliceSpecGen decodeVarintSliceSpecX
open CryptoVerification.LibsignalTripleRatchet.VarintBridge (decodeVarint_eq_varintSlow)
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWP.done -> sepWPDoneWire
open scoped CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary (DecodeGhost sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers hiding ikpLoopCommonPlaced
open scoped CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (decodeVarintSlowSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowEvents decodeVarintSlowBudgetSpecWithStack)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PortDepsPlaced RecordCodecIterEnv RecordCodecLoopEnv fitsEnv_recordCodecLoop_head
   noPanicQp sepWPp_mono_post sepWPp_call_noPanic_lscro)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
  (ikp_varintSlow_placed_ok)
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget
  (ikpExitPostPlaced ikpExitPostPlaced_prepend_iter decodeErr_616_placed_wp ikpLoopCommonPlaced)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section LoopVarintStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_lv (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_lv (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPState_lv (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_advancePC_lv (s : State) : s.advancePC.sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg64_gpr_lv (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg32_gpr_lv (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg_gpr_lv (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by
  cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_lv (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_lv (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPState_lv (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_lv (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_lv (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPState_lv (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_lv (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_lv (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPState_lv (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end LoopVarintStateSimp

theorem decodeVarintSlow_304_placed_cps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} (d : PortDepsPlaced M A lim H)
    {x : DecodeGhost} {s0 s : State} {sp' ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : IdentityKeyPairStructure}
    (hpc : s.pc = (blkPl_84).base + 304#64) (hrun : s.status = .Running)
    (hregs : IkpLoopRegsPlaced s0 sp' x.ret s)
    (hx23 : s.readReg64 .x23 = sp' + 32#64) (hx22 : s.readReg64 .x22 = sp' + 40#64)
    (hlen : bs.length < 2 ^ 63)
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
  have hcall := ikp_varintSlow_placed_ok d
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_subst := hregs.base.sp; subst hsp_subst
  have _hsp_align := hregs.base.spAligned; have _hx29 := hregs.x29
  have hstack := stackAt_sub_split s.sp (64 + 2 * extHookStack) (skipFieldStackX 100)
  unfold sliceCursorAt ikpLoopCommonPlaced
  simp only [hstack, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hregs.base.crl (mid := lsmpl.base 293) ?_; wp_steps
  refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (s.sp + 168#64, s.sp + 32#64, ptr, bs, st) hcall
    (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
    (by tryFromPost_sp_align hregs.base.spAligned) hcrl1
    (by simp [*, arm64_norm] : _ = (blkPl_84).base + bv% (312))
    (by simp [*, hregs.base.trace, arm64_norm])
    (T := ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗ ((s.sp + 32#64) ↦₆₄ ptr) ∗
      ((s.sp + 32#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      A.pool lim st s ∗ stackAt s.sp (64 + 2 * extHookStack))
    (φ := s.sp + 168#64 = s.sp + 168#64 ∧ bs.length < 18446744073709551616 ∧
      FitsEnv M lim st (DecodeVarintSlowEnv bs))
    (by simp [*, decodeVarintSlowSpecWithStack, decodeVarintSlowBudgetSpecWithStack,
      RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm])
    ⟨rfl, by omega, fitsEnv_recordCodecLoop_head (fun _ => RecordCodecIterEnv.of_decodeVarintSlow) hFit⟩
    (by sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs1 := hregs.of_steps hcrl1 rfl
    (by simp [*, hregs.base.trace, arm64_norm])
    (by simp [*, hregs.base.x26, arm64_norm]) (by simp [*, hregs.base.x27, arm64_norm])
    (by simp [*, hregs.base.x28, arm64_norm]) (by simp [*, arm64_norm])
    (by simp [*, hregs.x19, arm64_norm]) (by simp [*, hregs.x21, arm64_norm])
    (by simp [*, hregs.x24, arm64_norm])
  have hx23_2 : s2.readReg64 .x23 = s.sp + 32#64 := hcs2.2.2.2.2.1.trans (by simp [*, arm64_norm])
  have hx22_2 : s2.readReg64 .x22 = s.sp + 40#64 := hcs2.2.2.2.1.trans (by simp [*, arm64_norm])
  dsimp only [decodeVarintSlowSpecWithStack, decodeVarintSlowBudgetSpecWithStack]
  have hd_eq := decodeVarint_eq_varintSlow bs
  rw [hd_eq]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [Option.map]
    obtain ⟨k, _, _hkl, hrest⟩ := decodeVarint_suffix hd
    have hlen_sub : bs.length - (bs.length - rest.length) = rest.length := by
      rw [hrest, List.length_drop]; omega
    rw [hlen_sub, sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hx0_2, hx1_2⟩ => ?_
    have hevs0 : evs = [] := by
      rw [hevs]; unfold decodeVarintSlowEvents; rw [hd_eq, hd]; rfl
    subst hevs0
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    have _hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have _hx1_2' : s2.readReg64 (Reg.gpr 1#5) = key := hx1_2
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (220)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    refine SepWPp.mono_pre ?_
      (hcont key rest _ hd (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (hregs2.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
          (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
          (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm])
          (by simp [*, hregs2.x29, arm64_norm]) (by simp [*, hregs2.x19, arm64_norm])
          (by simp [*, hregs2.x21, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) (by simp [*, arm64_norm]))
    apply entails_of_eq; unfold sliceCursorAfter ikpLoopCommonPlaced; rw [hstack]
    simp only [arm64_norm]; sep_ac_rfl
  | none =>
    dsimp only [Option.map]; rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun evs => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun hevs => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hx0_1, _hx1_ne⟩ => ?_
    have _hx0_1' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    have hregs2 := hregs1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hregs1.base.trace) hcs2
    have _hsp2_eq := hregs2.base.sp
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_84).base + bv% (616)) ?_; wp_steps
    refine sepWPDoneWire (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl3
    have hpair := pointsTo64_pair_entails_memRegion16 (s.sp + 32#64)
      (ptr + BitVec.ofNat 64 (min 10 bs.length)) (BitVec.ofNat 64 (bs.length - min 10 bs.length))
    refine sepWPp_mono_post
      (SepWPp.mono_pre
        (P' := memRegion s.sp 32 ∗ memRegion (s.sp + 32#64) 16 ∗ ikpStructOf A.repAlloc (s.sp + 48#64) m ∗
          memRegion (s.sp + 96#64) 48 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗
          memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) _ ∗
          stackAt s.sp (skipFieldStackX 100) ∗ decodeErrorAt A.repAlloc (s2.readReg64 (Reg.gpr 1#5)))
        (by refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono hpair
                (sepConj_mono (ikpStructLoopOf_entails_of A.repAlloc (s.sp + 48#64) bs.length m)
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (decodeErrorWith_entails_at A.repAlloc (s2.readReg64 (Reg.gpr 1#5)) 0)))))))))))
            rw [hstack]; apply entails_of_eq
            simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
            sep_ac_rfl)
        (decodeErr_616_placed_wp d (x := x) (st := M.stepEvents evs st) (fuel := fuel) (maxLen := maxLen)
          (hnone hd)
          (hregs2.base.of_steps hcrl3 (by simp [*, hregs2.base.sp, arm64_norm])
            (by simp [*, hregs2.base.trace, arm64_norm]) (by simp [*, hregs2.base.x26, arm64_norm])
            (by simp [*, hregs2.base.x27, arm64_norm]) (by simp [*, hregs2.base.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, hregs2.x19, arm64_norm]) (by simp [*, hregs2.x24, arm64_norm])
          (by simp [*, arm64_norm])))
      fun sf Pf h => ikpExitPostPlaced_prepend_iter (RecordCodecIterEnv.of_decodeVarintSlow hevs) h

end LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopVarintBudget
