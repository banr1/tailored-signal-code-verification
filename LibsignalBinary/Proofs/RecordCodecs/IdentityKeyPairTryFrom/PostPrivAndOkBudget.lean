/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPrivAndOk
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `IdentityKeyPair::try_from` Private-Key Validation and `Ok` Packing

`RustCliAllocBudget`-threaded relocatable proof of the 32-byte private-key check, inline scalar
clamping, and `Ok` result packing (`+396 .. +568` → `+812`) on Block `84`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPrivAndOkBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary (DecodeGhost identityKeyPairResultAt
  sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers
  (IkpBaseStatePlaced memRegion72_split_err memRegion72_split_ok memRegion32_split_scratch
   ikpScratch32 ikpScratch32_entails_memRegion32 pkCells skCells vector32_exists_skCells
   ikpResult_err_spe9)
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.TripleRatchet
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PostPrivStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_ikpb (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_ikpb (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem pc_setMem_ikpb (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem status_setMem_ikpb (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setMem_ikpb (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPState_ikpb (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_advancePC_ikpb (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg64_gpr_ikpb (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg32_gpr_ikpb (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg_gpr_ikpb (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_ikpb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_ikpb (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPState_ikpb (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_ikpb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_ikpb (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPState_ikpb (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_ikpb (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_ikpb (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPState_ikpb (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓]
private theorem bfm32_clamp_ikpb1 : ∀ b : BitVec 8,
    (Arm64.evalBitfield .W32 .BFM 64#64 (b.zeroExtend 64) 0 5).setWidth 8 =
      (b &&& 0x7f#8) ||| 0x40#8 := by decide

@[local arm64_norm ↓]
private theorem bfm32_clamp_ikpb2 : ∀ b : BitVec 8,
    (Arm64.evalBitfield .W32 .BFM 64#64 ((b.zeroExtend 32).zeroExtend 64) 0 5).setWidth 8 =
      (b &&& 0x7f#8) ||| 0x40#8 := by decide

end PostPrivStateSimp

private theorem clamp_b0_post (b : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b &&& 1065151889656#64) = b &&& 248#8 := by
  revert b; decide

private theorem clamp_b31_post (b : BitVec 8) :
    BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 b >>> 0 &&& 63#64) =
      (b &&& 127#8) ||| 64#8 := by
  revert b; decide

theorem err_store_760_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {x : DecodeGhost} {st : M.σ} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr w24 w25 : BitVec 64} {pkBs skBs : List (BitVec 8)}
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (760)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx24 : s.readReg64 .x24 = w24) (hx25 : s.readReg64 .x25 = w25)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr)
    (herr : (x.ret ↦₈ 1#8) ∗ memRegion (x.ret + 1#64) 7 ∗
      ((x.ret + 8#64) ↦₆₄ w24) ∗ ((x.ret + 16#64) ↦₆₄ w25) ∗
      memRegion (x.ret + 24#64) 48 ⊢
      identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes)) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion x.ret 72 ∗ vecU8Buf A.repAlloc pkCap pkPtr pkBs ∗
        vecU8Buf A.repAlloc skCap skPtr skBs ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗
            A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (memRegion72_split_err x.ret)) ?_
  (conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc])
  refine Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w1 =>
    Wire.SepWPp.exists_pre fun b0 => ?_
  try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10,
    Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
    Reg.x28, Reg.x29, Reg.x30] at *
  have hsp_eq := hst.sp
  refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (772)) ?_
  wp_steps_sync_pool ((blkPl_84).base + bv% (772))
  refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre ?_
    (sepWPp_frame_noPanic
      (F := identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes))
      (cleanup_pk_sk_772_placed_wp (st := st)
        (pkCap := pkCap) (pkPtr := pkPtr) (skCap := skCap) (skPtr := skPtr)
        (pkBs := pkBs) (skBs := skBs) d
        (hst.of_steps hcrl1 (by tryFromPost_sp [hsp_eq])
          (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
          (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm]))
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
        (by simp [*, arm64_norm]) (by simp [*, arm64_norm]))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩)
  · try simp only [arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right herr))))
    apply entails_of_eq; ac_rfl
  · refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; ac_rfl

private theorem cleanup_pk_sk_564_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {st : M.σ} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr : BitVec 64} {pkBs skBs : List (BitVec 8)}
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (564)) (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (vecU8Buf A.repAlloc pkCap pkPtr pkBs ∗ vecU8Buf A.repAlloc skCap skPtr skBs ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗ stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  by_cases hcap : pkCap = 0#64
  · subst hcap; rw [vecU8Buf_zero]; refine Wire.SepWPp.pure_pre fun _ => ?_
    have _hsp_eq := hst.sp
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (792)) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_mono_post
      (Wire.SepWPp.mono_pre
        (by apply entails_of_eq; simp only [arm64_norm]; ac_rfl)
        (cleanup_sk_792_placed_wp (st := st) d
          (hst.of_steps hcrl1 (by simp_all [arm64_norm]) (by simp_all [hst.trace, arm64_norm])
            (by simp_all [hst.x26, arm64_norm]) (by simp_all [hst.x27, arm64_norm])
            (by simp_all [hst.x28, arm64_norm]))
          (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
          (by simp_all [arm64_norm]) (by simp_all [arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf (sepConj_mono_left ?_)⟩
    refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
    refine Entails.sepExists_right evs ?_
    rw [pure_true_emp (TwoOptByteFreeEnv.single hevs), emp_sepConj]
    exact Entails.refl _
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc pkCap pkPtr pkBs hcap)) ?_
    simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_placed_ok d
    have hsp_eq := hst.sp
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have _hne1 : (pkCap == 0#64) = false := beq_false_of_ne hcap
    have _hne2 : (pkCap != 0#64) = true := bne_iff_ne.mpr hcap
    refine sepWPp_of_sepWP_lscro hst.crl (mid := lsρ lsRustDeallocSym) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (pkPtr, pkCap.toNat, 1, st) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hcrl1
      (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (792))
      (by simp_all [hst.trace, arm64_norm])
      (T := A.pool lim st s ∗ A.live pkPtr pkCap.toNat 1 ∗ memRegion pkPtr pkCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := pkPtr = pkPtr ∧ pkCap.toNat = pkCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        RustLayoutOk pkCap.toNat 1 ∧ LsRetAddr624 ((blkPl_84).base + bv% (792)))
      (by simp_all [Hooks2Budget.rustDeallocExternSpecWithStack, rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, ⟨layoutOk_align1 hpos hlt, by decide⟩,
        lsRetAddr624_blockPlacement_base_add 84 (bv% (792)) (by decide) (by decide)⟩
      (by rw [RustCliAllocBudget.repAlloc_live, hstack, hsp_eq]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [Hooks2Budget.rustDeallocExternSpecWithStack,
      IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hst2 : IkpBaseStatePlaced s0 sp' s2 := {
      sp := hsp2.trans (by tryFromPost_sp [hsp_eq])
      spAligned := hsp2_align
      crl := hcrl2
      trace := htr2.trans (by simp_all [hst.trace, arm64_norm])
      x26 := hcs2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x26, arm64_norm])
      x27 := hcs2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x27, arm64_norm])
      x28 := hcs2.2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x28, arm64_norm])
    }
    have hx21_2 : s2.readReg64 .x21 = skCap := hcs2.2.2.1.trans (by simp_all [arm64_norm])
    have hx23_2 : s2.readReg64 .x23 = skPtr := hcs2.2.2.2.2.1.trans (by simp_all [arm64_norm])
    refine Wire.SepWPp.mono_pre
      (P' := vecU8Buf A.repAlloc skCap skPtr skBs ∗
        A.pool lim (M.stepEvents (rustDeallocEvents pkCap.toNat 1) st) s2 ∗
        stackAt sp' (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [arm64_norm]; try rw [hsp_eq]; rw [hstack]; ac_rfl) ?_
    refine sepWPp_mono_post
      (cleanup_sk_792_placed_wp d hst2 hpc2 hrun2 hx21_2 hx23_2)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf (sepConj_mono_left ?_)⟩
    refine Entails.sepExists_elim fun evs2 => Entails.pure_left fun hevs2 => ?_
    rw [← M.stepEvents_append]
    refine Entails.sepExists_right (rustDeallocEvents pkCap.toNat 1 ++ evs2) ?_
    rw [pure_true_emp (TwoOptByteFreeEnv.pair (OptByteFreeEnv.dealloc hpos hlt) hevs2), emp_sepConj]
    exact Entails.refl _

theorem post_pk_ok_396_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {x : DecodeGhost} {st : M.σ} {s0 s : State}
    {sp' pkCap pkPtr skCap skPtr : BitVec 64} {m : IdentityKeyPairStructure} {pk : PublicKey}
    (hdec : IdentityKeyPairStructure.decode x.bytes = some m)
    (hpk : PublicKey.deserialize m.publicKey = .ok pk) (hsk_lt : m.privateKey.length < 2 ^ 64)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (396)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx29 : s.readReg64 .x29 = sp' + 144#64)
    (hx24 : s.readReg64 .x24 = speWord 9)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 m.privateKey.length)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr)
    {w0 : BitVec 64} {b8 : BitVec 8} {w9 : BitVec 32} {h13 : BitVec 16}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (hpk_cells : ∀ a : BitVec 64, (a ↦ₛ pk.bytes.toList) = pkCells w0 b8 w9 h13 w15 w23 b31 a)
    (hx8 : s.readReg64 .x8 = b8.zeroExtend 64) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion sp' 32 ∗ ((sp' + 96#64) ↦₈ 0#8) ∗
        pkCells w0 b8 w9 h13 w15 w23 b31 (sp' + 97#64) ∗
        memRegion (sp' + 129#64) 15 ∗ memRegion x.ret 72 ∗
        vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ∗ vecU8Buf A.repAlloc skCap skPtr m.privateKey ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 32 ∗ memRegion (sp' + 96#64) 48 ∗
          identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          (∃∗ evs : List AllocEvent, ⌜TwoOptByteFreeEnv evs⌝ ∗
            A.pool lim (M.stepEvents evs st) sf) ∗
          stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  have hfold96 : ((sp' + 96#64) ↦₈ 0#8) ∗ pkCells w0 b8 w9 h13 w15 w23 b31 (sp' + 97#64) ∗
      memRegion (sp' + 129#64) 15 ⊢ memRegion (sp' + 96#64) 48 := by
    rw [← hpk_cells (sp' + 97#64)]
    have hm1 : ((sp' + 96#64) ↦₈ 0#8) ⊢ memRegion (sp' + 96#64) 1 := by
      rw [memRegion_one]; exact sepExists_intro _ 0#8
    have hm32 : ((sp' + 97#64) ↦ₛ pk.bytes.toList) ⊢ memRegion (sp' + 97#64) 32 := by
      simpa [pk.bytes.2] using pointsToBytes_entails_memRegion (sp' + 97#64) pk.bytes.toList
    rw [show (48 : Nat) = 1 + (32 + 15) by decide,
      Prost.memRegion_split (sp' + 96#64) 1 47 (by decide),
      Prost.memRegion_split (sp' + 96#64 + 1#64) 32 15 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono hm1 (sepConj_mono_left hm32)
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (memRegion32_split_scratch sp')) ?_
  (conv => arg 4; simp only [sepExists_sepConj_left, ikpScratch32, pkCells, sepConj_assoc])
  refine Wire.SepWPp.exists_pre fun sh28 => Wire.SepWPp.exists_pre fun sw24 =>
    Wire.SepWPp.exists_pre fun sb16 => Wire.SepWPp.exists_pre fun sw8 => ?_
  by_cases hlen32 : m.privateKey.length = 32
  · have htry_ok : IdentityKeyPair.tryFrom x.bytes =
        .ok ⟨⟨pk⟩, ⟨Ratchet.clampScalar ⟨m.privateKey, hlen32⟩⟩⟩ := by
      unfold IdentityKeyPair.tryFrom decodeIdentityKey deserializePrivateKey
      simp [hdec, hpk, hlen32, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
    obtain ⟨b0_s, w1_s, h5_s, h7_s, w9_s, h13_s, w15_s, w23_s, b31_s, hsk_src, hsk_dst⟩ :=
      vector32_exists_skCells ⟨m.privateKey, hlen32⟩
    have hpre_unpack :
        memRegion sp' 8 ∗ ((sp' + 8#64) ↦₆₄ sw8) ∗ ((sp' + 16#64) ↦₈ sb16) ∗
        memRegion (sp' + 17#64) 7 ∗ ((sp' + 24#64) ↦₃₂ sw24) ∗ ((sp' + 28#64) ↦₁₆ sh28) ∗
        memRegion (sp' + 30#64) 2 ∗ ((sp' + 96#64) ↦₈ 0#8) ∗
        ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 97#64 + 8#64) ↦₈ b8) ∗
        ((sp' + 97#64 + 9#64) ↦₃₂ w9) ∗ ((sp' + 97#64 + 13#64) ↦₁₆ h13) ∗
        ((sp' + 97#64 + 15#64) ↦₆₄ w15) ∗ ((sp' + 97#64 + 23#64) ↦₆₄ w23) ∗
        ((sp' + 97#64 + 31#64) ↦₈ b31) ∗ memRegion (sp' + 129#64) 15 ∗
        memRegion x.ret 72 ∗ vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ∗
        vecU8Buf A.repAlloc skCap skPtr m.privateKey ∗ A.pool lim st s ∗
        stackAt sp' (skipFieldStackX 100) ⊢
        ∃∗ sb0 : BitVec 8, ∃∗ sw1 : BitVec 32, ∃∗ sh5 : BitVec 16, ∃∗ sh7 : BitVec 16,
        ∃∗ sw9 : BitVec 32, ∃∗ sh13 : BitVec 16, ∃∗ sw15 : BitVec 64, ∃∗ sw23 : BitVec 64,
        ∃∗ sb31 : BitVec 8,
        ∃∗ dw0 : BitVec 64, ∃∗ db8 : BitVec 8, ∃∗ dw9 : BitVec 32, ∃∗ dh13 : BitVec 16,
        ∃∗ dw15 : BitVec 64, ∃∗ dw23 : BitVec 64, ∃∗ db31 : BitVec 8,
        ∃∗ b_tag : BitVec 8,
          memRegion sp' 8 ∗ ((sp' + 8#64) ↦₆₄ sw8) ∗ ((sp' + 16#64) ↦₈ sb16) ∗
          memRegion (sp' + 17#64) 7 ∗ ((sp' + 24#64) ↦₃₂ sw24) ∗ ((sp' + 28#64) ↦₁₆ sh28) ∗
          memRegion (sp' + 30#64) 2 ∗ ((sp' + 96#64) ↦₈ 0#8) ∗
          ((sp' + 97#64) ↦₆₄ w0) ∗ ((sp' + 97#64 + 8#64) ↦₈ b8) ∗
          ((sp' + 97#64 + 9#64) ↦₃₂ w9) ∗ ((sp' + 97#64 + 13#64) ↦₁₆ h13) ∗
          ((sp' + 97#64 + 15#64) ↦₆₄ w15) ∗ ((sp' + 97#64 + 23#64) ↦₆₄ w23) ∗
          ((sp' + 97#64 + 31#64) ↦₈ b31) ∗ memRegion (sp' + 129#64) 15 ∗
          (x.ret ↦₈ b_tag) ∗ pkCells dw0 db8 dw9 dh13 dw15 dw23 db31 (x.ret + 1#64) ∗
          skCells sb0 sw1 sh5 sh7 sw9 sh13 sw15 sw23 sb31 (x.ret + 0x21#64) ∗
          memRegion (x.ret + 0x41#64) 7 ∗ vecU8Buf A.repAlloc pkCap pkPtr m.publicKey ∗
          skCells b0_s w1_s h5_s h7_s w9_s h13_s w15_s w23_s b31_s skPtr ∗
          vecU8BufRest A.repAlloc skCap skPtr m.privateKey ∗ A.pool lim st s ∗
          stackAt sp' (skipFieldStackX 100) := by
      have hsk_ent : vecU8Buf A.repAlloc skCap skPtr m.privateKey ⊢
          skCells b0_s w1_s h5_s h7_s w9_s h13_s w15_s w23_s b31_s skPtr ∗
            vecU8BufRest A.repAlloc skCap skPtr m.privateKey := by
        refine Entails.trans (vecU8Buf_entails_slice_rest A.repAlloc skCap skPtr m.privateKey) ?_
        refine Entails.pure_left fun _ => ?_; rw [hsk_src skPtr]; exact Entails.refl _
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono (memRegion72_split_ok x.ret)
                  (sepConj_mono_right (sepConj_mono_left hsk_ent))))))))))))))))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      exact Entails.refl _
    refine Wire.SepWPp.mono_pre hpre_unpack ?_; clear hpre_unpack
    refine Wire.SepWPp.exists_pre fun sb0 => Wire.SepWPp.exists_pre fun sw1 =>
      Wire.SepWPp.exists_pre fun sh5 => Wire.SepWPp.exists_pre fun sh7 =>
      Wire.SepWPp.exists_pre fun sw9 => Wire.SepWPp.exists_pre fun sh13 =>
      Wire.SepWPp.exists_pre fun sw15 => Wire.SepWPp.exists_pre fun sw23 =>
      Wire.SepWPp.exists_pre fun sb31 =>
      Wire.SepWPp.exists_pre fun dw0 => Wire.SepWPp.exists_pre fun db8 =>
      Wire.SepWPp.exists_pre fun dw9 => Wire.SepWPp.exists_pre fun dh13 =>
      Wire.SepWPp.exists_pre fun dw15 => Wire.SepWPp.exists_pre fun dw23 =>
      Wire.SepWPp.exists_pre fun db31 => Wire.SepWPp.exists_pre fun b_tag => ?_
    (conv => arg 4; simp only [pkCells, skCells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc])
    have hcall := ikp_dealloc_placed_ok d
    try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30] at *
    have hsp_subst := hst.sp; subst hsp_subst
    have _hsp_align := hst.spAligned
    have hsp_eq : s.sp = s.sp := rfl
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (564)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (564))
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (sepWPp_frame_noPanic
        (F := memRegion s.sp 32 ∗ memRegion (s.sp + 96#64) 48 ∗
          identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes))
        (cleanup_pk_sk_564_placed_wp (st := st)
          (pkCap := pkCap) (pkPtr := pkPtr) (skCap := skCap) (skPtr := skPtr)
          (pkBs := m.publicKey) (skBs := m.privateKey) d
          (hst.of_steps hcrl1 (by tryFromPost_sp [hsp_eq])
            (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
            (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm]))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩)
    · have hok_res :
          (x.ret ↦₈ 0#8) ∗ pkCells w0 b8 w9 h13 w15 w23 b31 (x.ret + 1#64) ∗
            skCells (b0_s &&& 0xf8#8) w1_s h5_s h7_s w9_s h13_s w15_s w23_s
              ((b31_s &&& 0x7f#8) ||| 0x40#8) (x.ret + 0x21#64) ∗
            memRegion (x.ret + 0x41#64) 7 ⊢
          identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) := by
        rw [htry_ok, ← hpk_cells (x.ret + 1#64), ← hsk_dst (x.ret + 0x21#64)]
        dsimp only [identityKeyPairResultAt]; apply entails_of_eq; ac_rfl
      have hsk_fold :
          skCells b0_s w1_s h5_s h7_s w9_s h13_s w15_s w23_s b31_s skPtr ∗
            vecU8BufRest A.repAlloc skCap skPtr m.privateKey ⊢
          vecU8Buf A.repAlloc skCap skPtr m.privateKey := by
        rw [← hsk_src skPtr]; exact slice_rest_entails_vecU8Buf A.repAlloc skCap skPtr m.privateKey
      have hscr_fold := ikpScratch32_entails_memRegion32 w23 b31 w9 h13 s.sp
      dsimp only [pkCells, skCells, ikpScratch32] at hok_res hsk_fold hscr_fold hfold96
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hok_res hsk_fold hscr_fold hfold96
      refine Entails.trans ?_
        (sepConj_mono (sepConj_mono_right (sepConj_mono_left hsk_fold))
          (sepConj_mono hscr_fold (sepConj_mono hfold96 hok_res)))
      apply entails_of_eq; simp only [arm64_norm]; rw [clamp_b0_post, clamp_b31_post]; ac_rfl
    · refine Entails.trans (sepConj_mono_left hentf) ?_; apply entails_of_eq; ac_rfl
  · have hbv_ne : BitVec.ofNat 64 m.privateKey.length ≠ 32#64 := by
      intro heq; have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsk_lt] at hnat; exact hlen32 hnat
    have _hbv_bne : (BitVec.ofNat 64 m.privateKey.length != 32#64) = true := bne_iff_ne.mpr hbv_ne
    have _hbv_beq : (BitVec.ofNat 64 m.privateKey.length == 32#64) = false := beq_false_of_ne hbv_ne
    have htry_err : IdentityKeyPair.tryFrom x.bytes = .error (.badKeyLength m.privateKey.length) := by
      unfold IdentityKeyPair.tryFrom decodeIdentityKey deserializePrivateKey
      simp [hdec, hpk, hlen32, Bind.bind, Except.bind, Except.map]
    try dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x8, Reg.x9, Reg.x10,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30] at *
    have hsp_subst := hst.sp; subst hsp_subst
    have _hsp_align := hst.spAligned
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (760)) ?_
    wp_steps_sync_pool ((blkPl_84).base + bv% (760))
    refine Wire.SepWP.done (by simp [*, arm64_norm]) (by simp [*, arm64_norm]) ?_; intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (sepWPp_frame_noPanic
        (F := memRegion s.sp 32 ∗ memRegion (s.sp + 96#64) 48)
        (err_store_760_placed_wp (st := st)
          (pkCap := pkCap) (pkPtr := pkPtr) (skCap := skCap) (skPtr := skPtr)
          (pkBs := m.publicKey) (skBs := m.privateKey) d
          (hst.of_steps hcrl1 rfl
            (by simp [*, hst.trace, arm64_norm]) (by simp [*, hst.x26, arm64_norm])
            (by simp [*, hst.x27, arm64_norm]) (by simp [*, hst.x28, arm64_norm]))
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm]) (by simp [*, arm64_norm])
          (by simp [*, arm64_norm])
          (ikpResult_err_spe9 A.repAlloc x.ret m.privateKey.length htry_err))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩)
    · have hscr_fold := ikpScratch32_entails_memRegion32 w23 b31 w9 h13 s.sp
      dsimp only [pkCells, ikpScratch32] at hscr_fold hfold96
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hscr_fold hfold96
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono hscr_fold hfold96))
      apply entails_of_eq; simp only [arm64_norm]; ac_rfl
    · refine Entails.trans (sepConj_mono_left hentf) ?_; apply entails_of_eq; ac_rfl

end LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.PostPrivAndOkBudget
