/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopError
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `IdentityKeyPair::try_from` Error Cleanup and Convergence

`RustCliAllocBudget`-threaded convergence invariant at `+812` and `DecodeError` cleanup tail
(`+616 .. +684` → `+812`) on Block `84`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget

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
  (IkpBaseStatePlaced IkpLoopRegsPlaced ikpStructOf ikpStructAt ikpStructLoopOf
   ikpFold144 ikpResult_err_spe2 memRegion72_split_err)
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.TripleRatchet
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
open LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.DefsBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section LoopHelpersStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_lhb (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_lhb (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem pc_setMem_lhb (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem status_setMem_lhb (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setMem_lhb (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPState_lhb (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by
  cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_advancePC_lhb (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg64_gpr_lhb (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg32_gpr_lhb (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeReg_gpr_lhb (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_lhb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_lhb (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPState_lhb (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_lhb (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_lhb (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPState_lhb (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_lhb (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_lhb (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPState_lhb (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

end LoopHelpersStateSimp

def ikpExitMemPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (fuel maxLen : Nat)
    (sp' ret ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Except SignalProtocolError IdentityKeyPair) (sf : State) : SepProp :=
  memRegion sp' 144 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
    identityKeyPairResultAt A.repAlloc ret out ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗
    (∃∗ evs : List AllocEvent, ⌜IkpSubEnv fuel maxLen evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
    stackAt sp' (skipFieldStackX 100)

def ikpExitPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (fuel maxLen : Nat)
    (s0 : State) (sp' ret ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Except SignalProtocolError IdentityKeyPair) (sf : State) (Pf : SepProp) : Prop :=
  IkpBaseStatePlaced s0 sp' sf ∧ (Pf ⊢ ikpExitMemPlaced A lim st fuel maxLen sp' ret ptr bs out sf)

theorem ikpExitPostPlaced_prepend_iter [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {evs₁ : List AllocEvent} (h1 : RecordCodecIterEnv maxLen evs₁)
    {s0 : State} {sp' ret ptr : BitVec 64} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError IdentityKeyPair} {sf : State} {Pf : SepProp}
    (h : ikpExitPostPlaced A lim (M.stepEvents evs₁ st) fuel maxLen s0 sp' ret ptr bs out sf Pf) :
    ikpExitPostPlaced A lim st (fuel + 1) maxLen s0 sp' ret ptr bs out sf Pf := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, Entails.trans hent ?_⟩
  unfold ikpExitMemPlaced
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))))
  refine Entails.sepExists_elim fun evs₂ => Entails.pure_left fun h2 => ?_
  rw [← M.stepEvents_append]
  refine Entails.sepExists_right (evs₁ ++ evs₂) ?_
  rw [pure_true_emp (IkpSubEnv.prepend_iter h1 h2), emp_sepConj]
  exact Entails.refl _

theorem ikpExitPostPlaced_prepend_bytes [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {budget maxLen : Nat}
    {wt : WireType} {valCap : BitVec 64} {bsB v rest : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bsB = some (v, rest)) (hlen : bsB.length ≤ maxLen)
    (hevs₁ : evs₁ =
      LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore wt valCap bsB)
    {s0 : State} {sp' ret ptr : BitVec 64} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError IdentityKeyPair} {sf : State} {Pf : SepProp}
    (h : ikpExitPostPlaced A lim (M.stepEvents evs₁ st) budget maxLen s0 sp' ret ptr bs out sf Pf) :
    ikpExitPostPlaced A lim st (budget + 2 * v.length + 1) maxLen s0 sp' ret ptr bs out sf Pf := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, Entails.trans hent ?_⟩
  unfold ikpExitMemPlaced
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))))
  refine Entails.sepExists_elim fun evs₂ => Entails.pure_left fun h2 => ?_
  rw [← M.stepEvents_append]
  refine Entails.sepExists_right (evs₁ ++ evs₂) ?_
  rw [pure_true_emp (IkpSubEnv.prepend_bytes hm hlen hevs₁ h2), emp_sepConj]
  exact Entails.refl _

theorem ikpExitPostPlaced_mono_fuel [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {f₁ f₂ maxLen : Nat}
    (hle : f₁ ≤ f₂)
    {s0 : State} {sp' ret ptr : BitVec 64} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError IdentityKeyPair} {sf : State} {Pf : SepProp}
    (h : ikpExitPostPlaced A lim st f₁ maxLen s0 sp' ret ptr bs out sf Pf) :
    ikpExitPostPlaced A lim st f₂ maxLen s0 sp' ret ptr bs out sf Pf := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, Entails.trans hent ?_⟩
  unfold ikpExitMemPlaced
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))))
  refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
  refine Entails.sepExists_right evs ?_
  rw [pure_true_emp (hevs.mono_fuel hle), emp_sepConj]
  exact Entails.refl _

theorem ikp_advance_cursor_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {H : LibsignalHooks} {s0 s : State} {sp' ret ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {k : Nat} {R : SepProp}
    {out : Except SignalProtocolError IdentityKeyPair}
    (hkl : k ≤ bs.length) (hrest : rest = bs.drop k)
    (hsub : Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (sliceCursorAt (sp' + 32#64) (ptr + BitVec.ofNat 64 k) rest ∗ R)
      (ikpExitPostPlaced A lim st fuel maxLen s0 sp' ret (ptr + BitVec.ofNat 64 k) rest out)
      (noPanicQp s0)) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (sliceCursorAfter (sp' + 32#64) ptr bs rest ∗ R)
      (ikpExitPostPlaced A lim st fuel maxLen s0 sp' ret ptr bs out) (noPanicQp s0) := by
  have hk_eq : bs.length - rest.length = k := by rw [hrest, List.length_drop]; omega
  have hsplit := CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers.pointsToBytes_take_drop k bs ptr hkl
  rw [← hrest] at hsplit
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 32#64) (ptr + BitVec.ofNat 64 k) rest ∗ R) ∗ (ptr ↦ₛ bs.take k))
    (by unfold sliceCursorAfter sliceCursorAt; rw [hk_eq, hsplit]; apply entails_of_eq; ac_rfl) ?_
  refine sepWPp_frame_noPanic
    (Q' := ikpExitPostPlaced A lim st fuel maxLen s0 sp' ret (ptr + BitVec.ofNat 64 k) rest out)
    hsub fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  unfold ikpExitMemPlaced; rw [hsplit]; apply entails_of_eq; ac_rfl

theorem decodeErr_660_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {x : DecodeGhost} {st : M.σ} {s0 s : State}
    {sp' errPtr : BitVec 64}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (660)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx24 : s.readReg64 .x24 = speWord 9)
    (hx20 : s.readReg64 .x20 = errPtr) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion x.ret 72 ∗ decodeErrorAt A.repAlloc errPtr ∗ A.pool lim st s ∗
        stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          (∃∗ evsD : List AllocEvent, ⌜DropDecodeErrorEnv evsD⌝ ∗
            A.pool lim (M.stepEvents evsD st) sf) ∗
          stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  have hcall := ikp_dropDecodeError_placed_ok d
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (memRegion72_split_err x.ret)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w1 =>
    Wire.SepWPp.exists_pre fun b0 => ?_
  have hsp_subst := hst.sp; subst hsp_subst
  have hstack := stackAt_sub_split s.sp dropDecodeErrorStackX (skipFieldStackX 100)
  refine sepWPp_of_sepWP_lscro hst.crl (mid := lsmpl.base 4) ?_; wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (errPtr, st) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hst.spAligned) hcrl1
    (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (668))
    (by simp_all [hst.trace, arm64_norm])
    (T := decodeErrorAt A.repAlloc errPtr ∗ A.pool lim st s ∗ stackAt s.sp dropDecodeErrorStackX)
    (φ := errPtr = errPtr)
    (by simp_all (config := { decide := true }) [Prost.DefsBudget.dropDecodeErrorSpecX, Prost.DefsBudget.dropDecodeErrorSpecGen, arm64_norm, wp_norm])
    rfl (by rw [hstack]; sep_focus) ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [Prost.DefsBudget.dropDecodeErrorSpecX, Prost.DefsBudget.dropDecodeErrorSpecGen]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_left]
  refine Wire.SepWPp.exists_pre fun evsD => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hevsD => ?_
  have hx19_2 : s2.readReg64 .x19 = x.ret := hcs2.1.trans (by simp_all [arm64_norm])
  have hx24_2 : s2.readReg64 .x24 = speWord 9 := hcs2.2.2.2.2.2.1.trans (by simp_all [arm64_norm])
  refine sepWPp_of_sepWP_end_noPanic_lscro hcrl2 ?_
  wp_steps_sync_pool ((blkPl_84).base + bv% (812))
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl3
  have hst1 := hst.of_steps hcrl1 rfl
    (by simp_all [hst.trace, arm64_norm]) (by simp_all [hst.x26, arm64_norm])
    (by simp_all [hst.x27, arm64_norm]) (by simp_all [hst.x28, arm64_norm])
  have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hst1.trace) hcs2
  refine ⟨hst2.of_steps hcrl3 (by simp_all [hst2.sp, arm64_norm])
    (by simp_all [hst2.trace, arm64_norm]) (by simp_all [hst2.x26, arm64_norm])
    (by simp_all [hst2.x27, arm64_norm]) (by simp_all [hst2.x28, arm64_norm]), ?_⟩
  have hspe : speWord 9 - 7#64 = speWord 2 := rfl
  have hres := ikpResult_err_spe2 A.repAlloc x.ret w2 htry_err
  simp only [arm64_norm, hspe]
  refine Entails.sepExists_right evsD ?_
  rw [pure_true_emp hevsD, emp_sepConj]
  refine Entails.trans ?_ (sepConj_mono_left hres)
  apply entails_of_eq; rw [hstack]; ac_rfl

theorem decodeErr_640_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {x : DecodeGhost} {st : M.σ} {s0 s : State}
    {sp' skCap skPtr errPtr : BitVec 64} {skBs : List (BitVec 8)}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (640)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx24 : s.readReg64 .x24 = speWord 9)
    (hx20 : s.readReg64 .x20 = errPtr) (hx21 : s.readReg64 .x21 = skCap)
    (hx22 : s.readReg64 .x22 = skPtr) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (vecU8Buf A.repAlloc skCap skPtr skBs ∗ memRegion x.ret 72 ∗
        decodeErrorAt A.repAlloc errPtr ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseStatePlaced s0 sp' sf ∧
        (Pf ⊢ identityKeyPairResultAt A.repAlloc x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
          (∃∗ e2 : List AllocEvent, ∃∗ evsD : List AllocEvent,
            ⌜OptByteFreeEnv e2 ∧ DropDecodeErrorEnv evsD⌝ ∗
            A.pool lim (M.stepEvents (e2 ++ evsD) st) sf) ∗
          stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  by_cases hcap : skCap = 0#64
  · subst hcap; rw [vecU8Buf_zero]; refine Wire.SepWPp.pure_pre fun _ => ?_
    have _hsp_eq := hst.sp
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (660)) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_mono_post
      (Wire.SepWPp.mono_pre
        (by apply entails_of_eq; simp only [arm64_norm]; ac_rfl)
        (decodeErr_660_placed_wp (st := st) d htry_err
          (hst.of_steps hcrl1 (by simp_all [arm64_norm]) (by simp_all [hst.trace, arm64_norm])
            (by simp_all [hst.x26, arm64_norm]) (by simp_all [hst.x27, arm64_norm])
            (by simp_all [hst.x28, arm64_norm]))
          (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
          (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf
        (sepConj_mono_right (sepConj_mono_left ?_))⟩
    refine Entails.sepExists_elim fun evsD => Entails.pure_left fun hd => ?_
    refine Entails.sepExists_right [] (Entails.sepExists_right evsD ?_)
    rw [pure_true_emp ⟨OptByteFreeEnv.nil, hd⟩, emp_sepConj, List.nil_append]
    exact Entails.refl _
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc skCap skPtr skBs hcap)) ?_
    simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_placed_ok d
    have hsp_subst := hst.sp; subst hsp_subst
    have hstack := stackAt_sub_split s.sp extHookStack (skipFieldStackX 100)
    have _hne : (skCap == 0#64) = false := beq_false_of_ne hcap
    refine sepWPp_of_sepWP_lscro hst.crl (mid := lsρ lsRustDeallocSym) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (skPtr, skCap.toNat, 1, st) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hcrl1
      (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (660))
      (by simp_all [hst.trace, arm64_norm])
      (T := A.pool lim st s ∗ A.live skPtr skCap.toNat 1 ∗ memRegion skPtr skCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := skPtr = skPtr ∧ skCap.toNat = skCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk skCap.toNat 1)
      (by simp_all (config := { decide := true }) [Hooks2Budget.rustDeallocExternSpecWithStack, IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, rustCliDeallocBudgetExternSpecWithStack, arm64_norm, wp_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt, by decide⟩
      (by rw [RustCliAllocBudget.repAlloc_live, hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [Hooks2Budget.rustDeallocExternSpecWithStack,
      IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hst1 := hst.of_steps hcrl1 rfl
      (by simp_all [hst.trace, arm64_norm]) (by simp_all [hst.x26, arm64_norm])
      (by simp_all [hst.x27, arm64_norm]) (by simp_all [hst.x28, arm64_norm])
    have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hst1.trace) hcs2
    have hsp2_eq : s2.sp = s.sp := hst2.sp
    refine Wire.SepWPp.mono_pre
      (P' := memRegion x.ret 72 ∗ decodeErrorAt A.repAlloc errPtr ∗
        A.pool lim (M.stepEvents (rustDeallocEvents skCap.toNat 1) st) s2 ∗
        stackAt s.sp (skipFieldStackX 100))
      (by apply entails_of_eq; simp only [arm64_norm]; rw [hstack]; ac_rfl) ?_
    refine sepWPp_mono_post
      (decodeErr_660_placed_wp d htry_err hst2 hpc2 hrun2
        (hcs2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.2.2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.1.trans (by simp_all [arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf
        (sepConj_mono_right (sepConj_mono_left ?_))⟩
    refine Entails.sepExists_elim fun evsD => Entails.pure_left fun hd => ?_
    rw [← M.stepEvents_append]
    refine Entails.sepExists_right (rustDeallocEvents skCap.toNat 1) (Entails.sepExists_right evsD ?_)
    rw [pure_true_emp ⟨OptByteFreeEnv.dealloc hpos hlt, hd⟩, emp_sepConj]
    exact Entails.refl _

theorem decodeErr_616_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {x : DecodeGhost} {st : M.σ} {fuel maxLen : Nat}
    {s0 s : State} {sp' ptr errPtr : BitVec 64}
    {bs : List (BitVec 8)} {mErr : IdentityKeyPairStructure}
    (htry_err : IdentityKeyPair.tryFrom x.bytes = .error .invalidProtobufEncoding)
    (hst : IkpBaseStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_84).base + bv% (616)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret) (hx24 : s.readReg64 .x24 = speWord 9)
    (hx20 : s.readReg64 .x20 = errPtr) :
    Wire.SepWPp (lsProg_84 H) ((blkPl_84).base + bv% (812)) s
      (memRegion sp' 32 ∗ memRegion (sp' + 32#64) 16 ∗ ikpStructOf A.repAlloc (sp' + 48#64) mErr ∗
        memRegion (sp' + 96#64) 48 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
        memRegion x.ret 72 ∗ (ptr ↦ₛ bs) ∗ lsLogOff ∗ A.pool lim st s ∗
        stackAt sp' (skipFieldStackX 100) ∗ decodeErrorAt A.repAlloc errPtr)
      (ikpExitPostPlaced A lim st fuel maxLen s0 sp' x.ret ptr bs (IdentityKeyPair.tryFrom x.bytes))
      (noPanicQp s0) := by
  unfold ikpStructOf ikpStructAt
  simp only [vecU8At_eq_header_buf, vecHeader, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun pk => Wire.SepWPp.exists_pre fun sk => ?_
  by_cases hcap : pk.cap = 0#64
  · rw [hcap, vecU8Buf_zero]; simp only [sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun _ => ?_
    have hsp_subst := hst.sp; subst hsp_subst
    have _hsp_align := hst.spAligned
    refine sepWPp_of_sepWP_lscro hst.crl (mid := (blkPl_84).base + bv% (640)) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    have h144 := ikpFold144 s.sp 0#64 pk.ptr (BitVec.ofNat 64 mErr.publicKey.length)
      sk.cap sk.ptr (BitVec.ofNat 64 mErr.privateKey.length)
    dsimp only [vecHeader] at h144; simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
    have hst_next := hst.of_steps hcrl1 rfl (by simp_all [hst.trace, arm64_norm])
      (by simp_all [hst.x26, arm64_norm]) (by simp_all [hst.x27, arm64_norm])
      (by simp_all [hst.x28, arm64_norm])
    refine Wire.SepWPp.mono_pre ?_
      (sepWPp_frame_noPanic
        (F := memRegion s.sp 144 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗ (ptr ↦ₛ bs) ∗ lsLogOff)
        (decodeErr_640_placed_wp (st := st)
          (skCap := sk.cap) (skPtr := sk.ptr) (errPtr := errPtr) (skBs := mErr.privateKey)
          d htry_err hst_next
          (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
          (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
          (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]))
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩)
    · refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left h144))
      apply entails_of_eq; simp only [arm64_norm]; ac_rfl
    · unfold ikpExitMemPlaced
      refine Entails.trans (sepConj_mono_left hentf) ?_
      have hev_lift :
          (∃∗ e2 : List AllocEvent, ∃∗ evsD : List AllocEvent,
            ⌜OptByteFreeEnv e2 ∧ DropDecodeErrorEnv evsD⌝ ∗
            A.pool lim (M.stepEvents (e2 ++ evsD) st) sf) ⊢
          ∃∗ evs : List AllocEvent, ⌜IkpSubEnv fuel maxLen evs⌝ ∗
            A.pool lim (M.stepEvents evs st) sf := by
        refine Entails.sepExists_elim fun e2 => Entails.sepExists_elim fun evsD =>
          Entails.pure_left fun ⟨he2, hd⟩ => ?_
        have hc : IkpSubEnv fuel maxLen ([] ++ (e2 ++ evsD)) :=
          IkpSubEnv.of_cleanup (IkpPostCleanupEnv.of_errCleanup
            (RecordCodecErrCleanupEnv.of_two_drop OptByteFreeEnv.nil he2 hd))
        rw [List.nil_append] at hc
        refine Entails.sepExists_right (e2 ++ evsD) ?_
        rw [pure_true_emp hc, emp_sepConj]
        exact Entails.refl _
      refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hev_lift))) ?_
      apply entails_of_eq; ac_rfl
  · have hd := vecU8Buf_dealloc A.repAlloc pk.cap pk.ptr mErr.publicKey hcap
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hd)))))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_placed_ok d
    have hsp_subst := hst.sp; subst hsp_subst
    have _hsp_align := hst.spAligned
    have hstack := stackAt_sub_split s.sp extHookStack (skipFieldStackX 100)
    have _hne : (pk.cap == 0#64) = false := beq_false_of_ne hcap
    refine sepWPp_of_sepWP_lscro hst.crl (mid := lsρ lsRustDeallocSym) ?_; wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (pk.ptr, pk.cap.toNat, 1, st) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hcrl1
      (by simp_all [arm64_norm] : _ = (blkPl_84).base + bv% (640))
      (by simp_all [hst.trace, arm64_norm])
      (T := A.pool lim st s ∗ A.live pk.ptr pk.cap.toNat 1 ∗ memRegion pk.ptr pk.cap.toNat ∗ stackAt s.sp extHookStack)
      (φ := pk.ptr = pk.ptr ∧ pk.cap.toNat = pk.cap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ RustLayoutOk pk.cap.toNat 1)
      (by simp_all (config := { decide := true }) [Hooks2Budget.rustDeallocExternSpecWithStack, IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack, rustCliDeallocBudgetExternSpecWithStack, arm64_norm, wp_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt, by decide⟩
      (by rw [RustCliAllocBudget.repAlloc_live, hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [Hooks2Budget.rustDeallocExternSpecWithStack,
      IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hst1 := hst.of_steps hcrl1 rfl
      (by simp_all [hst.trace, arm64_norm]) (by simp_all [hst.x26, arm64_norm])
      (by simp_all [hst.x27, arm64_norm]) (by simp_all [hst.x28, arm64_norm])
    have hst2 := hst1.of_calleeSaved hsp2 hsp2_align hcrl2 (htr2.trans hst1.trace) hcs2
    have h144 := ikpFold144 s.sp pk.cap pk.ptr (BitVec.ofNat 64 mErr.publicKey.length)
      sk.cap sk.ptr (BitVec.ofNat 64 mErr.privateKey.length)
    dsimp only [vecHeader] at h144; simp only [BitVec.add_assoc, BitVec.reduceAdd] at h144
    refine Wire.SepWPp.mono_pre
      (P' := (vecU8Buf A.repAlloc sk.cap sk.ptr mErr.privateKey ∗ memRegion x.ret 72 ∗
        decodeErrorAt A.repAlloc errPtr ∗
        A.pool lim (M.stepEvents (rustDeallocEvents pk.cap.toNat 1) st) s2 ∗
        stackAt s.sp (skipFieldStackX 100)) ∗
        (memRegion s.sp 144 ∗ ((s.sp + 168#64) ↦₆₄ (s.sp + 32#64)) ∗ (ptr ↦ₛ bs) ∗ lsLogOff))
      (by refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left h144))
          apply entails_of_eq; simp only [arm64_norm]; rw [hstack]; ac_rfl) ?_
    refine sepWPp_frame_noPanic
      (decodeErr_640_placed_wp (st := M.stepEvents (rustDeallocEvents pk.cap.toNat 1) st)
        d htry_err hst2 hpc2 hrun2
        (hcs2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.2.2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.1.trans (by simp_all [arm64_norm]))
        (hcs2.2.2.2.1.trans (by simp_all [arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
    unfold ikpExitMemPlaced
    refine Entails.trans (sepConj_mono_left hentf) ?_
    have hev_lift :
        (∃∗ e2 : List AllocEvent, ∃∗ evsD : List AllocEvent,
          ⌜OptByteFreeEnv e2 ∧ DropDecodeErrorEnv evsD⌝ ∗
          A.pool lim (M.stepEvents (e2 ++ evsD)
            (M.stepEvents (rustDeallocEvents pk.cap.toNat 1) st)) sf) ⊢
        ∃∗ evs : List AllocEvent, ⌜IkpSubEnv fuel maxLen evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf := by
      refine Entails.sepExists_elim fun e2 => Entails.sepExists_elim fun evsD =>
        Entails.pure_left fun ⟨he2, hd⟩ => ?_
      rw [← M.stepEvents_append]
      have hc : IkpSubEnv fuel maxLen (rustDeallocEvents pk.cap.toNat 1 ++ (e2 ++ evsD)) :=
        IkpSubEnv.of_cleanup (IkpPostCleanupEnv.of_errCleanup
          (RecordCodecErrCleanupEnv.of_two_drop (OptByteFreeEnv.dealloc hpos hlt) he2 hd))
      refine Entails.sepExists_right (rustDeallocEvents pk.cap.toNat 1 ++ (e2 ++ evsD)) ?_
      rw [pure_true_emp hc, emp_sepConj]
      exact Entails.refl _
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hev_lift))) ?_
    apply entails_of_eq; ac_rfl

def ikpLoopCommonPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (sp' ret : BitVec 64)
    (len : Nat) (m : IdentityKeyPairStructure) (s : State) : SepProp :=
  memRegion sp' 32 ∗ ikpStructLoopOf A.repAlloc (sp' + 48#64) len m ∗
    memRegion (sp' + 96#64) 48 ∗ ((sp' + 168#64) ↦₆₄ (sp' + 32#64)) ∗
    memRegion ret 72 ∗ lsLogOff ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)

end LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.LoopErrorBudget
