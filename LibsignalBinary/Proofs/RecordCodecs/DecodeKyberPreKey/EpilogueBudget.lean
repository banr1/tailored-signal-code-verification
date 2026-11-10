/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Epilogue
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Layout
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymD
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Fetches
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.FetchesBudget
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `decode_kyber_pre_key` Epilogue Proofs

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` proofs of the `Ok`
(`+0x01c..+0x05c`) and `Err` (`+0x060..+0x080`) epilogue branches of `decode_kyber_pre_key`
(Block `595`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.EpilogueBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire CryptoVerification.RecordCodecs
open CryptoVerification
open CryptoVerification.RecordCodecs.Placed
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification.RecordCodecsBinary (DecodeGhost kyberPreKeyResultAt sepWPp_of_sepWP_lscro signedDecodeStack signedPreKeyStructAt)
open CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers (KpkSavedRegs errExit_pack kpkDecodeStack_drop_split kpkSubStack kyberDeserialize_of_none kyberDeserialize_of_some memRegion88_err_unpack memRegion88_unpack okExit_pack signedPreKeyBufs signedPreKeyStructAt_sp8_unpack words88Ret words88Sp)
open LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.FetchesBudget (dropDecodeError3_placed_call_ok noPanicQp sepWPp_call_noPanic_lscro sepWPp_end_noPanic_lscro)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (DropDecodeErrorEnv KyberDecodeEnv SpkDecodeEnv decodeKyberPreKeyRawSpec dropDecodeErrorBudgetSpec dropDecodeErrorBudgetSpecGen)
attribute [local irreducible] Program.fetch Program.externAt?

def kpkOff_retDec : BitVec 64 := 28#64
def kpkOff_retDrop : BitVec 64 := 104#64
attribute [local arm64_norm] kpkOff_retDec kpkOff_retDrop

def kpkPostPlaced {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (x : DecodeGhost) (s0 : State) :
    State → SepProp → Prop :=
  fun sf Pf =>
    sf.sp = s0.sp ∧
    (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
    (Pf ⊢ (decodeKyberPreKeyRawSpec A lim).post (x, st) s0 sf)

private theorem okExit_pack_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs1 : List AllocEvent) (sf : State)
    (sp ret bytesA : BitVec 64) (bytes : List (BitVec 8))
    (hevs1 : SpkDecodeEnv bytes.length evs1)
    (pubCap pubPtr privCap privPtr sigCap sigPtr c0 c1 c2 c3 : BitVec 64)
    (pad32 : BitVec 32) (m : SignedPreKeyRecordStructure) :
    (words88Ret ret pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
        privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
        sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
        m.timestamp (pad32 ++ m.id) ∗
      signedPreKeyBufs A.repAlloc pubCap pubPtr privCap privPtr sigCap sigPtr m) ∗
    (bytesA ↦ₛ bytes) ∗
    (memRegion (sp - 128#64) 8 ∗
      words88Sp (sp - 128#64) pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
        privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
        sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
        m.timestamp (pad32 ++ m.id) ∗
      ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
      ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
      ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
      ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
      stackAt (sp - 128#64) signedDecodeStack ∗
      memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack)) ∗
    A.pool lim (M.stepEvents evs1 st) sf ⊢
    (∃∗ evs : List AllocEvent, ⌜KyberDecodeEnv bytes.length evs⌝ ∗
      A.pool lim (M.stepEvents evs st) sf) ∗
    kyberPreKeyResultAt A.repAlloc ret (.ok ⟨m⟩) ∗
    (bytesA ↦ₛ bytes) ∗
    stackAt sp smallRootStack := by
  have hpack := okExit_pack (A.atState lim (M.stepEvents evs1 st) sf) sp ret bytesA bytes
    pubCap pubPtr privCap privPtr sigCap sigPtr c0 c1 c2 c3 pad32 m
  have hbuf_eq : signedPreKeyBufs (A.atState lim (M.stepEvents evs1 st) sf)
      pubCap pubPtr privCap privPtr sigCap sigPtr m =
      signedPreKeyBufs A.repAlloc pubCap pubPtr privCap privPtr sigCap sigPtr m := rfl
  have hres_eq : kyberPreKeyResultAt (A.atState lim (M.stepEvents evs1 st) sf) ret (.ok ⟨m⟩) =
      kyberPreKeyResultAt A.repAlloc ret (.ok ⟨m⟩) := rfl
  rw [hbuf_eq, hres_eq] at hpack
  dsimp only [RustCliAllocBudget.atState] at hpack
  have hpool : A.pool lim (M.stepEvents evs1 st) sf ⊢
      (∃∗ evs : List AllocEvent, ⌜KyberDecodeEnv bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) :=
    Entails.sepExists_right evs1 (Entails.pure_right (Or.inl hevs1) (Entails.refl _))
  simp only [sepConj_assoc] at hpack ⊢
  refine Entails.trans hpack ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hpool))) ?_
  apply entails_of_eq; ac_rfl

private theorem errExit_pack_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs1 evs2 : List AllocEvent) (sf : State)
    (sp ret bytesA e c0 c1 c2 c3 : BitVec 64) (bytes : List (BitVec 8))
    (hevs1 : SpkDecodeEnv bytes.length evs1) (hevs2 : DropDecodeErrorEnv evs2) :
    ((ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (ret + 16#64) 72) ∗
      (bytesA ↦ₛ bytes) ∗
      (memRegion (sp - 128#64) 8 ∗
        (((sp - 128#64 + 8#64) ↦₆₄ errTag) ∗ ((sp - 128#64 + 16#64) ↦₆₄ e) ∗
          memRegion (sp - 128#64 + 24#64) 72) ∗
        ((sp - 128#64 + 96#64) ↦₆₄ c0) ∗
        ((sp - 128#64 + 104#64) ↦₆₄ c1) ∗
        ((sp - 128#64 + 112#64) ↦₆₄ c2) ∗
        ((sp - 128#64 + 120#64) ↦₆₄ c3) ∗
        stackAt (sp - 128#64) signedDecodeStack ∗
        memRegion (sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack)) ∗
      A.pool lim (M.stepEvents (evs1 ++ evs2) st) sf ⊢
      (∃∗ evs : List AllocEvent, ⌜KyberDecodeEnv bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      kyberPreKeyResultAt A.repAlloc ret (.error .invalidProtobufEncoding) ∗
      (bytesA ↦ₛ bytes) ∗
      stackAt sp smallRootStack := by
  have hpack := errExit_pack (A.atState lim (M.stepEvents (evs1 ++ evs2) st) sf)
    sp ret bytesA e c0 c1 c2 c3 bytes
  have hres_eq : kyberPreKeyResultAt (A.atState lim (M.stepEvents (evs1 ++ evs2) st) sf)
      ret (.error .invalidProtobufEncoding) =
      kyberPreKeyResultAt A.repAlloc ret (.error .invalidProtobufEncoding) := rfl
  rw [hres_eq] at hpack
  dsimp only [RustCliAllocBudget.atState] at hpack
  have hpool : A.pool lim (M.stepEvents (evs1 ++ evs2) st) sf ⊢
      (∃∗ evs : List AllocEvent, ⌜KyberDecodeEnv bytes.length evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) :=
    Entails.sepExists_right (evs1 ++ evs2)
      (Entails.pure_right (Or.inr ⟨evs1, evs2, hevs1, hevs2, rfl⟩) (Entails.refl _))
  simp only [sepConj_assoc] at hpack ⊢
  refine Entails.trans hpack ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hpool))) ?_
  apply entails_of_eq; ac_rfl

/-- Relocatable `Ok` branch (`+0x01c..+0x05c`) in block `595`. -/
theorem epilogue_ok_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {evs1 : List AllocEvent}
    {H : LibsignalHooks}
    {x : DecodeGhost} {s0 s : State} {m : SignedPreKeyRecordStructure}
    (hdec : SignedPreKeyRecordStructure.decode x.bytes = some m)
    (hevs1 : SpkDecodeEnv x.bytes.length evs1)
    (hpc : s.pc = (blkPl_595).base + kpkOff_retDec)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 128#64)
    (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hsaved : KpkSavedRegs s0 s) :
    Wire.SepWPp (lsProg_595 H)
      (s0.readReg64 .x30) s
      (signedPreKeyStructAt A.repAlloc (s0.sp - 128#64 + 8#64) m ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 128#64 + 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 128#64 + 104#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 128#64 + 112#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 128#64 + 120#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        stackAt (s0.sp - 128#64) signedDecodeStack ∗
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ∗
        A.pool lim (M.stepEvents evs1 st) s)
      (kpkPostPlaced A lim st x s0)
      (noPanicQp s0) := by
  let _ := hsp
  set sp' := s0.sp - 128#64
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (signedPreKeyStructAt_sp8_unpack A.repAlloc sp' m)
      (sepConj_mono_left (memRegion88_unpack x.ret))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
    Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 =>
    Wire.SepWPp.exists_pre fun r6 => Wire.SepWPp.exists_pre fun r7 =>
    Wire.SepWPp.exists_pre fun r8 => Wire.SepWPp.exists_pre fun r9 =>
    Wire.SepWPp.exists_pre fun r10 =>
    Wire.SepWPp.exists_pre fun pubCap => Wire.SepWPp.exists_pre fun pubPtr =>
    Wire.SepWPp.exists_pre fun privCap => Wire.SepWPp.exists_pre fun privPtr =>
    Wire.SepWPp.exists_pre fun sigCap => Wire.SepWPp.exists_pre fun sigPtr =>
    Wire.SepWPp.exists_pre fun pad32 => ?_
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hpub_lt => ?_
  have hc := cap_add1_eq_of_lt hpub_lt
  unfold words88Sp words88Ret
  simp only [sepConj_assoc]
  have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
  refine sepWPp_end_noPanic_lscro hcrl ?_
  wp_steps_sync_pool (s0.readReg64 .x30)
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _
  have hsp_ret : s0.sp - 128#64 + 128#64 = s0.sp := by bv_omega
  refine ⟨by simp [sp', hsp_ret, arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm],
      by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x21,
      by simpa [arm64_norm] using hsaved.x22,
      by simpa [arm64_norm] using hsaved.x23,
      by simpa [arm64_norm] using hsaved.x24,
      by simpa [arm64_norm] using hsaved.x25,
      by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27,
      by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm],
      hv⟩
  · dsimp only [decodeKyberPreKeyRawSpec]
    rw [kyberDeserialize_of_some hdec, pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    refine Entails.trans ?_
      (okExit_pack_budget A lim st evs1 _ s0.sp x.ret x.bytesA x.bytes hevs1
        pubCap pubPtr privCap privPtr sigCap sigPtr
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19)
        pad32 m)
    unfold words88Sp words88Ret
    simp only [sp', arm64_norm]
    apply entails_of_eq; ac_rfl

/-- Relocatable `Err` branch (`+0x01c..+0x024`, `+0x060..+0x080`) in block `595`. -/
theorem epilogue_err_placed_wp [CryptoVerification.LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {evs1 : List AllocEvent}
    {H : LibsignalHooks}
    (hDrop : subroutine_ok (lsProg_551 H) (blkPl_551).base (dropDecodeErrorBudgetSpec M A lim))
    {x : DecodeGhost} {s0 s : State} {e : BitVec 64}
    (hdec : SignedPreKeyRecordStructure.decode x.bytes = none)
    (hevs1 : SpkDecodeEnv x.bytes.length evs1)
    (hpc : s.pc = (blkPl_595).base + kpkOff_retDec)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 128#64)
    (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hsaved : KpkSavedRegs s0 s) :
    Wire.SepWPp (lsProg_595 H)
      (s0.readReg64 .x30) s
      (((s0.sp - 128#64 + 8#64) ↦₆₄ errTag) ∗
        ((s0.sp - 128#64 + 16#64) ↦₆₄ e) ∗
        decodeErrorAt A.repAlloc e ∗
        memRegion (s0.sp - 128#64 + 24#64) 72 ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 128#64) 8 ∗
        ((s0.sp - 128#64 + 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 128#64 + 104#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 128#64 + 112#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 128#64 + 120#64) ↦₆₄ s0.readReg64 .x19) ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        stackAt (s0.sp - 128#64) signedDecodeStack ∗
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 kpkSubStack) (kpkSubStack - signedDecodeStack) ∗
        A.pool lim (M.stepEvents evs1 st) s)
      (kpkPostPlaced A lim st x s0)
      (noPanicQp s0) := by
  set sp' := s0.sp - 128#64
  have hcall := dropDecodeError3_placed_call_ok hDrop
  clear hDrop
  have hstack := kpkDecodeStack_drop_split sp'
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion88_err_unpack x.ret)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 => ?_
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_551).base) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]; rfl) (by simp [hrun, arm64_norm]) ?_
  intro hcrl1
  refine sepWPp_call_noPanic_lscro (e, M.stepEvents evs1 st) hcall
    (by simp [arm64_norm]; rfl)
    (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_595).base + kpkOff_retDrop) (by simp [arm64_norm])
    (T := decodeErrorAt A.repAlloc e ∗ A.pool lim (M.stepEvents evs1 st) s ∗
      stackAt sp' dropDecodeErrorStack)
    (φ := True)
    (by simp (config := { decide := true }) [dropDecodeErrorBudgetSpec, dropDecodeErrorBudgetSpecGen,
      dropDecodeErrorStack, RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC,
      RustCliAllocBudget.pool_setPState, sp', hsp_eq, arm64_norm, wp_norm])
    trivial
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [dropDecodeErrorBudgetSpec, dropDecodeErrorBudgetSpecGen]
  have hdrop_stk : 0x20 + allocHookStack = dropDecodeErrorStack := rfl
  rw [hdrop_stk]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun evs2 => ?_
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  refine Wire.SepWPp.pure_pre fun hevs2 => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [sp', hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
  have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = errTag := by simpa [arm64_norm] using hcs2.2.1
  have hsaved2 : KpkSavedRegs s0 s2 := KpkSavedRegs.of_calleeSaved
    ⟨by simpa [arm64_norm] using hsaved.x21,
     by simpa [arm64_norm] using hsaved.x22,
     by simpa [arm64_norm] using hsaved.x23,
     by simpa [arm64_norm] using hsaved.x24,
     by simpa [arm64_norm] using hsaved.x25,
     by simpa [arm64_norm] using hsaved.x26,
     by simpa [arm64_norm] using hsaved.x27,
     by simpa [arm64_norm] using hsaved.x28⟩ hcs2
  refine sepWPp_end_noPanic_lscro hcrl2 ?_
  wp_steps_sync_pool (s0.readReg64 .x30)
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro _
  have hsp_ret : s0.sp - 128#64 + 128#64 = s0.sp := by bv_omega
  refine ⟨by simp [sp', hsp_ret, arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm],
      by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved2.x21,
      by simpa [arm64_norm] using hsaved2.x22,
      by simpa [arm64_norm] using hsaved2.x23,
      by simpa [arm64_norm] using hsaved2.x24,
      by simpa [arm64_norm] using hsaved2.x25,
      by simpa [arm64_norm] using hsaved2.x26,
      by simpa [arm64_norm] using hsaved2.x27,
      by simpa [arm64_norm] using hsaved2.x28,
      by simp [arm64_norm],
      hv⟩
  · dsimp only [decodeKyberPreKeyRawSpec]
    rw [kyberDeserialize_of_none hdec, pure_true_emp (by simp [htr2, htr, arm64_norm]), emp_sepConj,
      ← M.stepEvents_append]
    refine Entails.trans ?_
      (errExit_pack_budget A lim st evs1 evs2 _ s0.sp x.ret x.bytesA e
        (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19)
        x.bytes hevs1 hevs2)
    simp only [sp', hstack, hsp_eq, arm64_norm]
    apply entails_of_eq; ac_rfl

end LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.EpilogueBudget
