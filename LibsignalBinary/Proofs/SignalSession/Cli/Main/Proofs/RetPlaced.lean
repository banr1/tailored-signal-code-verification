/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.FramePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `main_ret` Epilogue (`M+0xb80 .. M+0xba0`, Block `617`)

Verifies `main`'s shared return epilogue (`M+0xb80 .. M+0xba0`) on Block `617` under
`[LibsignalPlacement]`, restoring `sp`, `x19..x29`, and `d8..d15` and returning `w0 = w26` with
unchanged files and trace.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

@[local simp, local arm64_norm]
private theorem sp_sub_96_add_96_p (sp0 : BitVec 64) : (sp0 - 96#64) + 96#64 = sp0 := by
  calc
    (sp0 - 96#64) + 96#64 = sp0 + (-96#64 + 96#64) := by
      rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    _ = sp0 := BitVec.add_zero sp0

private theorem sepWPp_of_sepWP_ret_any_p {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog ret s P Q) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, hout | ⟨_, hmo⟩⟩
  · exact ⟨sf, hsteps, Or.inl hout⟩
  · exact (not_satisfies_false_sepConj hmo).elim

/-- Shared return epilogue (`M+0xb80 → lr` on Block `617`): returns `code` with `sp`, `x19..x29`
(from `mainSaved`), and `d8..d15` restored, and trace and files unchanged. -/
theorem main_ret_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {A : RustAlloc}
    {s0 s : State} {stk code : Nat} {Qp : State → SepProp → Prop}
    (hstk : mainFrameSize ≤ stk) (hs : AtRetPlaced CodeOk s0 s code) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s (retMem A s0 stk)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧ sf.trace = s.trace ∧
        sf.fs = s.fs ∧ (Pf ⊢ stackAt s0.sp stk ∗ A.pool ∗ anyHeap))
      Qp (mainOom s0) := by
  refine sepWPp_with_stk_le_two_pow_64 hstk
    (F := memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗ A.pool ∗ anyHeap)
    (Entails.of_eq (by
      unfold retMem
      dsimp only [mainFrameSize]
      ac_rfl))
    fun hstk64 => ?_
  have hpc : s.pc = (blkPl_617).base + 2944#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp : s.sp = s0.sp - 0x4e0#64 := hs.base.sp
  have hsp0 : s0.spAligned = true := hs.base.spAligned
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hsp60_al : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0
  have hw26 : (s.readReg64 (.gpr 26#5)).setWidth 32 = BitVec.ofNat 32 code := hs.w26
  have hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := hs.base.vregs
  apply sepWPp_of_sepWP_ret_any_p
  unfold retMem
  rw [mainSaved_eq_sub s0]
  simp only [sepConj_assoc]
  rw [mProgPlaced_eq]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  refine ⟨by simp only [arm64_norm, *], ?_, by simp only [arm64_norm, *],
    by simp only [arm64_norm, *], by simp only [arm64_norm, *], ?_⟩
  · refine calleeSavedPreserved_of_regs
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (Eq.trans (by simp only [calleeSavedVRegs, arm64_norm]) hvregs)
  · refine Entails.trans ?_ (retMem_entails_post A s0 hstk hstk64)
    unfold retMem
    rw [mainSaved_eq_sub s0]
    simp only [sepConj_assoc]
    exact Entails.refl _

end CryptoVerification.SignalSession.Cli.MainHops
