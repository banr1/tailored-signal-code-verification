/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Frame
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Frame and `InMainPlaced` Helpers for `main`

Re-exports pure stack-frame helpers from `Frame.lean` and provides `[LibsignalPlacement]`
`InMainPlaced` alignment and step-preservation lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-- When `s0.spAligned = true`, every state `s` in `InMainPlaced` has `s.spAligned = true`. -/
theorem InMainPlaced.spAligned_of_s0 [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s : State} {k : Nat}
    (hs : InMainPlaced CodeOk s0 s k) (hsp0 : s0.spAligned = true) :
    s.spAligned = true := by
  simp only [State.spAligned, hs.sp, mainFrameSize]
  exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hsp0

/-- Equivalence: `s.spAligned = true` in `InMainPlaced` iff `s0.spAligned = true`. -/
theorem InMainPlaced.spAligned_iff [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s : State} {k : Nat} (hs : InMainPlaced CodeOk s0 s k) :
    s.spAligned = true ↔ s0.spAligned = true := by
  refine ⟨fun h => ?_, hs.spAligned_of_s0⟩
  have heq : s0.sp = s.sp - (-0x4e0#64) := by
    calc
      s0.sp = s0.sp + (-0x4e0#64 + 0x4e0#64) := (BitVec.add_zero s0.sp).symm
      _ = (s0.sp + -0x4e0#64) + 0x4e0#64 := (BitVec.add_assoc _ _ _).symm
      _ = s.sp - (-0x4e0#64) := by
        rw [hs.sp, mainFrameSize]
        simp only [BitVec.sub_eq_add_neg, BitVec.neg_neg]
  simp only [State.spAligned] at h ⊢
  rw [heq]
  exact ProofLib.spAligned_sub s.sp (-0x4e0#64) h

/-- Every state `s` in `InMainPlaced` has `s.spAligned = true`. -/
theorem InMainPlaced.spAligned_state [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s : State} {k : Nat} (hs : InMainPlaced CodeOk s0 s k) :
    s.spAligned = true :=
  hs.spAligned_of_s0 hs.spAligned

/-- Assemble `InMainPlaced` after a straight-line step sequence or call returning with `CodeOk`. -/
theorem InMainPlaced.mk_step [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s s' : State} {k k' : Nat}
    (hs : InMainPlaced CodeOk s0 s k)
    (hpc : s'.pc = mPcPlaced k')
    (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp)
    (hfp : s'.readReg64 .fp = s.readReg64 .fp)
    (hinv : CodeOk s'.mem)
    (hvregs : calleeSavedVRegs s' = calleeSavedVRegs s) :
    InMainPlaced CodeOk s0 s' k' where
  pc := hpc
  run := hrun
  sp := hsp.trans hs.sp
  fp := hfp.trans hs.fp
  inv := hinv
  vregs := hvregs.trans hs.vregs
  spAligned := hs.spAligned

/-- Assemble `InMainPlaced` across a `subroutine_ok` callee return (`CalleeSavedPreserved s s'`). -/
theorem InMainPlaced.of_call [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {s0 s s' : State} {k k' : Nat}
    (hs : InMainPlaced CodeOk s0 s k)
    (hpc : s'.pc = mPcPlaced k')
    (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp)
    (hcs : CalleeSavedPreserved s s')
    (hkf : s.mem.KeepsFrozen s'.mem) :
    InMainPlaced CodeOk s0 s' k' where
  pc := hpc
  run := hrun
  sp := hsp.trans hs.sp
  fp := hcs.2.2.2.2.2.2.2.2.2.2.1.trans hs.fp
  inv := hCI.of_keepsFrozen hs.inv hkf
  vregs := hcs.2.2.2.2.2.2.2.2.2.2.2.trans hs.vregs
  spAligned := hs.spAligned

/-- Assemble `InMainPlaced` across a call that directly hands back `CodeOk s'.mem`. -/
theorem InMainPlaced.of_call_inv [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s s' : State} {k k' : Nat}
    (hs : InMainPlaced CodeOk s0 s k)
    (hpc : s'.pc = mPcPlaced k')
    (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp)
    (hcs : CalleeSavedPreserved s s')
    (hinv : CodeOk s'.mem) :
    InMainPlaced CodeOk s0 s' k' where
  pc := hpc
  run := hrun
  sp := hsp.trans hs.sp
  fp := hcs.2.2.2.2.2.2.2.2.2.2.1.trans hs.fp
  inv := hinv
  vregs := hcs.2.2.2.2.2.2.2.2.2.2.2.trans hs.vregs
  spAligned := hs.spAligned

end CryptoVerification.SignalSession.Cli.MainHops
