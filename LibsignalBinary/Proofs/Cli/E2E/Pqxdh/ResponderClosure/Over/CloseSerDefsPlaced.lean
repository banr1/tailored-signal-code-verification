/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDropPlaced
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `SessionRecord::serialize` (`Prev1`) Body Specs and Step Statements

Relocatable `[LibsignalPlacement]` body contract, field-2 write step (`+444 .. +692`), lifted
`serializeSubStackX` callee contracts, and tail step (`+692 .. ret`) for `<SessionRecord>::serialize`
(block 52) on `lsProg_52 H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Serialization CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open Proofs.libsignal.Hooks2

/-! ## Body and Bridge Statements -/

def SerializePrev1BodyPlacedOkStmt [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_52 H) (blkPl_52).base
    (withLsCodeLoaded lsmpl (serializePrev1BodySpecX A))

def SerializePrev1PlacedBridgeStmt [LibsignalPlacement] : Prop :=
  ∀ (A : RustAlloc) (H : LibsignalHooks),
    SerializePrev1BodyPlacedOkStmt A H → SerializePrev1PlacedOkStmt (lsProg_52 H) A

/-! ## Field-2 Write Step (`+444 .. +692`) -/

/-- Field-2 write block of `SessionRecord::serialize` (`+444 .. +692`) on `lsProg_52 H`. -/
def SerField2PlacedStepStmt [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  ∀ (sp0 q' cap ptr capE ptrE : BitVec 64) (bs enc : List (BitVec 8))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop},
    (∀ sf P_f,
      CryptoVerification.E2E.Record.Serialization.EncodeRawAux.PanicAllocPost s0 sf P_f →
        Qp sf P_f) →
    bs.length + (CryptoVerification.E2E.Record.lenField 2 enc).length < 2 ^ 32 →
    s.pc = (blkPl_52).base + bv% (444) →
    s.status = .Running →
    s.sp = sp0 - 800#64 →
    sp0 &&& 15#64 = 0#64 →
    s.trace = s0.trace →
    s.readReg64 .x22 = q' →
    s.readReg64 .x25 = 1#64 →
    P = (vecU8At A (sp0 - 432#64) cap ptr bs ∗ vecU8At A q' capE ptrE enc ∗ A.pool ∗
      stackAt (sp0 - 800#64) serializeSubStackX) ∗ F →
    (∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_52).base + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved s sm →
      SepWPpLsCl lsmpl (lsProg_52 H) ret sm
        ((vecU8At A (sp0 - 432#64) cap' ptr'
            (bs ++ CryptoVerification.E2E.Record.lenField 2 enc) ∗
          vecU8At A q' capE ptrE enc ∗ A.pool ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q Qp) →
    SepWPpLsCl lsmpl (lsProg_52 H) ret s P Q Qp

/-! ## Lifted Callee Contracts at `serializeSubStackX` -/

theorem vecVecClone1_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hK1 : VecVecClone1PlacedOkStmt A H) :
    subroutine_ok callerProg (blkPl_117).base
      (withLsCodeLoaded lsmpl (vecVecClone1SubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - vecVecClone1StackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) (j := 117) hK1))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [vecVecClone1SubSpecX, vecVecClone1SpecX,
      stackAt_serializeSub_splitX s0.sp vecVecClone1StackX (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [vecVecClone1SubSpecX, vecVecClone1SpecX,
      stackAt_serializeSub_splitX s0.sp vecVecClone1StackX (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem dealloc_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (deallocSubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Proofs.libsignal.Stage1X.extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.alloc.dealloc (callerProg := callerProg)))
    (fun ⟨p, size, align⟩ s0 => ?_)
    (fun ⟨p, size, align⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [deallocSubSpecX, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [deallocSubSpecX, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

/-! ## Tail Step (`+692 .. ret`) -/

/-- Epilogue of `SessionRecord::serialize` (`+692 .. ret`) on `lsProg_52 H`: writes `Ok(vec)` to
`out`, drops the cloned `SessionStructure` and `Vec<Vec<u8>>`, and returns. -/
def SerPrev1PlacedTailStmt [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  ∀ (out q' capE ptrE cap' ptr' o0 o1 o2 o3 : BitVec 64) (bs enc : List (BitVec 8))
    (w : SessionGhost) (sess' : Session (List (BitVec 8)))
    {ret : BitVec 64} {s0 sm : State} {Fx : SepProp} {Q Qp : State → SepProp → Prop},
    (∀ sf P_f,
      CryptoVerification.E2E.Record.Serialization.EncodeRawAux.PanicAllocPost s0 sf P_f →
        Qp sf P_f) →
    (∀ sf : State, sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      Q sf (((out ↦₆₄ okTagVec) ∗ vecU8 A (out + 8#64) bs ∗ A.pool ∗
        stackAt s0.sp serializeStackX) ∗ Fx)) →
    s0.sp &&& 15#64 = 0#64 →
    sm.pc = (blkPl_52).base + bv% (692) →
    sm.status = .Running →
    sm.sp = s0.sp - 800#64 →
    sm.trace = s0.trace →
    sm.readReg64 .x19 = out →
    (sm.readReg64 .x23 + 1#64 == 0#64) = false →
    sm.readReg64 .x24 = s0.sp - 800#64 →
    calleeSavedVRegs sm = calleeSavedVRegs s0 →
    SepWPpLsCl lsmpl (lsProg_52 H) ret sm
      ((vecU8At A (s0.sp - 432#64) cap' ptr' bs ∗ vecU8At A q' capE ptrE enc ∗ A.pool ∗
          stackAt (s0.sp - 800#64) serializeSubStackX) ∗
        (((s0.sp - 800#64) ↦₆₄ 1#64) ∗ ((s0.sp - 792#64) ↦₆₄ q') ∗
          ((s0.sp - 784#64) ↦₆₄ 1#64) ∗ A.live q' 24 8 ∗
          sessionStateReprAt A (s0.sp - 776#64) w sess' ∗
          memRegion (s0.sp - 408#64) 312 ∗
          (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
          ((out + 24#64) ↦₆₄ o3) ∗
          serSavedCells s0 ret ∗ Fx))
      Q Qp

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
