/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneBase
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `Chain::clone [local#1]` (`0x24848`): Stack Budget, Specifications, and Frame Layout

Defines the stack budget `chainCloneStackX`, specifications (`protoChainCloneSpecX`,
`chainCloneSpecX`, `senderChainCloneSpecX`), and stack-frame decomposition for
`<session_structure::Chain as Clone>::clone [local#1]` (`0x24848`, Block `82`) on `SP2Ext` and
under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open Proofs.libsignal
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_ChainCloneBaseX : True := trivial

/-! ## Stack budget and specifications -/

/-- Stack budget for `Chain::clone`: frame `208` + stub call at `Stage1X.extHookStack`. -/
abbrev chainCloneStackX : Nat := 208 + Stage1X.extHookStack

/-- `protoChainCloneSpec` at `chainCloneStackX`. -/
def protoChainCloneSpecX (A : RustAlloc) : Spec ChainCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s.sp chainCloneStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A (g', x.gc.2) x.dst) ∗
      protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `chainCloneSpec` at `chainCloneStackX`. -/
def chainCloneSpecX (A : RustAlloc) : Spec ChainCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      memRegion x.dst 104 ∗ chainAt A x.gc x.src ∗ A.pool ∗ stackAt s.sp chainCloneStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        chainAt A (g', x.gc.2) x.dst) ∗
      chainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `senderChainCloneSpec` at `chainCloneStackX`. -/
def senderChainCloneSpecX (A : RustAlloc) : Spec SenderChainCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      memRegion x.dst 104 ∗ optSenderChainAt A x.src (some x.g) (some x.sc) ∗
      A.pool ∗ stackAt s.sp chainCloneStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ g' : SenderChainGhost,
        ⌜g'.srk.bytes = x.g.srk.bytes ∧ g'.priv.bytes = x.g.priv.bytes⌝ ∗
        optSenderChainAt A x.dst (some g') (some x.sc)) ∗
      optSenderChainAt A x.src (some x.g) (some x.sc) ∗
      A.pool ∗ stackAt s0.sp chainCloneStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Callee contract abbreviations on `SP2Ext` -/

/-- `Chain::clone [local#1]` at `protoChainCloneSpecX`, in image. -/
def ProtoChainCloneLocal1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainCloneLocal1Name)
    ((protoChainCloneSpecX A).inImage img)

/-- `Chain::clone [local#1]` at `chainCloneSpecX`, in image. -/
def ChainCloneLocal1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainCloneLocal1Name)
    ((chainCloneSpecX A).inImage img)

/-- `Chain::clone [local#1]` at `senderChainCloneSpecX`, in image. -/
def SenderChainCloneLocal1OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr chainCloneLocal1Name)
    ((senderChainCloneSpecX A).inImage img)

/-! ## Stack-frame decomposition -/

theorem stackAt_chainClone_eq_x (sp : BitVec 64) :
    stackAt sp chainCloneStackX =
      stackAt (sp - 208#64) Stage1X.extHookStack ∗
      (∃∗ v0 : BitVec 64, (sp - 208#64) ↦₆₄ v0) ∗
      (∃∗ w1a : BitVec 32, (sp - 200#64) ↦₃₂ w1a) ∗
      (∃∗ w1b : BitVec 32, (sp - 196#64) ↦₃₂ w1b) ∗
      (∃∗ v2 : BitVec 64, (sp - 192#64) ↦₆₄ v2) ∗
      (∃∗ v3 : BitVec 64, (sp - 184#64) ↦₆₄ v3) ∗
      (∃∗ v4 : BitVec 64, (sp - 176#64) ↦₆₄ v4) ∗
      (∃∗ v5 : BitVec 64, (sp - 168#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (sp - 160#64) ↦₆₄ v6) ∗
      (∃∗ v7 : BitVec 64, (sp - 152#64) ↦₆₄ v7) ∗
      (∃∗ v8 : BitVec 64, (sp - 144#64) ↦₆₄ v8) ∗
      (∃∗ v9 : BitVec 64, (sp - 136#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (sp - 128#64) ↦₆₄ v10) ∗
      (∃∗ v11 : BitVec 64, (sp - 120#64) ↦₆₄ v11) ∗
      (∃∗ w12a : BitVec 32, (sp - 112#64) ↦₃₂ w12a) ∗
      (∃∗ w12b : BitVec 32, (sp - 108#64) ↦₃₂ w12b) ∗
      (∃∗ v13 : BitVec 64, (sp - 104#64) ↦₆₄ v13) ∗
      (∃∗ v14 : BitVec 64, (sp - 96#64) ↦₆₄ v14) ∗
      (∃∗ v15 : BitVec 64, (sp - 88#64) ↦₆₄ v15) ∗
      (∃∗ v16 : BitVec 64, (sp - 80#64) ↦₆₄ v16) ∗
      (∃∗ v17 : BitVec 64, (sp - 72#64) ↦₆₄ v17) ∗
      (∃∗ v18 : BitVec 64, (sp - 64#64) ↦₆₄ v18) ∗
      (∃∗ v19 : BitVec 64, (sp - 56#64) ↦₆₄ v19) ∗
      (∃∗ v20 : BitVec 64, (sp - 48#64) ↦₆₄ v20) ∗
      (∃∗ v21 : BitVec 64, (sp - 40#64) ↦₆₄ v21) ∗
      (∃∗ v22 : BitVec 64, (sp - 32#64) ↦₆₄ v22) ∗
      (∃∗ v23 : BitVec 64, (sp - 24#64) ↦₆₄ v23) ∗
      (∃∗ v24 : BitVec 64, (sp - 16#64) ↦₆₄ v24) ∗
      (∃∗ v25 : BitVec 64, (sp - 8#64) ↦₆₄ v25) := by
  have hsplit := stackAt_split_cells sp Stage1X.extHookStack 26 (by decide)
  change stackAt sp chainCloneStackX =
    stackAt (sp - 208#64) Stage1X.extHookStack ∗ cells (sp - BitVec.ofNat 64 208) 26 at hsplit
  rw [hsplit]
  simp (disch := decide) only [cells_sub_succ', Nat.reduceSub, cells_zero, sepConj_emp]
  change stackAt (sp - 208#64) Stage1X.extHookStack ∗
      ((∃∗ v0 : BitVec 64, (sp - 208#64) ↦₆₄ v0) ∗
      ((∃∗ v1 : BitVec 64, (sp - 200#64) ↦₆₄ v1) ∗
      ((∃∗ v2 : BitVec 64, (sp - 192#64) ↦₆₄ v2) ∗
      ((∃∗ v3 : BitVec 64, (sp - 184#64) ↦₆₄ v3) ∗
      ((∃∗ v4 : BitVec 64, (sp - 176#64) ↦₆₄ v4) ∗
      ((∃∗ v5 : BitVec 64, (sp - 168#64) ↦₆₄ v5) ∗
      ((∃∗ v6 : BitVec 64, (sp - 160#64) ↦₆₄ v6) ∗
      ((∃∗ v7 : BitVec 64, (sp - 152#64) ↦₆₄ v7) ∗
      ((∃∗ v8 : BitVec 64, (sp - 144#64) ↦₆₄ v8) ∗
      ((∃∗ v9 : BitVec 64, (sp - 136#64) ↦₆₄ v9) ∗
      ((∃∗ v10 : BitVec 64, (sp - 128#64) ↦₆₄ v10) ∗
      ((∃∗ v11 : BitVec 64, (sp - 120#64) ↦₆₄ v11) ∗
      ((∃∗ v12 : BitVec 64, (sp - 112#64) ↦₆₄ v12) ∗
      ((∃∗ v13 : BitVec 64, (sp - 104#64) ↦₆₄ v13) ∗
      ((∃∗ v14 : BitVec 64, (sp - 96#64) ↦₆₄ v14) ∗
      ((∃∗ v15 : BitVec 64, (sp - 88#64) ↦₆₄ v15) ∗
      ((∃∗ v16 : BitVec 64, (sp - 80#64) ↦₆₄ v16) ∗
      ((∃∗ v17 : BitVec 64, (sp - 72#64) ↦₆₄ v17) ∗
      ((∃∗ v18 : BitVec 64, (sp - 64#64) ↦₆₄ v18) ∗
      ((∃∗ v19 : BitVec 64, (sp - 56#64) ↦₆₄ v19) ∗
      ((∃∗ v20 : BitVec 64, (sp - 48#64) ↦₆₄ v20) ∗
      ((∃∗ v21 : BitVec 64, (sp - 40#64) ↦₆₄ v21) ∗
      ((∃∗ v22 : BitVec 64, (sp - 32#64) ↦₆₄ v22) ∗
      ((∃∗ v23 : BitVec 64, (sp - 24#64) ↦₆₄ v23) ∗
      ((∃∗ v24 : BitVec 64, (sp - 16#64) ↦₆₄ v24) ∗
      (∃∗ v25 : BitVec 64, (sp - 8#64) ↦₆₄ v25)))))))))))))))))))))))))) = _
  rw [memRegion_eight_eq_two_four (sp - 200#64), memRegion_eight_eq_two_four (sp - 112#64)]
  have h196 : sp - 200#64 + 4#64 = sp - 196#64 := by bv_omega
  have h108 : sp - 112#64 + 4#64 = sp - 108#64 := by bv_omega
  rw [h196, h108]
  ac_rfl

theorem fold_stackAt_chainClone_x (s0 : State) (v8 v9 v10 v13 : BitVec 64) :
    (stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ v8) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      stackAt s0.sp chainCloneStackX := by
  rw [stackAt_chainClone_eq_x s0.sp]
  unfold spillSlotsExist savedRegsOnStack
  have h8 : ((s0.sp - 144#64) ↦₆₄ v8) ⊢ ∃∗ x : BitVec 64, (s0.sp - 144#64) ↦₆₄ x :=
    Entails.sepExists_right v8 (Entails.refl _)
  have h9 : ((s0.sp - 136#64) ↦₆₄ v9) ⊢ ∃∗ x : BitVec 64, (s0.sp - 136#64) ↦₆₄ x :=
    Entails.sepExists_right v9 (Entails.refl _)
  have h10 : ((s0.sp - 128#64) ↦₆₄ v10) ⊢ ∃∗ x : BitVec 64, (s0.sp - 128#64) ↦₆₄ x :=
    Entails.sepExists_right v10 (Entails.refl _)
  have h13 : ((s0.sp - 104#64) ↦₆₄ v13) ⊢ ∃∗ x : BitVec 64, (s0.sp - 104#64) ↦₆₄ x :=
    Entails.sepExists_right v13 (Entails.refl _)
  have h14 : ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 96#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 29#5)) (Entails.refl _)
  have h15 : ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 88#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 30#5)) (Entails.refl _)
  have h16 : ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 80#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 28#5)) (Entails.refl _)
  have h17 : ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 72#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 27#5)) (Entails.refl _)
  have h18 : ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 64#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 26#5)) (Entails.refl _)
  have h19 : ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 56#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 25#5)) (Entails.refl _)
  have h20 : ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 48#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 24#5)) (Entails.refl _)
  have h21 : ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 40#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 23#5)) (Entails.refl _)
  have h22 : ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 32#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 22#5)) (Entails.refl _)
  have h23 : ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 24#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 21#5)) (Entails.refl _)
  have h24 : ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 16#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 20#5)) (Entails.refl _)
  have h25 : ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢ ∃∗ x : BitVec 64, (s0.sp - 8#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) (Entails.refl _)
  have hstep :
      (stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        ((∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
         (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
         (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
         (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
         (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
         (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
         (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
         (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
         (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7)) ∗
        ((s0.sp - 144#64) ↦₆₄ v8) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
         ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
         ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
         ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
         ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
         ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
         (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
         (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
         (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) ⊢
      (stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        ((∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
         (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
         (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
         (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
         (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
         (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
         (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
         (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
         (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7)) ∗
        (∃∗ v8 : BitVec 64, (s0.sp - 144#64) ↦₆₄ v8) ∗
        (∃∗ v9 : BitVec 64, (s0.sp - 136#64) ↦₆₄ v9) ∗
        (∃∗ v10 : BitVec 64, (s0.sp - 128#64) ↦₆₄ v10) ∗
        (∃∗ v13 : BitVec 64, (s0.sp - 104#64) ↦₆₄ v13) ∗
        ((∃∗ v14 : BitVec 64, (s0.sp - 96#64) ↦₆₄ v14) ∗
         (∃∗ v15 : BitVec 64, (s0.sp - 88#64) ↦₆₄ v15) ∗
         (∃∗ v16 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v16) ∗
         (∃∗ v17 : BitVec 64, (s0.sp - 72#64) ↦₆₄ v17) ∗
         (∃∗ v18 : BitVec 64, (s0.sp - 64#64) ↦₆₄ v18) ∗
         (∃∗ v19 : BitVec 64, (s0.sp - 56#64) ↦₆₄ v19) ∗
         (∃∗ v20 : BitVec 64, (s0.sp - 48#64) ↦₆₄ v20) ∗
         (∃∗ v21 : BitVec 64, (s0.sp - 40#64) ↦₆₄ v21) ∗
         (∃∗ v22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ v22) ∗
         (∃∗ v23 : BitVec 64, (s0.sp - 24#64) ↦₆₄ v23) ∗
         (∃∗ v24 : BitVec 64, (s0.sp - 16#64) ↦₆₄ v24) ∗
         (∃∗ v25 : BitVec 64, (s0.sp - 8#64) ↦₆₄ v25) ∗
         (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
         (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
         (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) :=
    sepConj_mono_right (sepConj_mono_right
      (sepConj_mono h8 (sepConj_mono h9 (sepConj_mono h10 (sepConj_mono h13
        (sepConj_mono h14 (sepConj_mono h15 (sepConj_mono h16 (sepConj_mono h17
          (sepConj_mono h18 (sepConj_mono h19 (sepConj_mono h20 (sepConj_mono h21
            (sepConj_mono h22 (sepConj_mono h23 (sepConj_mono h24
              (sepConj_mono_left h25)))))))))))))))))
  refine Entails.trans hstep ?_
  have hcomm :
      (stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        ((∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
         (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
         (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
         (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
         (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
         (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
         (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
         (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
         (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7)) ∗
        (∃∗ v8 : BitVec 64, (s0.sp - 144#64) ↦₆₄ v8) ∗
        (∃∗ v9 : BitVec 64, (s0.sp - 136#64) ↦₆₄ v9) ∗
        (∃∗ v10 : BitVec 64, (s0.sp - 128#64) ↦₆₄ v10) ∗
        (∃∗ v13 : BitVec 64, (s0.sp - 104#64) ↦₆₄ v13) ∗
        ((∃∗ v14 : BitVec 64, (s0.sp - 96#64) ↦₆₄ v14) ∗
         (∃∗ v15 : BitVec 64, (s0.sp - 88#64) ↦₆₄ v15) ∗
         (∃∗ v16 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v16) ∗
         (∃∗ v17 : BitVec 64, (s0.sp - 72#64) ↦₆₄ v17) ∗
         (∃∗ v18 : BitVec 64, (s0.sp - 64#64) ↦₆₄ v18) ∗
         (∃∗ v19 : BitVec 64, (s0.sp - 56#64) ↦₆₄ v19) ∗
         (∃∗ v20 : BitVec 64, (s0.sp - 48#64) ↦₆₄ v20) ∗
         (∃∗ v21 : BitVec 64, (s0.sp - 40#64) ↦₆₄ v21) ∗
         (∃∗ v22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ v22) ∗
         (∃∗ v23 : BitVec 64, (s0.sp - 24#64) ↦₆₄ v23) ∗
         (∃∗ v24 : BitVec 64, (s0.sp - 16#64) ↦₆₄ v24) ∗
         (∃∗ v25 : BitVec 64, (s0.sp - 8#64) ↦₆₄ v25) ∗
         (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
         (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
         (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b))) =
      (stackAt (s0.sp - 208#64) Stage1X.extHookStack ∗
        (∃∗ v0 : BitVec 64, (s0.sp - 208#64) ↦₆₄ v0) ∗
        (∃∗ w1a : BitVec 32, (s0.sp - 200#64) ↦₃₂ w1a) ∗
        (∃∗ w1b : BitVec 32, (s0.sp - 196#64) ↦₃₂ w1b) ∗
        (∃∗ v2 : BitVec 64, (s0.sp - 192#64) ↦₆₄ v2) ∗
        (∃∗ v3 : BitVec 64, (s0.sp - 184#64) ↦₆₄ v3) ∗
        (∃∗ v4 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v4) ∗
        (∃∗ v5 : BitVec 64, (s0.sp - 168#64) ↦₆₄ v5) ∗
        (∃∗ v6 : BitVec 64, (s0.sp - 160#64) ↦₆₄ v6) ∗
        (∃∗ v7 : BitVec 64, (s0.sp - 152#64) ↦₆₄ v7) ∗
        (∃∗ v8 : BitVec 64, (s0.sp - 144#64) ↦₆₄ v8) ∗
        (∃∗ v9 : BitVec 64, (s0.sp - 136#64) ↦₆₄ v9) ∗
        (∃∗ v10 : BitVec 64, (s0.sp - 128#64) ↦₆₄ v10) ∗
        (∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b) ∗
        (∃∗ v13 : BitVec 64, (s0.sp - 104#64) ↦₆₄ v13) ∗
        (∃∗ v14 : BitVec 64, (s0.sp - 96#64) ↦₆₄ v14) ∗
        (∃∗ v15 : BitVec 64, (s0.sp - 88#64) ↦₆₄ v15) ∗
        (∃∗ v16 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v16) ∗
        (∃∗ v17 : BitVec 64, (s0.sp - 72#64) ↦₆₄ v17) ∗
        (∃∗ v18 : BitVec 64, (s0.sp - 64#64) ↦₆₄ v18) ∗
        (∃∗ v19 : BitVec 64, (s0.sp - 56#64) ↦₆₄ v19) ∗
        (∃∗ v20 : BitVec 64, (s0.sp - 48#64) ↦₆₄ v20) ∗
        (∃∗ v21 : BitVec 64, (s0.sp - 40#64) ↦₆₄ v21) ∗
        (∃∗ v22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ v22) ∗
        (∃∗ v23 : BitVec 64, (s0.sp - 24#64) ↦₆₄ v23) ∗
        (∃∗ v24 : BitVec 64, (s0.sp - 16#64) ↦₆₄ v24) ∗
        (∃∗ v25 : BitVec 64, (s0.sp - 8#64) ↦₆₄ v25)) := by
    ac_rfl
  rw [hcomm]
  exact Entails.refl _

/-! ## Relocatable `[LibsignalPlacement]` specs and `SepWPpLs` combinators (Block `82`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- `SepWPp` guarded by `LibsignalCodeLoaded lsmpl s.mem`. -/
abbrev SepWPpLs [LibsignalPlacement] (prog : Program) (ret : BitVec 64) (s : State)
    (P : SepProp) (Q Qp : State → SepProp → Prop) : Prop :=
  LibsignalCodeLoaded lsmpl s.mem → SepWPp prog ret s P Q Qp

theorem SepWPpLs.of_sepWP [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpLs prog ret sm Pm Q Qp)) :
    SepWPpLs prog ret s P Q Qp :=
  fun hcl => SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

theorem SepWPpLs.weaken_pre [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPpLs prog ret s P' Q Qp) :
    SepWPpLs prog ret s P Q Qp :=
  fun hcl => SepWPp.weaken_pre hent (h hcl)

theorem SepWPpLs.pure_elim [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpLs prog ret s P Q Qp) :
    SepWPpLs prog ret s (⌜φ⌝ ∗ P) Q Qp :=
  fun hcl => SepWPp.pure_elim fun hφ => h hφ hcl

theorem sepWPp_of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

/-- `Chain::clone [local#1]` (Block `82`) at `protoChainCloneSpecX`, with `LibsignalCodeLoaded`. -/
def ProtoChainCloneLocal1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_82 H) (blkPl_82).base
    (withLsCodeLoaded lsmpl (protoChainCloneSpecX A))

/-- `Chain::clone [local#1]` (Block `82`) at `chainCloneSpecX`, with `LibsignalCodeLoaded`. -/
def ChainCloneLocal1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_82 H) (blkPl_82).base
    (withLsCodeLoaded lsmpl (chainCloneSpecX A))

/-- `Chain::clone [local#1]` (Block `82`) at `senderChainCloneSpecX`, with `LibsignalCodeLoaded`. -/
def SenderChainCloneLocal1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_82 H) (blkPl_82).base
    (withLsCodeLoaded lsmpl (senderChainCloneSpecX A))

end Placed

end CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
