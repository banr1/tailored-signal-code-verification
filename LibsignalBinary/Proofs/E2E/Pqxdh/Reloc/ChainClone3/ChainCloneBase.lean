/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.ChainClone3.ChainCloneFetch
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.SepLogic.WPp

/-!
# Base Layout and Stack Helpers for `Chain::clone [local#3]` (`0x766c8`)

Stack-frame decomposition, address normalization, and separation-logic invariants for
`<session_structure::Chain as Clone>::clone [local#3]` (`0x766c8`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.ChainClone3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

def protoChainAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧
    gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

def protoChainCloneSpec (A : RustAlloc) : Spec ChainCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      memRegion x.dst 104 ∗ protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s.sp chainCloneStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A (g', x.gc.2) x.dst) ∗
      protoChainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def ProtoChainClone3Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainClone3Name)
    (protoChainCloneSpec A)

def ChainClone3Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainClone3Name)
    (chainCloneSpec A)

def SenderChainClone3Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs)
    ((tripleRatchetProgAt b C ctl abs).fnAddr chainClone3Name)
    (senderChainCloneSpec A)

/-! ## 2. Stack Frame Decomposition and Address Normalization for `Chain::clone [local#2]` -/

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm, local wp_norm]
theorem fp_neg_48 (sp : BitVec 64) :
    sp - 96#64 + 18446744073709551568#64 = sp - 144#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fp_neg_40 (sp : BitVec 64) :
    sp - 96#64 + 18446744073709551576#64 = sp - 136#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fp_neg_32 (sp : BitVec 64) :
    sp - 96#64 + 18446744073709551584#64 = sp - 128#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fp_neg_24 (sp : BitVec 64) :
    sp - 96#64 + 18446744073709551592#64 = sp - 120#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fp_neg_12 (sp : BitVec 64) :
    sp - 96#64 + 18446744073709551604#64 = sp - 108#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fp_neg_8 (sp : BitVec 64) :
    sp - 96#64 + 18446744073709551608#64 = sp - 104#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fp_neg_48_int (sp : BitVec 64) :
    sp - 96#64 + (-48 : Int64).toBitVec = sp - 144#64 := fp_neg_48 sp

@[local arm64_norm, local wp_norm]
theorem fp_neg_40_int (sp : BitVec 64) :
    sp - 96#64 + (-40 : Int64).toBitVec = sp - 136#64 := fp_neg_40 sp

@[local arm64_norm, local wp_norm]
theorem fp_neg_32_int (sp : BitVec 64) :
    sp - 96#64 + (-32 : Int64).toBitVec = sp - 128#64 := fp_neg_32 sp

@[local arm64_norm, local wp_norm]
theorem fp_neg_24_int (sp : BitVec 64) :
    sp - 96#64 + (-24 : Int64).toBitVec = sp - 120#64 := fp_neg_24 sp

@[local arm64_norm, local wp_norm]
theorem fp_neg_12_int (sp : BitVec 64) :
    sp - 96#64 + (-12 : Int64).toBitVec = sp - 108#64 := fp_neg_12 sp

@[local arm64_norm, local wp_norm]
theorem fp_neg_8_int (sp : BitVec 64) :
    sp - 96#64 + (-8 : Int64).toBitVec = sp - 104#64 := fp_neg_8 sp

namespace BS5

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
theorem readReg_setMem_setPC_pre
    (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end BS5

theorem memRegion_eight_eq_two_four (a : BitVec 64) :
    (∃∗ v : BitVec 64, a ↦₆₄ v) =
      (∃∗ w0 : BitVec 32, a ↦₃₂ w0) ∗ (∃∗ w1 : BitVec 32, (a + 4#64) ↦₃₂ w1) := by
  rw [← memRegion_eight, ProofLib.memRegion_split a 4 4 (by decide),
    memRegion_four a, memRegion_four (a + 4#64)]

theorem cells_sub_succ' (sp : BitVec 64) (a k : Nat) (hk : k ≠ 0) (h : 8 ≤ a) :
    cells (sp - BitVec.ofNat 64 a) k =
      (∃∗ v : BitVec 64, (sp - BitVec.ofNat 64 a) ↦₆₄ v) ∗
        cells (sp - BitVec.ofNat 64 (a - 8)) (k - 1) := by
  rw [cells_sub_succ sp a k hk h, sepExists_sepConj_left]

theorem cells_add_succ' (ptr : BitVec 64) (a k : Nat) (hk : k ≠ 0) :
    cells (ptr + BitVec.ofNat 64 a) k =
      (∃∗ v : BitVec 64, (ptr + BitVec.ofNat 64 a) ↦₆₄ v) ∗
        cells (ptr + BitVec.ofNat 64 (a + 8)) (k - 1) := by
  have heq :
      cells (ptr + BitVec.ofNat 64 a) k =
        ∃∗ v : BitVec 64, ((ptr + BitVec.ofNat 64 a) ↦₆₄ v) ∗
          cells (ptr + BitVec.ofNat 64 (a + 8)) (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [cells_succ, Nat.add_sub_cancel]
    congr 1; funext v; congr 2
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [heq, sepExists_sepConj_left]

theorem stackAt_chainClone_eq (sp : BitVec 64) :
    stackAt sp chainCloneStack =
      stackAt (sp - 208#64) allocHookStack ∗
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
  have hsplit := stackAt_split_cells sp allocHookStack 26 (by decide)
  change stackAt sp chainCloneStack =
    stackAt (sp - 208#64) allocHookStack ∗ cells (sp - BitVec.ofNat 64 208) 26 at hsplit
  rw [hsplit]
  simp (disch := decide) only [cells_sub_succ', Nat.reduceSub, cells_zero, sepConj_emp]
  change stackAt (sp - 208#64) allocHookStack ∗
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

theorem memRegion_104_eq_slots (ptr : BitVec 64) :
    memRegion ptr 104 =
      (∃∗ v0 : BitVec 64, ptr ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (ptr + 8#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (ptr + 16#64) ↦₆₄ v2) ∗
      (∃∗ v3 : BitVec 64, (ptr + 24#64) ↦₆₄ v3) ∗
      (∃∗ v4 : BitVec 64, (ptr + 32#64) ↦₆₄ v4) ∗
      (∃∗ v5 : BitVec 64, (ptr + 40#64) ↦₆₄ v5) ∗
      (∃∗ v6 : BitVec 64, (ptr + 48#64) ↦₆₄ v6) ∗
      (∃∗ v7 : BitVec 64, (ptr + 56#64) ↦₆₄ v7) ∗
      (∃∗ v8 : BitVec 64, (ptr + 64#64) ↦₆₄ v8) ∗
      (∃∗ v9 : BitVec 64, (ptr + 72#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (ptr + 80#64) ↦₆₄ v10) ∗
      (∃∗ v11 : BitVec 64, (ptr + 88#64) ↦₆₄ v11) ∗
      (∃∗ w12 : BitVec 32, (ptr + 96#64) ↦₃₂ w12) ∗
      memRegion (ptr + 100#64) 4 := by
  rw [show (104 : Nat) = 96 + 8 from rfl, ProofLib.memRegion_split ptr 96 8 (by decide),
      show (8 : Nat) = 4 + 4 from rfl, ProofLib.memRegion_split (ptr + 96#64) 4 4 (by decide),
      (memRegion_cells ptr 12 (by decide) : memRegion ptr 96 = cells ptr 12),
      memRegion_four (ptr + 96#64),
      show cells ptr 12 = cells (ptr + BitVec.ofNat 64 0) 12 by rw [BitVec.add_zero]]
  simp (disch := decide) only [
    cells_add_succ', Nat.reduceAdd, Nat.reduceSub, cells_zero, sepConj_emp]
  have h0 : ptr + BitVec.ofNat 64 0 = ptr := BitVec.add_zero ptr
  have h100 : ptr + 96#64 + 4#64 = ptr + 100#64 := by bv_omega
  rw [h0, h100]
  change ((∃∗ v0 : BitVec 64, ptr ↦₆₄ v0) ∗
      ((∃∗ v1 : BitVec 64, (ptr + 8#64) ↦₆₄ v1) ∗
      ((∃∗ v2 : BitVec 64, (ptr + 16#64) ↦₆₄ v2) ∗
      ((∃∗ v3 : BitVec 64, (ptr + 24#64) ↦₆₄ v3) ∗
      ((∃∗ v4 : BitVec 64, (ptr + 32#64) ↦₆₄ v4) ∗
      ((∃∗ v5 : BitVec 64, (ptr + 40#64) ↦₆₄ v5) ∗
      ((∃∗ v6 : BitVec 64, (ptr + 48#64) ↦₆₄ v6) ∗
      ((∃∗ v7 : BitVec 64, (ptr + 56#64) ↦₆₄ v7) ∗
      ((∃∗ v8 : BitVec 64, (ptr + 64#64) ↦₆₄ v8) ∗
      ((∃∗ v9 : BitVec 64, (ptr + 72#64) ↦₆₄ v9) ∗
      ((∃∗ v10 : BitVec 64, (ptr + 80#64) ↦₆₄ v10) ∗
      (∃∗ v11 : BitVec 64, (ptr + 88#64) ↦₆₄ v11)))))))))))) ∗
      ((∃∗ w12 : BitVec 32, (ptr + 96#64) ↦₃₂ w12) ∗ memRegion (ptr + 100#64) 4) = _
  ac_rfl

/-! ## 3. Separation-Logic and Arithmetic Helpers for Cloning `Vec<u8>` & Keys -/

theorem sepProp_eq_of_entails {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  ProofLib.sepProp_eq_of_entails h1 h2

theorem srk_length_pos {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) : 0 < bs.length := by
  cases bs with
  | nil => nomatch h
  | cons _ _ => exact Nat.succ_pos _

theorem vecU8At_eq_of_nil (A : RustAlloc) (a cap ptr : BitVec 64) :
    vecU8At A a cap ptr [] =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A cap ptr [] := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]

theorem vecGhostAt_eq_of_nil (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hnil : g.bytes = []) :
    vecGhostAt A g a =
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A g.cap g.ptr [] := by
  unfold vecGhostAt
  rw [hnil, vecU8At_eq_of_nil]

theorem vecU8At_eq_of_pos (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8At A a cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
  unfold vecU8At vecHeader
  apply sepProp_eq_of_entails
  · rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
    have hne : cap ≠ 0 := by
      intro h0; rw [h0] at hlen; change bs.length ≤ 0 at hlen; omega
    simp only [hne, ↓reduceIte]
    apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
    have hcomm :
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) =
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
    have hne : cap ≠ 0 := by
      intro h0; rw [h0] at hlen; change bs.length ≤ 0 at hlen; omega
    rw [sepConj_pure_left_comm]
    apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
    simp only [hne, ↓reduceIte]
    have hcomm :
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _

theorem vecGhostAt_eq_of_pos (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hpos : 0 < g.bytes.length) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      (g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
      memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) :=
  vecU8At_eq_of_pos A a g.cap g.ptr g.bytes hpos

theorem vecU8Buf_nil_eq (A : RustAlloc) :
    vecU8Buf A 0#64 1#64 [] = emp := by
  unfold vecU8Buf
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by decide, by decide, by decide⟩
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _

theorem vecU8Buf_pos_eq (A : RustAlloc) (ptr' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hptr' : ptr' ≠ 0#64) :
    vecU8Buf A (BitVec.ofNat 64 bs.length) ptr' bs =
      A.live ptr' bs.length 1 ∗ (ptr' ↦ₛ bs) := by
  unfold vecU8Buf
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have ht := congrArg BitVec.toNat h0
    rw [htoNat] at ht; change bs.length = 0 at ht; omega
  have hptr_ne : ptr' ≠ 0 := hptr'
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by rw [htoNat], by rw [htoNat]; exact hlt, hptr_ne⟩
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
    exact Entails.refl _

/-- Invariant for the cloned `Option<chain::ChainKey>` buffer in registers `(x25, x28, w27)`
before it is written to the destination `Chain` at offset `+72`. -/
def clonedOptChainKeyBuf (A : RustAlloc) (ckPin' : VecPin)
    (x25 x28 : BitVec 64) (w27 : BitVec 32) : Option ChainKey → SepProp
  | none => ⌜x25 = optChainKeyNone⌝
  | some ck =>
      ⌜ckPin' = ⟨32#64, x28⟩ ∧ x25 = 32#64 ∧ w27 = ck.index⌝ ∗
        vecU8Buf A 32#64 x28 (keyToBytes32 ck.key)

theorem fold_optChainKeyAt (A : RustAlloc) (ckPin' : VecPin)
    (x25 x28 : BitVec 64) (w27 : BitVec 32) (optCk : Option ChainKey) (a : BitVec 64) :
    (((a ↦₆₄ x25) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ x25) ∗
      ((a + 24#64) ↦₃₂ w27) ∗ memRegion (a + 28#64) 4) ∗
     clonedOptChainKeyBuf A ckPin' x25 x28 w27 optCk) ⊢
      optChainKeyAt A ckPin' optCk a := by
  cases optCk with
  | none =>
    unfold clonedOptChainKeyBuf optChainKeyAt
    rw [sepConj_comm ((a ↦₆₄ x25) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ x25) ∗
      ((a + 24#64) ↦₃₂ w27) ∗ memRegion (a + 28#64) 4)]
    apply Entails.pure_left; rintro rfl
    have h8_1 : ((a + 8#64) ↦₆₄ x28) ⊢ memRegion (a + 8#64) 8 :=
      pointsTo64_entails_memRegion (a + 8#64) x28
    have h8_2 : ((a + 16#64) ↦₆₄ optChainKeyNone) ⊢ memRegion (a + 16#64) 8 :=
      pointsTo64_entails_memRegion (a + 16#64) optChainKeyNone
    have h4_1 : ((a + 24#64) ↦₃₂ w27) ⊢ memRegion (a + 24#64) 4 :=
      pointsTo32_entails_memRegion (a + 24#64) w27
    have hstep :
        ((a ↦₆₄ optChainKeyNone) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ optChainKeyNone) ∗
          ((a + 24#64) ↦₃₂ w27) ∗ memRegion (a + 28#64) 4) ⊢
        ((a ↦₆₄ optChainKeyNone) ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 ∗
          memRegion (a + 24#64) 4 ∗ memRegion (a + 28#64) 4) :=
      sepConj_mono_right (sepConj_mono h8_1 (sepConj_mono h8_2 (sepConj_mono_left h4_1)))
    refine Entails.trans hstep ?_
    have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
    have ha24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
    have ha28 : a + 24#64 + 4#64 = a + 28#64 := by bv_omega
    rw [show (24 : Nat) = 16 + 8 from rfl,
        ProofLib.memRegion_split (a + 8#64) 16 8 (by decide),
        show (16 : Nat) = 8 + 8 from rfl,
        ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
        ha16, ha24,
        show (8 : Nat) = 4 + 4 from rfl,
        ProofLib.memRegion_split (a + 24#64) 4 4 (by decide),
        ha28]
    have hcomm :
        ((a ↦₆₄ optChainKeyNone) ∗ memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8 ∗
          memRegion (a + 24#64) 4 ∗ memRegion (a + 28#64) 4) =
        ((a ↦₆₄ optChainKeyNone) ∗
          ((memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 8) ∗
           (memRegion (a + 24#64) 4 ∗ memRegion (a + 28#64) 4))) := by
      ac_rfl
    rw [hcomm]
    exact Entails.refl _
  | some ck =>
    unfold clonedOptChainKeyBuf optChainKeyAt
    dsimp only
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨rfl, rfl, rfl⟩
    dsimp only
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have hlen : BitVec.ofNat 64 (keyToBytes32 ck.key).length = 32#64 := by
      simp [keyToBytes32]
    rw [hlen]
    have hcomm :
        (((a ↦₆₄ 32#64) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
          ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4) ∗
         vecU8Buf A 32#64 x28 (keyToBytes32 ck.key)) =
        ((((a ↦₆₄ 32#64) ∗ ((a + 8#64) ↦₆₄ x28) ∗ ((a + 16#64) ↦₆₄ 32#64)) ∗
          vecU8Buf A 32#64 x28 (keyToBytes32 ck.key)) ∗
         ((a + 24#64) ↦₃₂ ck.index) ∗ memRegion (a + 28#64) 4) := by
      ac_rfl
    rw [hcomm]
    exact Entails.refl _

/-- Untouched parts of a source `chain::MessageKey` at `a` during the `MessageKey` clone loop. -/
def messageKeySourceFrame (A : RustAlloc) (gk : MessageKeyGhost)
    (mkg : MessageKeyGenerator) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗
    vecU8Buf A gk.cipher.cap gk.cipher.ptr [] ∗
  ((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗
    vecU8Buf A gk.mac.cap gk.mac.ptr [] ∗
  ((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗ vecU8Buf A gk.iv.cap gk.iv.ptr [] ∗
  ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
  memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length) (gk.seed.cap.toNat - mkg.seed.length) ∗
  memRegion (a + 100#64) 4

theorem messageKeyAt_eq_source (A : RustAlloc) (gk : MessageKeyGhost)
    (mkg : MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A (gk, mkg) a =
      ⌜0 < mkg.seed.length ∧ mkg.seed.length ≤ gk.seed.cap.toNat ∧
        gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
      ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      (gk.seed.ptr ↦ₛ mkg.seed) ∗
      ((a + 96#64) ↦₃₂ mkg.counter) ∗
      messageKeySourceFrame A gk mkg a := by
  unfold messageKeyAt messageKeySourceFrame
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro hseed_ne
    have hpos : 0 < mkg.seed.length := List.length_pos_of_ne_nil hseed_ne
    rw [vecU8At_eq_of_nil A a, vecU8At_eq_of_nil A (a + 24#64),
        vecU8At_eq_of_nil A (a + 48#64),
        vecU8At_eq_of_pos A (a + 72#64) gk.seed.cap gk.seed.ptr mkg.seed hpos]
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
    have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
    have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
    have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
    rw [ha32, ha40, ha56, ha64, ha80, ha88]
    have hpure_comm :
        (((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.cipher.cap gk.cipher.ptr []) ∗
         (((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.mac.cap gk.mac.ptr []) ∗
         (((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.iv.cap gk.iv.ptr []) ∗
         (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
          memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
            (gk.seed.cap.toNat - mkg.seed.length)) ∗
         ((a + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (a + 100#64) 4) =
        (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 16#64) ↦₆₄ 0#64) ∗
          ((a + 40#64) ↦₆₄ 0#64) ∗
          ((a + 64#64) ↦₆₄ 0#64) ∗
          ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((a + 96#64) ↦₃₂ mkg.counter) ∗
          ((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗
           vecU8Buf A gk.cipher.cap gk.cipher.ptr [] ∗
           ((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗
           vecU8Buf A gk.mac.cap gk.mac.ptr [] ∗
           ((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗
           vecU8Buf A gk.iv.cap gk.iv.ptr [] ∗
           ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
           memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
             (gk.seed.cap.toNat - mkg.seed.length) ∗
           memRegion (a + 100#64) 4)) := by
      ac_rfl
    rw [hpure_comm]
    apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
    exact Entails.pure_right ⟨hpos, hlen, hlt, hptr⟩ (Entails.refl _)
  · apply Entails.pure_left; rintro ⟨hpos, hlen, hlt, hptr⟩
    have hseed_ne : mkg.seed ≠ [] := List.ne_nil_of_length_pos hpos
    apply Entails.pure_right hseed_ne
    rw [vecU8At_eq_of_nil A a, vecU8At_eq_of_nil A (a + 24#64),
        vecU8At_eq_of_nil A (a + 48#64),
        vecU8At_eq_of_pos A (a + 72#64) gk.seed.cap gk.seed.ptr mkg.seed hpos]
    have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
    have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
    have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
    have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
    have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
    have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
    rw [ha32, ha40, ha56, ha64, ha80, ha88]
    have hpure_comm :
        (((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.cipher.cap gk.cipher.ptr []) ∗
         (((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.mac.cap gk.mac.ptr []) ∗
         (((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
          vecU8Buf A gk.iv.cap gk.iv.ptr []) ∗
         (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
          memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
            (gk.seed.cap.toNat - mkg.seed.length)) ∗
         ((a + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (a + 100#64) 4) =
        (⌜mkg.seed.length ≤ gk.seed.cap.toNat ∧ gk.seed.cap.toNat < 2 ^ 63 ∧ gk.seed.ptr ≠ 0⌝ ∗
          ((a + 16#64) ↦₆₄ 0#64) ∗
          ((a + 40#64) ↦₆₄ 0#64) ∗
          ((a + 64#64) ↦₆₄ 0#64) ∗
          ((a + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((a + 96#64) ↦₃₂ mkg.counter) ∗
          ((a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗
           vecU8Buf A gk.cipher.cap gk.cipher.ptr [] ∗
           ((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗
           vecU8Buf A gk.mac.cap gk.mac.ptr [] ∗
           ((a + 48#64) ↦₆₄ gk.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.iv.ptr) ∗
           vecU8Buf A gk.iv.cap gk.iv.ptr [] ∗
           ((a + 72#64) ↦₆₄ gk.seed.cap) ∗ A.live gk.seed.ptr gk.seed.cap.toNat 1 ∗
           memRegion (gk.seed.ptr + BitVec.ofNat 64 mkg.seed.length)
             (gk.seed.cap.toNat - mkg.seed.length) ∗
           memRegion (a + 100#64) 4)) := by
      ac_rfl
    rw [hpure_comm]
    exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

def clonedMessageKeyGhost (seedLen seedPtr' : BitVec 64) : MessageKeyGhost :=
  { cipher := ⟨0#64, 1#64⟩
    mac    := ⟨0#64, 1#64⟩
    iv     := ⟨0#64, 1#64⟩
    seed   := ⟨seedLen, seedPtr'⟩ }

theorem fold_cloned_messageKeyAt (A : RustAlloc) (mkg : MessageKeyGenerator)
    (seedPtr' dst : BitVec 64)
    (hpos : 0 < mkg.seed.length) (hlt : mkg.seed.length < 2 ^ 63) (hptr' : seedPtr' ≠ 0#64) :
    ((dst ↦₆₄ 0#64) ∗
      ((dst + 8#64) ↦₆₄ 1#64) ∗
      ((dst + 16#64) ↦₆₄ 0#64) ∗
      ((dst + 24#64) ↦₆₄ 0#64) ∗
      ((dst + 32#64) ↦₆₄ 1#64) ∗
      ((dst + 40#64) ↦₆₄ 0#64) ∗
      ((dst + 48#64) ↦₆₄ 0#64) ∗
      ((dst + 56#64) ↦₆₄ 1#64) ∗
      ((dst + 64#64) ↦₆₄ 0#64) ∗
      ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dst + 80#64) ↦₆₄ seedPtr') ∗
      ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dst + 96#64) ↦₃₂ mkg.counter) ∗
      memRegion (dst + 100#64) 4 ∗
      A.live seedPtr' mkg.seed.length 1 ∗
      (seedPtr' ↦ₛ mkg.seed)) =
      messageKeyAt A
        (clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length) seedPtr', mkg) dst := by
  unfold messageKeyAt clonedMessageKeyGhost
  have hseed_ne : mkg.seed ≠ [] := List.ne_nil_of_length_pos hpos
  rw [vecU8At_eq_of_nil A dst, vecU8At_eq_of_nil A (dst + 24#64),
      vecU8At_eq_of_nil A (dst + 48#64),
      vecU8At_eq_header_sep_buf A (dst + 72#64),
      vecU8Buf_nil_eq A,
      vecU8Buf_pos_eq A seedPtr' mkg.seed hpos hlt hptr']
  unfold vecHeader
  have hd32 : dst + 24#64 + 8#64 = dst + 32#64 := by bv_omega
  have hd40 : dst + 24#64 + 16#64 = dst + 40#64 := by bv_omega
  have hd56 : dst + 48#64 + 8#64 = dst + 56#64 := by bv_omega
  have hd64 : dst + 48#64 + 16#64 = dst + 64#64 := by bv_omega
  have hd80 : dst + 72#64 + 8#64 = dst + 80#64 := by bv_omega
  have hd88 : dst + 72#64 + 16#64 = dst + 88#64 := by bv_omega
  rw [hd32, hd40, hd56, hd64, hd80, hd88]
  simp only [sepConj_emp]
  apply sepProp_eq_of_entails
  · apply Entails.pure_right hseed_ne
    have hcomm :
        ((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64) ∗
          ((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64) ∗
          ((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64) ∗
          ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
          ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) =
        (((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64)) ∗
         (((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64)) ∗
         (((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64)) ∗
         ((((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
           ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length)) ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) ∗
         ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _
  · apply Entails.pure_left; intro _
    have hcomm :
        (((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64)) ∗
         (((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64)) ∗
         (((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64)) ∗
         ((((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
           ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length)) ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) ∗
         ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4) =
        ((dst ↦₆₄ 0#64) ∗ ((dst + 8#64) ↦₆₄ 1#64) ∗ ((dst + 16#64) ↦₆₄ 0#64) ∗
          ((dst + 24#64) ↦₆₄ 0#64) ∗ ((dst + 32#64) ↦₆₄ 1#64) ∗ ((dst + 40#64) ↦₆₄ 0#64) ∗
          ((dst + 48#64) ↦₆₄ 0#64) ∗ ((dst + 56#64) ↦₆₄ 1#64) ∗ ((dst + 64#64) ↦₆₄ 0#64) ∗
          ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗ ((dst + 80#64) ↦₆₄ seedPtr') ∗
          ((dst + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dst + 96#64) ↦₃₂ mkg.counter) ∗ memRegion (dst + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗ (seedPtr' ↦ₛ mkg.seed)) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _

def clonedChainGhost (gc : ChainGhost × ReceiverChain)
    (srkPtr' privPtr' mkCap' mkPtr' : BitVec 64)
    (keys' : List MessageKeyGhost) (ckPin' : VecPin) : ChainGhost :=
  { srk   := ⟨BitVec.ofNat 64 gc.1.srk.bytes.length, srkPtr', gc.1.srk.bytes⟩
    priv  := ⟨BitVec.ofNat 64 gc.1.priv.bytes.length, privPtr', gc.1.priv.bytes⟩
    mkCap := mkCap'
    mkPtr := mkPtr'
    keys  := keys'
    ck    := ckPin' }

theorem fold_chainAt_dst (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (dst srkPtr' privPtr' mkPtr' x25 x28 : BitVec 64) (w27 : BitVec 32)
    (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = gc.2.messageKeys.length) :
    ((dst ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      ((dst + 8#64) ↦₆₄ srkPtr') ∗
      ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      ((dst + 32#64) ↦₆₄ privPtr') ∗
      ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((dst + 56#64) ↦₆₄ mkPtr') ∗
      ((dst + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((dst + 72#64) ↦₆₄ x25) ∗
      ((dst + 80#64) ↦₆₄ x28) ∗
      ((dst + 88#64) ↦₆₄ x25) ∗
      ((dst + 96#64) ↦₃₂ w27) ∗
      memRegion (dst + 100#64) 4 ∗
      vecU8Buf A (BitVec.ofNat 64 gc.1.srk.bytes.length) srkPtr' gc.1.srk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 gc.1.priv.bytes.length) privPtr' gc.1.priv.bytes ∗
      vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 gc.2.messageKeys.length) mkPtr'
        (keys'.zip gc.2.messageKeys) ∗
      clonedOptChainKeyBuf A ckPin' x25 x28 w27 gc.2.chainKey) ⊢
      protoChainAt A
        (clonedChainGhost gc srkPtr' privPtr' (BitVec.ofNat 64 gc.2.messageKeys.length)
          mkPtr' keys' ckPin', gc.2) dst := by
  unfold protoChainAt clonedChainGhost vecGhostAt vecAt
  apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
  rw [vecU8At_eq_header_sep_buf A dst, vecU8At_eq_header_sep_buf A (dst + 24#64)]
  unfold vecHeader
  have hzip_len : (keys'.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  rw [hzip_len]
  have hd32 : dst + 24#64 + 8#64 = dst + 32#64 := by bv_omega
  have hd40 : dst + 24#64 + 16#64 = dst + 40#64 := by bv_omega
  have hd56 : dst + 48#64 + 8#64 = dst + 56#64 := by bv_omega
  have hd64 : dst + 48#64 + 16#64 = dst + 64#64 := by bv_omega
  have hd80 : dst + 72#64 + 8#64 = dst + 80#64 := by bv_omega
  have hd88 : dst + 72#64 + 16#64 = dst + 88#64 := by bv_omega
  have hd96 : dst + 72#64 + 24#64 = dst + 96#64 := by bv_omega
  have hd100 : dst + 72#64 + 28#64 = dst + 100#64 := by bv_omega
  rw [hd32, hd40, hd56, hd64]
  have hcomm :
      ((dst ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        ((dst + 8#64) ↦₆₄ srkPtr') ∗
        ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        ((dst + 24#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        ((dst + 32#64) ↦₆₄ privPtr') ∗
        ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        ((dst + 48#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
        ((dst + 56#64) ↦₆₄ mkPtr') ∗
        ((dst + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
        ((dst + 72#64) ↦₆₄ x25) ∗
        ((dst + 80#64) ↦₆₄ x28) ∗
        ((dst + 88#64) ↦₆₄ x25) ∗
        ((dst + 96#64) ↦₃₂ w27) ∗
        memRegion (dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.srk.bytes.length) srkPtr' gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.priv.bytes.length) privPtr' gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 gc.2.messageKeys.length) mkPtr'
          (keys'.zip gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 gc.2.chainKey) =
      ((((dst ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
         ((dst + 8#64) ↦₆₄ srkPtr') ∗
         ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length)) ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.srk.bytes.length) srkPtr' gc.1.srk.bytes) ∗
       ((((dst + 24#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
         ((dst + 32#64) ↦₆₄ privPtr') ∗
         ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length)) ∗
        vecU8Buf A (BitVec.ofNat 64 gc.1.priv.bytes.length) privPtr' gc.1.priv.bytes) ∗
       ((((dst + 48#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
         ((dst + 56#64) ↦₆₄ mkPtr') ∗
         ((dst + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length)) ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 gc.2.messageKeys.length) mkPtr'
          (keys'.zip gc.2.messageKeys)) ∗
       ((((dst + 72#64) ↦₆₄ x25) ∗
         ((dst + 80#64) ↦₆₄ x28) ∗
         ((dst + 88#64) ↦₆₄ x25) ∗
         ((dst + 96#64) ↦₃₂ w27) ∗
         memRegion (dst + 100#64) 4) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 gc.2.chainKey)) := by
    ac_rfl
  rw [hcomm]
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  have hck := fold_optChainKeyAt A ckPin' x25 x28 w27 gc.2.chainKey (dst + 72#64)
  rwa [hd80, hd88, hd96, hd100] at hck

/-! ## 4. Stack Bundles and Epilogue (`+0x2e0..+0x31c`) -/

/-- Callee-saved register save area `[s0.sp - 96#64 .. s0.sp - 8#64]` plus the two stack slots
`[s0.sp - 120#64 .. s0.sp - 108#64]` that are only referenced in dead code paths. -/
def savedRegsOnStack (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
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
  (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)

/-- The 8 spill slots `[sp - 208#64 .. sp - 152#64]` when existentially quantified. -/
def spillSlotsExist (sp : BitVec 64) : SepProp :=
  (∃∗ v0 : BitVec 64, (sp - 208#64) ↦₆₄ v0) ∗
  (∃∗ w1a : BitVec 32, (sp - 200#64) ↦₃₂ w1a) ∗
  (∃∗ w1b : BitVec 32, (sp - 196#64) ↦₃₂ w1b) ∗
  (∃∗ v2 : BitVec 64, (sp - 192#64) ↦₆₄ v2) ∗
  (∃∗ v3 : BitVec 64, (sp - 184#64) ↦₆₄ v3) ∗
  (∃∗ v4 : BitVec 64, (sp - 176#64) ↦₆₄ v4) ∗
  (∃∗ v5 : BitVec 64, (sp - 168#64) ↦₆₄ v5) ∗
  (∃∗ v6 : BitVec 64, (sp - 160#64) ↦₆₄ v6) ∗
  (∃∗ v7 : BitVec 64, (sp - 152#64) ↦₆₄ v7)

theorem fold_stackAt_chainClone (s0 : State) (v8 v9 v10 v13 : BitVec 64) :
    (stackAt (s0.sp - 208#64) allocHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ v8) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      stackAt s0.sp chainCloneStack := by
  rw [stackAt_chainClone_eq s0.sp]
  unfold spillSlotsExist savedRegsOnStack
  have h8 : ((s0.sp - 144#64) ↦₆₄ v8)
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 144#64) ↦₆₄ x :=
    Entails.sepExists_right v8 (Entails.refl _)
  have h9 : ((s0.sp - 136#64) ↦₆₄ v9)
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 136#64) ↦₆₄ x :=
    Entails.sepExists_right v9 (Entails.refl _)
  have h10 : ((s0.sp - 128#64) ↦₆₄ v10)
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 128#64) ↦₆₄ x :=
    Entails.sepExists_right v10 (Entails.refl _)
  have h13 : ((s0.sp - 104#64) ↦₆₄ v13)
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 104#64) ↦₆₄ x :=
    Entails.sepExists_right v13 (Entails.refl _)
  have h14 : ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 96#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 29#5)) (Entails.refl _)
  have h15 : ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 88#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 30#5)) (Entails.refl _)
  have h16 : ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 80#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 28#5)) (Entails.refl _)
  have h17 : ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 72#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 27#5)) (Entails.refl _)
  have h18 : ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 64#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 26#5)) (Entails.refl _)
  have h19 : ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 56#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 25#5)) (Entails.refl _)
  have h20 : ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 48#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 24#5)) (Entails.refl _)
  have h21 : ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 40#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 23#5)) (Entails.refl _)
  have h22 : ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 32#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 22#5)) (Entails.refl _)
  have h23 : ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 24#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 21#5)) (Entails.refl _)
  have h24 : ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 16#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 20#5)) (Entails.refl _)
  have h25 : ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
      ⊢ ∃∗ x : BitVec 64, (s0.sp - 8#64) ↦₆₄ x :=
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) (Entails.refl _)
  have hstep :
      (stackAt (s0.sp - 208#64) allocHookStack ∗
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
      (stackAt (s0.sp - 208#64) allocHookStack ∗
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
      (stackAt (s0.sp - 208#64) allocHookStack ∗
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
      (stackAt (s0.sp - 208#64) allocHookStack ∗
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

end CryptoVerification.LibsignalTripleRatchet.ChainClone3
