/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.Clone
public import LibsignalBinary.Proofs.Common.HookTrace
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.SepLogic

/-!
# Shared Definitions and Helpers for Relocatable `Chain::clone`

Defines the internal `protoChainAt` / `protoChainCloneSpec` contract, stack spill layouts, and
separation-logic helpers shared across the relocatable `Chain::clone` proofs.
-/

@[expose] public section

namespace CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainCloneDefs

open Arm64 ProofLib ProofLib.ProgramReflection
open Arm64.Obj CryptoVerification
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight memRegion_cells
open CryptoVerification.HookTrace
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone hiding chain_clone_placed_ok_of_hooks chain_clone_placed_ok senderChain_clone_placed_ok_of_hooks senderChain_clone_placed_ok calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32 calleeSavedVRegs_setPC calleeSavedVRegs_setPState calleeSavedVRegs_setMem
open ChainCloneRegReadSimp

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

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
  simp (disch := decide) only [cells_add_succ', Nat.reduceAdd, Nat.reduceSub, cells_zero, sepConj_emp]
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

theorem sepProp_eq_of_entails {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  Entails.antisymm h1 h2

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
  (a ↦₆₄ gk.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.cipher.ptr) ∗ vecU8Buf A gk.cipher.cap gk.cipher.ptr [] ∗
  ((a + 24#64) ↦₆₄ gk.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.mac.ptr) ∗ vecU8Buf A gk.mac.cap gk.mac.ptr [] ∗
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
      messageKeyAt A (clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length) seedPtr', mkg) dst := by
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

structure Slots104 where
  v0 : BitVec 64
  v1 : BitVec 64
  v2 : BitVec 64
  v3 : BitVec 64
  v4 : BitVec 64
  v5 : BitVec 64
  v6 : BitVec 64
  v7 : BitVec 64
  v8 : BitVec 64
  v9 : BitVec 64
  v10 : BitVec 64
  v11 : BitVec 64
  w12 : BitVec 32

theorem entails_sepExists_left {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, P x ⊢ Q) : (∃∗ x, P x) ⊢ Q := by
  unfold Entails sepExists at *
  intro hp ⟨x, hx⟩
  exact h x hp hx

theorem entails_sepExists_sepConj_left {α : Type} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, P x ∗ Q ⊢ R) : (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [sepExists_sepConj_left]
  exact entails_sepExists_left h

theorem entails_pull_exists {α : Type} {A : SepProp} {P : α → SepProp} {Q R : SepProp}
    (h : ∀ x, (A ∗ P x) ∗ Q ⊢ R) : A ∗ (∃∗ x, P x) ∗ Q ⊢ R := by
  rw [← sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]
  exact entails_sepExists_left h

theorem memRegion_104_eq_slots104 (ptr : BitVec 64) :
    memRegion ptr 104 =
      ∃∗ d : Slots104,
        (ptr ↦₆₄ d.v0) ∗
        ((ptr + 8#64) ↦₆₄ d.v1) ∗
        ((ptr + 16#64) ↦₆₄ d.v2) ∗
        ((ptr + 24#64) ↦₆₄ d.v3) ∗
        ((ptr + 32#64) ↦₆₄ d.v4) ∗
        ((ptr + 40#64) ↦₆₄ d.v5) ∗
        ((ptr + 48#64) ↦₆₄ d.v6) ∗
        ((ptr + 56#64) ↦₆₄ d.v7) ∗
        ((ptr + 64#64) ↦₆₄ d.v8) ∗
        ((ptr + 72#64) ↦₆₄ d.v9) ∗
        ((ptr + 80#64) ↦₆₄ d.v10) ∗
        ((ptr + 88#64) ↦₆₄ d.v11) ∗
        ((ptr + 96#64) ↦₃₂ d.w12) ∗
        memRegion (ptr + 100#64) 4 := by
  rw [memRegion_104_eq_slots ptr]
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v0 => ?_
    refine entails_pull_exists fun v1 => ?_
    refine entails_pull_exists fun v2 => ?_
    refine entails_pull_exists fun v3 => ?_
    refine entails_pull_exists fun v4 => ?_
    refine entails_pull_exists fun v5 => ?_
    refine entails_pull_exists fun v6 => ?_
    refine entails_pull_exists fun v7 => ?_
    refine entails_pull_exists fun v8 => ?_
    refine entails_pull_exists fun v9 => ?_
    refine entails_pull_exists fun v10 => ?_
    refine entails_pull_exists fun v11 => ?_
    refine entails_pull_exists fun w12 => ?_
    apply Entails.sepExists_right ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, w12⟩
    dsimp only
    simp only [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun d => ?_
    exact sepConj_mono (Entails.sepExists_right d.v0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v2 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v3 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v4 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v5 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v6 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v7 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v8 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v9 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v10 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right d.v11 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right d.w12 (Entails.refl _))))))))))))))

theorem epilogue_post_entails (A : RustAlloc) (x : ChainCloneGhost) (s0 sf : State)
    (srkPtr' privPtr' mkPtr' x25 x28 v9 v10 v13 : BitVec 64)
    (w27 : BitVec 32) (keys' : List MessageKeyGhost) (ckPin' : VecPin)
    (hsrk : PublicKey.deserialize x.gc.1.srk.bytes = .ok x.gc.2.senderRatchetKey)
    (hmax : x.gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : keys'.length = x.gc.2.messageKeys.length)
    (hsrc_klen : x.gc.1.keys.length = x.gc.2.messageKeys.length)
    (htrace : sf.trace = s0.trace) :
    ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
      ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
      ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 32#64) ↦₆₄ privPtr') ∗
      ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
      ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
      ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((x.dst + 72#64) ↦₆₄ x25) ∗
      ((x.dst + 80#64) ↦₆₄ x28) ∗
      ((x.dst + 88#64) ↦₆₄ x25) ∗
      ((x.dst + 96#64) ↦₃₂ w27) ∗
      memRegion (x.dst + 100#64) 4 ∗
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
      vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
        (keys'.zip x.gc.2.messageKeys) ∗
      clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
      protoChainAt A x.gc x.src ∗
      A.pool ∗
      stackAt (s0.sp - 208#64) allocHookStack ∗
      spillSlotsExist s0.sp ∗
      ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
      ((s0.sp - 136#64) ↦₆₄ v9) ∗
      ((s0.sp - 128#64) ↦₆₄ v10) ∗
      ((s0.sp - 104#64) ↦₆₄ v13) ∗
      savedRegsOnStack s0) ⊢
      (protoChainCloneSpec A).post x s0 sf := by
  unfold protoChainCloneSpec
  dsimp only
  apply Entails.pure_right htrace
  let g' := clonedChainGhost x.gc srkPtr' privPtr'
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr' keys' ckPin'
  have hg' :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey) ⊢
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        protoChainAt A (g', x.gc.2) x.dst) := by
    refine Entails.trans
      (fold_chainAt_dst A x.gc x.dst srkPtr' privPtr' mkPtr' x25 x28 w27 keys' ckPin'
        hsrk hmax hklen) ?_
    apply Entails.sepExists_right g'
    exact Entails.pure_right ⟨rfl, rfl, hklen.trans hsrc_klen.symm⟩ (Entails.refl _)
  have hst := fold_stackAt_chainClone s0
    (BitVec.ofNat 64 x.gc.2.messageKeys.length) v9 v10 v13
  have hgroup :
      ((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey ∗
        protoChainAt A x.gc x.src ∗
        A.pool ∗
        stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0) =
      (((x.dst ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 8#64) ↦₆₄ srkPtr') ∗
        ((x.dst + 16#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.srk.bytes.length) ∗
        ((x.dst + 24#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 32#64) ↦₆₄ privPtr') ∗
        ((x.dst + 40#64) ↦₆₄ BitVec.ofNat 64 x.gc.1.priv.bytes.length) ∗
        ((x.dst + 48#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 56#64) ↦₆₄ mkPtr') ∗
        ((x.dst + 64#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((x.dst + 72#64) ↦₆₄ x25) ∗
        ((x.dst + 80#64) ↦₆₄ x28) ∗
        ((x.dst + 88#64) ↦₆₄ x25) ∗
        ((x.dst + 96#64) ↦₃₂ w27) ∗
        memRegion (x.dst + 100#64) 4 ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.srk.bytes.length) srkPtr' x.gc.1.srk.bytes ∗
        vecU8Buf A (BitVec.ofNat 64 x.gc.1.priv.bytes.length) privPtr' x.gc.1.priv.bytes ∗
        vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 x.gc.2.messageKeys.length) mkPtr'
          (keys'.zip x.gc.2.messageKeys) ∗
        clonedOptChainKeyBuf A ckPin' x25 x28 w27 x.gc.2.chainKey) ∗
       protoChainAt A x.gc x.src ∗
       A.pool ∗
       (stackAt (s0.sp - 208#64) allocHookStack ∗
        spillSlotsExist s0.sp ∗
        ((s0.sp - 144#64) ↦₆₄ BitVec.ofNat 64 x.gc.2.messageKeys.length) ∗
        ((s0.sp - 136#64) ↦₆₄ v9) ∗
        ((s0.sp - 128#64) ↦₆₄ v10) ∗
        ((s0.sp - 104#64) ↦₆₄ v13) ∗
        savedRegsOnStack s0)) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono hg' (sepConj_mono_right (sepConj_mono_right hst))

/-- No-op shim spec that records trace preservation. -/
def sessionShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

/-- Region `memcpy` spec that records trace preservation. -/
def sessionMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ₛ bs)

theorem allocFailedIn_of_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem mul104_ne_of_lt {doneLen total : Nat}
    (hlt : doneLen < total) (htot : total ≤ maxMessageKeys) :
    BitVec.ofNat 64 (104 * total) ≠ BitVec.ofNat 64 (104 * doneLen) := by
  intro heq
  have h1 : 104 * total < 2 ^ 64 := by unfold maxMessageKeys at htot; omega
  have h2 : 104 * doneLen < 2 ^ 64 := by unfold maxMessageKeys at htot; omega
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ht
  omega

theorem mul104_beq_eq_false {doneLen total : Nat}
    (hlt : doneLen < total) (htot : total ≤ maxMessageKeys) :
    (BitVec.ofNat 64 (104 * total) == BitVec.ofNat 64 (104 * doneLen)) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul104_ne_of_lt hlt htot

theorem off_add_104 (doneLen : Nat) :
    BitVec.ofNat 64 (104 * doneLen) + 104#64 = BitVec.ofNat 64 (104 * (doneLen + 1)) := by
  simp [Nat.mul_add, BitVec.ofNat_add]

theorem ptr_off_add_104 (mkPtr' : BitVec 64) (doneLen : Nat) :
    mkPtr' + BitVec.ofNat 64 (104 * doneLen) + 104#64 =
      mkPtr' + BitVec.ofNat 64 (104 * (doneLen + 1)) := by
  rw [BitVec.add_assoc, off_add_104]

theorem memRegion_mk_cons (mkPtr' : BitVec 64) (doneLen n : Nat)
    (hn : n + 1 ≤ maxMessageKeys) :
    memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) (104 * (n + 1)) =
      memRegion (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) 104 ∗
      memRegion (mkPtr' + BitVec.ofNat 64 (104 * (doneLen + 1))) (104 * n) := by
  have hmul : 104 * (n + 1) = 104 + 104 * n := by omega
  have hle : 104 + 104 * n ≤ 2 ^ 64 := by unfold maxMessageKeys at hn; omega
  rw [hmul,
      ProofLib.memRegion_split (mkPtr' + BitVec.ofNat 64 (104 * doneLen)) 104 (104 * n) hle,
      ptr_off_add_104]

theorem ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]
  bv_omega

theorem fold_iter_messageKeys (A : RustAlloc)
    (gk : MessageKeyGhost) (mkg : MessageKeyGenerator)
    (srcCur dstCur seedPtr' : BitVec 64)
    (R0 R0b R1 R2 : SepProp)
    (hpos : 0 < mkg.seed.length)
    (hle : mkg.seed.length ≤ gk.seed.cap.toNat)
    (hlt : gk.seed.cap.toNat < 2 ^ 63)
    (hptr : gk.seed.ptr ≠ 0)
    (hptr' : seedPtr' ≠ 0#64) :
    ((seedPtr' ↦ₛ mkg.seed) ∗
      (gk.seed.ptr ↦ₛ mkg.seed) ∗
      R0 ∗
      R0b ∗
      A.live seedPtr' mkg.seed.length 1 ∗
      ((srcCur + 16#64) ↦₆₄ 0#64) ∗
      ((srcCur + 40#64) ↦₆₄ 0#64) ∗
      ((srcCur + 64#64) ↦₆₄ 0#64) ∗
      ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
      ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
      messageKeySourceFrame A gk mkg srcCur ∗
      R1 ∗
      (dstCur ↦₆₄ 0#64) ∗
      ((dstCur + 8#64) ↦₆₄ 1#64) ∗
      ((dstCur + 16#64) ↦₆₄ 0#64) ∗
      ((dstCur + 24#64) ↦₆₄ 0#64) ∗
      ((dstCur + 32#64) ↦₆₄ 1#64) ∗
      ((dstCur + 40#64) ↦₆₄ 0#64) ∗
      ((dstCur + 48#64) ↦₆₄ 0#64) ∗
      ((dstCur + 56#64) ↦₆₄ 1#64) ∗
      ((dstCur + 64#64) ↦₆₄ 0#64) ∗
      ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
      ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
      memRegion (dstCur + 100#64) 4 ∗
      R2) ⊢
    (messageKeyAt A (gk, mkg) srcCur ∗
      messageKeyAt A (clonedMessageKeyGhost (BitVec.ofNat 64 mkg.seed.length) seedPtr', mkg) dstCur ∗
      R1 ∗ R0 ∗ R0b ∗ R2) := by
  have hlt_seed : mkg.seed.length < 2 ^ 63 := by omega
  rw [← fold_cloned_messageKeyAt A mkg seedPtr' dstCur hpos hlt_seed hptr',
      messageKeyAt_eq_source A gk mkg srcCur]
  have hgroup :
      ((seedPtr' ↦ₛ mkg.seed) ∗
        (gk.seed.ptr ↦ₛ mkg.seed) ∗
        R0 ∗
        R0b ∗
        A.live seedPtr' mkg.seed.length 1 ∗
        ((srcCur + 16#64) ↦₆₄ 0#64) ∗
        ((srcCur + 40#64) ↦₆₄ 0#64) ∗
        ((srcCur + 64#64) ↦₆₄ 0#64) ∗
        ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
        ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
        messageKeySourceFrame A gk mkg srcCur ∗
        R1 ∗
        (dstCur ↦₆₄ 0#64) ∗
        ((dstCur + 8#64) ↦₆₄ 1#64) ∗
        ((dstCur + 16#64) ↦₆₄ 0#64) ∗
        ((dstCur + 24#64) ↦₆₄ 0#64) ∗
        ((dstCur + 32#64) ↦₆₄ 1#64) ∗
        ((dstCur + 40#64) ↦₆₄ 0#64) ∗
        ((dstCur + 48#64) ↦₆₄ 0#64) ∗
        ((dstCur + 56#64) ↦₆₄ 1#64) ∗
        ((dstCur + 64#64) ↦₆₄ 0#64) ∗
        ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
        ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
        memRegion (dstCur + 100#64) 4 ∗
        R2) =
      ((((srcCur + 16#64) ↦₆₄ 0#64) ∗
          ((srcCur + 40#64) ↦₆₄ 0#64) ∗
          ((srcCur + 64#64) ↦₆₄ 0#64) ∗
          ((srcCur + 80#64) ↦₆₄ gk.seed.ptr) ∗
          ((srcCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          (gk.seed.ptr ↦ₛ mkg.seed) ∗
          ((srcCur + 96#64) ↦₃₂ mkg.counter) ∗
          messageKeySourceFrame A gk mkg srcCur) ∗
        ((dstCur ↦₆₄ 0#64) ∗
          ((dstCur + 8#64) ↦₆₄ 1#64) ∗
          ((dstCur + 16#64) ↦₆₄ 0#64) ∗
          ((dstCur + 24#64) ↦₆₄ 0#64) ∗
          ((dstCur + 32#64) ↦₆₄ 1#64) ∗
          ((dstCur + 40#64) ↦₆₄ 0#64) ∗
          ((dstCur + 48#64) ↦₆₄ 0#64) ∗
          ((dstCur + 56#64) ↦₆₄ 1#64) ∗
          ((dstCur + 64#64) ↦₆₄ 0#64) ∗
          ((dstCur + 72#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dstCur + 80#64) ↦₆₄ seedPtr') ∗
          ((dstCur + 88#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
          ((dstCur + 96#64) ↦₃₂ mkg.counter) ∗
          memRegion (dstCur + 100#64) 4 ∗
          A.live seedPtr' mkg.seed.length 1 ∗
          (seedPtr' ↦ₛ mkg.seed)) ∗
        R1 ∗ R0 ∗ R0b ∗ R2) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono_left (Entails.pure_right ⟨hpos, hle, hlt, hptr⟩ (Entails.refl _))

theorem vecBuf_mk_nil_eq (A : RustAlloc) :
    vecBuf A 104 8 (messageKeyAt A) 0#64 8#64 [] = emp := by
  unfold vecBuf
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by decide, by decide, by decide⟩
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _

theorem vecBuf_mk_pos_eq (A : RustAlloc) (mkPtr' : BitVec 64)
    (xs : List (MessageKeyGhost × MessageKeyGenerator))
    (hpos : 0 < xs.length) (hmax : xs.length ≤ maxMessageKeys) (hptr' : mkPtr' ≠ 0#64) :
    vecBuf A 104 8 (messageKeyAt A) (BitVec.ofNat 64 xs.length) mkPtr' xs =
      A.live mkPtr' (104 * xs.length) 8 ∗
      arrayAt (messageKeyAt A) 104 mkPtr' xs := by
  unfold vecBuf
  have hlt64 : xs.length < 2 ^ 64 := by unfold maxMessageKeys at hmax; omega
  have htoNat : (BitVec.ofNat 64 xs.length).toNat = xs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
  have hne0 : BitVec.ofNat 64 xs.length ≠ 0 := ofNat_ne_zero_of_pos hpos hlt64
  have hptr_ne : mkPtr' ≠ 0 := hptr'
  have hcap_lt : xs.length * 104 < 2 ^ 63 := by unfold maxMessageKeys at hmax; omega
  have hmul_comm : xs.length * 104 = 104 * xs.length := Nat.mul_comm _ _
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, Nat.zero_mul,
      ProofLib.memRegion_zero, sepConj_emp, hmul_comm]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by rw [htoNat], by rw [htoNat]; exact hcap_lt, hptr_ne⟩
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, Nat.zero_mul,
      ProofLib.memRegion_zero, sepConj_emp, hmul_comm]
    exact Entails.refl _

def chainMkSourceFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
  A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
  memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
    ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_mk_source (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hpos : 0 < gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
        gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
      ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
      arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
      chainMkSourceFrame A gc a := by
  unfold protoChainAt chainMkSourceFrame vecAt vecHeader vecBuf
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [hzip_len, ha56, ha64]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          (if gc.1.mkCap = 0 then emp
           else A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
             arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
             memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
               ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104)) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          (if gc.1.mkCap = 0 then emp
           else A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
             arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
             memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
               ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104)) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hne : gc.1.mkCap ≠ 0 := by
      intro h0; rw [h0] at hle; change gc.2.messageKeys.length ≤ 0 at hle; omega
    simp only [hne, ↓reduceIte]
    apply Entails.pure_right ⟨hle, hlt, hptr⟩
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    have hne : gc.1.mkCap ≠ 0 := by
      intro h0; rw [h0] at hle; change gc.2.messageKeys.length ≤ 0 at hle; omega
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [hne, ↓reduceIte, sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
            ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.2.messageKeys.length ≤ gc.1.mkCap.toNat ∧
            gc.1.mkCap.toNat * 104 < 2 ^ 63 ∧ gc.1.mkPtr ≠ 0⌝ ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          arrayAt (messageKeyAt A) 104 gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          A.live gc.1.mkPtr (gc.1.mkCap.toNat * 104) 8 ∗
          memRegion (gc.1.mkPtr + BitVec.ofNat 64 (gc.2.messageKeys.length * 104))
            ((gc.1.mkCap.toNat - gc.2.messageKeys.length) * 104) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

structure SpillSlots where
  v0 : BitVec 64
  w1a : BitVec 32
  w1b : BitVec 32
  v2 : BitVec 64
  v3 : BitVec 64
  v4 : BitVec 64
  v5 : BitVec 64
  v6 : BitVec 64
  v7 : BitVec 64

theorem spillSlotsExist_eq_struct (sp : BitVec 64) :
    spillSlotsExist sp =
      ∃∗ s : SpillSlots,
        ((sp - 208#64) ↦₆₄ s.v0) ∗
        ((sp - 200#64) ↦₃₂ s.w1a) ∗
        ((sp - 196#64) ↦₃₂ s.w1b) ∗
        ((sp - 192#64) ↦₆₄ s.v2) ∗
        ((sp - 184#64) ↦₆₄ s.v3) ∗
        ((sp - 176#64) ↦₆₄ s.v4) ∗
        ((sp - 168#64) ↦₆₄ s.v5) ∗
        ((sp - 160#64) ↦₆₄ s.v6) ∗
        ((sp - 152#64) ↦₆₄ s.v7) := by
  unfold spillSlotsExist
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v0 => ?_
    refine entails_pull_exists fun w1a => ?_
    refine entails_pull_exists fun w1b => ?_
    refine entails_pull_exists fun v2 => ?_
    refine entails_pull_exists fun v3 => ?_
    refine entails_pull_exists fun v4 => ?_
    refine entails_pull_exists fun v5 => ?_
    refine entails_pull_exists fun v6 => ?_
    rw [sepExists_sepConj_right]
    refine entails_sepExists_left fun v7 => ?_
    apply Entails.sepExists_right ⟨v0, w1a, w1b, v2, v3, v4, v5, v6, v7⟩
    dsimp only
    simp only [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun s => ?_
    exact sepConj_mono (Entails.sepExists_right s.v0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.w1a (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.w1b (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v2 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v3 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v4 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v5 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right s.v6 (Entails.refl _))
      (Entails.sepExists_right s.v7 (Entails.refl _)))))))))

def savedRegsCore (s0 : State) : SepProp :=
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
  (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a)

theorem savedRegsOnStack_eq_core (s0 : State) :
    savedRegsOnStack s0 =
      ∃∗ p : BitVec 64 × BitVec 32,
        ((s0.sp - 120#64) ↦₆₄ p.1) ∗
        ((s0.sp - 108#64) ↦₃₂ p.2) ∗
        savedRegsCore s0 := by
  unfold savedRegsOnStack savedRegsCore
  rw [show (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
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
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b)) =
      ((∃∗ v11 : BitVec 64, (s0.sp - 120#64) ↦₆₄ v11) ∗
        (∃∗ w12b : BitVec 32, (s0.sp - 108#64) ↦₃₂ w12b) ∗
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
          (∃∗ w12a : BitVec 32, (s0.sp - 112#64) ↦₃₂ w12a))) by ac_rfl]
  apply sepProp_eq_of_entails
  · refine entails_sepExists_sepConj_left fun v11 => ?_
    refine entails_pull_exists fun w12b => ?_
    apply Entails.sepExists_right (v11, w12b)
    rw [sepConj_assoc]
    exact Entails.refl _
  · refine entails_sepExists_left fun p => ?_
    exact sepConj_mono (Entails.sepExists_right p.1 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right p.2 (Entails.refl _)))

theorem map_snd_zip_of_length_eq {α β : Type} (xs : List α) (ys : List β)
    (hlen : xs.length = ys.length) :
    (xs.zip ys).map Prod.snd = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs' ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys' =>
      simp only [List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih ys' (Nat.succ.inj hlen)

theorem mul_104_eq (n : Nat) :
    BitVec.ofNat 64 n * 104#64 = BitVec.ofNat 64 (104 * n) := by
  rw [Nat.mul_comm, BitVec.ofNat_mul]

theorem toNat_mul_104 {n : Nat} (hmax : n ≤ maxMessageKeys) :
    (BitVec.ofNat 64 (104 * n)).toNat = 104 * n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold maxMessageKeys at hmax; omega)]

def chainMkLenFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_mk_len (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      chainMkLenFrame A gc a := by
  unfold protoChainAt chainMkLenFrame vecAt vecHeader
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  rw [hzip_len, ha56, ha64]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

def chainCkSomeFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
  A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
  memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
  memRegion (a + 100#64) 4

theorem chainAt_eq_ck_some (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = some ck) :
    protoChainAt A gc a =
      ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
      ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
      ((a + 88#64) ↦₆₄ 32#64) ∗
      ((a + 96#64) ↦₃₂ ck.index) ∗
      (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
      chainCkSomeFrame A gc a := by
  unfold protoChainAt chainCkSomeFrame vecAt vecHeader
  have hzip_len : (gc.1.keys.zip gc.2.messageKeys).length = gc.2.messageKeys.length := by
    simp [hklen]
  have hck_len : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hck_pos : 0 < (keyToBytes32 ck.key).length := by rw [hck_len]; decide
  have ha56 : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
  have ha64 : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
  have ha80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  have ha88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
  have ha96 : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
  have ha100 : a + 72#64 + 28#64 = a + 100#64 := by bv_omega
  rw [hzip_len, hck]
  simp only [optChainKeyAt]
  rw [vecU8At_eq_of_pos A (a + 72#64) gc.1.ck.cap gc.1.ck.ptr (keyToBytes32 ck.key) hck_pos,
      hck_len, ha56, ha64, ha80, ha88, ha96, ha100]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    rw [show (vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.cap.toNat < 2 ^ 63 ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

def chainCkNoneCapFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  memRegion (a + 72#64 + 8#64) 24

theorem chainAt_eq_ck_none_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = none) :
    protoChainAt A gc a =
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      chainCkNoneCapFrame A gc a := by
  unfold protoChainAt chainCkNoneCapFrame
  rw [hck]
  dsimp only [optChainKeyAt, optChainKeyNone]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

def chainCkSomeCapFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64) : SepProp :=
  ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
  ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
  ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
  ((a + 88#64) ↦₆₄ 32#64) ∗
  ((a + 96#64) ↦₃₂ ck.index) ∗
  (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
  vecGhostAt A gc.1.srk a ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
  ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
  vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
  A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
  memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
  memRegion (a + 100#64) 4

theorem chainAt_eq_ck_some_cap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hck : gc.2.chainKey = some ck) :
    protoChainAt A gc a =
      ⌜gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
      ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
      chainCkSomeCapFrame A gc ck a := by
  rw [chainAt_eq_ck_some A gc ck a hsrk hmax hklen hck]
  unfold chainCkSomeFrame chainCkSomeCapFrame
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right hlt
    rw [show (((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) =
        (((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    exact sepConj_mono_right (Entails.pure_right ⟨hle, hptr⟩ (Entails.refl _))
  · apply Entails.pure_left; intro hlt
    rw [show (((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          ⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) =
        (⌜32 ≤ gc.1.ck.cap.toNat ∧ gc.1.ck.ptr ≠ 0⌝ ∗
          ((a + 64#64) ↦₆₄ BitVec.ofNat 64 gc.2.messageKeys.length) ∗
          ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
          ((a + 88#64) ↦₆₄ 32#64) ∗
          ((a + 96#64) ↦₃₂ ck.index) ∗
          (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
          vecGhostAt A gc.1.srk a ∗
          vecGhostAt A gc.1.priv (a + 24#64) ∗
          ((a + 48#64) ↦₆₄ gc.1.mkCap) ∗
          ((a + 56#64) ↦₆₄ gc.1.mkPtr) ∗
          vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
          ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
          A.live gc.1.ck.ptr gc.1.ck.cap.toNat 1 ∗
          memRegion (gc.1.ck.ptr + 32#64) (gc.1.ck.cap.toNat - 32) ∗
          memRegion (a + 100#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro ⟨hle, hptr⟩
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

def chainPrivLenFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
  ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
  vecU8Buf A gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_priv_len (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      chainPrivLenFrame A gc a := by
  unfold protoChainAt chainPrivLenFrame
  dsimp only [vecGhostAt, vecU8At, vecU8Buf, vecAt, vecHeader]
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [ha32, ha40]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    exact Entails.of_eq (by ac_rfl)

def chainPrivPosFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  vecGhostAt A gc.1.srk a ∗
  ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
  A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
  memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
    (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_priv_pos (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length)
    (hpos : 0 < gc.1.priv.bytes.length) :
    protoChainAt A gc a =
      ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
        gc.1.priv.cap.toNat < 2 ^ 63 ∧
        gc.1.priv.ptr ≠ 0⌝ ∗
      ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
      (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
      chainPrivPosFrame A gc a := by
  unfold protoChainAt chainPrivPosFrame
  dsimp only [vecGhostAt]
  have ha32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have ha40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [vecU8At_eq_of_pos A (a + 24#64) gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes hpos,
      ha32, ha40]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [sepConj_assoc]
    rw [show (vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    rw [show (vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) =
        (⌜gc.1.priv.bytes.length ≤ gc.1.priv.cap.toNat ∧
            gc.1.priv.cap.toNat < 2 ^ 63 ∧
            gc.1.priv.ptr ≠ 0⌝ ∗
          ((a + 32#64) ↦₆₄ gc.1.priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
          (gc.1.priv.ptr ↦ₛ gc.1.priv.bytes) ∗
          vecU8At A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
          ((a + 24#64) ↦₆₄ gc.1.priv.cap) ∗
          A.live gc.1.priv.ptr gc.1.priv.cap.toNat 1 ∗
          memRegion (gc.1.priv.ptr + BitVec.ofNat 64 gc.1.priv.bytes.length)
            (gc.1.priv.cap.toNat - gc.1.priv.bytes.length) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) by ac_rfl]
    exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

theorem sepWPp_pure_second {prog : Program} {ret : BitVec 64} {s : State}
    {A B : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B) Q Qp) :
    SepWPp prog ret s (A ∗ ⌜φ⌝ ∗ B) Q Qp := by
  rw [show A ∗ ⌜φ⌝ ∗ B = ⌜φ⌝ ∗ A ∗ B by ac_rfl]
  exact SepWPp.pure_elim h

theorem chainAt_eq_pure_sep (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    protoChainAt A gc a =
      ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
        gc.2.messageKeys.length ≤ maxMessageKeys ∧
        gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
      protoChainAt A gc a := by
  unfold protoChainAt
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro hp
    exact Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))
  · apply Entails.pure_left; intro _
    exact Entails.refl _

def chainSrkPosFrame (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) : SepProp :=
  (a ↦₆₄ gc.1.srk.cap) ∗
  A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
  memRegion (gc.1.srk.ptr + BitVec.ofNat 64 gc.1.srk.bytes.length)
    (gc.1.srk.cap.toNat - gc.1.srk.bytes.length) ∗
  vecGhostAt A gc.1.priv (a + 24#64) ∗
  vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
    (gc.1.keys.zip gc.2.messageKeys) ∗
  optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)

theorem chainAt_eq_srk_pos (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64)
    (hsrk : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey)
    (hmax : gc.2.messageKeys.length ≤ maxMessageKeys)
    (hklen : gc.1.keys.length = gc.2.messageKeys.length) :
    protoChainAt A gc a =
      ⌜gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧
        gc.1.srk.cap.toNat < 2 ^ 63 ∧
        gc.1.srk.ptr ≠ 0⌝ ∗
      ((a + 8#64) ↦₆₄ gc.1.srk.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
      (gc.1.srk.ptr ↦ₛ gc.1.srk.bytes) ∗
      chainSrkPosFrame A gc a := by
  have hpos : 0 < gc.1.srk.bytes.length := srk_length_pos hsrk
  unfold protoChainAt chainSrkPosFrame
  dsimp only [vecGhostAt]
  rw [vecU8At_eq_of_pos A a gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes hpos]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_left; rintro ⟨hle, hlt, hptr⟩
    apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
    simp only [sepConj_assoc]
    apply Entails.pure_right ⟨hle, hlt, hptr⟩
    exact Entails.of_eq (by ac_rfl)

def deadStackSlots (sp : BitVec 64) : SepProp :=
  (∃∗ v11 : BitVec 64, (sp - 120#64) ↦₆₄ v11) ∗
  (∃∗ w12a : BitVec 32, (sp - 112#64) ↦₃₂ w12a) ∗
  (∃∗ w12b : BitVec 32, (sp - 108#64) ↦₃₂ w12b)

theorem stackAt_chainClone_eq_entry (sp : BitVec 64) :
    stackAt sp chainCloneStack =
      stackAt (sp - 208#64) allocHookStack ∗
      spillSlotsExist sp ∗
      deadStackSlots sp ∗
      (∃∗ v8 : BitVec 64, (sp - 144#64) ↦₆₄ v8) ∗
      (∃∗ v9 : BitVec 64, (sp - 136#64) ↦₆₄ v9) ∗
      (∃∗ v10 : BitVec 64, (sp - 128#64) ↦₆₄ v10) ∗
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
  rw [stackAt_chainClone_eq sp]
  unfold spillSlotsExist deadStackSlots
  ac_rfl

end CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainCloneDefs
