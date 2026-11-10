/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
meta import LibsignalBinary.Proofs.Placed.GenLsBlock -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep

/-!
# `HookSat`-backed `black_box` Sibling of `ConsumeMessageKey/FindIndexProofs/Loop`

Weakens `h_bb : H lsBlackBoxU8Sym = some blackBoxHook` to
`h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat` for Block `26`
(`RatchetState::find_receiver_chain_index`), splitting the 16 B `black_box` stack
scratch (`[sp - 336, sp - 320)`) out of the existing `704` B region `[sp - 1024, sp - 320)`
(`688 + 16 = 704`) so `find_receiver_chain_index_placed_ok_sat` keeps a token-identical
conclusion on `findPlacedSpec A` (`stackAt s.sp 1024`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (PublicKey ReceiverChain maxMessageKeys)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_26 blkPC_201 blkPC_212 blkPl_26 blkPl_201
   blkPl_212 lsBlackBoxU8Sym lsLogFilterAddr ls_subroutine_ok_cl_of_block
   ls_subroutine_ok_cl_of_plain lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex
  (SepWP_chainAt_info SepWP_entails_pre SepWP_sepExists add_120_eq_add_104_add_16
   arrayAt_cons_sep_pre cells_208_unfold cells_96_unfold chainAt_eq_of_ok chainTail
   deserializeMemPlacedSpec deserializeMem_placed_ok eqStack findIdx?_map_cons_neg
   findIdx?_map_cons_pos findIdxStack_split findPlacedSpec idx_len_step_of_cons_cons
   idx_lt_two_pow_64_of_cons len_mul_104_step_of_cons_cons length_lt_cons
   list_cons_cons_mul_104_ne_104 list_cons_mul_104_sub_104 list_length_induction ofNat_idx_add_one
   out33_entails_memRegion pk_208_eq pk_208_eq_sep pk_247_eq_sep reg_mul_104_eq_ofNat
   sp_sub_248_orr_1 srkRest toNat_ofNat_of_lt zero_add_len_lt_of_mul_104)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat publicKeyEqMemSpec16 publicKey_eq_mem_placed_ok_16_sat)

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. Loop-Shaped `+16 B` `PublicKey::eq` Adapter & `1024`-Byte Stack Split -/

@[expose] def publicKeyEqMemLoopSpec16 :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗ memRegion (sp - 16#64 - 48#64) 48 ∗ stackAt (sp - 64#64) 16
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    memRegion (sp - 16#64) 16 ∗ memRegion (sp - 16#64 - 48#64) 48 ∗ stackAt (sp - 64#64) 16

theorem memRegion_80_eq_loopEq16 (sp : BitVec 64) :
    memRegion (sp - 80#64) 80 =
      memRegion (sp - 16#64) 16 ∗ memRegion (sp - 16#64 - 48#64) 48 ∗ stackAt (sp - 64#64) 16 := by
  simp only [stackAt]
  have h64 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  have h80 : sp - 64#64 - BitVec.ofNat 64 16 = sp - 80#64 := by bv_omega
  rw [h64, h80,
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 16) (k := 64)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 48) (k := 16)
        (b' := sp - 16#64) rfl (by bv_omega) (by decide)]
  sep_ac_rfl

theorem publicKeyEqMemLoop_placed_ok_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemLoopSpec16) := by
  refine subroutine_ok_map (publicKey_eq_mem_placed_ok_16_sat h_bb) ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [withLsCodeLoaded, publicKeyEqMemLoopSpec16, publicKeyEqMemSpec16,
      memRegion_80_eq_loopEq16 sp, sepConj_assoc] using hpre
  · intro sf hpost
    simpa only [withLsCodeLoaded, publicKeyEqMemLoopSpec16, publicKeyEqMemSpec16,
      memRegion_80_eq_loopEq16 sp, sepConj_assoc] using hpost

abbrev eqStack16 (sp : BitVec 64) : SepProp :=
  memRegion (sp - 272#64) 16 ∗ memRegion (sp - 320#64) 48 ∗ stackAt (sp - 320#64) 16

theorem findIdxStack_split_16 (sp : BitVec 64) :
    stackAt sp 1024 =
      memRegion (sp - 1024#64) 688 ∗ eqStack16 sp ∗
      memRegion (sp - 256#64) 8 ∗ memRegion (sp - 248#64) 33 ∗ memRegion (sp - 215#64) 7 ∗
      cells (sp - 208#64) 4 ∗ memRegion (sp - 176#64) 80 ∗ cells (sp - 96#64) 12 := by
  have h704 : memRegion (sp - 1024#64) 704 =
      memRegion (sp - 1024#64) 688 ∗ stackAt (sp - 320#64) 16 := by
    simp only [stackAt]
    have hb : sp - 320#64 - BitVec.ofNat 64 16 = sp - 336#64 := by bv_omega
    rw [hb]
    exact ProofLib.memRegion_split' (b := sp - 1024#64) (n := 688) (k := 16)
      (b' := sp - 336#64) rfl (by bv_omega) (by decide)
  rw [findIdxStack_split sp, h704]
  dsimp only [eqStack16, eqStack]
  sep_ac_rfl

abbrev loopStack16 (s0 : State) (u0 u1 u2 u3 : BitVec 64) : SepProp :=
  memRegion (s0.sp - 1024#64) 688 ∗
  memRegion (s0.sp - 272#64) 16 ∗ memRegion (s0.sp - 320#64) 48 ∗ stackAt (s0.sp - 320#64) 16 ∗
  memRegion (s0.sp - 256#64) 8 ∗ memRegion (s0.sp - 248#64) 33 ∗ memRegion (s0.sp - 215#64) 7 ∗
  ((s0.sp - 208#64) ↦₆₄ u0) ∗ ((s0.sp - 200#64) ↦₆₄ u1) ∗ ((s0.sp - 192#64) ↦₆₄ u2) ∗ ((s0.sp - 184#64) ↦₆₄ u3) ∗
  memRegion (s0.sp - 176#64) 80 ∗
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem entails_stackAt_1024_16 (sp : BitVec 64)
    (u0 u1 u2 u3 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    memRegion (sp - 1024#64) 688 ∗
    memRegion (sp - 272#64) 16 ∗ memRegion (sp - 320#64) 48 ∗ stackAt (sp - 320#64) 16 ∗
    memRegion (sp - 256#64) 8 ∗ memRegion (sp - 248#64) 33 ∗ memRegion (sp - 215#64) 7 ∗
    ((sp - 208#64) ↦₆₄ u0) ∗ ((sp - 200#64) ↦₆₄ u1) ∗ ((sp - 192#64) ↦₆₄ u2) ∗ ((sp - 184#64) ↦₆₄ u3) ∗
    memRegion (sp - 176#64) 80 ∗ ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
    ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗ ((sp - 48#64) ↦₆₄ v6) ∗
    ((sp - 40#64) ↦₆₄ v7) ∗ ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗ ((sp - 16#64) ↦₆₄ v10) ∗
    ((sp - 8#64) ↦₆₄ v11) ⊢ stackAt sp 1024 := by
  rw [findIdxStack_split_16 sp, cells_208_unfold sp, cells_96_unfold sp]
  simp only [eqStack16, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
    (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
    (Entails.sepExists_right v9 (Entails.sepExists_right v10 (Entails.sepExists_right v11
    (Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2
    (Entails.sepExists_right u3 (Entails.refl _))))))))))))))))

theorem loopStack16_entails_stackAt (s0 : State) (u0 u1 u2 u3 : BitVec 64) :
    loopStack16 s0 u0 u1 u2 u3 ⊢ stackAt s0.sp 1024 :=
  entails_stackAt_1024_16 s0.sp u0 u1 u2 u3
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 28#5)) (s0.readReg64 (Reg.gpr 27#5))
    (s0.readReg64 (Reg.gpr 26#5)) (s0.readReg64 (Reg.gpr 25#5))
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))

theorem after_heq_placed_entails_16 [LibsignalPlacement] (A : RustAlloc) (s0 : State)
    (theirA : BitVec 64) (their : PublicKey)
    (gc : ChainGhost × ReceiverChain) (rest : List (ChainGhost × ReceiverChain))
    (cur_p : BitVec 64) (P_pre : SepProp) (w0 w1 w2 w3 : BitVec 64)
    (h1 : PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
      gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
      gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = [])
    (h2 : gc.1.srk.bytes.length ≤ gc.1.srk.cap.toNat ∧ gc.1.srk.cap.toNat < 2 ^ 63 ∧ gc.1.srk.ptr ≠ 0)
    (hcap : gc.1.srk.cap ≠ 0)
    (hpk_cells : ∀ a : BitVec 64,
      (a ↦ₛ gc.2.senderRatchetKey.bytes.toList) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) :
    ((s0.sp - 208#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
      theirA ↦ₛ their.bytes.toList ∗
      memRegion (s0.sp - 272#64) 16 ∗
      memRegion (s0.sp - 320#64) 48 ∗
      stackAt (s0.sp - 320#64) 16 ∗
      gc.1.srk.ptr ↦ₛ gc.1.srk.bytes ∗
      (s0.sp - 248#64) ↦₈ 0#8 ∗
      (s0.sp - 247#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
      lsLogFilterAddr ↦₆₄ 0#64 ∗
      cur_p ↦₆₄ gc.1.srk.cap ∗
      (cur_p + 8#64) ↦₆₄ gc.1.srk.ptr ∗
      (cur_p + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length ∗
      A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
      srkRest gc.1.srk ∗
      chainTail A gc cur_p ∗
      arrayAt (chainAt A) 104 (cur_p + 104#64) rest ∗
      P_pre ∗
      memRegion (s0.sp - 1024#64) 688 ∗
      memRegion (s0.sp - 256#64) 8 ∗
      memRegion (s0.sp - 215#64) 7 ∗
      memRegion (s0.sp - 176#64) 80 ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
      (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
    (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
      (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      loopStack16 s0 w0 w1 w2 w3) := by
  have heq_rhs :
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack16 s0 w0 w1 w2 w3) =
      ((s0.sp - 208#64) ↦ₛ gc.2.senderRatchetKey.bytes.toList ∗
        theirA ↦ₛ their.bytes.toList ∗
        memRegion (s0.sp - 272#64) 16 ∗
        memRegion (s0.sp - 320#64) 48 ∗
        stackAt (s0.sp - 320#64) 16 ∗
        gc.1.srk.ptr ↦ₛ gc.1.srk.bytes ∗
        memRegion (s0.sp - 248#64) 33 ∗
        lsLogFilterAddr ↦₆₄ 0#64 ∗
        cur_p ↦₆₄ gc.1.srk.cap ∗
        (cur_p + 8#64) ↦₆₄ gc.1.srk.ptr ∗
        (cur_p + 16#64) ↦₆₄ BitVec.ofNat 64 gc.1.srk.bytes.length ∗
        A.live gc.1.srk.ptr gc.1.srk.cap.toNat 1 ∗
        srkRest gc.1.srk ∗
        chainTail A gc cur_p ∗
        arrayAt (chainAt A) 104 (cur_p + 104#64) rest ∗
        P_pre ∗
        memRegion (s0.sp - 1024#64) 688 ∗
        memRegion (s0.sp - 256#64) 8 ∗
        memRegion (s0.sp - 215#64) 7 ∗
        memRegion (s0.sp - 176#64) 80 ∗
        (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
        (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) := by
    dsimp only [arrayAt, loopStack16]
    rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap, pk_208_eq hpk_cells]
    sep_ac_rfl
  rw [heq_rhs]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
  rw [← sepConj_assoc]
  exact sepConj_mono_left (out33_entails_memRegion s0.sp (by simp))

/-! ## 2. Block `26` (`RatchetState::find_receiver_chain_index`) under `blackBoxSpecSat` -/

set_option maxHeartbeats 1600000 in
theorem find_loop_placed_ok_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64) (idx : Nat) (P_pre : SepProp)
    (u0 u1 u2 u3 : BitVec 64) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_26).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 idx)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hidx_len : idx + (gc :: rest).length < 2 ^ 63)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP ((blkPC_26).rebase (blkPl_26).base H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack16 s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜sf.trace = s0.trace ∧
              match Option.map (· + idx)
                ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) with
              | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
              | none => sf.readReg64 .x0 = 0#64⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
            (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hdeser0 : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (lsmpl.base 201) deserializeMemPlacedSpec :=
    deserializeMem_placed_ok H
  have hdeser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_26).rebase (blkPl_26).base H) hdeser0
  simp only [withLsCl, deserializeMemPlacedSpec] at hdeser
  have heq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withLsCodeLoaded lsmpl publicKeyEqMemLoopSpec16) :=
    publicKeyEqMemLoop_placed_ok_sat h_bb
  have heq := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_26).rebase (blkPl_26).base H) heq0
  simp only [withLsCl, publicKeyEqMemLoopSpec16] at heq
  induction rest using list_length_induction generalizing gc cur_p idx P_pre u0 u1 u2 u3 s with
  | h rest ih =>
    conv =>
      arg 4
      dsimp only [arrayAt]
      simp only [sepConj_assoc]
    apply SepWP_chainAt_info
    intro h1 h2 hcap hlen
    conv =>
      arg 4
      rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap]
      simp only [sepConj_assoc]
    wp_steps_lscl (lsmpl.base 201)
    wp_apply
    simp only [hsp, hx19, hx20, hx21, hx22, hx23, hx24, htrace.1, htrace.2] at *
    obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
      exists_unpack64_of_length_32 (bs := gc.2.senderRatchetKey.bytes.toList) (by simp)
    rw [← pk_247_eq_sep _ hpk_cells]
    wp_steps_lscl (lsmpl.base 212)
    rw [pk_247_eq_sep _ hpk_cells, pk_208_eq_sep _ hpk_cells]
    wp_apply
    simp only [hsp_sf, h, h_1, h_2, h_3, h_4, h_5, hvregs, hpost] at *
    refine SepWP_entails_pre
      (after_heq_placed_entails_16 A s0 theirA their gc rest cur_p P_pre w0 w1 w2 w3 h1 h2 hcap hpk_cells) ?_
    wp_steps
    wp_if hmatch
    · dsimp only [loopStack16]
      wp_steps
      rw [findIdx?_map_cons_pos idx (beq_iff_eq.mpr hmatch)]
      have hidx_toNat : (BitVec.ofNat 64 idx).toNat = idx :=
        toNat_ofNat_of_lt (idx_lt_two_pow_64_of_cons hidx_len)
      refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (loopStack16_entails_stackAt s0 w0 w1 w2 w3))))) ?_
      wp_done
    · have hmatch_b : ¬(gc.2.senderRatchetKey == their) = true := by
        rw [beq_iff_eq]; exact hmatch
      rw [findIdx?_map_cons_neg idx hmatch_b]
      rcases rest with _ | ⟨gc', rest'⟩
      · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] at *
        dsimp only [loopStack16]
        wp_steps
        simp only [List.map_nil, List.findIdx?_nil, Option.map_none]
        refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (loopStack16_entails_stackAt s0 w0 w1 w2 w3))))) ?_
        wp_done
      · wp_steps
        rw [list_cons_cons_mul_104_ne_104 gc gc' rest' hlen_lt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        conv =>
          arg 5; ext sf P_f
          rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        refine ih rest' (length_lt_cons gc' rest') gc' (cur_p + 104#64) (idx + 1)
          (chainAt A gc cur_p ∗ P_pre) w0 w1 w2 w3 _ (by assumption) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rfl
        · exact hrun_sf_1
        · exact hsp_sf_1
        · exact ofNat_idx_add_one idx
        · exact h_12
        · exact h_13
        · exact list_cons_mul_104_sub_104 gc (gc' :: rest')
        · exact h_15
        · exact add_120_eq_add_104_add_16 cur_p
        · exact ⟨hpost_1, hvregs_1⟩
        · exact idx_len_step_of_cons_cons hidx_len
        · exact len_mul_104_step_of_cons_cons hlen_lt

theorem find_loop_placed_ok_zero_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64)
    {u0 u1 u2 u3 : BitVec 64} {s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_26).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP ((blkPC_26).rebase (blkPl_26).base H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack16 s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜sf.trace = s0.trace ∧
              match (List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their) with
              | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
              | none => sf.readReg64 .x0 = 0#64⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
            (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have h := find_loop_placed_ok_sat A h_bb s0 theirA their R hsp0 rest gc cur_p 0 emp u0 u1 u2 u3 s
    hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 htrace
    (zero_add_len_lt_of_mul_104 hlen_lt) hlen_lt
  simpa only [emp_sepConj, Nat.add_zero, Option.map_id'] using h

/-- `HookSat` `black_box` sibling of `FindReceiverChainIndex.find_receiver_chain_index_placed_ok`
(token-identical conclusion on `findPlacedSpec A`). -/
theorem find_receiver_chain_index_placed_ok_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (findPlacedSpec A)) := by
  have hzero := find_loop_placed_ok_zero_sat A h_bb
  clear h_bb
  simp only [withLsCodeLoaded, findPlacedSpec]
  wp_init g s0
  obtain ⟨p, cs, theirA, their⟩ := g
  dsimp only at h h_1 h_2 h_3 h_4 h_5 ⊢
  subst h_2 h_4
  conv =>
    arg 4
    rw [findIdxStack_split_16 s0.sp, cells_208_unfold s0.sp, cells_96_unfold s0.sp]
    simp only [eqStack16, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  iterate 16 (apply SepWP_sepExists; intro _)
  wp_steps_lscl ((blkPl_26).base + 32#64)
  clear h
  wp_steps
  wp_if hcbz
  · wp_steps
    have hcs_nil : cs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← h_3, hcbz]
      rfl
    subst hcs_nil
    simp only [List.map_nil, List.findIdx?_nil]
    refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (entails_stackAt_1024_16 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))) ?_
    wp_done
  · wp_steps
    rcases cs with _ | ⟨gc, rest⟩
    · exfalso
      apply hcbz
      apply BitVec.eq_of_toNat_eq
      simpa using h_3
    · simp only [sepConj_assoc]
      refine SepWP.mono (by
        apply hzero s0 (s0.readReg64 (Reg.gpr 2#5)) their R h_1
          rest gc (s0.readReg64 (Reg.gpr 0#5))
        · assumption
        · rfl
        · exact hrun
        · rfl
        · rfl
        · rfl
        · rfl
        · exact reg_mul_104_eq_ofNat h_3
        · exact sp_sub_248_orr_1 h_1
        · rfl
        · exact ⟨rfl, rfl⟩
        · exact h_5) ?_
      rintro sf P_f _ _ ⟨hmf, hsp_f, hcs_f⟩
      refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
      rw [satisfies_pure_sepConj]
      exact hmf hm

end LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopSat
