/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import Mathlib.Algebra.Group.Nat.Defs
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WPp
import VCVio.Prelude.Core

@[expose] public section

namespace CryptoVerification.LibsignalSession.FindReceiverChainIndex

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames
  CryptoGames.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `PublicKey::deserialize` (`0x3db50`) -/

theorem publicKey_deserialize_ok_inversion {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) :
    bs = djbType :: pk.bytes.toList ++ bs.drop 33 ∧ 33 ≤ bs.length := by
  unfold PublicKey.deserialize at h
  rcases bs with _ | ⟨b0, b1⟩
  · contradiction
  · dsimp only at h
    split at h <;> try contradiction
    rename_i h_djb
    split at h <;> try contradiction
    rename_i h_len
    cases h
    have hb0 : b0 = djbType := Classical.not_not.mp h_djb
    subst hb0
    have hlen : 32 ≤ b1.length := by omega
    refine ⟨?_, by simp; omega⟩
    simp only [List.cons_append, List.cons.injEq, true_and]
    change b1 = (Vector.mk (b1.take 32).toArray (by simp [hlen]) : Vector (BitVec 8) 32).toList ++ b1.drop 32
    simp [List.take_append_drop]

theorem pointsToBytes_deserialize_split (ptr : BitVec 64) {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) :
    (ptr ↦ₛ bs) =
      ((ptr ↦₈ 5#8) ∗ ((ptr + 1#64) ↦ₛ pk.bytes.toList) ∗ ((ptr + 33#64) ↦ₛ bs.drop 33)) := by
  obtain ⟨hbs, _⟩ := publicKey_deserialize_ok_inversion h
  conv_lhs => rw [hbs]
  change (ptr ↦ₛ (5#8 :: pk.bytes.toList ++ bs.drop 33)) = _
  rw [List.cons_append, pointsToBytes_cons, pointsToBytes_append]
  have hlen : pk.bytes.toList.length = 32 := by simp
  rw [hlen]
  have h33 : ptr + 1#64 + BitVec.ofNat 64 32 = ptr + 33#64 := by bv_arith
  rw [h33]

theorem fnAddr_adrp_3dae0 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr "<libsignal_core::curve::PublicKey>::deserialize" + 32#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "session_message_encrypt" + 1292)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize"), BitVec.add_assoc,
    adrp_page_of_aligned hb]
  rfl

abbrev DeserGhost := BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64 × BitVec 8 × List (BitVec 8)

def deserializeSpec (b : BitVec 64) : Spec DeserGhost where
  pre := fun (ptr, bs, pk, sret, tag0, out32) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63 ∧
      PublicKey.deserialize bs = .ok pk ∧ out32.length = 32 ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
    (ptr ↦ₛ bs) ∗
    (sret ↦₈ tag0) ∗ ((sret + 1#64) ↦ₛ out32) ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)
  post := fun (ptr, bs, pk, sret, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    (sret ↦₈ 0#8) ∗ ((sret + 1#64) ↦ₛ pk.bytes.toList) ∗
    ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)

theorem deserialize_ok (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr "<libsignal_core::curve::PublicKey>::deserialize")
      (deserializeSpec b) := by
  simp only [deserializeSpec]
  code_fetches libsignalSessionCode libsignalSessionBin b H (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize") (num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize")) 272
  wp_init g s0
  have hadrp := fnAddr_adrp_3dae0 (b := b) (H := H) h
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ptr, bs, pk, sret, tag0, out32⟩ := g
  dsimp only at *
  subst h_1 h_3
  obtain ⟨_, hge33⟩ := publicKey_deserialize_ok_inversion h_5
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := pk.bytes.toList) (by simp)
  obtain ⟨u0, u1, u2, u3, _, hout_cells⟩ :=
    exists_unpack64_of_length_32 (bs := out32) h_6
  rw [pointsToBytes_deserialize_split (s0.readReg64 (Reg.gpr 0#5)) h_5,
    hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
    hout_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_if hcs
  · simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      h_2, decide_eq_true_eq] at hcs
    omega
  · wp_steps
    wp_if hcbz9
    · wp_steps
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_done
    · wp_steps
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_done

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block 201) -/

def deserializePlacedSpec [LibsignalPlacement] : Spec DeserGhost where
  pre := fun (ptr, bs, pk, sret, tag0, out32) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63 ∧
      PublicKey.deserialize bs = .ok pk ∧ out32.length = 32⌝ ∗
    (ptr ↦ₛ bs) ∗
    (sret ↦₈ tag0) ∗ ((sret + 1#64) ↦ₛ out32) ∗
    (lsLogFilterAddr ↦₆₄ 0#64)
  post := fun (ptr, bs, pk, sret, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    (sret ↦₈ 0#8) ∗ ((sret + 1#64) ↦ₛ pk.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64)

theorem deserialize_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base deserializePlacedSpec := by
  simp only [deserializePlacedSpec]
  wp_init g s0
  obtain ⟨ptr, bs, pk, sret, tag0, out32⟩ := g
  dsimp only at *
  subst h_1 h_3
  obtain ⟨_, hge33⟩ := publicKey_deserialize_ok_inversion h_5
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := pk.bytes.toList) (by simp)
  obtain ⟨u0, u1, u2, u3, _, hout_cells⟩ :=
    exists_unpack64_of_length_32 (bs := out32) h
  rw [pointsToBytes_deserialize_split (s0.readReg64 (Reg.gpr 0#5)) h_5,
    hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
    hout_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_if hcs
  · simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      h_2, decide_eq_true_eq] at hcs
    omega
  · wp_step
    wp_if hcbz9
    · wp_steps
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_done
    · wp_steps
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_done

end CryptoVerification.LibsignalSession.FindReceiverChainIndex
