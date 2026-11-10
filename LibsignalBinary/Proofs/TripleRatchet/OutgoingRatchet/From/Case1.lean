/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Frame
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `OutgoingTripleRatchet::from_session_state` Case 1 (`st.senderChain = none`)

Verifies the `missingSenderChain` error branch (`st.senderChain = none`) of
`<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_setWidth32 zeroExtend64_setWidth16 zeroExtend32_setWidth16
  zeroExtend64_setWidth8 zeroExtend32_setWidth8

/-! ## Case 1: `st.senderChain = none` (`missingSenderChain`) -/

theorem otrFrom_case1_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName)
      (otrFromCaseSpec A img (fun x => x.st.senderChain = none)) := by
  dsimp only [otrFromCaseSpec, otrFromSpec, Spec.inImage]
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.libsignalSessionBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") (num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) 0 120
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.libsignalSessionBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") (num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) 416 44
  wp_init
  have hadrp1 := fnAddr_adrp_b7fc (b := img.base)
    (H := Rust.withPanics ext)
    (ProofLib.ObjectLoad.base_aligned_of_loads himg)
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ss, G, st, ret⟩ := a
  dsimp only [logOff] at *
  refine SepWP.add_rodata (fun hm => rodata_missingSenderChain_intro himg h_2.roData hm) ?_
  refine SepWP.fold (sessionStateAt_sender_none A ss G st h_1) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  conv =>
    arg 4
    rw [sessionStateAt_eq_from_none A ss G st h_1 hGs,
        stackAt_prologue s0.sp,
        ret200_split_br1 ret]
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro r11
  apply SepWP.exists_elim; intro r10
  apply SepWP.exists_elim; intro r9
  apply SepWP.exists_elim; intro r8
  apply SepWP.exists_elim; intro r7
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  wp_steps
  have hmod := otrFrom_model_none ⟨ss, G, st, ret⟩ h_1
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .error (.invalidSessionStructure .missingSenderChain) :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = st :=
    congrArg Prod.snd hmod
  have hnopanic : (.error (.invalidSessionStructure .missingSenderChain) :
      Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8)))) ≠ .error .panic := by
    decide
  have hagree : G.AgreeExceptPq G := rfl
  refine FromSessionStateFacts.finish_otrFrom ⟨ss, G, st, ret⟩ G _ _ hmod1 hmod2 hnopanic hagree (by wp_done) ?_
  refine FromSessionStateFacts.fold_entails (sessionStateAt_from_none_fold A ss G st h_1 hGs) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 104) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 108))) 20#64 G.pq .missingSenderChain)
    (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  exact ent_of_eq (by ac_rfl)

theorem otrFrom_case1_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrFromName)
      (otrFromCaseSpec A img (fun x => x.st.senderChain = none)) :=
  otrFrom_case1_ok_ext himg

/-! ## Relocatable `[LibsignalPlacement]` Case 1 (`st.senderChain = none`) -/

theorem otrFrom_case1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpec A (fun x => x.st.senderChain = none)) := by
  dsimp only [otrFromCasePlacedSpec, otrFromRawPlacedSpec]
  wp_init
  obtain ⟨ss, G, st, ret⟩ := a
  dsimp only at *
  refine SepWP.add_rodata (fun hm => rodata_missingSenderChain_placed_intro h_3 hm) ?_
  refine SepWP.fold (sessionStateAt_sender_none A ss G st h_1) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  conv =>
    arg 4
    rw [sessionStateAt_eq_from_none A ss G st h_1 hGs,
        stackAt_prologue s0.sp,
        ret200_split_br1 ret]
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro r11
  apply SepWP.exists_elim; intro r10
  apply SepWP.exists_elim; intro r9
  apply SepWP.exists_elim; intro r8
  apply SepWP.exists_elim; intro r7
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  wp_steps
  have hmod := otrFrom_model_none ⟨ss, G, st, ret⟩ h_1
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .error (.invalidSessionStructure .missingSenderChain) :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = st :=
    congrArg Prod.snd hmod
  have hnopanic : (.error (.invalidSessionStructure .missingSenderChain) :
      Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8)))) ≠ .error .panic := by
    decide
  have hagree : G.AgreeExceptPq G := rfl
  refine FromSessionStateFacts.finish_otrFrom_placed ⟨ss, G, st, ret⟩ G _ _ hmod1 hmod2 hnopanic hagree (by wp_done) ?_
  refine FromSessionStateFacts.fold_entails (sessionStateAt_from_none_fold A ss G st h_1 hGs) (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (lsρ missingSenderChainSym) 20#64 G.pq .missingSenderChain)
    (by sep_focus) ?_
  refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
    (by sep_focus) ?_
  exact ent_of_eq (by ac_rfl)

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
