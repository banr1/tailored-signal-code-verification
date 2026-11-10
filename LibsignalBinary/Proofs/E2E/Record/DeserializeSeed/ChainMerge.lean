/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import ProofLib.SepLogic.WPp

/-!
# Seed `message::merge<Chain>` Verification

Proves that `prost::encoding::message::merge::<session_structure::Chain, &mut &[u8]> [local#1]`
(`0x3974`, block `11`) satisfies `chainMergeSeedSpec` (`chainMergeSeed_ok`) and
`chainMergeSeedPlacedSpec` (`chainMergeSeed_placed_ok`) when decoding a seed `ChainV` payload into
a default-initialized `Chain` slot (`sender_chain` at `SS + 0x90` or the stack temporary for
`receiver_chains`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem pure_sepConj_of_true_seedChain {φ : Prop} (h : φ) (P : SepProp) :
    ⌜φ⌝ ∗ P = P :=
  pure_sepConj_of_true h P

private theorem combine_chain_cursor_seedChain (slot ptr : BitVec 64) (n0 : BitVec 8)
    (b1 b2 b3a b3b b3c tail : List (BitVec 8))
    (hb3a_len : b3a.length = 2) :
    let ptr1 := ptr + 1#64
    let ptr2 := ptr1 + BitVec.ofNat 64 b1.length
    let ptr3a := ptr2 + BitVec.ofNat 64 b2.length
    let ptr3b := ptr3a + 2#64
    let ptr3c := ptr3b + BitVec.ofNat 64 b3b.length
    let ptrEnd := ptr3c + BitVec.ofNat 64 b3c.length
    (ptr ↦₈ n0) ∗
      (ptr1 ↦ₛ b1) ∗
      (ptr2 ↦ₛ b2) ∗
      (ptr3a ↦ₛ b3a) ∗
      (ptr3b ↦ₛ b3b) ∗
      (ptr3c ↦ₛ b3c) ∗
      sliceCursorAt slot ptrEnd tail =
    sliceCursorAfter slot ptr
      ([n0] ++ (b1 ++ (b2 ++ (b3a ++ (b3b ++ b3c)))) ++ tail) tail := by
  intro ptr1 ptr2 ptr3a ptr3b ptr3c ptrEnd
  rw [sliceCursorAfter_append_eq_seedChain slot ptr ([n0] ++ (b1 ++ (b2 ++ (b3a ++ (b3b ++ b3c))))) tail]
  rw [List.singleton_append, pointsToBytes_cons,
    pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  have hp2 : ptr + 1#64 + BitVec.ofNat 64 b1.length = ptr2 := rfl
  have hp3a : ptr2 + BitVec.ofNat 64 b2.length = ptr3a := rfl
  have hp3b : ptr3a + BitVec.ofNat 64 b3a.length = ptr3b := by dsimp [ptr3b]; rw [hb3a_len]
  have hp3c : ptr3b + BitVec.ofNat 64 b3b.length = ptr3c := rfl
  have hpEnd : ptr + BitVec.ofNat 64 (n0 :: (b1 ++ (b2 ++ (b3a ++ (b3b ++ b3c))))).length = ptrEnd := by
    dsimp [ptrEnd, ptr3c, ptr3b, ptr3a, ptr2, ptr1]
    simp only [List.length_append, hb3a_len]
    bv_omega
  rw [hp2, hp3a, hp3b, hp3c, hpEnd]
  dsimp only [ptr1]
  ac_rfl

/-- `prost::encoding::message::merge::<Chain>` (`0x3974`) satisfies `chainMergeSeedSpec` on
`tripleRatchetProgAt`, decoding the 1-byte length varint, `sender_ratchet_key` (tag `1`), optional
`sender_ratchet_key_private` (tag `2`), and inlined `chain_key` (`index` tag `1`, `key` tag `2`). -/
theorem chainMergeSeed_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) : ChainMergeSeedOk C ctl abs := by
  obtain ⟨_, hIM, hBM, _⟩ := hC
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  rcases x with ⟨a, c, bufRef, slot, ptr, tail, f⟩
  dsimp only [chainMergeSeedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, hSeed, hField, hlen_lt, hF, hsym⟩, hmem⟩
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hsp
  have hshape : SeedChainShape c := seedChainShape_of_seedFields_seedChain hSeed hField
  obtain ⟨srk, priv, i, k, rfl, hsrk_len, hpriv, hk_len⟩ := hshape
  have hc_bounds := chainEnc_length_bounds_seedChain (i := i) hsrk_len hpriv hk_len
  have hck_bounds := ckEnc_length_bounds_seedChain i hk_len
  let ck_body : List (BitVec 8) := pbVarint 1 i.toNat ++ pbBytes 2 k
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body]; omega
  have hsrk_lt : srk.length < 128 := by omega
  have hk_lt : k.length < 128 := by omega
  have hpb3 : pbBytes 3 ck_body = [0x1a#8, BitVec.ofNat 8 ck_body.length] ++ ck_body :=
    pbBytes_lt128_eq_seedChain 3 (by decide) ck_body hck_lt
  let b1 : List (BitVec 8) := pbBytes 1 srk
  let b2 : List (BitVec 8) := if priv = [] then [] else pbBytes 2 priv
  let b3a : List (BitVec 8) := [0x1a#8, BitVec.ofNat 8 ck_body.length]
  let b3b : List (BitVec 8) := pbVarint 1 i.toNat
  let b3c : List (BitVec 8) := pbBytes 2 k
  let enc : List (BitVec 8) := (ChainV.mk srk priv (some (i, k))).enc
  have henc_eq : enc = b1 ++ (b2 ++ (b3a ++ (b3b ++ b3c))) := by
    simp [enc, ChainV.enc, b1, b2, b3a, b3b, b3c, ck_body, hpb3, List.append_assoc]
  have henc_lt : enc.length < 128 := hc_bounds.2
  have hlen_lt0 : (1 + (enc.length + tail.length)) < 2 ^ 32 := by
    simp only [List.cons_append, List.length_cons,
      List.length_append] at hlen_lt
    dsimp [enc]; omega
  let ptr1 := ptr + 1#64
  let ptr2 := ptr1 + BitVec.ofNat 64 b1.length
  let ptr3a := ptr2 + BitVec.ofNat 64 b2.length
  let ptr3b := ptr3a + 2#64
  let ptr3c := ptr3b + BitVec.ofNat 64 b3b.length
  let ptrEnd := ptr3c + BitVec.ofNat 64 b3c.length
  have hmem' : s0.mem ⊨
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 enc.length :: (enc ++ tail)) ∗
        stackAt s0.sp chainMergeStack) ∗
        prostChainAt A0 a ⟨[], [], none⟩) ∗ R := by
    simp only [enc, List.cons_append, sepConj_assoc] at hmem ⊢
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hfull : SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs)
      (s0.readReg64 .lr) s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 enc.length :: (enc ++ tail)) ∗
        stackAt s0.sp chainMergeStack) ∗
        prostChainAt A0 a ⟨[], [], none⟩)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ chainMergeSeedSpec.post ⟨a, ⟨srk, priv, some (i, k)⟩, bufRef, slot, ptr, tail, f⟩ s0 sf))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ chainMergeSeedSpec.onPanic ⟨a, ⟨srk, priv, some (i, k)⟩, bufRef, slot, ptr, tail, f⟩ s0 sf ∗ R)) := by
    refine step_chainMerge_seg0_seedChain C ctl a bufRef slot ptr s0.sp enc tail
      henc_lt hlen_lt0 hpc hrun rfl hsp_align hF hsym hx0 hx1 hx2 ?_
    intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hvregs1 hlr1 hx19_1 hx20_1 hx24_1 hx26_1
    rw [prostChainAt_ck_none_eq_seedChain a [] [], henc_eq]
    have hlen_lt1 : (b1 ++ (b2 ++ (b3a ++ (b3b ++ b3c))) ++ tail).length < 2 ^ 32 := by
      rw [← henc_eq, List.length_append]; omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 a [] ∗
        sliceCursorAt slot ptr1 (b1 ++ ((b2 ++ (b3a ++ (b3b ++ b3c))) ++ tail)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          vecU8 A0 (a + 0x18#64) [] ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          ((a + 0x48#64) ↦₆₄ noneCap) ∗
          memRegion (a + 0x50#64) 24 ∗
          chainMergeSavedRegs s0.sp s0)))
      (by simp only [ptr1, henc_eq, List.append_assoc]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg1_seedChain C ctl hBM a bufRef slot ptr1 s0.sp
      srk (b2 ++ (b3a ++ (b3b ++ b3c))) tail hsrk_lt
      (by simpa [b1, List.append_assoc] using hlen_lt1)
      hpc1 hrun1 hsp1 hsp_align hF1 hsym1 htr1 hvregs1 hx19_1 hx20_1 hx24_1 ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hvregs2 hx19_2 hx20_2 hx24_2 hx26_2
    have hx26_2' : s2.readReg64 .x26 = 1#64 := hx26_2.trans hx26_1
    have hlen_lt2 : (b2 ++ (b3a ++ (b3b ++ b3c)) ++ tail).length < 2 ^ 32 := by
      simp only [List.length_append] at hlen_lt1 ⊢; omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x18#64) [] ∗
        sliceCursorAt slot ptr2 (b2 ++ ((b3a ++ (b3b ++ b3c)) ++ tail)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          vecU8 A0 a srk ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          ((a + 0x48#64) ↦₆₄ noneCap) ∗
          memRegion (a + 0x50#64) 24 ∗
          chainMergeSavedRegs s0.sp s0)))
      (by simp only [ptr2, b1, List.append_assoc]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg2_seedChain C ctl hBM a bufRef slot ptr2 s0.sp
      priv (b3a ++ (b3b ++ b3c)) tail hpriv
      (by simpa [b2, List.append_assoc] using hlen_lt2)
      hpc2 hrun2 hsp2 hsp_align hF2 hsym2 htr2 hvregs2 hx19_2 hx20_2 hx24_2 ?_
    intro s3 hpc3 hrun3 hsp3 hF3 hsym3 htr3 hvregs3 hx19_3 hx20_3 hx24_3 hx26_3
    have hx26_3' : s3.readReg64 .x26 = 1#64 := hx26_3.trans hx26_2'
    have hlen_lt3a : (2 + (ck_body.length + tail.length)) < 2 ^ 32 := by
      have hck_eq : b3b ++ b3c = ck_body := rfl
      simp only [b3a, hck_eq, List.length_append, List.length_cons, List.length_nil] at hlen_lt2
      omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          (ptr2 ↦ₛ b2) ∗
          vecU8 A0 a srk ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          chainMergeSavedRegs s0.sp s0)))
      (by
        have hck_eq : b3a ++ (b3b ++ b3c) ++ tail =
            0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail) := by
          simp [b3a, b3b, b3c, ck_body, List.cons_append, List.append_assoc]
        simp only [ptr3a, b2, List.append_assoc] at hck_eq ⊢
        rw [hck_eq]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3a_seedChain C ctl a bufRef slot ptr3a s0.sp
      ck_body tail hck_lt hlen_lt3a
      hpc3 hrun3 hsp3 hF3 hsym3 htr3 hvregs3 hx19_3 hx20_3 hx24_3 hx26_3' ?_
    intro s4 hpc4 hrun4 hsp4 hF4 hsym4 htr4 hvregs4 hx19_4 hx20_4 hx23_4 hx24_4
    have hlen_lt3b : (b3b ++ b3c ++ tail).length < 2 ^ 32 := by
      have hck_eq : b3b ++ b3c = ck_body := rfl
      rw [hck_eq, List.length_append]; omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr3b (b3b ++ (b3c ++ tail)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          (ptr2 ↦ₛ b2) ∗
          (ptr3a ↦ₛ b3a) ∗
          vecU8 A0 a srk ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          vecU8 A0 (a + 0x48#64) [] ∗
          memRegion (a + 0x64#64) 4 ∗
          chainMergeSavedRegs s0.sp s0)))
      (by
        have hck_eq : ck_body ++ tail = b3b ++ (b3c ++ tail) := by
          simp [ck_body, b3b, b3c, List.append_assoc]
        simp only [ptr3b, b3a]
        rw [hck_eq]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3b_seedChain C ctl hIM a bufRef slot ptr3b s0.sp
      i b3c tail hlen_lt3b
      hpc4 hrun4 hsp4 hsp_align hF4 hsym4 htr4 hvregs4 hx19_4 hx20_4 hx23_4 hx24_4 ?_
    intro s5 hpc5 hrun5 hsp5 hF5 hsym5 htr5 hvregs5 hx19_5 hx20_5 hx23_5 hx24_5
    have hlen_lt3c : (b3c ++ tail).length < 2 ^ 32 := by
      simp only [List.length_append] at hlen_lt3b ⊢; omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr3c (b3c ++ tail) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          (ptr2 ↦ₛ b2) ∗
          (ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          vecU8 A0 a srk ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          memRegion (a + 0x64#64) 4 ∗
          chainMergeSavedRegs s0.sp s0)))
      (by simp only [ptr3c, b3b]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3c_seedChain C ctl hBM a bufRef slot ptr3c s0.sp
      k tail hk_lt hlen_lt3c
      hpc5 hrun5 hsp5 hsp_align hF5 hsym5 htr5 hvregs5 hx19_5 hx20_5 hx23_5 hx24_5 ?_
    intro s6 hpc6 hrun6 hsp6 hF6 hsym6 htr6 hvregs6 hx19_6 _ hx23_6 hx24_6
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptrEnd tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack ∗
        chainMergeSavedRegs s0.sp s0) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          (ptr2 ↦ₛ b2) ∗
          (ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          (ptr3c ↦ₛ b3c) ∗
          vecU8 A0 a srk ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          vecU8 A0 (a + 0x48#64) k ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          memRegion (a + 0x64#64) 4)))
      (by simp only [ptrEnd, b3c]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3d_seedChain C ctl bufRef slot ptrEnd s0.sp tail
      hpc6 hrun6 hsp6 hsp_align hF6 hsym6 htr6 hvregs6 rfl hx19_6 hx23_6 hx24_6 ?_
    intro sf hpcf hrunf hspf _ _ htrf hx0f hcsf
    refine SepWPp.done hpcf hrunf ⟨hspf, hcsf, ?_⟩
    dsimp only [chainMergeSeedSpec]
    rw [prostChainAt_ck_some_eq_seedChain a srk priv i k]
    rw [pure_sepConj_of_true_seedChain ⟨htrf, hx0f⟩]
    have hcur := combine_chain_cursor_seedChain slot ptr
      (BitVec.ofNat 8 enc.length)
      b1 b2 b3a b3b b3c tail rfl
    dsimp only at hcur
    have hslice : [BitVec.ofNat 8 enc.length] ++ enc ++ tail =
        [BitVec.ofNat 8 enc.length] ++ (b1 ++ (b2 ++ (b3a ++ (b3b ++ b3c)))) ++ tail := by
      rw [henc_eq]
    change _ ⊢
      (vecU8 A0 a srk ∗ vecU8 A0 (a + 0x18#64) priv ∗
        vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
        vecU8 A0 (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4) ∗
      (bufRef ↦₆₄ slot) ∗
      sliceCursorAfter slot ptr ([BitVec.ofNat 8 enc.length] ++ enc ++ tail) tail ∗
      stackAt s0.sp chainMergeStack
    rw [hslice, ← hcur]
    dsimp only [ptr1, ptr2, ptr3a, ptr3b, ptr3c, ptrEnd]
    exact sep_ac_seedChain (by ac_rfl)
  refine ⟨_, R, hmem', fun R' hm' hL => ?_⟩
  obtain ⟨sf, hsteps, ⟨hpc_f, hrun_f, Pf, hmf, hsp_f, hcs_f, hent_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | hoom⟩ :=
    hfull R' hm' hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, Pf, hmf,
      fun hmR => Satisfies.mono (sepConj_mono_left hent_f) hmR, hsp_f, hcs_f⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, Pf, hmf, htr_f⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## Relocatable `[LibsignalPlacement]` Proof -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Relocatable `prost::encoding::message::merge::<Chain>` (block `11`, `lsProg_11 H`) satisfies
`chainMergeSeedPlacedSpec` given `DeserializeCalleesPlaced H`. -/
theorem chainMergeSeed_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hC : DeserializeCalleesPlaced H) : ChainMergeSeedPlacedOk H := by
  obtain ⟨_, hIM, hBM, _⟩ := hC
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcrl, hx0, hx1, hx2, hshape, hlen_lt, hmem⟩ := chainMergeSeedPlacedPre_unpack hpre
  rcases x with ⟨a, c, bufRef, slot, ptr, tail, f⟩
  dsimp only at hx1 hx2 hshape hlen_lt hmem
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hsp
  obtain ⟨srk, priv, i, k, rfl, hsrk_len, hpriv, hk_len⟩ := hshape
  have hc_bounds := chainEnc_length_bounds_seedChain (i := i) hsrk_len hpriv hk_len
  have hck_bounds := ckEnc_length_bounds_seedChain i hk_len
  let ck_body : List (BitVec 8) := pbVarint 1 i.toNat ++ pbBytes 2 k
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body]; omega
  have hsrk_lt : srk.length < 128 := by omega
  have hk_lt : k.length < 128 := by omega
  have hpb3 : pbBytes 3 ck_body = [0x1a#8, BitVec.ofNat 8 ck_body.length] ++ ck_body :=
    pbBytes_lt128_eq_seedChain 3 (by decide) ck_body hck_lt
  let b1 : List (BitVec 8) := pbBytes 1 srk
  let b2 : List (BitVec 8) := if priv = [] then [] else pbBytes 2 priv
  let b3a : List (BitVec 8) := [0x1a#8, BitVec.ofNat 8 ck_body.length]
  let b3b : List (BitVec 8) := pbVarint 1 i.toNat
  let b3c : List (BitVec 8) := pbBytes 2 k
  let enc : List (BitVec 8) := (ChainV.mk srk priv (some (i, k))).enc
  have henc_eq : enc = b1 ++ (b2 ++ (b3a ++ (b3b ++ b3c))) := by
    simp [enc, ChainV.enc, b1, b2, b3a, b3b, b3c, ck_body, hpb3, List.append_assoc]
  have henc_lt : enc.length < 128 := hc_bounds.2
  have hlen_lt0 : (1 + (enc.length + tail.length)) < 2 ^ 32 := by
    simp only [List.cons_append, List.length_cons,
      List.length_append] at hlen_lt
    dsimp [enc]; omega
  let ptr1 := ptr + 1#64
  let ptr2 := ptr1 + BitVec.ofNat 64 b1.length
  let ptr3a := ptr2 + BitVec.ofNat 64 b2.length
  let ptr3b := ptr3a + 2#64
  let ptr3c := ptr3b + BitVec.ofNat 64 b3b.length
  let ptrEnd := ptr3c + BitVec.ofNat 64 b3c.length
  have hmem' : s0.mem ⊨
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 enc.length :: (enc ++ tail)) ∗
        stackAt s0.sp chainMergeStack) ∗
        prostChainAt A0 a ⟨[], [], none⟩) ∗ R := by
    simp only [enc, List.cons_append, sepConj_assoc] at hmem ⊢
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  have hfull : SepWPp (lsProg_11 H)
      (s0.readReg64 .lr) s0
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (BitVec.ofNat 8 enc.length :: (enc ++ tail)) ∗
        stackAt s0.sp chainMergeStack) ∗
        prostChainAt A0 a ⟨[], [], none⟩)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ chainMergeSeedPlacedSpec.post ⟨a, ⟨srk, priv, some (i, k)⟩, bufRef, slot, ptr, tail, f⟩ s0 sf))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ Serialization.allocPanic (⟨a, ⟨srk, priv, some (i, k)⟩, bufRef, slot, ptr, tail, f⟩ : ChainMergeGhost) s0 sf ∗ R)) := by
    refine step_chainMerge_seg0_placed_seedChain a bufRef slot ptr s0.sp enc tail
      henc_lt hlen_lt0 hpc hrun rfl hsp_align hcrl hx0 hx1 hx2 ?_
    intro s1 hpc1 hrun1 hsp1 hcrl1 htr1 hvregs1 hlr1 hx19_1 hx20_1 hx24_1 hx26_1
    rw [prostChainAt_ck_none_eq_seedChain a [] [], henc_eq]
    have hlen_lt1 : (b1 ++ (b2 ++ (b3a ++ (b3b ++ b3c))) ++ tail).length < 2 ^ 32 := by
      rw [← henc_eq, List.length_append]; omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 a [] ∗
        sliceCursorAt slot ptr1 (b1 ++ ((b2 ++ (b3a ++ (b3b ++ b3c))) ++ tail)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          vecU8 A0 (a + 0x18#64) [] ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          ((a + 0x48#64) ↦₆₄ noneCap) ∗
          memRegion (a + 0x50#64) 24 ∗
          chainMergeSavedRegs s0.sp s0)))
      (by simp only [ptr1, henc_eq, List.append_assoc]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg1_placed_seedChain hBM a bufRef slot ptr1 s0.sp
      srk (b2 ++ (b3a ++ (b3b ++ b3c))) tail hsrk_lt
      (by simpa [b1, List.append_assoc] using hlen_lt1)
      hpc1 hrun1 hsp1 hsp_align hcrl1 htr1 hvregs1 hx19_1 hx20_1 hx24_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hvregs2 hx19_2 hx20_2 hx24_2 hx26_2
    have hx26_2' : s2.readReg64 .x26 = 1#64 := hx26_2.trans hx26_1
    have hlen_lt2 : (b2 ++ (b3a ++ (b3b ++ b3c)) ++ tail).length < 2 ^ 32 := by
      simp only [List.length_append] at hlen_lt1 ⊢; omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x18#64) [] ∗
        sliceCursorAt slot ptr2 (b2 ++ ((b3a ++ (b3b ++ b3c)) ++ tail)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          vecU8 A0 a srk ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          ((a + 0x48#64) ↦₆₄ noneCap) ∗
          memRegion (a + 0x50#64) 24 ∗
          chainMergeSavedRegs s0.sp s0)))
      (by simp only [ptr2, b1, List.append_assoc]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg2_placed_seedChain hBM a bufRef slot ptr2 s0.sp
      priv (b3a ++ (b3b ++ b3c)) tail hpriv
      (by simpa [b2, List.append_assoc] using hlen_lt2)
      hpc2 hrun2 hsp2 hsp_align hcrl2 htr2 hvregs2 hx19_2 hx20_2 hx24_2 ?_
    intro s3 hpc3 hrun3 hsp3 hcrl3 htr3 hvregs3 hx19_3 hx20_3 hx24_3 hx26_3
    have hx26_3' : s3.readReg64 .x26 = 1#64 := hx26_3.trans hx26_2'
    have hlen_lt3a : (2 + (ck_body.length + tail.length)) < 2 ^ 32 := by
      have hck_eq : b3b ++ b3c = ck_body := rfl
      simp only [b3a, hck_eq, List.length_append, List.length_cons, List.length_nil] at hlen_lt2
      omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        ((a + 0x48#64) ↦₆₄ noneCap) ∗
        memRegion (a + 0x50#64) 24 ∗
        sliceCursorAt slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          (ptr2 ↦ₛ b2) ∗
          vecU8 A0 a srk ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          chainMergeSavedRegs s0.sp s0)))
      (by
        have hck_eq : b3a ++ (b3b ++ b3c) ++ tail =
            0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ tail) := by
          simp [b3a, b3b, b3c, ck_body, List.cons_append, List.append_assoc]
        simp only [ptr3a, b2, List.append_assoc] at hck_eq ⊢
        rw [hck_eq]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3a_placed_seedChain a bufRef slot ptr3a s0.sp
      ck_body tail hck_lt hlen_lt3a
      hpc3 hrun3 hsp3 hcrl3 htr3 hvregs3 hx19_3 hx20_3 hx24_3 hx26_3' ?_
    intro s4 hpc4 hrun4 hsp4 hcrl4 htr4 hvregs4 hx19_4 hx20_4 hx23_4 hx24_4
    have hlen_lt3b : (b3b ++ b3c ++ tail).length < 2 ^ 32 := by
      have hck_eq : b3b ++ b3c = ck_body := rfl
      rw [hck_eq, List.length_append]; omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        ((a + 0x60#64) ↦₃₂ 0#32) ∗
        sliceCursorAt slot ptr3b (b3b ++ (b3c ++ tail)) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          (ptr2 ↦ₛ b2) ∗
          (ptr3a ↦ₛ b3a) ∗
          vecU8 A0 a srk ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          vecU8 A0 (a + 0x48#64) [] ∗
          memRegion (a + 0x64#64) 4 ∗
          chainMergeSavedRegs s0.sp s0)))
      (by
        have hck_eq : ck_body ++ tail = b3b ++ (b3c ++ tail) := by
          simp [ck_body, b3b, b3c, List.append_assoc]
        simp only [ptr3b, b3a]
        rw [hck_eq]
        exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3b_placed_seedChain hIM a bufRef slot ptr3b s0.sp
      i b3c tail hlen_lt3b
      hpc4 hrun4 hsp4 hsp_align hcrl4 htr4 hvregs4 hx19_4 hx20_4 hx23_4 hx24_4 ?_
    intro s5 hpc5 hrun5 hsp5 hcrl5 htr5 hvregs5 hx19_5 hx20_5 hx23_5 hx24_5
    have hlen_lt3c : (b3c ++ tail).length < 2 ^ 32 := by
      simp only [List.length_append] at hlen_lt3b ⊢; omega
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x48#64) [] ∗
        sliceCursorAt slot ptr3c (b3c ++ tail) ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          (ptr2 ↦ₛ b2) ∗
          (ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          vecU8 A0 a srk ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          memRegion (a + 0x64#64) 4 ∗
          chainMergeSavedRegs s0.sp s0)))
      (by simp only [ptr3c, b3b]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3c_placed_seedChain hBM a bufRef slot ptr3c s0.sp
      k tail hk_lt hlen_lt3c
      hpc5 hrun5 hsp5 hsp_align hcrl5 htr5 hvregs5 hx19_5 hx20_5 hx23_5 hx24_5 ?_
    intro s6 hpc6 hrun6 hsp6 hcrl6 htr6 hvregs6 hx19_6 _ hx23_6 hx24_6
    refine SepWPp.mono_pre_seedChain
      (P' := (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptrEnd tail ∗
        stackAt (s0.sp - 256#64) chainMergeSubStack ∗
        chainMergeSavedRegs s0.sp s0) ∗
        ((ptr ↦₈ BitVec.ofNat 8 enc.length) ∗
          (ptr1 ↦ₛ b1) ∗
          (ptr2 ↦ₛ b2) ∗
          (ptr3a ↦ₛ b3a) ∗
          (ptr3b ↦ₛ b3b) ∗
          (ptr3c ↦ₛ b3c) ∗
          vecU8 A0 a srk ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
          vecU8 A0 (a + 0x48#64) k ∗
          ((a + 0x60#64) ↦₃₂ i) ∗
          memRegion (a + 0x64#64) 4)))
      (by simp only [ptrEnd, b3c]; exact sep_ac_seedChain (by ac_rfl)) ?_
    refine step_chainMerge_seg3d_placed_seedChain bufRef slot ptrEnd s0.sp tail
      hpc6 hrun6 hsp6 hsp_align hcrl6 htr6 hvregs6 rfl hx19_6 hx23_6 hx24_6 ?_
    intro sf hpcf hrunf hspf _ htrf hx0f hcsf
    refine SepWPp.done hpcf hrunf ⟨hspf, hcsf, ?_⟩
    dsimp only [chainMergeSeedPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded,
      chainMergeSeedRawSpec]
    rw [prostChainAt_ck_some_eq_seedChain a srk priv i k]
    rw [pure_sepConj_of_true_seedChain ⟨htrf, hx0f⟩]
    have hcur := combine_chain_cursor_seedChain slot ptr
      (BitVec.ofNat 8 enc.length)
      b1 b2 b3a b3b b3c tail rfl
    dsimp only at hcur
    have hslice : [BitVec.ofNat 8 enc.length] ++ enc ++ tail =
        [BitVec.ofNat 8 enc.length] ++ (b1 ++ (b2 ++ (b3a ++ (b3b ++ b3c)))) ++ tail := by
      rw [henc_eq]
    change _ ⊢
      (vecU8 A0 a srk ∗ vecU8 A0 (a + 0x18#64) priv ∗
        vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
        vecU8 A0 (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4) ∗
      (bufRef ↦₆₄ slot) ∗
      sliceCursorAfter slot ptr ([BitVec.ofNat 8 enc.length] ++ enc ++ tail) tail ∗
      stackAt s0.sp chainMergeStack
    rw [hslice, ← hcur]
    dsimp only [ptr1, ptr2, ptr3a, ptr3b, ptr3c, ptrEnd]
    exact sep_ac_seedChain (by ac_rfl)
  refine ⟨_, R, hmem', fun R' hm' hL => ?_⟩
  obtain ⟨sf, hsteps, ⟨hpc_f, hrun_f, Pf, hmf, hsp_f, hcs_f, hent_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | hoom⟩ :=
    hfull R' hm' hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, Pf, hmf,
      fun hmR => Satisfies.mono (sepConj_mono_left hent_f) hmR, hsp_f, hcs_f⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, Pf, hmf, htr_f⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed

