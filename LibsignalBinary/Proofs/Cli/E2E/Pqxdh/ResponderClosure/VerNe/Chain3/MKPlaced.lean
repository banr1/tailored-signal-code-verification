/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MK
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKCntPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKSeedPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKPushPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKHeadPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey

/-!
# Placed `message::merge<Chain> [local#4]`: MessageKeys Slice (`Chain3MessageKeysPlacedStmt`)

`[LibsignalPlacement]` Block-`516` counterpart of `VerNe.Chain3.MK`, assembling the four placed
tag-4 sub-steps into `chain3MessageKeys_placed_ok`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000

/-! ## Assembly -/

set_option maxHeartbeats 400000 in
/-- Assembles `Chain3MessageKeysPlacedStmt` from the four placed tag-4 sub-step statements. -/
theorem chain3MessageKeys_placed_ok_of [LibsignalPlacement] (ext : String → Option (State → State))
    (hHead : Chain3MkHeadPlacedStmt ext) (hCnt : Chain3MkCntPlacedStmt ext)
    (hSeed : Chain3MkSeedPlacedStmt ext) (hPush : Chain3MkPushPlacedStmt ext) :
    Chain3MessageKeysPlacedStmt ext := by
  intro hC x R s0 k s hk htag hs
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hOk, hlen_pay, hmem⟩
  obtain ⟨mk, hfl⟩ := chainField_eq_key_of_tag4 htag
  have hmk_mem : mk ∈ x.c.keys := mem_keys_of_key_mem_fields (hfl ▸ List.getElem_mem hk)
  have hseed : mk.seed.length = 32 := hOk.2.2.2.1 mk hmk_mem
  have hbound : (chainGAfter x.c k).keys.length ≤ maxMessageKeys :=
    le_trans (chainGAfter_keys_length_le x.c k) hOk.2.2.2.2
  have hsp_sub_align : (s0.sp - 0xf0#64) &&& 15#64 = 0#64 := by
    have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    rwa [hsp] at h1
  have halign : s0.sp &&& 15#64 = 0#64 := c3mk_sp0_aligned_of_sub_240 hsp_sub_align
  let pfx : List (BitVec 8) :=
    encodeVarint (BitVec.ofNat 64 x.c.enc.length) ++ (x.c.fields.take k).flatMap ChainField.enc
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail
  have hpay_eq : x.c.payload ++ x.tail =
      pfx ++ (0x22#8 :: BitVec.ofNat 8 (pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed).length ::
        ((pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed) ++ rest)) := by
    rw [chainG_payload_split x.c k x.tail, drop_fields_flatMap_enc_of_key hk hfl x.tail,
      lenField_4_encMessageKey_eq hseed, encMessageKey_eq_pb hseed]; rfl
  have hcur_open : Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
      ((x.c.fields.drop k).flatMap ChainField.enc ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗ Prost.sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 (pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed).length ::
            ((pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed) ++ rest)) := by
    have hrem : (x.c.fields.drop k).flatMap ChainField.enc ++ x.tail =
        0x22#8 :: BitVec.ofNat 8 (pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed).length ::
          ((pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed) ++ rest) := by
      rw [drop_fields_flatMap_enc_of_key hk hfl x.tail, lenField_4_encMessageKey_eq hseed,
        encMessageKey_eq_pb hseed]; rfl
    rw [hrem, hpay_eq, sliceCursorAfter_append_eq_seedChain]
  have hmk_lt : (pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed).length < 128 := by
    rw [← encMessageKey_eq_pb hseed]; exact encMessageKey_length_lt128 hseed
  have htail_le : x.tail.length ≤ rest.length := by simp [rest]
  have hlen_a : 2 + ((pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed).length + rest.length) <
      2 ^ 62 := by
    have h := hlen_pay; rw [hpay_eq] at h
    simp only [List.length_append, List.length_cons] at h ⊢; omega
  have hlen_b : (pbVarint 1 mk.counter.toNat ++ (pbBytes 5 mk.seed ++ rest)).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_a ⊢; omega
  have hlen_c : (pbBytes 5 mk.seed ++ rest).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_a ⊢; omega
  have hk_lt : mk.seed.length < 128 := by omega
  have hmem' : s.mem ⊨
      ((x.bufRef ↦₆₄ x.slot) ∗ memRegion (s0.sp - 0xe8#64) 104 ∗
        Prost.sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 (pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed).length ::
            ((pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed) ++ rest)) ∗
        stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗
        RustHeap.vecOf A0 104 8 (fun mk b => prostMsgKeyAt A0 mk b) (x.a + 0x30#64)
          (chainGAfter x.c k).keys ∗
        c3mkChainNoKeys A0 x.a (chainGAfter x.c k) ∗ (x.ptr ↦ₛ pfx) ∗
        (memRegion (s0.sp - 0xf0#64) 8 ∗ memRegion (s0.sp - 0x80#64) 48 ∗
          ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x25) ∗
          memRegion (s0.sp - 0x38#64) 8 ∗
          ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 0x8#64) ↦₆₄ s0.readReg64 .x19))) ∗ R := by
    rw [chain3GAt_keys_split, hcur_open, chain3SavedRegs_c3mk_split] at hmem
    exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
  refine segStepG_of_sepWPp (ret := chain3PCPlacedAtW ext 0xa8#64) hmem' ?_
  refine SepWPp.focus_pre
    (hHead hC x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length) s0.sp
      (pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed) rest x.tail x R s0 s _ _ _
      hmk_lt htail_le hlen_a hpc hrun hsp halign hcl htr hx19 hx21 hx22 hx23 ?_)
  intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hx25_1 hregs1
  rw [List.append_assoc (pbVarint 1 mk.counter.toNat) (pbBytes 5 mk.seed) rest]
  refine SepWPp.focus_pre
    (hCnt hC x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length + 2#64) s0.sp mk.counter
      (pbBytes 5 mk.seed) rest x R s0 s1 _ _ _
      hlen_b hpc1 hrun1 hsp1 halign hcl1 htr1 (hregs1.1.trans hx19) hx25_1 ?_)
  intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hx25_2 hregs2
  refine SepWPp.focus_pre
    (hSeed hC x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
        BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length) s0.sp mk.seed rest x R s0 s2 _ _ _
      hk_lt hlen_c hpc2 hrun2 hsp2 halign hcl2 htr2 (hregs2.1.trans (hregs1.1.trans hx19))
      (hregs2.2.2.2.1.trans (hregs1.2.2.2.1.trans hx22)) hx25_2 ?_)
  intro s3 hpc3 hrun3 hsp3 hcl3 htr3 hx25_3 hregs3
  have hregs13 : Chain3MkRegs s s3 := (hregs1.trans hregs2).trans hregs3
  apply SepWPp.fold (Entails.of_eq (c3mk_prostMsgKeyAt_fold s0.sp mk)) (by sep_focus)
  refine SepWPp.focus_pre
    (hPush hC x.a x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
        BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length +
        BitVec.ofNat 64 (pbBytes 5 mk.seed).length) s0.sp (chainGAfter x.c k).keys mk rest
      x R s0 s3 _ _ _
      hbound hpc3 hrun3 hsp3 halign hcl3 htr3 (hregs13.1.trans hx19)
      (hregs13.2.1.trans hx20) (hregs13.2.2.2.2.2.1.trans hx24) hx25_3 ?_)
  intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hregs4
  have hregs : Chain3MkRegs s s4 := hregs13.trans hregs4
  refine SepWPp.done hpc4 hrun4 ?_
  intro hmem4
  have hal4 : s4.spAligned = true := by
    simp only [State.spAligned, hsp4, ← hsp]
    exact hal
  refine ⟨hpc4, hrun4, htr4, hregs.2.2.2.2.2.2.2.2.2.2.trans hvregs, hcl4, hsp4, hal4,
    hregs.2.2.2.2.2.2.2.2.2.1.trans hx29,
    hregs.1.trans hx19,
    hregs.2.1.trans hx20,
    hregs.2.2.1.trans hx21,
    hregs.2.2.2.1.trans hx22,
    hregs.2.2.2.2.1.trans hx23,
    hregs.2.2.2.2.2.1.trans hx24,
    hregs.2.2.2.2.2.2.1.trans hx26,
    hregs.2.2.2.2.2.2.2.1.trans hx27,
    hregs.2.2.2.2.2.2.2.2.1.trans hx28,
    hOk, hlen_pay, ?_⟩
  rw [chainGAfter_succ_of_key hk hfl, chain3GAt_push_key,
    chain3SavedRegs_c3mk_split,
    ← sliceCursorAfter_tag4_combine x.slot x.ptr (x.c.payload ++ x.tail) pfx
      (pbVarint 1 mk.counter.toNat) (pbBytes 5 mk.seed) rest hpay_eq]
  exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem4

set_option maxHeartbeats 400000 in
theorem chain3MessageKeys_placed_ok [LibsignalPlacement] (ext : String → Option (State → State)) :
    Chain3MessageKeysPlacedStmt ext :=
  chain3MessageKeys_placed_ok_of ext (chain3MkHead_placed_ok ext) (chain3MkCnt_placed_ok ext)
    (chain3MkSeed_placed_ok ext) (chain3MkPush_placed_ok ext)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
