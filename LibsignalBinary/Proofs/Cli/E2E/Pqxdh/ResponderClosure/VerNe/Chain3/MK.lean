/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKCnt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKHead
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKPush
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.MKSeed
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey

/-!
# `message::merge<Chain> [local#5]`: MessageKeys Slice (`Chain3MessageKeysStmt`)

Assembles the four tag-4 (`message_keys`, `+0x0a8 → +0x0a8`) sub-steps on a canonical `MessageKey`
encoding `0x22 :: L :: (v1 ++ v2) ++ rest`:
- `Chain3MkHeadStmt` (`+0x0a8 → +0x244`): outer key `0x22`, default scratch `MessageKey` at
  `sp0 - 0xe8`, and inner limit `x25 = |rest|`;
- `Chain3MkCntStmt` (`+0x244 → +0x244`): `counter` varint field (`pbVarint 1 counter`);
- `Chain3MkSeedStmt` (`+0x244 → +0x244`): 32-byte `seed` field (`pbBytes 5 seed`);
- `Chain3MkPushStmt` (`+0x244 → +0x0a8`): push of the scratch `MessageKey` onto `Vec<MessageKey>` at
  `a + 0x30`.
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

set_option maxRecDepth 200000

/-! ## 1. Frame pieces -/

set_option maxHeartbeats 400000 in
theorem c3mk_sp0_aligned_of_sub_240 {sp0 : BitVec 64} (h : (sp0 - 0xf0#64) &&& 15#64 = 0#64) :
    sp0 &&& 15#64 = 0#64 := by
  revert h; bv_robdd

set_option maxHeartbeats 400000 in
/-- The filled scratch is `prostMsgKeyAt A mk (sp0 - 0xe8)`. -/
theorem c3mk_prostMsgKeyAt_fold {A : RustAlloc} (sp0 : BitVec 64) (mk : MessageKeyGenerator) :
    vecU8 A (sp0 - 0xe8#64) [] ∗ vecU8 A (sp0 - 208#64) [] ∗ vecU8 A (sp0 - 184#64) [] ∗
      vecU8 A (sp0 - 160#64) mk.seed ∗ ((sp0 - 136#64) ↦₃₂ mk.counter) ∗
      memRegion (sp0 - 132#64) 4 = prostMsgKeyAt A mk (sp0 - 0xe8#64) := by
  unfold prostMsgKeyAt
  have e1 : (sp0 - 0xe8#64) + 24#64 = sp0 - 208#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 0xe8#64) + 48#64 = sp0 - 184#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e3 : (sp0 - 0xe8#64) + 72#64 = sp0 - 160#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e4 : (sp0 - 0xe8#64) + 96#64 = sp0 - 136#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e5 : (sp0 - 0xe8#64) + 100#64 = sp0 - 132#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [e1, e2, e3, e4, e5]

/-- `chain3GAt` without the `Vec<MessageKey>` at `a + 0x30`: the part the tag-4 path keeps. -/
def c3mkChainNoKeys (A : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  chain3VecAt A a c.srk ∗ chain3VecAt A (a + 0x18#64) c.priv ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

set_option maxHeartbeats 400000 in
theorem chain3GAt_keys_split (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    chain3GAt A a c =
      RustHeap.vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
        c3mkChainNoKeys A a c := by
  rcases c with ⟨srk, priv, ck, keys⟩
  rcases ck with _ | ⟨i, k⟩
  · unfold chain3GAt chainGRest c3mkChainNoKeys
    dsimp only
    ac_rfl
  · unfold chain3GAt chainGRest c3mkChainNoKeys
    dsimp only
    ac_rfl

set_option maxHeartbeats 400000 in
theorem c3mkChainNoKeys_update_keys (A : RustAlloc) (a : BitVec 64) (c : ChainG)
    (ks : List MessageKeyGenerator) :
    c3mkChainNoKeys A a { c with keys := ks } = c3mkChainNoKeys A a c := rfl

set_option maxHeartbeats 400000 in
/-- The chain after the push of `mk`. -/
theorem chain3GAt_push_key (A : RustAlloc) (a : BitVec 64) (c : ChainG) (mk : MessageKeyGenerator) :
    chain3GAt A a { c with keys := c.keys ++ [mk] } =
      RustHeap.vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) (c.keys ++ [mk]) ∗
        c3mkChainNoKeys A a c := by
  rw [chain3GAt_keys_split, c3mkChainNoKeys_update_keys]

set_option maxHeartbeats 400000 in
/-- `chain3SavedRegs` with the 104 scratch bytes `[sp0 - 0xe8, sp0 - 0x80)` split out. -/
theorem chain3SavedRegs_c3mk_split (sp0 : BitVec 64) (s0 : State) :
    chain3SavedRegs sp0 s0 =
      memRegion (sp0 - 0xe8#64) 104 ∗
        (memRegion (sp0 - 0xf0#64) 8 ∗ memRegion (sp0 - 0x80#64) 48 ∗
          ((sp0 - 0x50#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((sp0 - 0x48#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((sp0 - 0x40#64) ↦₆₄ s0.readReg64 .x25) ∗
          memRegion (sp0 - 0x38#64) 8 ∗
          ((sp0 - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((sp0 - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((sp0 - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((sp0 - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((sp0 - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((sp0 - 0x8#64) ↦₆₄ s0.readReg64 .x19)) := by
  have s1 := ProofLib.memRegion_split (sp0 - 0xf0#64) 8 152 (by decide)
  have s2 := ProofLib.memRegion_split (sp0 - 0xe8#64) 104 48 (by decide)
  have e1 : (sp0 - 0xf0#64) + BitVec.ofNat 64 8 = sp0 - 0xe8#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have e2 : (sp0 - 0xe8#64) + BitVec.ofNat 64 104 = sp0 - 0x80#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  rw [show (8 : Nat) + 152 = 160 by decide, e1] at s1
  rw [show (104 : Nat) + 48 = 152 by decide, e2] at s2
  unfold chain3SavedRegs
  rw [s1, s2]
  ac_rfl

/-! ## 2. Assembly -/

set_option maxHeartbeats 400000 in
/-- Assembles `Chain3MessageKeysStmtExt A` from the four tag-4 sub-step statements. -/
theorem chain3MessageKeys_ok_of_ext {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hHead : Chain3MkHeadStmtExt A img ext) (hCnt : Chain3MkCntStmtExt A img ext)
    (hSeed : Chain3MkSeedStmtExt A img ext) (hPush : Chain3MkPushStmtExt A img ext) :
    Chain3MessageKeysStmtExt A img ext := by
  intro hC x R s0 k s hk htag hs
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, hx29, hx19, hx20, hx21,
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
        A.pool ∗ stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗
        RustHeap.vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (x.a + 0x30#64)
          (chainGAfter x.c k).keys ∗
        c3mkChainNoKeys A x.a (chainGAfter x.c k) ∗ (x.ptr ↦ₛ pfx) ∗
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
  refine segStepG_of_sepWPp (ret := chain3PCAtW img ext 0xa8#64) hmem' ?_
  refine SepWPp.focus_pre
    (hHead hC x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length) s0.sp
      (pbVarint 1 mk.counter.toNat ++ pbBytes 5 mk.seed) rest x.tail x R s0 s _ _ _
      hmk_lt htail_le hlen_a hpc hrun hsp halign hF hsym htr hx19 hx21 hx22 hx23 ?_)
  intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hx25_1 hregs1
  rw [List.append_assoc (pbVarint 1 mk.counter.toNat) (pbBytes 5 mk.seed) rest]
  refine SepWPp.focus_pre
    (hCnt hC x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length + 2#64) s0.sp mk.counter
      (pbBytes 5 mk.seed) rest x R s0 s1 _ _ _
      hlen_b hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 (hregs1.1.trans hx19) hx25_1 ?_)
  intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hx25_2 hregs2
  refine SepWPp.focus_pre
    (hSeed hC x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
        BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length) s0.sp mk.seed rest x R s0 s2 _ _ _
      hk_lt hlen_c hpc2 hrun2 hsp2 halign hF2 hsym2 htr2 (hregs2.1.trans (hregs1.1.trans hx19))
      (hregs2.2.2.2.1.trans (hregs1.2.2.2.1.trans hx22)) hx25_2 ?_)
  intro s3 hpc3 hrun3 hsp3 hF3 hsym3 htr3 hx25_3 hregs3
  have hregs13 : Chain3MkRegs s s3 := (hregs1.trans hregs2).trans hregs3
  apply SepWPp.fold (Entails.of_eq (@c3mk_prostMsgKeyAt_fold A s0.sp mk)) (by sep_focus)
  refine SepWPp.focus_pre
    (hPush hC x.a x.bufRef x.slot
      (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
        BitVec.ofNat 64 (pbVarint 1 mk.counter.toNat).length +
        BitVec.ofNat 64 (pbBytes 5 mk.seed).length) s0.sp (chainGAfter x.c k).keys mk rest
      x R s0 s3 _ _ _
      hbound hpc3 hrun3 hsp3 halign hF3 hsym3 htr3 (hregs13.1.trans hx19)
      (hregs13.2.1.trans hx20) (hregs13.2.2.2.2.2.1.trans hx24) hx25_3 ?_)
  intro s4 hpc4 hrun4 hsp4 hF4 hsym4 htr4 hregs4
  have hregs : Chain3MkRegs s s4 := hregs13.trans hregs4
  refine SepWPp.done hpc4 hrun4 ?_
  intro hmem4
  have hal4 : s4.spAligned = true := by
    simp only [State.spAligned, hsp4, ← hsp]
    exact hal
  refine ⟨hpc4, hrun4, htr4, hregs.2.2.2.2.2.2.2.2.2.2.trans hvregs, hsym4, hF4, hsp4, hal4,
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

theorem chain3MessageKeys_ok_of (img : Obj.Image) (ext : String → Option (State → State))
    (hHead : Chain3MkHeadStmt img ext) (hCnt : Chain3MkCntStmt img ext)
    (hSeed : Chain3MkSeedStmt img ext) (hPush : Chain3MkPushStmt img ext) :
    Chain3MessageKeysStmt img ext := by
  rw [← Chain3MkHeadStmtExt_A0] at hHead
  rw [← Chain3MkCntStmtExt_A0] at hCnt
  rw [← Chain3MkSeedStmtExt_A0] at hSeed
  rw [← Chain3MkPushStmtExt_A0] at hPush
  rw [← Chain3MessageKeysStmtExt_A0]
  exact chain3MessageKeys_ok_of_ext img ext hHead hCnt hSeed hPush

/-- Tag-4 (`message_keys`) slice (`+0x0a8 → +0x0a8`) of `message::merge<Chain> [local#5]` for arbitrary `A : RustAlloc`. -/
theorem chain3MessageKeys_ok_ext {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) :
    Chain3MessageKeysStmtExt A img ext :=
  chain3MessageKeys_ok_of_ext img ext (chain3MkHead_ok_ext img ext) (chain3MkCnt_ok_ext img ext)
    (chain3MkSeed_ok_ext img ext) (chain3MkPush_ok_ext img ext)

theorem chain3MessageKeys_ok (img : Obj.Image) (ext : String → Option (State → State)) :
    Chain3MessageKeysStmt img ext := by
  rw [← Chain3MessageKeysStmtExt_A0]
  exact chain3MessageKeys_ok_ext img ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
