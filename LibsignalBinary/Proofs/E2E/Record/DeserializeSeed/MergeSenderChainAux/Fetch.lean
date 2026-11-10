/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
import LibsignalBinary.Proofs.Placed.BridgeReloc
import ProofLib.SepLogic.WPp

/-!
# Instruction Fetch, Jump Table, and Layout Helpers for Seed `merge_field` Tag `6`

Provides instruction-fetch automation, `.rodata` jump-table lemmas (index `5` for tag `6`), stack
splitting, and `prostSSAt` `sender_chain` (`SS + 0x90`) focus lemmas for
`SessionStructure::merge_field` (`0x581c`, block `15`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree mf6 [(ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 60), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 264) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 328), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1880) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1904)]

elab "mf6_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `CryptoVerification.E2E.Record.DeserializeSeed
      s!"mf6_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

end Fetch

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record

/-! ## Callee Offset Resolution -/

theorem chainMerge_fnAddr_eq_senderChain (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) =
      (tripleRatchetProgAt b C ctl abs).fnAddr chainMergeName := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  have h2 := (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, mergeFieldName, chainMergeName, h1, h2]
  rw [BitVec.add_assoc]
  rfl

/-! ## `.rodata` Jump Table (`0x4901c`, Index `5` for Tag `6`) -/

def jumpTable_senderChain : List (BitVec 8) :=
  [0x00#8, 0x82#8, 0x77#8, 0x5f#8, 0x19#8, 0x32#8, 0x8d#8, 0x6d#8,
   0xb5#8, 0xd6#8, 0xcb#8, 0x6d#8, 0x0b#8, 0x4c#8, 0x24#8]

theorem rodata_0x4601c_eq_senderChain :
    (libsignalSessionImage.data.drop (num% (ls_bytes% "0082775f19328d6db5d6cb6d") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 15 = jumpTable_senderChain := by
  rfl_kernel

theorem rodata_0x4601c_mem_senderChain :
    (num% (ls_bytes% "0082775f19328d6db5d6cb6d"), 15) ∈ libsignalSessionImage.roData :=
  List.mem_of_elem_eq_true (by rfl_kernel)

theorem rodata_jumpTable_intro_senderChain {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) ↦ᵣ jumpTable_senderChain) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_bytes% "0082775f19328d6db5d6cb6d")) (secLen := 15) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl rodata_0x4601c_mem_senderChain (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x4601c_eq_senderChain] at h

theorem jumpTable_byte5_split_senderChain (base : BitVec 64) :
    ((base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) ↦ᵣ jumpTable_senderChain) =
      ((base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) ↦ᵣ jumpTable_senderChain.take 5) ∗
        (((base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 5)) ↦₈ᵣ 0x32#8) ∗
         ((base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 6)) ↦ᵣ jumpTable_senderChain.drop 6)) := by
  have heq : jumpTable_senderChain = jumpTable_senderChain.take 5 ++ (0x32#8 :: jumpTable_senderChain.drop 6) := rfl
  have hlen : (jumpTable_senderChain.take 5).length = 5 := rfl
  have h1 : (base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) + BitVec.ofNat 64 5 = base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 5) := by
    rw [BitVec.add_assoc]; rfl
  have h2 : (base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 5)) + 1#64 = base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 6) := by
    rw [BitVec.add_assoc]; rfl
  conv_lhs => rw [heq]
  rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen, h1, h2]

theorem rodata_byte5_intro_senderChain {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 5)) ↦₈ᵣ 0x32#8) ∗ P := by
  have hm := rodata_jumpTable_intro_senderChain himg hro hP
  rw [jumpTable_byte5_split_senderChain img.base, sepConj_assoc] at hm
  have hm1 := Satisfies.of_sep_right hm
  rw [sepConj_comm (((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 5)) ↦₈ᵣ 0x32#8)) _, sepConj_assoc] at hm1
  exact Satisfies.of_sep_right hm1

theorem sepWPp_intro_rodata_byte5_senderChain {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWPp prog ret s (((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 5)) ↦₈ᵣ 0x32#8) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact rodata_byte5_intro_senderChain himg hro hm

theorem adrp_0x46000_eq_senderChain {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) :
    (entry + bv% (40) &&& bv% (2 ^ 64 - 4096)) = base + 20480#64 := by
  subst he
  have hadd : base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") + 40#64 = base + 22596#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [hadd, adrp_page_of_aligned hb]
  rfl

/-! ## Stack Frame Decomposition -/

/-- The saved register words and untouched cell at `[sp0 - 80#64 .. sp0)` after the prologue. -/
def savedRegs_senderChain (sp0 w56 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 56#64) ↦₆₄ w56) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_mergeFieldStack_split_senderChain (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStack =
      stackAt (sp0 - 80#64) 16304 ∗
        (∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64,
         ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64,
         ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
  have heq : mergeFieldStack = 16304 + 8 * 10 := rfl
  rw [heq, LibsignalTripleRatchet.stackAt_split_cells sp0 16304 10 (by decide)]
  simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, sepExists_sepConj_right]

theorem stackAt_16304_to_chainMerge_senderChain (sp0 : BitVec 64) :
    stackAt (sp0 - 80#64) 16304 =
      memRegion (sp0 - 16384#64) 3856 ∗
        memRegion (sp0 - 240#64) 160 ∗
        stackAt (sp0 - 240#64) chainMergeStack := by
  change memRegion ((sp0 - 80#64) - 16304#64) 16304 =
    memRegion (sp0 - 16384#64) 3856 ∗
      memRegion (sp0 - 240#64) 160 ∗
      memRegion ((sp0 - 240#64) - 12288#64) 12288
  have ha1 : (sp0 - 80#64) - 16304#64 = sp0 - 16384#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ha2 : (sp0 - 16384#64) + 3856#64 = (sp0 - 240#64) - 12288#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ha3 : ((sp0 - 240#64) - 12288#64) + 12288#64 = sp0 - 240#64 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit1 := memRegion_split (sp0 - 16384#64) 3856 12448 (by decide)
  rw [show (3856 : Nat) + 12448 = 16304 from rfl,
      show BitVec.ofNat 64 3856 = 3856#64 from rfl, ha2] at hsplit1
  have hsplit2 := memRegion_split ((sp0 - 240#64) - 12288#64) 12288 160 (by decide)
  rw [show (12288 : Nat) + 160 = 12448 from rfl,
      show BitVec.ofNat 64 12288 = 12288#64 from rfl, ha3] at hsplit2
  rw [ha1, hsplit1, hsplit2]
  ac_rfl

theorem sp_sub_240_aligned_senderChain {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 240#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

/-! ## `prostSSAt` `sender_chain` Layout Helpers -/

/-- All fields of `prostSSAt A ss v` except `sender` at `ss + 0x90`. -/
def prostSSRest_senderChain (A : RustAlloc) (ss : BitVec 64) (v : SSV) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ 0#32) ∗ ((ss + 0x150#64) ↦₆₄ 0#64)

theorem prostSSAt_sender_none_eq_senderChain (A : RustAlloc) (ss : BitVec 64) (v : SSV)
    (hnone : v.sender = none) :
    prostSSAt A ss v =
      ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96 ∗ prostSSRest_senderChain A ss v := by
  unfold prostSSAt prostSSRest_senderChain
  rw [hnone]
  dsimp only
  ac_rfl

theorem prostSSAt_sender_some_eq_senderChain (A : RustAlloc) (ss : BitVec 64) (v : SSV) (c : ChainV) :
    prostSSAt A ss (v.apply (.sender c)) =
      prostChainAt A (ss + 0x90#64) c ∗ prostSSRest_senderChain A ss v := by
  rcases v with ⟨ver, lik, rik, root, recv, sender, pending⟩
  unfold prostSSAt prostSSRest_senderChain SSV.apply
  dsimp only
  ac_rfl

theorem memRegion96_sender_split_senderChain (ss : BitVec 64) :
    memRegion (ss + 0x98#64) 96 =
      (∃∗ u1 : BitVec 64, (ss + 152#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (ss + 160#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (ss + 168#64) ↦₆₄ u3) ∗
      (∃∗ u4 : BitVec 64, (ss + 176#64) ↦₆₄ u4) ∗
      (∃∗ u5 : BitVec 64, (ss + 184#64) ↦₆₄ u5) ∗
      (∃∗ u6 : BitVec 64, (ss + 192#64) ↦₆₄ u6) ∗
      (∃∗ u7 : BitVec 64, (ss + 200#64) ↦₆₄ u7) ∗
      (∃∗ u8 : BitVec 64, (ss + 208#64) ↦₆₄ u8) ∗
      (∃∗ u9 : BitVec 64, (ss + 216#64) ↦₆₄ u9) ∗
      memRegion (ss + 224#64) 24 := by
  have h1 : memRegion (ss + 152#64) 96 = memRegion (ss + 152#64) 8 ∗ memRegion (ss + 160#64) 88 := by
    have h := memRegion_split (ss + 152#64) 8 88 (by decide)
    rw [BitVec.add_assoc] at h; exact h
  have h2 : memRegion (ss + 160#64) 88 = memRegion (ss + 160#64) 8 ∗ memRegion (ss + 168#64) 80 := by
    have h := memRegion_split (ss + 160#64) 8 80 (by decide)
    rw [BitVec.add_assoc] at h; exact h
  have h3 : memRegion (ss + 168#64) 80 = memRegion (ss + 168#64) 8 ∗ memRegion (ss + 176#64) 72 := by
    have h := memRegion_split (ss + 168#64) 8 72 (by decide)
    rw [BitVec.add_assoc] at h; exact h
  have h4 : memRegion (ss + 176#64) 72 = memRegion (ss + 176#64) 8 ∗ memRegion (ss + 184#64) 64 := by
    have h := memRegion_split (ss + 176#64) 8 64 (by decide)
    rw [BitVec.add_assoc] at h; exact h
  have h5 : memRegion (ss + 184#64) 64 = memRegion (ss + 184#64) 8 ∗ memRegion (ss + 192#64) 56 := by
    have h := memRegion_split (ss + 184#64) 8 56 (by decide)
    rw [BitVec.add_assoc] at h; exact h
  have h6 : memRegion (ss + 192#64) 56 = memRegion (ss + 192#64) 8 ∗ memRegion (ss + 200#64) 48 := by
    have h := memRegion_split (ss + 192#64) 8 48 (by decide)
    rw [BitVec.add_assoc] at h; exact h
  have h7 : memRegion (ss + 200#64) 48 = memRegion (ss + 200#64) 8 ∗ memRegion (ss + 208#64) 40 := by
    have h := memRegion_split (ss + 200#64) 8 40 (by decide)
    rw [BitVec.add_assoc] at h; exact h
  have h8 : memRegion (ss + 208#64) 40 = memRegion (ss + 208#64) 8 ∗ memRegion (ss + 216#64) 32 := by
    have h := memRegion_split (ss + 208#64) 8 32 (by decide)
    rw [BitVec.add_assoc] at h; exact h
  have h9 : memRegion (ss + 216#64) 32 = memRegion (ss + 216#64) 8 ∗ memRegion (ss + 224#64) 24 := by
    have h := memRegion_split (ss + 216#64) 8 24 (by decide)
    rw [BitVec.add_assoc] at h; exact h
  change memRegion (ss + 152#64) 96 = _
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  simp only [ProofLib.memRegion_eight]

theorem empty_vecU8_entails_senderChain (A : RustAlloc) (v a8 a16 : BitVec 64)
    (h8 : v + 8#64 = a8) (h16 : v + 16#64 = a16) :
    (v ↦₆₄ 0#64) ∗ (a8 ↦₆₄ 1#64) ∗ (a16 ↦₆₄ 0#64) ⊢ vecU8 A v [] := by
  unfold vecU8
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  unfold vecU8At vecHeader
  subst h8 h16
  have hp : (⌜([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem empty_vecOf_unit_entails_senderChain (A : RustAlloc) (v a8 a16 : BitVec 64)
    (h8 : v + 8#64 = a8) (h16 : v + 16#64 = a16) :
    (v ↦₆₄ 0#64) ∗ (a8 ↦₆₄ 8#64) ∗ (a16 ↦₆₄ 0#64) ⊢
      vecOf A 104 8 (fun (_ : Unit) _ => emp) v [] := by
  unfold vecOf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
  unfold vecAt vecHeader vecBuf
  subst h8 h16
  have hp : (⌜([] : List Unit).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem default_cells_entail_prostChainAt_senderChain (A : RustAlloc) (ss : BitVec 64) :
    ((ss + 144#64) ↦₆₄ 0#64) ∗ ((ss + 152#64) ↦₆₄ 1#64) ∗ ((ss + 160#64) ↦₆₄ 0#64) ∗
    ((ss + 168#64) ↦₆₄ 0#64) ∗ ((ss + 176#64) ↦₆₄ 1#64) ∗ ((ss + 184#64) ↦₆₄ 0#64) ∗
    ((ss + 192#64) ↦₆₄ 0#64) ∗ ((ss + 200#64) ↦₆₄ 8#64) ∗ ((ss + 208#64) ↦₆₄ 0#64) ∗
    ((ss + 216#64) ↦₆₄ noneCap) ∗ memRegion (ss + 224#64) 24 ⊢
      prostChainAt A (ss + 0x90#64) ⟨[], [], none⟩ := by
  unfold prostChainAt
  dsimp only
  have hv1 := empty_vecU8_entails_senderChain A (ss + 144#64) (ss + 152#64) (ss + 160#64)
    (by rw [BitVec.add_assoc]; rfl) (by rw [BitVec.add_assoc]; rfl)
  have hv2 := empty_vecU8_entails_senderChain A (ss + 144#64 + 0x18#64) (ss + 176#64) (ss + 184#64)
    (by simp only [BitVec.add_assoc]; rfl) (by simp only [BitVec.add_assoc]; rfl)
  have hv3 := empty_vecOf_unit_entails_senderChain A (ss + 144#64 + 0x30#64) (ss + 200#64) (ss + 208#64)
    (by simp only [BitVec.add_assoc]; rfl) (by simp only [BitVec.add_assoc]; rfl)
  have ha2 : ss + 144#64 + 0x18#64 = ss + 168#64 := by rw [BitVec.add_assoc]; rfl
  have ha3 : ss + 144#64 + 0x30#64 = ss + 192#64 := by rw [BitVec.add_assoc]; rfl
  have ha4 : ss + 0x90#64 + 0x48#64 = ss + 216#64 := by rw [BitVec.add_assoc]; rfl
  have ha5 : ss + 0x90#64 + 0x50#64 = ss + 224#64 := by rw [BitVec.add_assoc]; rfl
  rw [ha2] at hv2
  rw [ha3] at hv3
  rw [ha2, ha3, ha4, ha5]
  refine Entails.trans ?_
    (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono hv3 (Entails.refl _))))
  exact Entails.of_eq (by ac_rfl)

/-! ## Relocatable `[LibsignalPlacement]` Callee and `.rodata` Helpers -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem chainMerge_placed_sub_mergeField [LibsignalPlacement] {α : Type} {spec : Spec α}
    {H : String → Option (State → State)}
    (h : subroutine_ok (lsProg_11 H) (blkPl_11).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (lsProg_15 H) (lsmpl.base 11)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec) :=
  ls_call_ro_of_block (callerProg := lsProg_15 H) h

theorem chainMerge_placed_ok_sub_senderChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h : ChainMergeSeedPlacedOk H) :
    subroutine_ok (lsProg_15 H) (lsmpl.base 11) chainMergeSeedPlacedSpec :=
  chainMerge_placed_sub_mergeField h

theorem rodata_jumpTable_placed_intro_senderChain [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (lsmpl.ρ mergeFieldRodataSym ↦ᵣ jumpTable_senderChain) ∗ P :=
  lsro_slice_intro hro (by lsro_addr) (by decide +kernel) hP

theorem rodata_byte5_placed_intro_senderChain [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 5#64) ↦₈ᵣ 0x32#8) ∗ P :=
  lsro8_intro hro (by lsro_addr) (by decide +kernel) hP

theorem sepWP_intro_rodata_byte5_placed_senderChain [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsmpl.ρ mergeFieldRodataSym + 5#64) ↦₈ᵣ 0x32#8) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (rodata_byte5_placed_intro_senderChain hcrl.2 hm)

theorem sepWPp_intro_rodata_byte5_placed_senderChain [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s (((lsmpl.ρ mergeFieldRodataSym + 5#64) ↦₈ᵣ 0x32#8) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact rodata_byte5_placed_intro_senderChain hcrl.2 hm

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
