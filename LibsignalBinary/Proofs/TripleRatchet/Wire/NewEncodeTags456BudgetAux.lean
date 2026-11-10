/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123Budget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded `<SignalMessage>::new` Segment 2b Helpers & Tags 4, 6

`UuidParser`-generic pure and separation-logic bridges for fields 4–6, state-indexed no-panic
sequencing (`seq_noPanic_state_placed`), and relocatable `[LibsignalPlacement]` budget-threaded
segment lemmas (`0` allocations) for encoding tag 4 (`+0x278 → +0x2e0`) and tag 6 (`+0x378 → +0x3dc`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456BudgetAux

open Arm64 ProofLib SepProp CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl lsρ
   lsMemcpySym subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  encodedLenSpec encodeVarintSpec encodeVarintSpecX
open CryptoVerification.LibsignalTripleRatchet
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (EncodeVarintEnv encodeVarintEvents_of_spare encodeVarintSpec encodeVarintSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux
  (call_noPanic_placed stackAt_split_ge)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
  (framelessMemcpyBudgetSpec new_memcpy_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123BudgetAux
  (addresses_length_parse bind_state call_noPanic_extern
   encodeBytesField_4_protoMsg_parse encodeBytesField_5_protoMsg_empty_parse
   encodeBytesField_5_protoMsg_nonempty_parse encodeBytesField_6_protoMsg_none_parse
   encodeBytesField_6_protoMsg_some_parse encodeVarintSpecWithStack
   encodeVarintSpecWithStack_post_eq encodeVarintSpecWithStack_pre_eq
   encodeVarintSpecX_eq_withStack encodeVarintSpec_eq_withStack
   encode_protoMsg_length_bounds_parse serPrefix6_length_parse serPrefix_lengths_le_parse)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
theorem bv_ult_zero_local (v : BitVec 64) : v.ult 0#64 = false := by
  simp [BitVec.ult]

/-- Sequence a panic-free `SepWPp` segment (`Qp = fun _ _ => False`) whose spatial postcondition
depends on the intermediate machine state `sm` (carrying `A.pool lim st sm`) into an arbitrary
`SepWPp` continuation while preserving `LibsignalCodeLoaded`. -/
theorem seq_noPanic_state_placed [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (fun _ _ => False))
    (hfocus : P = P1 ∗ F)
    (h2 : ∀ sm, LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hfoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm (hcl.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim hfalse
  · exact (not_satisfies_false_sepConj hfoom).elim

/-! ## `UuidParser`-generic separation-logic and pure bridges for tags 4, 5, 6 -/

theorem wireSignalMessageAt_expose_ct_parse (parse : UuidParser) (A : RustAlloc)
    (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr base : BitVec 64)
    (hct_ne : x.ciphertext ≠ []) (hct_le : x.ciphertext.length ≤ 2 ^ 32) :
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
      base (x.protoMsg parse) =
    (ctCopyPtr ↦ₛ x.ciphertext) ∗
    (optVecU8At A ⟨33#64, rkPtr⟩ base (some x.senderRatchetKey.serialize) ∗
     ((base + 24#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
     ((base + 24#64 + 8#64) ↦₆₄ ctCopyPtr) ∗
     ((base + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
     ⌜ctCopyPtr ≠ 0#64 ∧ x.ciphertext.length < 2 ^ 63⌝ ∗
     A.live ctCopyPtr x.ciphertext.length 1 ∗
     optVecU8At A ⟨pqCap, pqCopyPtr⟩ (base + 48#64)
       (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
     optVecU8At A ⟨addrCap, addrPtr⟩ (base + 72#64) (x.addresses parse) ∗
     optU32At (base + 96#64) (some x.counter) ∗
     optU32At (base + 104#64) (some x.previousCounter)) := by
  unfold wireSignalMessageAt SignalMessageNewGhost.mkPins SignalMessageNewGhost.protoMsg
  dsimp only
  rw [optVecU8At_ct_nonempty_eq A (base + 24#64) ctCopyPtr x.ciphertext hct_ne (by omega)]
  apply eq_of_sep_focus
  sep_focus

theorem wireSignalMessageAt_expose_pq_parse (parse : UuidParser) (A : RustAlloc)
    (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCopyPtr addrCap addrPtr base : BitVec 64)
    (hpq_ne : x.pqRatchet ≠ [])
    (hpq_pin : PqPinOk (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr x.pqRatchet) :
    wireSignalMessageAt A
      (x.mkPins rkPtr ctCopyPtr (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr addrCap addrPtr)
      base (x.protoMsg parse) =
    (pqCopyPtr ↦ₛ x.pqRatchet) ∗
    (optVecU8At A ⟨33#64, rkPtr⟩ base (some x.senderRatchetKey.serialize) ∗
     optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
       (base + 24#64) (some x.ciphertext) ∗
     ((base + 48#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
     ((base + 48#64 + 8#64) ↦₆₄ pqCopyPtr) ∗
     ((base + 48#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
     ⌜pqCopyPtr ≠ 0#64 ∧ x.pqRatchet.length < 2 ^ 63⌝ ∗
     A.live pqCopyPtr x.pqRatchet.length 1 ∗
     optVecU8At A ⟨addrCap, addrPtr⟩ (base + 72#64) (x.addresses parse) ∗
     optU32At (base + 96#64) (some x.counter) ∗
     optU32At (base + 104#64) (some x.previousCounter)) := by
  unfold wireSignalMessageAt SignalMessageNewGhost.mkPins SignalMessageNewGhost.protoMsg
  dsimp only
  rw [optVecU8At_pq_nonempty_eq A (base + 48#64)
        (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr x.pqRatchet hpq_ne hpq_pin]
  apply eq_of_sep_focus
  sep_focus

theorem wireSignalMessageAt_expose_addrCap_parse (parse : UuidParser) (A : RustAlloc)
    (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr sp0 : BitVec 64)
    (hcap : x.addresses parse = none → addrCap = noneCap) :
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
      (sp0 - 288#64) (x.protoMsg parse) =
    ((sp0 - 216#64) ↦₆₄ addrCap) ∗
    (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
     optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
       ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
     optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
       (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
     optVecU8RestAt A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses parse) ∗
     optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
     optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) := by
  have h216 : (sp0 - 288#64) + 0x48#64 = sp0 - 216#64 := bv_sub_add_lit sp0 288 72
  unfold wireSignalMessageAt SignalMessageNewGhost.mkPins SignalMessageNewGhost.protoMsg
  dsimp only
  rw [optVecU8At_expose_cap_rest A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64)
        (x.addresses parse) hcap]
  dsimp only
  rw [h216]
  sep_focus

theorem wireSignalMessageAt_expose_addr_some_parse (parse : UuidParser) (A : RustAlloc)
    (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCap pqCopyPtr addrPtr sp0 : BitVec 64)
    (ad : List (BitVec 8)) (had : x.addresses parse = some ad) (had_len : ad.length = 36) :
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
      (sp0 - 288#64) (x.protoMsg parse) =
    ((sp0 - 216#64) ↦₆₄ 36#64) ∗
    ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
    ((sp0 - 200#64) ↦₆₄ 36#64) ∗
    (addrPtr ↦ₛ ad) ∗
    (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
     optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
       ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
     optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
       (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
     (⌜addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
      A.live addrPtr ad.length 1) ∗
     optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
     optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) := by
  unfold wireSignalMessageAt SignalMessageNewGhost.mkPins SignalMessageNewGhost.protoMsg
  dsimp only
  rw [optVecU8At_addr_some_eq A sp0 addrPtr (x.addresses parse) ad had had_len]
  apply eq_of_sep_focus
  sep_focus

theorem serPrefix5_of_pq_empty_parse (parse : UuidParser) (x : SignalMessageNewGhost)
    (h : x.pqRatchet = []) :
    x.serPrefix5 parse = x.serPrefix4 parse := by
  simp [SignalMessageNewGhost.serPrefix5, encodeBytesField_5_protoMsg_empty_parse parse x h]

theorem serPrefix6_of_addresses_none_parse (parse : UuidParser) (x : SignalMessageNewGhost)
    (h : x.addresses parse = none) :
    x.serPrefix6 parse = x.serPrefix5 parse := by
  simp [SignalMessageNewGhost.serPrefix6, encodeBytesField_6_protoMsg_none_parse parse x h]

theorem tag4_pure_facts_parse (parse : UuidParser) (x : SignalMessageNewGhost)
    (encLen : Nat)
    (henc_eq : encLen = (encode (x.protoMsg parse)).length)
    (hlo : 35 ≤ encLen) (hhi : encLen < 2 ^ 34)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32) :
    (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 ∧
    (BitVec.ofNat 64 (encLen + 9)).toNat < 2 ^ 63 ∧
    (x.serPrefix3 parse).length < (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (BitVec.ofNat 64 (encLen + 9) == BitVec.ofNat 64 (x.serPrefix3 parse).length) = false ∧
    (x.serPrefix3 parse ++ [0x22#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix3 parse ++ [0x22#8]).length +
      (encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    ((x.serPrefix3 parse ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 x.ciphertext.length)) ++
      x.ciphertext = x.serPrefix4 parse ∧
    (BitVec.ofNat 64 (encLen + 9) -
      BitVec.ofNat 64
        ((x.serPrefix3 parse ++ [0x22#8]) ++
          encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length).ult
      (BitVec.ofNat 64 x.ciphertext.length) = false ∧
    ((x.serPrefix3 parse ++ [0x22#8]) ++
      encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length + x.ciphertext.length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    BitVec.ofNat 64
      ((x.serPrefix3 parse ++ [0x22#8]) ++
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
      BitVec.ofNat 64 x.ciphertext.length =
      BitVec.ofNat 64 (x.serPrefix4 parse).length := by
  have htot : (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ⟨h0_len, h1_len, h12_le, h23_le, h34_le, h45_le, h56_le⟩ := serPrefix_lengths_le_parse parse x
  have h6_len : (x.serPrefix6 parse).length = 1 + encLen := by
    rw [henc_eq, serPrefix6_length_parse]
  have hp4_eq : ((x.serPrefix3 parse ++ [0x22#8]) ++
      encodeVarint (BitVec.ofNat 64 x.ciphertext.length)) ++ x.ciphertext =
      x.serPrefix4 parse := by
    simp [SignalMessageNewGhost.serPrefix4, encodeBytesField_4_protoMsg_parse, List.append_assoc]
  have hlen4 : ((x.serPrefix3 parse ++ [0x22#8]) ++
      encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length + x.ciphertext.length =
      (x.serPrefix4 parse).length := by
    rw [← List.length_append, hp4_eq]
  have hp3_toNat : (BitVec.ofNat 64 (x.serPrefix3 parse).length).toNat =
      (x.serPrefix3 parse).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hp3a_toNat : (BitVec.ofNat 64 ((x.serPrefix3 parse ++ [0x22#8]) ++
      encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length).toNat =
      ((x.serPrefix3 parse ++ [0x22#8]) ++
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨htot, by omega, by omega, ?_, ?_, ?_, hp4_eq, ?_, by omega, ?_⟩
  · apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  · rw [List.length_append, List.length_singleton]; omega
  · rw [List.length_append] at hlen4; omega
  · exact bv_sub_ult_false_of_add_lt htot hp3a_toNat hct_toNat (by omega)
  · rw [← BitVec.ofNat_add, hlen4]

theorem tag5_pure_facts_parse (parse : UuidParser) (x : SignalMessageNewGhost)
    (encLen : Nat)
    (henc_eq : encLen = (encode (x.protoMsg parse)).length)
    (hlo : 35 ≤ encLen) (hhi : encLen < 2 ^ 34)
    (hpq_ne : x.pqRatchet ≠ [])
    (hpq_lt : x.pqRatchet.length < 2 ^ 32) :
    (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 ∧
    (BitVec.ofNat 64 (encLen + 9)).toNat < 2 ^ 63 ∧
    (BitVec.ofNat 64 x.pqRatchet.length + 1#64 == 0#64) = false ∧
    (x.serPrefix4 parse).length < (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (BitVec.ofNat 64 (encLen + 9) == BitVec.ofNat 64 (x.serPrefix4 parse).length) = false ∧
    (x.serPrefix4 parse ++ [0x2a#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix4 parse ++ [0x2a#8]).length +
      (encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    ((x.serPrefix4 parse ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)) ++
      x.pqRatchet = x.serPrefix5 parse ∧
    (BitVec.ofNat 64 (encLen + 9) -
      BitVec.ofNat 64
        ((x.serPrefix4 parse ++ [0x2a#8]) ++
          encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length).ult
      (BitVec.ofNat 64 x.pqRatchet.length) = false ∧
    (BitVec.ofNat 64 x.pqRatchet.length == 0#64) = false ∧
    ((x.serPrefix4 parse ++ [0x2a#8]) ++
      encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length + x.pqRatchet.length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    BitVec.ofNat 64
      ((x.serPrefix4 parse ++ [0x2a#8]) ++
        encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
      BitVec.ofNat 64 x.pqRatchet.length =
      BitVec.ofNat 64 (x.serPrefix5 parse).length := by
  have htot : (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ⟨h0_len, h1_len, h12_le, h23_le, h34_le, h45_le, h56_le⟩ := serPrefix_lengths_le_parse parse x
  have h6_len : (x.serPrefix6 parse).length = 1 + encLen := by
    rw [henc_eq, serPrefix6_length_parse]
  have hpq_pos : 0 < x.pqRatchet.length := List.length_pos_iff.mpr hpq_ne
  have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hpq_bv_hi : BitVec.ofNat 64 x.pqRatchet.length < 4294967296#64 := by
    rw [BitVec.lt_def, hpq_toNat]; change x.pqRatchet.length < 4294967296; omega
  have hpq_bv_lo : 1#64 ≤ BitVec.ofNat 64 x.pqRatchet.length := by
    rw [BitVec.le_def, hpq_toNat]; change 1 ≤ x.pqRatchet.length; omega
  have hp5_eq : ((x.serPrefix4 parse ++ [0x2a#8]) ++
      encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)) ++ x.pqRatchet =
      x.serPrefix5 parse := by
    simp [SignalMessageNewGhost.serPrefix5, encodeBytesField_5_protoMsg_nonempty_parse parse x hpq_ne,
      List.append_assoc]
  have hlen5 : ((x.serPrefix4 parse ++ [0x2a#8]) ++
      encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length + x.pqRatchet.length =
      (x.serPrefix5 parse).length := by
    rw [← List.length_append, hp5_eq]
  have hp4_toNat : (BitVec.ofNat 64 (x.serPrefix4 parse).length).toNat =
      (x.serPrefix4 parse).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hp4a_toNat : (BitVec.ofNat 64 ((x.serPrefix4 parse ++ [0x2a#8]) ++
      encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length).toNat =
      ((x.serPrefix4 parse ++ [0x2a#8]) ++
        encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨htot, by omega,
    by revert hpq_bv_lo hpq_bv_hi; generalize BitVec.ofNat 64 x.pqRatchet.length = v; intros; bv_kernel,
    by omega, ?_, ?_, ?_, hp5_eq, ?_,
    by revert hpq_bv_lo hpq_bv_hi; generalize BitVec.ofNat 64 x.pqRatchet.length = v; intros; bv_kernel,
    by omega, ?_⟩
  · apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  · rw [List.length_append, List.length_singleton]; omega
  · rw [List.length_append] at hlen5; omega
  · exact bv_sub_ult_false_of_add_lt htot hp4a_toNat hpq_toNat (by omega)
  · rw [← BitVec.ofNat_add, hlen5]

theorem tag6_pure_facts_parse (parse : UuidParser) (x : SignalMessageNewGhost)
    (ad : List (BitVec 8)) (had : x.addresses parse = some ad)
    (encLen : Nat)
    (henc_eq : encLen = (encode (x.protoMsg parse)).length)
    (hlo : 35 ≤ encLen) (hhi : encLen < 2 ^ 34) :
    (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 ∧
    (BitVec.ofNat 64 (encLen + 9)).toNat < 2 ^ 63 ∧
    ad.length = 36 ∧
    ad ≠ [] ∧
    (x.serPrefix5 parse).length < (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (BitVec.ofNat 64 (encLen + 9) == BitVec.ofNat 64 (x.serPrefix5 parse).length) = false ∧
    (x.serPrefix5 parse ++ [0x32#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix5 parse ++ [0x32#8]).length + (encodeVarint 36#64).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    ((x.serPrefix5 parse ++ [0x32#8]) ++ encodeVarint 36#64) ++ ad = x.serPrefix6 parse ∧
    (BitVec.ofNat 64 (encLen + 9) -
      BitVec.ofNat 64 ((x.serPrefix5 parse ++ [0x32#8]) ++ encodeVarint 36#64).length).ult
      36#64 = false ∧
    ((x.serPrefix5 parse ++ [0x32#8]) ++ encodeVarint 36#64).length + 36 ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    BitVec.ofNat 64 ((x.serPrefix5 parse ++ [0x32#8]) ++ encodeVarint 36#64).length + 36#64 =
      BitVec.ofNat 64 (x.serPrefix6 parse).length := by
  have htot : (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ⟨h0_len, h1_len, h12_le, h23_le, h34_le, h45_le, h56_le⟩ := serPrefix_lengths_le_parse parse x
  have h6_len : (x.serPrefix6 parse).length = 1 + encLen := by
    rw [henc_eq, serPrefix6_length_parse]
  have had_len : ad.length = 36 := addresses_length_parse had
  have had_ne : ad ≠ [] := by intro h; simp [h] at had_len
  have hp6_eq : ((x.serPrefix5 parse ++ [0x32#8]) ++ encodeVarint 36#64) ++ ad =
      x.serPrefix6 parse := by
    simp [SignalMessageNewGhost.serPrefix6, encodeBytesField_6_protoMsg_some_parse parse x had,
      encodeVarint_36, List.append_assoc]
  have hlen6 : ((x.serPrefix5 parse ++ [0x32#8]) ++ encodeVarint 36#64).length + 36 =
      (x.serPrefix6 parse).length := by
    have h := congrArg List.length hp6_eq
    rw [List.length_append, had_len] at h
    exact h
  have hp5_toNat : (BitVec.ofNat 64 (x.serPrefix5 parse).length).toNat =
      (x.serPrefix5 parse).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hp5a_toNat : (BitVec.ofNat 64 ((x.serPrefix5 parse ++ [0x32#8]) ++
      encodeVarint 36#64).length).toNat =
      ((x.serPrefix5 parse ++ [0x32#8]) ++ encodeVarint 36#64).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨htot, by omega, had_len, had_ne, by omega, ?_, ?_, ?_, hp6_eq, ?_, by omega, ?_⟩
  · apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  · rw [List.length_append, List.length_singleton]; omega
  · rw [List.length_append] at hlen6; omega
  · exact bv_sub_ult_false_of_add_lt htot hp5a_toNat (by decide) (by omega)
  · rw [← BitVec.ofNat_add, hlen6]

/-! ## Encoding tag 4 (`ciphertext`, `+0x278 → +0x2e0`, `0` allocations) -/

theorem new_encode_tag4_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {varStack cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : varStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecWithStack A lim varStack)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 736#64)
      s
      (((sp0 - 392#64) ↦₆₄ w392) ∗
       wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix3 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 parse).length ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix4 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
  clear h_mc
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds_parse parse x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, hp3_lt, hcmp4, hvar4_lt, hvar4_fit,
        hp4_eq, hcmp_ct, hp3a_slice_le, hp4_bv_eq⟩ :=
    tag4_pure_facts_parse parse x (encode (x.protoMsg parse)).length rfl
      henc_lo henc_hi hct_le
  simp only [List.append_assoc, List.singleton_append] at hcmp_ct hp3a_slice_le hp4_bv_eq
  have hp4_eq' :
      (x.serPrefix3 parse ++ 0x22#8 ::
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length)) ++ x.ciphertext =
      x.serPrefix4 parse := by
    simpa only [List.append_assoc, List.singleton_append] using hp4_eq
  clear hp4_eq
  rw [serVec_expose_one A.repAlloc sp0
        (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix3 parse).length)
        (serPtr + BitVec.ofNat 64 (x.serPrefix3 parse).length + 1#64)
        (x.serPrefix3 parse) hp3_lt htot_lt hserPtr rfl rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl
  wp_steps_sync_pool (lsmpl.base 10)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  let gx4 : EncodeVarintGhost :=
    ⟨BitVec.ofNat 64 x.ciphertext.length, sp0 - 176#64,
     BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9),
     serPtr, x.serPrefix3 parse ++ [0x22#8]⟩
  refine call_noPanic_placed (x := (gx4, st))
    (F := ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
    hcl0 hVarint (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    rw [stackAt_split_ge hle hbnd (sp0 - 416#64)] at hm
    rw [encodeVarintSpecWithStack_pre_eq A lim varStack gx4 st _ (sp0 - 416#64)
          (by simp only [gx4, wp_norm, arm64_norm])
          (by simp only [gx4, wp_norm, arm64_norm])
          hvar4_lt hvar4_fit
          (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A.repAlloc sp0
          (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix3 parse).length)
          (BitVec.ofNat 64 (x.serPrefix3 parse).length + 1#64)
          (serPtr + BitVec.ofNat 64 (x.serPrefix3 parse).length + 1#64)
          (x.serPrefix3 parse) 0x22#8 hp3_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpecWithStack_post_eq A lim varStack gx4 st _ sf1 (sp0 - 416#64)
        (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs4 => SepWPp.exists_elim fun cap' =>
    SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rw [sepConj_left_comm]
  refine SepWPp.pure_elim fun hevs4 => ?_
  have hevs4_nil : evs4 = [] := by
    rw [hevs4]; exact encodeVarintEvents_of_spare (x := gx4) hvar4_fit
  subst hevs4_nil
  rw [M.stepEvents_nil]
  rcases hno_grow hvar4_fit with ⟨hcap', hptr'⟩
  dsimp only [gx4] at hcap' hptr' ⊢
  subst cap' ptr'
  simp only [List.append_assoc, List.singleton_append]
  by_cases hct_nil : x.ciphertext = []
  · have hct_zero : BitVec.ofNat 64 x.ciphertext.length = 0#64 := by simp [hct_nil]
    have hp4_nil : x.serPrefix3 parse ++ 0x22#8 ::
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length) = x.serPrefix4 parse := by
      simpa only [hct_nil, List.append_nil] using hp4_eq'
    rw [hp4_nil,
        vecU8At_eq_of_pos A.repAlloc (sp0 - 176#64)
          (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
          serPtr (x.serPrefix4 parse) (by omega)]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool ((blkPl_63).base + 736#64)
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, hct_zero,
        hsp1, hsp0_align, h19_1, h20_1, h21_1, h23_1, h24_1, h26_1, h27_1, h28_1, hfp_1,
        htr1, and_self]
    · rw [stackAt_split_ge hle hbnd (sp0 - 416#64)]
      exact entails_of_sep_focus (by sep_focus)
  · have hct_pos : 0 < x.ciphertext.length := List.length_pos_iff.mpr hct_nil
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hct_nz : (BitVec.ofNat 64 x.ciphertext.length == 0#64) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro heq
      have := congrArg BitVec.toNat heq
      rw [hct_toNat, BitVec.toNat_zero] at this
      omega
    rw [serVec_expose_slice A.repAlloc sp0
          (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
          serPtr
          (BitVec.ofNat 64 (x.serPrefix3 parse ++ 0x22#8 ::
            encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length)
          (BitVec.ofNat 64 x.ciphertext.length)
          (serPtr + BitVec.ofNat 64 (x.serPrefix3 parse ++ 0x22#8 ::
            encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
            BitVec.ofNat 64 x.ciphertext.length)
          (x.serPrefix3 parse ++ 0x22#8 :: encodeVarint (BitVec.ofNat 64 x.ciphertext.length))
          x.ciphertext.length
          hp3a_slice_le htot_lt hserPtr hct_pos rfl rfl rfl,
        wireSignalMessageAt_expose_ct_parse parse A.repAlloc x rkPtr ctCopyPtr pqCap pqCopyPtr
          addrCap addrPtr (sp0 - 288#64) hct_nil hct_le]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1])
    refine bind_state ?_
    intro s_mc
    refine call_noPanic_extern
      (x := (serPtr + BitVec.ofNat 64 (x.serPrefix3 parse ++ 0x22#8 ::
              encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length,
             ctCopyPtr, x.ciphertext))
      (F := ((sp0 - 176#64) ↦₆₄
              BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)) ∗
            ((sp0 - 168#64) ↦₆₄ serPtr) ∗
            ((sp0 - 160#64) ↦₆₄
              BitVec.ofNat 64 (x.serPrefix3 parse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length) ∗
            A.repAlloc.live serPtr
              (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)).toNat 1 ∗
            (serPtr ↦ₛ (x.serPrefix3 parse ++ 0x22#8 ::
              encodeVarint (BitVec.ofNat 64 x.ciphertext.length))) ∗
            memRegion
              (serPtr + BitVec.ofNat 64 (x.serPrefix3 parse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
                BitVec.ofNat 64 x.ciphertext.length)
              ((BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)).toNat -
                (x.serPrefix3 parse ++ 0x22#8 ::
                  encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length -
                x.ciphertext.length) ∗
            A.pool lim st s_mc ∗ stackAt (sp0 - 416#64) varStack ∗
            ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            (optVecU8At A.repAlloc ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
             (((sp0 - 288#64) + 0x18#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
             (((sp0 - 288#64) + 0x18#64 + 8#64) ↦₆₄ ctCopyPtr) ∗
             (((sp0 - 288#64) + 0x18#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
             ⌜ctCopyPtr ≠ 0#64 ∧ x.ciphertext.length < 2 ^ 63⌝ ∗
             A.repAlloc.live ctCopyPtr x.ciphertext.length 1 ∗
             optVecU8At A.repAlloc ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
               (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
             optVecU8At A.repAlloc ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64)
               (x.addresses parse) ∗
             optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
             optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
            memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
      hmemcpy (by simp only [s_mc, wp_norm, arm64_norm])
      (by simp only [s_mc, wp_norm, arm64_norm, hrun1])
      (by simp only [s_mc, State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [s_mc, wp_norm, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      dsimp only [s_mc] at hm ⊢
      simp only [framelessMemcpyBudgetSpec, withVmPreserved]
      rw [session2MemcpySpec_pre_eq _ _ _ _
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm, hct_toNat])]
      simp only [sepConj_assoc] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    dsimp only [s_mc] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [wp_norm, arm64_norm,
      hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h26_1, h27_1, h28_1, hfp_1]
      at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm2 => SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
    dsimp only [s_mc] at hvm2 htr2 ⊢
    rw [← A.pool_transport lim st _ sf2 hvm2]
    simp only [wp_norm, arm64_norm, htr1] at htr2
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool ((blkPl_63).base + 736#64)
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm,
        hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h26_2, h27_2, h28_2, hfp_2,
        htr2, and_self]
    · rw [← hp4_bv_eq,
          stackAt_split_ge hle hbnd (sp0 - 416#64),
          ← hp4_eq',
          ← serVec_pack_slice A.repAlloc sp0
              (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
              serPtr
              (BitVec.ofNat 64 (x.serPrefix3 parse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length)
              (BitVec.ofNat 64 x.ciphertext.length)
              (BitVec.ofNat 64 (x.serPrefix3 parse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
                BitVec.ofNat 64 x.ciphertext.length)
              (serPtr + BitVec.ofNat 64 (x.serPrefix3 parse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
                BitVec.ofNat 64 x.ciphertext.length)
              (x.serPrefix3 parse ++ 0x22#8 :: encodeVarint (BitVec.ofNat 64 x.ciphertext.length))
              x.ciphertext
              hp3a_slice_le htot_lt hserPtr hct_nil rfl rfl rfl rfl]
      exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag4_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 736#64)
      s
      (((sp0 - 392#64) ↦₆₄ w392) ∗
       wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix3 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 parse).length ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix4 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_encode_tag4_wpp_placed_at (varStack := encodeVarintStack) (cmStack := computeMacStack)
    (by decide) (by decide) h_mc (by rwa [← encodeVarintSpec_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392 hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag4_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 736#64)
      s
      (((sp0 - 392#64) ↦₆₄ w392) ∗
       wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix3 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 parse).length ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix4 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_encode_tag4_wpp_placed_at (varStack := encodeVarintStackX) (cmStack := computeMacStackX)
    (by decide) (by decide) h_mc (by rwa [← encodeVarintSpecX_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392 hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

/-! ## Encoding tag 6 (`addresses` when `some ad`, `+0x378 → +0x3dc`, `0` allocations) -/

theorem new_encode_tag6_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {varStack cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : varStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecWithStack A lim varStack)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrPtr serPtr : BitVec 64)
    (ad : List (BitVec 8)) (had : x.addresses parse = some ad)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 888#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix5 parse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix5 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 parse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix6 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
  clear h_mc
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds_parse parse x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, had_len, had_ne, hp5_lt, hcmp6, hvar6_lt, hvar6_fit,
        hp6_eq, hcmp_ad, hp5a_slice_le, hp6_bv_eq⟩ :=
    tag6_pure_facts_parse parse x ad had (encode (x.protoMsg parse)).length rfl
      henc_lo henc_hi
  simp only [List.append_assoc, List.singleton_append] at hcmp_ad hp5a_slice_le hp6_bv_eq
  have hp6_eq' : (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64) ++ ad = x.serPrefix6 parse := by
    simpa only [List.append_assoc, List.singleton_append] using hp6_eq
  clear hp6_eq
  rw [serVec_expose_one A.repAlloc sp0
        (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix5 parse).length)
        (serPtr + BitVec.ofNat 64 (x.serPrefix5 parse).length + 1#64)
        (x.serPrefix5 parse) hp5_lt htot_lt hserPtr rfl rfl,
      wireSignalMessageAt_expose_addr_some_parse parse A.repAlloc x rkPtr ctCopyPtr pqCap pqCopyPtr
        addrPtr sp0 ad had had_len]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl
  wp_steps_sync_pool (lsmpl.base 10)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  let gx6 : EncodeVarintGhost :=
    ⟨36#64, sp0 - 176#64,
     BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9),
     serPtr, x.serPrefix5 parse ++ [0x32#8]⟩
  refine call_noPanic_placed (x := (gx6, st))
    (F := ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
          ((sp0 - 200#64) ↦₆₄ 36#64) ∗
          (addrPtr ↦ₛ ad) ∗
          (optVecU8At A.repAlloc ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
           optVecU8At A.repAlloc ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
             ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A.repAlloc ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
             (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           (⌜addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
            A.repAlloc.live addrPtr ad.length 1) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
           optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
    hcl0 hVarint (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    rw [stackAt_split_ge hle hbnd (sp0 - 416#64)] at hm
    rw [encodeVarintSpecWithStack_pre_eq A lim varStack gx6 st _ (sp0 - 416#64)
          (by simp only [gx6, wp_norm, arm64_norm])
          (by simp only [gx6, wp_norm, arm64_norm])
          hvar6_lt hvar6_fit
          (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A.repAlloc sp0
          (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix5 parse).length)
          (BitVec.ofNat 64 (x.serPrefix5 parse).length + 1#64)
          (serPtr + BitVec.ofNat 64 (x.serPrefix5 parse).length + 1#64)
          (x.serPrefix5 parse) 0x32#8 hp5_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpecWithStack_post_eq A lim varStack gx6 st _ sf1 (sp0 - 416#64)
        (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs6 => SepWPp.exists_elim fun cap' =>
    SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rw [sepConj_left_comm]
  refine SepWPp.pure_elim fun hevs6 => ?_
  have hevs6_nil : evs6 = [] := by
    rw [hevs6]; exact encodeVarintEvents_of_spare (x := gx6) hvar6_fit
  subst hevs6_nil
  rw [M.stepEvents_nil]
  rcases hno_grow hvar6_fit with ⟨hcap', hptr'⟩
  dsimp only [gx6] at hcap' hptr' ⊢
  subst cap' ptr'
  simp only [List.append_assoc, List.singleton_append]
  rw [serVec_expose_slice A.repAlloc sp0
        (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
        serPtr
        (BitVec.ofNat 64 (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64).length)
        36#64
        (serPtr + BitVec.ofNat 64 (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64).length +
          36#64)
        (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64)
        36
        hp5a_slice_le htot_lt hserPtr (by decide) rfl rfl rfl]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine bind_state ?_
  intro s_mc
  refine call_noPanic_extern
    (x := (serPtr + BitVec.ofNat 64 (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64).length,
           addrPtr, ad))
    (F := ((sp0 - 176#64) ↦₆₄
            BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄
            BitVec.ofNat 64 (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64).length) ∗
          A.repAlloc.live serPtr
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64)) ∗
          memRegion
            (serPtr + BitVec.ofNat 64 (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64).length +
              36#64)
            ((BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)).toNat -
              (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64).length - 36) ∗
          A.pool lim st s_mc ∗ stackAt (sp0 - 416#64) varStack ∗
          ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
          ((sp0 - 200#64) ↦₆₄ 36#64) ∗
          (optVecU8At A.repAlloc ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
           optVecU8At A.repAlloc ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
             ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A.repAlloc ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
             (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           (⌜addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
            A.repAlloc.live addrPtr ad.length 1) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
           optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
    hmemcpy (by simp only [s_mc, wp_norm, arm64_norm])
    (by simp only [s_mc, wp_norm, arm64_norm, hrun1])
    (by simp only [s_mc, State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [s_mc, wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    dsimp only [s_mc] at hm ⊢
    simp only [framelessMemcpyBudgetSpec, withVmPreserved]
    have h36_toNat : (36#64 : BitVec 64).toNat = 36 := rfl
    rw [session2MemcpySpec_pre_eq _ _ _ _
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, had_len, h36_toNat])]
    simp only [had_len, sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  dsimp only [s_mc] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [wp_norm, arm64_norm,
    hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h27_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc]
  refine SepWPp.pure_elim fun hvm2 => SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
  dsimp only [s_mc] at hvm2 htr2 ⊢
  rw [← A.pool_transport lim st _ sf2 hvm2]
  simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_63).base + 988#64)
  refine SepWP.done
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm,
      hsp2, hsp0_align, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h27_2, hfp_2,
      htr2, and_self]
  · rw [← hp6_bv_eq,
        stackAt_split_ge hle hbnd (sp0 - 416#64),
        ← hp6_eq',
        ← serVec_pack_slice A.repAlloc sp0
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr
            (BitVec.ofNat 64 (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64).length)
            36#64
            (BitVec.ofNat 64 (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64).length +
              36#64)
            (serPtr + BitVec.ofNat 64 (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64).length +
              36#64)
            (x.serPrefix5 parse ++ 0x32#8 :: encodeVarint 36#64)
            ad
            (by rw [had_len]; exact hp5a_slice_le) htot_lt hserPtr had_ne rfl (by rw [had_len]) rfl rfl,
        had_len]
    exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag6_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrPtr serPtr : BitVec 64)
    (ad : List (BitVec 8)) (had : x.addresses parse = some ad)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 888#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix5 parse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix5 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 parse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix6 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_encode_tag6_wpp_placed_at (varStack := encodeVarintStack) (cmStack := computeMacStack)
    (by decide) (by decide) h_mc (by rwa [← encodeVarintSpec_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrPtr serPtr ad had hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx29

theorem new_encode_tag6_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrPtr serPtr : BitVec 64)
    (ad : List (BitVec 8)) (had : x.addresses parse = some ad)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 888#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix5 parse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix5 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 parse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix6 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_encode_tag6_wpp_placed_at (varStack := encodeVarintStackX) (cmStack := computeMacStackX)
    (by decide) (by decide) h_mc (by rwa [← encodeVarintSpecX_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrPtr serPtr ad had hct_le hpq_lt hserPtr
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx29

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456BudgetAux
