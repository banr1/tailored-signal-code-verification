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
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456BudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded `<SignalMessage>::new` Segment 2b (`+0x278 .. +0x3dc`)

Re-exports `NewEncodeTags456BudgetAux` (tags 4 and 6) and proves relocatable `[LibsignalPlacement]`
budget-threaded segment lemmas (`0` allocations) for optional fields 5 (`pq_ratchet`) and 6
(`addresses`) (`+0x2e0 → +0x3dc`) on Block `63`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456Budget

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
  (bind_state encodeVarintSpecWithStack encodeVarintSpecWithStack_post_eq
   encodeVarintSpecWithStack_pre_eq encodeVarintSpecX_eq_withStack
   encodeVarintSpec_eq_withStack encode_protoMsg_length_bounds_parse)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456BudgetAux
  (new_encode_tag4_wpp_placed new_encode_tag4_wpp_placed_at new_encode_tag4_wpp_placed_x
   new_encode_tag6_wpp_placed new_encode_tag6_wpp_placed_at new_encode_tag6_wpp_placed_x
   seq_noPanic_state_placed serPrefix5_of_pq_empty_parse serPrefix6_of_addresses_none_parse
   tag4_pure_facts_parse tag5_pure_facts_parse tag6_pure_facts_parse
   wireSignalMessageAt_expose_addrCap_parse wireSignalMessageAt_expose_addr_some_parse
   wireSignalMessageAt_expose_ct_parse wireSignalMessageAt_expose_pq_parse)

export LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456BudgetAux
  (seq_noPanic_state_placed wireSignalMessageAt_expose_ct_parse
   wireSignalMessageAt_expose_pq_parse wireSignalMessageAt_expose_addrCap_parse
   wireSignalMessageAt_expose_addr_some_parse serPrefix5_of_pq_empty_parse
   serPrefix6_of_addresses_none_parse tag4_pure_facts_parse tag5_pure_facts_parse
   tag6_pure_facts_parse new_encode_tag4_wpp_placed_at new_encode_tag4_wpp_placed
   new_encode_tag4_wpp_placed_x new_encode_tag6_wpp_placed_at new_encode_tag6_wpp_placed
   new_encode_tag6_wpp_placed_x)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
theorem bv_ult_zero_local (v : BitVec 64) : v.ult 0#64 = false := by
  simp [BitVec.ult]

private theorem intro_state_eq {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : ∀ sc : State, sc = s → SepWPp prog ret sc P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  h s rfl

/-! ## Encoding Optional Tags 5 & 6 (`+0x2e0 → +0x3dc`, `0` Allocations) -/

private theorem new_encode_tag56_pq_empty_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {varStack cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : varStack ≤ cmStack)
    (hbnd : cmStack ≤ 2 ^ 64)
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecWithStack A lim varStack)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (hpq_nil : x.pqRatchet = [])
    (haddrCap : addrCap = if (x.addresses parse).isSome then 36#64 else noneCap)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0_align : (sp0 &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 parse).length)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (((sp0 - 408#64) ↦₆₄ w408) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ 32#64) ∗
       wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix4 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 parse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix6 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hpqCap_eq : pqCap = BitVec.allOnes 64 := by
    simpa [PqPinOk, hpq_nil, noneCap] using hpq_pin
  subst hpqCap_eq
  have hp45_eq : x.serPrefix4 parse = x.serPrefix5 parse :=
    (serPrefix5_of_pq_empty_parse parse x hpq_nil).symm
  cases haddr_eq : x.addresses parse with
  | none =>
    have haddrCap_eq : addrCap = BitVec.allOnes 64 := by
      simpa [haddr_eq, noneCap] using haddrCap
    clear haddrCap
    subst haddrCap_eq
    have hp56_eq : x.serPrefix5 parse = x.serPrefix6 parse :=
      (serPrefix6_of_addresses_none_parse parse x haddr_eq).symm
    rw [wireSignalMessageAt_expose_addrCap_parse parse A.repAlloc x rkPtr ctCopyPtr
          (BitVec.allOnes 64) pqCopyPtr (BitVec.allOnes 64) addrPtr sp0 (fun _ => rfl)]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool ((blkPl_63).base + 988#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm,
        ← hp56_eq, ← hp45_eq,
        hsp, hsp0_align, hx19, hx21, hx23, hx24, hx25, hx27, hx29, and_self]
    · rw [hp45_eq, hp56_eq]
      exact entails_of_sep_focus (by sep_focus)
  | some ad =>
    have haddrCap_eq : addrCap = 36#64 := by
      simpa [haddr_eq] using haddrCap
    clear haddrCap
    subst haddrCap_eq
    have htag6 := new_encode_tag6_wpp_placed_at (st := st) (Qp := fun _ _ => False) hle hbnd h_mc hVarint
      x sp0 rkPtr ctCopyPtr (BitVec.allOnes 64) pqCopyPtr addrPtr serPtr ad haddr_eq
      hct_le hpq_lt hserPtr
    rw [wireSignalMessageAt_expose_addrCap_parse parse A.repAlloc x rkPtr ctCopyPtr
          (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr sp0 (fun h => by simp [h] at haddr_eq)]
    simp only [sepConj_assoc]
    apply signalMessageNew_of_sepWP_placed (mid := (blkPl_63).base + bv% (888)) hcl
    wp_steps_sync_pool ((blkPl_63).base + bv% (888))
    apply SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun])
    intro hcl0
    rw [hp45_eq]
    refine intro_state_eq fun s_b hs_b => ?_
    rw [← hs_b] at hcl0 ⊢
    refine seq_noPanic_state_placed
      (F := ((sp0 - 408#64) ↦₆₄ rkPtr) ∗ ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            ((sp0 - 344#64) ↦₆₄ ctCopyPtr))
      hcl0
      (htag6 s_b hcl0
        (by rw [hs_b]; simp only [wp_norm, arm64_norm])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hrun])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hsp])
        (by rw [hs_b]; simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hx19])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hx21])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hx23])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hx24])
        (by rw [← hp45_eq, hs_b]; simp only [wp_norm, arm64_norm, hx25])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hx27])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hx29]))
      (by
        rw [wireSignalMessageAt_expose_addrCap_parse parse A.repAlloc x rkPtr ctCopyPtr
              (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr sp0 (fun h => by simp [h] at haddr_eq)]
        sep_focus)
      ?_
    intro sm _ hpcm hrunm h1
    rw [hs_b] at h1
    refine SepWPp.done hpcm hrunm ⟨by simpa only [wp_norm, arm64_norm] using h1, ?_⟩
    rw [wireSignalMessageAt_expose_addrCap_parse parse A.repAlloc x rkPtr ctCopyPtr
          (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr sp0 (fun h => by simp [h] at haddr_eq)]
    exact entails_of_sep_focus (by sep_focus)

private theorem new_encode_tag56_pq_nonempty_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {varStack cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : varStack ≤ cmStack)
    (hbnd : cmStack ≤ 2 ^ 64)
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecWithStack A lim varStack)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (hpq_nil : x.pqRatchet ≠ [])
    (haddrCap : addrCap = if (x.addresses parse).isSome then 36#64 else noneCap)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0_align : (sp0 &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 parse).length)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (((sp0 - 408#64) ↦₆₄ w408) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ 32#64) ∗
       wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix4 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 parse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix6 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hemp : x.pqRatchet.isEmpty = false := List.isEmpty_eq_false_iff.mpr hpq_nil
  have hpq_pin' := hpq_pin
  simp only [PqPinOk, hemp, Bool.false_eq_true, ↓reduceIte] at hpq_pin'
  obtain ⟨rfl, hpq_pos, _, hpqPtr_ne⟩ := hpq_pin'
  have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hmemcpy := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63))
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds_parse parse x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, hpq_cmn, hp4_lt, hcmp5, hvar5_lt, hvar5_fit,
        hp5_eq, hcmp_pq, hpq_nz, hp4a_slice_le, hp5_bv_eq⟩ :=
    tag5_pure_facts_parse parse x (encode (x.protoMsg parse)).length rfl
      henc_lo henc_hi hpq_nil hpq_lt
  have hp5_eq' :
      (x.serPrefix4 parse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)) ++
        x.pqRatchet = x.serPrefix5 parse := by
    simpa only [List.append_assoc, List.singleton_append] using hp5_eq
  simp only [List.append_assoc, List.singleton_append] at hcmp_pq hp4a_slice_le hp5_bv_eq
  have htag6_opt := fun (st_cur : M.σ) (ad : List (BitVec 8)) (had : x.addresses parse = some ad) =>
    new_encode_tag6_wpp_placed_at (st := st_cur) (Qp := fun _ _ => False) hle hbnd h_mc hVarint
      x sp0 rkPtr ctCopyPtr (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr addrPtr serPtr ad had
      hct_le hpq_lt hserPtr
  rw [serVec_expose_one A.repAlloc sp0
        (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix4 parse).length)
        (serPtr + BitVec.ofNat 64 (x.serPrefix4 parse).length + 1#64)
        (x.serPrefix4 parse) hp4_lt htot_lt hserPtr rfl rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl
  wp_steps_sync_pool (lsmpl.base 10)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  let gx5 : EncodeVarintGhost :=
    ⟨BitVec.ofNat 64 x.pqRatchet.length, sp0 - 176#64,
     BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9),
     serPtr, x.serPrefix4 parse ++ [0x2a#8]⟩
  refine call_noPanic_placed (x := (gx5, st))
    (F := ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ 32#64) ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
    hcl0 hVarint (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    rw [stackAt_split_ge hle hbnd (sp0 - 416#64)] at hm
    rw [encodeVarintSpecWithStack_pre_eq A lim varStack gx5 st _ (sp0 - 416#64)
          (by simp only [gx5, wp_norm, arm64_norm])
          (by simp only [gx5, wp_norm, arm64_norm])
          hvar5_lt hvar5_fit
          (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A.repAlloc sp0
          (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix4 parse).length)
          (BitVec.ofNat 64 (x.serPrefix4 parse).length + 1#64)
          (serPtr + BitVec.ofNat 64 (x.serPrefix4 parse).length + 1#64)
          (x.serPrefix4 parse) 0x2a#8 hp4_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hcl1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm,
    hsp, hx19, hx21, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpecWithStack_post_eq A lim varStack gx5 st _ sf1 (sp0 - 416#64)
        (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs5 => SepWPp.exists_elim fun cap' =>
    SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rw [sepConj_left_comm]
  refine SepWPp.pure_elim fun hevs5 => ?_
  have hevs5_nil : evs5 = [] := by
    rw [hevs5]; exact encodeVarintEvents_of_spare (x := gx5) hvar5_fit
  subst hevs5_nil
  rw [M.stepEvents_nil]
  rcases hno_grow hvar5_fit with ⟨hcap', hptr'⟩
  dsimp only [gx5] at hcap' hptr' ⊢
  subst cap' ptr'
  simp only [List.append_assoc, List.singleton_append]
  rw [serVec_expose_slice A.repAlloc sp0
        (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
        serPtr
        (BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
          encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length)
        (BitVec.ofNat 64 x.pqRatchet.length)
        (serPtr + BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
          encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
          BitVec.ofNat 64 x.pqRatchet.length)
        (x.serPrefix4 parse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))
        x.pqRatchet.length
        hp4a_slice_le htot_lt hserPtr hpq_pos rfl rfl rfl,
      wireSignalMessageAt_expose_pq_parse parse A.repAlloc x rkPtr ctCopyPtr pqCopyPtr
        addrCap addrPtr (sp0 - 288#64) hpq_nil hpq_pin]
  simp only [sepConj_assoc]
  apply signalMessageNew_of_sepWP_placed (mid := lsρ lsMemcpySym) hcl1
  wp_steps_sync_pool (lsρ lsMemcpySym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  intro hcl1'
  refine bind_state ?_
  intro s_mc
  refine call_noPanic_placed
    (x := (serPtr + BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length,
           pqCopyPtr, x.pqRatchet))
    (F := ((sp0 - 176#64) ↦₆₄
            BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄
            BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
              encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length) ∗
          A.repAlloc.live serPtr
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ (x.serPrefix4 parse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))) ∗
          memRegion
            (serPtr + BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
              encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
              BitVec.ofNat 64 x.pqRatchet.length)
            ((BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)).toNat -
              (x.serPrefix4 parse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length -
              x.pqRatchet.length) ∗
          A.pool lim st s_mc ∗ stackAt (sp0 - 416#64) varStack ∗
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ 32#64) ∗
          (optVecU8At A.repAlloc ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
           optVecU8At A.repAlloc ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
             ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           (((sp0 - 288#64) + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
           (((sp0 - 288#64) + 0x30#64 + 8#64) ↦₆₄ pqCopyPtr) ∗
           (((sp0 - 288#64) + 0x30#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
           ⌜pqCopyPtr ≠ 0#64 ∧ x.pqRatchet.length < 2 ^ 63⌝ ∗
           A.repAlloc.live pqCopyPtr x.pqRatchet.length 1 ∗
           optVecU8At A.repAlloc ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64)
             (x.addresses parse) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
           optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - varStack))
    hcl1' hmemcpy (by simp only [s_mc, wp_norm, arm64_norm])
    (by simp only [s_mc, wp_norm, arm64_norm, hrun1])
    (by simp only [s_mc, State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [s_mc, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    dsimp only [s_mc] at hm ⊢
    simp only [framelessMemcpyBudgetSpec, withVmPreserved]
    rw [session2MemcpySpec_pre_eq _ _ _ _
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hpq_toNat])]
    simp only [sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hcl2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  dsimp only [s_mc] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [wp_norm, arm64_norm,
    hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc]
  refine SepWPp.pure_elim fun hvm2 => SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
  dsimp only [s_mc] at hvm2 htr2 ⊢
  rw [← A.pool_transport lim st _ sf2 hvm2]
  simp only [wp_norm, arm64_norm, htr1] at htr2
  have h216 : (sp0 - 288#64) + 0x48#64 = sp0 - 216#64 := bv_sub_add_lit sp0 288 72
  cases haddr_eq : x.addresses parse with
  | none =>
    have haddrCap_eq : addrCap = BitVec.allOnes 64 := by
      simpa [haddr_eq, noneCap] using haddrCap
    clear haddrCap
    subst haddrCap_eq
    have hp56_eq : x.serPrefix5 parse = x.serPrefix6 parse :=
      (serPrefix6_of_addresses_none_parse parse x haddr_eq).symm
    rw [optVecU8At_expose_cap_rest A.repAlloc ⟨BitVec.allOnes 64, addrPtr⟩
          ((sp0 - 288#64) + 0x48#64) none (fun _ => rfl),
        h216]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool ((blkPl_63).base + 988#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm,
        ← hp56_eq,
        hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h27_2, hfp_2,
        htr2, and_self]
    · rw [← hp56_eq, ← hp5_bv_eq,
          stackAt_split_ge hle hbnd (sp0 - 416#64),
          ← hp5_eq',
          ← serVec_pack_slice A.repAlloc sp0
              (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
              serPtr
              (BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length)
              (BitVec.ofNat 64 x.pqRatchet.length)
              (BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                BitVec.ofNat 64 x.pqRatchet.length)
              (serPtr + BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                BitVec.ofNat 64 x.pqRatchet.length)
              (x.serPrefix4 parse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))
              x.pqRatchet
              hp4a_slice_le htot_lt hserPtr hpq_nil rfl rfl rfl rfl]
      exact entails_of_sep_focus (by sep_focus)
  | some ad =>
    have haddrCap_eq : addrCap = 36#64 := by
      simpa [haddr_eq] using haddrCap
    clear haddrCap
    subst haddrCap_eq
    have htag6 := htag6_opt st ad haddr_eq
    rw [optVecU8At_expose_cap_rest A.repAlloc ⟨36#64, addrPtr⟩
          ((sp0 - 288#64) + 0x48#64) (some ad) (by nofun),
        h216]
    simp only [sepConj_assoc]
    apply signalMessageNew_of_sepWP_placed (mid := (blkPl_63).base + bv% (888)) hcl2
    wp_steps_sync_pool ((blkPl_63).base + bv% (888))
    apply SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun2])
    intro hcl2'
    refine intro_state_eq fun s_b hs_b => ?_
    rw [← hs_b] at hcl2' ⊢
    refine seq_noPanic_state_placed
      (F := ((sp0 - 408#64) ↦₆₄ rkPtr) ∗ ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            ((sp0 - 344#64) ↦₆₄ ctCopyPtr))
      hcl2'
      (htag6 s_b hcl2'
        (by rw [hs_b]; simp only [wp_norm, arm64_norm])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hrun2])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hsp2])
        (by rw [hs_b]; simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, h19_2])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, h20_2])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, h21_2])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, h23_2])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, h24_2])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, h27_2])
        (by rw [hs_b]; simp only [wp_norm, arm64_norm, hfp_2]))
      (by
        rw [← hp5_bv_eq, stackAt_split_ge hle hbnd (sp0 - 416#64),
            ← hp5_eq',
            ← serVec_pack_slice A.repAlloc sp0
                (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
                serPtr
                (BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length)
                (BitVec.ofNat 64 x.pqRatchet.length)
                (BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (serPtr + BitVec.ofNat 64 (x.serPrefix4 parse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (x.serPrefix4 parse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))
                x.pqRatchet
                hp4a_slice_le htot_lt hserPtr hpq_nil rfl rfl rfl rfl,
            wireSignalMessageAt_expose_pq_parse parse A.repAlloc x rkPtr ctCopyPtr pqCopyPtr
              36#64 addrPtr (sp0 - 288#64) hpq_nil hpq_pin,
            haddr_eq,
            optVecU8At_expose_cap_rest A.repAlloc ⟨36#64, addrPtr⟩
              ((sp0 - 288#64) + 0x48#64) (some ad) (by nofun),
            h216]
        sep_focus)
      ?_
    intro sm _ hpcm hrunm h1
    rw [hs_b] at h1
    refine SepWPp.done hpcm hrunm
      ⟨by simpa only [wp_norm, arm64_norm, htr2, hfp_2] using h1, ?_⟩
    rw [wireSignalMessageAt_expose_pq_parse parse A.repAlloc x rkPtr ctCopyPtr pqCopyPtr
          36#64 addrPtr (sp0 - 288#64) hpq_nil hpq_pin,
        haddr_eq,
        optVecU8At_expose_cap_rest A.repAlloc ⟨36#64, addrPtr⟩
          ((sp0 - 288#64) + 0x48#64) (some ad) (by nofun),
        h216]
    dsimp only
    exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag56_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {varStack cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : varStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecWithStack A lim varStack)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (haddrCap : addrCap = if (x.addresses parse).isSome then 36#64 else noneCap)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 parse).length)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (((sp0 - 408#64) ↦₆₄ w408) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ 32#64) ∗
       wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix4 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 parse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix6 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  by_cases hpq_nil : x.pqRatchet = []
  · exact new_encode_tag56_pq_empty_placed_at hle hbnd h_mc hVarint
      x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408
      hct_le hpq_lt hserPtr hpq_pin hpq_nil haddrCap
      s hcl hpc hrun hsp hsp0_align hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29
  · exact new_encode_tag56_pq_nonempty_placed_at hle hbnd h_mc hVarint
      x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408
      hct_le hpq_lt hserPtr hpq_pin hpq_nil haddrCap
      s hcl hpc hrun hsp hsp0_align hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag56_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (haddrCap : addrCap = if (x.addresses parse).isSome then 36#64 else noneCap)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 parse).length)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (((sp0 - 408#64) ↦₆₄ w408) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ 32#64) ∗
       wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix4 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 parse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix6 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_encode_tag56_wpp_placed_at (varStack := encodeVarintStack) (cmStack := computeMacStack)
    (by decide) (by decide) h_mc (by rwa [← encodeVarintSpec_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408
    hct_le hpq_lt hserPtr hpq_pin haddrCap
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag56_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (haddrCap : addrCap = if (x.addresses parse).isSome then 36#64 else noneCap)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 parse).length)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (((sp0 - 408#64) ↦₆₄ w408) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ 32#64) ∗
       wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
         serPtr (x.serPrefix4 parse) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 parse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            serPtr (x.serPrefix6 parse) ∗
          A.pool lim st sm ∗ stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_encode_tag56_wpp_placed_at (varStack := encodeVarintStackX) (cmStack := computeMacStackX)
    (by decide) (by decide) h_mc (by rwa [← encodeVarintSpecX_eq_withStack])
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408
    hct_le hpq_lt hserPtr hpq_pin haddrCap
    s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456Budget
