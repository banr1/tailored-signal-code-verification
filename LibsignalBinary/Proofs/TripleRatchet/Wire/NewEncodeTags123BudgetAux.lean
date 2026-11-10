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
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded `<SignalMessage>::new` Segment 2a Helpers (`+0x100 .. +0x1b8`)

Allocator event suffix after `serialized` allocation (`newAfterSerAllocEvents`),
`UuidParser`-generic pure and separation-logic bridges, and relocatable `[LibsignalPlacement]`
budget-threaded segment lemmas for storing `wire::SignalMessage` (`+0x100 → +0x13c`) and
allocating `serialized` (`+0x13c → +0x1b8`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123BudgetAux

open Arm64 ProofLib SepProp CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open ProofLib.ProgramReflection
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl lsρ
   lsMemcpySym lsRustAllocSym lsRustNoAllocShimSym withLsCodeLoaded)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  encodedLenSpec encodeVarintSpec encodeVarintSpecX
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.NewEncodeTags123Callees
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   RustLayoutOk fitsEvents_append fitsEvents_nil rustAllocEvents rustCliAllocBudgetSpec
   rustCliAllocNoOomSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (computeMacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (EncodeVarintEnv encodeVarintEvents_of_spare encodeVarintSpec encodeVarintSpecX encodedLenSpec)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux
  (call_noPanic_placed newPostPrologueEvents stackAt_split_ge)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
  (framelessMemcpyBudgetSpec new_allocNoOom_placed_ok new_memcpy_placed_ok
   new_shim_placed_ok noAllocShimBudgetSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem bind_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : let sc := s; SepWPp prog ret sc P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  h

theorem call_noPanic_extern {α : Type} {prog : Program}
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
        intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with
    ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpanic sm (F ∗ R) hpan hpost).elim
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact (hoom sm (F ∗ R) hoom_s hpost).elim

/-! ## Event suffix after `serialized` allocation (`+0x1b8 .. return`) -/

/-- Remaining allocator events of `<SignalMessage>::new` after `new_alloc_ser_wpp_placed`
(`+0x1b8 .. return`; tags 1–6 emit `[]` because `serialized` has exact capacity). -/
def newAfterSerAllocEvents (x : SignalMessageNewGhost) : List AllocEvent :=
  computeMacEvents ++
    (if x.ciphertext.isEmpty then [] else rustAllocEvents x.ciphertext.length 1) ++
    (if x.pqRatchet.isEmpty then [] else rustAllocEvents x.pqRatchet.length 1) ++
    rustDeallocEvents 33 1 ++
    (if x.ciphertext.isEmpty then [] else rustDeallocEvents x.ciphertext.length 1) ++
    (if x.pqRatchet.isEmpty then [] else rustDeallocEvents x.pqRatchet.length 1)

theorem newPostPrologueEvents_eq_serAlloc_append (parse : UuidParser) (x : SignalMessageNewGhost) :
    newPostPrologueEvents parse x =
      rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1 ++ newAfterSerAllocEvents x := by
  simp only [newPostPrologueEvents, newAfterSerAllocEvents, List.append_assoc]

theorem fitsEvents_serAlloc_and_after_of_postPrologue {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {parse : UuidParser} {x : SignalMessageNewGhost}
    (h : FitsEvents M lim st (newPostPrologueEvents parse x)) :
    let serEvs := rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1
    FitsEvents M lim st serEvs ∧
      FitsEvents M lim (M.stepEvents serEvs st) (newAfterSerAllocEvents x) := by
  rw [newPostPrologueEvents_eq_serAlloc_append] at h
  exact (fitsEvents_append M lim _ _ st).mp h

/-! ## `UuidParser`-generic pure and spatial helpers -/

theorem addresses_length_parse {parse : UuidParser} {x : SignalMessageNewGhost}
    {ad : List (BitVec 8)} (h : x.addresses parse = some ad) :
    ad.length = 36 := by
  simp only [SignalMessageNewGhost.addresses] at h
  cases hx : x.loc with
  | none => simp [hx] at h
  | some l =>
    simp only [hx, Option.bind_some] at h
    exact serializeAddresses_length h

theorem encodeBytesField_1_protoMsg_parse (parse : UuidParser) (x : SignalMessageNewGhost) :
    encodeBytesField 1 (x.protoMsg parse).ratchetKey =
      [0x0a#8, 0x21#8] ++ x.senderRatchetKey.serialize := by
  simp [SignalMessageNewGhost.protoMsg, encodeBytesField, publicKey_serialize_length,
    encodeKey_1_ld, encodeVarint_33]

theorem encodeUint32Field_2_protoMsg_parse (parse : UuidParser)
    (x : SignalMessageNewGhost) :
    encodeUint32Field 2 (x.protoMsg parse).counter =
      [0x10#8] ++ encodeVarint (x.counter.zeroExtend 64) := by
  simp [SignalMessageNewGhost.protoMsg, encodeUint32Field, encodeKey_2_varint]

theorem encodeUint32Field_3_protoMsg_parse (parse : UuidParser)
    (x : SignalMessageNewGhost) :
    encodeUint32Field 3 (x.protoMsg parse).previousCounter =
      [0x18#8] ++ encodeVarint (x.previousCounter.zeroExtend 64) := by
  simp [SignalMessageNewGhost.protoMsg, encodeUint32Field, encodeKey_3_varint]

theorem encodeBytesField_4_protoMsg_parse (parse : UuidParser) (x : SignalMessageNewGhost) :
    encodeBytesField 4 (x.protoMsg parse).ciphertext =
      [0x22#8] ++ encodeVarint (BitVec.ofNat 64 x.ciphertext.length) ++ x.ciphertext := by
  simp [SignalMessageNewGhost.protoMsg, encodeBytesField, encodeKey_4_ld]

theorem encodeBytesField_5_protoMsg_empty_parse (parse : UuidParser)
    (x : SignalMessageNewGhost) (h : x.pqRatchet = []) :
    encodeBytesField 5 (x.protoMsg parse).pqRatchet = [] := by
  simp [SignalMessageNewGhost.protoMsg, h, encodeBytesField]

theorem encodeBytesField_5_protoMsg_nonempty_parse (parse : UuidParser)
    (x : SignalMessageNewGhost) (h : x.pqRatchet ≠ []) :
    encodeBytesField 5 (x.protoMsg parse).pqRatchet =
      [0x2a#8] ++ encodeVarint (BitVec.ofNat 64 x.pqRatchet.length) ++ x.pqRatchet := by
  have hemp : x.pqRatchet.isEmpty = false := List.isEmpty_eq_false_iff.mpr h
  simp [SignalMessageNewGhost.protoMsg, hemp, encodeBytesField, encodeKey_5_ld]

theorem encodeBytesField_6_protoMsg_none_parse (parse : UuidParser)
    (x : SignalMessageNewGhost) (h : x.addresses parse = none) :
    encodeBytesField 6 (x.protoMsg parse).addresses = [] := by
  simp [SignalMessageNewGhost.protoMsg, h, encodeBytesField]

theorem encodeBytesField_6_protoMsg_some_parse (parse : UuidParser)
    (x : SignalMessageNewGhost) {ad : List (BitVec 8)} (h : x.addresses parse = some ad) :
    encodeBytesField 6 (x.protoMsg parse).addresses = [0x32#8, 0x24#8] ++ ad := by
  have hlen := addresses_length_parse h
  simp [SignalMessageNewGhost.protoMsg, h, hlen, encodeBytesField, encodeKey_6_ld, encodeVarint_36]

theorem encode_protoMsg_length_bounds_parse (parse : UuidParser) (x : SignalMessageNewGhost)
    (hct : x.ciphertext.length ≤ 2 ^ 32) (hpq : x.pqRatchet.length < 2 ^ 32) :
    35 ≤ (encode (x.protoMsg parse)).length ∧
      (encode (x.protoMsg parse)).length < 2 ^ 34 := by
  unfold encode
  rw [encodeBytesField_1_protoMsg_parse, encodeUint32Field_2_protoMsg_parse,
    encodeUint32Field_3_protoMsg_parse, encodeBytesField_4_protoMsg_parse]
  have hrk := publicKey_serialize_length x.senderRatchetKey
  have ⟨_, hv2⟩ :=
    CryptoVerification.LibsignalTripleRatchet.signalMessageNew_encodeVarint_length_bounds
      (x.counter.zeroExtend 64)
  have ⟨_, hv3⟩ :=
    CryptoVerification.LibsignalTripleRatchet.signalMessageNew_encodeVarint_length_bounds
      (x.previousCounter.zeroExtend 64)
  have ⟨_, hv4⟩ :=
    CryptoVerification.LibsignalTripleRatchet.signalMessageNew_encodeVarint_length_bounds
      (BitVec.ofNat 64 x.ciphertext.length)
  have hpq_len : (encodeBytesField 5 (x.protoMsg parse).pqRatchet).length ≤
      11 + x.pqRatchet.length := by
    by_cases hpq0 : x.pqRatchet = []
    · rw [encodeBytesField_5_protoMsg_empty_parse parse x hpq0]; simp
    · rw [encodeBytesField_5_protoMsg_nonempty_parse parse x hpq0]
      have ⟨_, hv5⟩ :=
        CryptoVerification.LibsignalTripleRatchet.signalMessageNew_encodeVarint_length_bounds
          (BitVec.ofNat 64 x.pqRatchet.length)
      simp only [List.length_append, List.length_singleton]
      omega
  have had_len : (encodeBytesField 6 (x.protoMsg parse).addresses).length ≤ 38 := by
    cases had : x.addresses parse with
    | none => rw [encodeBytesField_6_protoMsg_none_parse parse x had]; simp
    | some ad =>
      rw [encodeBytesField_6_protoMsg_some_parse parse x had]
      have := addresses_length_parse had
      simp [this]
  simp only [List.length_append, List.length_cons, List.length_nil, hrk]
  omega

theorem wireLengthsFit_protoMsg_parse (parse : UuidParser) (x : SignalMessageNewGhost)
    (hct : x.ciphertext.length ≤ 2 ^ 32) (hpq : x.pqRatchet.length < 2 ^ 32) :
    WireLengthsFit (x.protoMsg parse) := by
  unfold WireLengthsFit
  have ⟨_, hlt⟩ := encode_protoMsg_length_bounds_parse parse x hct hpq
  omega

theorem serPrefix6_eq_serializeContent_parse (parse : UuidParser)
    (x : SignalMessageNewGhost) :
    x.serPrefix6 parse =
      serializeContent protoSignalCodec x.messageVersion x.senderRatchetKey x.counter
        x.previousCounter x.ciphertext x.pqRatchet (x.addresses parse) := by
  simp only [SignalMessageNewGhost.serPrefix6, SignalMessageNewGhost.serPrefix5,
    SignalMessageNewGhost.serPrefix4, SignalMessageNewGhost.serPrefix3,
    SignalMessageNewGhost.serPrefix2, SignalMessageNewGhost.serPrefix1,
    SignalMessageNewGhost.serPrefix0, serializeContent, protoSignalCodec,
    encode, SignalMessageNewGhost.protoMsg,
    List.cons_append, List.nil_append, List.append_assoc]

theorem serPrefix6_length_parse (parse : UuidParser) (x : SignalMessageNewGhost) :
    (x.serPrefix6 parse).length = 1 + (encode (x.protoMsg parse)).length := by
  rw [serPrefix6_eq_serializeContent_parse]
  simp [serializeContent, protoSignalCodec, SignalMessageNewGhost.protoMsg]
  omega

theorem serPrefix_lengths_le_parse (parse : UuidParser) (x : SignalMessageNewGhost) :
    (x.serPrefix0).length = 1 ∧
    (x.serPrefix1 parse).length = 36 ∧
    (x.serPrefix1 parse).length ≤ (x.serPrefix2 parse).length ∧
    (x.serPrefix2 parse).length ≤ (x.serPrefix3 parse).length ∧
    (x.serPrefix3 parse).length ≤ (x.serPrefix4 parse).length ∧
    (x.serPrefix4 parse).length ≤ (x.serPrefix5 parse).length ∧
    (x.serPrefix5 parse).length ≤ (x.serPrefix6 parse).length := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [SignalMessageNewGhost.serPrefix1, SignalMessageNewGhost.serPrefix0,
      encodeBytesField_1_protoMsg_parse, publicKey_serialize_length]
  · simp [SignalMessageNewGhost.serPrefix2]
  · simp [SignalMessageNewGhost.serPrefix3]
  · simp [SignalMessageNewGhost.serPrefix4]
  · simp [SignalMessageNewGhost.serPrefix5]
  · simp [SignalMessageNewGhost.serPrefix6]

theorem tag123_pure_facts_parse (parse : UuidParser) (x : SignalMessageNewGhost)
    (encLen : Nat)
    (henc_eq : encLen = (encode (x.protoMsg parse)).length)
    (hlo : 35 ≤ encLen) (hhi : encLen < 2 ^ 34) :
    (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 ∧
    (BitVec.ofNat 64 (encLen + 9)).toNat < 2 ^ 63 ∧
    (x.serPrefix0).length = 1 ∧
    (BitVec.ofNat 64 (encLen + 9) == 1#64) = false ∧
    (x.serPrefix0 ++ [0x0a#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix0 ++ [0x0a#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64).length = 3 ∧
    (BitVec.ofNat 64 (encLen + 9) - 3#64).ult 33#64 = false ∧
    x.senderRatchetKey.serialize.length = 33 ∧
    x.senderRatchetKey.serialize ≠ [] ∧
    ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) ++ x.senderRatchetKey.serialize =
      x.serPrefix1 parse ∧
    (x.serPrefix1 parse).length = 36 ∧
    (BitVec.ofNat 64 (encLen + 9) == 36#64) = false ∧
    (x.serPrefix1 parse ++ [0x10#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix1 parse ++ [0x10#8]).length + (encodeVarint (x.counter.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (x.serPrefix1 parse ++ [0x10#8]) ++ encodeVarint (x.counter.zeroExtend 64) =
      x.serPrefix2 parse ∧
    (x.serPrefix2 parse).length < (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (BitVec.ofNat 64 (encLen + 9) == BitVec.ofNat 64 (x.serPrefix2 parse).length) = false ∧
    (x.serPrefix2 parse ++ [0x18#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix2 parse ++ [0x18#8]).length +
      (encodeVarint (x.previousCounter.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (x.serPrefix2 parse ++ [0x18#8]) ++ encodeVarint (x.previousCounter.zeroExtend 64) =
      x.serPrefix3 parse := by
  have htot : (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbv_lo : 44#64 ≤ BitVec.ofNat 64 (encLen + 9) := by
    rw [BitVec.le_def, htot]; change 44 ≤ encLen + 9; omega
  have hbv_hi : BitVec.ofNat 64 (encLen + 9) < 17179869193#64 := by
    rw [BitVec.lt_def, htot]; change encLen + 9 < 17179869193; omega
  have ⟨h0_len, h1_len, h12_le, h23_le, h34_le, h45_le, h56_le⟩ :=
    serPrefix_lengths_le_parse parse x
  have h6_len : (x.serPrefix6 parse).length = 1 + encLen := by
    rw [henc_eq, serPrefix6_length_parse]
  have hp1_eq : ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) ++
      x.senderRatchetKey.serialize = x.serPrefix1 parse := by
    simp [SignalMessageNewGhost.serPrefix1, encodeBytesField_1_protoMsg_parse, encodeVarint_33,
      List.append_assoc]
  have hp2_eq : (x.serPrefix1 parse ++ [0x10#8]) ++ encodeVarint (x.counter.zeroExtend 64) =
      x.serPrefix2 parse := by
    simp [SignalMessageNewGhost.serPrefix2, encodeUint32Field_2_protoMsg_parse, List.append_assoc]
  have hp3_eq : (x.serPrefix2 parse ++ [0x18#8]) ++
      encodeVarint (x.previousCounter.zeroExtend 64) = x.serPrefix3 parse := by
    simp [SignalMessageNewGhost.serPrefix3, encodeUint32Field_3_protoMsg_parse, List.append_assoc]
  have hp2_lt : (x.serPrefix2 parse).length < encLen + 9 := by omega
  have hp2_toNat : (BitVec.ofNat 64 (x.serPrefix2 parse).length).toNat =
      (x.serPrefix2 parse).length := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨htot, by omega, h0_len, ?_, ?_, ?_, ?_, ?_,
    publicKey_serialize_length x.senderRatchetKey,
    publicKey_serialize_ne_nil x.senderRatchetKey,
    hp1_eq, h1_len, ?_, ?_, ?_, hp2_eq, by omega, ?_, ?_, ?_, hp3_eq⟩
  · bv_kernel
  · simp [h0_len]
  · simp [h0_len, encodeVarint_33, htot]
  · simp [h0_len, encodeVarint_33]
  · bv_kernel
  · bv_kernel
  · simp [h1_len]
  · have hlen2 : ((x.serPrefix1 parse ++ [0x10#8]) ++
        encodeVarint (x.counter.zeroExtend 64)).length = (x.serPrefix2 parse).length := by
      rw [hp2_eq]
    rw [List.length_append] at hlen2
    omega
  · apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  · rw [List.length_append, List.length_singleton]; omega
  · have hlen3 : ((x.serPrefix2 parse ++ [0x18#8]) ++
        encodeVarint (x.previousCounter.zeroExtend 64)).length = (x.serPrefix3 parse).length := by
      rw [hp3_eq]
    rw [List.length_append] at hlen3
    omega

theorem pack_wire_post_parse (parse : UuidParser) (A : RustAlloc)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr addrLen : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32) :
    (((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
     ((sp0 - 320#64) ↦₆₄ pqCap) ∗
     (((sp0 - 312#64) ↦₆₄ addrCap) ∗ ((sp0 - 304#64) ↦₆₄ addrPtr) ∗
       ((sp0 - 296#64) ↦₆₄ addrLen)) ∗
     (((sp0 - 288#64) ↦₆₄ 33#64) ∗ ((sp0 - 280#64) ↦₆₄ rkPtr) ∗ ((sp0 - 272#64) ↦₆₄ 33#64) ∗
       signalMessageNew_vecU8Buf A 33#64 rkPtr x.senderRatchetKey.serialize) ∗
     (((sp0 - 264#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
       ((sp0 - 256#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 248#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
       signalMessageNew_vecU8Buf A (BitVec.ofNat 64 x.ciphertext.length) ctCopyPtr x.ciphertext) ∗
     (((sp0 - 240#64) ↦₆₄ pqCap) ∗ ((sp0 - 232#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
       optPqBuf A pqCap pqCopyPtr x.pqRatchet) ∗
     (((sp0 - 216#64) ↦₆₄ addrCap) ∗ ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
       ((sp0 - 200#64) ↦₆₄ addrLen) ∗
       optAddrBuf A addrCap addrPtr addrLen (x.addresses parse)) ∗
     (((sp0 - 192#64) ↦₃₂ 1#32) ∗ ((sp0 - 188#64) ↦₃₂ x.counter)) ∗
     (((sp0 - 184#64) ↦₃₂ 1#32) ∗ ((sp0 - 180#64) ↦₃₂ x.previousCounter))) ⊢
    ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
    ((sp0 - 320#64) ↦₆₄ pqCap) ∗
    memRegion (sp0 - 312#64) 24 ∗
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
      (sp0 - 288#64) (x.protoMsg parse) := by
  have hrk := optVecU8At_rk_of_vecU8Buf A (sp0 - 288#64) rkPtr x.senderRatchetKey
  have hct := optVecU8At_ct_of_vecU8Buf A (sp0 - 264#64) ctCopyPtr x.ciphertext (by omega)
  have hpq := optVecU8At_of_optPqBuf A (sp0 - 240#64) pqCap pqCopyPtr x.pqRatchet
  have haddr := optVecU8At_of_optAddrBuf A (sp0 - 216#64) addrCap addrPtr addrLen (x.addresses parse)
  have hm24 := cells3_entails_memRegion_24 (sp0 - 312#64) addrCap addrPtr addrLen
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub] at hrk hct hpq haddr hm24
  simp (disch := decide) only [wireSignalMessageAt, SignalMessageNewGhost.mkPins,
    SignalMessageNewGhost.protoMsg, optU32At, bv_sub_add_lit, Nat.reduceSub]
  rw [hrk, hct]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hm24
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hpq (sepConj_mono haddr (Entails.of_eq (by sep_ac_rfl))))))))

theorem wireSignalMessageAt_expose_rk_parse (parse : UuidParser) (A : RustAlloc)
    (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr a : BitVec 64) :
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
        a (x.protoMsg parse) =
      ((rkPtr ↦ₛ x.senderRatchetKey.serialize) ∗
       ((a ↦₆₄ 33#64) ∗ ((a + 8#64) ↦₆₄ rkPtr) ∗ ((a + 16#64) ↦₆₄ 33#64) ∗
        ⌜rkPtr ≠ 0#64 ∧ x.senderRatchetKey.serialize.length < 2 ^ 63⌝ ∗
        A.live rkPtr x.senderRatchetKey.serialize.length 1 ∗
        optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩ (a + 0x18#64)
          (some x.ciphertext) ∗
        optVecU8At A ⟨pqCap, pqCopyPtr⟩ (a + 0x30#64)
          (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
        optVecU8At A ⟨addrCap, addrPtr⟩ (a + 0x48#64) (x.addresses parse) ∗
        optU32At (a + 0x60#64) (some x.counter) ∗
        optU32At (a + 0x68#64) (some x.previousCounter))) := by
  simp only [wireSignalMessageAt, SignalMessageNewGhost.mkPins, SignalMessageNewGhost.protoMsg]
  rw [optVecU8At_rk_eq]
  sep_ac_rfl

theorem encodedLenBudgetSpec_pre_eq (A : RustAlloc) (x : EncodedLenGhost) (s : State)
    (sp_val : BitVec 64)
    (hx0 : s.readReg64 .x0 = x.a) (hfit : WireLengthsFit x.m) (hsp : s.sp = sp_val) :
    (encodedLenSpec A).pre x s = wireSignalMessageAt A x.g x.a x.m ∗ stackAt sp_val encodedLenStack := by
  unfold encodedLenSpec; dsimp only; rw [hx0, hsp, eq_true hfit]; simp only [wp_norm, arm64_norm]

/-- Stack-parameterized budget contract of `encode_varint::<Vec<u8>> [local#1]`, unifying
`encodeVarintSpec` (`encodeVarintStack`) and `encodeVarintSpecX` (`encodeVarintStackX`). -/
def encodeVarintSpecWithStack {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (varStack : Nat) : Spec (EncodeVarintGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      (x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodeVarintEnv x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt s.sp varStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      (∃∗ evs : List AllocEvent, ⌜EncodeVarintEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp varStack

theorem encodeVarintSpec_eq_withStack {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    encodeVarintSpec A lim = encodeVarintSpecWithStack A lim encodeVarintStack := rfl

theorem encodeVarintSpecX_eq_withStack {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    encodeVarintSpecX A lim = encodeVarintSpecWithStack A lim encodeVarintStackX := rfl

theorem fitsEnv_encodeVarint_of_spare {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : EncodeVarintGhost}
    (hspare : x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat) :
    FitsEnv M lim st (EncodeVarintEnv x) := by
  intro evs hevs
  rw [hevs, encodeVarintEvents_of_spare hspare]
  simp only [fitsEvents_nil]

theorem encodeVarintSpecWithStack_pre_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (varStack : Nat) (x : EncodeVarintGhost) (st : M.σ) (s : State)
    (sp_val : BitVec 64)
    (hx0 : s.readReg64 .x0 = x.val) (hx1 : s.readReg64 .x1 = x.v)
    (hlt : x.bs.length + 10 < 2 ^ 62)
    (hspare : x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat)
    (hsp : s.sp = sp_val) :
    (encodeVarintSpecWithStack A lim varStack).pre (x, st) s =
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗ stackAt sp_val varStack := by
  have hfit : FitsEnv M lim st (EncodeVarintEnv x) = True :=
    eq_true (fitsEnv_encodeVarint_of_spare hspare)
  unfold encodeVarintSpecWithStack; dsimp only
  rw [hx0, hx1, hsp, eq_true (Or.inr hlt), hfit]
  simp only [wp_norm, arm64_norm]

theorem encodeVarintSpecWithStack_post_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (varStack : Nat) (x : EncodeVarintGhost) (st : M.σ) (s0 sf : State)
    (sp_val : BitVec 64) (hsp0 : s0.sp = sp_val) :
    (encodeVarintSpecWithStack A lim varStack).post (x, st) s0 sf =
      ⌜sf.trace = s0.trace⌝ ∗
        (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
        (∃∗ evs : List AllocEvent, ⌜EncodeVarintEnv x evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗
        stackAt sp_val varStack := by
  simp only [encodeVarintSpecWithStack, hsp0]

/-! ## Storing `wire::SignalMessage` at `sp + 0x80` (`+0x100 → +0x13c`) -/

theorem new_store_wire_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks}
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr addrLen w376 w320 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 256#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hx9 : s.readReg64 .x9 = pqCap) :
    SepWP ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 316#64)
      s
      (((sp0 - 376#64) ↦₆₄ w376) ∗
       ((sp0 - 320#64) ↦₆₄ w320) ∗
       ((sp0 - 312#64) ↦₆₄ addrCap) ∗
       ((sp0 - 304#64) ↦₆₄ addrPtr) ∗
       ((sp0 - 296#64) ↦₆₄ addrLen) ∗
       memRegion (sp0 - 288#64) 112 ∗
       signalMessageNew_vecU8Buf A.repAlloc 33#64 rkPtr x.senderRatchetKey.serialize ∗
       signalMessageNew_vecU8Buf A.repAlloc (BitVec.ofNat 64 x.ciphertext.length)
         ctCopyPtr x.ciphertext ∗
       optPqBuf A.repAlloc pqCap pqCopyPtr x.pqRatchet ∗
       optAddrBuf A.repAlloc addrCap addrPtr addrLen (x.addresses parse) ∗
       A.pool lim st s)
      (fun sf P =>
        (sf.sp = sp0 - 416#64 ∧
         sf.spAligned = true ∧
         sf.readReg64 .x0 = sp0 - 288#64 ∧
         sf.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sf.readReg64 .x20 = x.senderRatchetKeyA ∧
         sf.readReg64 .x21 = 33#64 ∧
         sf.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sf.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sf.readReg64 .x24 = x.ret ∧
         sf.readReg64 .x25 = pqCopyPtr ∧
         sf.readReg64 .x26 = ctCopyPtr ∧
         sf.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sf.readReg64 .x28 = rkPtr ∧
         sf.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sf s) ∧
        (P ⊢
          ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          memRegion (sp0 - 312#64) 24 ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          A.pool lim st sf)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  rw [memRegion_wire_112 sp0]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => ?_
  wp_steps_sync_pool ((blkPl_63).base + 316#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp, hsp0_align,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, and_self]
  · have hpack :=
      pack_wire_post_parse parse A.repAlloc x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr
        addrCap addrPtr addrLen hct_bound
    have h4 : ∀ X Y Z W U : SepProp, X ∗ Y ∗ Z ∗ W ∗ U = (X ∗ Y ∗ Z ∗ W) ∗ U :=
      fun _ _ _ _ _ => by sep_ac_rfl
    conv_rhs => rw [h4]
    refine Entails.trans ?_ (sepConj_mono_left hpack)
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## `encoded_len` and `serialized` buffer allocation (`+0x13c → +0x1b8`) -/

theorem new_alloc_ser_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle_enc : encodedLenStack ≤ cmStack := by decide)
    (hle_alloc : allocHookStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (encodedLenSpec A.repAlloc))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr w176 w168 w160 : BitVec 64)
    (w384 w380 verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit_ser : FitsEvents M lim st (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1))
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (_hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 440#64)
      s
      (((sp0 - 384#64) ↦₃₂ w384) ∗
       ((sp0 - 380#64) ↦₃₂ w380) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       wireSignalMessageAt A.repAlloc
         (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       ((sp0 - 176#64) ↦₆₄ w176) ∗
       ((sp0 - 168#64) ↦₆₄ w168) ∗
       ((sp0 - 160#64) ↦₆₄ w160) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 ≠ 0#64 ∧
         sm.readReg64 .x23 = 1#64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            (sm.readReg64 .x22) x.serPrefix0 ∗
          A.pool lim
            (M.stepEvents (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1) st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
  have halloc :=
    new_allocNoOom_placed_ok h_alloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
  clear h_shim h_alloc
  have hfit := wireLengthsFit_protoMsg_parse parse x hct_bound hpq_bound
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds_parse parse x hct_bound hpq_bound
  have ⟨h_adds1, h_cmp9, h_tbz, h_hi, h_add9_eq, h_add9_toNat⟩ :=
    encLen_overflow_checks henc_lo henc_hi
  have h_pos9 : 0 < (encode (x.protoMsg parse)).length + 9 := by omega
  have h_le9 : (encode (x.protoMsg parse)).length + 9 ≤ 9223372036854775807 := by omega
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  apply SepWPp.of_sepWP (mid := lsmpl.base 108)
  wp_steps_sync_pool (lsmpl.base 108)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
  refine bind_state ?_
  intro s_el1
  refine call_noPanic_extern
    (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr,
      x.protoMsg parse⟩)
    (F := ((sp0 - 384#64) ↦₃₂ w384) ∗ ((sp0 - 380#64) ↦₃₂ w380) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool lim st s_el1 ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack))
    hEncLen (by simp only [s_el1, wp_norm, arm64_norm])
    (by simp only [s_el1, wp_norm, arm64_norm, hrun])
    (by simp only [s_el1, State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [s_el1, wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    dsimp only [s_el1] at hm ⊢
    rw [stackAt_split_ge hle_enc hbnd (sp0 - 416#64)] at hm
    rw [encodedLenBudgetSpec_pre_eq A.repAlloc _ _ (sp0 - 416#64)
          (by simp only [wp_norm, arm64_norm, hx0]) hfit
          (by simp only [wp_norm, arm64_norm, hsp])]
    simp only [sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  dsimp only [s_el1] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [wp_norm, arm64_norm, hsp, hx19, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [encodedLenSpec, wp_norm, arm64_norm, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hvm1, hx0_1, htr1⟩ => ?_
  dsimp only [s_el1] at hvm1 htr1 ⊢
  rw [← A.pool_transport lim st _ sf1 hvm1]
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp, sepConj_assoc]
  have hfold_el1 :
      stackAt (sp0 - 416#64) encodedLenStack ∗
        memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack) =
      stackAt (sp0 - 416#64) cmStack :=
    (stackAt_split_ge hle_enc hbnd (sp0 - 416#64)).symm
  conv =>
    arg 4
    rw [show wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
          (sp0 - 288#64) (x.protoMsg parse) ∗
        stackAt (sp0 - 416#64) encodedLenStack ∗
        (sp0 - 384#64) ↦₃₂ w384 ∗ (sp0 - 380#64) ↦₃₂ w380 ∗ (sp0 - 332#64) ↦₃₂ verW32 ∗
        (sp0 - 176#64) ↦₆₄ w176 ∗ (sp0 - 168#64) ↦₆₄ w168 ∗ (sp0 - 160#64) ↦₆₄ w160 ∗
        A.pool lim st sf1 ∗
        memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack) =
        (stackAt (sp0 - 416#64) encodedLenStack ∗
          memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack)) ∗
        wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
          (sp0 - 288#64) (x.protoMsg parse) ∗
        (sp0 - 384#64) ↦₃₂ w384 ∗ (sp0 - 380#64) ↦₃₂ w380 ∗ (sp0 - 332#64) ↦₃₂ verW32 ∗
        (sp0 - 176#64) ↦₆₄ w176 ∗ (sp0 - 168#64) ↦₆₄ w168 ∗ (sp0 - 160#64) ↦₆₄ w160 ∗
        A.pool lim st sf1 by sep_ac_rfl, hfold_el1]
  simp only [wp_norm, arm64_norm] at htr1
  apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
  refine bind_state ?_
  intro s_shim
  refine call_noPanic_extern (x := ())
    (F := wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗ ((sp0 - 176#64) ↦₆₄ w176) ∗
          ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool lim st s_shim ∗ stackAt (sp0 - 416#64) cmStack)
    hshim (by simp only [s_shim, wp_norm, arm64_norm])
    (by simp only [s_shim, wp_norm, arm64_norm, hrun1])
    (by simp only [s_shim, State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [s_shim, wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    dsimp only [s_shim] at hm ⊢
    simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc,
      emp_sepConj, State.mem_setMem] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  dsimp only [s_shim] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [wp_norm, arm64_norm, hsp1,
      h19_1, h21_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun hvm2 => SepWPp.pure_elim fun htr2 => ?_
  dsimp only [s_shim] at hvm2 htr2 ⊢
  rw [← A.pool_transport lim st _ sf2 hvm2]
  simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun2])
  refine call_noPanic_extern
    (x := ((encode (x.protoMsg parse)).length + 9, 1, st))
    (F := wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗ ((sp0 - 176#64) ↦₆₄ w176) ∗
          ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - allocHookStack))
    halloc (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun2])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    have hlay : RustLayoutOk ((encode (x.protoMsg parse)).length + 9) 1 :=
      ⟨⟨h_pos9, ⟨0, rfl⟩, by omega⟩, by decide⟩
    rw [stackAt_split_ge hle_alloc hbnd (sp0 - 416#64)] at hm
    dsimp only [rustCliAllocNoOomSpec]
    simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm, hsp2, h_add9_toNat, hlay, hfit_ser,
      and_self, pure_true, emp_sepConj] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf3 hpc3 hrun3 hsp3 ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
  simp only [wp_norm, arm64_norm, hsp2, h19_2, h20_2, h21_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2]
    at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
  dsimp only [rustCliAllocNoOomSpec]
  simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hpres3, hoom, _halign_ptr⟩ => ?_
  have htr3 : sf3.trace = s.trace := by
    have ht := hpres3.2.1
    simp only [wp_norm, arm64_norm, htr2] at ht
    exact ht
  have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  simp only [arm64_norm] at hoom hoom_beq
  let st' := M.stepEvents (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1) st
  have hfold_alloc :
      stackAt (sp0 - 416#64) allocHookStack ∗
        memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - allocHookStack) =
      stackAt (sp0 - 416#64) cmStack :=
    (stackAt_split_ge hle_alloc hbnd (sp0 - 416#64)).symm
  conv =>
    arg 4
    simp only [wp_norm, arm64_norm, hsp2, sepConj_assoc]
    rw [show A.pool lim (M.stepEvents (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1) st) sf3 ∗
        stackAt (sp0 - 416#64) allocHookStack ∗
        A.live (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) 1 ∗
        memRegion (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) ∗
        wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
          (sp0 - 288#64) (x.protoMsg parse) ∗
        (sp0 - 384#64) ↦₃₂ x.counter ∗ (sp0 - 380#64) ↦₃₂ x.previousCounter ∗
        (sp0 - 332#64) ↦₃₂ verW32 ∗ (sp0 - 176#64) ↦₆₄ w176 ∗
        (sp0 - 168#64) ↦₆₄ w168 ∗ (sp0 - 160#64) ↦₆₄ w160 ∗
        memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - allocHookStack) =
        memRegion (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) ∗
        (stackAt (sp0 - 416#64) allocHookStack ∗
          memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - allocHookStack)) ∗
        A.live (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) 1 ∗
        A.pool lim st' sf3 ∗
        wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
          (sp0 - 288#64) (x.protoMsg parse) ∗
        (sp0 - 384#64) ↦₃₂ x.counter ∗ (sp0 - 380#64) ↦₃₂ x.previousCounter ∗
        (sp0 - 332#64) ↦₃₂ verW32 ∗ (sp0 - 176#64) ↦₆₄ w176 ∗
        (sp0 - 168#64) ↦₆₄ w168 ∗ (sp0 - 160#64) ↦₆₄ w160 by sep_ac_rfl, hfold_alloc]
  rw [memRegion_split_one (sf3.readReg64 (Reg.gpr 0#5))
        ((encode (x.protoMsg parse)).length + 9) (by omega) (by omega)]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun b0 => ?_
  apply SepWPp.of_sepWP (mid := lsmpl.base 108)
  wp_steps_sync_pool (lsmpl.base 108)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun3])
  refine bind_state ?_
  intro s_el2
  refine call_noPanic_extern
    (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr,
      x.protoMsg parse⟩)
    (F := A.live (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) 1 ∗
          ((sf3.readReg64 (Reg.gpr 0#5)) ↦₈ versionByte x.messageVersion) ∗
          memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) ((encode (x.protoMsg parse)).length + 8) ∗
          A.pool lim st' s_el2 ∗
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗ ((sp0 - 160#64) ↦₆₄ 1#64) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack))
    hEncLen (by simp only [s_el2, wp_norm, arm64_norm])
    (by simp only [s_el2, wp_norm, arm64_norm, hrun3])
    (by simp only [s_el2, State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align])
    (by simp only [s_el2, wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    have hv : BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (verW32 <<< 4)) =
        versionByte x.messageVersion := by
      rw [← hver]; unfold versionByte currentVersion; bv_kernel
    dsimp only [s_el2] at hm ⊢
    rw [stackAt_split_ge hle_enc hbnd (sp0 - 416#64), hv] at hm
    rw [encodedLenBudgetSpec_pre_eq A.repAlloc _ _ (sp0 - 416#64)
          (by simp only [wp_norm, arm64_norm]) hfit
          (by simp only [wp_norm, arm64_norm, hsp3])]
    simp only [sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf4 hpc4 hrun4 hsp4 ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4⟩
  dsimp only [s_el2] at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
  simp only [wp_norm, arm64_norm, hsp3, h19_3, h20_3, h21_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3]
    at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
  simp only [encodedLenSpec, wp_norm, arm64_norm, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hvm4, hx0_4, htr4⟩ => ?_
  dsimp only [s_el2] at hvm4 htr4 ⊢
  rw [← A.pool_transport lim st' _ sf4 hvm4]
  simp only [wp_norm, arm64_norm, htr3] at htr4
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp3, sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_63).base + 440#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun4]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp4, hsp0_align, h19_4, h20_4, h21_4, h22_4, ne_eq,
      eq_false hoom, not_false_eq_true, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4,
      htr4, and_self]
  · rw [stackAt_split_ge hle_enc hbnd (sp0 - 416#64)]
    unfold SignalMessageNewGhost.serPrefix0
    simp only [wp_norm, arm64_norm, h22_4, st']
    change _ ⊢ _
    rw [← A.repAlloc_live,
        ← pack_serPrefix0 A.repAlloc sp0 (sf3.readReg64 (Reg.gpr 0#5)) x.messageVersion
            (encode (x.protoMsg parse)).length henc_lo henc_hi hoom]
    simp only [sepConj_assoc]
    exact entails_of_sep_focus (by sep_focus)

theorem new_alloc_ser_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (encodedLenSpec A.repAlloc))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr w176 w168 w160 : BitVec 64)
    (w384 w380 verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit_ser : FitsEvents M lim st (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1))
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 440#64)
      s
      (((sp0 - 384#64) ↦₃₂ w384) ∗
       ((sp0 - 380#64) ↦₃₂ w380) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       wireSignalMessageAt A.repAlloc
         (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       ((sp0 - 176#64) ↦₆₄ w176) ∗
       ((sp0 - 168#64) ↦₆₄ w168) ∗
       ((sp0 - 160#64) ↦₆₄ w160) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 ≠ 0#64 ∧
         sm.readReg64 .x23 = 1#64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            (sm.readReg64 .x22) x.serPrefix0 ∗
          A.pool lim
            (M.stepEvents (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_alloc_ser_wpp_placed_at (cmStack := computeMacStack) (by decide) (by decide) (by decide)
    h_shim h_alloc hEncLen x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr
    w176 w168 w160 w384 w380 verW32 hver hct_bound hpq_bound hfit_ser
    s hpc hrun hsp hsp_align hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_alloc_ser_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (encodedLenSpec A.repAlloc))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr w176 w168 w160 : BitVec 64)
    (w384 w380 verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit_ser : FitsEvents M lim st (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1))
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 440#64)
      s
      (((sp0 - 384#64) ↦₃₂ w384) ∗
       ((sp0 - 380#64) ↦₃₂ w380) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       wireSignalMessageAt A.repAlloc
         (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       ((sp0 - 176#64) ↦₆₄ w176) ∗
       ((sp0 - 168#64) ↦₆₄ w168) ∗
       ((sp0 - 160#64) ↦₆₄ w160) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 ≠ 0#64 ∧
         sm.readReg64 .x23 = 1#64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            (sm.readReg64 .x22) x.serPrefix0 ∗
          A.pool lim
            (M.stepEvents (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_alloc_ser_wpp_placed_at (cmStack := computeMacStackX) (by decide) (by decide) (by decide)
    h_shim h_alloc hEncLen x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr
    w176 w168 w160 w384 w380 verW32 hver hct_bound hpq_bound hfit_ser
    s hpc hrun hsp hsp_align hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29


end LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123BudgetAux
