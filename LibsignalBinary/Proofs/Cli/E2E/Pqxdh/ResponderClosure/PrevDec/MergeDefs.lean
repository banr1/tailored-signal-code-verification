/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ConstsMerge
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs

/-!
# Handshake `bytes::merge` Contract Definitions and Codec Bridges

Defines `bytesMerge3Stack` (`33120` B), `bytesMerge3RawSpec`, `bytesMerge3Spec`,
`bytesMerge3ProtoRawSpec`, and `bytesMerge3ProtoSpec` for
`prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]`, together with stack-splitting and
`LibsignalSpqrV1.Proto.mergeBytes` equivalence lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts

/-! ## `bytesMerge3Stack` (`33120` B) and `bytesMerge3Spec` -/

/-- Stack budget for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]`:
own frame `0xe0` (`224`) bytes plus `decodeVarint2StackX` (`32896` B) = `33120` B (`48 + bytesMergeStackX`). -/
abbrev bytesMerge3Stack : Nat := 0xe0 + decodeVarint2StackX

/-- Raw contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]`
(`888` B, `222` instructions). -/
def bytesMerge3RawSpec (A : RustAlloc) : Spec BytesMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMerge3Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]` in a loaded image `img`. -/
def bytesMerge3Spec (A : RustAlloc) (img : Obj.Image) : Spec BytesMergeGhost :=
  (bytesMerge3RawSpec A).inImage img

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]`
meets `bytesMerge3Spec A img` on `tripleRatchetProgAtExt img.base ext`. -/
def BytesMerge6OkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge6Name)
    (bytesMerge3Spec A img)

/-! ## Stack Layout and `MergePost3` / `MergePanic3` Lifting Lemmas -/

theorem stackAt_varint2_to_slice (sp0 : BitVec 64) :
    stackAt (sp0 - 224#64) decodeVarint2StackX =
      memRegion (sp0 - 33120#64) 48 ∗ stackAt (sp0 - 224#64) decodeVarintSliceStackX := by
  have h : sp0 - 224#64 - 32896#64 = sp0 - 33120#64 := by bv_omega
  rw [← h]
  exact stackAt_split_sub (sp0 - 224#64) 48 decodeVarintSliceStackX (by decide)

theorem stackAt_bytesMerge3_eq (sp0 : BitVec 64) :
    stackAt sp0 bytesMerge3Stack =
      memRegion (sp0 - 33120#64) 48 ∗ stackAt sp0 bytesMergeStackX :=
  stackAt_split_sub sp0 48 bytesMergeStackX (by decide)

theorem stackAt_bytesMerge3_entry (sp0 : BitVec 64) :
    stackAt sp0 bytesMerge3Stack =
      stackAt (sp0 - 224#64) decodeVarint2StackX ∗
      memRegion (sp0 - 224#64) 8 ∗
      memRegion (sp0 - 216#64) 48 ∗
      memRegion (sp0 - 168#64) 104 ∗
      cells (sp0 - 64#64) 8 := by
  rw [stackAt_bytesMerge3_eq sp0, stackAt_bytesMergeX_entry sp0, stackAt_varint2_to_slice sp0]
  ac_rfl

abbrev MergePost3 (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpec A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanic3 (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpec A).onPanic x s0 sf ∗ R)

theorem SepWPp.to_subroutineOutcome3 {prog : Program} {A : RustAlloc} {img : Obj.Image}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P (MergePost3 A x s0 R) (MergePanic3 A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (bytesMerge3Spec A img) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem SepWPp.lift_merge3 {prog : Program} {A : RustAlloc}
    {x : BytesMergeGhost} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergePostX A x s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))
      (MergePanicX A x s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))) :
    SepWPp prog (s0.readReg64 .lr) s (memRegion (s0.sp - 33120#64) 48 ∗ P)
      (MergePost3 A x s0 R) (MergePanic3 A x s0 R) := by
  intro F hm hL
  have hm' : s.mem ⊨ P ∗ (memRegion (s0.sp - 33120#64) 48 ∗ F) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h (memRegion (s0.sp - 33120#64) 48 ∗ F) hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, memRegion (s0.sp - 33120#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf, ?_, hsp, hcs⟩⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 33120#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmr
    have hp := hpost hmr'
    dsimp only [bytesMergeRawSpecX, bytesMerge3RawSpec] at hp ⊢
    rw [stackAt_bytesMerge3_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hp
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, memRegion (s0.sp - 33120#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf, ?_⟩)⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 33120#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmr
    have hp := hpanic hmr'
    dsimp only [bytesMergeRawSpecX, bytesMerge3RawSpec] at hp ⊢
    rw [← sepConj_assoc] at hp
    exact allowPanic_frame id hp
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## Equivalence with `LibsignalSpqrV1.Proto.mergeBytes` -/

/-- Bijection from `LibsignalSpqrV1.Proto.WireType` to `LibsignalProtoCodec.WireType`. -/
def protoWireTypeToCodec : LibsignalSpqrV1.Proto.WireType → WireType
  | .varint => .varint
  | .SixtyFourBit => .sixtyFourBit
  | .lengthDelimited => .lengthDelimited
  | .startGroup => .startGroup
  | .endGroup => .endGroup
  | .ThirtyTwoBit => .thirtyTwoBit

@[simp]
theorem protoWireTypeToCodec_toNat (wt : LibsignalSpqrV1.Proto.WireType) :
    BitVec.ofNat 8 (protoWireTypeToCodec wt).toNat = wt.toU32.setWidth 8 := by
  cases wt <;> rfl

theorem proto_takeExact_toOption (n : Nat) (bs : List (BitVec 8)) :
    (LibsignalSpqrV1.Proto.takeExact n bs).toOption =
      if bs.length < n then none else some (bs.take n, bs.drop n) := by
  induction n generalizing bs with
  | zero =>
    simp [LibsignalSpqrV1.Proto.takeExact, Except.toOption]
  | succ n ih =>
    cases bs with
    | nil =>
      simp [LibsignalSpqrV1.Proto.takeExact, Except.toOption]
    | cons b rest =>
      have hbind : (LibsignalSpqrV1.Proto.takeExact (n + 1) (b :: rest)).toOption =
          ((LibsignalSpqrV1.Proto.takeExact n rest).toOption).map (fun p => (b :: p.1, p.2)) := by
        simp only [LibsignalSpqrV1.Proto.takeExact]
        rcases LibsignalSpqrV1.Proto.takeExact n rest with _ | ⟨hd, tl⟩ <;> rfl
      rw [hbind, ih]
      by_cases hlt : rest.length < n
      · simp [hlt]
      · simp [hlt]

private theorem bitvec8_lt_0x80_iff (b : BitVec 8) :
    (b < 0x80#8) ↔ b.toNat ≤ 0x7F := by
  simp [BitVec.lt_def]; omega

private theorem bitvec8_ge_0x02_iff (b : BitVec 8) :
    (b ≥ 0x02#8) ↔ 0x02 ≤ b.toNat := by
  simp [BitVec.le_def]

theorem proto_decodeVarintAux_toOption (fuel idx : Nat) (acc : BitVec 64) (bs : List (BitVec 8))
    (hfuel : fuel + idx = 10) (hidx : idx < 10) :
    (LibsignalSpqrV1.Proto.decodeVarintAux fuel idx acc bs).toOption = decodeVarintAux idx acc bs := by
  induction fuel generalizing idx acc bs with
  | zero => omega
  | succ fuel ih =>
    cases bs with
    | nil =>
      simp [LibsignalSpqrV1.Proto.decodeVarintAux, decodeVarintAux, Except.toOption]
    | cons b rest =>
      have hshift : ((b &&& 0x7f#8).zeroExtend 64 <<< (idx * 7)) =
          ((b &&& 0x7F).zeroExtend 64 <<< (7 * idx)) := by
        rw [Nat.mul_comm]
        rfl
      by_cases h9 : idx = 9
      · subst h9
        have hfuel0 : fuel = 0 := by omega
        subst hfuel0
        simp only [LibsignalSpqrV1.Proto.decodeVarintAux, decodeVarintAux, beq_self_eq_true, ↓reduceIte, true_and]
        by_cases hb2 : 0x02 ≤ b.toNat
        · have hb2' : b ≥ 0x02#8 := (bitvec8_ge_0x02_iff b).mpr hb2
          simp [hb2, hb2', Except.toOption]
        · have hb2' : ¬ (b ≥ 0x02#8) := fun h => hb2 ((bitvec8_ge_0x02_iff b).mp h)
          have hb_lt : b.toNat ≤ 0x7F := by
            change ¬ (2 ≤ b.toNat) at hb2
            omega
          simp [hb2, hb2', hb_lt, Except.toOption]
      · have h9_beq : (idx == 9) = false := beq_false_of_ne h9
        simp only [LibsignalSpqrV1.Proto.decodeVarintAux, decodeVarintAux, h9_beq, Bool.false_eq_true, ↓reduceIte, h9, false_and, hshift]
        by_cases hlt : b.toNat ≤ 0x7F
        · have hlt' : b < 0x80#8 := (bitvec8_lt_0x80_iff b).mpr hlt
          simp [hlt, hlt', Except.toOption]
        · have hlt' : ¬ (b < 0x80#8) := fun h => hlt ((bitvec8_lt_0x80_iff b).mp h)
          simp only [hlt, hlt', ↓reduceIte]
          exact ih (idx + 1) (acc ||| ((b &&& 0x7F).zeroExtend 64 <<< (7 * idx))) rest (by omega) (by omega)

@[simp]
theorem proto_decodeVarint_toOption (bs : List (BitVec 8)) :
    (LibsignalSpqrV1.Proto.decodeVarint bs).toOption = decodeVarint bs :=
  proto_decodeVarintAux_toOption 10 0 0#64 bs rfl (by decide)

@[simp]
theorem proto_mergeBytes_toOption (wt : LibsignalSpqrV1.Proto.WireType) (bs : List (BitVec 8)) :
    (LibsignalSpqrV1.Proto.mergeBytes wt bs).toOption = mergeBytes (protoWireTypeToCodec wt) bs := by
  cases wt <;> simp only [LibsignalSpqrV1.Proto.mergeBytes, LibsignalSpqrV1.Proto.checkWireType, protoWireTypeToCodec, mergeBytes]
  case lengthDelimited =>
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
    rcases hdv : LibsignalSpqrV1.Proto.decodeVarint bs with err | ⟨len, rest⟩
    · have hdv' : decodeVarint bs = none := by
        rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint bs = some (len, rest) := by
        rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp only [hdv', Bind.bind, Except.bind, proto_takeExact_toOption]
  all_goals rfl

/-- Ghost input for `bytesMerge3ProtoRawSpec`, parameterized directly by `LibsignalSpqrV1.Proto.WireType`. -/
structure BytesMergeProtoGhost where
  wt : LibsignalSpqrV1.Proto.WireType
  valPtr : BitVec 64
  valCap : BitVec 64
  valBuf : BitVec 64
  valBs : List (BitVec 8)
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

def BytesMergeProtoGhost.toCodec (x : BytesMergeProtoGhost) : BytesMergeGhost :=
  { wt := protoWireTypeToCodec x.wt
    valPtr := x.valPtr
    valCap := x.valCap
    valBuf := x.valBuf
    valBs := x.valBs
    bufRef := x.bufRef
    slot := x.slot
    ptr := x.ptr
    bs := x.bs }

/-- Raw contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]`
stated directly in terms of `LibsignalSpqrV1.Proto.mergeBytes`. -/
def bytesMerge3ProtoRawSpec (A : RustAlloc) : Spec BytesMergeProtoGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.wt.toU32.setWidth 8 ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMerge3Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMerge3Stack ∗
      match (LibsignalSpqrV1.Proto.mergeBytes x.wt x.bs).toOption with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]`
in a loaded image `img` against `LibsignalSpqrV1.Proto.mergeBytes`. -/
def bytesMerge3ProtoSpec (A : RustAlloc) (img : Obj.Image) : Spec BytesMergeProtoGhost :=
  (bytesMerge3ProtoRawSpec A).inImage img

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]`
meets `bytesMerge3ProtoSpec A img` on `tripleRatchetProgAtExt img.base ext`. -/
def BytesMerge6ProtoOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge6Name)
    (bytesMerge3ProtoSpec A img)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  bytesMerge6Name
  bytesMerge3Stack
  bytesMerge3RawSpec
  bytesMerge3Spec
  BytesMerge6OkExt
  protoWireTypeToCodec
  BytesMergeProtoGhost
  bytesMerge3ProtoRawSpec
  bytesMerge3ProtoSpec
  BytesMerge6ProtoOkExt
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
