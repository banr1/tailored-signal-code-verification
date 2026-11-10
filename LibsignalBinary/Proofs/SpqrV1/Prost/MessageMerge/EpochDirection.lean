/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParams
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Verification of `EpochDirection::merge` (`0x4f544`, Block `299`)

Proves `prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>`
against `(epochDirectionMergeSpec A).inImage img` (`LibsignalSpqrV1.Proto.mergeMessage EpochDirectionPB.mergeField`)
and its relocatable `[LibsignalPlacement]` counterpart on Block `299`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

theorem skipBelow3_98_eq_stackAt_97 (sp : BitVec 64) :
    skipBelow3 sp 98 = stackAt (sp - 96#64) (skipField3Stack 97) :=
  congrArg (stackAt (sp - 96#64)) (rfl : 98 * 0x60 + decodeVarint2Stack = skipField3Stack 97)

/-! ## 1. Representation Predicates & Specification -/

/-- `Vec<u8>` at `v` whose capacity satisfies `BytesMergeCapOk cap remLen`. -/
def vecU8CapOkAt (A : RustAlloc) (v : BitVec 64) (remLen : Nat) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap remLen⌝ ∗ vecU8At A v cap ptr bs

/-- `EpochDirectionPB` at `a` (`56` bytes) whose `next` and `prev` `Vec<u8>` capacities satisfy
`BytesMergeCapOk _ remLen`. -/
def epochDirectionPBCapOkAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) : SepProp :=
  vecU8CapOkAt A a remLen d.next ∗
    vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
    ((a + 0x30#64) ↦₃₂ d.ctr) ∗
    memRegion (a + 0x34#64) 4

theorem vecU8CapOkAt_mono {A : RustAlloc} {v : BitVec 64} {rem1 rem2 : Nat} {bs : List (BitVec 8)}
    (hle : rem2 ≤ rem1) :
    vecU8CapOkAt A v rem1 bs ⊢ vecU8CapOkAt A v rem2 bs := by
  unfold vecU8CapOkAt
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => Entails.pure_left fun hcap => ?_
  have hcap2 : BytesMergeCapOk cap rem2 := bytesMergeCapOk_mono hcap hle
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun cap' => ∃∗ ptr', ⌜BytesMergeCapOk cap' rem2⌝ ∗ vecU8At A v cap' ptr' bs) cap)
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun ptr' => ⌜BytesMergeCapOk cap rem2⌝ ∗ vecU8At A v cap ptr' bs) ptr)
  rw [pure_sepConj_of_true hcap2]; exact Entails.refl _

theorem vecU8CapOkAt_entails_rustBytesVecAt (A : RustAlloc) (v : BitVec 64) (remLen : Nat) (bs : List (BitVec 8)) :
    vecU8CapOkAt A v remLen bs ⊢ rustBytesVecAt A v bs := by
  unfold vecU8CapOkAt rustBytesVecAt
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => Entails.pure_left fun _ => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun cap' => ∃∗ ptr', vecU8At A v cap' ptr' bs) cap)
  exact Entails.sepExists_intro (P := fun ptr' => vecU8At A v cap ptr' bs) ptr

theorem vecU8At_zero_entails_vecU8CapOkAt (A : RustAlloc) (v : BitVec 64) (remLen : Nat) :
    vecU8At A v 0#64 1#64 [] ⊢ vecU8CapOkAt A v remLen [] := by
  unfold vecU8CapOkAt
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  have hcap : BytesMergeCapOk 0#64 remLen := bytesMergeCapOk_zero
  simp only [hcap, pure_true, emp_sepConj]
  exact Entails.refl _

theorem epochDirectionPBCapOkAt_mono {A : RustAlloc} {a : BitVec 64} {rem1 rem2 : Nat} {d : EpochDirectionPB}
    (hle : rem2 ≤ rem1) :
    epochDirectionPBCapOkAt A a rem1 d ⊢ epochDirectionPBCapOkAt A a rem2 d := by
  unfold epochDirectionPBCapOkAt
  exact sepConj_mono (vecU8CapOkAt_mono hle)
    (sepConj_mono (vecU8CapOkAt_mono hle) (Entails.refl _))

theorem epochDirectionPBCapOkAt_entails_epochDirectionPBAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    epochDirectionPBCapOkAt A a remLen d ⊢ epochDirectionPBAt A a d := by
  unfold epochDirectionPBCapOkAt epochDirectionPBAt
  exact sepConj_mono (vecU8CapOkAt_entails_rustBytesVecAt A a remLen d.next)
    (sepConj_mono (vecU8CapOkAt_entails_rustBytesVecAt A (a + 0x18#64) remLen d.prev) (Entails.refl _))

theorem epochDirectionPBCapOkAt_entails_exists (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    epochDirectionPBCapOkAt A a remLen d ⊢ ∃∗ d' : EpochDirectionPB, epochDirectionPBAt A a d' :=
  Entails.trans (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A a remLen d) (Entails.sepExists_intro d)

/-- Stack budget for `prost::encoding::message::merge::<EpochDirection, &mut &[u8]>` (`0x4f544`):
own frame `0x60` (`96`) bytes plus `skipField3Stack 97` (`= skipField3Stack 98`). -/
abbrev epochDirectionMergeStack : Nat := skipField3Stack 98

/-- Ghost arguments of `prost::encoding::message::merge::<EpochDirection, &mut &[u8]>` (`0x4f544`). -/
structure EpochDirectionMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : EpochDirectionPB
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Contract of `prost::encoding::message::merge::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, &mut &[u8]>`
(`0x4f544`, 145 instructions) in terms of `LibsignalSpqrV1.Proto.mergeMessage EpochDirectionPB.mergeField`.
Bound `x.bs.length < 2 ^ 63` is discharged by caller `Epoch::merge` (`0x4db50`) from the input slice cursor invariant;
`epochDirectionPBCapOkAt` is discharged by `Epoch::merge` via `vecU8At_zero_entails_vecU8CapOkAt` when initializing
`None -> Some` (`cap = 0`) and via `epochDirectionPBCapOkAt_mono` on repeated merges into `Some`. -/
def epochDirectionMergeSpec (A : RustAlloc) : Spec EpochDirectionMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧ s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      epochDirectionPBCapOkAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp epochDirectionMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp epochDirectionMergeStack ∗
      match (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ epochDirectionPBCapOkAt A x.msgPtr rest.length m' ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : EpochDirectionPB, epochDirectionPBAt A x.msgPtr m') ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 2. Pure Model Step Lemmas for `EpochDirectionPB.mergeField` -/

theorem epochDirectionPB_mergeField_tag1 (m : EpochDirectionPB) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (EpochDirectionPB.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then (decodeVarint rest).map (fun (v, rest') => ({ m with ctr := v.truncate 32 }, rest')) else none := by
  unfold EpochDirectionPB.mergeField Proto.mergeUint32 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, beq_self_eq_true, ↓reduceIte]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem epochDirectionPB_mergeField_tag2 (m : EpochDirectionPB) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (EpochDirectionPB.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeBytes (codecWireTypeToProto iwt) rest).toOption.map (fun (v, rest') => ({ m with next := v }, rest')) := by
  unfold EpochDirectionPB.mergeField
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> rfl

theorem epochDirectionPB_mergeField_tag3 (m : EpochDirectionPB) (iwt : WireType) (rest : List (BitVec 8)) (depth' : Nat) :
    (EpochDirectionPB.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeBytes (codecWireTypeToProto iwt) rest).toOption.map (fun (v, rest') => ({ m with prev := v }, rest')) := by
  unfold EpochDirectionPB.mergeField
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> rfl

theorem epochDirectionPB_mergeField_other (m : EpochDirectionPB) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) (hne3 : tag ≠ 3) :
    (EpochDirectionPB.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold EpochDirectionPB.mergeField; simp only [hb1, hb2, hb3, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest' <;> {
    have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'; rw [← hsf']; rfl }

/-! ## 3. Symbolic Execution & Loop Invariant Proof -/

/-- Loop-header separation-logic bundle at `+0x0a0` (`0x4f5e4`). -/
def epochDirectionLoopPre (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : EpochDirectionPB) (bs cur : List (BitVec 8)) : SepProp :=
  epochDirectionPBCapOkAt A msgPtr cur.length m ∗
    memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool

/-- Error-exit separation-logic bundle (where the slice cursor has been collapsed to `memRegion slot 16 ∗ (ptr ↦ₛ bs)`
and `epochDirectionPBCapOkAt` to `epochDirectionPBAt`). -/
def epochDirectionErrFrame (A : RustAlloc) (s0 : State) (msgPtr bufRef slot ptr : BitVec 64)
    (m : EpochDirectionPB) (bs : List (BitVec 8)) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    epochDirectionPBAt A msgPtr m ∗ (bufRef ↦₆₄ slot) ∗
    memRegion slot 16 ∗ (ptr ↦ₛ bs) ∗ A.pool

theorem epochDirectionPBAt_entails_exists (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    epochDirectionPBAt A a d ⊢ ∃∗ d' : EpochDirectionPB, epochDirectionPBAt A a d' :=
  Entails.sepExists_intro d

/-- Shared exit from `+0x074` (`entry + 116#64`) when `x1 = err ≠ 0#64` owns `decodeErrorAtStackLen A err 0`. -/
theorem epochDirection_err0_ret_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {err : BitVec 64}
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64) (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  epochDirectionMerge_fetches b H 116 24
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_ret
  unfold WppPost epochDirectionMergeSpec
  simp only [hnone, stackAt_skipField3 _ 98 (by decide), epochDirectionErrFrame,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (epochDirectionPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps
  wp_done

/-- Shared exit from `+0x068` (`entry + 104#64`): calls `DecodeError::from` on `(s0.sp - 96#64, w)`
and returns at `+0x070..+0x088`. -/
theorem epochDirection_from_err_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb85c#64) (decodeErrorFromSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {w : BitVec 64}
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 104#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ w) ∗ memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  epochDirectionMerge_fetches b H 104 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffb85c#64)
  conv => arg 4; rw [skipBelow3_err s0.sp 98 (by decide), epochDirectionErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, w))
    (ret_pc := entry + 112#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp
  apply SepWPp.of_sepWP_ret
  unfold WppPost epochDirectionMergeSpec
  simp only [decodeErrorFromSpec, hnone, stackAt_skipField3 _ 98 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 98 (by decide)) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A _) (by sep_focus)
  apply SepWP.fold (epochDirectionPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48 s0.sp) (by sep_focus)
  wp_done

/-- Shared exit from `+0x224` (`entry + 548#64`): calls `DecodeError::push` on `(s0.sp - 96#64, err, 0)`
and returns at `+0x228..+0x240`. -/
theorem epochDirection_push_err_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb564#64) (decodeErrorPushSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {err : BitVec 64}
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 548#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 96#64)
    (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗
        epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  epochDirectionMerge_fetches b H 548 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffb564#64)
  conv => arg 4; rw [skipBelow3_err s0.sp 98 (by decide), epochDirectionErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, err, 0))
    (ret_pc := entry + 552#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by decide : 0 < 2 ^ 32)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp
  apply SepWPp.of_sepWP_ret
  unfold WppPost epochDirectionMergeSpec
  simp only [decodeErrorPushSpec, hnone, stackAt_skipField3 _ 98 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 98 (by decide)) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (epochDirectionPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48 s0.sp err) (by sep_focus)
  wp_done

/-- Step lemma for unknown field tags (`tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3`) at `+0x08c` (`entry + 140#64`):
calls `skip_field [local#3]` (`entry + 0xffffffffffffc630#64`) and either exits on error
or continues at the loop header `entry + 160#64` (`+0x0a0`). -/
theorem epochDirection_skip_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffc630#64) (skipField3Spec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32) (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 140#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @epochDirection_err0_ret_exit b A H x R s0
  epochDirectionMerge_fetches b H 140 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffc630#64) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_98_eq_stackAt_97 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 152#64) hSkipCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP (mid := entry + 116#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_98_eq_stackAt_97, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (Entails.of_eq (by dsimp only [epochDirectionErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_img (mid := entry + 160#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_98_eq_stackAt_97, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_mono hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (Entails.of_eq (by dsimp only [epochDirectionLoopPre]; ac_rfl))
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Shared exit for tag 1 (`ctr`) from `+0x204` (`entry + 516#64`): stores `err` (`X8`) at `[sp]`,
sets up `"EpochDirection"` / `"ctr"` descriptors, and falls through to `+0x224` (`entry + 548#64`). -/
theorem epochDirection_tag1_push_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb564#64) (decodeErrorPushSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {err : BitVec 64}
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 516#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = err) (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; have hpush_exit := @epochDirection_push_err_exit b A H hPushCall x R s0
  epochDirectionMerge_fetches b H 516 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 548#64)
  (conv => arg 4; rw [sepConj_memRegion_48_split_96]); apply SepWP.exists_elim; intro v_stk0
  wp_steps; wp_reach
  apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
  exact hpush_exit hnone herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hsp])
    ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Step lemma for tag 1 (`ctr`) at `+0x11c` (`entry + 284#64`) when `iwt ≠ .varint`. -/
theorem epochDirection_tag1_wt_err_step {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb85c#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb564#64) (decodeErrorPushSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 284#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have htag1_push := @epochDirection_tag1_push_exit b A H hPushCall x R s0; have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
  epochDirectionMerge_fetches b H 284 4; epochDirectionMerge_fetches b H 484 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffb85c#64)
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, memRegion_48_wtErr96 s0.sp, skipBelow3_err s0.sp 98 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
  wp_steps
  apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr rest.length m) (by sep_focus)
  wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, 0x8000000000000006#64))
    (ret_pc := entry + 512#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP (mid := entry + 516#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
  apply SepWP.fold (skipBelow3_err_entails s0.sp 98 (by decide)) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
  exact htag1_push hnone hve_ne hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Step lemma for tag 1 (`ctr`) at `+0x11c` (`entry + 284#64`) when `iwt = .varint`. -/
theorem epochDirection_tag1_varint_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb564#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffdf88#64) (decodeVarint2Spec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ctr := v.truncate 32 } x.bs rest')
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 284#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have htag1_push := @epochDirection_tag1_push_exit b A H hPushCall x R s0
  epochDirectionMerge_fetches b H 284 24; epochDirectionMerge_fetches b H 316 12
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffdf88#64) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 296#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply SepWPp.of_sepWP (mid := entry + 516#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
    exact htag1_push hnone hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPp.of_sepWP_img (mid := entry + 160#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, epochDirectionPBCapOkAt, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (@vecU8CapOkAt_mono A x.msgPtr rest.length rest'.length m.next hrest'_le) (by sep_focus); apply SepWP.fold (@vecU8CapOkAt_mono A (x.msgPtr + 0x18#64) rest.length rest'.length m.prev hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ctr := v.truncate 32 } x.bs rest') (by dsimp only [epochDirectionLoopPre, epochDirectionPBCapOkAt]; sep_entail)
    exact hcont v rest' _ hdv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

theorem vecU8At_entails_rustBytesVecAt (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ rustBytesVecAt A v bs := by
  unfold rustBytesVecAt
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun cap' => ∃∗ ptr', vecU8At A v cap' ptr' bs) cap)
  exact Entails.sepExists_intro (P := fun ptr' => vecU8At A v cap ptr' bs) ptr

theorem vecU8At_entails_vecU8CapOkAt {A : RustAlloc} {v cap ptr : BitVec 64} {remLen : Nat} {bs : List (BitVec 8)}
    (hcap : BytesMergeCapOk cap remLen) : vecU8At A v cap ptr bs ⊢ vecU8CapOkAt A v remLen bs := by
  unfold vecU8CapOkAt; refine Entails.trans ?_ (Entails.sepExists_intro (P := fun cap' => ∃∗ ptr', ⌜BytesMergeCapOk cap' remLen⌝ ∗ vecU8At A v cap' ptr' bs) cap)
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun ptr' => ⌜BytesMergeCapOk cap remLen⌝ ∗ vecU8At A v cap ptr' bs) ptr)
  simp only [hcap, pure_true, emp_sepConj]; exact Entails.refl _

theorem epochDirectionPBCapOkAt_unfold_next (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    epochDirectionPBCapOkAt A a remLen d =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap remLen⌝ ∗ vecU8At A a cap ptr d.next ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗ ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) := by
  conv => lhs; unfold epochDirectionPBCapOkAt; arg 1; unfold vecU8CapOkAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem epochDirectionPBCapOkAt_unfold_prev (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    epochDirectionPBCapOkAt A a remLen d =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap remLen⌝ ∗ vecU8CapOkAt A a remLen d.next ∗
        vecU8At A (a + 0x18#64) cap ptr d.prev ∗ ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) := by
  conv => lhs; unfold epochDirectionPBCapOkAt; arg 2; arg 1; unfold vecU8CapOkAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; ac_rfl

@[simp] theorem proto_mergeBytes_codec_toOption (iwt : WireType) (rest : List (BitVec 8)) :
    (Proto.mergeBytes (codecWireTypeToProto iwt) rest).toOption = mergeBytes iwt rest := by
  rw [proto_mergeBytes_toOption, protoWireTypeToCodec_codecWireTypeToProto]

theorem mergeBytes_length {iwt : WireType} {bs v r : List (BitVec 8)} (h : mergeBytes iwt bs = some (v, r)) : r.length ≤ bs.length :=
  (proto_mergeBytes_suffix (by rw [proto_mergeBytes_codec_toOption]; exact h)).1

theorem mergeBytes_suffix {iwt : WireType} {bs v r : List (BitVec 8)} (h : mergeBytes iwt bs = some (v, r)) : IsDropSuffix bs r :=
  (proto_mergeBytes_suffix (by rw [proto_mergeBytes_codec_toOption]; exact h)).2

/-- Step lemma for tag 2 (`next : Vec<u8>`) at `+0x104` (`entry + 260#64`). -/
theorem epochDirection_tag2_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb564#64) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffdbf8#64) ((bytesMerge3RawSpec A).inImage img))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit → HighCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with next := v } x.bs rest')
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : HighCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @epochDirection_push_err_exit b A H hPushCall x R s0
  epochDirectionMerge_fetches b H 260 24; epochDirectionMerge_fetches b H 448 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffdbf8#64) hinv
  conv => arg 4; rw [epochDirectionLoopPre, epochDirectionPBCapOkAt_unfold_next,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 98 (by decide) (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_cap; apply SepWP.exists_elim; intro v_ptr; apply SepWP.pure_elim; intro hcap
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_inImage (x := ⟨iwt, x.msgPtr, v_cap, v_ptr, m.next, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 272#64) hBytesCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by (conv => lhs; dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]); rfl)
    (⟨hrest_lt, hcap⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk v_cap rest.length) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP (mid := entry + 548#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_rustBytesVecAt A x.msgPtr v_cap v_ptr m.next) (by sep_focus); apply SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A (x.msgPtr + 0x18#64) rest.length m.prev) (by sep_focus)
    (conv => arg 4; rw [memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]); apply SepWP.exists_elim; intro v_stk0
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame, epochDirectionPBAt]; sep_entail)
    exact hpush_exit hnone hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPp.of_sepWP_img (mid := entry + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap'; apply SepWP.exists_elim; intro ptr'; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap'⟩
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapOkAt hcap') (by sep_focus); apply SepWP.fold (@vecU8CapOkAt_mono A (x.msgPtr + 0x18#64) rest.length rest'.length m.prev hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with next := v } x.bs rest') (by dsimp only [epochDirectionLoopPre, epochDirectionPBCapOkAt]; sep_entail)
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Step lemma for tag 3 (`prev : Vec<u8>`) at `+0x0ec` (`entry + 236#64`). -/
theorem epochDirection_tag3_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb564#64) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffdbf8#64) ((bytesMerge3RawSpec A).inImage img))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with prev := v } x.bs rest')
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 236#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @epochDirection_push_err_exit b A H hPushCall x R s0
  epochDirectionMerge_fetches b H 236 24; epochDirectionMerge_fetches b H 424 24; epochDirectionMerge_fetches b H 468 16
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffdbf8#64) hinv
  conv => arg 4; rw [epochDirectionLoopPre, epochDirectionPBCapOkAt_unfold_prev,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 98 (by decide) (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_cap; apply SepWP.exists_elim; intro v_ptr; apply SepWP.pure_elim; intro hcap
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_inImage (x := ⟨iwt, x.msgPtr + 0x18#64, v_cap, v_ptr, m.prev, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 248#64) hBytesCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by (conv => lhs; dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]); rfl)
    (⟨hrest_lt, hcap⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk v_cap rest.length) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP (mid := entry + 548#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A x.msgPtr rest.length m.next) (by sep_focus); apply SepWP.fold (vecU8At_entails_rustBytesVecAt A (x.msgPtr + 0x18#64) v_cap v_ptr m.prev) (by sep_focus)
    (conv => arg 4; rw [memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]); apply SepWP.exists_elim; intro v_stk0
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame, epochDirectionPBAt]; sep_entail)
    exact hpush_exit hnone hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPp.of_sepWP_img (mid := entry + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap'; apply SepWP.exists_elim; intro ptr'; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap'⟩
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapOkAt hcap') (by sep_focus); apply SepWP.fold (@vecU8CapOkAt_mono A x.msgPtr rest.length rest'.length m.next hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with prev := v } x.bs rest') (by dsimp only [epochDirectionLoopPre, epochDirectionPBCapOkAt]; sep_entail)
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Loop exit lemma at `+0x0a0` (`entry + 160#64`) when `cur.length ≤ limit`. -/
theorem epochDirection_loop_le_exit {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb85c#64) (decodeErrorFromSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin EpochDirectionPB.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    epochDirectionMerge_fetches b H 160 12; epochDirectionMerge_fetches b H 328 32
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP_ret; unfold WppPost epochDirectionMergeSpec
    simp only [hsome, stackAt_skipField3 _ 98 (by decide), epochDirectionLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps; wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @epochDirection_from_err_exit b A H hFromCall x R s0
    epochDirectionMerge_fetches b H 160 12; epochDirectionMerge_fetches b H 328 4; epochDirectionMerge_fetches b H 408 16; epochDirectionMerge_fetches b H 72 8
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 104#64)
    conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Loop key-decoding step at `+0x0a0` (`entry + 160#64`) when `¬ cur.length ≤ limit`. -/
theorem epochDirection_decode_key_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb85c#64) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffdf88#64) (decodeVarint2Spec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin EpochDirectionPB.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 212#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : HighCalleeSaved s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  have herr0_exit := @epochDirection_err0_ret_exit b A H x R s0; have hfrom_exit := @epochDirection_from_err_exit b A H hFromCall x R s0
  epochDirectionMerge_fetches b H 160 52; epochDirectionMerge_fetches b H 360 48; epochDirectionMerge_fetches b H 72 8
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffdf88#64) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 180#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := entry + 116#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm1
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP (mid := entry + 104#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 := pointsTo64_memRegion32_entails_40 s0.sp key; rw [← bv_sub_add_lit s0.sp 96 8] at h40; apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP (mid := entry + 104#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64); rw [← bv_sub_add_lit s0.sp 96 8] at h40; apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := entry + 104#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPp.of_sepWP_img (mid := entry + 212#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (epochDirectionPBCapOkAt_mono hrest_le_cur) (by sep_focus); wp_steps; wp_reach; intro hinvm
          apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (by dsimp only [epochDirectionLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Main loop induction for `EpochDirection::merge` (`0x4f544`) at `+0x0a0` (`entry + 160#64`). -/
theorem epochDirection_loop_ok {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb85c#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb564#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffdf88#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffc630#64) (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffdbf8#64) ((bytesMerge3RawSpec A).inImage img))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : EpochDirectionPB) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin EpochDirectionPB.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 160#64 →
      s.status = .Running → s.sp = s0.sp - 96#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s → ImgCallInv img s →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s m rest} => @epochDirection_tag1_varint_step b img A H hPushCall hVarintCall x R s0 s m rest limit
  have htag1_wt_err := @epochDirection_tag1_wt_err_step b A H hFromCall hPushCall x R s0
  have htag2_step := fun {s m rest iwt} => @epochDirection_tag2_step b img A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have htag3_step := fun {s m rest iwt} => @epochDirection_tag3_step b img A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @epochDirection_skip_step b img A H hSkipCall x R s0 s m rest tag iwt limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs _
    exact epochDirection_loop_le_exit hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact epochDirection_loop_le_exit hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine epochDirection_decode_key_step hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' hinv'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97) protoPrefixStep_epochDirectionPB_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [epochDirectionPB_mergeField_tag1] at hloop_ok
        epochDirectionMerge_fetches b H 212 8
        generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
        apply SepWPp.of_sepWP_img (mid := entry + 284#64) hinv'; wp_steps; wp_reach; intro hinv'
        by_cases hiwt : iwt = .varint
        · subst hiwt
          have hnone_dv : decodeVarint rest = none →
              (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro hdv; simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_none]
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf hnone_dv
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin EpochDirectionPB.mergeField (rest'.length - limit) { m with ctr := v.truncate 32 } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_some]
          exact ih { m with ctr := v.truncate 32 } rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
        · have hnone_wt : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none]
          exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf hnone_wt
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [epochDirectionPB_mergeField_tag2, proto_mergeBytes_codec_toOption] at hloop_ok
          epochDirectionMerge_fetches b H 212 16
          generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
          apply SepWPp.of_sepWP_img (mid := entry + 260#64) hinv'; wp_steps; wp_reach; intro hinv'
          have hnone_mb : mergeBytes iwt rest = none →
              (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
          refine htag2_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
            (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
          have hres_next : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin EpochDirectionPB.mergeField (rest'.length - limit) { m with next := v } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hmb, Option.map_some]
          exact ih { m with next := v } rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [epochDirectionPB_mergeField_tag3, proto_mergeBytes_codec_toOption] at hloop_ok
            epochDirectionMerge_fetches b H 212 24
            generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
            apply SepWPp.of_sepWP_img (mid := entry + 236#64) hinv'; wp_steps; wp_reach; intro hinv'
            have hnone_mb : mergeBytes iwt rest = none →
                (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
            refine htag3_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
              (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
            have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hres_next : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin EpochDirectionPB.mergeField (rest'.length - limit) { m with prev := v } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            exact ih { m with prev := v } rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
          · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
            obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
            have hb3_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 3#32) = true := by simp only [bne, hb3_1, Bool.not_false]
            have hb3_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 3#32) = true := by simp only [bne, hb3_2, Bool.not_false]
            rw [epochDirectionPB_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3] at hloop_ok
            epochDirectionMerge_fetches b H 212 24
            generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
            apply SepWPp.of_sepWP_img (mid := entry + 140#64) hinv'; wp_steps; wp_reach; intro hinv'
            have hnone_sf : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = none →
                (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
            refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
            have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hres_next : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin EpochDirectionPB.mergeField (rest'.length - limit) m rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              rw [hres_cur, hloop_ok, hsf]; rfl
            exact ih m rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''

/-- Contract-parameterized verification of `prost::encoding::message::merge::<EpochDirection, &mut &[u8]>` (`0x4f544`). -/
theorem epochDirectionMerge_ok_of_contracts {b : BitVec 64} {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb85c#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffb564#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffdf88#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffc630#64) (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName + 0xffffffffffffdbf8#64) ((bytesMerge3RawSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b H) ((libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName) ((epochDirectionMergeSpec A).inImage img) := by
  apply subroutine_ok_inImage_of_withImgProp; unfold withImgProp epochDirectionMergeSpec; wpp_init x s0
  apply SepWPp.elim_imgCallInvProp; intro hinv0; replace hpc : s0.pc = (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName := hpc
  conv => arg 6; ext sf P_f; simp only [epochDirectionMergeSpec, sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp _ _ _ _ (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0)
  have herr0_exit := @epochDirection_err0_ret_exit b A H x R s0; have hfrom_exit := @epochDirection_from_err_exit b A H hFromCall x R s0
  have hloop := fun {limit n m cur s} hlim_lt =>
    @epochDirection_loop_ok b img A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall x R s0 limit hsp_align h hlim_lt n m cur s
  epochDirectionMerge_fetches b H 0 104
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr epochDirectionMergeName = entry; examples_hide_fetches
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by revert h_1'; bv_bits
    apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffdf88#64) hinv0
    (conv => arg 4; rw [epochDirectionMergeStack, stackAt_skipField3 s0.sp 98 (by decide), skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp; wp_steps; wp_reach; intro hinv0
    refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := entry + 48#64) hVarintCall hinv0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl) h (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP (mid := entry + 116#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
      exact herr0_exit hnone hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0; have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
        apply SepWPp.of_sepWP (mid := entry + 104#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt; have hsub := bv_len_sub_limit hlt_len; have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
          have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf; (conv => rhs; rw [hsuf, List.drop_drop]); exact congrArg (List.drop · x.bs) (by omega)
        have hres0 : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            (mergeLoopBin EpochDirectionPB.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
          simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
          rcases mergeLoopBin EpochDirectionPB.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_img (mid := entry + 160#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (epochDirectionPBCapOkAt_mono hrest0_le) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]); wp_steps; wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0) (by rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hlim_lt (Nat.le_refl _) hrest0_le hrest0_suf hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]; cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by rw [← hbne1]; congr 2; bv_bits
    have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]; cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP (mid := entry + 104#64)
    (conv => arg 4; rw [epochDirectionMergeStack, stackAt_skipField3 s0.sp 98 (by decide), sliceCursorAt, memRegion_48_wtErr96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp; apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0; wp_steps
    apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus); wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- `prost::encoding::message::merge::<EpochDirection, &mut &[u8]>` (`0x4f544`) meets
`(epochDirectionMergeSpec A).inImage img` on `tripleRatchetProgAtExt img.base ext` given `((bytesMerge3RawSpec A).inImage img)`. -/
theorem epochDirectionMerge_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name) ((bytesMerge3RawSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr epochDirectionMergeName) ((epochDirectionMergeSpec A).inImage img) := by
  refine epochDirectionMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_
  · rw [fnAddr_offset_eq_H (name := epochDirectionMergeName) (callee := decodeErrorFromName)]; exact hC.decode_error_from
  · rw [fnAddr_offset_eq_H (name := epochDirectionMergeName) (callee := decodeErrorPushName)]; exact hC.decode_error_push
  · rw [fnAddr_offset_eq_H (name := epochDirectionMergeName) (callee := Varint.decodeVarint2Name)]; exact decodeVarint2_ok_ext hC
  · rw [fnAddr_offset_eq_H (name := epochDirectionMergeName) (callee := skipField3Name)]; exact skipField3_ok_ext hC
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr epochDirectionMergeName + 0xffffffffffffdbf8#64 = (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff epochDirectionMergeName)) + 0xffffffffffffdbf8#64 = img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff bytesMerge3Name)
      rw [epochDirectionMerge_fnOff, bytesMerge3_fnOff]; bv_omega
    rw [h_off]; exact hBytes

/-- End-to-end `.inImage img` contract for `EpochDirection::merge` discharging `hBytes` via `bytes_merge_3_ok_ext`. -/
theorem epochDirectionMerge_ok_ext_of_bytes_contracts {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) (hBC : BytesMerge3Contracts img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr epochDirectionMergeName) ((epochDirectionMergeSpec A).inImage img) :=
  epochDirectionMerge_ok_ext hC hBC.ok_ext

/-! ## 4. Relocatable `[LibsignalPlacement]` Verification (Block `299`) -/

theorem epochDirection_err0_ret_exit_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {err : BitVec 64}
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_299).base + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64) (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_ret
  unfold WppPost epochDirectionMergeSpec
  simp only [hnone, stackAt_skipField3 _ 98 (by decide), epochDirectionErrFrame,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (epochDirectionPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps
  wp_done

theorem epochDirection_from_err_exit_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {w : BitVec 64}
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_299).base + 104#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ w) ∗ memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [skipBelow3_err s0.sp 98 (by decide), epochDirectionErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, w))
    (ret_pc := (blkPl_299).base + 112#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp
  apply SepWPp.of_sepWP_ret
  unfold WppPost epochDirectionMergeSpec
  simp only [decodeErrorFromSpec, hnone, stackAt_skipField3 _ 98 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 98 (by decide)) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A _) (by sep_focus)
  apply SepWP.fold (epochDirectionPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48 s0.sp) (by sep_focus)
  wp_done

theorem epochDirection_push_err_exit_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {err : BitVec 64}
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_299).base + 548#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 96#64)
    (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗
        epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [skipBelow3_err s0.sp 98 (by decide), epochDirectionErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, err, 0))
    (ret_pc := (blkPl_299).base + 552#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by decide : 0 < 2 ^ 32)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp
  apply SepWPp.of_sepWP_ret
  unfold WppPost epochDirectionMergeSpec
  simp only [decodeErrorPushSpec, hnone, stackAt_skipField3 _ 98 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 98 (by decide)) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (epochDirectionPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48 s0.sp err) (by sep_focus)
  wp_done

theorem epochDirection_skip_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 263) (skipField3Spec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32) (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_299).base + 140#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @epochDirection_err0_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_98_eq_stackAt_97 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep_lscro (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_299).base + 152#64) hSkipCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP (mid := (blkPl_299).base + 116#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_98_eq_stackAt_97, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (Entails.of_eq (by dsimp only [epochDirectionErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_98_eq_stackAt_97, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_mono hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (Entails.of_eq (by dsimp only [epochDirectionLoopPre]; ac_rfl))
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

theorem epochDirection_tag1_push_exit_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {err : BitVec 64}
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_299).base + 516#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = err) (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; have hpush_exit := @epochDirection_push_err_exit_placed _ A H hPushCall x R s0
  apply SepWPp.of_sepWP (mid := (blkPl_299).base + 548#64)
  (conv => arg 4; rw [sepConj_memRegion_48_split_96]); apply SepWP.exists_elim; intro v_stk0
  wp_steps; wp_reach
  apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
  exact hpush_exit hnone herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hsp])
    ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem epochDirection_tag1_wt_err_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hpc : s.pc = (blkPl_299).base + 284#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have htag1_push := @epochDirection_tag1_push_exit_placed _ A H hPushCall x R s0; have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
  apply SepWPp.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, memRegion_48_wtErr96 s0.sp, skipBelow3_err s0.sp 98 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
  wp_steps
  apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr rest.length m) (by sep_focus)
  wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, 0x8000000000000006#64))
    (ret_pc := (blkPl_299).base + 512#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP (mid := (blkPl_299).base + 516#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
  apply SepWP.fold (skipBelow3_err_entails s0.sp 98 (by decide)) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
  exact htag1_push hnone hve_ne hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem epochDirection_tag1_varint_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ctr := v.truncate 32 } x.bs rest')
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_299).base + 284#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have htag1_push := @epochDirection_tag1_push_exit_placed _ A H hPushCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep_lscro (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_299).base + 296#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply SepWPp.of_sepWP (mid := (blkPl_299).base + 516#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
    exact htag1_push hnone hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, epochDirectionPBCapOkAt, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (@vecU8CapOkAt_mono A x.msgPtr rest.length rest'.length m.next hrest'_le) (by sep_focus); apply SepWP.fold (@vecU8CapOkAt_mono A (x.msgPtr + 0x18#64) rest.length rest'.length m.prev hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ctr := v.truncate 32 } x.bs rest') (by dsimp only [epochDirectionLoopPre, epochDirectionPBCapOkAt]; sep_entail)
    exact hcont v rest' _ hdv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

theorem epochDirection_tag2_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit → HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with next := v } x.bs rest')
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_299).base + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @epochDirection_push_err_exit_placed _ A H hPushCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [epochDirectionLoopPre, epochDirectionPBCapOkAt_unfold_next,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 98 (by decide) (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_cap; apply SepWP.exists_elim; intro v_ptr; apply SepWP.pure_elim; intro hcap
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := ⟨iwt, x.msgPtr, v_cap, v_ptr, m.next, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_299).base + 272#64) hBytesCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by (conv => lhs; dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]); rfl)
    (⟨hrest_lt, hcap⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk v_cap rest.length) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP (mid := (blkPl_299).base + 548#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_rustBytesVecAt A x.msgPtr v_cap v_ptr m.next) (by sep_focus); apply SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A (x.msgPtr + 0x18#64) rest.length m.prev) (by sep_focus)
    (conv => arg 4; rw [memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]); apply SepWP.exists_elim; intro v_stk0
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame, epochDirectionPBAt]; sep_entail)
    exact hpush_exit hnone hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap'; apply SepWP.exists_elim; intro ptr'; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap'⟩
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapOkAt hcap') (by sep_focus); apply SepWP.fold (@vecU8CapOkAt_mono A (x.msgPtr + 0x18#64) rest.length rest'.length m.prev hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with next := v } x.bs rest') (by dsimp only [epochDirectionLoopPre, epochDirectionPBCapOkAt]; sep_entail)
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

theorem epochDirection_tag3_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with prev := v } x.bs rest')
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_299).base + 236#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @epochDirection_push_err_exit_placed _ A H hPushCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [epochDirectionLoopPre, epochDirectionPBCapOkAt_unfold_prev,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 98 (by decide) (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_cap; apply SepWP.exists_elim; intro v_ptr; apply SepWP.pure_elim; intro hcap
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := ⟨iwt, x.msgPtr + 0x18#64, v_cap, v_ptr, m.prev, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_299).base + 248#64) hBytesCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by (conv => lhs; dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]); rfl)
    (⟨hrest_lt, hcap⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk v_cap rest.length) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP (mid := (blkPl_299).base + 548#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A x.msgPtr rest.length m.next) (by sep_focus); apply SepWP.fold (vecU8At_entails_rustBytesVecAt A (x.msgPtr + 0x18#64) v_cap v_ptr m.prev) (by sep_focus)
    (conv => arg 4; rw [memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]); apply SepWP.exists_elim; intro v_stk0
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame, epochDirectionPBAt]; sep_entail)
    exact hpush_exit hnone hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap'; apply SepWP.exists_elim; intro ptr'; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap'⟩
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapOkAt hcap') (by sep_focus); apply SepWP.fold (@vecU8CapOkAt_mono A x.msgPtr rest.length rest'.length m.next hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with prev := v } x.bs rest') (by dsimp only [epochDirectionLoopPre, epochDirectionPBCapOkAt]; sep_entail)
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

theorem epochDirection_loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin EpochDirectionPB.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_299).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    apply SepWPp.of_sepWP_ret; unfold WppPost epochDirectionMergeSpec
    simp only [hsome, stackAt_skipField3 _ 98 (by decide), epochDirectionLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps; wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @epochDirection_from_err_exit_placed _ A H hFromCall x R s0
    apply SepWPp.of_sepWP (mid := (blkPl_299).base + 104#64)
    conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Placed loop key-decoding step at `+0x0a0` (`(blkPl_299).base + 160#64`) when `¬ cur.length ≤ limit`. -/
theorem epochDirection_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 s : State} {m : EpochDirectionPB} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin EpochDirectionPB.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_299).base + 212#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_299).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  have herr0_exit := @epochDirection_err0_ret_exit_placed _ A H x R s0; have hfrom_exit := @epochDirection_from_err_exit_placed _ A H hFromCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_keep_lscro (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := (blkPl_299).base + 180#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := (blkPl_299).base + 116#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm1
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP (mid := (blkPl_299).base + 104#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 := pointsTo64_memRegion32_entails_40 s0.sp key; rw [← bv_sub_add_lit s0.sp 96 8] at h40; apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP (mid := (blkPl_299).base + 104#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64); rw [← bv_sub_add_lit s0.sp 96 8] at h40; apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := (blkPl_299).base + 104#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr cur.length m) (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach
          apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 212#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (epochDirectionPBCapOkAt_mono hrest_le_cur) (by sep_focus); wp_steps; wp_reach; intro hinvm
          apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (by dsimp only [epochDirectionLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Placed main loop induction for `EpochDirection::merge` (Block `299`) at `+0x0a0` (`(blkPl_299).base + 160#64`). -/
theorem epochDirection_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 263) (skipField3Spec A))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : EpochDirectionMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : EpochDirectionPB) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin EpochDirectionPB.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_299).base + 160#64 →
      s.status = .Running → s.sp = s0.sp - 96#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
        (epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s m rest} => @epochDirection_tag1_varint_step_placed _ A H hPushCall hVarintCall x R s0 s m rest limit
  have htag1_wt_err := @epochDirection_tag1_wt_err_step_placed _ A H hFromCall hPushCall x R s0
  have htag2_step := fun {s m rest iwt} => @epochDirection_tag2_step_placed _ A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have htag3_step := fun {s m rest iwt} => @epochDirection_tag3_step_placed _ A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @epochDirection_skip_step_placed _ A H hSkipCall x R s0 s m rest tag iwt limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs _
    exact epochDirection_loop_le_exit_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact epochDirection_loop_le_exit_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine epochDirection_decode_key_step_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' hinv'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97) protoPrefixStep_epochDirectionPB_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [epochDirectionPB_mergeField_tag1] at hloop_ok
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 284#64) hinv'; wp_steps; wp_reach; intro hinv'
        by_cases hiwt : iwt = .varint
        · subst hiwt
          have hnone_dv : decodeVarint rest = none →
              (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro hdv; simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_none]
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf hnone_dv
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv; have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin EpochDirectionPB.mergeField (rest'.length - limit) { m with ctr := v.truncate 32 } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_some]
          exact ih { m with ctr := v.truncate 32 } rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
        · have hnone_wt : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none]
          exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf hnone_wt
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [epochDirectionPB_mergeField_tag2, proto_mergeBytes_codec_toOption] at hloop_ok
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 260#64) hinv'; wp_steps; wp_reach; intro hinv'
          have hnone_mb : mergeBytes iwt rest = none →
              (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
          refine htag2_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
            (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
          have hres_next : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin EpochDirectionPB.mergeField (rest'.length - limit) { m with next := v } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hmb, Option.map_some]
          exact ih { m with next := v } rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [epochDirectionPB_mergeField_tag3, proto_mergeBytes_codec_toOption] at hloop_ok
            apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 236#64) hinv'; wp_steps; wp_reach; intro hinv'
            have hnone_mb : mergeBytes iwt rest = none →
                (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
            refine htag3_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
              (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
            have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hres_next : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin EpochDirectionPB.mergeField (rest'.length - limit) { m with prev := v } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            exact ih { m with prev := v } rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
          · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
            obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
            have hb3_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 3#32) = true := by simp only [bne, hb3_1, Bool.not_false]
            have hb3_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 3#32) = true := by simp only [bne, hb3_2, Bool.not_false]
            rw [epochDirectionPB_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3] at hloop_ok
            apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 140#64) hinv'; wp_steps; wp_reach; intro hinv'
            have hnone_sf : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = none →
                (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
            refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv'
            have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hres_next : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin EpochDirectionPB.mergeField (rest'.length - limit) m rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              rw [hres_cur, hloop_ok, hsf]; rfl
            exact ih m rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''

/-- Contract-parameterized `[LibsignalPlacement]` verification of `EpochDirection::merge` (Block `299`). -/
theorem epochDirectionMerge_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 263) (skipField3Spec A))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A))) :
    subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (blkPl_299).base (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp; unfold withLscroProp epochDirectionMergeSpec; wpp_init x s0
  apply SepWPp.elim_lscroProp; intro hinv0; replace hpc : s0.pc = (blkPl_299).base := hpc
  conv => arg 6; ext sf P_f; simp only [epochDirectionMergeSpec, sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp _ _ _ _ (WppPost (epochDirectionMergeSpec A) x R s0) (WppPanic R s0)
  have herr0_exit := @epochDirection_err0_ret_exit_placed _ A H x R s0; have hfrom_exit := @epochDirection_from_err_exit_placed _ A H hFromCall x R s0
  have hloop := fun {limit n m cur s} hlim_lt =>
    @epochDirection_loop_ok_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall x R s0 limit hsp_align h hlim_lt n m cur s
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by revert h_1'; bv_bits
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
    (conv => arg 4; rw [epochDirectionMergeStack, stackAt_skipField3 s0.sp 98 (by decide), skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp; wp_steps; wp_reach; intro hinv0
    refine SepWPp.call_frame_keep_lscro (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := (blkPl_299).base + 48#64) hVarintCall hinv0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl) h (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP (mid := (blkPl_299).base + 116#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
      exact herr0_exit hnone hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0; have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
        apply SepWPp.of_sepWP (mid := (blkPl_299).base + 104#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt; have hsub := bv_len_sub_limit hlt_len; have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
          have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf; (conv => rhs; rw [hsuf, List.drop_drop]); exact congrArg (List.drop · x.bs) (by omega)
        have hres0 : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            (mergeLoopBin EpochDirectionPB.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
          simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
          rcases mergeLoopBin EpochDirectionPB.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus); apply SepWP.fold (epochDirectionPBCapOkAt_mono hrest0_le) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]); wp_steps; wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' := epochDirectionLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0) (by rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hlim_lt (Nat.le_refl _) hrest0_le hrest0_suf hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]; cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by rw [← hbne1]; congr 2; bv_bits
    have hnone : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]; cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP (mid := (blkPl_299).base + 104#64)
    (conv => arg 4; rw [epochDirectionMergeStack, stackAt_skipField3 s0.sp 98 (by decide), sliceCursorAt, memRegion_48_wtErr96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp; apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0; wp_steps
    apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus); wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 96#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 98 ∗ epochDirectionErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs) (by dsimp only [epochDirectionErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

end CryptoVerification.SpqrV1.Prost.MessageMerge
