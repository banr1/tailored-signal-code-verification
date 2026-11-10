/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafVarint -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafReserve -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome

@[expose] public section

set_option autoImplicit false

/-!
# Leaf Callee Specifications for Inlined `SessionStructure::decode`

Symbol names, stack budgets, and callee specifications (`skipField3Spec`, `SkipField6OkExtX`,
`GrowOneMessageKeyOkExtX`) for the leaf routines invoked by the handshake `SessionStructure::decode`
loop (`decode_varint [local#5]`, `skip_field [local#6]`, `RawVec<MessageKey>::grow_one`, and
`do_reserve_and_handle [local#10]`).
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
open Proofs.libsignal.Stage1X

/-- `prost::encoding::skip_field::<&mut &[u8]> [local#6]` (105 instructions, `420B`). -/
abbrev skipField6Name : String :=
  "prost::encoding::skip_field::<&mut &[u8]> [local#5]"

theorem skipField6_fnOff :
    libsignalSessionCode.fnOff skipField6Name =
      num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#5]") :=
  (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#5]")

/-- `<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one`
(26 instructions, shared at the same offset as `growOneChainName`). -/
abbrev growOneMessageKeyName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one"

/-- Stack budget for `prost::encoding::skip_field::<&mut &[u8]>` at recursion budget `depth`
under Regime A (`decodeVarint2StackX`). -/
abbrev skipField3Stack (depth : Nat) : Nat :=
  (depth + 1) * 0x60 + decodeVarint2StackX

/-- Contract of `prost::encoding::skip_field::<&mut &[u8]>` in terms of
`LibsignalProtoCodec.skipField` under Regime A (`skipField3Stack`). -/
def skipField3Spec (A : RustAlloc) : Spec SkipFieldGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 x.depth ∧ x.depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipField3Stack x.depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipField3Stack x.depth) ∗
      match skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Case-restricted specification for `skip_field` at fixed recursion budget `depth`. -/
def skipField3SpecAt (A : RustAlloc) (depth : Nat) (P : SkipFieldGhost → Prop) :
    Spec SkipFieldGhost where
  pre := fun x s =>
    ⌜P x ∧ x.depth = depth ∧
      (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.tag ∧ x.tag < 2 ^ 32 ∧
      s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = BitVec.ofNat 32 depth ∧ depth < 2 ^ 32 ∧
      x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp (skipField3Stack depth)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp (skipField3Stack depth) ∗
      match skipField (2 * x.bs.length + 2) depth x.tag x.wt x.bs with
      | some rest =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack region below the 96-byte frame of `skip_field` at recursion budget `depth`. -/
abbrev skipBelow3 (sp : BitVec 64) (depth : Nat) : SepProp :=
  stackAt (sp - 96#64) (depth * 0x60 + decodeVarint2StackX)

private theorem bv_sub_add_96 (sp v : BitVec 64) :
    sp - 96#64 = sp - (v + 96#64) + v := by bv_lin

private theorem bv_sub_96_sub (sp v : BitVec 64) :
    sp - 96#64 - v = sp - (v + 96#64) := by bv_lin

private theorem bv_sub_96_add_cancel (sp u w : BitVec 64) :
    sp - 96#64 - w = sp - 96#64 - (u + w) + u := by bv_lin

theorem stackAt_skipField3 (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    stackAt sp (skipField3Stack depth) =
      (∃∗ v19 : BitVec 64, ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64,
        ∃∗ v22 : BitVec 64, ∃∗ v_lr : BitVec 64, ∃∗ v_fp : BitVec 64,
        skipBelow3 sp depth ∗
          memRegion (sp - 96#64) 48 ∗
          ((sp - 48#64) ↦₆₄ v_fp) ∗ ((sp - 40#64) ↦₆₄ v_lr) ∗
          ((sp - 32#64) ↦₆₄ v22) ∗ ((sp - 24#64) ↦₆₄ v21) ∗
          ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v19)) := by
  simp only [stackAt, skipBelow3]
  have hlen : skipField3Stack depth = (depth * 0x60 + decodeVarint2StackX) + 96 := by
    simp only [skipField3Stack]; omega
  have hbound : skipField3Stack depth ≤ 2 ^ 64 := by
    simp only [skipField3Stack, decodeVarint2StackX, decodeVarintSlowStackX,
      decodeErrorHookStackX, extHookStack]
    omega
  have hbit : BitVec.ofNat 64 (skipField3Stack depth) =
      BitVec.ofNat 64 (depth * 0x60 + decodeVarint2StackX) + 96#64 := by
    rw [hlen, BitVec.ofNat_add]
  have h1 := memRegion_split'
    (b := sp - BitVec.ofNat 64 (skipField3Stack depth))
    (b' := sp - 96#64)
    (n := depth * 0x60 + decodeVarint2StackX) (k := 96)
    (N := skipField3Stack depth) hlen
    (by rw [hbit]; exact bv_sub_add_96 sp _)
    hbound
  have hsp_sub :
      sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2StackX) =
        sp - BitVec.ofNat 64 (skipField3Stack depth) := by
    rw [hbit]; exact bv_sub_96_sub sp _
  have h2 := memRegion_split' (b := sp - 96#64) (b' := sp - 48#64)
    (n := 48) (k := 48) (N := 96) rfl (by bv_lin) (by decide)
  have h3 := memRegion_split' (b := sp - 48#64) (b' := sp - 40#64)
    (n := 8) (k := 40) (N := 48) rfl (by bv_lin) (by decide)
  have h4 := memRegion_split' (b := sp - 40#64) (b' := sp - 32#64)
    (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  have h5 := memRegion_split' (b := sp - 32#64) (b' := sp - 24#64)
    (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have h6 := memRegion_split' (b := sp - 24#64) (b' := sp - 16#64)
    (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have h7 := memRegion_split' (b := sp - 16#64) (b' := sp - 8#64)
    (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  rw [hsp_sub, h1, h2, h3, h4, h5, h6, h7,
    Prost.memRegion_eight (sp - 48#64), Prost.memRegion_eight (sp - 40#64),
    Prost.memRegion_eight (sp - 32#64), Prost.memRegion_eight (sp - 24#64),
    Prost.memRegion_eight (sp - 16#64), Prost.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

abbrev skipLeafRest3 (sp : BitVec 64) (depth : Nat) : SepProp :=
  memRegion (sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2StackX)) (depth * 0x60)

theorem skipBelow3_leaf (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipBelow3 sp depth =
      skipLeafRest3 sp depth ∗ stackAt (sp - 96#64) decodeVarint2StackX := by
  simp only [skipBelow3, skipLeafRest3, stackAt]
  have hbound : depth * 0x60 + decodeVarint2StackX ≤ 2 ^ 64 := by
    simp only [decodeVarint2StackX, decodeVarintSlowStackX, decodeErrorHookStackX, extHookStack]
    omega
  have hbit : BitVec.ofNat 64 (depth * 0x60 + decodeVarint2StackX) =
      BitVec.ofNat 64 (depth * 0x60) + BitVec.ofNat 64 decodeVarint2StackX :=
    BitVec.ofNat_add _ _
  exact memRegion_split'
    (b := sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2StackX))
    (b' := sp - 96#64 - BitVec.ofNat 64 decodeVarint2StackX)
    (n := depth * 0x60) (k := decodeVarint2StackX)
    (N := depth * 0x60 + decodeVarint2StackX) rfl
    (by rw [hbit]; exact bv_sub_96_add_cancel sp _ _)
    hbound

theorem skipBelow3_leaf_entails (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipLeafRest3 sp depth ∗ stackAt (sp - 96#64) decodeVarint2StackX ⊢
      skipBelow3 sp depth :=
  Entails.of_eq (skipBelow3_leaf sp depth hdepth).symm

abbrev skipErrRest3 (sp : BitVec 64) (depth : Nat) : SepProp :=
  memRegion (sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2StackX))
    (depth * 0x60 + 0x80)

theorem skipBelow3_err (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipBelow3 sp depth =
      skipErrRest3 sp depth ∗ stackAt (sp - 96#64) decodeErrorHookStackX := by
  simp only [skipBelow3, skipErrRest3, stackAt]
  have hlen : depth * 0x60 + decodeVarint2StackX =
      (depth * 0x60 + 0x80) + decodeErrorHookStackX := by
    simp only [decodeVarint2StackX, decodeVarintSlowStackX]; omega
  have hbound : depth * 0x60 + decodeVarint2StackX ≤ 2 ^ 64 := by
    simp only [decodeVarint2StackX, decodeVarintSlowStackX, decodeErrorHookStackX, extHookStack]
    omega
  have hbit : BitVec.ofNat 64 (depth * 0x60 + decodeVarint2StackX) =
      BitVec.ofNat 64 (depth * 0x60 + 0x80) + BitVec.ofNat 64 decodeErrorHookStackX := by
    rw [hlen, BitVec.ofNat_add]
  exact memRegion_split'
    (b := sp - 96#64 - BitVec.ofNat 64 (depth * 0x60 + decodeVarint2StackX))
    (b' := sp - 96#64 - BitVec.ofNat 64 decodeErrorHookStackX)
    (n := depth * 0x60 + 0x80) (k := decodeErrorHookStackX)
    (N := depth * 0x60 + decodeVarint2StackX) hlen
    (by rw [hbit]; exact bv_sub_96_add_cancel sp _ _)
    hbound

theorem skipBelow3_err_entails (sp : BitVec 64) (depth : Nat) (hdepth : depth < 2 ^ 32) :
    skipErrRest3 sp depth ∗ stackAt (sp - 96#64) decodeErrorHookStackX ⊢
      skipBelow3 sp depth :=
  Entails.of_eq (skipBelow3_err sp depth hdepth).symm

theorem subroutine_ok_skipField3_or {A : RustAlloc} {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (h1 : subroutine_ok prog entry ((skipField3SpecAt A depth P).inImage img))
    (h2 : subroutine_ok prog entry ((skipField3SpecAt A depth Q).inImage img)) :
    subroutine_ok prog entry ((skipField3SpecAt A depth (fun x => P x ∨ Q x)).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.2.1.1 with hP | hQ
  · refine h1.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.inImage, skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1, ⟨hP, hpre.2.1.2⟩, hpre.2.2⟩
  · refine h2.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [Spec.inImage, skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1, ⟨hQ, hpre.2.1.2⟩, hpre.2.2⟩

theorem subroutine_ok_skipField3_imp {A : RustAlloc} {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    {depth : Nat} {P Q : SkipFieldGhost → Prop}
    (himp : ∀ x, P x → Q x)
    (h : subroutine_ok prog entry ((skipField3SpecAt A depth Q).inImage img)) :
    subroutine_ok prog entry ((skipField3SpecAt A depth P).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [Spec.inImage, skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre.1, ⟨himp x hpre.2.1.1, hpre.2.1.2⟩, hpre.2.2⟩

theorem skipField3SpecAt_reaches_outcome_eq (prog : Program) (img : Obj.Image) (A : RustAlloc)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (R : SepProp) (s0 : State) :
    reaches_outcome prog ((skipField3SpecAt A x.depth P).inImage img) x R s0 s0 =
      reaches_outcome prog ((skipField3Spec A).inImage img) x R s0 s0 :=
  reaches_outcome_eq_of_parts_eq (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

theorem subroutine_ok_skipField3Spec_of_at_depth {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    (h : ∀ depth, depth < 2 ^ 32 → subroutine_ok prog entry ((skipField3SpecAt A depth (fun _ => True)).inImage img)) :
    subroutine_ok prog entry ((skipField3Spec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  simp only [Spec.inImage, skipField3Spec, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.2.1.2.2.2.2.2.1
  refine (h x.depth hdepth).mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [Spec.inImage, skipField3SpecAt, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hpre'.1, ⟨trivial, trivial, hpre'.2.1⟩, hpre'.2.2⟩

abbrev HighCalleeSaved3 (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

abbrev skipGroupLoopPre3 (A : RustAlloc) (s0 : State) (d : Nat)
    (bufRef slot ptr v_pad : BitVec 64) (bs cur : List (BitVec 8)) : SepProp :=
  (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool ∗
    memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ v_pad) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    skipBelow3 s0.sp (d + 1)

/-- Contract statement for `skip_field::<&mut &[u8]> [local#6]` under Regime-A. -/
def SkipField6OkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr skipField6Name)
    ((skipField3Spec A).inImage img)

/-- Contract statement for `RawVec<MessageKey>::grow_one` under Regime-A
(`growOneChainSpecX A = growOne104SpecX A`, stride 104, align 8). -/
def GrowOneMessageKeyOkExtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr growOneMessageKeyName)
    ((growOneChainSpecX A).inImage img)

/-- `growOneMessageKeyName` and `growOneChainName` resolve to the exact same symbol offset in
`libsignalSessionCode`. -/
theorem growOneMessageKey_fnOff_eq_chain :
    libsignalSessionCode.fnOff growOneMessageKeyName =
      libsignalSessionCode.fnOff growOneChainName := by
  have h1 := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
  rw [h1, h2]

theorem growOneMessageKey_fnAddr_eq_chain (b : BitVec 64)
    (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr growOneMessageKeyName =
      (libsignalSessionCode.rebase b H).fnAddr growOneChainName := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, growOneMessageKey_fnOff_eq_chain]

/-- `RawVec<MessageKey>::grow_one` meets `(growOneChainSpecX A).inImage img`
under `Proofs.libsignal.Stage1X.AllocContractsX img A ext`, by reusing `growOneChain_ok_x`. -/
theorem growOneMessageKey_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    GrowOneMessageKeyOkExtX img A ext := by
  unfold GrowOneMessageKeyOkExtX tripleRatchetProgAtExt
  rw [growOneMessageKey_fnAddr_eq_chain]
  exact Proofs.libsignal.Stage1X.growOneChain_ok_x hA

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
