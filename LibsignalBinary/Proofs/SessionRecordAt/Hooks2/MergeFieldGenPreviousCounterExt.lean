/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
/-!
# `SessionStructure::merge_field` Tag 5 (`previous_counter`)

Verifies `SessionStructure::merge_field` (`0x5ca4`, Block `15`) on protobuf tag 5
(`previous_counter`) on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem genField_tag_eq_5_iff (fl : GenField) :
    fl.tag = 5 ↔ ∃ v, fl = .prevCounter v := by
  cases fl <;> simp [GenField.tag]

private theorem mergeUint32_prevCounter_previousCounter (v : BitVec 32) (tail : List (BitVec 8)) :
    mergeUint32 .varint ((GenField.prevCounter v).payload ++ tail) = some (v, tail) := by
  exact mergeUint32_encode v tail

private theorem rodata_0x46020_byte0_eq_previousCounter :
    (libsignalSessionImage.data.drop (num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 4) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 1 = [25#8] := by
  rfl_kernel

private theorem holdsBytes_rodata_0x46020_previousCounter {s : State}
    (hF : sessionImg0.FrozenLoaded s) :
    Arm64.Obj.HoldsBytes s.mem (sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 4)) [25#8] (fun _ => .ro) :=
  loads_rodata_holdsBytes E2E.Record.loads_sessionImg0 hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 4)) (n := 1) (bs := [25#8])
    (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (by rfl_kernel)
    (by rfl_kernel)
    rfl
    rodata_0x46020_byte0_eq_previousCounter

private theorem sepWPp_intro_rodata_0x46020_previousCounter {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : sessionImg0.FrozenLoaded s)
    (h : SepWPp prog ret s (((sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 4)) ↦₈ᵣ 25#8) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc, ← pointsToBytesRO_singleton]
  exact Satisfies.of_holdsBytes_ro (holdsBytes_rodata_0x46020_previousCounter hF) (by decide) hm

run_meta do
  let optInstr := Lean.mkApp (Lean.mkConst ``Option [0]) (Lean.mkConst ``Arm64.Instr)
  let tree := Lean.mkConst ``CryptoVerification.libsignalSessionCode_tree
  let fnOff := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let ranges : List (Nat × Nat) := [(0, 64), (164, 24), (1880, 28)]
  for (k0, len) in ranges do
    for i in [0 : len / 4] do
      let addr := fnOff + k0 + 4 * i
      let hex := String.ofList (Nat.toDigits 16 addr)
      let thmName := Lean.Name.str `CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter s!"decode_0x{hex}_previousCounter"
      let lhs := Lean.mkApp2 (Lean.mkConst ``ProofLib.ProgramReflection.WordTree.fetchDecodeAt)
        tree (Lean.mkNatLit addr)
      let rhs ← Lean.Meta.reduce lhs
      let eqTy := Lean.mkApp3 (Lean.mkConst ``Eq [1]) optInstr lhs rhs
      let eqPrf := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) optInstr lhs
      Lean.addDecl (.thmDecl {
        name := thmName
        levelParams := []
        type := eqTy
        value := eqPrf
      })

local elab "mf5_code_fetches_from " codeId:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let fetchEntry := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := Lean.mkIdent (Lean.Name.str `CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter s!"previousCounter_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Lean.Syntax.mkNumLit (toString k)
    if k == 0 then
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

local macro "mf5_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| mf5_code_fetches_from CryptoVerification.libsignalSessionCode $b $H
    (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") (num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) $k0 $len)

private theorem drop_left_sepWPp_previousCounter {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

private theorem int32Merge_ok_sub_previousCounter {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Prost.Int32MergeOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
      (Prost.int32MergeSpec A) := by
  have heq : (tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) =
      (tripleRatchetProgAt b C ctl abs).fnAddr Prost.int32MergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"), (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact h

private def prostSSGRest_previousCounter (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

private theorem prostSSGAt_eq_prevCounter_sep_rest_previousCounter (A : RustAlloc) (ss : BitVec 64) (v : SSG) :
    prostSSGAt A ss v = ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗ prostSSGRest_previousCounter A ss v := by
  unfold prostSSGAt prostSSGRest_previousCounter
  ac_rfl

private theorem stackAt_mergeField_split_previousCounter (sp : BitVec 64) :
    stackAt sp mergeFieldStack =
      memRegion (sp - 16384#64) 7792 ∗
        stackAt (sp - 240#64) Prost.int32MergeStack ∗
        memRegion (sp - 240#64) 160 ∗
        memRegion (sp - 56#64) 8 ∗
        (∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
         ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w25 : BitVec 64,
         ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
          ((sp - 80#64) ↦₆₄ w29) ∗ ((sp - 72#64) ↦₆₄ w30) ∗
          ((sp - 64#64) ↦₆₄ w25) ∗
          ((sp - 48#64) ↦₆₄ w24) ∗ ((sp - 40#64) ↦₆₄ w23) ∗
          ((sp - 32#64) ↦₆₄ w22) ∗ ((sp - 24#64) ↦₆₄ w21) ∗
          ((sp - 16#64) ↦₆₄ w20) ∗ ((sp - 8#64) ↦₆₄ w19)) := by
  have h0 := LibsignalTripleRatchet.stackAt_split_cells sp 16144 30 (by decide)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 30)) 30 (by decide)] at h0
  change stackAt sp mergeFieldStack = stackAt (sp - 240#64) 16144 ∗ memRegion (sp - 240#64) 240 at h0
  have hsub := ProofLib.stackAt_split_bottom (sp - 240#64) Prost.int32MergeStack 7792 (by decide)
  change stackAt (sp - 240#64) 16144 =
    memRegion (sp - 240#64 - 16144#64) 7792 ∗ stackAt (sp - 240#64) Prost.int32MergeStack at hsub
  have hsub_addr : sp - 240#64 - 16144#64 = sp - 16384#64 := by bv_omega
  rw [hsub_addr] at hsub
  have s1 := Prost.memRegion_split (sp - 240#64) 160 80 (by decide)
  rw [bv_sub_add_lit sp 240 160] at s1
  have s2 := Prost.memRegion_split (sp - 80#64) 8 72 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s2
  have s3 := Prost.memRegion_split (sp - 72#64) 8 64 (by decide)
  rw [bv_sub_add_lit sp 72 8] at s3
  have s4 := Prost.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s4
  have s5 := Prost.memRegion_split (sp - 56#64) 8 48 (by decide)
  rw [bv_sub_add_lit sp 56 8] at s5
  have s6 := Prost.memRegion_split (sp - 48#64) 8 40 (by decide)
  rw [bv_sub_add_lit sp 48 8] at s6
  have s7 := Prost.memRegion_split (sp - 40#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 40 8] at s7
  have s8 := Prost.memRegion_split (sp - 32#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 32 8] at s8
  have s9 := Prost.memRegion_split (sp - 24#64) 8 16 (by decide)
  rw [bv_sub_add_lit sp 24 8] at s9
  have s10 := Prost.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s10
  rw [h0, hsub, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    Prost.memRegion_eight (sp - 80#64), Prost.memRegion_eight (sp - 72#64),
    Prost.memRegion_eight (sp - 64#64),
    Prost.memRegion_eight (sp - 48#64), Prost.memRegion_eight (sp - 40#64),
    Prost.memRegion_eight (sp - 32#64), Prost.memRegion_eight (sp - 24#64),
    Prost.memRegion_eight (sp - 16#64), Prost.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

private theorem adrp_0x4601c_eq_previousCounter (base entry : BitVec 64)
    (halign : base &&& 0xfff#64 = 0#64) (hentry : base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") = entry) :
    (entry + bv% (40) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" - page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 712)) = base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
  subst hentry
  bv_arith

private theorem setWidth8_zext64_trunc32_previousCounter (v : BitVec 64) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)) = BitVec.setWidth 8 v := by
  change BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) = BitVec.setWidth 8 v
  rw [BitVec.setWidth_setWidth_of_le (BitVec.setWidth 32 v) (by decide),
    BitVec.setWidth_setWidth_of_le v (by decide)]

private theorem int64_raw_toBitVec_previousCounter (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change n = n % 18446744073709551616
  exact (Nat.mod_eq_of_lt h).symm

private theorem allowPanic_call_previousCounter {s_call s0 sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  have h1 : allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    unfold allocFailedIn
    rw [htr]
    exact id
  exact allowPanic_frame h1 hm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero int64_raw_toBitVec_previousCounter

private theorem holdsBytes_rodata_0x46020_previousCounter_ext {img : Obj.Image} {s : State}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hF : img.FrozenLoaded s) :
    Arm64.Obj.HoldsBytes s.mem (img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 4)) [25#8] (fun _ => .ro) :=
  loads_rodata_holdsBytes hLoads hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 4)) (n := 1) (bs := [25#8])
    (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (by rfl_kernel)
    (by rfl_kernel)
    rfl
    rodata_0x46020_byte0_eq_previousCounter

private theorem sepWPp_intro_rodata_0x46020_previousCounter_ext {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hF : img.FrozenLoaded s)
    (h : SepWPp prog ret s (((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 4)) ↦₈ᵣ 25#8) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc, ← pointsToBytesRO_singleton]
  exact Satisfies.of_holdsBytes_ro (holdsBytes_rodata_0x46020_previousCounter_ext hLoads hF) (by decide) hm

theorem int32Merge_ok_sub_previousCounter_extW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Prost.X.Int32MergeOkW img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
      ((Prost.X.int32MergeSpecW A).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) =
      (SP2Ext img.base ext).fnAddr Prost.int32MergeName := by
    rw [SP2Ext, contractProg, Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"), (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact h

private theorem stackAt_mergeField_split_previousCounter_extW (sp : BitVec 64) :
    stackAt sp mergeFieldStackX =
      memRegion (sp - 32768#64) 7792 ∗
        stackAt (sp - 240#64) Prost.X.int32MergeStackW ∗
        memRegion (sp - 240#64) 160 ∗
        memRegion (sp - 56#64) 8 ∗
        (∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
         ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w25 : BitVec 64,
         ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
          ((sp - 80#64) ↦₆₄ w29) ∗ ((sp - 72#64) ↦₆₄ w30) ∗
          ((sp - 64#64) ↦₆₄ w25) ∗
          ((sp - 48#64) ↦₆₄ w24) ∗ ((sp - 40#64) ↦₆₄ w23) ∗
          ((sp - 32#64) ↦₆₄ w22) ∗ ((sp - 24#64) ↦₆₄ w21) ∗
          ((sp - 16#64) ↦₆₄ w20) ∗ ((sp - 8#64) ↦₆₄ w19)) := by
  have h0 := LibsignalTripleRatchet.stackAt_split_cells sp 32528 30 (by decide)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 30)) 30 (by decide)] at h0
  change stackAt sp mergeFieldStackX = stackAt (sp - 240#64) 32528 ∗ memRegion (sp - 240#64) 240 at h0
  have hsub := ProofLib.stackAt_split_bottom (sp - 240#64) Prost.X.int32MergeStackW 7792 (by decide)
  change stackAt (sp - 240#64) 32528 =
    memRegion (sp - 240#64 - 32528#64) 7792 ∗ stackAt (sp - 240#64) Prost.X.int32MergeStackW at hsub
  have hsub_addr : sp - 240#64 - 32528#64 = sp - 32768#64 := by bv_omega
  rw [hsub_addr] at hsub
  have s1 := Prost.memRegion_split (sp - 240#64) 160 80 (by decide)
  rw [bv_sub_add_lit sp 240 160] at s1
  have s2 := Prost.memRegion_split (sp - 80#64) 8 72 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s2
  have s3 := Prost.memRegion_split (sp - 72#64) 8 64 (by decide)
  rw [bv_sub_add_lit sp 72 8] at s3
  have s4 := Prost.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s4
  have s5 := Prost.memRegion_split (sp - 56#64) 8 48 (by decide)
  rw [bv_sub_add_lit sp 56 8] at s5
  have s6 := Prost.memRegion_split (sp - 48#64) 8 40 (by decide)
  rw [bv_sub_add_lit sp 48 8] at s6
  have s7 := Prost.memRegion_split (sp - 40#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 40 8] at s7
  have s8 := Prost.memRegion_split (sp - 32#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 32 8] at s8
  have s9 := Prost.memRegion_split (sp - 24#64) 8 16 (by decide)
  rw [bv_sub_add_lit sp 24 8] at s9
  have s10 := Prost.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s10
  rw [h0, hsub, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    Prost.memRegion_eight (sp - 80#64), Prost.memRegion_eight (sp - 72#64),
    Prost.memRegion_eight (sp - 64#64),
    Prost.memRegion_eight (sp - 48#64), Prost.memRegion_eight (sp - 40#64),
    Prost.memRegion_eight (sp - 32#64), Prost.memRegion_eight (sp - 24#64),
    Prost.memRegion_eight (sp - 16#64), Prost.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

run_meta do
  let optInstr := Lean.mkApp (Lean.mkConst ``Option [0]) (Lean.mkConst ``Arm64.Instr)
  let tree := Lean.mkConst ``CryptoVerification.libsignalSessionCode_tree
  let fnOff := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let ranges : List (Nat × Nat) := [(0, 64), (164, 24), (1880, 28)]
  for (k0, len) in ranges do
    for i in [0 : len / 4] do
      let addr := fnOff + k0 + 4 * i
      let hex := String.ofList (Nat.toDigits 16 addr)
      let thmName := Lean.Name.str `CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter s!"decode_0x{hex}_previousCounter"
      let lhs := Lean.mkApp2 (Lean.mkConst ``ProofLib.ProgramReflection.WordTree.fetchDecodeAt)
        tree (Lean.mkNatLit addr)
      let rhs ← Lean.Meta.reduce lhs
      let eqTy := Lean.mkApp3 (Lean.mkConst ``Eq [1]) optInstr lhs rhs
      let eqPrf := Lean.mkApp2 (Lean.mkConst ``Eq.refl [1]) optInstr lhs
      try
        Lean.addDecl (.thmDecl {
          name := thmName
          levelParams := []
          type := eqTy
          value := eqPrf
        })
      catch _ => pure ()

theorem mergeFieldGenPreviousCounter_ok_extWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext) :
    MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 5) := by
  unfold MergeFieldGenOkAtWA OkAtX mergeFieldGenSpecAtWA
  have hInt32 := int32Merge_ok_sub_previousCounter_extW hC.2.1
  have halign : img.base &&& 0xfff#64 = 0#64 :=
    base_aligned_of_loads hLoads
  have hentry_eq : img.base + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") =
      (SP2Ext img.base ext).fnAddr mergeFieldName := by
    rw [SP2Ext, contractProg, Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")]
  mf5_fetches img.base (Rust.withPanics ext) 0 64
  mf5_fetches img.base (Rust.withPanics ext) 164 24
  mf5_fetches img.base (Rust.withPanics ext) 1880 28
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v_ss, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨_, R, hpre, ?_⟩
  clear hpre
  dsimp only
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag, hf_ok, hf_fresh, h_len, h_loaded, h_sym⟩ => ?_
  obtain ⟨v_fld, h_fld⟩ := (genField_tag_eq_5_iff fld).mp htag
  subst h_fld
  change BitVec.setWidth 32 (s0.readReg64 Reg.x1) = 5#32 at hx1
  change BitVec.setWidth 8 (s0.readReg64 Reg.x2) = 0#8 at hx2
  dsimp only [SP2Ext, contractProg] at hInt32 hentry_eq hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr mergeFieldName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  refine sepWPp_intro_rodata_0x46020_previousCounter_ext hLoads h_loaded ?_
  conv =>
    arg 4
    rw [prostSSGAt_eq_prevCounter_sep_rest_previousCounter A ss v_ss, stackAt_mergeField_split_previousCounter_extW s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w19 => ?_
  refine SepWPp.exists_elim fun w20 => ?_
  refine SepWPp.exists_elim fun w21 => ?_
  refine SepWPp.exists_elim fun w22 => ?_
  refine SepWPp.exists_elim fun w23 => ?_
  refine SepWPp.exists_elim fun w24 => ?_
  refine SepWPp.exists_elim fun w25 => ?_
  refine SepWPp.exists_elim fun w30 => ?_
  refine SepWPp.exists_elim fun w29 => ?_
  apply SepWPp.of_sepWP_frozen_seedChain h_loaded h_sym (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
  wp_steps
  rw [adrp_0x4601c_eq_previousCounter img.base entry halign hentry_eq]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hFm hsymm
  apply drop_left_sepWPp_previousCounter
  refine SepWPp.call
    (x := Prost.Int32MergeGhost.mk .varint (ss + 332#64) bufRef slot ptr ((GenField.prevCounter v_fld).payload ++ tail))
    (ret_pc := entry + bv% (180))
    (F := prostSSGRest_previousCounter A ss v_ss ∗
      memRegion (s0.sp - 32768#64) 7792 ∗
      memRegion (s0.sp - 240#64) 160 ∗
      memRegion (s0.sp - 56#64) 8 ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    hInt32
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align)
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro R' hm
    have h_len63 : ((GenField.prevCounter v_fld).payload ++ tail).length < 2 ^ 63 :=
      Nat.lt_trans h_len (by decide)
    dsimp only [Spec.inImage]
    simp only [Prost.X.int32MergeSpecW, Prost.memRegion_four (ss + 332#64),
      arm64_norm, setWidth8_zext64_trunc32_previousCounter, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, satisfies_pure_sepConj, satisfies_sepExists]
    refine ⟨v_ss.prevCounter, ⟨⟨hFm, h_sym⟩, ⟨hx2, h_len63⟩⟩, ?_⟩
    convert hm using 1
    · ac_rfl
    · rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    exact allowPanic_call_previousCounter rfl hm
  · intro sm hpcm hrunm hspm hcsm
    obtain ⟨-, -, -, -, -, -, -, hx26m, hx27m, hx28m, -, hvregsm⟩ := hcsm
    simp only [arm64_norm] at hspm hx26m hx27m hx28m hvregsm
    have hsm_align : sm.spAligned = true := by
      simp only [State.spAligned, hspm, arm64_norm] at hsp_align ⊢
      exact hsp_align
    dsimp only [Spec.inImage]
    simp only [Prost.X.int32MergeSpecW, mergeUint32_prevCounter_previousCounter,
      arm64_norm, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htrm, hx0m⟩ => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩⟩
    intro hm
    refine ⟨⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩, ?_⟩
    rw [show v_ss.apply (GenField.prevCounter v_fld) = { v_ss with prevCounter := v_fld } from rfl,
      prostSSGAt_eq_prevCounter_sep_rest_previousCounter A ss { v_ss with prevCounter := v_fld },
      show prostSSGRest_previousCounter A ss { v_ss with prevCounter := v_fld } = prostSSGRest_previousCounter A ss v_ss from rfl,
      stackAt_mergeField_split_previousCounter_extW s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, satisfies_sepExists]
    refine ⟨s0.readReg64 (Reg.gpr 19#5), s0.readReg64 (Reg.gpr 20#5),
      s0.readReg64 (Reg.gpr 21#5), s0.readReg64 (Reg.gpr 22#5),
      s0.readReg64 (Reg.gpr 23#5), s0.readReg64 (Reg.gpr 24#5),
      s0.readReg64 (Reg.gpr 25#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 29#5), ?_⟩
    convert hm using 1
    ac_rfl

private theorem mergeFieldGenSpecAtWA_A0_previousCounter (img : Obj.Image) (P : GenField → Prop) :
    mergeFieldGenSpecAtWA A0 img P = mergeFieldGenSpecAtW img P := by
  have hp : A0.pool = emp := rfl
  unfold mergeFieldGenSpecAtWA mergeFieldGenSpecAtW
  congr 1
  · funext x s; simp only [hp, emp_sepConj]
  · funext x s sf; simp only [hp, emp_sepConj]

theorem mergeFieldGenPreviousCounter_ok_extW (img : Obj.Image)
    (ext : String → Option (State → State)) (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext) :
    MergeFieldGenOkAtW img ext (fun fl => fl.tag = 5) := by
  unfold MergeFieldGenOkAtW
  rw [← mergeFieldGenSpecAtWA_A0_previousCounter]
  exact mergeFieldGenPreviousCounter_ok_extWA img A0 ext hLoads hC

/-! ## Relocatable `[LibsignalPlacement]` proof for tag 5 (`previous_counter`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_MergeFieldGenPreviousCounterExt_Placed : True := trivial

private theorem int32Merge_placed_ok_sub_previousCounter_extW [LibsignalPlacement]
    {H : LibsignalHooks}
    (h : Prost.X.Int32MergePlacedOkW A0 H) :
    subroutine_ok (lsProg_15 H) (lsmpl.base 8)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.int32MergeSpecW A0)) :=
  ls_call_ro_of_cl (callerProg := lsProg_15 H) h

private theorem rodata_byte4_placed_intro_previousCounter_ext [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 4#64) ↦₈ᵣ 25#8) ∗ P :=
  lsro8_intro hro (by lsro_addr) (by decide +kernel) hP

private theorem sepWPp_intro_rodata_byte4_placed_previousCounter_ext [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s (((lsmpl.ρ mergeFieldRodataSym + 4#64) ↦₈ᵣ 25#8) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact rodata_byte4_placed_intro_previousCounter_ext hcrl.2 hm

/-- Relocatable `SessionStructure::merge_field` (Block `15`, `lsProg_15 H`) on tag 5
(`previous_counter`) at `mergeFieldStackX`. -/
theorem mergeFieldGenPreviousCounter_placed_okW [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeFieldGenPlacedOkW H (fun fl => fl.tag = 5) := by
  unfold MergeFieldGenPlacedOkW mergeFieldGenPlacedSpecW
  have hInt32 := int32Merge_placed_ok_sub_previousCounter_extW hC.2.1
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v_ss, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  refine ⟨_, R, hpre_raw, ?_⟩
  clear hpre hpre_raw
  dsimp only [mergeFieldGenRawSpecW]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag, hf_ok, hf_fresh, h_len⟩ => ?_
  obtain ⟨v_fld, h_fld⟩ := (genField_tag_eq_5_iff fld).mp htag
  subst h_fld
  change BitVec.setWidth 32 (s0.readReg64 Reg.x1) = 5#32 at hx1
  change BitVec.setWidth 8 (s0.readReg64 Reg.x2) = 0#8 at hx2
  refine sepWPp_intro_rodata_byte4_placed_previousCounter_ext hcrl0 ?_
  conv =>
    arg 4
    rw [prostSSGAt_eq_prevCounter_sep_rest_previousCounter A0 ss v_ss,
      stackAt_mergeField_split_previousCounter_extW s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w19 => ?_
  refine SepWPp.exists_elim fun w20 => ?_
  refine SepWPp.exists_elim fun w21 => ?_
  refine SepWPp.exists_elim fun w22 => ?_
  refine SepWPp.exists_elim fun w23 => ?_
  refine SepWPp.exists_elim fun w24 => ?_
  refine SepWPp.exists_elim fun w25 => ?_
  refine SepWPp.exists_elim fun w30 => ?_
  refine SepWPp.exists_elim fun w29 => ?_
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 8) hcrl0
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcrl_call
  apply drop_left_sepWPp_previousCounter
  refine SepWPp.call_lscro
    (x := Prost.Int32MergeGhost.mk .varint (ss + 332#64) bufRef slot ptr ((GenField.prevCounter v_fld).payload ++ tail))
    (ret_pc := (blkPl_15).base + 180#64)
    (F := prostSSGRest_previousCounter A0 ss v_ss ∗
      memRegion (s0.sp - 32768#64) 7792 ∗
      memRegion (s0.sp - 240#64) 160 ∗
      memRegion (s0.sp - 56#64) 8 ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    hInt32
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align)
    hcrl_call
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro R' hm
    have hpool : A0.pool = emp := rfl
    have h_len63 : ((GenField.prevCounter v_fld).payload ++ tail).length < 2 ^ 63 :=
      Nat.lt_trans h_len (by decide)
    simp only [Prost.X.int32MergeSpecW, hpool, emp_sepConj, Prost.memRegion_four (ss + 332#64),
      arm64_norm, setWidth8_zext64_trunc32_previousCounter, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, satisfies_pure_sepConj, satisfies_sepExists]
    refine ⟨v_ss.prevCounter, ⟨hx2, h_len63⟩, ?_⟩
    convert hm using 1
    · ac_rfl
    · rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    exact allowPanic_call_previousCounter rfl hm
  · intro sm hpcm hrunm hspm _hcrlm hcsm
    obtain ⟨-, -, -, -, -, -, -, hx26m, hx27m, hx28m, -, hvregsm⟩ := hcsm
    simp only [arm64_norm] at hspm hx26m hx27m hx28m hvregsm
    have hsm_align : sm.spAligned = true := by
      simp only [State.spAligned, hspm, arm64_norm] at hsp_align ⊢
      exact hsp_align
    have hpool : A0.pool = emp := rfl
    simp only [Prost.X.int32MergeSpecW, mergeUint32_prevCounter_previousCounter, hpool, emp_sepConj,
      arm64_norm, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htrm, hx0m⟩ => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩⟩
    intro hm
    refine ⟨⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩, ?_⟩
    rw [show v_ss.apply (GenField.prevCounter v_fld) = { v_ss with prevCounter := v_fld } from rfl,
      prostSSGAt_eq_prevCounter_sep_rest_previousCounter A0 ss { v_ss with prevCounter := v_fld },
      show prostSSGRest_previousCounter A0 ss { v_ss with prevCounter := v_fld } = prostSSGRest_previousCounter A0 ss v_ss from rfl,
      stackAt_mergeField_split_previousCounter_extW s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, satisfies_sepExists]
    refine ⟨s0.readReg64 (Reg.gpr 19#5), s0.readReg64 (Reg.gpr 20#5),
      s0.readReg64 (Reg.gpr 21#5), s0.readReg64 (Reg.gpr 22#5),
      s0.readReg64 (Reg.gpr 23#5), s0.readReg64 (Reg.gpr 24#5),
      s0.readReg64 (Reg.gpr 25#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 29#5), ?_⟩
    convert hm using 1
    ac_rfl

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter

