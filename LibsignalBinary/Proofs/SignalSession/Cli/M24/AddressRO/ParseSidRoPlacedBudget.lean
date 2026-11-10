/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsDecodeHex32Placed
public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.ParserTryParse
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import ProofLib.Placed.OpcodeExclusion
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Placed Read-Only `ServiceId` Parsing Chain

Proves `parseSid_ro_placed_vm_ok_rocl` for `ServiceId::parse_from_service_id_string` (Block `206`,
via `<uuid::Uuid>::try_parse` on Block `252`, `uuid::parser::try_parse` on Block `255`, and
`uuid::parser::decode_hex32` on Block `254`) on read-only (`↦ᵣ`) input slices while preserving
`VmPreserved` and `fs`. In the hyphenated UUID branch, the 32 hex bytes are copied onto the stack
buffer at `sp - 88` before calling `decode_hex32`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.ParseSidRoPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkPC_206 blkPl_206 blkPC_252 blkPl_252 blkPC_254 blkPl_254 blkPC_255 blkPl_255
   libsignalSessionLib ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
   ls_subroutine_ok_of_block lsmpl sepWP_seq_lscl withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchetRepr
  (ServiceIdParser UuidParser decodeHex32 parseHyphenated parseSimple serviceIdParse urnPrefix
   uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack parseSidFrameStack parseSidResultAt uuidErrParseOther uuidResultAt
   uuidTryParseStack)
open CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse
  (ParserRegsPreserved bne_32_of_lt braced_all_eq braced_ne_0 braced_ne_37
   decodeHex32ResultAt decodeHex32ResultAt_sp52_none decodeHex32ResultAt_sp52_some
   decodeHex32ResultAt_sp88_none decodeHex32ResultAt_sp88_some decodeHex32Spec
   decodeHex32_of_length_32 decodeNibbles drop_eq_take_append_cons_drop entails_of_eq
   eq_ofNat_of_toNat_eq exists_word9_of_length_9 foldl_stepAcc_zero isHexByte len_eq_of_reg_eq
   len_ne_of_reg_ne list_length_17_elim list_length_32_elim memRegion_out17_split
   memRegion_out28_split memRegion_out32_split memRegion_sp52_17_none memRegion_sp52_17_some
   memRegion_sp56_17_split memRegion_sp88_17_none memRegion_sp88_17_some
   memRegion_sp88_32_for_hyphen memRegion_sp88_32_for_simple parseHyphenated_all_eq
   parseHyphenated_ne_13 parseHyphenated_ne_18 parseHyphenated_ne_23 parseHyphenated_ne_8
   parseHyphenated_of_parts parserTryParseResultAt parserTryParseResultAt_some_eq
   parserTryParseResultAt_sp56_none parserTryParseResultAt_sp56_some pointsToBytes_16_tail_expand
   pointsToBytes_17_expand pointsToBytes_32_expand pointsToBytes_32_sub32_expand
   pointsToBytes_entails_stackAt_32 rawCombine rawCombine_step_eq rawNibble sepWP_parser_branch
   sepWP_parser_hyph36 stack32_zero_eq_replicate stackAt_32_split stackAt_parser_split
   stackAt_uuid_split stepAcc subroutine_ok_of_sepWP_entails subroutine_ok_of_sepWP_simple
   urnPrefix_val urn_all_eq uuidResultAt_some_eq uuidTryParse_of_other_len)
open CryptoVerification.LibsignalTripleRatchet.ParseServiceId
  (exists_cons4_of_le le_of_not_ult length_eq_36_of_eq_36 length_eq_36_of_eq_40
   length_ne_36_of_ne_36 length_ne_36_of_ne_40 memRegion_17_none_split memRegion_out1_16_split
   memRegion_sp64_none_split memRegion_sp64_some_split parseSidResultAt_some_eq
   serviceIdParse_cons4_aci serviceIdParse_cons4_pni serviceIdParse_of_lt_4
   stackAt_parseSidFrame_split toNat_lt_of_ult uuidResultAt_sp64_none uuidResultAt_sp64_some)
open CryptoVerification.SignalSession.Cli.MainHops.UuidFs
  (DecodeLoopInvFs DecodeLoopPostFs decodeHex32_placed_okFs)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (sepWP_rebase_vmPreserved tpidrEl0_applyWriteback trapHooks vmPreserved_advancePC
   vmPreserved_appendTrace vmPreserved_applyWriteback vmPreserved_refl_iff vmPreserved_setFs
   vmPreserved_setMem_write16 vmPreserved_setMem_write32 vmPreserved_setMem_write64
   vmPreserved_setMem_write8 vmPreserved_setMem_writeBytes vmPreserved_setPC vmPreserved_setPState
   vmPreserved_setStatus vmPreserved_stepExclLoop vmPreserved_writeReg vmPreserved_writeReg32
   vmPreserved_writeReg64 vmPreserved_writeVReg128 vmPreserved_writeVReg32 vmPreserved_writeVReg64)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_placed (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

/-! ## Read-only input specifications -/

def decodeHex32ROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (out, src, hex) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = src ∧ hex.length = 32⌝ ∗
      (src ↦ᵣ hex) ∗ memRegion out 17 ∗ stackAt s.sp 0x20
  post := fun (out, src, hex) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (src ↦ᵣ hex) ∗ decodeHex32ResultAt out (decodeHex32 hex) ∗ stackAt s0.sp 0x20

def parserTryParseROSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out17) s =>
    (⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out17⌝ ∗
      (p ↦ᵣ bs) ∗ memRegion out17 17) ∗ stackAt s.sp 0x80
  post := fun (p, bs, out17) s0 sf =>
    (⌜sf.trace = s0.trace⌝ ∗
      (p ↦ᵣ bs) ∗ parserTryParseResultAt out17 (uuidTryParse bs)) ∗ stackAt s0.sp 0x80

def uuidTryParseROSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ᵣ bs) ∗ memRegion out 32
  post := fun (p, bs, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (p ↦ᵣ bs) ∗ uuidResultAt out (parse bs)

def uuidTryParseCodeROSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun x s => (uuidTryParseROSpec parse).pre x s ∗ stackAt s.sp uuidTryParseStack
  post := fun x s0 sf => (uuidTryParseROSpec parse).post x s0 sf ∗ stackAt s0.sp uuidTryParseStack

def uuidTryParseStackROSpec (hookStack : Nat := 0) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun x s => (uuidTryParseROSpec uuidTryParse).pre x s ∗ stackAt s.sp hookStack
  post := fun x s0 sf => (uuidTryParseROSpec uuidTryParse).post x s0 sf ∗ stackAt s0.sp hookStack

def parseSidROSpec (parse : ServiceIdParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ᵣ bs) ∗ memRegion out 17
  post := fun (p, bs, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ᵣ bs) ∗ parseSidResultAt out (parse bs)

def parseSidCodeStackROSpec (hookStack : Nat := 0) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun x s =>
    (parseSidROSpec (serviceIdParse uuidTryParse)).pre x s ∗
      stackAt (s.sp - 80#64) hookStack ∗ stackAt s.sp parseSidFrameStack
  post := fun x s0 sf =>
    (parseSidROSpec (serviceIdParse uuidTryParse)).post x s0 sf ∗
      stackAt (s0.sp - 80#64) hookStack ∗ stackAt s0.sp parseSidFrameStack

/-! ## Byte-packing helpers -/

private theorem pointsToBytesRO_cons_off (p : BitVec 64) (k : Nat) (x : BitVec 8)
    (xs : List (BitVec 8)) :
    ((p + BitVec.ofNat 64 k) ↦ᵣ (x :: xs)) =
      (((p + BitVec.ofNat 64 k) ↦₈ᵣ x) ∗ ((p + BitVec.ofNat 64 (k + 1)) ↦ᵣ xs)) := by
  rw [pointsToBytesRO_cons]
  have h : (p + BitVec.ofNat 64 k) + 1#64 = p + BitVec.ofNat 64 (k + 1) := by
    rw [BitVec.add_assoc]; congr 1
    change BitVec.ofNat 64 k + BitVec.ofNat 64 1 = BitVec.ofNat 64 (k + 1)
    rw [← BitVec.ofNat_add]
  rw [h]

private theorem exists_word64_both_of_length_8 (s : List (BitVec 8)) (h : s.length = 8) :
    ∃ w : BitVec 64,
      (∀ a : BitVec 64, (a ↦ᵣ s) = (a ↦₆₄ᵣ w)) ∧
      (∀ a : BitVec 64, (a ↦ₛ s) = (a ↦₆₄ w)) := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0,
    fun a => pointsToBytesRO8_eq_pointsTo64RO a b0 b1 b2 b3 b4 b5 b6 b7,
    fun a => pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7⟩

private theorem exists_word32_both_of_length_4 (s : List (BitVec 8)) (h : s.length = 4) :
    ∃ w : BitVec 32,
      (∀ a : BitVec 64, (a ↦ᵣ s) = (a ↦₃₂ᵣ w)) ∧
      (∀ a : BitVec 64, (a ↦ₛ s) = (a ↦₃₂ w)) := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at h)
  exact ⟨b3 ++ b2 ++ b1 ++ b0,
    fun a => pointsToBytesRO4_eq_pointsTo32RO a b0 b1 b2 b3,
    fun a => pointsToBytes4_eq_pointsTo32 a b0 b1 b2 b3⟩

private theorem exists_36_parts_ro (s : List (BitVec 8)) (h : s.length = 36) :
    ∃ (hex32 : List (BitVec 8)) (b8 b13 b18 b23 : BitVec 8)
      (w0 w4 : BitVec 64) (w1 w2 w3 w5 : BitVec 32),
      hex32.length = 32 ∧
      s[8]? = some b8 ∧ s[13]? = some b13 ∧ s[18]? = some b18 ∧ s[23]? = some b23 ∧
      s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++ s.drop 24 = hex32 ∧
      (∀ p : BitVec 64,
        (p ↦ᵣ s) =
          (p ↦₆₄ᵣ w0) ∗ ((p + 8#64) ↦₈ᵣ b8) ∗ ((p + 9#64) ↦₃₂ᵣ w1) ∗
          ((p + 13#64) ↦₈ᵣ b13) ∗ ((p + 14#64) ↦₃₂ᵣ w2) ∗ ((p + 18#64) ↦₈ᵣ b18) ∗
          ((p + 19#64) ↦₃₂ᵣ w3) ∗ ((p + 23#64) ↦₈ᵣ b23) ∗ ((p + 24#64) ↦₆₄ᵣ w4) ∗
          ((p + 32#64) ↦₃₂ᵣ w5)) ∧
      (∀ sp : BitVec 64,
        (((sp - 88#64) ↦₆₄ w0) ∗ ((sp - 80#64) ↦₃₂ w1) ∗ ((sp - 76#64) ↦₃₂ w2) ∗
         ((sp - 72#64) ↦₃₂ w3) ∗ ((sp - 68#64) ↦₆₄ w4) ∗ ((sp - 60#64) ↦₃₂ w5)) =
        ((sp - 88#64) ↦ₛ hex32)) := by
  let s0 := s.take 8
  let b8 := s[8]'(by omega)
  let s1 := (s.drop 9).take 4
  let b13 := s[13]'(by omega)
  let s2 := (s.drop 14).take 4
  let b18 := s[18]'(by omega)
  let s3 := (s.drop 19).take 4
  let b23 := s[23]'(by omega)
  let s4 := (s.drop 24).take 8
  let s5 := s.drop 32
  have hs0 : s0.length = 8 := by simp [s0, h]
  have hs1 : s1.length = 4 := by simp [s1, h]
  have hs2 : s2.length = 4 := by simp [s2, h]
  have hs3 : s3.length = 4 := by simp [s3, h]
  have hs4 : s4.length = 8 := by simp [s4, h]
  have hs5 : s5.length = 4 := by simp [s5, h]
  rcases exists_word64_both_of_length_8 s0 hs0 with ⟨w0, hw0_ro, hw0_rw⟩
  rcases exists_word32_both_of_length_4 s1 hs1 with ⟨w1, hw1_ro, hw1_rw⟩
  rcases exists_word32_both_of_length_4 s2 hs2 with ⟨w2, hw2_ro, hw2_rw⟩
  rcases exists_word32_both_of_length_4 s3 hs3 with ⟨w3, hw3_ro, hw3_rw⟩
  rcases exists_word64_both_of_length_8 s4 hs4 with ⟨w4, hw4_ro, hw4_rw⟩
  rcases exists_word32_both_of_length_4 s5 hs5 with ⟨w5, hw5_ro, hw5_rw⟩
  have hs24 : s.drop 24 = s4 ++ s5 := by
    dsimp only [s4, s5]
    rw [show (32 : Nat) = 24 + 8 from rfl, ← List.drop_drop, List.take_append_drop]
  let hex32 := s0 ++ (s1 ++ (s2 ++ (s3 ++ (s4 ++ s5))))
  have hhex_eq : s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++ s.drop 24 = hex32 := by
    simp only [s0, s1, s2, s3, hs24, hex32, List.append_assoc]
  have hhex_len : hex32.length = 32 := by
    simp only [hex32, List.length_append, hs0, hs1, hs2, hs3, hs4, hs5]
  have hs_decomp : s = s0 ++ ([b8] ++ (s1 ++ ([b13] ++ (s2 ++ ([b18] ++ (s3 ++ ([b23] ++ (s4 ++ s5)))))))) := by
    have e1 : s = s0 ++ ([b8] ++ s.drop 9) :=
      drop_eq_take_append_cons_drop s 0 8 (by omega)
    have e2 : s.drop 9 = s1 ++ ([b13] ++ s.drop 14) :=
      drop_eq_take_append_cons_drop s 9 4 (by omega)
    have e3 : s.drop 14 = s2 ++ ([b18] ++ s.drop 19) :=
      drop_eq_take_append_cons_drop s 14 4 (by omega)
    have e4 : s.drop 19 = s3 ++ ([b23] ++ s.drop 24) :=
      drop_eq_take_append_cons_drop s 19 4 (by omega)
    rw [e1, e2, e3, e4, hs24]
  refine ⟨hex32, b8, b13, b18, b23, w0, w4, w1, w2, w3, w5, hhex_len,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    hhex_eq, ?_, ?_⟩
  · intro p
    conv => lhs; rw [hs_decomp]
    rw [pointsToBytesRO_append, pointsToBytesRO_append, pointsToBytesRO_append,
        pointsToBytesRO_append, pointsToBytesRO_append, pointsToBytesRO_append,
        pointsToBytesRO_append, pointsToBytesRO_append, pointsToBytesRO_append]
    simp only [hs0, hs1, hs2, hs3, hs4, List.length_singleton,
      hw0_ro, hw1_ro, hw2_ro, hw3_ro, hw4_ro, hw5_ro, pointsToBytesRO_singleton,
      BitVec.add_assoc, BitVec.reduceAdd]
  · intro sp
    symm
    dsimp only [hex32]
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
        pointsToBytes_append, pointsToBytes_append]
    simp only [hs0, hs1, hs2, hs3, hs4, hw0_rw, hw1_rw, hw2_rw, hw3_rw, hw4_rw, hw5_rw, arm64_norm]

private theorem exists_38_parts_ro (bs : List (BitVec 8)) (h : bs.length = 38) :
    ∃ (b0 b37 : BitVec 8) (s36 : List (BitVec 8)),
      s36.length = 36 ∧
      bs = [b0] ++ (s36 ++ [b37]) ∧
      uuidTryParse bs =
        (if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none) ∧
      (∀ p : BitVec 64,
        (p ↦ᵣ bs) =
          ((p + 1#64) ↦ᵣ s36) ∗ ((p ↦₈ᵣ b0) ∗ ((p + 37#64) ↦₈ᵣ b37))) := by
  let b0 := bs[0]'(by omega)
  let s36 := (bs.drop 1).take 36
  let b37 := bs[37]'(by omega)
  have hs36 : s36.length = 36 := by simp [s36, h]
  have hbs0 : bs = [b0] ++ bs.drop 1 := by
    conv => lhs; rw [← List.take_append_drop 1 bs]
    rw [List.take_one, List.head?_eq_getElem?, getElem?_pos bs 0 (by omega), Option.toList_some]
  have hbs1 : bs.drop 1 = s36 ++ [b37] := by
    have := drop_eq_take_append_cons_drop bs 1 36 (by omega)
    have h38 : bs.drop 38 = [] := List.drop_eq_nil_of_le (by omega)
    rw [h38, List.append_nil] at this
    exact this
  have hbs : bs = [b0] ++ (s36 ++ [b37]) := by rw [hbs0, hbs1]
  have hhead : bs.head? = some b0 := by simp [hbs]
  have hlast : bs.getLast? = some b37 := by
    have : bs = ([b0] ++ s36) ++ [b37] := by simp [hbs]
    rw [this, List.getLast?_concat]
  have hdrop : bs.tail.take 36 = s36 := by rw [hbs0]; rfl
  have huuid : uuidTryParse bs =
      (if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none) := by
    unfold uuidTryParse
    simp [h, hhead, hlast, hdrop]
  refine ⟨b0, b37, s36, hs36, hbs, huuid, fun p => ?_⟩
  have h1 := pointsToBytesRO_append p [b0] (s36 ++ [b37])
  have h2 := pointsToBytesRO_append (p + 1#64) s36 [b37]
  have hlen36 : BitVec.ofNat 64 s36.length = 36#64 := by rw [hs36]
  have hp37 : p + 1#64 + 36#64 = p + 37#64 := by bv_arith
  rw [hbs, h1, pointsToBytesRO_singleton p b0]
  change (p ↦₈ᵣ b0) ∗ ((p + 1#64) ↦ᵣ (s36 ++ [b37])) = _
  rw [h2, hlen36, hp37, pointsToBytesRO_singleton (p + 37#64) b37]
  simp only [sepConj_left_comm]

private theorem pointsToBytesRO9_eq (p : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) :
    (p ↦ᵣ [b0, b1, b2, b3, b4, b5, b6, b7, b8]) =
      (p ↦₈ᵣ b0) ∗ ((p + 1#64) ↦₈ᵣ b1) ∗ ((p + 2#64) ↦₈ᵣ b2) ∗ ((p + 3#64) ↦₈ᵣ b3) ∗
      ((p + 4#64) ↦₈ᵣ b4) ∗ ((p + 5#64) ↦₈ᵣ b5) ∗ ((p + 6#64) ↦₈ᵣ b6) ∗
      ((p + 7#64) ↦₈ᵣ b7) ∗ ((p + 8#64) ↦₈ᵣ b8) := by
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem exists_45_parts_ro (bs : List (BitVec 8)) (h : bs.length = 45) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) (s36 : List (BitVec 8)),
      s36.length = 36 ∧
      uuidTryParse bs =
        (if 0x75#8 = b0 ∧ 0x72#8 = b1 ∧ 0x6e#8 = b2 ∧ 0x3a#8 = b3 ∧
            0x75#8 = b4 ∧ 0x75#8 = b5 ∧ 0x69#8 = b6 ∧ 0x64#8 = b7 ∧ 0x3a#8 = b8
         then parseHyphenated s36 else none) ∧
      (∀ p : BitVec 64,
        (p ↦ᵣ bs) =
          ((p + 9#64) ↦ᵣ s36) ∗
          ((p ↦₈ᵣ b0) ∗ ((p + 1#64) ↦₈ᵣ b1) ∗ ((p + 2#64) ↦₈ᵣ b2) ∗ ((p + 3#64) ↦₈ᵣ b3) ∗
           ((p + 4#64) ↦₈ᵣ b4) ∗ ((p + 5#64) ↦₈ᵣ b5) ∗ ((p + 6#64) ↦₈ᵣ b6) ∗
           ((p + 7#64) ↦₈ᵣ b7) ∗ ((p + 8#64) ↦₈ᵣ b8))) := by
  let pfx := bs.take 9
  let s36 := bs.drop 9
  have hpfx_len : pfx.length = 9 := by simp [pfx, h]
  have hs36_len : s36.length = 36 := by simp [s36, h]
  rcases exists_word9_of_length_9 pfx hpfx_len with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, hpfx⟩
  have hbs : bs = [b0, b1, b2, b3, b4, b5, b6, b7, b8] ++ s36 := by
    rw [← hpfx]
    exact (List.take_append_drop 9 bs).symm
  have huuid : uuidTryParse bs =
      (if 0x75#8 = b0 ∧ 0x72#8 = b1 ∧ 0x6e#8 = b2 ∧ 0x3a#8 = b3 ∧
          0x75#8 = b4 ∧ 0x75#8 = b5 ∧ 0x69#8 = b6 ∧ 0x64#8 = b7 ∧ 0x3a#8 = b8
       then parseHyphenated s36 else none) := by
    unfold uuidTryParse
    rw [urnPrefix_val]
    simp [hbs, hs36_len, List.isPrefixOf]
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, s36, hs36_len, huuid, fun p => ?_⟩
  have h1 := pointsToBytesRO_append p [b0, b1, b2, b3, b4, b5, b6, b7, b8] s36
  have hlen9 : BitVec.ofNat 64 [b0, b1, b2, b3, b4, b5, b6, b7, b8].length = 9#64 := rfl
  rw [hbs, h1, hlen9, pointsToBytesRO9_eq p b0 b1 b2 b3 b4 b5 b6 b7 b8, sepConj_comm]

private theorem pointsToBytesRO_cons4 (p : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (bs' : List (BitVec 8)) :
    (p ↦ᵣ (b0 :: b1 :: b2 :: b3 :: bs')) =
      (p ↦₃₂ᵣ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((p + 4#64) ↦ᵣ bs') := by
  change (p ↦ᵣ ([b0, b1, b2, b3] ++ bs')) = _
  rw [pointsToBytesRO_append, pointsToBytesRO4_eq_pointsTo32RO]
  rfl

/-! ## `uuid::parser::decode_hex32` (Block `254`) -/

private theorem decode_hex32_iter_step_ro_fs_placed [LibsignalPlacement]
    (hooks : String → Option (State → State))
    (target_pc : BitVec 64) (s0 s : State) (out src sp' acc : BitVec 64) (i : Nat)
    (c old_b : BitVec 8) (Frame : SepProp) (post : State → SepProp → Prop)
    (hinv : DecodeLoopInvFs (blkPl_254).base s0 s out src sp' acc i)
    (hnext : ∀ s' : State,
      s'.pc = (if (BitVec.ofNat 64 i + 1#64 != 32#64) = true
               then (blkPl_254).base + 20#64
               else (blkPl_254).base + 88#64) →
      s'.status = .Running →
      s'.sp = sp' →
      s'.readReg64 (Reg.gpr 0#5) = out →
      s'.readReg64 (Reg.gpr 1#5) = src →
      s'.readReg64 (Reg.gpr 8#5) = stepAcc acc c →
      s'.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 (i + 1) →
      s'.readReg64 (Reg.gpr 10#5) = sp' →
      s'.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) →
      s'.trace = s0.trace →
      s'.fs = s0.fs →
      CalleeSavedPreserved s0 s' →
      SepWP ((blkPC_254).rebase (blkPl_254).base hooks) target_pc s'
        (((src + BitVec.ofNat 64 i) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame) post) :
    SepWP ((blkPC_254).rebase (blkPl_254).base hooks) target_pc s
      (((src + BitVec.ofNat 64 i) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ old_b) ∗ Frame) post := by
  rcases hinv with ⟨⟨hpc, hrun, hsp, hsp_align, hx0, hx1, hx8, hx9, hx10, hx30, htrace, hcs⟩, hfs⟩
  have hsp' : s.sp &&& 15#64 = 0#64 := hsp ▸ hsp_align
  wp_steps
  refine SepWP.weaken_pre
    (show _ ⊢ (((src + BitVec.ofNat 64 i) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame) from
      Entails.of_eq (congrArg
        (fun b => ((src + BitVec.ofNat 64 i) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ b) ∗ Frame)
        (by clear * -; revert c; decide))) ?_
  apply hnext
  · rfl
  · simp only [arm64_norm, hrun]
  · simp only [arm64_norm, hsp]
  · simp only [arm64_norm, hx0]
  · simp only [arm64_norm, hx1]
  · simp only [arm64_norm, hx8]
    unfold stepAcc
    exact congrArg
      (fun v => BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 acc) ||| v)))
      (by clear * -; revert c; decide)
  · simp only [arm64_norm, BitVec.ofNat_add]
  · simp only [arm64_norm, hx10]
  · simp only [arm64_norm, hx30]
  · simp only [arm64_norm, htrace]
  · simp only [arm64_norm, hfs]
  · simp (config := { decide := true }) only [arm64_norm, hcs]

private theorem decode_hex32_loop_ro_fs_placed [LibsignalPlacement]
    (hooks : String → Option (State → State))
    (target_pc : BitVec 64) (s0 : State) (out src sp' : BitVec 64)
    (post : State → SepProp → Prop) :
    ∀ (rem_src rem_sp : List (BitVec 8)) (i : Nat) (acc : BitVec 64)
      (s : State) (Frame : SepProp),
      rem_src ≠ [] →
      rem_sp.length = rem_src.length →
      i + rem_src.length = 32 →
      DecodeLoopInvFs (blkPl_254).base s0 s out src sp' acc i →
      (∀ sf : State,
        DecodeLoopPostFs (blkPl_254).base s0 sf out src sp' (rem_src.foldl stepAcc acc) →
        SepWP ((blkPC_254).rebase (blkPl_254).base hooks) target_pc sf
          (((src + BitVec.ofNat 64 i) ↦ᵣ rem_src) ∗
           ((sp' + BitVec.ofNat 64 i) ↦ₛ (rem_src.map rawNibble)) ∗ Frame) post) →
      SepWP ((blkPC_254).rebase (blkPl_254).base hooks) target_pc s
        (((src + BitVec.ofNat 64 i) ↦ᵣ rem_src) ∗
         ((sp' + BitVec.ofNat 64 i) ↦ₛ rem_sp) ∗ Frame) post
  | [], _, _, _, _, _, hne, _, _, _, _ => absurd rfl hne
  | c :: rest_src, rem_sp, i, acc, s, Frame, _, hlen_sp, hi_sum, hinv, hcont => by
    rcases rem_sp with _ | ⟨old_b, rest_sp⟩
    · simp at hlen_sp
    have hsplit_pre :
        (((src + BitVec.ofNat 64 i) ↦ᵣ (c :: rest_src)) ∗
         ((sp' + BitVec.ofNat 64 i) ↦ₛ (old_b :: rest_sp)) ∗ Frame) =
        (((src + BitVec.ofNat 64 i) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ old_b) ∗
         (((src + BitVec.ofNat 64 (i + 1)) ↦ᵣ rest_src) ∗
          ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗ Frame)) := by
      rw [pointsToBytesRO_cons_off src i c rest_src, pointsToBytes_cons_off sp' i old_b rest_sp]
      sep_ac_rfl
    rw [hsplit_pre]
    refine decode_hex32_iter_step_ro_fs_placed hooks target_pc s0 s out src sp' acc i c old_b
      (((src + BitVec.ofNat 64 (i + 1)) ↦ᵣ rest_src) ∗
       ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗ Frame) post hinv ?_
    intro s' hpc' hrun' hsp' hx0' hx1' hx8' hx9' hx10' hx30' htrace' hfs' hcs'
    rcases rest_src with _ | ⟨c2, rest_src'⟩
    · have hi31 : i = 31 := by simp at hi_sum; omega
      subst hi31
      have hpc_done : s'.pc = (blkPl_254).base + 88#64 := by
        simpa using hpc'
      have hpost_inv : DecodeLoopPostFs (blkPl_254).base s0 s' out src sp' ([c].foldl stepAcc acc) :=
        ⟨⟨hpc_done, hrun', hsp', hinv.inv.hsp_align, hx0', hx1', hx8', hx30', htrace', hcs'⟩, hfs'⟩
      have hrest_sp : rest_sp = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen_sp)
      subst hrest_sp
      have hrecomb :
          (((src + BitVec.ofNat 64 31) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 31) ↦₈ rawNibble c) ∗
           (((src + BitVec.ofNat 64 (31 + 1)) ↦ᵣ []) ∗
            ((sp' + BitVec.ofNat 64 (31 + 1)) ↦ₛ []) ∗ Frame)) =
          (((src + BitVec.ofNat 64 31) ↦ᵣ [c]) ∗
           ((sp' + BitVec.ofNat 64 31) ↦ₛ ([c].map rawNibble)) ∗ Frame) := by
        simp only [List.map_cons, List.map_nil, pointsToBytesRO_singleton, pointsToBytesRO_nil,
          pointsToBytes_singleton, pointsToBytes_nil, emp_sepConj]
      rw [hrecomb]
      exact hcont s' hpost_inv
    · have hi_lt : i + 1 < 32 := by simp at hi_sum; omega
      have hbne : (BitVec.ofNat 64 i + 1#64 != 32#64) = true := bne_32_of_lt hi_lt
      simp only [hbne, ↓reduceIte] at hpc'
      have hnext_inv : DecodeLoopInvFs (blkPl_254).base s0 s' out src sp' (stepAcc acc c) (i + 1) :=
        ⟨⟨hpc', hrun', hsp', hinv.inv.hsp_align, hx0', hx1', hx8', hx9', hx10', hx30', htrace', hcs'⟩,
         hfs'⟩
      have hrearr1 :
          (((src + BitVec.ofNat 64 i) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗
           (((src + BitVec.ofNat 64 (i + 1)) ↦ᵣ (c2 :: rest_src')) ∗
            ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗ Frame)) =
          (((src + BitVec.ofNat 64 (i + 1)) ↦ᵣ (c2 :: rest_src')) ∗
           ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗
           (((src + BitVec.ofNat 64 i) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame)) := by
        sep_ac_rfl
      rw [hrearr1]
      refine decode_hex32_loop_ro_fs_placed hooks target_pc s0 out src sp' post
        (c2 :: rest_src') rest_sp (i + 1) (stepAcc acc c) s'
        (((src + BitVec.ofNat 64 i) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame)
        (List.cons_ne_nil _ _) (by simp at hlen_sp; omega) (by simp at hi_sum ⊢; omega)
        hnext_inv ?_
      intro sf hpost_sf
      have hrearr2 :
          (((src + BitVec.ofNat 64 (i + 1)) ↦ᵣ (c2 :: rest_src')) ∗
           ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ ((c2 :: rest_src').map rawNibble)) ∗
           (((src + BitVec.ofNat 64 i) ↦₈ᵣ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame)) =
          (((src + BitVec.ofNat 64 i) ↦ᵣ (c :: c2 :: rest_src')) ∗
           ((sp' + BitVec.ofNat 64 i) ↦ₛ ((c :: c2 :: rest_src').map rawNibble)) ∗ Frame) := by
        simp only [List.map_cons]
        rw [pointsToBytesRO_cons_off src i c (c2 :: rest_src'),
            pointsToBytes_cons_off sp' i (rawNibble c) (rawNibble c2 :: List.map rawNibble rest_src')]
        sep_ac_rfl
      rw [hrearr2]
      exact hcont sf hpost_sf

private theorem decode_hex32_post_err_ro_fs_placed [LibsignalPlacement]
    (hooks : String → Option (State → State))
    (s0 sf : State) (out src : BitVec 64) (hex : List (BitVec 8)) (R : SepProp)
    (hlen : hex.length = 32)
    (hall : hex.all isHexByte = false)
    (hpost : DecodeLoopPostFs (blkPl_254).base s0 sf out src (s0.sp - 32#64) (hex.foldl stepAcc 0#64)) :
    SepWP ((blkPC_254).rebase (blkPl_254).base hooks) (s0.readReg64 (Reg.gpr 30#5)) sf
      ((src ↦ᵣ hex) ∗ ((s0.sp - 32#64) ↦ₛ (hex.map rawNibble)) ∗ memRegion out 17 ∗ R)
      (fun s' Q =>
        s'.status = .Running ∧
        s'.sp = s0.sp ∧
        CalleeSavedPreserved s0 s' ∧
        (Q ⊢ decodeHex32ROSpec.keepsFs.post (out, src, hex) s0 s' ∗ R)) := by
  rcases hpost with ⟨⟨hpc, hrun, hsp, hsp_align, hx0, hx1, hx8_0, hx30, htrace, hcs⟩, hfs⟩
  have hx8 : sf.readReg64 (Reg.gpr 8#5) = 1#64 := by
    rw [hx8_0, foldl_stepAcc_zero, hall]; rfl
  clear hx8_0
  have hsp' : sf.sp &&& 15#64 = 0#64 := hsp ▸ hsp_align
  have hmem17 : memRegion out 17 = (∃∗ b0 : BitVec 8, out ↦₈ b0) ∗ memRegion (out + 1#64) 16 := by
    rw [show (17 : Nat) = 1 + 16 from rfl, memRegion_split out 1 16 (by decide), memRegion_one]
  rw [hmem17]
  wp_pull_exists
  wp_steps
  apply SepWP.done
  · rfl
  · simp only [arm64_norm, hrun]
  refine ⟨by simp only [arm64_norm, hrun], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hcs], ?_⟩
  have hdec : decodeHex32 hex = none := by
    rw [decodeHex32_of_length_32 hlen, hall]; rfl
  dsimp only [Spec.keepsFs, decodeHex32ROSpec]
  rw [hdec]
  dsimp only [decodeHex32ResultAt]
  simp only [arm64_norm, hfs, htrace, pure_true, emp_sepConj, sepConj_assoc]
  have hcells := pointsToBytes_entails_stackAt_32 s0.sp (hex.map rawNibble) (by simp [hlen])
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hcells)) ?_
  apply entails_of_eq
  sep_ac_rfl

private theorem decode_hex32_post_ok_ro_fs_placed [LibsignalPlacement]
    (hooks : String → Option (State → State))
    (s0 sf : State) (out src : BitVec 64) (hex : List (BitVec 8)) (R : SepProp)
    (hlen : hex.length = 32)
    (hall : hex.all isHexByte = true)
    (hpost : DecodeLoopPostFs (blkPl_254).base s0 sf out src (s0.sp - 32#64) (hex.foldl stepAcc 0#64)) :
    SepWP ((blkPC_254).rebase (blkPl_254).base hooks) (s0.readReg64 (Reg.gpr 30#5)) sf
      ((src ↦ᵣ hex) ∗ ((s0.sp - 32#64) ↦ₛ (hex.map rawNibble)) ∗ memRegion out 17 ∗ R)
      (fun s' Q =>
        s'.status = .Running ∧
        s'.sp = s0.sp ∧
        CalleeSavedPreserved s0 s' ∧
        (Q ⊢ decodeHex32ROSpec.keepsFs.post (out, src, hex) s0 s' ∗ R)) := by
  rcases hpost with ⟨⟨hpc, hrun, hsp, hsp_align, hx0, hx1, hx8_0, hx30, htrace, hcs⟩, hfs⟩
  have hx8 : sf.readReg64 (Reg.gpr 8#5) = 0#64 := by
    rw [hx8_0, foldl_stepAcc_zero, hall]; rfl
  clear hx8_0
  have hsp' : sf.sp &&& 15#64 = 0#64 := hsp ▸ hsp_align
  have hns_len : (hex.map rawNibble).length = 32 := by simp [hlen]
  rcases list_length_32_elim (hex.map rawNibble) hns_len with
    ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
     n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, hns⟩
  have hdec_len :
      (decodeNibbles [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
                      n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31]).length = 16 := rfl
  have hdec : decodeHex32 hex =
      some ⟨decodeNibbles [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
                           n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31],
            hdec_len⟩ := by
    rw [decodeHex32_of_length_32 hlen]
    simp only [hall, ↓reduceIte]
    congr 1
    exact Subtype.ext (congrArg decodeNibbles hns)
  have hdec_res : decodeHex32ResultAt out (decodeHex32 hex) =
      (out ↦₈ 1#8) ∗
      ((out + 1#64) ↦ₛ
        [rawCombine n0 n1, rawCombine n2 n3, rawCombine n4 n5, rawCombine n6 n7,
         rawCombine n8 n9, rawCombine n10 n11, rawCombine n12 n13, rawCombine n14 n15,
         rawCombine n16 n17, rawCombine n18 n19, rawCombine n20 n21, rawCombine n22 n23,
         rawCombine n24 n25, rawCombine n26 n27, rawCombine n28 n29, rawCombine n30 n31]) := by
    rw [hdec]; rfl
  rw [hns, ← hsp, pointsToBytes_32_expand sf.sp]
  rw [memRegion_eq_exists_bytes out 17 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro os
  wp_focus_pure; intro hos_len
  rcases list_length_17_elim os hos_len with
    ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, hos⟩
  rw [hos, pointsToBytes_17_expand out]
  wp_steps
  apply SepWP.done
  · rfl
  · simp only [arm64_norm, hrun]
  refine ⟨by simp only [arm64_norm, hrun], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hcs], ?_⟩
  dsimp only [Spec.keepsFs, decodeHex32ROSpec]
  simp only [arm64_norm, hfs, htrace, pure_true, emp_sepConj, sepConj_assoc, rawCombine_step_eq]
  rw [hdec_res, ← pointsToBytes_32_sub32_expand s0.sp, ← pointsToBytes_16_tail_expand out]
  have hcells := pointsToBytes_entails_stackAt_32 s0.sp
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
     n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31] rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hcells)) ?_
  apply entails_of_eq
  sep_ac_rfl

/-- Block `254` (`uuid::parser::decode_hex32`) meets `decodeHex32ROSpec.keepsFs` under `[LibsignalPlacement]`. -/
theorem decodeHex32_ro_placed_okFs [LibsignalPlacement]
    (hooks : String → Option (State → State)) :
    subroutine_ok ((blkPC_254).rebase (blkPl_254).base hooks) (blkPl_254).base
      decodeHex32ROSpec.keepsFs := by
  apply subroutine_ok_of_sepWP_entails
  intro ⟨out, src, hex⟩ R s0 hpc hrun hsp_align
  conv => arg 4; simp only [Spec.keepsFs, decodeHex32ROSpec, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0, hx1, hlen⟩
  conv => arg 4; rw [stackAt_32_split s0.sp]
  wp_pull_exists
  have hloop := decode_hex32_loop_ro_fs_placed hooks (s0.readReg64 (Reg.gpr 30#5)) s0 out src (s0.sp - 32#64)
  have herr := fun sf => decode_hex32_post_err_ro_fs_placed hooks s0 sf out src hex R hlen
  have hok := fun sf => decode_hex32_post_ok_ro_fs_placed hooks s0 sf out src hex R hlen
  wp_steps 5
  have hgroup :
      ((src ↦ᵣ hex) ∗ memRegion out 17 ∗
       ((s0.sp - 32#64) ↦₆₄ 0#64) ∗ ((s0.sp - 24#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 16#64) ↦₆₄ 0#64) ∗ ((s0.sp - 8#64) ↦₆₄ 0#64) ∗ R) =
      (((src + BitVec.ofNat 64 0) ↦ᵣ hex) ∗
       (((s0.sp - 32#64) + BitVec.ofNat 64 0) ↦ₛ List.replicate 32 0#8) ∗
       (memRegion out 17 ∗ R)) := by
    have h0a : src + BitVec.ofNat 64 0 = src := by bv_arith
    have h0b : s0.sp - 32#64 + BitVec.ofNat 64 0 = s0.sp - 32#64 := by bv_arith
    rw [h0a, h0b, ← stack32_zero_eq_replicate s0.sp]
    sep_ac_rfl
  rw [hgroup]
  have hsp32_align : (s0.sp - 32#64) &&& 15#64 = 0#64 := by
    unfold State.spAligned at hsp_align
    have h : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := s0.sp.isLt; omega
  have hhex_ne : hex ≠ [] := by intro h; simp [h] at hlen
  refine hloop _ hex (List.replicate 32 0#8) 0 0#64 _ (memRegion out 17 ∗ R)
    hhex_ne (by simp [hlen]) (by omega)
    ⟨⟨rfl, by simp only [arm64_norm, hrun], by simp only [arm64_norm],
      hsp32_align, by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm],
      by simp (config := { decide := true }) only [arm64_norm, CalleeSavedPreserved.rfl]⟩,
     by simp only [arm64_norm]⟩
    ?_
  intro sf hpost_sf
  have h0a : src + BitVec.ofNat 64 0 = src := by bv_arith
  have h0b : s0.sp - 32#64 + BitVec.ofNat 64 0 = s0.sp - 32#64 := by bv_arith
  rw [h0a, h0b]
  cases hall : hex.all isHexByte
  · exact herr sf hall hpost_sf
  · exact hok sf hall hpost_sf

/-! ## `VmPreserved` lifting and `ServiceId` parsing chain -/

private theorem sepWP_vm_step {P : Program} {b mid target : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq hwp fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm

private theorem sepWP_lscl_vm_step [LibsignalPlacement] {P : Program} {b mid target : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hwp : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧
      (LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post :=
  sepWP_seq_lscl hcl (mid := mid) (SepWP.mono hwp fun _ _ _ _ ⟨hvm, hk⟩ hcl' => hk hcl' hvm)

private def vmCore (s : State) := (s.brkStart, s.brk, s.tpidrEl0, s.physMemAvail, s.fs, s.mem.perm)
private theorem vmCore_setPC (s : State) (p : BitVec 64) : vmCore (s.setPC p) = vmCore s := by cases s; rfl
private theorem vmCore_advancePC (s : State) : vmCore s.advancePC = vmCore s := by cases s; rfl
private theorem vmCore_setPState (s : State) (p : PState) : vmCore (s.setPState p) = vmCore s := by cases s; rfl
private theorem vmCore_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : vmCore (s.writeReg64 r v) = vmCore s := by cases s; cases r <;> rfl
private theorem vmCore_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : vmCore (s.writeReg32 r v) = vmCore s := by cases s; cases r <;> rfl
private theorem vmCore_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) : vmCore (s.writeReg w r v) = vmCore s := by cases s; cases w <;> cases r <;> rfl
private theorem vmCore_setMem (s : State) (m : Memory) :
    vmCore (s.setMem m) = ((vmCore s).1, (vmCore s).2.1, (vmCore s).2.2.1, (vmCore s).2.2.2.1, (vmCore s).2.2.2.2.1, m.perm) := by cases s; rfl
private theorem vm_of_core {s1 s2 : State} (h : vmCore s1 = vmCore s2) : VmPreserved s1 s2 :=
  ⟨⟨(congrArg Prod.fst h).symm, (congrArg (fun x => x.2.1) h).symm, (congrArg (fun x => x.2.2.1) h).symm⟩,
    (congrArg (fun x => x.2.2.2.1) h).symm,
    fun a => congrFun (congrArg (fun x => x.2.2.2.2.2) h).symm a,
    LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (congrArg (fun x => x.2.2.2.2.1) h).symm⟩

local macro "vm_core_step" : tactic =>
  `(tactic| exact vm_of_core (by simp only [vmCore_setPC, vmCore_advancePC, vmCore_setPState,
    vmCore_writeReg64, vmCore_writeReg32, vmCore_writeReg, vmCore_setMem]))

attribute [local irreducible] VmPreserved

private theorem vm_chain {s0 s1 s2 : State} (h01 : VmPreserved s0 s1) (h12 : VmPreserved s1 s2) :
    VmPreserved s0 s2 := h01.trans h12

private theorem strip_codeLoaded_of_keep_local {P : Program} {m : Memory} (hL : P.CodeLoaded m) :
    P.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep P) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap; have hsub : P.base + BitVec.ofNat 64 i - P.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep P (P.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep; rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_of_keep_local (P : Program) (m : Memory) :
    P.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep P) m) :=
  fun _ hx => of_decide_eq_true (ProofLib.strip_perm_x_imp hx).2

private theorem findSome?_override_none_local : ∀ (l : List (String × Nat)) (off : Nat),
    (l.findSome? fun (_, o) => if o == off then (none : Option (State → State)) else none) = none
  | [], _ => rfl
  | (_, _) :: tl, off => by dsimp only [List.findSome?]; rw [ite_self]; exact findSome?_override_none_local tl off

private theorem findSome?_trapHooks_some_local : ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
    (l.findSome? fun (n, o) => if o == off then trapHooks n else none) = some f →
    f = fun s => s.setStatus (.Exception "extern")
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons, trapHooks] at h
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte, Option.some.injEq] at h; exact h.symm
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h; exact findSome?_trapHooks_some_local tl h

private theorem findSome?_stubs_eq_none_local (Hk : String → Option (State → State)) :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then trapHooks n else none) = none →
      (l.findSome? fun (n, o) => if o == off then Hk n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    simp only [List.findSome?_cons, trapHooks] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h; cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact findSome?_stubs_eq_none_local Hk tl h

private theorem externAt?_rebase_trapHooks_some_local {P : Program} {b pc : BitVec 64} {f : State → State}
    (h : (P.rebase b trapHooks).externAt? pc = some f) : f = fun s => s.setStatus (.Exception "extern") := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at h; dsimp only at h
  rw [findSome?_override_none_local] at h
  cases hm : (P.stubs.findSome? fun (n, o) => if o == (pc - b).toNat then trapHooks n else none) with
  | none => rw [hm] at h; cases h
  | some g => rw [hm] at h; injection h with hgf; subst hgf; exact findSome?_trapHooks_some_local P.stubs hm

private theorem externAt?_rebase_eq_none_of_trapHooks_local {P : Program} {b pc : BitVec 64}
    {Hk : String → Option (State → State)} (h : (P.rebase b trapHooks).externAt? pc = none) :
    (P.rebase b Hk).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at h ⊢; dsimp only at h ⊢
  rw [findSome?_override_none_local] at h ⊢
  have h1 : (P.stubs.findSome? fun (n, o) => if o == (pc - b).toNat then trapHooks n else none) = none := by
    cases hm : (P.stubs.findSome? fun (n, o) => if o == (pc - b).toNat then trapHooks n else none) with
    | none => rfl
    | some _ => rw [hm] at h; cases h
  rw [findSome?_stubs_eq_none_local Hk P.stubs h1]; rfl

private theorem steps_start_running_local {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_blk254_lift_strip [LibsignalPlacement] (H : LibsignalHooks)
    (hall_svc : ((blkPC_254).rebase (blkPl_254).base trapHooks).allInstrs (fun ins => !ins.isSvc0) = true)
    (hall_msr : ((blkPC_254).rebase (blkPl_254).base trapHooks).allInstrs (fun ins => !ins.isMsrTpidrEl0) = true)
    {s1' sf' : State} (hsteps : Steps ((blkPC_254).rebase (blkPl_254).base trapHooks) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let Q := (blkPC_254).rebase (blkPl_254).base trapHooks
    let P := (blkPC_254).rebase (blkPl_254).base H
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep Q) s1 → Q.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep Q) sf ∧
        Steps P s1 sf ∧ ProofLib.NonSyscallPreserved s1 sf ∧ sf.tpidrEl0 = s1.tpidrEl0 := by
  intro Q P
  induction hsteps with
  | refl => exact fun s1 hs1 _ => ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1, rfl⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1; have hrb' : sb'.status = .Running := steps_start_running_local hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ =>
      rw [externAt?_rebase_trapHooks_some_local he] at hrb'
      cases s1; cases hrb'
    | extern_fault _ _ _ => cases s1; cases hrb'
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := (by cases s1; exact hr1')
      have hL1' := strip_codeLoaded_of_keep_local hL1
      have hexec' := strip_execOnlyIn_of_keep_local Q s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_svc hL1' hexec' _ inst hfe'
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
      have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := (by cases s1; rfl)
      have hmem_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).mem =
          ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem := (by cases s1; rfl)
      have hext_trap : Q.externAt? s1.pc = none := by
        rw [hpc_eq] at hfe'
        cases he : Q.externAt? s1.pc with
        | none => rfl
        | some _ => unfold Program.fetchMem at hfe'; rw [he] at hfe'; cases hfe'
      have hext_P : P.externAt? s1.pc = none :=
        externAt?_rebase_eq_none_of_trapHooks_local (Hk := H) hext_trap
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        rw [hpc_eq, hmem_eq] at hfe'; unfold Program.fetchMem at hfe' ⊢
        rw [hext_trap] at hfe'; rw [hext_P]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
          split at hfe'
          · contradiction
          · rename_i hce'
            have hce : s1.mem.canExec s1.pc 4 = true := by
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
              unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk; have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem).read32 s1.pc =
                s1.mem.read32 s1.pc := by simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'; simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
      have hev_Q : Q.evalInst inst (ProofLib.stripS (ProofLib.progKeep Q) s1) =
          ProofLib.stripS (ProofLib.progKeep Q) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have htp_1 : (execInst inst s1).tpidrEl0 = s1.tpidrEl0 := by
        refine Step.tpidrEl0_of_noMsrTpidrEl0 (prog := P) ?_ ?_ hstep_P
        · intro i hfi; rw [hfe_P] at hfi; injection hfi with h_eq; subst h_eq; exact hnmsr
        · intro _ hfk; rw [hext_P] at hfk; cases hfk
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest, htp_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_Q (hstep_P.codeLoaded hL1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest,
        htp_rest.trans htp_1⟩

private theorem blk254_vm_lift [LibsignalPlacement] {α : Type} {spec : Spec α}
    (H : LibsignalHooks)
    (hok : subroutine_ok ((blkPC_254).rebase (blkPl_254).base trapHooks) (blkPl_254).base spec)
    (hpre_strip : ∀ (x : α) (k : BitVec 64 → Bool) (s0 : State),
      spec.pre x (ProofLib.stripS k s0) = spec.pre x s0)
    (hpost_strip : ∀ (x : α) (k : BitVec 64 → Bool) (s0 sf : State),
      spec.post x (ProofLib.stripS k s0) (ProofLib.stripS k sf) = spec.post x s0 sf)
    (hpan : ∀ (x : α) (s0 sf : State), spec.onPanic x s0 sf = ⌜False⌝)
    (hexit : ∀ (x : α) (c : BitVec 64) (s0 sf : State), spec.onExit x c s0 sf = ⌜False⌝)
    (hoom : ∀ (x : α) (s0 sf : State), spec.onOom x s0 sf = ⌜False⌝) :
    subroutine_ok ((blkPC_254).rebase (blkPl_254).base H)
      (blkPl_254).base
      (withVmPreserved spec) := by
  apply subroutine_ok_intro
  intro x R s0 hpc hrun hpre hal hL
  let Q := (blkPC_254).rebase (blkPl_254).base trapHooks
  have hQ_eq : Q = libsignalSessionLib.blockProgram lsmpl 254 trapHooks :=
    (inferInstance : IsLsBlockProg Q 254 trapHooks).eq_blockProgram
  have hall_svc : Q.allInstrs (fun ins => !ins.isSvc0) = true := by
    rw [hQ_eq]
    exact PlacedLib.program_noSvc0_of_patchSafe
      (lib := libsignalSessionLib.blockLib 254) (by rfl) blkPl_254 trapHooks
  have hall_msr : Q.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true := by
    rw [hQ_eq]
    exact PlacedLib.program_noMsrTpidrEl0_of_patchSafe
      (lib := libsignalSessionLib.blockLib 254) (by rfl) blkPl_254 trapHooks
  let keep := ProofLib.progKeep Q
  have hL_Q : Q.CodeLoaded s0.mem := hL.of_base_code rfl rfl
  have hL_strip : Q.CodeLoaded (ProofLib.stripExecOutside keep s0.mem) :=
    strip_codeLoaded_of_keep_local hL_Q
  dsimp only [withVmPreserved] at hpre
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hpre
  have hpc_s : (ProofLib.stripS keep s0).pc = (blkPl_254).base := by cases s0; exact hpc
  have hrun_s : (ProofLib.stripS keep s0).status = .Running := by cases s0; exact hrun
  have hal_s : (ProofLib.stripS keep s0).spAligned = true := by cases s0; exact hal
  have hm_s : (ProofLib.stripS keep s0).mem ⊨ spec.pre x (ProofLib.stripS keep s0) ∗ R_view := by
    rw [hpre_strip]
    cases s0; exact hm_strip
  obtain ⟨sf', hstepsQ, ⟨hpc_f', hrun_f', hpost', hcc'⟩ | ⟨_, hoom'⟩⟩ :=
    subroutine_ok_apply_full (oom := fun _ => False) hok
      x R_view hpc_s hrun_s hm_s hal_s
      (by intro _ _ hp; rw [hpan] at hp; exact not_satisfies_false_sepConj hp)
      (by intro _ _ _ he; rw [hexit] at he; exact not_satisfies_false_sepConj he)
      (by intro _ _ ho; rw [hoom] at ho; exact not_satisfies_false_sepConj ho)
      hL_strip
  · obtain ⟨sf, hsf_eq, hstepsP, hnsp, htp⟩ :=
      steps_blk254_lift_strip H hall_svc hall_msr hstepsQ hrun_f' s0 rfl hL_Q
    have hvm : VmPreserved s0 sf := hnsp.toVmPreserved htp
    have hperm_eq : ∀ a, sf.mem.perm a = s0.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hpost_mem' : ProofLib.stripExecOutside keep sf.mem ⊨
        spec.post x s0 sf ∗ R_view := by
      rw [hsf_eq, hpost_strip] at hpost'
      cases sf; exact hpost'
    have hpost_mem : sf.mem ⊨ spec.post x s0 sf ∗ R :=
      hunstrip hperm_eq hpost_mem'
    have hpc_f : sf.pc = s0.readReg64 .x30 := by rw [hsf_eq] at hpc_f'; cases s0; cases sf; exact hpc_f'
    have hsp_f : sf.sp = s0.sp := by have hsp_f' := hcc'.1; rw [hsf_eq] at hsp_f'; cases s0; cases sf; exact hsp_f'
    have hrun_f : sf.status = .Running := by rw [hsf_eq] at hrun_f'; cases sf; exact hrun_f'
    have hcs_f : CalleeSavedPreserved s0 sf := by
      have hcs' := hcc'.2; rw [hsf_eq] at hcs'; cases s0; cases sf; exact hcs'
    refine ⟨sf, hstepsP, Or.inl ⟨hpc_f, hrun_f, ?_, ⟨hsp_f, hcs_f⟩⟩⟩
    dsimp only [withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, hpost_mem⟩
  · exact False.elim hoom'

private theorem decodeHex32_placed_vm_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_254).rebase (blkPl_254).base H)
      (blkPl_254).base
      (withVmPreserved decodeHex32Spec.keepsFs) :=
  blk254_vm_lift H (decodeHex32_placed_okFs trapHooks)
    (fun _ _ s0 => by cases s0; rfl)
    (fun _ _ s0 sf => by cases s0; cases sf; rfl)
    (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)

private theorem decodeHex32_ro_placed_vm_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_254).rebase (blkPl_254).base H)
      (blkPl_254).base
      (withVmPreserved decodeHex32ROSpec.keepsFs) :=
  blk254_vm_lift H (decodeHex32_ro_placed_okFs trapHooks)
    (fun _ _ s0 => by cases s0; rfl)
    (fun _ _ s0 sf => by cases s0; cases sf; rfl)
    (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl)

private abbrev parserPostROVm (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64)
    (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨ (withVmPreserved parserTryParseROSpec.keepsFs).post (p, bs, out17) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev parserFrameSep (sliceP : SepProp) (out17 : BitVec 64)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 : State) : SepProp :=
  ((sliceP ∗ (out17 ↦₆₄ out_w0) ∗ ((out17 + 8#64) ↦₆₄ out_w1) ∗ ((out17 + 16#64) ↦₈ out_b2)) ∗
   (stackAt (s0.sp - 96#64) 0x20 ∗ memRegion (s0.sp - 96#64) 8 ∗ memRegion (s0.sp - 88#64) 32 ∗
    memRegion (s0.sp - 56#64) 4 ∗ memRegion (s0.sp - 52#64) 17 ∗ memRegion (s0.sp - 35#64) 3 ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))

private theorem wp_err_ro_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hsp_align : s0.spAligned = true) (huuid : uuidTryParse bs = none)
    (hpc : s.pc = (blkPl_255).base + bv% (420)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx8 : s.readReg64 .x8 = out17)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep (p ↦ᵣ bs) out17 out_w0 out_w1 out_b2 s0)
      (parserPostROVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  dsimp only [parserFrameSep]
  apply sepWP_vm_step (mid := s0.readReg64 .x30)
  by_vm_steps
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
    have hvm_tot := vm_chain hvm0 hvm1
    unfold parserPostROVm withVmPreserved Spec.keepsFs parserTryParseROSpec
    simp only [huuid, parserTryParseResultAt, stackAt_parser_split s0.sp]
    wp_done

private theorem wp_simple_ro_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 32) (hpc : s.pc = (blkPl_255).base + bv% (328))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p) (hx8 : s.readReg64 .x8 = out17)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep (p ↦ᵣ bs) out17 out_w0 out_w1 out_b2 s0)
      (parserPostROVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_255).rebase (blkPl_255).base hooks) (decodeHex32_ro_placed_vm_ok hooks)
  change subroutine_ok _ (lsmpl.base 254) _ at hcallee_hex
  simp only [withLsCl, withVmPreserved, Spec.keepsFs, decodeHex32ROSpec, sepConj_assoc] at hcallee_hex
  have huuid : uuidTryParse bs = decodeHex32 bs := by unfold uuidTryParse parseSimple; simp [hlen]
  dsimp only [parserFrameSep]
  rw [memRegion_sp88_32_for_simple s0.sp]
  apply sepWP_lscl_vm_step hcl0 (mid := lsmpl.base 254)
  by_vm_steps
    wp_steps
    refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun _hcl_call hvm1 => ?_⟩
    have hvm01 := vm_chain hvm0 hvm1
    wp_apply
    have hvm_hex := vm_chain hvm01 ‹_›
    cases hdec : decodeHex32 bs with
    | none =>
      rw [decodeHex32ResultAt_sp88_none s0.sp, hsp]
      apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm_hex hvm2
        unfold parserPostROVm withVmPreserved Spec.keepsFs parserTryParseROSpec
        simp only [huuid, hdec, parserTryParseResultAt, stackAt_parser_split s0.sp,
          memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_none s0.sp]
        wp_done
    | some u =>
      rw [decodeHex32ResultAt_sp88_some s0.sp u, hsp]
      apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm_hex hvm2
        unfold parserPostROVm withVmPreserved Spec.keepsFs parserTryParseROSpec
        simp only [huuid, hdec, parserTryParseResultAt_some_eq, stackAt_parser_split s0.sp,
          memRegion_sp88_32_for_simple s0.sp, memRegion_sp88_17_some s0.sp]
        wp_done

set_option maxHeartbeats 800000 in
private theorem wp_hyphenated_ro_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p p19 : BitVec 64) (bs s36 : List (BitVec 8)) (Frame : SepProp) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true)
    (hs36 : s36.length = 36) (hframe : (p ↦ᵣ bs) = ((p19 ↦ᵣ s36) ∗ Frame))
    (huuid : uuidTryParse bs = parseHyphenated s36)
    (hpc : s.pc = (blkPl_255).base + bv% (44)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = p19)
    (hx8 : s.readReg64 .x8 = out17) (hx29 : s.readReg64 .x29 = s0.sp - 32#64)
    (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep ((p19 ↦ᵣ s36) ∗ Frame) out17 out_w0 out_w1 out_b2 s0)
      (parserPostROVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have hcallee_hex := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_255).rebase (blkPl_255).base hooks) (decodeHex32_placed_vm_ok hooks)
  change subroutine_ok _ (lsmpl.base 254) _ at hcallee_hex
  simp only [withLsCl, withVmPreserved, Spec.keepsFs, decodeHex32Spec, sepConj_assoc] at hcallee_hex
  rcases exists_36_parts_ro s36 hs36 with
    ⟨hex32, b8, b13, b18, b23, w0, w4, w1, w2, w3, w5,
     hhex_len, hb8, hb13, hb18, hb23, hhex_eq, hp19_split, hsp_hex32⟩
  have hph := parseHyphenated_of_parts s36 hex32 b8 b13 b18 b23 hs36 hb8 hb13 hb18 hb23 hhex_eq
  dsimp only [parserFrameSep]
  rw [hp19_split p19, memRegion_sp88_32_for_hyphen s0.sp]
  wp_pull_exists
  wp_steps
  wp_if h8
  · apply sepWP_vm_step (mid := s0.readReg64 .x30)
    by_vm_steps
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
      have hvm_tot := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
      unfold parserPostROVm withVmPreserved Spec.keepsFs parserTryParseROSpec
      simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_8 hph h8, parserTryParseResultAt,
        stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
      wp_done
  · wp_steps; wp_if h13
    · apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
        have hvm_tot := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
        unfold parserPostROVm withVmPreserved Spec.keepsFs parserTryParseROSpec
        simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_13 hph h13, parserTryParseResultAt,
          stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
        wp_done
    · wp_steps; wp_if h18
      · apply sepWP_vm_step (mid := s0.readReg64 .x30)
        by_vm_steps
          wp_steps
          refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
          have hvm_tot := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
          unfold parserPostROVm withVmPreserved Spec.keepsFs parserTryParseROSpec
          simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_18 hph h18, parserTryParseResultAt,
            stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
          wp_done
      · wp_steps; wp_if h23
        · apply sepWP_vm_step (mid := s0.readReg64 .x30)
          by_vm_steps
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm1 => ?_⟩
            have hvm_tot := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
            unfold parserPostROVm withVmPreserved Spec.keepsFs parserTryParseROSpec
            simp only [hframe, hp19_split p19, huuid, parseHyphenated_ne_23 hph h23, parserTryParseResultAt,
              stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp]
            wp_done
        · have hall := parseHyphenated_all_eq hph h8 h13 h18 h23
          apply sepWP_lscl_vm_step (by convert hcl0 using 1; wp_norm_lhs) (mid := lsmpl.base 254)
          by_vm_steps
            wp_steps
            refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun _hcl_call hvm1 => ?_⟩
            have hvm01 := vm_chain (vm_chain hvm0 (by simp only [arm64_norm])) hvm1
            apply SepWP.focus_rw (hsp_hex32 s0.sp)
            wp_apply
            have hvm_hex := vm_chain hvm01 ‹_›
            cases hdec : decodeHex32 hex32 with
            | none =>
              rw [decodeHex32ResultAt_sp52_none s0.sp, ← hsp_hex32 s0.sp, hsp]
              apply sepWP_vm_step (mid := s0.readReg64 .x30)
              by_vm_steps
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
                have hvm_tot := vm_chain hvm_hex hvm2
                unfold parserPostROVm withVmPreserved Spec.keepsFs parserTryParseROSpec
                simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt,
                  stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp, memRegion_sp52_17_none s0.sp]
                wp_done
            | some u =>
              rw [decodeHex32ResultAt_sp52_some s0.sp u, ← hsp_hex32 s0.sp, hsp]
              apply sepWP_vm_step (mid := s0.readReg64 .x30)
              by_vm_steps
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
                have hvm_tot := vm_chain hvm_hex hvm2
                unfold parserPostROVm withVmPreserved Spec.keepsFs parserTryParseROSpec
                simp only [hframe, hp19_split p19, huuid, hall, hdec, parserTryParseResultAt_some_eq,
                  stackAt_parser_split s0.sp, memRegion_sp88_32_for_hyphen s0.sp, memRegion_sp52_17_some s0.sp]
                wp_done

set_option maxHeartbeats 800000 in
private theorem wp_braced_ro_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 38) (hpc : s.pc = (blkPl_255).base + bv% (388))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p) (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64) (htr : s.trace = s0.trace)
    (hfs : s.fs = s0.fs) (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep (p ↦ᵣ bs) out17 out_w0 out_w1 out_b2 s0)
      (parserPostROVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have h_hyph := wp_hyphenated_ro_vm_placed hooks
  have h_err := wp_err_ro_vm_placed hooks
  rcases exists_38_parts_ro bs hlen with ⟨b0, b37, s36, hs36, _, huuid, hp_split⟩
  dsimp only [parserFrameSep]
  rw [hp_split p]; wp_steps; wp_if hb0
  · rw [← hp_split p]
    refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (braced_ne_0 huuid hb0)
      ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm]))
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
  · wp_steps; wp_if hb37
    · rw [← hp_split p]
      refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align (braced_ne_37 huuid hb37)
        ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm]))
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · wp_step; wp_step
      refine h_hyph p (p + 1#64) bs s36 ((p ↦₈ᵣ b0) ∗ ((p + 37#64) ↦₈ᵣ b37))
        out17 R out_w0 out_w1 out_b2 s0 _ (by convert hcl0 using 1; wp_norm_lhs)
        hsp_align hs36 (hp_split p) (braced_all_eq huuid hb0 hb37)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm]))
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs

set_option maxHeartbeats 800000 in
private theorem wp_urn_ro_vm_placed [LibsignalPlacement] (hooks : LibsignalHooks)
    (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (R : SepProp)
    (out_w0 out_w1 : BitVec 64) (out_b2 : BitVec 8) (s0 s : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s.mem) (hsp_align : s0.spAligned = true)
    (hlen : bs.length = 45) (hpc : s.pc = (blkPl_255).base + bv% (212))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = p) (hx8 : s.readReg64 .x8 = out17)
    (hx29 : s.readReg64 .x29 = s0.sp - 32#64) (htr : s.trace = s0.trace)
    (hfs : s.fs = s0.fs) (hvm0 : VmPreserved s0 s) (hcs : ParserRegsPreserved s0 s) :
    SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s
      (parserFrameSep (p ↦ᵣ bs) out17 out_w0 out_w1 out_b2 s0)
      (parserPostROVm p bs out17 s0 R) := by
  rcases hcs with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  have h_hyph := wp_hyphenated_ro_vm_placed hooks
  have h_err := wp_err_ro_vm_placed hooks
  rcases exists_45_parts_ro bs hlen with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, s36, hs36, huuid, hp_split⟩
  dsimp only [parserFrameSep]
  rw [hp_split p]; wp_steps; wp_if hb0
  · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x75#8 ≠ b0 from fun h => hb0 (h ▸ rfl)]
    rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
      ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
  · wp_steps; wp_if hb1
    · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x72#8 ≠ b1 from fun h => hb1 (h ▸ rfl)]
      rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
        ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
    · wp_steps; wp_if hb2
      · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x6e#8 ≠ b2 from fun h => hb2 (h ▸ rfl)]
        rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
          ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
      · wp_steps; wp_if hb3
        · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x3a#8 ≠ b3 from fun h => hb3 (h ▸ rfl)]
          rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
            ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
        · wp_steps; wp_if hb4
          · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x75#8 ≠ b4 from fun h => hb4 (h ▸ rfl)]
            rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
              ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
          · wp_steps; wp_if hb5
            · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x75#8 ≠ b5 from fun h => hb5 (h ▸ rfl)]
              rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
                ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
            · wp_steps; wp_if hb6
              · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x69#8 ≠ b6 from fun h => hb6 (h ▸ rfl)]
                rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
                  ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
              · wp_steps; wp_if hb7
                · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x64#8 ≠ b7 from fun h => hb7 (h ▸ rfl)]
                  rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
                    ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
                · wp_steps; wp_if hb8
                  · have hnone : uuidTryParse bs = none := by simp [huuid, show 0x3a#8 ≠ b8 from fun h => hb8 (h ▸ rfl)]
                    rw [← hp_split p]; refine h_err p bs out17 R out_w0 out_w1 out_b2 s0 _ hsp_align hnone
                      ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm])) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs
                  · wp_step; wp_step
                    refine h_hyph p (p + 9#64) bs s36
                      ((p ↦₈ᵣ b0) ∗ ((p + 1#64) ↦₈ᵣ b1) ∗ ((p + 2#64) ↦₈ᵣ b2) ∗
                       ((p + 3#64) ↦₈ᵣ b3) ∗ ((p + 4#64) ↦₈ᵣ b4) ∗ ((p + 5#64) ↦₈ᵣ b5) ∗
                       ((p + 6#64) ↦₈ᵣ b6) ∗ ((p + 7#64) ↦₈ᵣ b7) ∗ ((p + 8#64) ↦₈ᵣ b8))
                      out17 R out_w0 out_w1 out_b2 s0 _ (by convert hcl0 using 1; wp_norm_lhs)
                      hsp_align hs36 (hp_split p)
                      (urn_all_eq huuid hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (vm_chain hvm0 (by simp only [arm64_norm]))
                      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wp_norm_lhs

set_option maxHeartbeats 800000 in
private theorem parserTryParse_ro_placed_vm_ok [LibsignalPlacement] (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_255).rebase (blkPl_255).base hooks) (blkPl_255).base
      (withLsCodeLoaded lsmpl (withVmPreserved parserTryParseROSpec.keepsFs)) := by
  apply subroutine_ok_of_sepWP_simple
  intro ⟨p, bs, out17⟩ R s0 hpc hrun hsp
  change SepWP ((blkPC_255).rebase (blkPl_255).base hooks) (s0.readReg64 .x30) s0
    (((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out17⌝ ∗
      (p ↦ᵣ bs) ∗ memRegion out17 17) ∗ stackAt s0.sp 0x80) ∗
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) (parserPostROVm p bs out17 s0 R)
  rw [sepConj_comm]; apply SepWP.pure_elim; intro hcl0
  have h_braced := wp_braced_ro_vm_placed hooks
  have h_urn := wp_urn_ro_vm_placed hooks
  have h_simple := wp_simple_ro_vm_placed hooks
  have h_hyph := wp_hyphenated_ro_vm_placed hooks
  have h_err := wp_err_ro_vm_placed hooks
  simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩
  rw [memRegion_out17_split out17, stackAt_parser_split s0.sp]; wp_pull_exists
  apply sepWP_lscl_vm_step hcl0 (mid := (blkPl_255).base + bv% (16))
  by_vm_steps
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hcl1 hvm1 => ?_⟩
    wp_steps; wp_if hgt
    · have hne32 : bs.length ≠ 32 := fun hlen => by
        rw [show s0.readReg64 .x1 = 32#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      have hne36 : bs.length ≠ 36 := fun hlen => by
        rw [show s0.readReg64 .x1 = 36#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      wp_steps; wp_if heq38
      · apply sepWP_parser_branch
        refine h_braced p bs out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs)
          hsp (len_eq_of_reg_eq hx1 heq38) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
      · have hne38 := len_ne_of_reg_ne hx1 heq38
        wp_steps; wp_if hne45_reg
        · have huuid := uuidTryParse_of_other_len hne32 hne36 hne38 (len_ne_of_reg_ne hx1 hne45_reg)
          apply sepWP_parser_branch
          refine h_err p bs out17 R _ _ _ s0 _ hsp huuid ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
        · apply sepWP_parser_branch
          refine h_urn p bs out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs)
            hsp (len_eq_of_reg_eq hx1 hne45_reg) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
    · have hne38 : bs.length ≠ 38 := fun hlen => by
        rw [show s0.readReg64 .x1 = 38#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      have hne45 : bs.length ≠ 45 := fun hlen => by
        rw [show s0.readReg64 .x1 = 45#64 by rw [eq_ofNat_of_toNat_eq hx1, hlen]] at hgt; revert hgt; decide
      wp_steps; wp_if heq32
      · apply sepWP_parser_branch
        refine h_simple p bs out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs)
          hsp (len_eq_of_reg_eq hx1 heq32) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
      · have hne32 := len_ne_of_reg_ne hx1 heq32
        wp_steps; wp_if hne36_reg
        · have huuid := uuidTryParse_of_other_len hne32 (len_ne_of_reg_ne hx1 hne36_reg) hne38 hne45
          apply sepWP_parser_branch
          refine h_err p bs out17 R _ _ _ s0 _ hsp huuid ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs
        · have hlen36 := len_eq_of_reg_eq hx1 hne36_reg
          have huuid : uuidTryParse bs = parseHyphenated bs := by unfold uuidTryParse; simp [hlen36]
          apply sepWP_parser_hyph36
          refine h_hyph p p bs bs emp out17 R _ _ _ s0 _ (by convert hcl1 using 1; wp_norm_lhs)
            hsp hlen36 (sepConj_emp (p ↦ᵣ bs)).symm huuid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first | exact vm_chain hvm1 (by vm_core_step) | wp_norm_lhs

private theorem uuidTryParse_ro_placed_vm_ok [LibsignalPlacement] (hooks : LibsignalHooks) :
    subroutine_ok ((blkPC_252).rebase (blkPl_252).base hooks) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeROSpec uuidTryParse).keepsFs)) := by
  have hcallee := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_252).rebase (blkPl_252).base hooks) (parserTryParse_ro_placed_vm_ok hooks)
  change subroutine_ok _ (lsmpl.base 255) _ at hcallee
  simp only [withLsCl, withVmPreserved, Spec.keepsFs, parserTryParseROSpec, sepConj_assoc] at hcallee
  apply subroutine_ok_of_sepWP_simple
  intro ⟨p, bs, out⟩ R s0 hpc hrun hsp
  dsimp only [withLsCodeLoaded, withVmPreserved, Spec.keepsFs, uuidTryParseCodeROSpec,
    uuidTryParseROSpec, BitVec.ofNat_eq_ofNat] at *
  rw [sepConj_comm]; apply SepWP.pure_elim; intro hcl0
  simp only [sepConj_assoc]; apply SepWP.pure_elim; rintro ⟨hx0, hx1, hx8⟩
  rw [memRegion_out32_split out, stackAt_uuid_split s0.sp]; wp_pull_exists
  apply sepWP_lscl_vm_step hcl0 (mid := lsmpl.base 255)
  by_vm_steps
    wp_steps
    refine SepWP.done (by rfl) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun _hcl_call hvm1 => ?_⟩
    wp_apply
    have hvm_p := vm_chain hvm1 ‹_›
    cases huuid : uuidTryParse bs with
    | none =>
      rw [parserTryParseResultAt_sp56_none s0.sp]; wp_pull_exists; wp_focus_pure; intro _htag
      apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm_p hvm2
        simp only [uuidResultAt, uuidErrParseOther, memRegion_out28_split out, memRegion_sp56_17_split s0.sp]
        wp_done
    | some u =>
      rw [parserTryParseResultAt_sp56_some s0.sp u]
      apply sepWP_vm_step (mid := s0.readReg64 .x30)
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [arm64_norm], fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm_p hvm2
        simp only [uuidResultAt_some_eq out u, memRegion_sp56_17_split s0.sp]
        wp_done

private theorem uuidTryParseWithStack_ro_vm_keepsFs_of_withLsCodeLoaded {pl : Obj.MultiPlacement}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h : subroutine_ok P addr
      (withLsCodeLoaded pl (withVmPreserved (uuidTryParseCodeROSpec uuidTryParse).keepsFs)))
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr
      (withLsCodeLoaded pl (withVmPreserved (uuidTryParseStackROSpec hookStack).keepsFs)) := by
  apply subroutine_ok_outcome_intro
  intro ⟨p, bs, out⟩ R s0 hpc hrun hpre hal
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗
        stackAt s0.sp uuidTryParseStack := by
    have h1 := stackAt_split_bottom s0.sp uuidTryParseStack (hookStack - uuidTryParseStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded pl (withVmPreserved (uuidTryParseCodeROSpec uuidTryParse).keepsFs)).pre
        (p, bs, out) s0 ∗ R' := by
    dsimp only [withLsCodeLoaded, withVmPreserved, Spec.keepsFs, uuidTryParseStackROSpec,
      uuidTryParseCodeROSpec, uuidTryParseROSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine (h.to_outcome (p, bs, out) R' s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan_sat⟩ | ⟨code, _, hex_sat⟩ | ⟨_, hoom_sat⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, withVmPreserved, Spec.keepsFs, uuidTryParseStackROSpec,
      uuidTryParseCodeROSpec, uuidTryParseROSpec, R'] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact False.elim (not_satisfies_false_sepConj hpan_sat)
  · exact False.elim (not_satisfies_false_sepConj hex_sat)
  · exact False.elim (not_satisfies_false_sepConj hoom_sat)

set_option maxHeartbeats 800000 in
private theorem parseSid_ro_placed_vm_ok_of_contract_stack [LibsignalPlacement]
    (H : LibsignalHooks) (hookStack : Nat := 0)
    (huuid_entry : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseStackROSpec hookStack).keepsFs))) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (blkPl_206).base
      (withLsCodeLoaded lsmpl (withVmPreserved (parseSidCodeStackROSpec hookStack).keepsFs)) := by
  have huuid := ls_subroutine_ok_of_block (callerProg := (blkPC_206).rebase (blkPl_206).base H) huuid_entry
  change subroutine_ok _ (lsmpl.base 252) _ at huuid
  unfold withLsCodeLoaded withVmPreserved Spec.keepsFs at huuid ⊢
  simp only [parseSidCodeStackROSpec, parseSidROSpec, uuidTryParseStackROSpec, uuidTryParseROSpec] at huuid ⊢
  clear huuid_entry; wp_init x s0; obtain ⟨p, bs, out⟩ := x; dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_eq : (s0.readReg64 (Reg.gpr 1#5)).toNat = bs.length := by assumption
  rw [memRegion_17_none_split out, stackAt_parseSidFrame_split s0.sp]; wp_pull_exists
  apply sepWP_lscl_vm_step hcl0 (mid := (blkPl_206).base + bv% (16))
  by_vm_steps
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hcl1 hvm1 => ?_⟩
    wp_steps; wp_if hlt4
    · rw [serviceIdParse_of_lt_4 bs (toNat_lt_of_ult hlen_eq hlt4), parseSidResultAt]
      apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
      by_vm_steps
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm2 => ?_⟩
        have hvm_tot := vm_chain hvm1 (vm_chain (by vm_core_step) hvm2)
        wp_done
    · obtain ⟨b0, b1, b2, b3, bs', rfl⟩ := exists_cons4_of_le (le_of_not_ult hlen_eq hlt4)
      rw [pointsToBytesRO_cons4 p b0 b1 b2 b3 bs']; wp_steps; wp_if hpni
      · rw [serviceIdParse_cons4_pni b0 b1 b2 b3 bs' hpni]; wp_steps; wp_if hlen40
        · simp only [length_ne_36_of_ne_40 hlen_eq hlen40, ↓reduceIte, parseSidResultAt]
          apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
          by_vm_steps
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm2 => ?_⟩
            have hvm_tot := vm_chain hvm1 (vm_chain (by vm_core_step) hvm2)
            wp_done
        · have heq36 := length_eq_36_of_eq_40 hlen_eq hlen40; simp only [heq36, ↓reduceIte]
          apply sepWP_lscl_vm_step (by simpa using hcl1) (mid := lsmpl.base 252)
          by_vm_steps
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hcl2 hvm2 => ?_⟩
            have hvm12 := vm_chain (vm_chain hvm1 (by vm_core_step)) hvm2
            wp_call huuid (p + 4#64, bs', s0.sp - 64#64)
            have hvm_u := vm_chain hvm12 ‹_›
            cases hparse : uuidTryParse bs' with
            | none =>
              rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
              dsimp only [Option.map, parseSidResultAt]
              apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
              by_vm_steps
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm3 => ?_⟩
                have hvm_tot := vm_chain hvm_u hvm3
                wp_done
            | some u =>
              rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp, memRegion_out1_16_split out]
              dsimp only [Option.map]; rw [parseSidResultAt_some_eq out true u]; wp_pull_exists
              apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
              by_vm_steps
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm3 => ?_⟩
                have hvm_tot := vm_chain hvm_u hvm3
                wp_done
      · rw [serviceIdParse_cons4_aci b0 b1 b2 b3 bs' hpni, ← pointsToBytesRO_cons4 p b0 b1 b2 b3 bs']
        wp_steps; wp_if hlen36
        · simp only [length_ne_36_of_ne_36 hlen_eq hlen36, ↓reduceIte, parseSidResultAt]
          apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
          by_vm_steps
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm2 => ?_⟩
            have hvm_tot := vm_chain hvm1 (vm_chain (by vm_core_step) hvm2)
            wp_done
        · have heq36 := length_eq_36_of_eq_36 hlen_eq hlen36; simp only [heq36, ↓reduceIte]
          apply sepWP_lscl_vm_step (by simpa using hcl1) (mid := lsmpl.base 252)
          by_vm_steps
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hcl2 hvm2 => ?_⟩
            have hvm12 := vm_chain (vm_chain hvm1 (by vm_core_step)) hvm2
            wp_call huuid (p, b0 :: b1 :: b2 :: b3 :: bs', s0.sp - 64#64)
            have hvm_u := vm_chain hvm12 ‹_›
            cases hparse : uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') with
            | none =>
              rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
              dsimp only [Option.map, parseSidResultAt]
              apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
              by_vm_steps
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm3 => ?_⟩
                have hvm_tot := vm_chain hvm_u hvm3; wp_done
            | some u =>
              rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp, memRegion_out1_16_split out]
              dsimp only [Option.map]; rw [parseSidResultAt_some_eq out false u]; wp_pull_exists
              apply sepWP_vm_step (mid := s0.readReg64 (Reg.gpr 30#5))
              by_vm_steps
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp_all, fun hvm3 => ?_⟩
                have hvm_tot := vm_chain hvm_u hvm3; wp_done

private theorem hookStack_le_of_frame_disjoint_local {m : Memory} {sp : BitVec 64} {hookStack : Nat}
    {R : SepProp}
    (hm : m ⊨ stackAt (sp - 80#64) hookStack ∗ stackAt sp parseSidFrameStack ∗ R) :
    hookStack ≤ 2 ^ 64 := by
  by_cases h0 : hookStack = 0
  · omega
  · have hm' :
        m ⊨ memRegion (sp - 80#64) 80 ∗
          (memRegion ((sp - 80#64) - BitVec.ofNat 64 hookStack) hookStack ∗ R) := by
      dsimp only [stackAt, parseSidFrameStack] at hm
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    have hd := disjointRegions_of_coversRegion (by decide) (Nat.pos_of_ne_zero h0)
      (IsBlock.memRegion (sp - 80#64) 80).covers
      (IsBlock.memRegion ((sp - 80#64) - BitVec.ofNat 64 hookStack) hookStack).covers
      hm'
    have hlt1 := (((sp - 80#64) - BitVec.ofNat 64 hookStack) - (sp - 80#64)).isLt
    have hlt2 := ((sp - 80#64) - ((sp - 80#64) - BitVec.ofNat 64 hookStack)).isLt
    have h1 := hd.1
    have h2 := hd.2
    omega

private theorem parseSid_ro_blk206_vm_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (withVmPreserved (parseSidCodeStackROSpec hookStack).keepsFs)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hmax : hookStack ≤ 2 ^ 64 := by
    have hm :
        s0.mem ⊨ stackAt (s0.sp - 80#64) hookStack ∗ stackAt s0.sp parseSidFrameStack ∗
          (⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
            (parseSidROSpec (serviceIdParse uuidTryParse)).pre x s0 ∗ R) := by
      dsimp only [withLsCodeLoaded, withVmPreserved, Spec.keepsFs, parseSidCodeStackROSpec] at hpre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
    exact hookStack_le_of_frame_disjoint_local hm
  exact (parseSid_ro_placed_vm_ok_of_contract_stack H hookStack
    (uuidTryParseWithStack_ro_vm_keepsFs_of_withLsCodeLoaded
      (uuidTryParse_ro_placed_vm_ok H) hstack hmax)).to_outcome
    x R s0 hpc hrun hpre hal

private theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_local
    {α : Type} {prog : Program} {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨⟨hcl, _⟩, hpre_spec⟩ := extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_comm (spec.pre x s0), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl, hpre_spec⟩
  exact (h.to_outcome x R s0 hpc hrun hpre' hsp).mono_outcome fun _ hout => hout

theorem parseSid_ro_placed_vm_ok_rocl [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsRoCl lsmpl (withVmPreserved (parseSidCodeStackROSpec hookStack).keepsFs)) := by
  have h0 : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (lsmpl.base 206)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (parseSidCodeStackROSpec hookStack).keepsFs)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_local
      (parseSid_ro_blk206_vm_ok H hookStack hstack)
  exact ls_subroutine_ok_rocl_of_block (callerProg := prog) h0 hi (by decide) (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.ParseSidRoPlacedBudget
