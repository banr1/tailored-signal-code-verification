/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionRecord::deserialize` Loop Entry (`+0x000` → `+0x254`)

Verifies the `SessionRecord::deserialize` prologue, `SessionStructure::default()` initialization,
and outer protobuf key and length-varint decode (`+0x000` → `+0x254`) on `SP2Ext` and under
relocatable `[LibsignalPlacement]`.
-/

namespace Proofs.libsignal.Hooks2.DeserLoopEntryGExt

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre_loopEntryG (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local simp, local arm64_norm]
private theorem int64_toBitVec_mk (u : UInt64) : ({ toUInt64 := u } : Int64).toBitVec = u.toBitVec := rfl

@[local simp, local arm64_norm]
private theorem uint64_toBitVec_mk (v : BitVec 64) : ({ toBitVec := v } : UInt64).toBitVec = v := rfl

@[local simp, local arm64_norm]
private theorem bitVec_toFin_mk_64 (n : Nat) (h : n < 18446744073709551616 := by decide) :
    ({ toFin := ⟨n, h⟩ } : BitVec 64) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  exact (Nat.mod_eq_of_lt h).symm

run_meta do
  let optInstr := Lean.mkApp (Lean.mkConst ``Option [0]) (Lean.mkConst ``Arm64.Instr)
  let tree := Lean.mkConst ``CryptoVerification.libsignalSessionCode_tree
  let fnOff := num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")
  let ranges : List (Nat × Nat) :=
    [(0, 144), (208, 176), (512, 8), (532, 64)]
  for (k0, len) in ranges do
    for i in [0 : len / 4] do
      let addr := fnOff + k0 + 4 * i
      let hex := String.ofList (Nat.toDigits 16 addr)
      let thmName := Lean.Name.str `Proofs.libsignal.Hooks2.DeserLoopEntryGExt s!"d0_decode_0x{hex}"
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

local elab "d0_fetch_range " codeId:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "d0_fetch_range"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let fetchEntry := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := Lean.mkIdent (Lean.Name.str `Proofs.libsignal.Hooks2.DeserLoopEntryGExt s!"d0_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Lean.Syntax.mkNumLit (toString k)
    if k == 0 then
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

local macro "d0_fetches_1a " b:term:max H:term:max : tactic =>
  `(tactic| (
    d0_fetch_range CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 0 144
    d0_fetch_range CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 208 52
  ))

local macro "d0_fetches_1b " b:term:max H:term:max : tactic =>
  `(tactic| d0_fetch_range CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 260 88)

local macro "d0_fetches_2a " b:term:max H:term:max : tactic =>
  `(tactic| (
    d0_fetch_range CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 348 36
    d0_fetch_range CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 576 20
  ))

local macro "d0_fetches_2b_pre " b:term:max H:term:max : tactic =>
  `(tactic| (
    d0_fetch_range CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 348 24
    d0_fetch_range CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 512 8
    d0_fetch_range CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 532 8
  ))

local macro "d0_fetches_2b_post " b:term:max H:term:max : tactic =>
  `(tactic| d0_fetch_range CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 540 56)

theorem recDeser_fnAddr_sp2ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr recDeserializeName = b + bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") := by
  dsimp only [SP2Ext, contractProg]
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize")]

theorem decodeVarintSlice_fnAddr_sp2ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr Prost.decodeVarintSliceName = b + bv% (ls_off% "prost::encoding::varint::decode_varint_slice") := by
  dsimp only [SP2Ext, contractProg]
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]

theorem decodeVarintSlice_fnAddr_eq_deser_at_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr recDeserializeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") =
      (SP2Ext b ext).fnAddr Prost.decodeVarintSliceName := by
  rw [recDeser_fnAddr_sp2ext, decodeVarintSlice_fnAddr_sp2ext]
  bv_omega

/-! ## Pure codec and varint helpers -/

private theorem encodeKey_1_ld_loopEntryG : encodeKey 1 .lengthDelimited = [0x0a#8] := rfl

private theorem encodeVarint_length_pos_loopEntryG (v : BitVec 64) :
    0 < (encodeVarint v).length :=
  List.length_pos_iff.mpr (encodeVarint_ne_nil v)

private theorem encodeVarint_of_lt_128_loopEntryG {n : Nat} (hn : n < 128) :
    encodeVarint (BitVec.ofNat 64 n) = [BitVec.ofNat 8 n] := by
  have h1 : (BitVec.ofNat 64 n).toNat < 0x80 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  unfold encodeVarint encodeVarintAux
  simp only [h1, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

private theorem encodeVarint_cons_of_ge_128_loopEntryG {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 20) :
    encodeVarint (BitVec.ofNat 64 n) =
      BitVec.ofNat 8 (n % 128 + 128) :: encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : ¬ ((BitVec.ofNat 64 n).toNat < 0x80) := by omega
  unfold encodeVarint encodeVarintAux
  simp only [h1, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, hn,
    show (0x7F : BitVec 64).toNat = 127 from rfl,
    Nat.and_two_pow_sub_one_eq_mod n 7,
    show (0x80 : BitVec 64).toNat = 128 from rfl,
    Nat.or_comm, ← hor, BitVec.toNat_ofNat]
  omega

private theorem signExtend64_bit63_eq_false_iff_loopEntryG (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = false ↔ b0.toNat ≤ 0x7F := by
  revert b0; decide

private theorem signExtend64_bit63_eq_true_iff_loopEntryG (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = true ↔ 0x7F < b0.toNat := by
  revert b0; decide

private theorem signExtend64_eq_zeroExtend64_of_le_loopEntryG (b0 : BitVec 8) (h : b0.toNat ≤ 0x7F) :
    b0.signExtend 64 = b0.zeroExtend 64 := by
  revert b0 h; decide

private theorem signExtend64_ofNat8_lt_128_loopEntryG {n : Nat} (hn : n < 128) :
    (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hle : (BitVec.ofNat 8 n).toNat ≤ 0x7F := by rw [BitVec.toNat_ofNat]; omega
  rw [signExtend64_eq_zeroExtend64_of_le_loopEntryG _ hle]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-! ## `prostSSGAt` initialization and stack splitting -/

private theorem sp_sub_1904_aligned_loopEntryG {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0x770#64) &&& 15#64 = 0#64 ∧ (sp0 - 0x770#64 + 1808#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h; rw [e] at h'
  have hlt := sp0.isLt
  have hsub : sp0 - 0x770#64 + 1808#64 = sp0 - 96#64 := by bv_omega
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega
  · rw [hsub]; apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega

private theorem empty_vecU8_intro_loopEntryG (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A v [] := by
  dsimp only [vecU8, vecU8At, vecHeader]; simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [↓reduceIte, sepConj_emp, sepConj_assoc]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := by decide
  rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) by ac_rfl]
  exact Entails.pure_right hp (Entails.refl _)

private theorem empty_vecChainG_intro_loopEntryG (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecOf A 104 8 (fun c a => prostChainGAt A a c) v [] := by
  dsimp only [vecOf, vecAt, vecHeader, vecBuf]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 8#64)
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
      arrayAt (fun c a => prostChainGAt A a c) 104 8#64 [] ∗
      memRegion (8#64 + BitVec.ofNat 64 (([] : List ChainG).length * 104))
        (((0#64 : BitVec 64).toNat - ([] : List ChainG).length) * 104)) = emp := rfl
  rw [hite]; simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_emp]
  exact Entails.pure_right (by decide) (Entails.refl _)

private theorem pointsTo64_zero_split32_loopEntryG (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  simpa using pointsTo64_split32 a 0#64

private def ssRawCells_loopEntryG (L : BitVec 64) : SepProp :=
  (((L + 0x420#64) ↦₆₄ 0#64) ∗ ((L + 0x428#64) ↦₆₄ 1#64) ∗ ((L + 0x430#64) ↦₆₄ 0#64)) ∗
  (((L + 0x438#64) ↦₆₄ 0#64) ∗ ((L + 0x440#64) ↦₆₄ 1#64) ∗ ((L + 0x448#64) ↦₆₄ 0#64)) ∗
  (((L + 0x450#64) ↦₆₄ 0#64) ∗ ((L + 0x458#64) ↦₆₄ 1#64) ∗ ((L + 0x460#64) ↦₆₄ 0#64)) ∗
  (((L + 0x468#64) ↦₆₄ 0#64) ∗ ((L + 0x470#64) ↦₆₄ 8#64) ∗ ((L + 0x478#64) ↦₆₄ 0#64)) ∗
  (((L + 0x480#64) ↦₆₄ 0#64) ∗ ((L + 0x488#64) ↦₆₄ 1#64) ∗ ((L + 0x490#64) ↦₆₄ 0#64)) ∗
  (((L + 0x498#64) ↦₆₄ 0#64) ∗ ((L + 0x4a0#64) ↦₆₄ 1#64) ∗ ((L + 0x4a8#64) ↦₆₄ 0#64)) ∗
  ((L + 0x4b0#64) ↦₆₄ noneCap) ∗ ((L + 0x518#64) ↦₆₄ noneCap) ∗
  ((L + 0x548#64) ↦₆₄ noneCap) ∗ ((L + 0x568#64) ↦₆₄ 0#64) ∗ ((L + 0x570#64) ↦₆₄ 0#64)

private theorem prostSSGAt_empty_intro_loopEntryG (A : RustAlloc) (L : BitVec 64) :
    ssRawCells_loopEntryG L ∗ memRegion (L + 0x4b8#64) 96 ∗
      memRegion (L + 0x520#64) 40 ∗ memRegion (L + 0x550#64) 24 ⊢
      prostSSGAt A (L + 0x420#64) SSG.empty := by
  unfold ssRawCells_loopEntryG prostSSGAt SSG.empty; dsimp only
  have h1 := empty_vecU8_intro_loopEntryG A (L + 0x420#64)
  have h2 := empty_vecU8_intro_loopEntryG A (L + 0x420#64 + 0x18#64)
  have h3 := empty_vecU8_intro_loopEntryG A (L + 0x420#64 + 0x30#64)
  have h4 := empty_vecChainG_intro_loopEntryG A (L + 0x420#64 + 0x48#64)
  have h5 := empty_vecU8_intro_loopEntryG A (L + 0x420#64 + 0x60#64)
  have h6 := empty_vecU8_intro_loopEntryG A (L + 0x420#64 + 0x78#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢
  rw [pointsTo64_zero_split32_loopEntryG (L + 0x568#64)]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1904_sub_96_loopEntryG (L : BitVec 64) :
    L + 1904#64 + bv% (2 ^ 64 - 96) = L + 1808#64 := by rw [BitVec.add_assoc]; rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_1808_loopEntryG (L : BitVec 64) :
    L + 1808#64 - 1808#64 = L := by bv_omega

@[local arm64_norm ↓, local wp_norm ↓]
private theorem add_1808_sub_40_loopEntryG (L : BitVec 64) :
    L + 1808#64 + bv% (2 ^ 64 - 40) = L + 1768#64 := by rw [BitVec.add_assoc]; rfl

private def deserSavedAt_loopEntryG (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 1808#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 1816#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((L + 1824#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 1832#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((L + 1840#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 1848#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((L + 1856#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 1864#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((L + 1872#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 1880#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((L + 1888#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 1896#64) ↦₆₄ s0.readReg64 .x19)

private theorem deserSavedAt_eq_loopEntryG (s0 : State) :
    deserSavedAt_loopEntryG (deserSpL s0.sp) s0 = deserSaved s0 := by
  unfold deserSavedAt_loopEntryG deserSaved deserSpL; dsimp only
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

/-! ## `SessionStructure::default()` stores (`+0x104` → `+0x15c`) -/

private def ssUninitCells_loopEntryG (L : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64) :
    SepProp :=
  ((L + 1056#64) ↦₆₄ noneCap) ∗
  ((L + 1064#64) ↦₆₄ c1) ∗ ((L + 1072#64) ↦₆₄ c2) ∗ ((L + 1080#64) ↦₆₄ c3) ∗
  ((L + 1088#64) ↦₆₄ c4) ∗ ((L + 1096#64) ↦₆₄ c5) ∗ ((L + 1104#64) ↦₆₄ c6) ∗
  ((L + 1112#64) ↦₆₄ c7) ∗ ((L + 1120#64) ↦₆₄ c8) ∗ ((L + 1128#64) ↦₆₄ c9) ∗
  ((L + 1136#64) ↦₆₄ c10) ∗ ((L + 1144#64) ↦₆₄ c11) ∗ ((L + 1152#64) ↦₆₄ c12) ∗
  ((L + 1160#64) ↦₆₄ c13) ∗ ((L + 1168#64) ↦₆₄ c14) ∗ ((L + 1176#64) ↦₆₄ c15) ∗
  ((L + 1184#64) ↦₆₄ c16) ∗ ((L + 1192#64) ↦₆₄ c17) ∗ ((L + 1200#64) ↦₆₄ c18) ∗
  ((L + 1304#64) ↦₆₄ c19) ∗ ((L + 1352#64) ↦₆₄ c20) ∗
  ((L + 1384#64) ↦₆₄ c21) ∗ ((L + 1392#64) ↦₆₄ c22)

private theorem step_1b_loopEntryG (img : Obj.Image) (ext : String → Option (State → State))
    (L : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 260#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halign : L &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = 2#64) (hx21 : s.readReg64 .x21 = noneCap)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx26 : s.readReg64 .x26 = 8#64)
    (hnext : ∀ s' : State, s'.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 348#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .x19 = s.readReg64 .x19 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = s.readReg64 .x29 →
      post s' (ssRawCells_loopEntryG L)) :
    SepWP (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + 348#64) s
      (ssUninitCells_loopEntryG L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22)
      post := by
  let H := Rust.withPanics ext
  d0_fetches_1b img.base H
  dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches; unfold ssUninitCells_loopEntryG
  have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  rw [hnone] at hx21 ⊢
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold ssRawCells_loopEntryG; rw [hnone]; ac_rfl

/-! ## Prologue and outer key `0x0a` fast path (`+0x000` → `+0x104`) -/

private def step1aPre_loopEntryG (L p : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) : SepProp :=
  ((L + 1808#64) ↦₆₄ w0) ∗ ((L + 1816#64) ↦₆₄ w1) ∗
  ((L + 1824#64) ↦₆₄ w2) ∗ ((L + 1832#64) ↦₆₄ w3) ∗
  ((L + 1840#64) ↦₆₄ w4) ∗ ((L + 1848#64) ↦₆₄ w5) ∗
  ((L + 1856#64) ↦₆₄ w6) ∗ ((L + 1864#64) ↦₆₄ w7) ∗
  ((L + 1872#64) ↦₆₄ w8) ∗ ((L + 1880#64) ↦₆₄ w9) ∗
  ((L + 1888#64) ↦₆₄ w10) ∗ ((L + 1896#64) ↦₆₄ w11) ∗
  (L ↦₆₄ u0) ∗ ((L + 1016#64) ↦₆₄ u1) ∗ ((L + 1024#64) ↦₆₄ u2) ∗
  ((L + 1032#64) ↦₆₄ u3) ∗ ((L + 1040#64) ↦₆₄ u4) ∗
  ((L + 1048#64) ↦₆₄ u5) ∗ ((L + 1056#64) ↦₆₄ u6) ∗
  ((L + 1768#64) ↦₆₄ u7) ∗ (p ↦₈ 10#8)

private def step1aPost_loopEntryG (L p : BitVec 64) (len1 : Nat) (s0 : State) : SepProp :=
  deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗
  ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
  ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗
  ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1056#64) ↦₆₄ noneCap) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 10#8)

private theorem step_1a_loopEntryG (img : Obj.Image) (ext : String → Option (State → State))
    (L p out : BitVec 64) (len1 : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName) (hrun : s0.status = .Running)
    (hsp : s0.sp = L + 1904#64) (halignL : L &&& 15#64 = 0#64)
    (halign1808 : (L + 1808#64) &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + len1))
    (hx8 : s0.readReg64 .x8 = out) (hlen1_pos : 0 < len1) (hlen1_lt : len1 < 2 ^ 20)
    (hnext : ∀ s1 : State, s1.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 260#64 → s1.status = .Running →
      s1.sp = L → (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) → s1.readReg64 .x0 = 2#64 →
      s1.readReg64 .x19 = out → s1.readReg64 .x21 = noneCap →
      s1.readReg64 .x23 = L + 1032#64 → s1.readReg64 .x24 = 1#64 →
      s1.readReg64 .x26 = 8#64 → s1.readReg64 .x29 = L + 1808#64 →
      post s1 (step1aPost_loopEntryG L p len1 s0)) :
    SepWP (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + 260#64) s0
      (step1aPre_loopEntryG L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7)
      post := by
  let H := Rust.withPanics ext
  d0_fetches_1a img.base H
  dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches; unfold step1aPre_loopEntryG
  change len1 < 1048576 at hlen1_lt
  have hcbz : (BitVec.ofNat 64 (1 + len1) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + len1 = 0 at hnat; omega
  have hsub1 : BitVec.ofNat 64 (1 + len1) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 len1 := by
    rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + len1) - 1#64 = BitVec.ofNat 64 len1 := by
    rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by rw [hnone]; simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step1aPost_loopEntryG deserSavedAt_loopEntryG; rw [hnone]
  simp only [Reg.x29, Reg.x30, Reg.x28, Reg.x27, Reg.x26, Reg.x25, Reg.x24, Reg.x23,
    Reg.x22, Reg.x21, Reg.x20, Reg.x19]
  ac_rfl

/-! ## Single-byte length varint fast path (`+0x15c` → `+0x254`, `N < 128`) -/

private def step2aPre_loopEntryG (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (1 + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private def step2aPost_loopEntryG (L p : BitVec 64) (N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 2#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)

private theorem step_2a_loopEntryG (img : Obj.Image) (ext : String → Option (State → State))
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_lt : N < 128)
    (hnext : ∀ s' : State, s'.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2aPost_loopEntryG L p N)) :
    SepWP (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + 596#64) s (step2aPre_loopEntryG L p N) post := by
  let H := Rust.withPanics ext
  d0_fetches_2a img.base H
  dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches; unfold step2aPre_loopEntryG
  have hcbz : (BitVec.ofNat 64 (1 + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + N = 0 at hnat; omega
  have hse := signExtend64_ofNat8_lt_128_loopEntryG hN_lt
  have hbit63 : (((BitVec.ofNat 8 N).signExtend 64).getLsbD 63 == true) = false :=
    (signExtend64_bit63_eq_false_iff_loopEntryG (BitVec.ofNat 8 N)).mpr (by rw [BitVec.toNat_ofNat]; omega)
  have hsub1 : BitVec.ofNat 64 (1 + N) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + N) - 1#64 = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2aPost_loopEntryG; ac_rfl

/-! ## Multi-byte length varint via `decode_varint_slice` (`+0x15c` → `+0x254`, `128 ≤ N < 2 ^ 20`) -/

private def step2bPre_loopEntryG (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128))

private theorem step_2b_pre_loopEntryG (img : Obj.Image) (ext : String → Option (State → State))
    (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_ge : 128 ≤ N) (hVN_lt : vlen + N < 2 ^ 20)
    (hnext : ∀ s' : State, s'.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .lr = (SP2Ext img.base ext).fnAddr recDeserializeName + 540#64 →
      s'.readReg64 .x0 = L + 1400#64 → s'.readReg64 .x1 = p + 1#64 →
      s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) → s'.readReg64 .x19 = out →
      s'.readReg64 .x20 = L + 1016#64 → s'.readReg64 .x23 = L + 1032#64 →
      s'.readReg64 .x29 = L + 1808#64 → post s' (step2bPre_loopEntryG L p vlen N)) :
    SepWP (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) s (step2bPre_loopEntryG L p vlen N) post := by
  let H := Rust.withPanics ext
  d0_fetches_2b_pre img.base H
  dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches; unfold step2bPre_loopEntryG
  have hcbz : (BitVec.ofNat 64 (vlen + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change vlen + N = 0 at hnat; omega
  have hbit63 :
      (((BitVec.ofNat 8 (N % 128 + 128)).signExtend 64).getLsbD 63 == true) = true :=
    (signExtend64_bit63_eq_true_iff_loopEntryG (BitVec.ofNat 8 (N % 128 + 128))).mpr
      (by rw [BitVec.toNat_ofNat]; omega)
  have hhi10 : (10#64).ult (BitVec.ofNat 64 (vlen + N)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      decide_eq_true_eq]; omega
  have hule10 : (BitVec.ofNat 64 (vlen + N)).ule 10#64 = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step2bPre_loopEntryG; ac_rfl

private def step2bPostPre_loopEntryG (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N))

private def step2bPostPost_loopEntryG (L p : BitVec 64) (vlen N : Nat) : SepProp :=
  ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
  ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗
  ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
  ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N)

private theorem step_2b_post_loopEntryG (img : Obj.Image) (ext : String → Option (State → State))
    (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 540#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halignL : L &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = L + 1016#64)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx29 : s.readReg64 .x29 = L + 1808#64)
    (hVN_lt : vlen + N < 2 ^ 20)
    (hnext : ∀ s' : State, s'.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2bPostPost_loopEntryG L p vlen N)) :
    SepWP (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + 596#64) s (step2bPostPre_loopEntryG L p vlen N) post := by
  let H := Rust.withPanics ext
  d0_fetches_2b_post img.base H
  dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches; unfold step2bPostPre_loopEntryG
  have hsub2 : BitVec.ofNat 64 (vlen + N) - BitVec.ofNat 64 vlen = BitVec.ofNat 64 N := by
    rw [BitVec.ofNat_add]; bv_omega
  have hult2 : (BitVec.ofNat 64 (vlen + N)).ult (BitVec.ofNat 64 vlen) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show vlen < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2bPostPost_loopEntryG; ac_rfl

/-! ## Memory splitting and folding helpers -/

private theorem memRegion_succ8_loopEntryG (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) =
      (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

private theorem memRegion_1064_336_cells_loopEntryG (L : BitVec 64) :
    ((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336 =
      ∃∗ c22 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c19 : BitVec 64,
      ∃∗ c18 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c15 : BitVec 64,
      ∃∗ c14 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c12 : BitVec 64, ∃∗ c11 : BitVec 64,
      ∃∗ c10 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c6 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ c1 : BitVec 64,
        ssUninitCells_loopEntryG L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
        memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 := by
  rw [memRegion_split (L + 1064#64) 144 192 (by decide),
    memRegion_split (L + 1064#64 + 144#64) 96 96 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64) 8 88 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (L + 1304#64), ProofLib.memRegion_eight (L + 1352#64)]
  conv_lhs =>
    arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2
    simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold ssUninitCells_loopEntryG
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem memRegion_1904_split_loopEntryG (L p : BitVec 64) :
    memRegion L 1904 ∗ (p ↦₈ 0x0a#8) =
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
      ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        step1aPre_loopEntryG L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗
        memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 := by
  rw [memRegion_split L 8 1896 (by decide),
    memRegion_split (L + 8#64) 1008 888 (by decide),
    memRegion_split (L + 8#64 + 1008#64) 48 840 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64) 336 504 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64) 368 136 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64) 8 128 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64 + 8#64) 32 96 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1; arg 1; simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp]
  conv_lhs =>
    arg 1; arg 2; arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2
    simp (discharger := decide) only [memRegion_succ8_loopEntryG, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold step1aPre_loopEntryG
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem stackAt_recDeserialize_split_loopEntryG (sp0 : BitVec 64) :
    stackAt sp0 recDeserializeStack =
      stackAt (deserSpL sp0) deserCalleeStack ∗ memRegion (deserSpL sp0) 1904 := by
  change memRegion (sp0 - 65536#64) 65536 =
    memRegion (sp0 - 0x770#64 - 63632#64) 63632 ∗ memRegion (sp0 - 0x770#64) 1904
  rw [memRegion_split (sp0 - 65536#64) 63632 1904 (by decide)]
  have h1 : sp0 - 65536#64 = sp0 - 0x770#64 - 63632#64 := by bv_omega
  have h2 : sp0 - 65536#64 + 63632#64 = sp0 - 0x770#64 := by bv_omega
  rw [h2, h1]

private theorem memRegion_0_1016_intro_loopEntryG (L : BitVec 64) :
    (L ↦₆₄ 0#64) ∗ memRegion (L + 8#64) 1008 ⊢ memRegion L 0x3f8 := by
  rw [show (0x3f8 : Nat) = 1016 by decide, memRegion_split L 8 1008 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion L 0#64)

private def deserFixedLocalsG_loopEntryG (A : RustAlloc) (L : BitVec 64) : SepProp :=
  memRegion L 0x3f8 ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗
    ((L + 0x418#64) ↦₆₄ 0#64) ∗ prostSSGAt A (L + 0x420#64) SSG.empty ∗ memRegion (L + 0x6f0#64) 0x20

private theorem step1b_post_entails_loopEntryG (A : RustAlloc) (L p : BitVec 64) (len1 : Nat) (s0 : State)
    (hL : L = deserSpL s0.sp) :
    ssRawCells_loopEntryG L ∗ memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗
      memRegion (L + 1360#64) 24 ∗ deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗
      ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗
      memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ⊢
    ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
      ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG A L ∗ deserSaved s0 := by
  have hss := prostSSGAt_empty_intro_loopEntryG A L
  have hm0 := memRegion_0_1016_intro_loopEntryG L
  have hds : deserSavedAt_loopEntryG L s0 = deserSaved s0 := hL ▸ deserSavedAt_eq_loopEntryG s0
  unfold deserFixedLocalsG_loopEntryG; rw [hds,
    show (0x408#64 : BitVec 64) = 1032#64 from rfl, show (0x410#64 : BitVec 64) = 1040#64 from rfl,
    show (0x418#64 : BitVec 64) = 1048#64 from rfl, show (0x6f0#64 : BitVec 64) = 1776#64 from rfl,
    show (0x20 : Nat) = 32 from rfl]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (Entails.trans (sepConj_mono (sepConj_mono hss hm0)
      (Entails.refl (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗
        ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        memRegion (L + 1776#64) 32 ∗ deserSaved s0))) (Entails.of_eq (by ac_rfl)))

private theorem scratch24_368_fold_loopEntryG (L v w : BitVec 64) :
    ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗
      ((L + 1408#64) ↦₆₄ v) ∗ ((L + 1416#64) ↦₆₄ w) ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 := by
  have h0 : ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) = ((L + 1400#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32_loopEntryG (L + 1400#64)).symm
    rwa [show L + 1400#64 + 4#64 = L + 1404#64 by bv_omega] at hs
  rw [← sepConj_assoc, h0, memRegion_split (L + 1400#64) 24 344 (by decide),
    memRegion_split (L + 1400#64) 8 16 (by decide), memRegion_split (L + 1400#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion (L + 1400#64) 0#64)
      (sepConj_mono (pointsTo64_entails_memRegion (L + 1408#64) v)
        (pointsTo64_entails_memRegion (L + 1416#64) w))) (Entails.refl _))

private theorem deserLocalsG_of_2a_loopEntryG (A : RustAlloc) (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields r).flatMap GenField.enc).length) ++
      (recFields r).flatMap GenField.enc)
    (hN : ((recFields r).flatMap GenField.enc).length < 128) :
    let body := (recFields r).flatMap GenField.enc
    step2aPost_loopEntryG L p body.length ∗ ((p + 1#64 + 1#64) ↦ₛ body) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG A L =
    deserLocalsGA A L p (encodeRecord r) body SSG.empty := by
  intro body
  have hpfx : encodeRecord r = 0x0a#8 :: BitVec.ofNat 8 body.length :: body := by
    rw [heq, encodeKey_1_ld_loopEntryG, encodeVarint_of_lt_128_loopEntryG hN]; rfl
  have hsub : (encodeRecord r).length - body.length = 2 := by rw [hpfx, List.length_cons, List.length_cons]; omega
  have hbytes : (p ↦ₛ encodeRecord r) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 body.length) ∗ ((p + 1#64 + 1#64) ↦ₛ body) := by
    rw [hpfx, pointsToBytes_cons, pointsToBytes_cons]
  unfold deserLocalsGA Prost.sliceCursorAfter deserFixedLocalsG_loopEntryG step2aPost_loopEntryG
  rw [hsub, hbytes, show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega, show (BitVec.ofNat 64 2 : BitVec 64) = 2#64 from rfl,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl, show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]; ac_rfl

private theorem step2bPostPost_entails_loopEntryG (L p : BitVec 64) (vlen N : Nat) :
    step2bPostPost_loopEntryG L p vlen N ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) := by
  unfold step2bPostPost_loopEntryG
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_left (Q := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N))
      (scratch24_368_fold_loopEntryG L (BitVec.ofNat 64 N) (BitVec.ofNat 64 vlen)))

private theorem deserLocalsG_of_2b_loopEntryG (A : RustAlloc) (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields r).flatMap GenField.enc).length) ++
      (recFields r).flatMap GenField.enc) :
    let body := (recFields r).flatMap GenField.enc
    let vlen := (encodeVarint (BitVec.ofNat 64 body.length)).length
    (step2bPostPost_loopEntryG L p vlen body.length ∗ memRegion (L + 1424#64) 344) ∗
      ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) ∗
      (p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopEntryG A L ⊢
    deserLocalsGA A L p (encodeRecord r) body SSG.empty := by
  intro body vlen
  refine Entails.trans (sepConj_mono_left (step2bPostPost_entails_loopEntryG L p vlen body.length)) ?_
  have hpfx : encodeRecord r = 0x0a#8 :: (encodeVarint (BitVec.ofNat 64 body.length) ++ body) := by
    rw [heq, encodeKey_1_ld_loopEntryG]; rfl
  have hsub : (encodeRecord r).length - body.length = 1 + vlen := by
    rw [hpfx, List.length_cons, List.length_append]; omega
  have hptr : p + 1#64 + BitVec.ofNat 64 vlen = p + BitVec.ofNat 64 (1 + vlen) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have hbytes : (p ↦ₛ encodeRecord r) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) := by
    rw [hpfx, pointsToBytes_cons]
  unfold deserLocalsGA Prost.sliceCursorAfter deserFixedLocalsG_loopEntryG
  rw [hsub, hptr, hbytes, show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega, show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl, show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]
  exact Entails.of_eq (by ac_rfl)

private theorem stackAt_deserCallee_split_varint_loopEntryG (L : BitVec 64) :
    stackAt L deserCalleeStack =
      stackAt L Prost.X.decodeVarintSliceStackW ∗ memRegion (L - 63632#64) 38976 := by
  change memRegion (L - 63632#64) 63632 = memRegion (L - 24656#64) 24656 ∗ memRegion (L - 63632#64) 38976
  rw [memRegion_split (L - 63632#64) 38976 24656 (by decide)]
  rw [show L - 63632#64 + 38976#64 = L - 24656#64 by bv_omega, sepConj_comm]

private theorem allocFailedIn_of_trace_eq_loopEntryG {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at h ⊢; rwa [htr] at h

private theorem allowPanic_frame_trace_loopEntryG {s0 sm sf : State} {F R : SepProp} (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq_loopEntryG htr) h

private theorem step_1_combined_loopEntryG (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length)
    (hx8 : s0.readReg64 .x8 = x.out)
    (heq : encodeRecord x.r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields x.r).flatMap GenField.enc).length) ++
      (recFields x.r).flatMap GenField.enc)
    (hrec_lt : (encodeRecord x.r).length < 2 ^ 20) (hal : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s0.sp recDeserializeStack ∗ R)
    (hL : (SP2Ext img.base ext).CodeLoaded s0.mem) :
    let L := deserSpL s0.sp; let body := (recFields x.r).flatMap GenField.enc
    let rest1 := encodeVarint (BitVec.ofNat 64 body.length) ++ body
    ∃ s2, Steps (SP2Ext img.base ext) s0 s2 ∧ s2.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 348#64 ∧
      s2.status = .Running ∧ s2.sp = L ∧ (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
      s2.readReg64 .x19 = x.out ∧ s2.readReg64 .x23 = L + 1032#64 ∧ s2.readReg64 .x29 = L + 1808#64 ∧
      (s2.mem ⊨ (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
          ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ (x.p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG A L ∗ deserSaved s0) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
  intro L body rest1
  have hsp0 : s0.sp = L + 1904#64 := by change s0.sp = s0.sp - 0x770#64 + 1904#64; bv_omega
  obtain ⟨halignL, halign1808⟩ := sp_sub_1904_aligned_loopEntryG (decide_eq_true_iff.mp hal)
  have hbs_cons : encodeRecord x.r = 0x0a#8 :: rest1 := by rw [heq, encodeKey_1_ld_loopEntryG]; rfl
  have hv_pos := encodeVarint_length_pos_loopEntryG (BitVec.ofNat 64 body.length)
  have hlen1_pos : 0 < rest1.length := by simp only [rest1, List.length_append]; omega
  have hlen1_lt : rest1.length < 2 ^ 20 := by rw [hbs_cons, List.length_cons] at hrec_lt; omega
  have hx1' : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + rest1.length) := by rw [hx1, hbs_cons, List.length_cons, Nat.add_comm]
  have hm0a : s0.mem ⊨ (memRegion L 1904 ∗ (x.p ↦₈ 0x0a#8)) ∗
      (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
    rw [hbs_cons, pointsToBytes_cons, stackAt_recDeserialize_split_loopEntryG s0.sp] at hm0
    dsimp only [L]; convert hm0 using 1; ac_rfl
  rw [memRegion_1904_split_loopEntryG L x.p] at hm0a; simp only [sepExists_sepConj_left, satisfies_sepExists] at hm0a
  rcases hm0a with ⟨w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1, w0, u7, u6, u5, u4, u3, u2, u1, u0, hm0b⟩
  have hm0c : s0.mem ⊨ step1aPre_loopEntryG L x.p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
      (memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by convert hm0b using 1; ac_rfl
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, rfl, hsp1, htr1, hx0_1, hx19_1, hx21_1, hx23_1, hx24_1, hx26_1, hx29_1⟩ | ⟨_, _hoom⟩⟩ :=
    (step_1a_loopEntryG img ext L x.p x.out rest1.length w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7
      (post := fun s' P => P = step1aPost_loopEntryG L x.p rest1.length s0 ∧ s'.sp = L ∧
        (s'.trace = s0.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s0) ∧ s'.readReg64 .x0 = 2#64 ∧
        s'.readReg64 .x19 = x.out ∧ s'.readReg64 .x21 = noneCap ∧ s'.readReg64 .x23 = L + 1032#64 ∧
        s'.readReg64 .x24 = 1#64 ∧ s'.readReg64 .x26 = 8#64 ∧ s'.readReg64 .x29 = L + 1808#64)
      hpc hrun hsp0 halignL halign1808 hx0 hx1' hx8 hlen1_pos hlen1_lt
      (fun s' _ _ hsp' htr' hx0' hx19' hx21' hx23' hx24' hx26' hx29' =>
        ⟨rfl, hsp', htr', hx0', hx19', hx21', hx23', hx24', hx26', hx29'⟩)).elim hm0c hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hm1a : s1.mem ⊨ (((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336) ∗
      (deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold step1aPost_loopEntryG at hm1; convert hm1 using 1; ac_rfl
  rw [memRegion_1064_336_cells_loopEntryG L] at hm1a; simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1a
  rcases hm1a with ⟨c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, hm1b⟩
  have hm1c : s1.mem ⊨ ssUninitCells_loopEntryG L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
      ((memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 ∗
        deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold ssUninitCells_loopEntryG at hm1b ⊢; convert hm1b using 1; ac_rfl
  obtain ⟨s2, hst2, ⟨hpc2, hrun2, P2, hm2, rfl, hsp2, htr2, hx19_2, hx23_2, hx29_2⟩ | ⟨_, _hoom⟩⟩ :=
    (step_1b_loopEntryG img ext L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      (post := fun s' P => P = ssRawCells_loopEntryG L ∧ s'.sp = L ∧
        (s'.trace = s1.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s1) ∧ s'.readReg64 .x19 = s1.readReg64 .x19 ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = s1.readReg64 .x29)
      hpc1 hrun1 hsp1 halignL hx0_1 hx21_1 hx23_1 hx24_1 hx26_1
      (fun s' _ _ hsp' htr' hx19' hx23' hx29' => ⟨rfl, hsp', htr', hx19', hx23', hx29'⟩)).elim hm1c (hst1.codeLoaded hL)
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s2, hst1.trans hst2, hpc2, hrun2, hsp2, ⟨htr2.1.trans htr1.1, htr2.2.trans htr1.2⟩,
    hx19_2.trans hx19_1, hx23_2, hx29_2.trans hx29_1, ?_⟩
  rw [← sepConj_assoc] at hm2
  exact Satisfies.mono (sepConj_mono_left (step1b_post_entails_loopEntryG A L x.p rest1.length s0 rfl)) hm2

private theorem deserializeGenSpecAtA_A0_entry (img : Obj.Image) :
    deserializeGenSpecAtA A0 img = deserializeGenSpecAt img := by
  have hp : A0.pool = emp := rfl
  unfold deserializeGenSpecAtA deserializeGenSpecAt; simp only [hp, emp_sepConj]

private theorem DeserLoopGAtWA_A0_entry (img : Obj.Image) (ext : String → Option (State → State)) :
    DeserLoopGAtWA img A0 ext = DeserLoopGAtW img ext := by
  funext x R s0 k s; have hp : A0.pool = emp := rfl
  unfold DeserLoopGAtWA DeserLoopGAtW DeserLoopGAtX; simp only [deserLocalsGA_A0, hp, emp_sepConj]

/-! ### Loop entry from field layout -/
set_option maxHeartbeats 1600000 in
theorem deserLoopEntryG_ok_of_fieldsA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hC : DeserializeCalleesAtWA img A ext) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (deserializeGenSpecAtA A img).pre x s0 ∗ R) (hal : s0.spAligned = true)
    (heq : DeserializeScope x.r → encodeRecord x.r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields x.r).flatMap GenField.enc).length) ++
      (recFields x.r).flatMap GenField.enc)
    (hlt : DeserializeScope x.r → (encodeRecord x.r).length < 2 ^ 20) :
    DeserStepGAtWA img A ext x R s0 s0 (DeserLoopGAtWA img A ext x R s0 0) := by
  intro hL0; dsimp only [deserializeGenSpecAtA] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hr, hF0, hsym0⟩, hm0⟩
  have hm0' : s0.mem ⊨ (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s0.sp recDeserializeStack ∗ (A.pool ∗ R) := by
    convert hm0 using 1; ac_rfl
  have heq' := heq hr; have hrec_lt := hlt hr
  obtain ⟨halignL, _halign1808⟩ := sp_sub_1904_aligned_loopEntryG (decide_eq_true_iff.mp hal)
  obtain ⟨s2, hst2, hpc2, hrun2, hsp2, htr2, hx19_2, hx23_2, hx29_2, hm2⟩ :=
    step_1_combined_loopEntryG img A ext x (A.pool ∗ R) s0 hpc hrun hx0 hx1 hx8 heq' hrec_lt hal hm0' hL0
  set L := deserSpL s0.sp; set body := (recFields x.r).flatMap GenField.enc
  set N := body.length; set rest1 := encodeVarint (BitVec.ofNat 64 N) ++ body
  have hbs_cons : encodeRecord x.r = 0x0a#8 :: rest1 := by rw [heq', encodeKey_1_ld_loopEntryG]; rfl
  have hrest1_lt : rest1.length < 2 ^ 20 := by rw [hbs_cons, List.length_cons] at hrec_lt; omega
  by_cases hN : N < 128
  · have hr1 : rest1 = BitVec.ofNat 8 N :: body := by
      simp only [rest1, encodeVarint_of_lt_128_loopEntryG hN, List.singleton_append]
    have hlen1 : rest1.length = 1 + N := by rw [hr1, List.length_cons, Nat.add_comm]
    have hm2a : s2.mem ⊨ step2aPre_loopEntryG L x.p N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ body) ∗ (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗
          deserFixedLocalsG_loopEntryG A L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ (A.pool ∗ R)) := by
      rw [hlen1, hr1, pointsToBytes_cons] at hm2; unfold step2aPre_loopEntryG; convert hm2 using 1; ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl, hsp3, htr3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2a_loopEntryG img ext L x.p x.out N
        (post := fun s' P => P = step2aPost_loopEntryG L x.p N ∧ s'.sp = L ∧
          (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧ s'.readReg64 .x19 = x.out ∧
          s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN
        (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' => ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim hm2a (hst2.codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    refine ⟨s3, hst2.trans hst3, Or.inl ⟨by unfold deserPCAtX; rw [hpc3], hrun3,
      ⟨htr3.1.trans htr2.1, htr3.2.trans htr2.2⟩, by rw [(hst2.trans hst3).symtab_eq, hsym0],
      (hst2.trans hst3).frozenLoaded hF0, hsp3, by rw [State.spAligned, hsp3]; exact decide_eq_true halignL,
      hx29_3, hx19_3, hx20_3, hx23_3, ?_⟩⟩
    have hloc := deserLocalsG_of_2a_loopEntryG A L x.p x.r heq' hN
    have hdrop : (((recFields x.r).drop 0).flatMap GenField.enc) = body := by rw [List.drop_zero]
    have hss0 : ssgAfter x.r 0 = SSG.empty := rfl
    change s3.mem ⊨ deserLocalsGA A L x.p (encodeRecord x.r) (((recFields x.r).drop 0).flatMap GenField.enc) (ssgAfter x.r 0) ∗
      memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
    rw [hdrop, hss0, ← hloc]; convert hm3 using 1; ac_rfl
  · have hN_ge : 128 ≤ N := by omega
    set vlen := (encodeVarint (BitVec.ofNat 64 N)).length
    set vtail := encodeVarintAux 9 (BitVec.ofNat 64 N >>> 7)
    have hlen1 : rest1.length = vlen + N := List.length_append
    have hVN_lt : vlen + N < 2 ^ 20 := by rw [← hlen1]; exact hrest1_lt
    have hN_lt : N < 2 ^ 20 := by omega
    have hr1 : rest1 = BitVec.ofNat 8 (N % 128 + 128) :: (vtail ++ body) := by
      simp only [rest1, vtail, encodeVarint_cons_of_ge_128_loopEntryG hN_ge hN_lt, List.cons_append]
    have hm2_bytes : ((x.p + 1#64) ↦ₛ rest1) =
        ((x.p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128)) ∗ ((x.p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) := by
      rw [hr1, pointsToBytes_cons]
    have hm2c : s2.mem ⊨ step2bPre_loopEntryG L x.p vlen N ∗
        (((x.p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) ∗ (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗
          deserFixedLocalsG_loopEntryG A L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ (A.pool ∗ R)) := by
      rw [hlen1, hm2_bytes] at hm2; unfold step2bPre_loopEntryG; convert hm2 using 1; ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl, hsp3, htr3, hlr_3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2b_pre_loopEntryG img ext L x.p x.out vlen N
        (post := fun s' P => P = step2bPre_loopEntryG L x.p vlen N ∧ s'.sp = L ∧
          (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧
          s'.readReg64 .lr = (SP2Ext img.base ext).fnAddr recDeserializeName + 540#64 ∧
          s'.readReg64 .x0 = L + 1400#64 ∧ s'.readReg64 .x1 = x.p + 1#64 ∧
          s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) ∧ s'.readReg64 .x19 = x.out ∧
          s'.readReg64 .x20 = L + 1016#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN_ge hVN_lt
        (fun s' _ _ hsp' htr' hlr' hx0' hx1' hx2' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hlr', hx0', hx1', hx2', hx19', hx20', hx23', hx29'⟩)).elim hm2c (hst2.codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hpc3' : s3.pc = (SP2Ext img.base ext).fnAddr Prost.decodeVarintSliceName := by
      rw [hpc3, decodeVarintSlice_fnAddr_eq_deser_at_ext]
    have hal3 : s3.spAligned = true := by rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    have hx2_3_nat : (s3.readReg64 .x2).toNat = rest1.length := by
      rw [hx2_3, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpre_slice : Prost.VarintSlicePre rest1 := Or.inl (by omega)
    let gvar : Prost.DecodeVarintSliceGhost := ⟨L + 1400#64, x.p + 1#64, rest1⟩
    let F_call : SepProp := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
      ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗ memRegion (L - 63632#64) 38976 ∗
      memRegion (L + 1424#64) 344 ∗ (x.p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopEntryG A L ∗ deserSaved s0 ∗ memRegion x.out 368
    have hm3_call : s3.mem ⊨ ((Prost.X.decodeVarintSliceSpecW A).inImage img).pre gvar s3 ∗ (F_call ∗ R) := by
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW; dsimp only [gvar]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨(hst2.trans hst3).frozenLoaded hF0, (hst2.trans hst3).symtab_eq.trans hsym0⟩,
        ⟨hx0_3, hx1_3, hx2_3_nat, by omega, hpre_slice⟩, ?_⟩
      unfold step2bPre_loopEntryG at hm3
      rw [memRegion_split (L + 1400#64) 24 344 (by decide), stackAt_deserCallee_split_varint_loopEntryG L,
        show L + 1400#64 + 24#64 = L + 1424#64 by bv_omega] at hm3
      dsimp only [F_call]; rw [hsp3, hm2_bytes]; convert hm3 using 1; ac_rfl
    obtain ⟨s4, hst4, hpost4, _⟩ :=
      hC.1.no_fault_before_outcome gvar (F_call ∗ R) s3 hpc3' hrun3 hm3_call hal3 ((hst2.trans hst3).codeLoaded hL0)
    rcases hpost4 with ⟨⟨hpc4, _, hrun4⟩, ⟨hsp4, hcs4⟩, hm4⟩ | ⟨hpan4, hm4_pan⟩ | ⟨code, _, hm4_ex⟩ | ⟨_, hm4_oom⟩
    · have hpc4' : s4.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 540#64 := by rw [hpc4, hlr_3]
      have hsp4' : s4.sp = L := by rw [hsp4, hsp3]
      have hx19_4 : s4.readReg64 .x19 = x.out := by rw [hcs4.1, hx19_3]
      have hx20_4 : s4.readReg64 .x20 = L + 1016#64 := by rw [hcs4.2.1, hx20_3]
      have hx23_4 : s4.readReg64 .x23 = L + 1032#64 := by rw [hcs4.2.2.2.2.1, hx23_3]
      have hx29_4 : s4.readReg64 .x29 = L + 1808#64 := by rw [hcs4.2.2.2.2.2.2.2.2.2.2.1, hx29_3]
      have hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hcs4.2.2.2.2.2.2.2.2.2.2.2.trans (htr3.2.trans htr2.2)
      have hdec : decodeVarint rest1 = some (BitVec.ofNat 64 N, body) := decodeVarint_encodeVarint (BitVec.ofNat 64 N) body
      have hsub1 : rest1.length - body.length = vlen := by rw [hlen1]; change (vlen + N) - N = vlen; omega
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW at hm4; dsimp only [gvar] at hm4
      rw [hdec] at hm4; dsimp only [Prost.varintSliceResultAt] at hm4
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm4; rcases hm4 with ⟨htr4, hm4⟩
      have hm4a : s4.mem ⊨ step2bPostPre_loopEntryG L x.p vlen N ∗
          (memRegion (L + 1424#64) 344 ∗ ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗
            deserFixedLocalsG_loopEntryG A L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ (A.pool ∗ R)) := by
        dsimp only [F_call] at hm4; unfold step2bPostPre_loopEntryG
        rw [hsp3, pointsTo64_zero_split32_loopEntryG (L + 1400#64), hsub1] at hm4
        rw [stackAt_deserCallee_split_varint_loopEntryG L]
        rw [show L + 1400#64 + 4#64 = L + 1404#64 by bv_omega,
          show L + 1400#64 + 8#64 = L + 1408#64 by bv_omega,
          show L + 1400#64 + 16#64 = L + 1416#64 by bv_omega] at hm4
        convert hm4 using 1; ac_rfl
      obtain ⟨s5, hst5, ⟨hpc5, hrun5, P5, hm5, rfl, hsp5, htr5, hx19_5, hx20_5, hx23_5, hx29_5⟩ | ⟨_, _hoom⟩⟩ :=
        (step_2b_post_loopEntryG img ext L x.p x.out vlen N
          (post := fun s' P => P = step2bPostPost_loopEntryG L x.p vlen N ∧ s'.sp = L ∧
            (s'.trace = s4.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s4) ∧ s'.readReg64 .x19 = x.out ∧
            s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
          hpc4' hrun4 hsp4' halignL hx19_4 hx20_4 hx23_4 hx29_4 hVN_lt
          (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
            ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim hm4a ((hst2.trans (hst3.trans hst4)).codeLoaded hL0)
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      refine ⟨s5, (hst2.trans (hst3.trans hst4)).trans hst5, Or.inl ⟨by unfold deserPCAtX; rw [hpc5], hrun5,
        ⟨(htr5.1.trans htr4).trans (htr3.1.trans htr2.1), htr5.2.trans hv4⟩,
        by rw [((hst2.trans (hst3.trans hst4)).trans hst5).symtab_eq, hsym0],
        ((hst2.trans (hst3.trans hst4)).trans hst5).frozenLoaded hF0,
        hsp5, by rw [State.spAligned, hsp5]; exact decide_eq_true halignL, hx29_5, hx19_5, hx20_5, hx23_5, ?_⟩⟩
      have hloc := deserLocalsG_of_2b_loopEntryG A L x.p x.r heq'
      have hdrop : (((recFields x.r).drop 0).flatMap GenField.enc) = body := by rw [List.drop_zero]
      have hss0 : ssgAfter x.r 0 = SSG.empty := rfl
      change s5.mem ⊨ deserLocalsGA A L x.p (encodeRecord x.r) (((recFields x.r).drop 0).flatMap GenField.enc) (ssgAfter x.r 0) ∗
        memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [hdrop, hss0]
      have hm5a : s5.mem ⊨
          ((step2bPostPost_loopEntryG L x.p vlen N ∗ memRegion (L + 1424#64) 344) ∗
            ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopEntryG A L) ∗
          (memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R) := by
        convert hm5 using 1; ac_rfl
      exact Satisfies.mono (sepConj_mono_left hloc) hm5a
    · refine ⟨s4, (hst2.trans hst3).trans hst4, Or.inr ⟨hpan4, ?_⟩⟩
      dsimp only [deserializeGenSpecAtA, Serialization.allocPanic]
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW at hm4_pan; dsimp only at hm4_pan
      have hm4_pan' : s4.mem ⊨ ((⌜allocFailedIn s3 s4 ∧ s3.trace <+: s4.trace⌝ ∗ anyHeap) ∗ F_call) ∗ R := by
        convert hm4_pan using 1; ac_rfl
      exact allowPanic_frame_trace_loopEntryG (htr3.1.trans htr2.1) hm4_pan'
    · exact False.elim (not_satisfies_false_sepConj hm4_ex)
    · exact False.elim (not_satisfies_false_sepConj hm4_oom)

theorem deserLoopEntryG_ok_of_fields (img : Obj.Image)
    (ext : String → Option (State → State))
    (hC : DeserializeCalleesAtW img ext) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (deserializeGenSpecAt img).pre x s0 ∗ R) (hal : s0.spAligned = true)
    (heq : DeserializeScope x.r → encodeRecord x.r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFields x.r).flatMap GenField.enc).length) ++
      (recFields x.r).flatMap GenField.enc)
    (hlt : DeserializeScope x.r → (encodeRecord x.r).length < 2 ^ 20) :
    DeserStepGAtW img ext x R s0 s0 (DeserLoopGAtW img ext x R s0 0) := by
  unfold DeserStepGAtW
  rw [← deserializeGenSpecAtA_A0_entry, ← DeserLoopGAtWA_A0_entry]
  exact deserLoopEntryG_ok_of_fieldsA img A0 ext hC x R s0 hpc hrun (by rwa [deserializeGenSpecAtA_A0_entry]) hal heq hlt

theorem deserLoopEntryG_ok_atWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hC : DeserializeCalleesAtWA img A ext) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (deserializeGenSpecAtA A img).pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStepGAtWA img A ext x R s0 s0 (DeserLoopGAtWA img A ext x R s0 0) :=
  deserLoopEntryG_ok_of_fieldsA img A ext hC x R s0 hpc hrun hpre hal
    (encodeRecord_eq_recFields x.r) encodeRecord_length_lt

theorem deserLoopEntryG_ok_atW (img : Obj.Image)
    (ext : String → Option (State → State))
    (hC : DeserializeCalleesAtW img ext) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (deserializeGenSpecAt img).pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStepGAtW img ext x R s0 s0 (DeserLoopGAtW img ext x R s0 0) :=
  deserLoopEntryG_ok_of_fields img ext hC x R s0 hpc hrun hpre hal
    (encodeRecord_eq_recFields x.r) encodeRecord_length_lt

/-! ## Relocatable `[LibsignalPlacement]` loop entry -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

private theorem encodeVarint_cons_of_ge_128_placed_loopEntryG {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 62) :
    encodeVarint (BitVec.ofNat 64 n) =
      BitVec.ofNat 8 (n % 128 + 128) :: encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : ¬ ((BitVec.ofNat 64 n).toNat < 0x80) := by omega
  unfold encodeVarint encodeVarintAux
  simp only [h1, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, hn,
    show (0x7F : BitVec 64).toNat = 127 from rfl,
    Nat.and_two_pow_sub_one_eq_mod n 7,
    show (0x80 : BitVec 64).toNat = 128 from rfl,
    Nat.or_comm, ← hor, BitVec.toNat_ofNat]
  omega

private theorem deserLocalsG_of_2a_placed_loopEntryG (L p : BitVec 64) (bs body : List (BitVec 8))
    (heq : bs = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 body.length) ++ body)
    (hN : body.length < 128) :
    step2aPost_loopEntryG L p body.length ∗
      ((p + 1#64 + 1#64) ↦ₛ body) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG A0 L =
    deserLocalsG L p bs body SSG.empty := by
  have hpfx : bs = 0x0a#8 :: BitVec.ofNat 8 body.length :: body := by
    rw [heq, encodeKey_1_ld_loopEntryG, encodeVarint_of_lt_128_loopEntryG hN]; rfl
  have hsub : bs.length - body.length = 2 := by
    rw [hpfx, List.length_cons, List.length_cons]; omega
  have hbytes : (p ↦ₛ bs) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 body.length) ∗
        ((p + 1#64 + 1#64) ↦ₛ body) := by
    rw [hpfx, pointsToBytes_cons, pointsToBytes_cons]
  unfold deserLocalsG Prost.sliceCursorAfter deserFixedLocalsG_loopEntryG step2aPost_loopEntryG
  rw [hsub, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (BitVec.ofNat 64 2 : BitVec 64) = 2#64 from rfl,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]; ac_rfl

private theorem deserLocalsG_of_2b_placed_loopEntryG (L p : BitVec 64) (bs body : List (BitVec 8))
    (heq : bs = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 body.length) ++ body) :
    let vlen := (encodeVarint (BitVec.ofNat 64 body.length)).length
    (step2bPostPost_loopEntryG L p vlen body.length ∗ memRegion (L + 1424#64) 344) ∗
      ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) ∗
      (p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopEntryG A0 L ⊢
    deserLocalsG L p bs body SSG.empty := by
  intro vlen
  refine Entails.trans
    (sepConj_mono_left (step2bPostPost_entails_loopEntryG L p vlen body.length)) ?_
  have hpfx : bs = 0x0a#8 :: (encodeVarint (BitVec.ofNat 64 body.length) ++ body) := by
    rw [heq, encodeKey_1_ld_loopEntryG]; rfl
  have hsub : bs.length - body.length = 1 + vlen := by
    rw [hpfx, List.length_cons, List.length_append]; omega
  have hptr : p + 1#64 + BitVec.ofNat 64 vlen = p + BitVec.ofNat 64 (1 + vlen) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have hbytes : (p ↦ₛ bs) =
      (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) := by
    rw [hpfx, pointsToBytes_cons]
  unfold deserLocalsG Prost.sliceCursorAfter deserFixedLocalsG_loopEntryG
  rw [hsub, hptr, hbytes,
    show (0x3f8#64 : BitVec 64) = 1016#64 from rfl,
    show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl,
    show (0x170 : Nat) = 368 from rfl,
    show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]
  exact Entails.of_eq (by ac_rfl)

private theorem step_1b_placed_loopEntryG [LibsignalPlacement] {H : LibsignalHooks} (L : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64)
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 260#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halign : L &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = 2#64) (hx21 : s.readReg64 .x21 = noneCap)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx26 : s.readReg64 .x26 = 8#64)
    (hnext : ∀ s' : State, s'.pc = (blkPl_46).base + 348#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) →
      s'.readReg64 .x19 = s.readReg64 .x19 → s'.readReg64 .x23 = L + 1032#64 →
      s'.readReg64 .x29 = s.readReg64 .x29 → post s' (ssRawCells_loopEntryG L)) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 348#64) s
      (ssUninitCells_loopEntryG L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22)
      post := by
  unfold ssUninitCells_loopEntryG
  have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  rw [hnone] at hx21 ⊢
  (iterate 22 wp_step)
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold ssRawCells_loopEntryG; rw [hnone]; ac_rfl

private theorem step_1a_placed_loopEntryG [LibsignalPlacement] {H : LibsignalHooks}
    (L p out : BitVec 64) (len1 : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64)
    {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_46).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = L + 1904#64) (halignL : L &&& 15#64 = 0#64)
    (halign1808 : (L + 1808#64) &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + len1))
    (hx8 : s0.readReg64 .x8 = out) (hlen1_pos : 0 < len1) (hlen1_lt : len1 < 2 ^ 62)
    (hnext : ∀ s1 : State, s1.pc = (blkPl_46).base + 260#64 → s1.status = .Running →
      s1.sp = L → (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      s1.readReg64 .x0 = 2#64 → s1.readReg64 .x19 = out → s1.readReg64 .x21 = noneCap →
      s1.readReg64 .x23 = L + 1032#64 → s1.readReg64 .x24 = 1#64 →
      s1.readReg64 .x26 = 8#64 → s1.readReg64 .x29 = L + 1808#64 →
      post s1 (step1aPost_loopEntryG L p len1 s0)) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 260#64) s0
      (step1aPre_loopEntryG L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7)
      post := by
  unfold step1aPre_loopEntryG
  have hcbz : (BitVec.ofNat 64 (1 + len1) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + len1 = 0 at hnat; omega
  have hsub1 : BitVec.ofNat 64 (1 + len1) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 len1 := by
    rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + len1) - 1#64 = BitVec.ofNat 64 len1 := by
    rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  (iterate 49 wp_step)
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by rw [hnone]; simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step1aPost_loopEntryG deserSavedAt_loopEntryG; rw [hnone]
  simp only [Reg.x29, Reg.x30, Reg.x28, Reg.x27, Reg.x26, Reg.x25, Reg.x24, Reg.x23,
    Reg.x22, Reg.x21, Reg.x20, Reg.x19]
  ac_rfl

private theorem step_2a_placed_loopEntryG [LibsignalPlacement] {H : LibsignalHooks}
    (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_lt : N < 128)
    (hnext : ∀ s' : State, s'.pc = (blkPl_46).base + 596#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) →
      s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2aPost_loopEntryG L p N)) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 596#64) s (step2aPre_loopEntryG L p N) post := by
  unfold step2aPre_loopEntryG
  have hcbz : (BitVec.ofNat 64 (1 + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change 1 + N = 0 at hnat; omega
  have hse := signExtend64_ofNat8_lt_128_loopEntryG hN_lt
  have hbit63 : (((BitVec.ofNat 8 N).signExtend 64).getLsbD 63 == true) = false :=
    (signExtend64_bit63_eq_false_iff_loopEntryG (BitVec.ofNat 8 N)).mpr (by rw [BitVec.toNat_ofNat]; omega)
  have hsub1 : BitVec.ofNat 64 (1 + N) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + N) - 1#64 = BitVec.ofNat 64 N := by
    rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  (iterate 14 wp_step)
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2aPost_loopEntryG; ac_rfl

private theorem step_2b_pre_placed_loopEntryG [LibsignalPlacement] {H : LibsignalHooks}
    (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64)
    (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_ge : 128 ≤ N) (hVN_lt : vlen + N < 2 ^ 62)
    (hnext : ∀ s' : State, s'.pc = lsmpl.base 76 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) →
      s'.readReg64 .lr = (blkPl_46).base + 540#64 →
      s'.readReg64 .x0 = L + 1400#64 → s'.readReg64 .x1 = p + 1#64 →
      s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) → s'.readReg64 .x19 = out →
      s'.readReg64 .x20 = L + 1016#64 → s'.readReg64 .x23 = L + 1032#64 →
      s'.readReg64 .x29 = L + 1808#64 → post s' (step2bPre_loopEntryG L p vlen N)) :
    SepWP (lsProg_46 H) (lsmpl.base 76) s (step2bPre_loopEntryG L p vlen N) post := by
  unfold step2bPre_loopEntryG
  have hcbz : (BitVec.ofNat 64 (vlen + N) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne]; intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat
    change vlen + N = 0 at hnat; omega
  have hbit63 :
      (((BitVec.ofNat 8 (N % 128 + 128)).signExtend 64).getLsbD 63 == true) = true :=
    (signExtend64_bit63_eq_true_iff_loopEntryG (BitVec.ofNat 8 (N % 128 + 128))).mpr
      (by rw [BitVec.toNat_ofNat]; omega)
  have hhi10 : (10#64).ult (BitVec.ofNat 64 (vlen + N)) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      decide_eq_true_eq]; omega
  have hule10 : (BitVec.ofNat 64 (vlen + N)).ule 10#64 = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  (iterate 10 wp_step)
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])) ?_
  unfold step2bPre_loopEntryG; ac_rfl

private theorem step_2b_post_placed_loopEntryG [LibsignalPlacement] {H : LibsignalHooks}
    (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_46).base + 540#64) (hrun : s.status = .Running)
    (hsp : s.sp = L) (halignL : L &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = L + 1016#64)
    (hx23 : s.readReg64 .x23 = L + 1032#64) (hx29 : s.readReg64 .x29 = L + 1808#64)
    (hVN_lt : vlen + N < 2 ^ 62)
    (hnext : ∀ s' : State, s'.pc = (blkPl_46).base + 596#64 → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) →
      s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 →
      s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 →
      post s' (step2bPostPost_loopEntryG L p vlen N)) :
    SepWP (lsProg_46 H) ((blkPl_46).base + 596#64) s (step2bPostPre_loopEntryG L p vlen N) post := by
  unfold step2bPostPre_loopEntryG
  have hsub2 : BitVec.ofNat 64 (vlen + N) - BitVec.ofNat 64 vlen = BitVec.ofNat 64 N := by
    rw [BitVec.ofNat_add]; bv_omega
  have hult2 : (BitVec.ofNat 64 (vlen + N)).ult (BitVec.ofNat 64 vlen) = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show vlen < 2 ^ 64 by omega),
      decide_eq_false_iff_not]; omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  (iterate 14 wp_step)
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P)
    (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2bPostPost_loopEntryG; ac_rfl

private theorem step_1_combined_placed_loopEntryG [LibsignalPlacement] {H : LibsignalHooks}
    (p out : BitVec 64) (bs body : List (BitVec 8)) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_46).base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx8 : s0.readReg64 .x8 = out)
    (heq : bs = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 body.length) ++ body)
    (hrec_lt : bs.length < 2 ^ 62) (hal : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (p ↦ₛ bs) ∗ memRegion out 368 ∗ stackAt s0.sp recDeserializeStack ∗ R)
    (hL : (lsProg_46 H).CodeLoaded s0.mem) :
    let L := deserSpL s0.sp
    let rest1 := encodeVarint (BitVec.ofNat 64 body.length) ++ body
    ∃ s2, Steps (lsProg_46 H) s0 s2 ∧ s2.pc = (blkPl_46).base + 348#64 ∧
      s2.status = .Running ∧ s2.sp = L ∧
      (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
      s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = L + 1032#64 ∧
      s2.readReg64 .x29 = L + 1808#64 ∧
      (s2.mem ⊨
        (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
          ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ (p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG A0 L ∗ deserSaved s0) ∗
        (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
  intro L rest1
  have hsp0 : s0.sp = L + 1904#64 := by change s0.sp = s0.sp - 0x770#64 + 1904#64; bv_omega
  obtain ⟨halignL, halign1808⟩ := sp_sub_1904_aligned_loopEntryG (decide_eq_true_iff.mp hal)
  have hbs_cons : bs = 0x0a#8 :: rest1 := by rw [heq, encodeKey_1_ld_loopEntryG]; rfl
  have hv_pos := encodeVarint_length_pos_loopEntryG (BitVec.ofNat 64 body.length)
  have hlen1_pos : 0 < rest1.length := by simp only [rest1, List.length_append]; omega
  have hlen1_lt : rest1.length < 2 ^ 62 := by rw [hbs_cons, List.length_cons] at hrec_lt; omega
  have hx1' : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + rest1.length) := by
    rw [hx1, hbs_cons, List.length_cons, Nat.add_comm]
  have hm0a : s0.mem ⊨ (memRegion L 1904 ∗ (p ↦₈ 0x0a#8)) ∗
      (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
    rw [hbs_cons, pointsToBytes_cons, stackAt_recDeserialize_split_loopEntryG s0.sp] at hm0
    dsimp only [L]; convert hm0 using 1; ac_rfl
  rw [memRegion_1904_split_loopEntryG L p] at hm0a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm0a
  rcases hm0a with ⟨w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1, w0, u7, u6, u5, u4, u3, u2, u1, u0, hm0b⟩
  have hm0c : s0.mem ⊨
      step1aPre_loopEntryG L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
      (memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗
        memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    convert hm0b using 1; ac_rfl
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, rfl,
    hsp1, htr1, hx0_1, hx19_1, hx21_1, hx23_1, hx24_1, hx26_1, hx29_1⟩ | ⟨_, _hoom⟩⟩ :=
    (step_1a_placed_loopEntryG L p out rest1.length
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7
      (post := fun s' P => P = step1aPost_loopEntryG L p rest1.length s0 ∧
        s'.sp = L ∧ (s'.trace = s0.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s0) ∧
        s'.readReg64 .x0 = 2#64 ∧ s'.readReg64 .x19 = out ∧ s'.readReg64 .x21 = noneCap ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x24 = 1#64 ∧
        s'.readReg64 .x26 = 8#64 ∧ s'.readReg64 .x29 = L + 1808#64)
      hpc hrun hsp0 halignL halign1808 hx0 hx1' hx8 hlen1_pos hlen1_lt
      (fun s' _ _ hsp' htr' hx0' hx19' hx21' hx23' hx24' hx26' hx29' =>
        ⟨rfl, hsp', htr', hx0', hx19', hx21', hx23', hx24', hx26', hx29'⟩)).elim hm0c hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hm1a : s1.mem ⊨ (((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336) ∗
      (deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold step1aPost_loopEntryG at hm1; convert hm1 using 1; ac_rfl
  rw [memRegion_1064_336_cells_loopEntryG L] at hm1a
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1a
  rcases hm1a with ⟨c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11,
    c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, hm1b⟩
  have hm1c : s1.mem ⊨
      ssUninitCells_loopEntryG L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
      ((memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 ∗
        deserSavedAt_loopEntryG L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗
        ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
        ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32) ∗
        (((p + 1#64) ↦ₛ rest1) ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold ssUninitCells_loopEntryG at hm1b ⊢; convert hm1b using 1; ac_rfl
  obtain ⟨s2, hst2, ⟨hpc2, hrun2, P2, hm2, rfl, hsp2, htr2, hx19_2, hx23_2, hx29_2⟩ | ⟨_, _hoom⟩⟩ :=
    (step_1b_placed_loopEntryG L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      (post := fun s' P => P = ssRawCells_loopEntryG L ∧
        s'.sp = L ∧ (s'.trace = s1.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s1) ∧
        s'.readReg64 .x19 = s1.readReg64 .x19 ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = s1.readReg64 .x29)
      hpc1 hrun1 hsp1 halignL hx0_1 hx21_1 hx23_1 hx24_1 hx26_1
      (fun s' _ _ hsp' htr' hx19' hx23' hx29' =>
        ⟨rfl, hsp', htr', hx19', hx23', hx29'⟩)).elim hm1c (hst1.codeLoaded hL)
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s2, hst1.trans hst2, hpc2, hrun2, hsp2, ⟨htr2.1.trans htr1.1, htr2.2.trans htr1.2⟩,
    hx19_2.trans hx19_1, hx23_2, hx29_2.trans hx29_1, ?_⟩
  rw [← sepConj_assoc] at hm2
  exact Satisfies.mono (sepConj_mono_left (step1b_post_entails_loopEntryG A0 L p rest1.length s0 rfl)) hm2

set_option maxHeartbeats 1600000 in
/-- Relocatable `SessionRecord::deserialize` entry step (`+0x000` → `+0x254`) on `lsProg_46 H`,
parameterized over input bytes `bs` and body bytes `body` with `bs.length < 2 ^ 62`. -/
theorem deserLoopEntry_raw_placed_ok [LibsignalPlacement] (H : LibsignalHooks)
    (hVarint : Prost.X.DecodeVarintSlicePlacedOkW A0 H)
    (p out : BitVec 64) (bs body : List (BitVec 8)) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_46).base) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 bs.length)
    (hx8 : s0.readReg64 .x8 = out) (hal : s0.spAligned = true)
    (hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (heq : bs = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 body.length) ++ body)
    (hrec_lt : bs.length < 2 ^ 62)
    (hm0 : s0.mem ⊨ (p ↦ₛ bs) ∗ memRegion out 368 ∗ stackAt s0.sp recDeserializeStack ∗ R) :
    (lsProg_46 H).CodeLoaded s0.mem →
      ∃ s', Steps (lsProg_46 H) s0 s' ∧
        ((s'.pc = deserPlacedPC 0x254#64 ∧ s'.status = .Running ∧
          (s'.trace = s0.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s0) ∧
          LibsignalCodeRoLoaded lsmpl s'.mem ∧
          s'.sp = deserSpL s0.sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
          s'.readReg64 .x19 = out ∧ s'.readReg64 .x20 = 0#64 ∧
          s'.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
          (s'.mem ⊨ deserLocalsG (deserSpL s0.sp) p bs body SSG.empty ∗
            memRegion out 368 ∗ stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)) ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ Serialization.allocPanic () s0 s' ∗ R))) := by
  intro hL0
  obtain ⟨halignL, _halign1808⟩ := sp_sub_1904_aligned_loopEntryG (decide_eq_true_iff.mp hal)
  obtain ⟨s2, hst2, hpc2, hrun2, hsp2, htr2, hx19_2, hx23_2, hx29_2, hm2⟩ :=
    step_1_combined_placed_loopEntryG p out bs body R s0 hpc hrun hx0 hx1 hx8 heq hrec_lt hal hm0 hL0
  set L := deserSpL s0.sp
  set N := body.length
  set rest1 := encodeVarint (BitVec.ofNat 64 N) ++ body
  have hbs_cons : bs = 0x0a#8 :: rest1 := by rw [heq, encodeKey_1_ld_loopEntryG]; rfl
  have hrest1_lt : rest1.length < 2 ^ 62 := by rw [hbs_cons, List.length_cons] at hrec_lt; omega
  by_cases hN : N < 128
  · have hr1 : rest1 = BitVec.ofNat 8 N :: body := by
      simp only [rest1, encodeVarint_of_lt_128_loopEntryG hN, List.singleton_append]
    have hlen1 : rest1.length = 1 + N := by rw [hr1, List.length_cons, Nat.add_comm]
    have hm2a : s2.mem ⊨ step2aPre_loopEntryG L p N ∗
        (((p + 1#64 + 1#64) ↦ₛ body) ∗ (p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG A0 L ∗ deserSaved s0 ∗
          memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
      rw [hlen1, hr1, pointsToBytes_cons] at hm2
      unfold step2aPre_loopEntryG; convert hm2 using 1; ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl, hsp3, htr3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2a_placed_loopEntryG L p out N
        (post := fun s' P => P = step2aPost_loopEntryG L p N ∧
          s'.sp = L ∧ (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧
          s'.readReg64 .x19 = out ∧ s'.readReg64 .x20 = 0#64 ∧
          s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN
        (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim hm2a (hst2.codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    refine ⟨s3, hst2.trans hst3, Or.inl ?_⟩
    refine ⟨hpc3, hrun3, ⟨htr3.1.trans htr2.1, htr3.2.trans htr2.2⟩,
      hcrl0.of_keepsFrozen (hst2.trans hst3).keepsFrozen,
      hsp3, by rw [State.spAligned, hsp3]; exact decide_eq_true halignL,
      hx29_3, hx19_3, hx20_3, hx23_3, ?_⟩
    rw [← deserLocalsG_of_2a_placed_loopEntryG L p bs body heq hN]
    convert hm3 using 1; ac_rfl
  · have hN_ge : 128 ≤ N := by omega
    set vlen := (encodeVarint (BitVec.ofNat 64 N)).length
    set vtail := encodeVarintAux 9 (BitVec.ofNat 64 N >>> 7)
    have hlen1 : rest1.length = vlen + N := List.length_append
    have hVN_lt : vlen + N < 2 ^ 62 := by rw [← hlen1]; exact hrest1_lt
    have hN_lt : N < 2 ^ 62 := by omega
    have hr1 : rest1 = BitVec.ofNat 8 (N % 128 + 128) :: (vtail ++ body) := by
      simp only [rest1, vtail, encodeVarint_cons_of_ge_128_placed_loopEntryG hN_ge hN_lt, List.cons_append]
    have hm2_bytes : ((p + 1#64) ↦ₛ rest1) =
        ((p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128)) ∗
          ((p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) := by
      rw [hr1, pointsToBytes_cons]
    have hm2c : s2.mem ⊨ step2bPre_loopEntryG L p vlen N ∗
        (((p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) ∗
          (p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopEntryG A0 L ∗
          deserSaved s0 ∗ memRegion out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
      rw [hlen1, hm2_bytes] at hm2
      unfold step2bPre_loopEntryG; convert hm2 using 1; ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl,
      hsp3, htr3, hlr_3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2b_pre_placed_loopEntryG L p out vlen N
        (post := fun s' P => P = step2bPre_loopEntryG L p vlen N ∧
          s'.sp = L ∧ (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧
          s'.readReg64 .lr = (blkPl_46).base + 540#64 ∧
          s'.readReg64 .x0 = L + 1400#64 ∧ s'.readReg64 .x1 = p + 1#64 ∧
          s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) ∧ s'.readReg64 .x19 = out ∧
          s'.readReg64 .x20 = L + 1016#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧
          s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN_ge hVN_lt
        (fun s' _ _ hsp' htr' hlr' hx0' hx1' hx2' hx19' hx20' hx23' hx29' =>
          ⟨rfl, hsp', htr', hlr', hx0', hx1', hx2', hx19', hx20', hx23', hx29'⟩)).elim
        hm2c (hst2.codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hal3 : s3.spAligned = true := by rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    have hx2_3_nat : (s3.readReg64 .x2).toNat = rest1.length := by
      rw [hx2_3, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpre_slice : Prost.VarintSlicePre rest1 := Or.inl (by omega)
    have hcrl3 : LibsignalCodeRoLoaded lsmpl s3.mem := hcrl0.of_keepsFrozen (hst2.trans hst3).keepsFrozen
    have hcall : subroutine_ok (lsProg_46 H) (lsmpl.base 76)
        (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.decodeVarintSliceSpecW A0)) :=
      ls_call_ro_of_cl (callerProg := lsProg_46 H) hVarint
    let gvar : Prost.DecodeVarintSliceGhost := ⟨L + 1400#64, p + 1#64, rest1⟩
    let F_call : SepProp :=
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗
        ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗
        memRegion (L - 63632#64) 38976 ∗ memRegion (L + 1424#64) 344 ∗
        (p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopEntryG A0 L ∗ deserSaved s0 ∗ memRegion out 368
    have hm3_call : s3.mem ⊨
        (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.decodeVarintSliceSpecW A0)).pre
          gvar s3 ∗ (F_call ∗ R) := by
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl3, ?_⟩
      unfold Prost.X.decodeVarintSliceSpecW; dsimp only [gvar]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_3, hx1_3, hx2_3_nat, by omega, hpre_slice⟩, ?_⟩
      unfold step2bPre_loopEntryG at hm3
      rw [memRegion_split (L + 1400#64) 24 344 (by decide),
        stackAt_deserCallee_split_varint_loopEntryG L] at hm3
      have h1424 : L + 1400#64 + 24#64 = L + 1424#64 := by bv_omega
      have hpool : A0.pool = emp := rfl
      rw [h1424] at hm3
      dsimp only [F_call]
      rw [hsp3, hpool, hm2_bytes]
      convert hm3 using 1; ac_rfl
    obtain ⟨s4, hst4, hpost4, _⟩ :=
      hcall.no_fault_before_outcome gvar (F_call ∗ R) s3 hpc3 hrun3 hm3_call hal3
        ((hst2.trans hst3).codeLoaded hL0)
    rcases hpost4 with ⟨⟨hpc4, _, hrun4⟩, ⟨hsp4, hcs4⟩, hm4⟩ | ⟨hpan4, hm4_pan⟩ | ⟨code, _, hm4_ex⟩ | ⟨_, hm4_oom⟩
    · have hpc4' : s4.pc = (blkPl_46).base + 540#64 := by rw [hpc4, hlr_3]
      have hsp4' : s4.sp = L := by rw [hsp4, hsp3]
      have hx19_4 : s4.readReg64 .x19 = out := by rw [hcs4.1, hx19_3]
      have hx20_4 : s4.readReg64 .x20 = L + 1016#64 := by rw [hcs4.2.1, hx20_3]
      have hx23_4 : s4.readReg64 .x23 = L + 1032#64 := by rw [hcs4.2.2.2.2.1, hx23_3]
      have hx29_4 : s4.readReg64 .x29 = L + 1808#64 := by rw [hcs4.2.2.2.2.2.2.2.2.2.2.1, hx29_3]
      have hv4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 :=
        hcs4.2.2.2.2.2.2.2.2.2.2.2.trans (htr3.2.trans htr2.2)
      have hdec : decodeVarint rest1 = some (BitVec.ofNat 64 N, body) :=
        decodeVarint_encodeVarint (BitVec.ofNat 64 N) body
      have hsub1 : rest1.length - body.length = vlen := by
        rw [hlen1]; change (vlen + N) - N = vlen; omega
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hm4
      unfold Prost.X.decodeVarintSliceSpecW at hm4; dsimp only [gvar] at hm4
      rw [hdec] at hm4; dsimp only [Prost.varintSliceResultAt] at hm4
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
      rcases hm4 with ⟨htr4, hm4⟩
      have hm4a : s4.mem ⊨ step2bPostPre_loopEntryG L p vlen N ∗
          (memRegion (L + 1424#64) 344 ∗ ((p + 1#64) ↦ₛ rest1) ∗ (p ↦₈ 0x0a#8) ∗
            deserFixedLocalsG_loopEntryG A0 L ∗ deserSaved s0 ∗ memRegion out 368 ∗
            stackAt L deserCalleeStack ∗ R) := by
        dsimp only [F_call] at hm4; unfold step2bPostPre_loopEntryG
        have hpool : A0.pool = emp := rfl
        rw [hsp3, hpool, pointsTo64_zero_split32_loopEntryG (L + 1400#64), hsub1] at hm4
        rw [stackAt_deserCallee_split_varint_loopEntryG L]
        have ha1 : L + 1400#64 + 4#64 = L + 1404#64 := by bv_omega
        have ha2 : L + 1400#64 + 8#64 = L + 1408#64 := by bv_omega
        have ha3 : L + 1400#64 + 16#64 = L + 1416#64 := by bv_omega
        rw [ha1, ha2, ha3] at hm4
        convert hm4 using 1; ac_rfl
      obtain ⟨s5, hst5, ⟨hpc5, hrun5, P5, hm5, rfl, hsp5, htr5, hx19_5, hx20_5, hx23_5, hx29_5⟩ | ⟨_, _hoom⟩⟩ :=
        (step_2b_post_placed_loopEntryG L p out vlen N
          (post := fun s' P => P = step2bPostPost_loopEntryG L p vlen N ∧
            s'.sp = L ∧ (s'.trace = s4.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s4) ∧
            s'.readReg64 .x19 = out ∧ s'.readReg64 .x20 = 0#64 ∧
            s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
          hpc4' hrun4 hsp4' halignL hx19_4 hx20_4 hx23_4 hx29_4 hVN_lt
          (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' =>
            ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim
          hm4a ((hst2.trans (hst3.trans hst4)).codeLoaded hL0)
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      have hsteps_all := (hst2.trans (hst3.trans hst4)).trans hst5
      refine ⟨s5, hsteps_all, Or.inl ?_⟩
      refine ⟨hpc5, hrun5, ⟨(htr5.1.trans htr4).trans (htr3.1.trans htr2.1), htr5.2.trans hv4⟩,
        hcrl0.of_keepsFrozen hsteps_all.keepsFrozen,
        hsp5, by rw [State.spAligned, hsp5]; exact decide_eq_true halignL,
        hx29_5, hx19_5, hx20_5, hx23_5, ?_⟩
      have hm5a : s5.mem ⊨
          ((step2bPostPost_loopEntryG L p vlen N ∗ memRegion (L + 1424#64) 344) ∗
            ((p + 1#64) ↦ₛ rest1) ∗ (p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopEntryG A0 L) ∗
          (memRegion out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R) := by
        convert hm5 using 1; ac_rfl
      exact Satisfies.mono (sepConj_mono_left (deserLocalsG_of_2b_placed_loopEntryG L p bs body heq)) hm5a
    · refine ⟨s4, (hst2.trans hst3).trans hst4, Or.inr ⟨hpan4, ?_⟩⟩
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hm4_pan
      unfold Prost.X.decodeVarintSliceSpecW at hm4_pan; dsimp only [Serialization.allocPanic] at hm4_pan ⊢
      have hm4_pan' : s4.mem ⊨
          ((⌜allocFailedIn s3 s4 ∧ s3.trace <+: s4.trace⌝ ∗ anyHeap) ∗ F_call) ∗ R := by
        convert hm4_pan using 1; ac_rfl
      exact allowPanic_frame_trace_loopEntryG (htr3.1.trans htr2.1) hm4_pan'
    · exact False.elim (not_satisfies_false_sepConj hm4_ex)
    · exact False.elim (not_satisfies_false_sepConj hm4_oom)

/-- Relocatable `SessionRecord::deserialize` loop entry (`+0x000` → `+0x254`, `k = 0`) on
`lsProg_46 H`. -/
theorem deserLoopEntryG_placed_okW [LibsignalPlacement] (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (blkPl_46).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ deserializeGenPlacedSpec.pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStepGPlacedW H x R s0 s0 (DeserLoopGPlacedW x R s0 0) := by
  obtain ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [deserializeGenRawSpec] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx8, hr⟩, hm0⟩
  rw [sepConj_assoc, sepConj_assoc] at hm0
  have heq := encodeRecord_eq_recFields x.r hr
  have hlt : (encodeRecord x.r).length < 2 ^ 62 :=
    Nat.lt_trans (encodeRecord_length_lt hr) (by decide)
  intro hL0
  obtain ⟨s', hst, hout⟩ :=
    deserLoopEntry_raw_placed_ok H hC.1 x.p x.out (encodeRecord x.r)
      ((recFields x.r).flatMap GenField.enc) R s0 hpc hrun hx0 hx1 hx8 hal hcrl0 heq hlt hm0 hL0
  refine ⟨s', hst, ?_⟩
  rcases hout with hok | hpan
  · refine Or.inl ?_
    have hss0 : ssgAfter x.r 0 = SSG.empty := rfl
    simpa only [DeserLoopGPlacedW, List.drop_zero, hss0] using hok
  · exact Or.inr hpan

end Placed

end Proofs.libsignal.Hooks2.DeserLoopEntryGExt
