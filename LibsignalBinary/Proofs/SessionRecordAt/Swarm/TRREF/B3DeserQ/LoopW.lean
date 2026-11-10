/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.LoopIter
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopExitG
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserTransportX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopExitGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopIterGExt
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.ReprMove
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# W-Stack `SessionRecord::deserialize` Loop Entry, Iteration, Exit, and `.base` Framing

Verifies `.base` field framing (`mergeFieldQOkAtWA_base`), loop entry (`deserLoopEntryQ_ok_atW`),
loop iteration (`deserLoopIterQ_ok_atWA`), loop exit (`deserLoopExitQ_ok_of_memcpyA`), and full loop
assembly (`deserializeExactQWA_ok`, `recordDeserializeOpen_of_exactQA`) on `SP2Ext` with slice length
`< 2 ^ 62`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord CanonSession allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Bin (BinCanonSession recordDeserializeStack)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Hooks2.DeserLoopEntryGExt

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
open CryptoVerification.E2E.Record.DeserializeSeed.LoopIterStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero ofNat_succ_sub_one_loopIter
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setPC_pre_loopW (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setMem_setPC_pre_loopW (s : State) (pc : BitVec 64) (m : Memory) : ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg64_setPC_pre_loopW (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg64_setMem_setPC_pre_loopW (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) : ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg32_setPC_pre_loopW (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg32_setMem_setPC_pre_loopW (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) : ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg_setPC_pre_loopW (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) : (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg_setMem_setPC_pre_loopW (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) : ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local simp, local arm64_norm] private theorem int64_toBitVec_mk_loopW (u : UInt64) : ({ toUInt64 := u } : Int64).toBitVec = u.toBitVec := rfl
@[local simp, local arm64_norm] private theorem uint64_toBitVec_mk_loopW (v : BitVec 64) : ({ toBitVec := v } : UInt64).toBitVec = v := rfl
@[local simp, local arm64_norm] private theorem bitVec_toFin_mk_64_loopW (n : Nat) (h : n < 18446744073709551616 := by decide) : ({ toFin := ⟨n, h⟩ } : BitVec 64) = BitVec.ofNat 64 n := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt h).symm

theorem L1_B3DeserQ_LoopW : True := trivial

/-! ## `.base` framing (`mergeFieldQOkAtWA_base` / `mergeFieldQOkAtW_base`) -/

abbrev mergeFieldGenSpecAtW62 := mergeFieldGenSpecAtW
abbrev MergeFieldGenOkAtW62 := MergeFieldGenOkAtW

private theorem mergeFieldGenSpecAtWA_A0 (img : Obj.Image) (P : GenField → Prop) :
    mergeFieldGenSpecAtWA A0 img P = mergeFieldGenSpecAtW img P := by
  have hp : A0.pool = emp := rfl
  unfold mergeFieldGenSpecAtWA mergeFieldGenSpecAtW; simp only [hp, emp_sepConj]

private theorem mergeFieldQSpecAtWA_A0 (img : Obj.Image) (P : GenFieldQ → Prop) :
    mergeFieldQSpecAtWA A0 img P = mergeFieldQSpecAtW img P := by
  have hp : A0.pool = emp := rfl
  unfold mergeFieldQSpecAtWA mergeFieldQSpecAtW; simp only [hp, emp_sepConj]

/-- Lifts any `MergeFieldGenOkAtWA img A ext P` (tags 1..9) to
`MergeFieldQOkAtWA img A ext (fun fl => ∃ f, P f ∧ fl = .base f)`. -/
theorem mergeFieldQOkAtWA_base (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    {P : GenField → Prop} (hBase : MergeFieldGenOkAtWA img A ext P) :
    MergeFieldQOkAtWA img A ext (fun fl => ∃ f, P f ∧ fl = .base f) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' := hpre; simp only [mergeFieldQSpecAtWA, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hx4, ⟨f, hPf, hfl⟩, hok, hfresh, hlen, hF, hsym⟩, hmem⟩
  rcases x with ⟨ss, ⟨vbase, vext⟩, fld, bufSlot, curSlot, p, rest⟩
  dsimp only at hfl hx0 hx1 hx2 hx3 hx4 hok hfresh hlen hmem; subst hfl
  rcases hfresh with ⟨hvext, hfresh_f⟩; dsimp only at hvext hfresh_f; subst hvext
  let xG : MergeFieldGenGhost := ⟨ss, vbase, f, bufSlot, curSlot, p, rest⟩
  have hpreG : s0.mem ⊨ (mergeFieldGenSpecAtWA A img P).pre xG s0 ∗ R := by
    simp only [mergeFieldGenSpecAtWA, xG, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hPf, hok, hfresh_f, hlen, hF, hsym⟩, ?_⟩; rw [← prostSSGQAt_empty A ss vbase]; exact hmem
  refine hBase.mono_outcome xG R s0 hpc hrun hpreG hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩; simp only [mergeFieldGenSpecAtWA, mergeFieldQSpecAtWA, xG, SSGQ.apply] at hpost ⊢
    rw [prostSSGQAt_empty A ss (vbase.apply f)]; exact hpost
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

theorem mergeFieldQOkAtW_base (img : Obj.Image) (ext : String → Option (State → State))
    {P : GenField → Prop} (hBase : MergeFieldGenOkAtW img ext P) :
    MergeFieldQOkAtW img ext (fun fl => ∃ f, P f ∧ fl = .base f) := by
  unfold MergeFieldQOkAtW; rw [← mergeFieldQSpecAtWA_A0]
  exact mergeFieldQOkAtWA_base img A0 ext (by unfold MergeFieldGenOkAtWA; rwa [mergeFieldGenSpecAtWA_A0])

/-! ## Loop entry (`deserLoopEntryQ_ok_atW`) -/

local elab "d0_fetch_range_q " codeId:ident b:term:max H:term:max hfn:term:max off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "d0_fetch_range_q"
  let k0 := k0.getNat; let len := len.getNat; let codeBase := codeId.getId.eraseMacroScopes
  let fetchEntry := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := Lean.mkIdent (Lean.Name.str `Proofs.libsignal.Hooks2.DeserLoopEntryGExt s!"d0_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Lean.Syntax.mkNumLit (toString k)
    if k == 0 then Lean.Elab.Tactic.evalTactic (← `(tactic| have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else Lean.Elab.Tactic.evalTactic (← `(tactic| have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

local macro "d0_fetches_1a_q " b:term:max H:term:max : tactic => `(tactic| (
  d0_fetch_range_q CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 0 144
  d0_fetch_range_q CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 208 52))
local macro "d0_fetches_1b_q " b:term:max H:term:max : tactic => `(tactic| d0_fetch_range_q CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 260 88)
local macro "d0_fetches_2a_q " b:term:max H:term:max : tactic => `(tactic| (
  d0_fetch_range_q CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 348 36
  d0_fetch_range_q CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 576 20))
local macro "d0_fetches_2b_pre_q " b:term:max H:term:max : tactic => `(tactic| (
  d0_fetch_range_q CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 348 24
  d0_fetch_range_q CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 512 8
  d0_fetch_range_q CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 532 8))
local macro "d0_fetches_2b_post_q " b:term:max H:term:max : tactic => `(tactic| d0_fetch_range_q CryptoVerification.libsignalSessionCode $b $H (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize") (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) 540 56)

private theorem encodeKey_1_ld_loopW : encodeKey 1 .lengthDelimited = [0x0a#8] := rfl
private theorem encodeVarint_length_pos_loopW (v : BitVec 64) : 0 < (encodeVarint v).length := List.length_pos_iff.mpr (encodeVarint_ne_nil v)
private theorem encodeVarint_of_lt_128_loopW {n : Nat} (hn : n < 128) : encodeVarint (BitVec.ofNat 64 n) = [BitVec.ofNat 8 n] := by
  have h1 : (BitVec.ofNat 64 n).toNat < 0x80 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  unfold encodeVarint encodeVarintAux; simp only [h1, ↓reduceIte]; congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
private theorem encodeVarint_cons_of_ge_128_loopW {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 33) :
    encodeVarint (BitVec.ofNat 64 n) = BitVec.ofNat 8 (n % 128 + 128) :: encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : ¬ ((BitVec.ofNat 64 n).toNat < 0x80) := by omega
  unfold encodeVarint encodeVarintAux; simp only [h1, ↓reduceIte]; congr 1; apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1; simp only [Nat.reducePow, Nat.reduceMul] at hor
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, hn, show (0x7F : BitVec 64).toNat = 127 from rfl,
    Nat.and_two_pow_sub_one_eq_mod n 7, show (0x80 : BitVec 64).toNat = 128 from rfl, Nat.or_comm, ← hor, BitVec.toNat_ofNat]; omega
private theorem signExtend64_bit63_eq_false_iff_loopW (b0 : BitVec 8) : ((b0.signExtend 64).getLsbD 63 == true) = false ↔ b0.toNat ≤ 0x7F := by revert b0; decide
private theorem signExtend64_bit63_eq_true_iff_loopW (b0 : BitVec 8) : ((b0.signExtend 64).getLsbD 63 == true) = true ↔ 0x7F < b0.toNat := by revert b0; decide
private theorem signExtend64_eq_zeroExtend64_of_le_loopW (b0 : BitVec 8) (h : b0.toNat ≤ 0x7F) : b0.signExtend 64 = b0.zeroExtend 64 := by revert b0 h; decide
private theorem signExtend64_ofNat8_lt_128_loopW {n : Nat} (hn : n < 128) : (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hle : (BitVec.ofNat 8 n).toNat ≤ 0x7F := by rw [BitVec.toNat_ofNat]; omega
  rw [signExtend64_eq_zeroExtend64_of_le_loopW _ hle]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
private theorem sp_sub_1904_aligned_loopW {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0x770#64) &&& 15#64 = 0#64 ∧ (sp0 - 0x770#64 + 1808#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h; rw [e] at h'; have hlt := sp0.isLt; have hsub : sp0 - 0x770#64 + 1808#64 = sp0 - 96#64 := by bv_omega
  refine ⟨by apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega,
    by rw [hsub]; apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega⟩
private theorem empty_vecU8_intro_loopW (A : RustAlloc) (v : BitVec 64) : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A v [] := by
  dsimp only [vecU8, vecU8At, vecHeader]; simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64); refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [↓reduceIte, sepConj_emp, sepConj_assoc]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := by decide
  have heq : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗ ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗ ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by ac_rfl
  rw [heq]; exact Entails.pure_right hp (Entails.refl _)
private theorem empty_vecChainG_intro_loopW (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecOf A 104 8 (fun c a => prostChainGAt A a c) v [] := by
  dsimp only [vecOf, vecAt, vecHeader, vecBuf]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64); refine Entails.trans ?_ (Entails.sepExists_intro 8#64)
  have hite : (if (0#64 : BitVec 64) = 0 then emp else A.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
    arrayAt (fun c a => prostChainGAt A a c) 104 8#64 [] ∗
    memRegion (8#64 + BitVec.ofNat 64 (([] : List ChainG).length * 104)) (((0#64 : BitVec 64).toNat - ([] : List ChainG).length) * 104)) = emp := rfl
  rw [hite]; simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc, sepConj_emp]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64 := by decide
  have heq : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗ ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64⌝ =
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64⌝ ∗ ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by ac_rfl
  rw [heq]; exact Entails.pure_right hp (Entails.refl _)
private theorem pointsTo64_zero_split32_loopW (a : BitVec 64) : (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by simpa using pointsTo64_split32 a 0#64

private def ssRawCells_loopW (L : BitVec 64) : SepProp :=
  (((L + 0x420#64) ↦₆₄ 0#64) ∗ ((L + 0x428#64) ↦₆₄ 1#64) ∗ ((L + 0x430#64) ↦₆₄ 0#64)) ∗ (((L + 0x438#64) ↦₆₄ 0#64) ∗ ((L + 0x440#64) ↦₆₄ 1#64) ∗ ((L + 0x448#64) ↦₆₄ 0#64)) ∗
  (((L + 0x450#64) ↦₆₄ 0#64) ∗ ((L + 0x458#64) ↦₆₄ 1#64) ∗ ((L + 0x460#64) ↦₆₄ 0#64)) ∗ (((L + 0x468#64) ↦₆₄ 0#64) ∗ ((L + 0x470#64) ↦₆₄ 8#64) ∗ ((L + 0x478#64) ↦₆₄ 0#64)) ∗
  (((L + 0x480#64) ↦₆₄ 0#64) ∗ ((L + 0x488#64) ↦₆₄ 1#64) ∗ ((L + 0x490#64) ↦₆₄ 0#64)) ∗ (((L + 0x498#64) ↦₆₄ 0#64) ∗ ((L + 0x4a0#64) ↦₆₄ 1#64) ∗ ((L + 0x4a8#64) ↦₆₄ 0#64)) ∗
  ((L + 0x4b0#64) ↦₆₄ noneCap) ∗ ((L + 0x518#64) ↦₆₄ noneCap) ∗ ((L + 0x548#64) ↦₆₄ noneCap) ∗ ((L + 0x568#64) ↦₆₄ 0#64) ∗ ((L + 0x570#64) ↦₆₄ 0#64)

private theorem prostSSGAt_empty_intro_loopW (A : RustAlloc) (L : BitVec 64) :
    ssRawCells_loopW L ∗ memRegion (L + 0x4b8#64) 96 ∗ memRegion (L + 0x520#64) 40 ∗ memRegion (L + 0x550#64) 24 ⊢ prostSSGAt A (L + 0x420#64) SSG.empty := by
  unfold ssRawCells_loopW prostSSGAt SSG.empty; dsimp only
  have h1 := empty_vecU8_intro_loopW A (L + 0x420#64); have h2 := empty_vecU8_intro_loopW A (L + 0x420#64 + 0x18#64); have h3 := empty_vecU8_intro_loopW A (L + 0x420#64 + 0x30#64)
  have h4 := empty_vecChainG_intro_loopW A (L + 0x420#64 + 0x48#64); have h5 := empty_vecU8_intro_loopW A (L + 0x420#64 + 0x60#64); have h6 := empty_vecU8_intro_loopW A (L + 0x420#64 + 0x78#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢; rw [pointsTo64_zero_split32_loopW (L + 0x568#64)]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))

@[local arm64_norm ↓, local wp_norm ↓] private theorem add_1904_sub_96_loopW (L : BitVec 64) : L + 1904#64 + bv% (2 ^ 64 - 96) = L + 1808#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem add_1808_sub_1808_loopW (L : BitVec 64) : L + 1808#64 - 1808#64 = L := by bv_omega
@[local arm64_norm ↓, local wp_norm ↓] private theorem add_1808_sub_40_loopW (L : BitVec 64) : L + 1808#64 + bv% (2 ^ 64 - 40) = L + 1768#64 := by rw [BitVec.add_assoc]; rfl

private def deserSavedAt_loopW (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 1808#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 1816#64) ↦₆₄ s0.readReg64 .x30) ∗ ((L + 1824#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 1832#64) ↦₆₄ s0.readReg64 .x27) ∗ ((L + 1840#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 1848#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((L + 1856#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 1864#64) ↦₆₄ s0.readReg64 .x23) ∗ ((L + 1872#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 1880#64) ↦₆₄ s0.readReg64 .x21) ∗ ((L + 1888#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 1896#64) ↦₆₄ s0.readReg64 .x19)
private theorem deserSavedAt_eq_loopW (s0 : State) : deserSavedAt_loopW (deserSpL s0.sp) s0 = deserSaved s0 := by
  unfold deserSavedAt_loopW deserSaved deserSpL; dsimp only; simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
private def ssUninitCells_loopW (L : BitVec 64) (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64) : SepProp :=
  ((L + 1056#64) ↦₆₄ noneCap) ∗ ((L + 1064#64) ↦₆₄ c1) ∗ ((L + 1072#64) ↦₆₄ c2) ∗ ((L + 1080#64) ↦₆₄ c3) ∗ ((L + 1088#64) ↦₆₄ c4) ∗ ((L + 1096#64) ↦₆₄ c5) ∗ ((L + 1104#64) ↦₆₄ c6) ∗ ((L + 1112#64) ↦₆₄ c7) ∗ ((L + 1120#64) ↦₆₄ c8) ∗ ((L + 1128#64) ↦₆₄ c9) ∗ ((L + 1136#64) ↦₆₄ c10) ∗ ((L + 1144#64) ↦₆₄ c11) ∗
  ((L + 1152#64) ↦₆₄ c12) ∗ ((L + 1160#64) ↦₆₄ c13) ∗ ((L + 1168#64) ↦₆₄ c14) ∗ ((L + 1176#64) ↦₆₄ c15) ∗ ((L + 1184#64) ↦₆₄ c16) ∗ ((L + 1192#64) ↦₆₄ c17) ∗ ((L + 1200#64) ↦₆₄ c18) ∗ ((L + 1304#64) ↦₆₄ c19) ∗ ((L + 1352#64) ↦₆₄ c20) ∗ ((L + 1384#64) ↦₆₄ c21) ∗ ((L + 1392#64) ↦₆₄ c22)
private theorem step_1b_loopW (img : Obj.Image) (ext : String → Option (State → State)) (L : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 260#64) (hrun : s.status = .Running) (hsp : s.sp = L) (halign : L &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = 2#64) (hx21 : s.readReg64 .x21 = noneCap) (hx23 : s.readReg64 .x23 = L + 1032#64) (hx24 : s.readReg64 .x24 = 1#64) (hx26 : s.readReg64 .x26 = 8#64)
    (hnext : ∀ s' : State, s'.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 348#64 → s'.status = .Running → s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) →
      s'.readReg64 .x19 = s.readReg64 .x19 → s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = s.readReg64 .x29 → post s' (ssRawCells_loopW L)) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName + 348#64) s (ssUninitCells_loopW L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22) post := by
  let H := Rust.withPanics ext; d0_fetches_1b_q img.base H; dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry; examples_hide_fetches; unfold ssUninitCells_loopW; have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl; rw [hnone] at hx21 ⊢
  (iterate 22 wp_step); apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P) (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold ssRawCells_loopW; rw [hnone]; ac_rfl
private def step1aPre_loopW (L p : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) : SepProp :=
  ((L + 1808#64) ↦₆₄ w0) ∗ ((L + 1816#64) ↦₆₄ w1) ∗ ((L + 1824#64) ↦₆₄ w2) ∗ ((L + 1832#64) ↦₆₄ w3) ∗ ((L + 1840#64) ↦₆₄ w4) ∗ ((L + 1848#64) ↦₆₄ w5) ∗ ((L + 1856#64) ↦₆₄ w6) ∗ ((L + 1864#64) ↦₆₄ w7) ∗ ((L + 1872#64) ↦₆₄ w8) ∗ ((L + 1880#64) ↦₆₄ w9) ∗ ((L + 1888#64) ↦₆₄ w10) ∗ ((L + 1896#64) ↦₆₄ w11) ∗
  (L ↦₆₄ u0) ∗ ((L + 1016#64) ↦₆₄ u1) ∗ ((L + 1024#64) ↦₆₄ u2) ∗ ((L + 1032#64) ↦₆₄ u3) ∗ ((L + 1040#64) ↦₆₄ u4) ∗ ((L + 1048#64) ↦₆₄ u5) ∗ ((L + 1056#64) ↦₆₄ u6) ∗ ((L + 1768#64) ↦₆₄ u7) ∗ (p ↦₈ 10#8)
private def step1aPost_loopW (L p : BitVec 64) (len1 : Nat) (s0 : State) : SepProp :=
  deserSavedAt_loopW L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1056#64) ↦₆₄ noneCap) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 10#8)
private theorem step_1a_loopW (img : Obj.Image) (ext : String → Option (State → State)) (L p out : BitVec 64) (len1 : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) {s0 : State} {post : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName) (hrun : s0.status = .Running) (hsp : s0.sp = L + 1904#64) (halignL : L &&& 15#64 = 0#64) (halign1808 : (L + 1808#64) &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + len1)) (hx8 : s0.readReg64 .x8 = out) (hlen1_pos : 0 < len1) (hlen1_lt : len1 < 2 ^ 33)
    (hnext : ∀ s1 : State, s1.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 260#64 → s1.status = .Running → s1.sp = L → (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      s1.readReg64 .x0 = 2#64 → s1.readReg64 .x19 = out → s1.readReg64 .x21 = noneCap → s1.readReg64 .x23 = L + 1032#64 → s1.readReg64 .x24 = 1#64 → s1.readReg64 .x26 = 8#64 → s1.readReg64 .x29 = L + 1808#64 → post s1 (step1aPost_loopW L p len1 s0)) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName + 260#64) s0 (step1aPre_loopW L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7) post := by
  let H := Rust.withPanics ext; d0_fetches_1a_q img.base H; dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry; examples_hide_fetches; unfold step1aPre_loopW
  have hcbz : (BitVec.ofNat 64 (1 + len1) == 0#64) = false := by simp only [beq_eq_false_iff_ne]; intro h; have hnat := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat; change 1 + len1 = 0 at hnat; omega
  have hsub1 : BitVec.ofNat 64 (1 + len1) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 len1 := by rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + len1) - 1#64 = BitVec.ofNat 64 len1 := by rw [Nat.add_comm 1 len1, BitVec.ofNat_add]; bv_omega
  (iterate 49 wp_step); apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]); have hnone : noneCap = bv% (2 ^ 64 - 1) := rfl
  refine Eq.ndrec (motive := fun P => post _ P) (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by rw [hnone]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step1aPost_loopW deserSavedAt_loopW; rw [hnone]; simp only [Reg.x29, Reg.x30, Reg.x28, Reg.x27, Reg.x26, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl
private def step2aPre_loopW (L p : BitVec 64) (N : Nat) : SepProp := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (1 + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)
private def step2aPost_loopW (L p : BitVec 64) (N : Nat) : SepProp := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 2#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)
private theorem step_2a_loopW (img : Obj.Image) (ext : String → Option (State → State)) (L p out : BitVec 64) (N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L) (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64) (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_lt : N < 128)
    (hnext : ∀ s' : State, s'.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 → s'.status = .Running → s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 → s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 → post s' (step2aPost_loopW L p N)) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName + 596#64) s (step2aPre_loopW L p N) post := by
  let H := Rust.withPanics ext; d0_fetches_2a_q img.base H; dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry; examples_hide_fetches; unfold step2aPre_loopW
  have hcbz : (BitVec.ofNat 64 (1 + N) == 0#64) = false := by simp only [beq_eq_false_iff_ne]; intro h; have hnat := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat; change 1 + N = 0 at hnat; omega
  have hse := signExtend64_ofNat8_lt_128_loopW hN_lt
  have hbit63 : (((BitVec.ofNat 8 N).signExtend 64).getLsbD 63 == true) = false := (signExtend64_bit63_eq_false_iff_loopW (BitVec.ofNat 8 N)).mpr (by rw [BitVec.toNat_ofNat]; omega)
  have hsub1 : BitVec.ofNat 64 (1 + N) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 N := by rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hsub1' : BitVec.ofNat 64 (1 + N) - 1#64 = BitVec.ofNat 64 N := by rw [Nat.add_comm 1 N, BitVec.ofNat_add]; bv_omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  (iterate 14 wp_step); apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P) (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2aPost_loopW; ac_rfl
private def step2bPre_loopW (L p : BitVec 64) (vlen N : Nat) : SepProp := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128))
private theorem step_2b_pre_loopW (img : Obj.Image) (ext : String → Option (State → State)) (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 348#64) (hrun : s.status = .Running) (hsp : s.sp = L) (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = L + 1032#64) (hx29 : s.readReg64 .x29 = L + 1808#64) (hN_ge : 128 ≤ N) (hVN_lt : vlen + N < 2 ^ 33)
    (hnext : ∀ s' : State, s'.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") → s'.status = .Running →
      s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .lr = (SP2Ext img.base ext).fnAddr recDeserializeName + 540#64 → s'.readReg64 .x0 = L + 1400#64 → s'.readReg64 .x1 = p + 1#64 → s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) → s'.readReg64 .x19 = out → s'.readReg64 .x20 = L + 1016#64 → s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 → post s' (step2bPre_loopW L p vlen N)) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) s (step2bPre_loopW L p vlen N) post := by
  let H := Rust.withPanics ext; d0_fetches_2b_pre_q img.base H; dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry; examples_hide_fetches; unfold step2bPre_loopW
  have hcbz : (BitVec.ofNat 64 (vlen + N) == 0#64) = false := by simp only [beq_eq_false_iff_ne]; intro h; have hnat := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hnat; change vlen + N = 0 at hnat; omega
  have hbit63 : (((BitVec.ofNat 8 (N % 128 + 128)).signExtend 64).getLsbD 63 == true) = true := (signExtend64_bit63_eq_true_iff_loopW (BitVec.ofNat 8 (N % 128 + 128))).mpr (by rw [BitVec.toNat_ofNat]; omega)
  have hhi10 : (10#64).ult (BitVec.ofNat 64 (vlen + N)) = true := by simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega), decide_eq_true_eq]; omega
  have hule10 : (BitVec.ofNat 64 (vlen + N)).ule 10#64 = false := by simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega), decide_eq_false_iff_not]; omega
  (iterate 10 wp_step); apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P) (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2bPre_loopW; ac_rfl
private def step2bPostPre_loopW (L p : BitVec 64) (vlen N : Nat) : SepProp := ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗ ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N))
private def step2bPostPost_loopW (L p : BitVec 64) (vlen N : Nat) : SepProp := ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗ ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N)
private theorem step_2b_post_loopW (img : Obj.Image) (ext : String → Option (State → State)) (L p out : BitVec 64) (vlen N : Nat) {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 540#64) (hrun : s.status = .Running) (hsp : s.sp = L) (halignL : L &&& 15#64 = 0#64) (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = L + 1016#64) (hx23 : s.readReg64 .x23 = L + 1032#64) (hx29 : s.readReg64 .x29 = L + 1808#64) (hVN_lt : vlen + N < 2 ^ 33)
    (hnext : ∀ s' : State, s'.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 → s'.status = .Running → s'.sp = L → (s'.trace = s.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s) → s'.readReg64 .x19 = out → s'.readReg64 .x20 = 0#64 → s'.readReg64 .x23 = L + 1032#64 → s'.readReg64 .x29 = L + 1808#64 → post s' (step2bPostPost_loopW L p vlen N)) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName + 596#64) s (step2bPostPre_loopW L p vlen N) post := by
  let H := Rust.withPanics ext; d0_fetches_2b_post_q img.base H; dsimp only [SP2Ext, contractProg] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry; examples_hide_fetches; unfold step2bPostPre_loopW
  have hsub2 : BitVec.ofNat 64 (vlen + N) - BitVec.ofNat 64 vlen = BitVec.ofNat 64 N := by rw [BitVec.ofNat_add]; bv_omega
  have hult2 : (BitVec.ofNat 64 (vlen + N)).ult (BitVec.ofNat 64 vlen) = false := by simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vlen + N < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show vlen < 2 ^ 64 by omega), decide_eq_false_iff_not]; omega
  have hult_self : (BitVec.ofNat 64 N).ult (BitVec.ofNat 64 N) = false := by simp [BitVec.ult]
  have hsub_self : BitVec.ofNat 64 N - BitVec.ofNat 64 N = 0#64 := by bv_omega
  (iterate 14 wp_step); apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine Eq.ndrec (motive := fun P => post _ P) (hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])) ?_
  unfold step2bPostPost_loopW; ac_rfl

private theorem memRegion_succ8_loopW (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) = (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

private theorem memRegion_1064_336_cells_loopW (L : BitVec 64) :
    ((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336 =
      ∃∗ c22 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c19 : BitVec 64, ∃∗ c18 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c15 : BitVec 64,
      ∃∗ c14 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c12 : BitVec 64, ∃∗ c11 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c6 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c3 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c1 : BitVec 64,
        ssUninitCells_loopW L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
        memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 := by
  rw [memRegion_split (L + 1064#64) 144 192 (by decide), memRegion_split (L + 1064#64 + 144#64) 96 96 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64) 8 88 (by decide), memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide), memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs => arg 2; arg 1; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (L + 1304#64), ProofLib.memRegion_eight (L + 1352#64)]
  conv_lhs => arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold ssUninitCells_loopW; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem memRegion_1904_split_loopW (L p : BitVec 64) :
    memRegion L 1904 ∗ (p ↦₈ 0x0a#8) =
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        step1aPre_loopW L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 := by
  rw [memRegion_split L 8 1896 (by decide), memRegion_split (L + 8#64) 1008 888 (by decide),
    memRegion_split (L + 8#64 + 1008#64) 48 840 (by decide), memRegion_split (L + 8#64 + 1008#64 + 48#64) 336 504 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64) 368 136 (by decide), memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64) 8 128 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64 + 8#64) 32 96 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs => arg 1; arg 1; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp]
  conv_lhs => arg 1; arg 2; arg 2; arg 1; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs => arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs => arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold step1aPre_loopW; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem stackAt_recDeserialize_split_loopW (sp0 : BitVec 64) :
    stackAt sp0 recDeserializeStack = stackAt (deserSpL sp0) deserCalleeStack ∗ memRegion (deserSpL sp0) 1904 := by
  change memRegion (sp0 - 65536#64) 65536 = memRegion (sp0 - 0x770#64 - 63632#64) 63632 ∗ memRegion (sp0 - 0x770#64) 1904
  rw [memRegion_split (sp0 - 65536#64) 63632 1904 (by decide)]
  have h1 : sp0 - 65536#64 = sp0 - 0x770#64 - 63632#64 := by bv_omega
  have h2 : sp0 - 65536#64 + 63632#64 = sp0 - 0x770#64 := by bv_omega
  rw [h2, h1]

private theorem memRegion_0_1016_intro_loopW (L : BitVec 64) : (L ↦₆₄ 0#64) ∗ memRegion (L + 8#64) 1008 ⊢ memRegion L 0x3f8 := by
  rw [show (0x3f8 : Nat) = 1016 by decide, memRegion_split L 8 1008 (by decide)]; exact sepConj_mono_left (pointsTo64_entails_memRegion L 0#64)

private def deserFixedLocalsG_loopW (A : RustAlloc) (L : BitVec 64) : SepProp :=
  memRegion L 0x3f8 ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗ prostSSGAt A (L + 0x420#64) SSG.empty ∗ memRegion (L + 0x6f0#64) 0x20

private theorem step1b_post_entails_loopW (A : RustAlloc) (L p : BitVec 64) (len1 : Nat) (s0 : State) (hL : L = deserSpL s0.sp) :
    ssRawCells_loopW L ∗ memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 ∗ deserSavedAt_loopW L s0 ∗ (L ↦₆₄ 0#64) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ⊢
    ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopW A L ∗ deserSaved s0 := by
  have hss := prostSSGAt_empty_intro_loopW A L; have hm0 := memRegion_0_1016_intro_loopW L
  have hds : deserSavedAt_loopW L s0 = deserSaved s0 := hL ▸ deserSavedAt_eq_loopW s0
  unfold deserFixedLocalsG_loopW; rw [hds, show (0x408#64 : BitVec 64) = 1032#64 from rfl, show (0x410#64 : BitVec 64) = 1040#64 from rfl,
    show (0x418#64 : BitVec 64) = 1048#64 from rfl, show (0x6f0#64 : BitVec 64) = 1776#64 from rfl, show (0x20 : Nat) = 32 from rfl]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans (sepConj_mono (sepConj_mono hss hm0)
    (Entails.refl (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗ memRegion (L + 1776#64) 32 ∗ deserSaved s0))) (Entails.of_eq (by ac_rfl)))

private theorem scratch24_368_fold_loopW (L v w : BitVec 64) :
    ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗ ((L + 1408#64) ↦₆₄ v) ∗ ((L + 1416#64) ↦₆₄ w) ∗ memRegion (L + 1424#64) 344 ⊢ memRegion (L + 1400#64) 368 := by
  have h0 : ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) = ((L + 1400#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32_loopW (L + 1400#64)).symm; rw [show L + 1400#64 + 4#64 = L + 1404#64 by bv_omega] at hs; exact hs
  rw [← sepConj_assoc, h0, memRegion_split (L + 1400#64) 24 344 (by decide), memRegion_split (L + 1400#64) 8 16 (by decide), memRegion_split (L + 1400#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion (L + 1400#64) 0#64)
    (sepConj_mono (pointsTo64_entails_memRegion (L + 1408#64) v) (pointsTo64_entails_memRegion (L + 1416#64) w))) (Entails.refl _))

private theorem deserLocalsG_of_2a_loopW (A : RustAlloc) (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 ((recFieldsQ r).flatMap GenFieldQ.enc).length) ++ (recFieldsQ r).flatMap GenFieldQ.enc)
    (hN : ((recFieldsQ r).flatMap GenFieldQ.enc).length < 128) :
    let body := (recFieldsQ r).flatMap GenFieldQ.enc
    step2aPost_loopW L p body.length ∗ ((p + 1#64 + 1#64) ↦ₛ body) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopW A L = deserLocalsGA A L p (encodeRecord r) body SSG.empty := by
  intro body
  have hpfx : encodeRecord r = 0x0a#8 :: BitVec.ofNat 8 body.length :: body := by rw [heq, encodeKey_1_ld_loopW, encodeVarint_of_lt_128_loopW hN]; rfl
  have hsub : (encodeRecord r).length - body.length = 2 := by rw [hpfx, List.length_cons, List.length_cons]; omega
  have hbytes : (p ↦ₛ encodeRecord r) = (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 body.length) ∗ ((p + 1#64 + 1#64) ↦ₛ body) := by rw [hpfx, pointsToBytes_cons, pointsToBytes_cons]
  unfold deserLocalsGA Prost.sliceCursorAfter deserFixedLocalsG_loopW step2aPost_loopW
  rw [hsub, hbytes, show (0x3f8#64 : BitVec 64) = 1016#64 from rfl, show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (BitVec.ofNat 64 2 : BitVec 64) = 2#64 from rfl, show (0x578#64 : BitVec 64) = 1400#64 from rfl, show (0x170 : Nat) = 368 from rfl, show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]; ac_rfl

private theorem step2bPostPost_entails_loopW (L p : BitVec 64) (vlen N : Nat) :
    step2bPostPost_loopW L p vlen N ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) := by
  unfold step2bPostPost_loopW
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left (Q := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
    ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N)) (scratch24_368_fold_loopW L (BitVec.ofNat 64 N) (BitVec.ofNat 64 vlen)))

private theorem deserLocalsG_of_2b_loopW (A : RustAlloc) (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 ((recFieldsQ r).flatMap GenFieldQ.enc).length) ++ (recFieldsQ r).flatMap GenFieldQ.enc) :
    let body := (recFieldsQ r).flatMap GenFieldQ.enc; let vlen := (encodeVarint (BitVec.ofNat 64 body.length)).length
    (step2bPostPost_loopW L p vlen body.length ∗ memRegion (L + 1424#64) 344) ∗ ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) ∗ (p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopW A L ⊢
    deserLocalsGA A L p (encodeRecord r) body SSG.empty := by
  intro body vlen; refine Entails.trans (sepConj_mono_left (step2bPostPost_entails_loopW L p vlen body.length)) ?_
  have hpfx : encodeRecord r = 0x0a#8 :: (encodeVarint (BitVec.ofNat 64 body.length) ++ body) := by rw [heq, encodeKey_1_ld_loopW]; rfl
  have hsub : (encodeRecord r).length - body.length = 1 + vlen := by rw [hpfx, List.length_cons, List.length_append]; omega
  have hptr : p + 1#64 + BitVec.ofNat 64 vlen = p + BitVec.ofNat 64 (1 + vlen) := by rw [BitVec.ofNat_add, BitVec.add_assoc]
  have hbytes : (p ↦ₛ encodeRecord r) = (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) := by rw [hpfx, pointsToBytes_cons]
  unfold deserLocalsGA Prost.sliceCursorAfter deserFixedLocalsG_loopW
  rw [hsub, hptr, hbytes, show (0x3f8#64 : BitVec 64) = 1016#64 from rfl, show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl, show (0x170 : Nat) = 368 from rfl, show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]
  exact Entails.of_eq (by ac_rfl)

private theorem stackAt_deserCallee_split_varint_loopW (L : BitVec 64) :
    stackAt L deserCalleeStack = stackAt L Prost.X.decodeVarintSliceStackW ∗ memRegion (L - 63632#64) 38976 := by
  change memRegion (L - 63632#64) 63632 = memRegion (L - 24656#64) 24656 ∗ memRegion (L - 63632#64) 38976
  rw [memRegion_split (L - 63632#64) 38976 24656 (by decide), show L - 63632#64 + 38976#64 = L - 24656#64 by bv_omega, sepConj_comm]

private theorem allocFailedIn_of_trace_eq_loopW {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by unfold allocFailedIn at h ⊢; rwa [htr] at h
private theorem allowPanic_frame_trace_loopW {s0 sm sf : State} {F R : SepProp} (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) : sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq_loopW htr) h

private theorem step_1_combined_loopW (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = x.p) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length) (hx8 : s0.readReg64 .x8 = x.out)
    (heq : encodeRecord x.r = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 ((recFieldsQ x.r).flatMap GenFieldQ.enc).length) ++ (recFieldsQ x.r).flatMap GenFieldQ.enc)
    (hrec_lt : (encodeRecord x.r).length < 2 ^ 33) (hal : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s0.sp recDeserializeStack ∗ R)
    (hL : (SP2Ext img.base ext).CodeLoaded s0.mem) :
    let L := deserSpL s0.sp; let body := (recFieldsQ x.r).flatMap GenFieldQ.enc; let rest1 := encodeVarint (BitVec.ofNat 64 body.length) ++ body
    ∃ s2, Steps (SP2Ext img.base ext) s0 s2 ∧ s2.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 348#64 ∧
      s2.status = .Running ∧ s2.sp = L ∧ (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
      s2.readReg64 .x19 = x.out ∧ s2.readReg64 .x23 = L + 1032#64 ∧ s2.readReg64 .x29 = L + 1808#64 ∧
      (s2.mem ⊨ (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗
          ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗ (x.p ↦₈ 0x0a#8) ∗
          memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopW A L ∗ deserSaved s0) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
  intro L body rest1
  have hsp0 : s0.sp = L + 1904#64 := by change s0.sp = s0.sp - 0x770#64 + 1904#64; bv_omega
  obtain ⟨halignL, halign1808⟩ := sp_sub_1904_aligned_loopW (decide_eq_true_iff.mp hal)
  have hbs_cons : encodeRecord x.r = 0x0a#8 :: rest1 := by rw [heq, encodeKey_1_ld_loopW]; rfl
  have hv_pos := encodeVarint_length_pos_loopW (BitVec.ofNat 64 body.length)
  have hlen1_pos : 0 < rest1.length := by simp only [rest1, List.length_append]; omega
  have hlen1_lt : rest1.length < 2 ^ 33 := by rw [hbs_cons, List.length_cons] at hrec_lt; omega
  have hx1' : s0.readReg64 .x1 = BitVec.ofNat 64 (1 + rest1.length) := by rw [hx1, hbs_cons, List.length_cons, Nat.add_comm]
  have hm0a : s0.mem ⊨ (memRegion L 1904 ∗ (x.p ↦₈ 0x0a#8)) ∗ (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R) := by
    rw [hbs_cons, pointsToBytes_cons, stackAt_recDeserialize_split_loopW s0.sp] at hm0; dsimp only [L]; convert hm0 using 1; ac_rfl
  rw [memRegion_1904_split_loopW L x.p] at hm0a; simp only [sepExists_sepConj_left, satisfies_sepExists] at hm0a
  rcases hm0a with ⟨w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1, w0, u7, u6, u5, u4, u3, u2, u1, u0, hm0b⟩
  have hm0c : s0.mem ⊨ step1aPre_loopW L x.p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
      (memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗ memRegion (L + 1400#64) 368 ∗
        memRegion (L + 1776#64) 32 ∗ (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by convert hm0b using 1; ac_rfl
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, rfl, hsp1, htr1, hx0_1, hx19_1, hx21_1, hx23_1, hx24_1, hx26_1, hx29_1⟩ | ⟨_, _hoom⟩⟩ :=
    (step_1a_loopW img ext L x.p x.out rest1.length w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7
      (post := fun s' P => P = step1aPost_loopW L x.p rest1.length s0 ∧ s'.sp = L ∧ (s'.trace = s0.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s0) ∧
        s'.readReg64 .x0 = 2#64 ∧ s'.readReg64 .x19 = x.out ∧ s'.readReg64 .x21 = noneCap ∧
        s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x24 = 1#64 ∧ s'.readReg64 .x26 = 8#64 ∧ s'.readReg64 .x29 = L + 1808#64)
      hpc hrun hsp0 halignL halign1808 hx0 hx1' hx8 hlen1_pos hlen1_lt
      (fun s' _ _ hsp' htr' hx0' hx19' hx21' hx23' hx24' hx26' hx29' => ⟨rfl, hsp', htr', hx0', hx19', hx21', hx23', hx24', hx26', hx29'⟩)).elim hm0c hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hm1a : s1.mem ⊨ (((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336) ∗
      (deserSavedAt_loopW L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗
        ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold step1aPost_loopW at hm1; convert hm1 using 1; ac_rfl
  rw [memRegion_1064_336_cells_loopW L] at hm1a; simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1a
  rcases hm1a with ⟨c22, c21, c20, c19, c18, c17, c16, c15, c14, c13, c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, hm1b⟩
  have hm1c : s1.mem ⊨ ssUninitCells_loopW L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
      ((memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 ∗
        deserSavedAt_loopW L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 rest1.length) ∗
        ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
        (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32) ∗
        (((x.p + 1#64) ↦ₛ rest1) ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ R)) := by
    unfold ssUninitCells_loopW at hm1b ⊢; convert hm1b using 1; ac_rfl
  obtain ⟨s2, hst2, ⟨hpc2, hrun2, P2, hm2, rfl, hsp2, htr2, hx19_2, hx23_2, hx29_2⟩ | ⟨_, _hoom⟩⟩ :=
    (step_1b_loopW img ext L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22
      (post := fun s' P => P = ssRawCells_loopW L ∧ s'.sp = L ∧ (s'.trace = s1.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s1) ∧
        s'.readReg64 .x19 = s1.readReg64 .x19 ∧ s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = s1.readReg64 .x29)
      hpc1 hrun1 hsp1 halignL hx0_1 hx21_1 hx23_1 hx24_1 hx26_1
      (fun s' _ _ hsp' htr' hx19' hx23' hx29' => ⟨rfl, hsp', htr', hx19', hx23', hx29'⟩)).elim hm1c (hst1.codeLoaded hL)
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s2, hst1.trans hst2, hpc2, hrun2, hsp2, ⟨htr2.1.trans htr1.1, htr2.2.trans htr1.2⟩, hx19_2.trans hx19_1, hx23_2, hx29_2.trans hx29_1, ?_⟩
  rw [← sepConj_assoc] at hm2
  exact Satisfies.mono (sepConj_mono_left (step1b_post_entails_loopW A L x.p rest1.length s0 rfl)) hm2

private theorem deserializeGenSpecAtA_A0 (img : Obj.Image) : deserializeGenSpecAtA A0 img = deserializeGenSpecAt img := by
  have hp : A0.pool = emp := rfl; unfold deserializeGenSpecAtA deserializeGenSpecAt; simp only [hp, emp_sepConj]
private theorem deserializeQSpecAtWA_A0 (img : Obj.Image) : deserializeQSpecAtWA A0 img = deserializeQSpecAtW img := by
  have hp : A0.pool = emp := rfl; unfold deserializeQSpecAtWA deserializeQSpecAtW; rw [deserializeGenSpecAtA_A0]; simp only [hp, emp_sepConj]
private theorem deserOutRawQA_A0 : deserOutRawQA A0 = deserOutRawQ := by
  funext x s0 sf; have hp : A0.pool = emp := rfl; unfold deserOutRawQA deserOutRawQ; simp only [deserOutRecordQA_A0, hp, emp_sepConj]
private theorem deserializeQExactSpecAtWA_A0 (img : Obj.Image) : deserializeQExactSpecAtWA A0 img = deserializeQExactSpecAtW img := by
  unfold deserializeQExactSpecAtWA deserializeQExactSpecAtW; rw [deserializeQSpecAtWA_A0, deserOutRawQA_A0]
private theorem DeserLoopQAtWA_A0 (img : Obj.Image) (ext : String → Option (State → State)) : DeserLoopQAtWA img A0 ext = DeserLoopQAtW img ext := by
  funext x R s0 k s; have hp : A0.pool = emp := rfl; unfold DeserLoopQAtWA DeserLoopQAtW; simp only [deserLocalsQA_A0, hp, emp_sepConj]
private theorem DeserRetQAtWA_A0 : DeserRetQAtWA A0 = DeserRetQAtW := by
  funext x R s0 sf; unfold DeserRetQAtWA DeserRetQAtW; rw [deserOutRawQA_A0]

set_option maxHeartbeats 1600000 in
theorem deserLoopEntryQ_ok_of_fieldsA (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hC : DeserializeCalleesAtWA img A ext) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (deserializeQSpecAtWA A img).pre x s0 ∗ R) (hal : s0.spAligned = true)
    (heq : DeserializeScopeP_Q NonEmptyV1Q x.r → encodeRecord x.r = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 ((recFieldsQ x.r).flatMap GenFieldQ.enc).length) ++ (recFieldsQ x.r).flatMap GenFieldQ.enc)
    (hlt : DeserializeScopeP_Q NonEmptyV1Q x.r → (encodeRecord x.r).length < 2 ^ 33) :
    DeserStepQAtWA img A ext x R s0 s0 (DeserLoopQAtWA img A ext x R s0 0) := by
  intro hL0; dsimp only [deserializeQSpecAtWA] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hr, hF0, hsym0⟩, hm0⟩
  have hm0' : s0.mem ⊨ (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ stackAt s0.sp recDeserializeStack ∗ (A.pool ∗ R) := by convert hm0 using 1; ac_rfl
  have heq' := heq hr; have hrec_lt := hlt hr; obtain ⟨halignL, _halign1808⟩ := sp_sub_1904_aligned_loopW (decide_eq_true_iff.mp hal)
  obtain ⟨s2, hst2, hpc2, hrun2, hsp2, htr2, hx19_2, hx23_2, hx29_2, hm2⟩ := step_1_combined_loopW img A ext x (A.pool ∗ R) s0 hpc hrun hx0 hx1 hx8 heq' hrec_lt hal hm0' hL0
  set L := deserSpL s0.sp; set body := (recFieldsQ x.r).flatMap GenFieldQ.enc; set N := body.length; set rest1 := encodeVarint (BitVec.ofNat 64 N) ++ body
  have hbs_cons : encodeRecord x.r = 0x0a#8 :: rest1 := by rw [heq', encodeKey_1_ld_loopW]; rfl
  have hrest1_lt : rest1.length < 2 ^ 33 := by rw [hbs_cons, List.length_cons] at hrec_lt; omega
  by_cases hN : N < 128
  · have hr1 : rest1 = BitVec.ofNat 8 N :: body := by simp only [rest1, encodeVarint_of_lt_128_loopW hN, List.singleton_append]
    have hlen1 : rest1.length = 1 + N := by rw [hr1, List.length_cons, Nat.add_comm]
    have hm2a : s2.mem ⊨ step2aPre_loopW L x.p N ∗ (((x.p + 1#64 + 1#64) ↦ₛ body) ∗ (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗
        deserFixedLocalsG_loopW A L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ (A.pool ∗ R)) := by
      rw [hlen1, hr1, pointsToBytes_cons] at hm2; unfold step2aPre_loopW; convert hm2 using 1; ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl, hsp3, htr3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2a_loopW img ext L x.p x.out N (post := fun s' P => P = step2aPost_loopW L x.p N ∧ s'.sp = L ∧ (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧
          s'.readReg64 .x19 = x.out ∧ s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' => ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim hm2a (hst2.codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    refine ⟨s3, hst2.trans hst3, Or.inl ⟨by unfold deserPCAtX; rw [hpc3], hrun3, ⟨htr3.1.trans htr2.1, htr3.2.trans htr2.2⟩, by rw [(hst2.trans hst3).symtab_eq, hsym0],
      (hst2.trans hst3).frozenLoaded hF0, hsp3, by rw [State.spAligned, hsp3]; exact decide_eq_true halignL, hx29_3, hx19_3, hx20_3, hx23_3, ?_⟩⟩
    have hloc := deserLocalsG_of_2a_loopW A L x.p x.r heq' hN; have hdrop : (((recFieldsQ x.r).drop 0).flatMap GenFieldQ.enc) = body := by rw [List.drop_zero]
    have hss0 : ssgqAfter x.r 0 = ⟨SSG.empty, ExtraGQ.empty⟩ := rfl
    change s3.mem ⊨ deserLocalsQA A L x.p (encodeRecord x.r) (((recFieldsQ x.r).drop 0).flatMap GenFieldQ.enc) (ssgqAfter x.r 0) ∗ memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
    rw [hdrop, hss0, deserLocalsQA_base, ← hloc]; convert hm3 using 1; ac_rfl
  · have hN_ge : 128 ≤ N := by omega
    set vlen := (encodeVarint (BitVec.ofNat 64 N)).length; set vtail := encodeVarintAux 9 (BitVec.ofNat 64 N >>> 7)
    have hlen1 : rest1.length = vlen + N := List.length_append
    have hVN_lt : vlen + N < 2 ^ 33 := by rw [← hlen1]; exact hrest1_lt
    have hN_lt : N < 2 ^ 33 := by omega
    have hr1 : rest1 = BitVec.ofNat 8 (N % 128 + 128) :: (vtail ++ body) := by simp only [rest1, vtail, encodeVarint_cons_of_ge_128_loopW hN_ge hN_lt, List.cons_append]
    have hm2_bytes : ((x.p + 1#64) ↦ₛ rest1) = ((x.p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128)) ∗ ((x.p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) := by rw [hr1, pointsToBytes_cons]
    have hm2c : s2.mem ⊨ step2bPre_loopW L x.p vlen N ∗ (((x.p + 1#64 + 1#64) ↦ₛ (vtail ++ body)) ∗ (x.p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗
        deserFixedLocalsG_loopW A L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ (A.pool ∗ R)) := by
      rw [hlen1, hm2_bytes] at hm2; unfold step2bPre_loopW; convert hm2 using 1; ac_rfl
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, rfl, hsp3, htr3, hlr_3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx23_3, hx29_3⟩ | ⟨_, _hoom⟩⟩ :=
      (step_2b_pre_loopW img ext L x.p x.out vlen N (post := fun s' P => P = step2bPre_loopW L x.p vlen N ∧ s'.sp = L ∧ (s'.trace = s2.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s2) ∧
          s'.readReg64 .lr = (SP2Ext img.base ext).fnAddr recDeserializeName + 540#64 ∧ s'.readReg64 .x0 = L + 1400#64 ∧ s'.readReg64 .x1 = x.p + 1#64 ∧
          s'.readReg64 .x2 = BitVec.ofNat 64 (vlen + N) ∧ s'.readReg64 .x19 = x.out ∧ s'.readReg64 .x20 = L + 1016#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
        hpc2 hrun2 hsp2 hx19_2 hx23_2 hx29_2 hN_ge hVN_lt
        (fun s' _ _ hsp' htr' hlr' hx0' hx1' hx2' hx19' hx20' hx23' hx29' => ⟨rfl, hsp', htr', hlr', hx0', hx1', hx2', hx19', hx20', hx23', hx29'⟩)).elim hm2c (hst2.codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hpc3' : s3.pc = (SP2Ext img.base ext).fnAddr Prost.decodeVarintSliceName := by rw [hpc3, decodeVarintSlice_fnAddr_eq_deser_at_ext]
    have hal3 : s3.spAligned = true := by rw [State.spAligned, hsp3]; exact decide_eq_true halignL
    have hx2_3_nat : (s3.readReg64 .x2).toNat = rest1.length := by rw [hx2_3, hlen1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpre_slice : Prost.VarintSlicePre rest1 := Or.inl (by omega)
    let gvar : Prost.DecodeVarintSliceGhost := ⟨L + 1400#64, x.p + 1#64, rest1⟩
    let F_call : SepProp := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (x.p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗
      memRegion (L - 63632#64) 38976 ∗ memRegion (L + 1424#64) 344 ∗ (x.p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopW A L ∗ deserSaved s0 ∗ memRegion x.out 368
    have hm3_call : s3.mem ⊨ ((Prost.X.decodeVarintSliceSpecW A).inImage img).pre gvar s3 ∗ (F_call ∗ R) := by
      unfold Spec.inImage Prost.X.decodeVarintSliceSpecW; dsimp only [gvar]; simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨(hst2.trans hst3).frozenLoaded hF0, (hst2.trans hst3).symtab_eq.trans hsym0⟩, ⟨hx0_3, hx1_3, hx2_3_nat, by omega, hpre_slice⟩, ?_⟩
      unfold step2bPre_loopW at hm3; rw [memRegion_split (L + 1400#64) 24 344 (by decide), stackAt_deserCallee_split_varint_loopW L, show L + 1400#64 + 24#64 = L + 1424#64 by bv_omega] at hm3
      dsimp only [F_call]; rw [hsp3, hm2_bytes]; convert hm3 using 1; ac_rfl
    obtain ⟨s4, hst4, hpost4, -⟩ := hC.1.no_fault_before_outcome gvar (F_call ∗ R) s3 hpc3' hrun3 hm3_call hal3 ((hst2.trans hst3).codeLoaded hL0)
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
      rw [hdec] at hm4; dsimp only [Prost.varintSliceResultAt] at hm4; rw [sepConj_assoc, satisfies_pure_sepConj] at hm4; rcases hm4 with ⟨htr4, hm4⟩
      have hm4a : s4.mem ⊨ step2bPostPre_loopW L x.p vlen N ∗ (memRegion (L + 1424#64) 344 ∗ ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗
          deserFixedLocalsG_loopW A L ∗ deserSaved s0 ∗ memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ (A.pool ∗ R)) := by
        dsimp only [F_call] at hm4; unfold step2bPostPre_loopW
        rw [hsp3, pointsTo64_zero_split32_loopW (L + 1400#64), hsub1] at hm4; rw [stackAt_deserCallee_split_varint_loopW L]
        rw [show L + 1400#64 + 4#64 = L + 1404#64 by bv_omega, show L + 1400#64 + 8#64 = L + 1408#64 by bv_omega, show L + 1400#64 + 16#64 = L + 1416#64 by bv_omega] at hm4
        convert hm4 using 1; ac_rfl
      obtain ⟨s5, hst5, ⟨hpc5, hrun5, P5, hm5, rfl, hsp5, htr5, hx19_5, hx20_5, hx23_5, hx29_5⟩ | ⟨_, _hoom⟩⟩ :=
        (step_2b_post_loopW img ext L x.p x.out vlen N (post := fun s' P => P = step2bPostPost_loopW L x.p vlen N ∧ s'.sp = L ∧ (s'.trace = s4.trace ∧ calleeSavedVRegs s' = calleeSavedVRegs s4) ∧
            s'.readReg64 .x19 = x.out ∧ s'.readReg64 .x20 = 0#64 ∧ s'.readReg64 .x23 = L + 1032#64 ∧ s'.readReg64 .x29 = L + 1808#64)
          hpc4' hrun4 hsp4' halignL hx19_4 hx20_4 hx23_4 hx29_4 hVN_lt
          (fun s' _ _ hsp' htr' hx19' hx20' hx23' hx29' => ⟨rfl, hsp', htr', hx19', hx20', hx23', hx29'⟩)).elim hm4a ((hst2.trans (hst3.trans hst4)).codeLoaded hL0)
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      refine ⟨s5, (hst2.trans (hst3.trans hst4)).trans hst5, Or.inl ⟨by unfold deserPCAtX; rw [hpc5], hrun5, ⟨(htr5.1.trans htr4).trans (htr3.1.trans htr2.1), htr5.2.trans hv4⟩,
        by rw [((hst2.trans (hst3.trans hst4)).trans hst5).symtab_eq, hsym0], ((hst2.trans (hst3.trans hst4)).trans hst5).frozenLoaded hF0,
        hsp5, by rw [State.spAligned, hsp5]; exact decide_eq_true halignL, hx29_5, hx19_5, hx20_5, hx23_5, ?_⟩⟩
      have hloc := deserLocalsG_of_2b_loopW A L x.p x.r heq'; have hdrop : (((recFieldsQ x.r).drop 0).flatMap GenFieldQ.enc) = body := by rw [List.drop_zero]
      have hss0 : ssgqAfter x.r 0 = ⟨SSG.empty, ExtraGQ.empty⟩ := rfl
      change s5.mem ⊨ deserLocalsQA A L x.p (encodeRecord x.r) (((recFieldsQ x.r).drop 0).flatMap GenFieldQ.enc) (ssgqAfter x.r 0) ∗ memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
      rw [hdrop, hss0, deserLocalsQA_base]
      have hm5a : s5.mem ⊨ ((step2bPostPost_loopW L x.p vlen N ∗ memRegion (L + 1424#64) 344) ∗ ((x.p + 1#64) ↦ₛ rest1) ∗ (x.p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopW A L) ∗
          (memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R) := by convert hm5 using 1; ac_rfl
      exact Satisfies.mono (sepConj_mono_left hloc) hm5a
    · refine ⟨s4, (hst2.trans hst3).trans hst4, Or.inr ⟨hpan4, ?_⟩⟩
      dsimp only [deserializeQSpecAtWA, allocPanic]; unfold Spec.inImage Prost.X.decodeVarintSliceSpecW at hm4_pan; dsimp only at hm4_pan
      have hm4_pan' : s4.mem ⊨ ((⌜allocFailedIn s3 s4 ∧ s3.trace <+: s4.trace⌝ ∗ anyHeap) ∗ F_call) ∗ R := by convert hm4_pan using 1; ac_rfl
      exact allowPanic_frame_trace_loopW (htr3.1.trans htr2.1) hm4_pan'
    · exact False.elim (not_satisfies_false_sepConj hm4_ex)
    · exact False.elim (not_satisfies_false_sepConj hm4_oom)

theorem deserLoopEntryQ_ok_of_fields (img : Obj.Image) (ext : String → Option (State → State))
    (hC : DeserializeCalleesAtW img ext) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (deserializeQSpecAtW img).pre x s0 ∗ R) (hal : s0.spAligned = true)
    (heq : DeserializeScopeP_Q NonEmptyV1Q x.r → encodeRecord x.r = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 ((recFieldsQ x.r).flatMap GenFieldQ.enc).length) ++ (recFieldsQ x.r).flatMap GenFieldQ.enc)
    (hlt : DeserializeScopeP_Q NonEmptyV1Q x.r → (encodeRecord x.r).length < 2 ^ 33) :
    DeserStepQAtW img ext x R s0 s0 (DeserLoopQAtW img ext x R s0 0) := by
  unfold DeserStepQAtW; rw [← deserializeQSpecAtWA_A0, ← DeserLoopQAtWA_A0]
  exact deserLoopEntryQ_ok_of_fieldsA img A0 ext hC x R s0 hpc hrun (by rwa [deserializeQSpecAtWA_A0]) hal heq hlt

theorem deserLoopEntryQ_ok_atWA (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hC : DeserializeCalleesAtWA img A ext) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (deserializeQSpecAtWA A img).pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStepQAtWA img A ext x R s0 s0 (DeserLoopQAtWA img A ext x R s0 0) :=
  deserLoopEntryQ_ok_of_fieldsA img A ext hC x R s0 hpc hrun hpre hal (encodeRecord_eq_recFieldsQ x.r) encodeRecord_length_ltQ

theorem deserLoopEntryQ_ok_atW (img : Obj.Image) (ext : String → Option (State → State))
    (hC : DeserializeCalleesAtW img ext) (x : DeserializeGenGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (deserializeQSpecAtW img).pre x s0 ∗ R) (hal : s0.spAligned = true) :
    DeserStepQAtW img ext x R s0 s0 (DeserLoopQAtW img ext x R s0 0) :=
  deserLoopEntryQ_ok_of_fields img ext hC x R s0 hpc hrun hpre hal (encodeRecord_eq_recFieldsQ x.r) encodeRecord_length_ltQ

/-! ## Loop iteration (`deserLoopIterQ_ok_atW`) -/

def keyByte_diterQ (fl : GenFieldQ) : BitVec 8 := BitVec.ofNat 8 (fl.tag * 8 + if fl.wt = .varint then 0 else 2)
theorem enc_eq_keyByte_cons_diterQ (fl : GenFieldQ) : fl.enc = keyByte_diterQ fl :: fl.payload := by rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl
theorem drop_flatMap_enc_diterQ {r : SessionRecord (List (BitVec 8))} {k : Nat} (hk : k < (recFieldsQ r).length) :
    ((recFieldsQ r).drop k).flatMap GenFieldQ.enc = (recFieldsQ r)[k].enc ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc := by rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]
theorem ssgqAfter_succ_diterQ {r : SessionRecord (List (BitVec 8))} {k : Nat} (hk : k < (recFieldsQ r).length) :
    ssgqAfter r (k + 1) = (ssgqAfter r k).apply (recFieldsQ r)[k] := by simp only [ssgqAfter, List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
def preBytes_diterQ (r : SessionRecord (List (BitVec 8))) (k : Nat) : List (BitVec 8) :=
  encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 ((recFieldsQ r).flatMap GenFieldQ.enc).length) ++ ((recFieldsQ r).take k).flatMap GenFieldQ.enc
def curPtr_diterQ (p : BitVec 64) (r : SessionRecord (List (BitVec 8))) (k : Nat) : BitVec 64 := p + BitVec.ofNat 64 (preBytes_diterQ r k).length
theorem encodeRecord_eq_preBytes_append_diterQ {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    encodeRecord r = preBytes_diterQ r k ++ ((recFieldsQ r).drop k).flatMap GenFieldQ.enc := by
  have hs : (recFieldsQ r).flatMap GenFieldQ.enc = ((recFieldsQ r).take k).flatMap GenFieldQ.enc ++ ((recFieldsQ r).drop k).flatMap GenFieldQ.enc := by rw [← List.flatMap_append, List.take_append_drop]
  rw [encodeRecord_eq_recFieldsQ r hr, preBytes_diterQ, List.append_assoc, List.append_assoc, ← hs, ← List.append_assoc]
theorem rem_length_lt_diterQ {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    (((recFieldsQ r).drop k).flatMap GenFieldQ.enc).length < 2 ^ 33 := by have h1 := encodeRecord_length_ltQ hr; rw [encodeRecord_eq_preBytes_append_diterQ hr k, List.length_append] at h1; omega
theorem payload_rest_length_lt_diterQ {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc).length < 2 ^ 33 := by
  have h := rem_length_lt_diterQ hr k; rw [drop_flatMap_enc_diterQ hk, enc_eq_keyByte_cons_diterQ, List.cons_append, List.length_cons] at h; omega
theorem encodeRecord_sub_rem_length_diterQ {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    (encodeRecord r).length - (((recFieldsQ r).drop k).flatMap GenFieldQ.enc).length = (preBytes_diterQ r k).length := by rw [encodeRecord_eq_preBytes_append_diterQ hr k, List.length_append]; omega

theorem sliceCursorAfter_split_key_diterQ (L p : BitVec 64) {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r) (((recFieldsQ r).drop k).flatMap GenFieldQ.enc) =
      ((L + 0x3f8#64) ↦₆₄ curPtr_diterQ p r k) ∗ ((L + 0x400#64) ↦₆₄ BitVec.ofNat 64 (((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc).length + 1)) ∗
        (curPtr_diterQ p r k ↦₈ keyByte_diterQ (recFieldsQ r)[k]) ∗ ((curPtr_diterQ p r k + 1#64) ↦ₛ ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)) ∗ (p ↦ₛ preBytes_diterQ r k) := by
  unfold Prost.sliceCursorAfter; have hsub := encodeRecord_sub_rem_length_diterQ hr k
  have hrem : ((recFieldsQ r).drop k).flatMap GenFieldQ.enc = keyByte_diterQ (recFieldsQ r)[k] :: ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) := by
    rw [drop_flatMap_enc_diterQ hk, enc_eq_keyByte_cons_diterQ, List.cons_append]
  have hbs_split : (p ↦ₛ encodeRecord r) = (p ↦ₛ preBytes_diterQ r k) ∗ (curPtr_diterQ p r k ↦₈ keyByte_diterQ (recFieldsQ r)[k]) ∗
      ((curPtr_diterQ p r k + 1#64) ↦ₛ ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)) := by
    conv_lhs => rw [encodeRecord_eq_preBytes_append_diterQ hr k, hrem]
    rw [pointsToBytes_append, ← curPtr_diterQ, pointsToBytes_cons]
  rw [hsub, ← curPtr_diterQ, show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega, hbs_split, hrem, List.length_cons]; ac_rfl

theorem sliceCursorAfter_unsplit_key_diterQ (L p : BitVec 64) {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr_diterQ p r k + 1#64) ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) (((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) ∗
      (curPtr_diterQ p r k ↦₈ keyByte_diterQ (recFieldsQ r)[k]) ∗ (p ↦ₛ preBytes_diterQ r k) =
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r) (((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) := by
  let fl := (recFieldsQ r)[k]; let rest := ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc
  have hrem : ((recFieldsQ r).drop k).flatMap GenFieldQ.enc = keyByte_diterQ fl :: (fl.payload ++ rest) := by rw [drop_flatMap_enc_diterQ hk, enc_eq_keyByte_cons_diterQ, List.cons_append]
  have hbs_eq : encodeRecord r = preBytes_diterQ r k ++ (keyByte_diterQ fl :: (fl.payload ++ rest)) := by rw [encodeRecord_eq_preBytes_append_diterQ hr k, hrem]
  have hpay_sub : (fl.payload ++ rest).length - rest.length = fl.payload.length := by rw [List.length_append]; omega
  have hbs_sub : (encodeRecord r).length - rest.length = (preBytes_diterQ r k).length + 1 + fl.payload.length := by rw [hbs_eq, List.length_append, List.length_cons, List.length_append]; omega
  have hptr : curPtr_diterQ p r k + 1#64 + BitVec.ofNat 64 ((fl.payload ++ rest).length - rest.length) = p + BitVec.ofNat 64 ((encodeRecord r).length - rest.length) := by
    rw [hpay_sub, hbs_sub, curPtr_diterQ, BitVec.ofNat_add, BitVec.ofNat_add]; bv_omega
  have hbs_pts : (p ↦ₛ encodeRecord r) = (p ↦ₛ preBytes_diterQ r k) ∗ (curPtr_diterQ p r k ↦₈ keyByte_diterQ fl) ∗ ((curPtr_diterQ p r k + 1#64) ↦ₛ (fl.payload ++ rest)) := by
    conv_lhs => rw [hbs_eq]
    rw [pointsToBytes_append, ← curPtr_diterQ, pointsToBytes_cons]
  unfold Prost.sliceCursorAfter; rw [hptr, hbs_pts]; ac_rfl

theorem deserLocalsQA_decomp_diterQ (A : RustAlloc) (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGQ) :
    deserLocalsQA A L p bs rest v = Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗ prostSSGQAt A (L + 0x420#64) v ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ deserFixed_loopIter L := by
  unfold deserLocalsQA deserFixed_loopIter
  generalize memRegion L 0x3f8 = m1; generalize memRegion (L + 0x578#64) 0x170 = m2; generalize memRegion (L + 0x6f0#64) 0x20 = m3; ac_rfl

theorem deserLocalsQ_decomp_diterQ (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGQ) :
    deserLocalsQ L p bs rest v = Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗ prostSSGQAt A0 (L + 0x420#64) v ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ deserFixed_loopIter L :=
  deserLocalsQA_decomp_diterQ A0 L p bs rest v

private theorem ule_zero_ofNat_succ_diterQ {n : Nat} (hn : n < 2 ^ 33) : (BitVec.ofNat 64 (n + 1)).ule 0#64 = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)]; omega
@[local arm64_norm] private theorem keyByte_signExtend_lsb63_diterQ (fl : GenFieldQ) : (BitVec.signExtend 64 (keyByte_diterQ fl)).getLsbD 63 = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterQ, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt]
@[local arm64_norm] private theorem keyByte_signExtend_lsr32_diterQ (fl : GenFieldQ) : (BitVec.signExtend 64 (keyByte_diterQ fl)) >>> 32 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterQ, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt]
@[local arm64_norm] private theorem keyByte_signExtend_and7_ule6_diterQ (fl : GenFieldQ) : (6#64).ule (BitVec.signExtend 64 (keyByte_diterQ fl) &&& 7#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterQ, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt]
@[local arm64_norm] private theorem keyByte_signExtend_tag_w1_diterQ (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (keyByte_diterQ fl))) >>> 3)) = BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterQ, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt]
@[local arm64_norm] private theorem tag_zeroExtend_ofNat32_diterQ (fl : GenFieldQ) : BitVec.zeroExtend 64 (BitVec.ofNat 32 fl.tag) = BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [GenFieldQ.tag, GenField.tag]
@[local arm64_norm] private theorem tag_ofNat64_beq0_diterQ (fl : GenFieldQ) : (BitVec.ofNat 64 fl.tag == 0#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [GenFieldQ.tag, GenField.tag]
@[local arm64_norm] private theorem tag_ofNat64_setWidth32_diterQ (fl : GenFieldQ) : (BitVec.ofNat 64 fl.tag).setWidth 32 = BitVec.ofNat 32 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [GenFieldQ.tag, GenField.tag]

theorem step_254_to_2e8_loopIterQ_at_ext (img : Obj.Image) (ext : String → Option (State → State))
    (L curPtr : BitVec 64) (fl : GenFieldQ) (n : Nat) (s : State) {post : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64) (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = L + 0x710#64) (hx20 : s.readReg64 .x20 = 0#64) (hx23 : s.readReg64 .x23 = L + 0x408#64) (hn : n < 2 ^ 33)
    (hnext : ∀ sm : State,
      sm.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) →
      sm.status = .Running → sm.sp = s.sp → (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) → sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr recDeserializeName + 748#64 →
      sm.readReg64 .x0 = L + 0x420#64 → (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag → (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat →
      sm.readReg64 .x3 = L + 0x6e8#64 → (sm.readReg64 .x4).setWidth 32 = 99#32 → sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = 0#64 →
      sm.readReg64 .x23 = L + 0x408#64 → sm.readReg64 .x29 = L + 0x710#64 → post sm (stepPost_loopIter L curPtr (keyByte_diterQ fl) n)) :
    SepWP (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))) s
      (stepPre_loopIter L curPtr (keyByte_diterQ fl) n) post := by
  have hule := ule_zero_ofNat_succ_diterQ hn; let H := Rust.withPanics ext; diter_fetches img.base H
  dsimp only [SP2Ext, contractProg] at hpc hnext ⊢; generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr recDeserializeName = entry
  examples_hide_fetches; unfold stepPre_loopIter; iterate 22 wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]; rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterQ, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt, WireType.toNat])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

/-- One-field `SessionRecord::deserialize` loop iteration (`k → k + 1`, `A : RustAlloc`) on
`SP2Ext img.base ext` for `DeserializeScopeP_Q NonEmptyV1Q`. -/
theorem deserLoopIterQ_ok_atWA (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hMF : MergeFieldQOkAtWA img A ext (fun _ => True)) (x : DeserializeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    (hk : k < (recFieldsQ x.r).length) (hs : DeserLoopQAtWA img A ext x R s0 k s) :
    DeserStepQAtWA img A ext x R s0 s (fun s' => DeserLoopQAtWA img A ext x R s0 (k + 1) s') := by
  obtain ⟨hpc, hrun, htr, hsym, hF, hsp, hal, hx29, hx19, hx20, hx23, hmem⟩ := hs
  let L := deserSpL s0.sp; let fl := (recFieldsQ x.r)[k]; let rest := ((recFieldsQ x.r).drop (k + 1)).flatMap GenFieldQ.enc
  let payRest := fl.payload ++ rest; let curPtr := curPtr_diterQ x.p x.r k
  have hpc_entry : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 := hpc
  have hn_lt : payRest.length < 2 ^ 33 := payload_rest_length_lt_diterQ hr hk
  set F_loop : SepProp := (x.p ↦ₛ preBytes_diterQ x.r k) ∗ prostSSGQAt A (L + 0x420#64) (ssgqAfter x.r k) ∗
    ((curPtr + 1#64) ↦ₛ payRest) ∗ deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗ deserCalleeUnused_loopIterW L ∗ stackAt L mergeFieldStackX ∗ deserSaved s0 ∗ (A.pool ∗ R)
  have hmem1 : s.mem ⊨ stepPre_loopIter L curPtr (keyByte_diterQ fl) payRest.length ∗ F_loop := by
    have hmem' : s.mem ⊨ deserLocalsQA A L x.p (encodeRecord x.r) (((recFieldsQ x.r).drop k).flatMap GenFieldQ.enc) (ssgqAfter x.r k) ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ (A.pool ∗ R) := by convert hmem using 1; ac_rfl
    rw [deserLocalsQA_decomp_diterQ, deserOutRegion_eq_loopIter, sliceCursorAfter_split_key_diterQ L x.p hr hk, stackAt_deserCallee_split_loopIterW L, sep_perm1_loopIter] at hmem'; exact hmem'
  intro hL
  obtain ⟨sm, hsteps1, ⟨-, -, Pm, hmm, hpcm, hrunm, hspm, htrm, hlrm, hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hx23m, hx29m, hPm⟩ | ⟨_, _hoom1⟩⟩ :=
    (step_254_to_2e8_loopIterQ_at_ext img ext L curPtr fl payRest.length s (post := fun sm Pm =>
        sm.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) ∧
        sm.status = .Running ∧ sm.sp = s.sp ∧ (sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧ sm.readReg64 .lr = (SP2Ext img.base ext).fnAddr recDeserializeName + 748#64 ∧
        sm.readReg64 .x0 = L + 0x420#64 ∧ (sm.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 fl.tag ∧ (sm.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 fl.wt.toNat ∧
        sm.readReg64 .x3 = L + 0x6e8#64 ∧ (sm.readReg64 .x4).setWidth 32 = 99#32 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = 0#64 ∧ sm.readReg64 .x23 = L + 0x408#64 ∧ sm.readReg64 .x29 = L + 0x710#64 ∧ Pm = stepPost_loopIter L curPtr (keyByte_diterQ fl) payRest.length)
      hpc_entry hrun hx29 hx20 hx23 hn_lt (fun _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩)).elim hmem1 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom1).elim
  subst hPm; have hFm : img.FrozenLoaded sm := hsteps1.frozenLoaded hF; have hsymm : sm.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
  have hLm : (SP2Ext img.base ext).CodeLoaded sm.mem := hsteps1.codeLoaded hL; have hspm_L : sm.sp = L := hspm.trans hsp
  have hal_m : sm.spAligned = true := by simp only [State.spAligned] at hal ⊢; rwa [hspm]
  have hcall : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")))
      (mergeFieldQSpecAtWA A img (fun _ => True)) := by rw [fnAddr_mergeField_eq_deser_at_ext]; exact hMF
  let g : MergeFieldQGhost := ⟨L + 0x420#64, ssgqAfter x.r k, fl, L + 0x6e8#64, L + 0x3f8#64, curPtr + 1#64, rest⟩
  set F_mf : SepProp := (curPtr ↦₈ keyByte_diterQ fl) ∗ (x.p ↦ₛ preBytes_diterQ x.r k) ∗ deserFixed_loopIter L ∗ deserOutRegion_loopIter x.out ∗ deserCalleeUnused_loopIterW L ∗ deserSaved s0
  have hok : fl.Ok := recFieldsQ_ok x.r hr fl (List.getElem_mem hk); have hfresh : fl.Fresh (ssgqAfter x.r k) := recFieldsQ_fresh x.r hr k hk
  have hpay_lt62 : (fl.payload ++ rest).length < 2 ^ 62 := Nat.lt_trans hn_lt (by decide)
  have hpre_mf : sm.mem ⊨ (mergeFieldQSpecAtWA A img (fun _ => True)).pre g sm ∗ (F_mf ∗ R) := by
    dsimp only [mergeFieldQSpecAtWA, g]; rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx2m, hx3m, hx4m, trivial, hok, hfresh, hpay_lt62, hFm, hsymm⟩, ?_⟩
    rw [hspm_L]; unfold Prost.sliceCursorAt; rw [show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega]; dsimp only [stepPost_loopIter, F_loop] at hmm; dsimp only [F_mf]; convert hmm using 1; ac_rfl
  obtain ⟨s2, hsteps2, hout, -⟩ := hcall.no_fault_before_outcome g (F_mf ∗ R) sm hpcm hrunm hpre_mf hal_m hLm
  rcases hout with ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hpost2⟩ | ⟨hpan2, hpost2⟩ | ⟨code, _, hpost2⟩ | ⟨_, hoom2⟩
  · rw [hlrm] at hpc2; dsimp only [mergeFieldQSpecAtWA, g] at hpost2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2; obtain ⟨⟨htr2, hx0_2⟩, hmem2⟩ := hpost2
    have hmem2' : s2.mem ⊨ (prostSSGQAt A (L + 0x420#64) ((ssgqAfter x.r k).apply fl) ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗ stackAt sm.sp mergeFieldStackX) ∗ (F_mf ∗ (A.pool ∗ R)) := by convert hmem2 using 1; ac_rfl
    have hL2 : (SP2Ext img.base ext).CodeLoaded s2.mem := hsteps2.codeLoaded hLm
    obtain ⟨sf, hsteps3, ⟨-, -, P_f, hmf, hpcf, hrunf, hspf, htrf, hx19f, hx20f, hx23f, hx29f, hPf⟩ | ⟨_, _hoom3⟩⟩ :=
      (step_2ec_loopIter_at_ext img ext s2
        (P := prostSSGQAt A (L + 0x420#64) ((ssgqAfter x.r k).apply fl) ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗ stackAt sm.sp mergeFieldStackX)
        (post := fun sf P_f => sf.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 596#64 ∧ sf.status = .Running ∧ sf.sp = s2.sp ∧ (sf.trace = s2.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s2) ∧
          sf.readReg64 .x19 = s2.readReg64 .x19 ∧ sf.readReg64 .x20 = s2.readReg64 .x20 ∧ sf.readReg64 .x23 = s2.readReg64 .x23 ∧ sf.readReg64 .x29 = s2.readReg64 .x29 ∧
          P_f = (prostSSGQAt A (L + 0x420#64) ((ssgqAfter x.r k).apply fl) ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr + 1#64) payRest rest ∗ stackAt sm.sp mergeFieldStackX))
        hpc2 hrun2 hx0_2 (fun _ h1 h2 h3 h4 h5 h6 h7 h8 => ⟨h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩)).elim hmem2' hL2
    rotate_left; · exact (not_satisfies_false_sepConj _hoom3).elim
    subst hPf; have hsteps_all : Steps (SP2Ext img.base ext) s sf := (hsteps1.trans hsteps2).trans hsteps3
    have hsp_sf : sf.sp = L := hspf.trans (hsp2.trans hspm_L); have hsp_s : sf.sp = s.sp := hsp_sf.trans hsp.symm
    have hal_sf : sf.spAligned = true := by simp only [State.spAligned] at hal ⊢; rwa [hsp_s]
    refine ⟨sf, hsteps_all, Or.inl ⟨hpcf, hrunf, ⟨htrf.1.trans (htr2.trans (htrm.1.trans htr.1)), htrf.2.trans (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans (htrm.2.trans htr.2))⟩, hsteps_all.symtab_eq.trans hsym, hsteps_all.frozenLoaded hF, hsp_sf, hal_sf,
      hx29f.trans (hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hx29m), hx19f.trans (hcs2.1.trans (hx19m.trans hx19)), hx20f.trans (hcs2.2.1.trans hx20m), hx23f.trans (hcs2.2.2.2.2.1.trans hx23m), ?_⟩⟩
    rw [hspm_L] at hmf
    have hmf' : sf.mem ⊨ deserLocalsQA A L x.p (encodeRecord x.r) (((recFieldsQ x.r).drop (k + 1)).flatMap GenFieldQ.enc) (ssgqAfter x.r (k + 1)) ∗
        memRegion x.out 368 ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ (A.pool ∗ R) := by
      rw [deserLocalsQA_decomp_diterQ, deserOutRegion_eq_loopIter, ssgqAfter_succ_diterQ hk, ← sliceCursorAfter_unsplit_key_diterQ L x.p hr hk, stackAt_deserCallee_split_loopIterW L, ← sep_perm3_loopIter]
      exact hmf
    change sf.mem ⊨ deserLocalsQA A L x.p (encodeRecord x.r) (((recFieldsQ x.r).drop (k + 1)).flatMap GenFieldQ.enc) (ssgqAfter x.r (k + 1)) ∗ memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R
    convert hmf' using 1; ac_rfl
  · refine ⟨s2, hsteps1.trans hsteps2, Or.inr ⟨hpan2, ?_⟩⟩
    dsimp only [mergeFieldQSpecAtWA, deserializeQSpecAtWA, allocPanic] at hpost2 ⊢; rw [← sepConj_assoc] at hpost2
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hpost2; rw [allocFailedIn, htrm.1, htr.1] at ha; rw [htrm.1, htr.1] at hp; exact ⟨ha, hp⟩
  · exact (not_satisfies_false_sepConj hpost2).elim
  · exact (not_satisfies_false_sepConj hoom2).elim

theorem deserLoopIterQ_ok_atW (img : Obj.Image) (ext : String → Option (State → State))
    (hMF : MergeFieldQOkAtW img ext (fun _ => True)) (x : DeserializeGenGhost) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) (hr : DeserializeScopeP_Q NonEmptyV1Q x.r)
    (hk : k < (recFieldsQ x.r).length) (hs : DeserLoopQAtW img ext x R s0 k s) :
    DeserStepQAtW img ext x R s0 s (fun s' => DeserLoopQAtW img ext x R s0 (k + 1) s') := by
  unfold DeserStepQAtW; rw [← deserializeQSpecAtWA_A0, ← DeserLoopQAtWA_A0]
  exact deserLoopIterQ_ok_atWA img A0 ext (by unfold MergeFieldQOkAtWA; rwa [mergeFieldQSpecAtWA_A0]) x R s0 k s hr hk (by rwa [DeserLoopQAtWA_A0])

/-! ## Loop exit (`deserLoopExitQ_ok_extWA` / `deserLoopExitQ_ok_atW`) -/

def ProstSSGQMovePropA (A : RustAlloc) : Prop :=
  ∀ {m : Memory} {L : BitVec 64} {v : SSGQ} {R : SepProp}, (m ⊨ prostSSGQAt A (L + 0x420#64) v ∗ R) →
    ∃ w0 : BitVec 64, ∃ rest : List (BitVec 8), ∃ H : SepProp,
      w0 ≠ noneCap ∧ rest.length = 336 ∧ (∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGQAt A b v) ∧
      (m ⊨ (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H) ∗ R)

abbrev ProstSSGQMoveProp : Prop := ProstSSGQMovePropA A0

private theorem fnOff_deser_dexitQ :
    libsignalSessionCode.fnOff recDeserializeName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") :=
  ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::deserialize"

local elab "dexit_code_fetches_from_q " codeId:ident b:term:max H:term:max hfn:term:max off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "dexit_code_fetches_from_q"
  let k0 := k0.getNat; let len := len.getNat; let codeBase := codeId.getId.eraseMacroScopes
  let fetchEntry := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := Lean.mkIdent (Lean.Name.str `CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopExitG s!"loopExit_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Lean.Syntax.mkNumLit (toString k)
    if k == 0 then Lean.Elab.Tactic.evalTactic (← `(tactic| have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else Lean.Elab.Tactic.evalTactic (← `(tactic| have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

local macro "dexit_fetches_q " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| dexit_code_fetches_from_q CryptoVerification.libsignalSessionCode $b $H fnOff_deser_dexitQ (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) $k0 $len)

@[local arm64_norm] private theorem int64_raw_toBitVec_dexitQ (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt h).symm
private theorem w0_add_one_ne_zero_dexitQ {w0 : BitVec 64} (h : w0 ≠ noneCap) : w0 + 1#64 ≠ 0#64 := by unfold noneCap at h; bv_omega
private theorem w0_add_one_beq_zero_dexitQ {w0 : BitVec 64} (h : w0 ≠ noneCap) : (w0 + 1#64 == 0#64) = false := by rw [beq_eq_false_iff_ne]; exact w0_add_one_ne_zero_dexitQ h

private def deserSavedAtL_dexitQ (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 0x710#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 0x718#64) ↦₆₄ s0.readReg64 .x30) ∗ ((L + 0x720#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 0x728#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((L + 0x730#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 0x738#64) ↦₆₄ s0.readReg64 .x25) ∗ ((L + 0x740#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 0x748#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((L + 0x750#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 0x758#64) ↦₆₄ s0.readReg64 .x21) ∗ ((L + 0x760#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 0x768#64) ↦₆₄ s0.readReg64 .x19)
private theorem deserSaved_eq_atL_dexitQ (s0 : State) : deserSaved s0 = deserSavedAtL_dexitQ (deserSpL s0.sp) s0 := by
  unfold deserSaved deserSavedAtL_dexitQ deserSpL; rw [show s0.sp - 0x60#64 = s0.sp - 0x770#64 + 0x710#64 by bv_omega]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
private theorem sliceCursorAfter_nil_dexitQ (L p : BitVec 64) (bs : List (BitVec 8)) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p bs [] = ((L + 0x3f8#64) ↦₆₄ (p + BitVec.ofNat 64 bs.length)) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (p ↦ₛ bs) := by
  unfold Prost.sliceCursorAfter; rw [show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega, List.length_nil, Nat.sub_zero]
private theorem memRegion_3f8_split_dexitQ (L : BitVec 64) :
    memRegion L 0x3f8 = memRegion L 8 ∗ (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) := by
  rw [memRegion_split' (b := L) (b' := L + 8#64) (N := 0x3f8) (n := 8) (k := 1008) (by decide) rfl (by decide),
    memRegion_split' (b := L + 8#64) (b' := L + 0x158#64) (N := 1008) (n := 336) (k := 672) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := L + 0x158#64) (b' := L + 0x2a8#64) (N := 672) (n := 336) (k := 336) (by decide) (by bv_omega) (by decide)]
private theorem memRegion_out_split_dexitQ (out : BitVec 64) :
    memRegion out 368 = ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
      (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗ ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗ memRegion (out + 0x20#64) 336 := by
  rw [memRegion_split' (b := out) (b' := out + 8#64) (N := 368) (n := 8) (k := 360) (by decide) rfl (by decide),
    memRegion_split' (b := out + 8#64) (b' := out + 0x10#64) (N := 360) (n := 8) (k := 352) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := out + 0x10#64) (b' := out + 0x18#64) (N := 352) (n := 8) (k := 344) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := out + 0x18#64) (b' := out + 0x20#64) (N := 344) (n := 8) (k := 336) (by decide) (by bv_omega) (by decide),
    ProofLib.memRegion_eight out, ProofLib.memRegion_eight (out + 8#64), ProofLib.memRegion_eight (out + 0x10#64), ProofLib.memRegion_eight (out + 0x18#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
private theorem satisfies_memRegion_out_split_dexitQ {m : Memory} {out : BitVec 64} {R : SepProp} (h : m ⊨ memRegion out 368 ∗ R) :
    ∃ u0 u1 u2 u3 : BitVec 64, m ⊨ ((out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗ ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗ memRegion (out + 0x20#64) 336) ∗ R := by
  rw [memRegion_out_split_dexitQ out] at h; simp only [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u3, u2, u1, u0, h⟩; exact ⟨u0, u1, u2, u3, by simpa only [sepConj_assoc] using h⟩

private theorem deserSavedAtL_entails_memRegion_dexitQ (L : BitVec 64) (s0 : State) : deserSavedAtL_dexitQ L s0 ⊢ memRegion (L + 0x710#64) 0x60 := by
  unfold deserSavedAtL_dexitQ
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  have join (n : Nat) (h : n + 8 ≤ 2 ^ 64) : memRegion (L + 0x710#64) n ∗ memRegion (L + BitVec.ofNat 64 (0x710 + n)) 8 = memRegion (L + 0x710#64) (n + 8) :=
    (memRegion_split' (b := L + 0x710#64) (b' := L + BitVec.ofNat 64 (0x710 + n)) (n := n) (k := 8) rfl (by bv_omega) h).symm
  simp only [← sepConj_assoc]
  rw [join 8 (by decide), join 16 (by decide), join 24 (by decide), join 32 (by decide), join 40 (by decide),
    join 48 (by decide), join 56 (by decide), join 64 (by decide), join 72 (by decide), join 80 (by decide), join 88 (by decide)]
  exact Entails.refl _

private theorem dexit_locals_entails_memRegion_dexitQ (L c0 w0 : BitVec 64) (s0 : State) (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗ ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
      ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗ ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
      memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗ deserSavedAtL_dexitQ L s0 ⊢ memRegion L 0x770 := by
  have hb (a : BitVec 64) : (a ↦ₛ rest) ⊢ memRegion a 336 := by rw [← hrest]; exact ProofLib.pointsToBytes_entails_memRegion a rest
  refine Entails.trans (sepConj_mono_right (sepConj_mono (hb (L + 8#64)) (sepConj_mono (hb (L + 0x158#64)) (sepConj_mono (hb (L + 0x2a8#64))
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (hb (L + 0x428#64)) (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono_right (deserSavedAtL_entails_memRegion_dexitQ L s0))))))))))))))) ?_
  have join (n k : Nat) (h : n + k ≤ 2 ^ 64) : memRegion L n ∗ memRegion (L + BitVec.ofNat 64 n) k = memRegion L (n + k) :=
    (memRegion_split' (b := L) (b' := L + BitVec.ofNat 64 n) (n := n) (k := k) rfl rfl h).symm
  simp only [← sepConj_assoc]
  rw [join 8 336 (by decide), join 344 336 (by decide), join 680 336 (by decide), join 1016 8 (by decide), join 1024 8 (by decide),
    join 1032 8 (by decide), join 1040 8 (by decide), join 1048 8 (by decide), join 1056 8 (by decide), join 1064 336 (by decide),
    join 1400 0x170 (by decide), join 1768 8 (by decide), join 1776 0x20 (by decide), join 1808 0x60 (by decide)]
  exact Entails.refl _

private theorem dexit_frame_entails_stackAt_dexitQ (s0 : State) (c0 w0 : BitVec 64) (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    let L := deserSpL s0.sp
    stackAt L deserCalleeStack ∗ (memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
      ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
      ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      memRegion (L + 0x6f0#64) 0x20 ∗ deserSavedAtL_dexitQ L s0) ⊢ stackAt s0.sp recDeserializeStack := by
  intro L; refine Entails.trans (sepConj_mono_right (dexit_locals_entails_memRegion_dexitQ L c0 w0 s0 rest hrest)) ?_; unfold stackAt
  have h1 : s0.sp - BitVec.ofNat 64 recDeserializeStack = L - BitVec.ofNat 64 deserCalleeStack := by dsimp [L, deserSpL, recDeserializeStack, deserCalleeStack]; bv_omega
  rw [h1, memRegion_split' (b := L - BitVec.ofNat 64 deserCalleeStack) (b' := L) (N := recDeserializeStack) (n := deserCalleeStack) (k := 0x770) (by decide)
    (by dsimp [deserCalleeStack, recDeserializeStack]; bv_omega) (by decide)]
  exact Entails.refl _

@[local simp, local wp_norm, local arm64_norm] private theorem frozenLoaded_writeReg64_dexitQ (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 64) : img.FrozenLoaded (s.writeReg64 r v) = img.FrozenLoaded s := propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩
@[local simp, local wp_norm, local arm64_norm] private theorem frozenLoaded_writeReg32_dexitQ (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 32) : img.FrozenLoaded (s.writeReg32 r v) = img.FrozenLoaded s := propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩
@[local simp, local wp_norm, local arm64_norm] private theorem frozenLoaded_setPC_dexitQ (img : Obj.Image) (s : State) (pc : BitVec 64) : img.FrozenLoaded (s.setPC pc) = img.FrozenLoaded s := propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩
@[local simp, local wp_norm, local arm64_norm] private theorem frozenLoaded_setPState_dexitQ (img : Obj.Image) (s : State) (ps : PState) : img.FrozenLoaded (s.setPState ps) = img.FrozenLoaded s := propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩
@[local simp, local wp_norm, local arm64_norm] private theorem frozenLoaded_writeVReg128_dexitQ (img : Obj.Image) (s : State) (idx : BitVec 5) (v : BitVec 128) : img.FrozenLoaded (s.writeVReg128 idx v) = img.FrozenLoaded s := propext ⟨frozenLoaded_of_mem_eq rfl, frozenLoaded_of_mem_eq rfl⟩
@[local simp, local wp_norm, local arm64_norm] private theorem symtab_setPState_dexitQ (s : State) (ps : PState) : (s.setPState ps).symtab = s.symtab := rfl

private theorem memcpy_ok_inv_dexitQ {img : Obj.Image} {ext : String → Option (State → State)}
    (hmc_ok : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img)) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      { pre := ((sessionMemcpySpec deserCalleeStack).inImage img).pre
        post := fun a s0 sf => ⌜img.FrozenLoaded sf ∧ sf.symtab = img.symtab⌝ ∗ (sessionMemcpySpec deserCalleeStack).post a s0 sf } := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hm hsp hCode => ?_
  have hm_in := hm; dsimp only [Spec.inImage] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hfrozen, hsym⟩, -⟩
  obtain ⟨sf, hsteps, hout, -⟩ := hmc_ok.no_fault_before_outcome x R s0 hpc hrun hm_in hsp hCode
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hsteps.frozenLoaded hfrozen, hsteps.symtab_eq.trans hsym⟩, hpost⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpost; exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpost; exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [Spec.inImage, sessionMemcpySpec, libcMemcpySpec] at hpost; exact False.elim (not_satisfies_false_sepConj hpost)

set_option maxHeartbeats 800000 in
private theorem dexit_sepWP_dexitQ {img : Obj.Image} {ext : String → Option (State → State)}
    (hmc_ok : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img))
    {s0 s : State} {L out w0 u0 u1 u2 u3 : BitVec 64} {rest : List (BitVec 8)}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr recDeserializeName + 0x254#64) (hrun : s.status = .Running) (hsp : s.sp = L) (hal : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = L + 0x710#64) (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = 0#64) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hw0 : w0 ≠ noneCap) (hrest : rest.length = 336) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    SepWP (SP2Ext img.base ext) (s0.readReg64 .lr) s
      (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗
        ((L + 0x418#64) ↦₆₄ 0#64) ∗ ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗
        ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗ memRegion (out + 0x20#64) 336 ∗ stackAt L deserCalleeStack ∗ deserSavedAtL_dexitQ L s0)
      (fun sf P_f => sf.sp = L + 0x770#64 ∧ sf.trace = s.trace ∧ CalleeSavedPreserved s0 sf ∧
        P_f = (((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗
          ((L + 0x418#64) ↦₆₄ 0#64) ∗ ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗
          ((out + 0x10#64) ↦₆₄ 0#64) ∗ ((out + 0x18#64) ↦₆₄ w0) ∗ ((out + 0x20#64) ↦ₛ rest) ∗ stackAt L deserCalleeStack ∗ deserSavedAtL_dexitQ L s0)) := by
  subst hsp; have hmemcpy := memcpy_ok_inv_dexitQ hmc_ok
  have hw0_ne := w0_add_one_ne_zero_dexitQ hw0; have hw0_beq := w0_add_one_beq_zero_dexitQ hw0
  dexit_fetches_q img.base (Rust.withPanics ext) 492 20; dexit_fetches_q img.base (Rust.withPanics ext) 596 16
  dexit_fetches_q img.base (Rust.withPanics ext) 780 4; dexit_fetches_q img.base (Rust.withPanics ext) 852 68
  dexit_fetches_q img.base (Rust.withPanics ext) 1208 32; dexit_fetches_q img.base (Rust.withPanics ext) 1248 44
  dsimp only [SP2Ext, contractProg] at hpc hmemcpy ⊢
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr recDeserializeName = entry at *
  examples_hide_fetches; unfold deserSavedAtL_dexitQ
  wp_steps; wp_call hmemcpy (s.sp + 8#64, s.sp + 0x428#64, rest)
  wp_steps; wp_call hmemcpy (s.sp + 0x2a8#64, s.sp + 8#64, rest)
  wp_steps; wp_call hmemcpy (s.sp + 0x158#64, s.sp + 0x2a8#64, rest)
  apply ProofLib.SepWP.of_sepWP_inv (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize")) (by assumption) (by assumption)
  wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF_c4 hsym_c4; wp_call hmemcpy (out + 0x20#64, s.sp + 0x158#64, rest)
  wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]; ac_rfl

/-- `SessionRecord::deserialize` loop exit (`k = |recFieldsQ x.r|` → return, `A : RustAlloc`) from
`memcpy`. -/
theorem deserLoopExitQ_ok_of_memcpyA (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hmc_ok : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img))
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State)
    (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) (hs : DeserLoopQAtWA img A ext x R s0 (recFieldsQ x.r).length s) :
    DeserStepQAtWA img A ext x R s0 s (DeserRetQAtWA A x R s0) := by
  let _ := hr; rcases hs with ⟨hpc, hrun, ⟨htr, hvregs⟩, hsym, hfr, hsp, hal, hx29, hx19, hx20, _hx23, hmem⟩
  let L := deserSpL s0.sp; let v := ssgqAfter x.r (recFieldsQ x.r).length; let bs := encodeRecord x.r
  have hmem : s.mem ⊨ deserLocalsQA A L x.p bs (((recFieldsQ x.r).drop (recFieldsQ x.r).length).flatMap GenFieldQ.enc) v ∗
    memRegion x.out 368 ∗ A.pool ∗ stackAt L deserCalleeStack ∗ deserSaved s0 ∗ R := hmem
  rw [List.drop_length, List.flatMap_nil] at hmem; unfold deserLocalsQA at hmem
  rw [sliceCursorAfter_nil_dexitQ L x.p bs, memRegion_3f8_split_dexitQ L, deserSaved_eq_atL_dexitQ s0] at hmem
  let c0 := x.p + BitVec.ofNat 64 bs.length
  have hmem1 : s.mem ⊨ prostSSGQAt A (L + 0x420#64) v ∗
      (memRegion x.out 368 ∗ memRegion L 8 ∗ (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_dexitQ L s0 ∗ (A.pool ∗ R)) := by
    dsimp only [c0]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  obtain ⟨w0, rest, H, hw0, hrest, hrebuild, hmem2⟩ := satisfies_prostSSGQAt_moveA hmem1
  have hmem3 : s.mem ⊨ memRegion x.out 368 ∗ (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H ∗ memRegion L 8 ∗
       (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) ∗
       ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (x.p ↦ₛ bs) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
       memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗
       stackAt L deserCalleeStack ∗ deserSavedAtL_dexitQ L s0 ∗ (A.pool ∗ R)) := Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  obtain ⟨u0, u1, u2, u3, hmem3'⟩ := satisfies_memRegion_out_split_dexitQ hmem3
  let F := (x.p ↦ₛ bs) ∗ H ∗ memRegion L 8 ∗ ((L + 0x3f8#64) ↦₆₄ c0) ∗ memRegion (L + 0x578#64) 0x170 ∗ memRegion (L + 0x6f0#64) 0x20 ∗ (A.pool ∗ R)
  have hmem4 : s.mem ⊨ (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336 ∗
      ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗ ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
      ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ (x.out ↦₆₄ u0) ∗ ((x.out + 8#64) ↦₆₄ u1) ∗ ((x.out + 0x10#64) ↦₆₄ u2) ∗ ((x.out + 0x18#64) ↦₆₄ u3) ∗ memRegion (x.out + 0x20#64) 336 ∗
      stackAt L deserCalleeStack ∗ deserSavedAtL_dexitQ L s0) ∗ F := by dsimp only [F]; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem3'
  intro hL
  have hwp := dexit_sepWP_dexitQ hmc_ok (s0 := s0) (u0 := u0) (u1 := u1) (u2 := u2) (u3 := u3) hpc hrun hsp hal hx29 hx19 hx20 hvregs hw0 hrest hfr hsym
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem4 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hspf0 : sf.sp = s0.sp := by rw [hspf]; dsimp [L, deserSpL]; bv_omega
  refine ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩⟩
  have hmf1 : sf.mem ⊨ ((x.p ↦ₛ bs) ∗ ((x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ 8#64) ∗ ((x.out + 0x10#64) ↦₆₄ 0#64) ∗
        (((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ H)) ∗
      (stackAt L deserCalleeStack ∗ (memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
        ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
        ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
        memRegion (L + 0x6f0#64) 0x20 ∗ deserSavedAtL_dexitQ L s0))) ∗ (A.pool ∗ R) := by
    dsimp only [F, L] at hmf ⊢; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf
  have hss_out : ((x.out + 0x18#64) ↦₆₄ w0) ∗ ((x.out + 0x20#64) ↦ₛ rest) ∗ H ⊢ prostSSGQAt A (x.out + 0x18#64) v := by
    have hr := hrebuild (x.out + 0x18#64); rwa [show x.out + 0x18#64 + 8#64 = x.out + 0x20#64 by bv_omega] at hr
  have hstk := dexit_frame_entails_stackAt_dexitQ s0 c0 w0 rest hrest; dsimp only at hstk
  have hmf2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hss_out))) hstk))) hmf1
  unfold deserOutRawQA deserOutRecordQA; rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htracef.trans htr, ?_⟩; dsimp only [v, bs] at hmf2; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf2

theorem deserLoopExitQ_ok_of_memcpy (img : Obj.Image) (ext : String → Option (State → State))
    (hmc_ok : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img))
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State)
    (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) (hs : DeserLoopQAtW img ext x R s0 (recFieldsQ x.r).length s) :
    DeserStepQAtW img ext x R s0 s (DeserRetQAtW x R s0) := by
  unfold DeserStepQAtW; rw [← deserializeQSpecAtWA_A0, ← DeserRetQAtWA_A0]
  exact deserLoopExitQ_ok_of_memcpyA img A0 ext hmc_ok x R s0 s hr (by rwa [DeserLoopQAtWA_A0])

theorem deserLoopExitQ_ok_extWA (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hC : Stage2ContractsA img A ext) (x : DeserializeGenGhost) (R : SepProp) (s0 s : State)
    (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) (hs : DeserLoopQAtWA img A ext x R s0 (recFieldsQ x.r).length s) :
    DeserStepQAtWA img A ext x R s0 s (DeserRetQAtWA A x R s0) :=
  deserLoopExitQ_ok_of_memcpyA img A ext (memcpy_ok_extWA hC) x R s0 s hr hs

theorem deserLoopExitQ_ok_extW (img : Obj.Image) (ext : String → Option (State → State))
    (hC : Stage2ContractsA0 img ext) (x : DeserializeGenGhost) (R : SepProp) (s0 s : State)
    (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) (hs : DeserLoopQAtW img ext x R s0 (recFieldsQ x.r).length s) :
    DeserStepQAtW img ext x R s0 s (DeserRetQAtW x R s0) :=
  deserLoopExitQ_ok_of_memcpy img ext (memcpy_ok_extW hC) x R s0 s hr hs

abbrev deserLoopExitQ_ok_atWA := @deserLoopExitQ_ok_extWA
abbrev deserLoopExitQ_ok_atW := @deserLoopExitQ_ok_extW

/-! ## Exact and general loop assembly -/

/-- Bundle of the 3 `SessionRecord::deserialize` leaf theorems on `SP2Ext img.base ext` for `(A : RustAlloc)`. -/
structure DeserLeavesQWA (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  entry : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State), s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName →
    s0.status = .Running → (s0.mem ⊨ (deserializeQSpecAtWA A img).pre x s0 ∗ R) → s0.spAligned = true → DeserStepQAtWA img A ext x R s0 s0 (DeserLoopQAtWA img A ext x R s0 0)
  iter : MergeFieldQOkAtWA img A ext (fun _ => True) → ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State),
    DeserializeScopeP_Q NonEmptyV1Q x.r → k < (recFieldsQ x.r).length → DeserLoopQAtWA img A ext x R s0 k s → DeserStepQAtWA img A ext x R s0 s (DeserLoopQAtWA img A ext x R s0 (k + 1))
  exit : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 s : State), DeserializeScopeP_Q NonEmptyV1Q x.r →
    DeserLoopQAtWA img A ext x R s0 (recFieldsQ x.r).length s → DeserStepQAtWA img A ext x R s0 s (DeserRetQAtWA A x R s0)

structure DeserLeavesQW (img : Obj.Image) (ext : String → Option (State → State)) : Prop where
  entry : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State), s0.pc = (SP2Ext img.base ext).fnAddr recDeserializeName →
    s0.status = .Running → (s0.mem ⊨ (deserializeQSpecAtW img).pre x s0 ∗ R) → s0.spAligned = true → DeserStepQAtW img ext x R s0 s0 (DeserLoopQAtW img ext x R s0 0)
  iter : MergeFieldQOkAtW img ext (fun _ => True) → ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 : State) (k : Nat) (s : State),
    DeserializeScopeP_Q NonEmptyV1Q x.r → k < (recFieldsQ x.r).length → DeserLoopQAtW img ext x R s0 k s → DeserStepQAtW img ext x R s0 s (DeserLoopQAtW img ext x R s0 (k + 1))
  exit : ∀ (x : DeserializeGenGhost) (R : SepProp) (s0 s : State), DeserializeScopeP_Q NonEmptyV1Q x.r →
    DeserLoopQAtW img ext x R s0 (recFieldsQ x.r).length s → DeserStepQAtW img ext x R s0 s (DeserRetQAtW x R s0)

private theorem DeserLeavesQW.toQWA {img : Obj.Image} {ext : String → Option (State → State)} (h : DeserLeavesQW img ext) : DeserLeavesQWA img A0 ext where
  entry x R s0 hpc hrun hpre hal := by unfold DeserStepQAtWA; rw [deserializeQSpecAtWA_A0, DeserLoopQAtWA_A0]; exact h.entry x R s0 hpc hrun (by rwa [← deserializeQSpecAtWA_A0]) hal
  iter hMF x R s0 k s hr hk hs := by
    unfold DeserStepQAtWA; rw [deserializeQSpecAtWA_A0, DeserLoopQAtWA_A0]
    exact h.iter (by unfold MergeFieldQOkAtW; rwa [← mergeFieldQSpecAtWA_A0]) x R s0 k s hr hk (by rwa [← DeserLoopQAtWA_A0])
  exit x R s0 s hr hs := by unfold DeserStepQAtWA; rw [deserializeQSpecAtWA_A0, DeserRetQAtWA_A0]; exact h.exit x R s0 s hr (by rwa [← DeserLoopQAtWA_A0])

theorem deserLeavesQWA_of_contracts (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hCallees : DeserializeCalleesAtWA img A ext) (hC : Stage2ContractsA img A ext) : DeserLeavesQWA img A ext :=
  ⟨deserLoopEntryQ_ok_atWA img A ext hCallees, deserLoopIterQ_ok_atWA img A ext, deserLoopExitQ_ok_extWA img A ext hC⟩
theorem deserLeavesQW_of_contracts (img : Obj.Image) (ext : String → Option (State → State))
    (hCallees : DeserializeCalleesAtW img ext) (hC : Stage2ContractsA0 img ext) : DeserLeavesQW img ext :=
  ⟨deserLoopEntryQ_ok_atW img ext hCallees, deserLoopIterQ_ok_atW img ext, deserLoopExitQ_ok_extW img ext hC⟩

theorem deserLoopQWA_run_exact (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hD : DeserLeavesQWA img A ext) (hMF : MergeFieldQOkAtWA img A ext (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFieldsQ x.r).length → DeserLoopQAtWA img A ext x R s0 k s → reaches_outcome (SP2Ext img.base ext) (deserializeQExactSpecAtWA A img) x R s0 s := by
  intro m; induction m with
  | zero =>
    intro k s hk hs; simp only [Nat.add_zero] at hk; subst hk
    exact segStepG_then (hD.exit x R s0 s hr hs) fun sf ⟨hret, hcc, hmem⟩ =>
      reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hmem⟩)
  | succ m ih =>
    intro k s hk hs
    exact segStepG_then (hD.iter hMF x R s0 k s hr (by omega) hs) fun s' hs' =>
      ih (k + 1) s' (by omega) hs'

theorem deserLoopQW_run_exact (img : Obj.Image) (ext : String → Option (State → State))
    (hD : DeserLeavesQW img ext) (hMF : MergeFieldQOkAtW img ext (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFieldsQ x.r).length → DeserLoopQAtW img ext x R s0 k s → reaches_outcome (SP2Ext img.base ext) (deserializeQExactSpecAtW img) x R s0 s := by
  intro m k s hk hs; rw [← deserializeQExactSpecAtWA_A0]
  exact deserLoopQWA_run_exact img A0 ext hD.toQWA (by unfold MergeFieldQOkAtWA; rwa [mergeFieldQSpecAtWA_A0]) hr m k s hk (by rwa [DeserLoopQAtWA_A0])

theorem deserializeExactQWA_ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hD : DeserLeavesQWA img A ext) (hMF : MergeFieldQOkAtWA img A ext (fun _ => True)) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName) (deserializeQExactSpecAtWA A img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hr : DeserializeScopeP_Q NonEmptyV1Q x.r := by have h := hpre; simp only [deserializeQExactSpecAtWA, deserializeQSpecAtWA, sepConj_assoc, satisfies_pure_sepConj] at h; exact h.1.2.2.2.1
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs =>
    deserLoopQWA_run_exact img A ext hD hMF hr _ 0 s (Nat.zero_add _) hs

theorem deserializeExactQW_ok (img : Obj.Image) (ext : String → Option (State → State))
    (hD : DeserLeavesQW img ext) (hMF : MergeFieldQOkAtW img ext (fun _ => True)) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr recDeserializeName) (deserializeQExactSpecAtW img) := by
  rw [← deserializeQExactSpecAtWA_A0]; exact deserializeExactQWA_ok img A0 ext hD.toQWA (by unfold MergeFieldQOkAtWA; rwa [mergeFieldQSpecAtWA_A0])

theorem deserOutQWA_post (img : Obj.Image) (A : RustAlloc) (x : DeserializeGenGhost) (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) (s0 sf : State) :
    deserOutRawQA A x s0 sf ⊢ (deserializeQSpecAtWA A img).post x s0 sf := by
  dsimp only [deserOutRawQA, deserializeQSpecAtWA, deserializeGenSpecAtA]
  refine sepConj_mono_right (sepConj_mono_right (Entails.trans (sepConj_mono_left (deserReprQA_ok A x.r hr x.out)) ?_))
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun g => Entails.sepExists_right g (by rw [sepConj_assoc]; exact Entails.refl _)

theorem deserOutQW_post (img : Obj.Image) (x : DeserializeGenGhost) (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) (s0 sf : State) :
    deserOutRawQ x s0 sf ⊢ (deserializeQSpecAtW img).post x s0 sf := by
  rw [← deserializeQSpecAtWA_A0, ← congrFun (congrFun (congrFun deserOutRawQA_A0 x) s0) sf]; exact deserOutQWA_post img A0 x hr s0 sf

theorem deserLoopQWA_run (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hD : DeserLeavesQWA img A ext) (hMF : MergeFieldQOkAtWA img A ext (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFieldsQ x.r).length → DeserLoopQAtWA img A ext x R s0 k s → reaches_outcome (SP2Ext img.base ext) (deserializeQSpecAtWA A img) x R s0 s := by
  intro m; induction m with
  | zero =>
    intro k s hk hs; simp only [Nat.add_zero] at hk; subst hk; refine segStepG_then (hD.exit x R s0 s hr hs) ?_
    rintro sf ⟨hret, hcc, hmem⟩; exact reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left (deserOutQWA_post img A x hr s0 sf)) hmem⟩)
  | succ m ih =>
    intro k s hk hs; exact segStepG_then (hD.iter hMF x R s0 k s hr (by omega) hs) fun s' hs' => ih (k + 1) s' (by omega) hs'

theorem deserLoopQW_run (img : Obj.Image) (ext : String → Option (State → State))
    (hD : DeserLeavesQW img ext) (hMF : MergeFieldQOkAtW img ext (fun _ => True))
    {x : DeserializeGenGhost} {R : SepProp} {s0 : State} (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) :
    ∀ (m k : Nat) (s : State), k + m = (recFieldsQ x.r).length → DeserLoopQAtW img ext x R s0 k s → reaches_outcome (SP2Ext img.base ext) (deserializeQSpecAtW img) x R s0 s := by
  intro m k s hk hs; rw [← deserializeQSpecAtWA_A0]
  exact deserLoopQWA_run img A0 ext hD.toQWA (by unfold MergeFieldQOkAtWA; rwa [mergeFieldQSpecAtWA_A0]) hr m k s hk (by rwa [DeserLoopQAtWA_A0])

theorem deserializeBodyQWA_ok (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hD : DeserLeavesQWA img A ext) (hMF : MergeFieldQOkAtWA img A ext (fun _ => True)) :
    OkAtX img.base ext recDeserializeName (deserializeQSpecAtWA A img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hr : DeserializeScopeP_Q NonEmptyV1Q x.r := by have h := hpre; simp only [deserializeQSpecAtWA, sepConj_assoc, satisfies_pure_sepConj] at h; exact h.1.2.2.2.1
  exact segStepG_then (hD.entry x R s0 hpc hrun hpre hal) fun s hs => deserLoopQWA_run img A ext hD hMF hr (recFieldsQ x.r).length 0 s (Nat.zero_add _) hs

theorem deserializeBodyQW_ok (img : Obj.Image) (ext : String → Option (State → State))
    (hD : DeserLeavesQW img ext) (hMF : MergeFieldQOkAtW img ext (fun _ => True)) :
    OkAtX img.base ext recDeserializeName (deserializeQSpecAtW img) := by
  unfold OkAtX; rw [← deserializeQSpecAtWA_A0]; exact deserializeBodyQWA_ok img A0 ext hD.toQWA (by unfold MergeFieldQOkAtWA; rwa [mergeFieldQSpecAtWA_A0])

/-- Generic transport: `deserializeQExactSpecAtWA A img` implies
`(recordDeserializeOpenSpec_Q NonEmptyV1Q A).inImage img`. -/
theorem recordDeserializeOpen_of_exactQA {prog : Program} {entry : BitVec 64} (A : RustAlloc) (img : Obj.Image)
    (hdeser : subroutine_ok prog entry (deserializeQExactSpecAtWA A img)) :
    subroutine_ok prog entry ((recordDeserializeOpenSpec_Q NonEmptyV1Q A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨ptr, bs, out, sess⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' := hpre; dsimp only [Spec.inImage, recordDeserializeOpenSpec_Q] at hpre'
  rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hF, hsym⟩, hpre'⟩; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1_nat, hx8, hbs, hr, G0, hG0⟩, hmem⟩; subst hbs
  have hlen_lt : (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length < 2 ^ 33 := encodeRecord_length_ltQ hr
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length := by
    apply BitVec.eq_of_toNat_eq; rw [hx1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let x_deserialize : DeserializeGenGhost := ⟨ptr, out, ⟨some sess⟩⟩
  let R_deserialize : SepProp := memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack) (recordDeserializeStack - recDeserializeStack) ∗ R
  have hpre_deserialize : s0.mem ⊨ (deserializeQExactSpecAtWA A img).pre x_deserialize s0 ∗ R_deserialize := by
    dsimp only [deserializeQExactSpecAtWA, deserializeQSpecAtWA, x_deserialize, R_deserialize]
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hx0, hx1, hx8, hr, hF, hsym⟩, ?_⟩; convert hmem using 1; ac_rfl
  refine hdeser.mono_outcome x_deserialize R_deserialize s0 hpc hrun hpre_deserialize hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩; dsimp only [deserializeQExactSpecAtWA, deserOutRawQA, x_deserialize, R_deserialize] at hq
    have hq' := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (deserOutRecordQA_entails_binCanonSession A sess hG0 hr out))))) hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'; rcases hq' with ⟨htr, hq_mem⟩
    dsimp only [Spec.inImage, recordDeserializeOpenSpec_Q]; rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩; convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [deserializeQExactSpecAtWA, allocPanic, Spec.inImage, recordDeserializeOpenSpec_Q, R_deserialize] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢; rcases hq with ⟨hfail, hq_mem⟩; refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack) (recordDeserializeStack - recDeserializeStack)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (entails_anyHeap _)
    refine Satisfies.mono hany ?_; convert hq_mem using 1; ac_rfl
  · dsimp only [deserializeQExactSpecAtWA] at hq; rw [satisfies_pure_sepConj] at hq; exact hq.1.elim
  · dsimp only [deserializeQExactSpecAtWA] at hq; rw [satisfies_pure_sepConj] at hq; exact hq.1.elim

theorem recordDeserializeOpen_of_exactQ {prog : Program} {entry : BitVec 64} (img : Obj.Image)
    (hdeser : subroutine_ok prog entry (deserializeQExactSpecAtW img)) :
    subroutine_ok prog entry ((recordDeserializeOpenSpec_Q NonEmptyV1Q A0).inImage img) :=
  recordDeserializeOpen_of_exactQA A0 img (by rwa [deserializeQExactSpecAtWA_A0])

end Symbolic.Swarm.TRREF.B3DeserQ
