/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import LibsignalBinary.Proofs.TripleRatchet.Prog
public import ProofLib.GenPlacedFetches
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Fetch
import ProofLib.SepLogic.WPp

/-!
# Verification of 82- and 93-Instruction `V1State.Unchunked.*::encoded_len` Leaves

Parametric symbolic execution and `[local#1]` / `[local#2]` instantiations for the 82-instruction
(`HeaderSent`, `EkSentCt1Received`) and 93-instruction (`Ct1Sent`, `Ct1SentEkReceived`)
`V1State.Unchunked.*::encoded_len` leaf subroutines.
-/

@[expose] public section


namespace CryptoVerification
set_option maxRecDepth 2000000
gen_ls_blk 162
gen_ls_blk 180
gen_ls_blk 185
gen_ls_blk 192
gen_ls_blk 387
gen_ls_blk 408
gen_ls_blk 411
gen_ls_blk 421
end CryptoVerification

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open EncodedLen

local notation "tripleRatchetProgAtExt" => CryptoVerification.LibsignalTripleRatchet.contractProg

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

private theorem subroutine_ok_repack {G1 G2 : Type} {prog : Program} {entry : BitVec 64}
    {S1 : Spec G1} {S2 : Spec G2} (f : G2 → G1)
    (hpre : ∀ x s, S2.pre x s = S1.pre (f x) s)
    (hpost : ∀ x s0 sf, S2.post x s0 sf = S1.post (f x) s0 sf)
    (hok : subroutine_ok prog entry S1)
    (honPanic : ∀ x s0 sf, S2.onPanic x s0 sf = S1.onPanic (f x) s0 sf := by intros; rfl)
    (honExit : ∀ x c s0 sf, S2.onExit x c s0 sf = S1.onExit (f x) c s0 sf := by intros; rfl)
    (honOom : ∀ x s0 sf, S2.onOom x s0 sf = S1.onOom (f x) s0 sf := by intros; rfl) :
    subroutine_ok prog entry S2 := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre0 hsp
  rw [hpre] at hpre0
  refine (hok.to_outcome (f x) R s0 hpc hrun hpre0 hsp).mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨hpan, hmpan⟩ | ⟨code, hex, hmex⟩ | ⟨hoom, hmoom⟩
  · rw [← hpost] at hpost0; exact Or.inl ⟨hret, hcc, hpost0⟩
  · rw [← honPanic] at hmpan; exact Or.inr (Or.inl ⟨hpan, hmpan⟩)
  · rw [← honExit] at hmex; exact Or.inr (Or.inr (Or.inl ⟨code, hex, hmex⟩))
  · rw [← honOom] at hmoom; exact Or.inr (Or.inr (Or.inr ⟨hoom, hmoom⟩))

/-! ## Part 1: 82-Instruction Group (`HeaderSent`, `EkSentCt1Received`) -/

/-- Entry address predicate for all 4 functions in the 82-insn group. -/
def IsUnchunked82Entry (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ b abs, prog = tripleRatchetProgAtExt b abs ∧
    ((tripleRatchetProgAtExt b abs).fnAddr headerSentEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr headerSentEncodedLenLocal2Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr ekSentCt1ReceivedEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name = entry)) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    (prog = (@blkPC_185).rebase (@blkPl_185 inst).base H ∧ entry = (@blkPl_185 inst).base) ∨
    (prog = (@blkPC_411).rebase (@blkPl_411 inst).base H ∧ entry = (@blkPl_411 inst).base) ∨
    (prog = (@blkPC_192).rebase (@blkPl_192 inst).base H ∧ entry = (@blkPl_192 inst).base) ∨
    (prog = (@blkPC_421).rebase (@blkPl_421 inst).base H ∧ entry = (@blkPl_421 inst).base))

theorem unchunked82_fetch_entry {f : BitVec 64 → Option Instr}
    {a1 a2 a3 a4 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry ∨ a3 = entry ∨ a4 = entry)
    {ins : Instr}
    (h1 : f a1 = some ins) (h2 : f a2 = some ins)
    (h3 : f a3 = some ins) (h4 : f a4 = some ins) :
    f entry = some ins := by
  rcases hfn with rfl | rfl | rfl | rfl <;> assumption

theorem unchunked82_fetch_add {f : BitVec 64 → Option Instr}
    {a1 a2 a3 a4 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry ∨ a3 = entry ∨ a4 = entry)
    {k : Nat} {ins : Instr}
    (h1 : f (a1 + BitVec.ofNat 64 k) = some ins)
    (h2 : f (a2 + BitVec.ofNat 64 k) = some ins)
    (h3 : f (a3 + BitVec.ofNat 64 k) = some ins)
    (h4 : f (a4 + BitVec.ofNat 64 k) = some ins) :
    f (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl | rfl | rfl <;> assumption

theorem unchunked82_fetch_entry_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsUnchunked82Entry prog entry) {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr headerSentEncodedLenLocal1Name) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr headerSentEncodedLenLocal2Name) = some ins)
    (h3 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ekSentCt1ReceivedEncodedLenLocal1Name) = some ins)
    (h4 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name) = some ins)
    (hb1 : ∀ [LibsignalPlacement] H, ((blkPC_185).rebase (blkPl_185).base H).fetch ((blkPl_185).base + 0#64) = some ins)
    (hb2 : ∀ [LibsignalPlacement] H, ((blkPC_411).rebase (blkPl_411).base H).fetch ((blkPl_411).base + 0#64) = some ins)
    (hb3 : ∀ [LibsignalPlacement] H, ((blkPC_192).rebase (blkPl_192).base H).fetch ((blkPl_192).base + 0#64) = some ins)
    (hb4 : ∀ [LibsignalPlacement] H, ((blkPC_421).rebase (blkPl_421).base H).fetch ((blkPl_421).base + 0#64) = some ins) :
    prog.fetch entry = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl | rfl | rfl⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · exact h3 b _
  · exact h4 b _
  · simpa using @hb1 inst H
  · simpa using @hb2 inst H
  · simpa using @hb3 inst H
  · simpa using @hb4 inst H

theorem unchunked82_fetch_add_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsUnchunked82Entry prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr headerSentEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr headerSentEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (h3 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ekSentCt1ReceivedEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h4 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (hb1 : ∀ [LibsignalPlacement] H, ((blkPC_185).rebase (blkPl_185).base H).fetch ((blkPl_185).base + BitVec.ofNat 64 k) = some ins)
    (hb2 : ∀ [LibsignalPlacement] H, ((blkPC_411).rebase (blkPl_411).base H).fetch ((blkPl_411).base + BitVec.ofNat 64 k) = some ins)
    (hb3 : ∀ [LibsignalPlacement] H, ((blkPC_192).rebase (blkPl_192).base H).fetch ((blkPl_192).base + BitVec.ofNat 64 k) = some ins)
    (hb4 : ∀ [LibsignalPlacement] H, ((blkPC_421).rebase (blkPl_421).base H).fetch ((blkPl_421).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl | rfl | rfl⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · exact h3 b _
  · exact h4 b _
  · exact @hb1 inst H
  · exact @hb2 inst H
  · exact @hb3 inst H
  · exact @hb4 inst H

open Lean Elab Tactic in
elab "unchunked82_fetches_range " hfn:ident kStart:num kEnd:num : tactic => do
  let blks := #[185, 411, 192, 421]
  let offs := #[0x39e34, 0x63eac, 0x3a330, 0x67474]
  let fnOffs := #[
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x39e34,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x63eac,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x3a330,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x67474
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let hexK := String.ofList (Nat.toDigits 16 k)
    let decs := offs.map fun off => mkIdent (`CryptoVerification.SpqrV1.ProtoRepr |>.str s!"spqrUnchunked82Bin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let d0 := decs[0]!; let d1 := decs[1]!; let d2 := decs[2]!; let d3 := decs[3]!
    let f0 := fnOffs[0]!; let f1 := fnOffs[1]!; let f2 := fnOffs[2]!; let f3 := fnOffs[3]!
    let bIds := blks.map fun bi => mkIdent (Name.mkSimple s!"blkPC_{bi}_rebase_fetch_0x{hexK}")
    let b0 := bIds[0]!; let b1 := bIds[1]!; let b2 := bIds[2]!; let b3 := bIds[3]!
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := unchunked82_fetch_entry_prog $hfn (fun b H => $fetchEntry (b := b) (H := H) $f0 (by decide) $d0) (fun b H => $fetchEntry (b := b) (H := H) $f1 (by decide) $d1) (fun b H => $fetchEntry (b := b) (H := H) $f2 (by decide) $d2) (fun b H => $fetchEntry (b := b) (H := H) $f3 (by decide) $d3) (fun [LibsignalPlacement] H => $b0 _ H) (fun [LibsignalPlacement] H => $b1 _ H) (fun [LibsignalPlacement] H => $b2 _ H) (fun [LibsignalPlacement] H => $b3 _ H)))
    else
      evalTactic (← `(tactic| have := unchunked82_fetch_add_prog $hfn (k := $kq) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f0 (by decide) $d0) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f1 (by decide) $d1) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f2 (by decide) $d2) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f3 (by decide) $d3) (fun [LibsignalPlacement] H => $b0 _ H) (fun [LibsignalPlacement] H => $b1 _ H) (fun [LibsignalPlacement] H => $b2 _ H) (fun [LibsignalPlacement] H => $b3 _ H)))

theorem unchunked4Unpacked_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {a : BitVec 64}
    {epoch : BitVec 64} {auth : Option AuthenticatorPB} {f3 f4 : List (BitVec 8)} {R : SepProp} {m : Memory}
    (hm : m ⊨ unchunked4Unpacked A g a epoch auth f3 f4 ∗ R) :
    OptAuthBounds g.auth auth ∧ VecU8FieldBounds f3 ∧ VecU8FieldBounds f4 := by
  unfold unchunked4Unpacked at hm
  have ha : m ⊨ optAuthPayload A g.auth (a + 48#64) auth ∗
      ((a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
       ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
       ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ ((a + 96#64) ↦₆₄ epoch) ∗ R) := by convert hm using 1; ac_rfl
  have hf3 : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
       ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
       ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 48#64) auth ∗ ((a + 96#64) ↦₆₄ epoch) ∗ R) := by convert hm using 1; ac_rfl
  have hf4 : m ⊨ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
       ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗
       ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 48#64) auth ∗ ((a + 96#64) ↦₆₄ epoch) ∗ R) := by convert hm using 1; ac_rfl
  exact ⟨optAuthPayload_bounds ha, vecU8Buf_fieldBounds hf3, vecU8Buf_fieldBounds hf4⟩

theorem step_unchunked82_epoch (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked82Entry prog entry)
    (g : Unchunked4PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hauth_b : OptAuthBounds g.auth auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked4Unpacked A g a epoch auth f3 f4 ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (if auth.isSome then entry + 56#64 else entry + 188#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) → EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm ((unchunked4Unpacked A g a epoch auth f3 f4 ∗
        ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked82_fetches_range hfn 0 56
  obtain ⟨hcap_beq, hcap_bne, _⟩ := hauth_b; subst hP
  have hP1 : unchunked4Unpacked A g a epoch auth f3 f4 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 48#64) auth ∗ ((a + 96#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  by_cases hep : epoch = 0#64
  · apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen]) (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem step_unchunked82_auth_none (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked82Entry prog entry)
    (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8)) (hauth : auth = none)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 188#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked4Unpacked A g a epoch auth f3 f4 ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth; unchunked82_fetches_range hfn 188 196
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP; apply SepWPp.of_sepWP (mid := entry + 196#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem step_unchunked82_auth_some (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked82Entry prog entry)
    (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hauth : auth = some au) (hauth_b : OptAuthBounds g.auth auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked4Unpacked A g a epoch auth f3 f4 ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth; unchunked82_fetches_range hfn 56 184
  obtain ⟨_, _, hroot_beq, hroot_bne, hmac_beq, hmac_bne⟩ := hauth_b.2.2 au rfl
  have hauth_fit : optAuthenticatorPBFieldEncodedLen (some au) < 2 ^ 64 := by
    unfold unchunked2EncodedLen at hfit; omega
  have hbody_lt : authenticatorPBEncodedLen au < 2 ^ 64 := by
    dsimp [optAuthenticatorPBFieldEncodedLen] at hauth_fit; omega
  have htot := bv_optAuthField_some au
  have hcmp := cmp_ls_false_of_lt
    (vlen := varintLen (BitVec.ofNat 64 (authenticatorPBEncodedLen au)))
    (tot := optAuthenticatorPBFieldEncodedLen (some au))
    (by dsimp [optAuthenticatorPBFieldEncodedLen]; omega) hauth_fit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  obtain ⟨hadd_final, hccf1, hccf2, hccf3, hccf4⟩ :=
    adds_no_overflow_of_eq (a := optAuthenticatorPBFieldEncodedLen (some au))
      (b := u64VarintFieldEncodedLen epoch) (c := unchunked2EncodedLen epoch (some au)) rfl hfit
  subst hP
  have hP1 : unchunked4Unpacked A g a epoch (some au) f3 f4 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.auth.rootKey.cap) ∗ ((a + 56#64) ↦₆₄ g.auth.rootKey.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 au.rootKey.length) ∗
      vecU8Buf A g.auth.rootKey.cap g.auth.rootKey.ptr au.rootKey ∗
      ((a + 72#64) ↦₆₄ g.auth.macKey.cap) ∗ ((a + 80#64) ↦₆₄ g.auth.macKey.ptr) ∗ ((a + 88#64) ↦₆₄ BitVec.ofNat 64 au.macKey.length) ∗
      vecU8Buf A g.auth.macKey.cap g.auth.macKey.ptr au.macKey ∗ ((a + 96#64) ↦₆₄ epoch) := by
    simp only [unchunked4Unpacked, optAuthCap, optAuthPayload, arm64_norm]
  rw [hP1]
  cases hre : au.rootKey.isEmpty with
  | true =>
    have hr_len : au.rootKey.length = 0 := List.isEmpty_iff.mp hre |> congrArg List.length
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_00 : authenticatorPBEncodedLen au = 0 := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre, hme]
      have hopt_00 : optAuthenticatorPBFieldEncodedLen (some au) = 2 := by simp [optAuthenticatorPBFieldEncodedLen, hbody_00, varintLen]
      rw [hopt_00] at hadd_final hccf1 hccf2
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]; exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      have hbody_01 : bytesFieldEncodedLen au.macKey = authenticatorPBEncodedLen au := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre]
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]; exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc_r := bv_bytesField_nonempty hre
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_10 : bytesFieldEncodedLen au.rootKey = authenticatorPBEncodedLen au := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hme]
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]; exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
        adds_no_overflow_of_eq (a := bytesFieldEncodedLen au.macKey) (b := bytesFieldEncodedLen au.rootKey) (c := authenticatorPBEncodedLen au) rfl hbody_lt
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]; exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Tag-3 `f3: Vec<u8>` field length (`+0x0c4..+0x0ec` -> `+0x0f0` = `entry + 240#64`). -/
theorem step_unchunked82_f3 (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked82Entry prog entry)
    (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hf3_b : VecU8FieldBounds f3) (hfit : unchunked3EncodedLen epoch auth f3 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 196#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth))
    (hP : P = unchunked4Unpacked A g a epoch auth f3 f4 ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 240#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked82_fetches_range hfn 196 240
  obtain ⟨_, hf3_beq, hf3_bne⟩ := hf3_b; subst hP
  have hP1 : unchunked4Unpacked A g a epoch auth f3 f4 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 48#64) auth ∗ ((a + 96#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f3.isEmpty with
  | true =>
    have hf3_len : f3.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked2EncodedLen epoch auth = unchunked3EncodedLen epoch auth f3 := by
      simp [unchunked2EncodedLen, unchunked3EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := entry + 240#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]; exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f3) (b := unchunked2EncodedLen epoch auth)
        (c := unchunked3EncodedLen epoch auth f3) rfl hfit
    apply SepWPp.of_sepWP (mid := entry + 240#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]; exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Tag-4 `f4: Vec<u8>` field length + epilogue (`+0x0f0..+0x120: ldp, ret`). -/
theorem step_unchunked82_f4 (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked82Entry prog entry)
    (g : Unchunked4PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8))
    (hf4_b : VecU8FieldBounds f4) (hfit : unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 240#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked4Unpacked A g a epoch auth f3 f4 ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4) →
      CalleeSavedPreserved s0 sf → Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  unchunked82_fetches_range hfn 240 292
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  obtain ⟨_, hf4_beq, hf4_bne⟩ := hf4_b; subst hP
  have hP1 : unchunked4Unpacked A g a epoch auth f3 f4 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 48#64) auth ∗ ((a + 96#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f4.isEmpty with
  | true =>
    have hf4_len : f4.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked3EncodedLen epoch auth f3 = unchunked4EncodedLen epoch auth f3 f4 := by
      simp [unchunked3EncodedLen, unchunked4EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr); wp_steps
    apply SepWP.done (by simp_all) (by simp_all); apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]; exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by epochEncLen_cc_close)
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f4) (b := unchunked3EncodedLen epoch auth f3)
        (c := unchunked4EncodedLen epoch auth f3 f4) rfl hfit
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr); wp_steps
    apply SepWP.done (by simp_all) (by simp_all); apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]; exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by epochEncLen_cc_close)

/-- Shared `subroutine_ok` proof for all functions in the 82-insn group. -/
theorem unchunked82_entry_pinned_ok (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked82Entry prog entry) :
    subroutine_ok prog entry (unchunked4EncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, epoch, auth, f3, f4⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [unchunked4EncodedLenPinnedSpec, unchunked4PinnedAt_eq_unpacked,
    unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have hfit3 : unchunked3EncodedLen epoch auth f3 < 2 ^ 64 := by
    unfold unchunked4EncodedLen unchunked3EncodedLen at *; omega
  have hfit2 : unchunked2EncodedLen epoch auth < 2 ^ 64 := by
    unfold unchunked3EncodedLen unchunked2EncodedLen at *; omega
  obtain ⟨hauth_b, hf3_b, hf4_b⟩ := unchunked4Unpacked_bounds hpre
  refine ⟨(unchunked4Unpacked A g a epoch auth f3 f4 ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  refine step_unchunked82_epoch (F := R) prog A entry hfn g a s0.sp v16 v8 epoch auth f3 f4
    hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine step_unchunked82_auth_none (F := FSave) prog A entry hfn g a epoch none f3 f4 rfl
      hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine step_unchunked82_f3 (F := FSave) prog A entry hfn g a epoch none f3 f4
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    have hsp3' : s3.sp = s0.sp - 16#64 := by rw [hsp3, hsp2, hsp1]
    have hcs3' : EpochEncLenCalleeSaved s0 s3 := hcs1.trans (hcs2.trans hcs3)
    refine step_unchunked82_f4 (F := R) prog A entry hfn g a s0.sp epoch none f3 f4
      hf4_b hfit hpc3 hrun3 hsp3' halign hx0_3 hx8_3 hcs3' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩; intro hm_f; rw [sepConj_emp] at hm_f
    simp only [unchunked4EncodedLenPinnedSpec, unchunked4PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  · simp only [Option.isSome_some, ↓reduceIte] at hpc1
    refine step_unchunked82_auth_some (F := FSave) prog A entry hfn g a epoch (some au) au f3 f4
      rfl hauth_b hfit2 hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine step_unchunked82_f3 (F := FSave) prog A entry hfn g a epoch (some au) f3 f4
      hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    have hsp3' : s3.sp = s0.sp - 16#64 := by rw [hsp3, hsp2, hsp1]
    have hcs3' : EpochEncLenCalleeSaved s0 s3 := hcs1.trans (hcs2.trans hcs3)
    refine step_unchunked82_f4 (F := R) prog A entry hfn g a s0.sp epoch (some au) f3 f4
      hf4_b hfit hpc3 hrun3 hsp3' halign hx0_3 hx8_3 hcs3' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩; intro hm_f; rw [sepConj_emp] at hm_f
    simp only [unchunked4EncodedLenPinnedSpec, unchunked4PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

theorem unchunked82_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr headerSentEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr headerSentEncodedLenLocal2Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (unchunked4EncodedLenPinnedSpec A) :=
  unchunked82_entry_pinned_ok _ A entry (Or.inl ⟨b, ext, rfl, hfn⟩)

theorem unchunked4EncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (unchunked4EncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (unchunked4EncodedLenSpec A) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, epoch, auth, f3, f4⟩ R s0 hpc hrun hpre hsp
  simp only [unchunked4EncodedLenSpec, unchunked4At_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome ⟨a, g, epoch, auth, f3, f4⟩ R s0 hpc hrun hpre hsp).mono_outcome
    (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [unchunked4EncodedLenSpec, unchunked4At_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### Instantiations for `HeaderSent` and `EkSentCt1Received` (`[local#1, #2]`) -/

def HeaderSentEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr headerSentEncodedLenLocal1Name) (headerSentEncodedLenPinnedSpec A)
def HeaderSentEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr headerSentEncodedLenLocal1Name) (headerSentEncodedLenSpec A)
def HeaderSentEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr headerSentEncodedLenLocal1Name) (headerSentEncodedLenPinnedSpec A)
def HeaderSentEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr headerSentEncodedLenLocal1Name) (headerSentEncodedLenSpec A)
def HeaderSentEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr headerSentEncodedLenLocal2Name) (headerSentEncodedLenPinnedSpec A)
def HeaderSentEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr headerSentEncodedLenLocal2Name) (headerSentEncodedLenSpec A)
def HeaderSentEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr headerSentEncodedLenLocal2Name) (headerSentEncodedLenPinnedSpec A)
def HeaderSentEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr headerSentEncodedLenLocal2Name) (headerSentEncodedLenSpec A)
def HeaderSentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_185).rebase (blkPl_185).base (Rust.withPanics ext)) (blkPl_185).base (headerSentEncodedLenPinnedSpec A)
def HeaderSentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_185).rebase (blkPl_185).base (Rust.withPanics ext)) (blkPl_185).base (headerSentEncodedLenSpec A)
def HeaderSentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_185).rebase (blkPl_185).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_185).base (headerSentEncodedLenPinnedSpec A)
def HeaderSentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_185).rebase (blkPl_185).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_185).base (headerSentEncodedLenSpec A)
def HeaderSentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_411).rebase (blkPl_411).base (Rust.withPanics ext)) (blkPl_411).base (headerSentEncodedLenPinnedSpec A)
def HeaderSentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_411).rebase (blkPl_411).base (Rust.withPanics ext)) (blkPl_411).base (headerSentEncodedLenSpec A)
def HeaderSentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_411).rebase (blkPl_411).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_411).base (headerSentEncodedLenPinnedSpec A)
def HeaderSentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_411).rebase (blkPl_411).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_411).base (headerSentEncodedLenSpec A)

theorem headerSentEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : HeaderSentEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked82_entry_pinned_ok_ext b A ext _ (Or.inl rfl))
theorem headerSentEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : HeaderSentEncodedLenLocal1OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked4EncodedLen_ok_of_pinned (unchunked82_entry_pinned_ok_ext b A ext _ (Or.inl rfl)))
theorem headerSentEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderSentEncodedLenLocal1PinnedOk b C A ctl abs :=
  headerSentEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem headerSentEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderSentEncodedLenLocal1Ok b C A ctl abs :=
  headerSentEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem headerSentEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : HeaderSentEncodedLenLocal2PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked82_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inl rfl)))
theorem headerSentEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : HeaderSentEncodedLenLocal2OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked4EncodedLen_ok_of_pinned (unchunked82_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inl rfl))))
theorem headerSentEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderSentEncodedLenLocal2PinnedOk b C A ctl abs :=
  headerSentEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem headerSentEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderSentEncodedLenLocal2Ok b C A ctl abs :=
  headerSentEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem headerSentEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : HeaderSentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked82_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩))
theorem headerSentEncodedLen_local1_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : HeaderSentEncodedLenLocal1PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked4EncodedLen_ok_of_pinned (unchunked82_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩)))
theorem headerSentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderSentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  headerSentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem headerSentEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderSentEncodedLenLocal1PlacedOk C A ctl abs :=
  headerSentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem headerSentEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : HeaderSentEncodedLenLocal2PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked82_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))
theorem headerSentEncodedLen_local2_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : HeaderSentEncodedLenLocal2PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked4EncodedLen_ok_of_pinned (unchunked82_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)))
theorem headerSentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderSentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  headerSentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem headerSentEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderSentEncodedLenLocal2PlacedOk C A ctl abs :=
  headerSentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def EkSentCt1ReceivedEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncodedLenLocal1Name) (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def EkSentCt1ReceivedEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncodedLenLocal1Name) (ekSentCt1ReceivedEncodedLenSpec A)
def EkSentCt1ReceivedEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ekSentCt1ReceivedEncodedLenLocal1Name) (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def EkSentCt1ReceivedEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ekSentCt1ReceivedEncodedLenLocal1Name) (ekSentCt1ReceivedEncodedLenSpec A)
def EkSentCt1ReceivedEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name) (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def EkSentCt1ReceivedEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name) (ekSentCt1ReceivedEncodedLenSpec A)
def EkSentCt1ReceivedEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name) (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def EkSentCt1ReceivedEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ekSentCt1ReceivedEncodedLenLocal2Name) (ekSentCt1ReceivedEncodedLenSpec A)
def EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_192).rebase (blkPl_192).base (Rust.withPanics ext)) (blkPl_192).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def EkSentCt1ReceivedEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_192).rebase (blkPl_192).base (Rust.withPanics ext)) (blkPl_192).base (ekSentCt1ReceivedEncodedLenSpec A)
def EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_192).rebase (blkPl_192).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_192).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def EkSentCt1ReceivedEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_192).rebase (blkPl_192).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_192).base (ekSentCt1ReceivedEncodedLenSpec A)
def EkSentCt1ReceivedEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_421).rebase (blkPl_421).base (Rust.withPanics ext)) (blkPl_421).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def EkSentCt1ReceivedEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_421).rebase (blkPl_421).base (Rust.withPanics ext)) (blkPl_421).base (ekSentCt1ReceivedEncodedLenSpec A)
def EkSentCt1ReceivedEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_421).rebase (blkPl_421).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_421).base (ekSentCt1ReceivedEncodedLenPinnedSpec A)
def EkSentCt1ReceivedEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_421).rebase (blkPl_421).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_421).base (ekSentCt1ReceivedEncodedLenSpec A)

theorem ekSentCt1ReceivedEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked82_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl))))
theorem ekSentCt1ReceivedEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal1OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked4EncodedLen_ok_of_pinned (unchunked82_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl)))))
theorem ekSentCt1ReceivedEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal1PinnedOk b C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ekSentCt1ReceivedEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal1Ok b C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ekSentCt1ReceivedEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal2PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked82_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr rfl))))
theorem ekSentCt1ReceivedEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal2OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked4EncodedLen_ok_of_pinned (unchunked82_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr rfl)))))
theorem ekSentCt1ReceivedEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal2PinnedOk b C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ekSentCt1ReceivedEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal2Ok b C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked82_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))
theorem ekSentCt1ReceivedEncodedLen_local1_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal1PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked4EncodedLen_ok_of_pinned (unchunked82_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)))
theorem ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ekSentCt1ReceivedEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal2PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked82_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩))
theorem ekSentCt1ReceivedEncodedLen_local2_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal2PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked4EncodedLen_ok_of_pinned (unchunked82_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩)))
theorem ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ekSentCt1ReceivedEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentCt1ReceivedEncodedLenLocal2PlacedOk C A ctl abs :=
  ekSentCt1ReceivedEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 2: 93-Instruction Group (`Ct1Sent`, `Ct1SentEkReceived`) -/

/-- Entry address predicate for all 4 functions in the 93-insn group. -/
def IsUnchunked93Entry (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ b abs, prog = tripleRatchetProgAtExt b abs ∧
    ((tripleRatchetProgAtExt b abs).fnAddr ct1SentEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr ct1SentEncodedLenLocal2Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr ct1SentEkReceivedEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr ct1SentEkReceivedEncodedLenLocal2Name = entry)) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    (prog = (@blkPC_180).rebase (@blkPl_180 inst).base H ∧ entry = (@blkPl_180 inst).base) ∨
    (prog = (@blkPC_408).rebase (@blkPl_408 inst).base H ∧ entry = (@blkPl_408 inst).base) ∨
    (prog = (@blkPC_162).rebase (@blkPl_162 inst).base H ∧ entry = (@blkPl_162 inst).base) ∨
    (prog = (@blkPC_387).rebase (@blkPl_387 inst).base H ∧ entry = (@blkPl_387 inst).base))

theorem unchunked93_fetch_entry {f : BitVec 64 → Option Instr}
    {a1 a2 a3 a4 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry ∨ a3 = entry ∨ a4 = entry)
    {ins : Instr}
    (h1 : f a1 = some ins) (h2 : f a2 = some ins)
    (h3 : f a3 = some ins) (h4 : f a4 = some ins) :
    f entry = some ins := by
  rcases hfn with rfl | rfl | rfl | rfl <;> assumption

theorem unchunked93_fetch_add {f : BitVec 64 → Option Instr}
    {a1 a2 a3 a4 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry ∨ a3 = entry ∨ a4 = entry)
    {k : Nat} {ins : Instr}
    (h1 : f (a1 + BitVec.ofNat 64 k) = some ins)
    (h2 : f (a2 + BitVec.ofNat 64 k) = some ins)
    (h3 : f (a3 + BitVec.ofNat 64 k) = some ins)
    (h4 : f (a4 + BitVec.ofNat 64 k) = some ins) :
    f (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl | rfl | rfl <;> assumption

theorem unchunked93_fetch_entry_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsUnchunked93Entry prog entry) {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct1SentEncodedLenLocal1Name) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct1SentEncodedLenLocal2Name) = some ins)
    (h3 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct1SentEkReceivedEncodedLenLocal1Name) = some ins)
    (h4 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct1SentEkReceivedEncodedLenLocal2Name) = some ins)
    (hb1 : ∀ [LibsignalPlacement] H, ((blkPC_180).rebase (blkPl_180).base H).fetch ((blkPl_180).base + 0#64) = some ins)
    (hb2 : ∀ [LibsignalPlacement] H, ((blkPC_408).rebase (blkPl_408).base H).fetch ((blkPl_408).base + 0#64) = some ins)
    (hb3 : ∀ [LibsignalPlacement] H, ((blkPC_162).rebase (blkPl_162).base H).fetch ((blkPl_162).base + 0#64) = some ins)
    (hb4 : ∀ [LibsignalPlacement] H, ((blkPC_387).rebase (blkPl_387).base H).fetch ((blkPl_387).base + 0#64) = some ins) :
    prog.fetch entry = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl | rfl | rfl⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · exact h3 b _
  · exact h4 b _
  · simpa using @hb1 inst H
  · simpa using @hb2 inst H
  · simpa using @hb3 inst H
  · simpa using @hb4 inst H

theorem unchunked93_fetch_add_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsUnchunked93Entry prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct1SentEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct1SentEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (h3 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct1SentEkReceivedEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h4 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct1SentEkReceivedEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (hb1 : ∀ [LibsignalPlacement] H, ((blkPC_180).rebase (blkPl_180).base H).fetch ((blkPl_180).base + BitVec.ofNat 64 k) = some ins)
    (hb2 : ∀ [LibsignalPlacement] H, ((blkPC_408).rebase (blkPl_408).base H).fetch ((blkPl_408).base + BitVec.ofNat 64 k) = some ins)
    (hb3 : ∀ [LibsignalPlacement] H, ((blkPC_162).rebase (blkPl_162).base H).fetch ((blkPl_162).base + BitVec.ofNat 64 k) = some ins)
    (hb4 : ∀ [LibsignalPlacement] H, ((blkPC_387).rebase (blkPl_387).base H).fetch ((blkPl_387).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl | rfl | rfl⟩ | ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · exact h3 b _
  · exact h4 b _
  · exact @hb1 inst H
  · exact @hb2 inst H
  · exact @hb3 inst H
  · exact @hb4 inst H

open Lean Elab Tactic in
elab "unchunked93_fetches_range " hfn:ident kStart:num kEnd:num : tactic => do
  let blks := #[180, 408, 162, 387]
  let offs := #[0x39a94, 0x63948, 0x388b8, 0x5ed84]
  let fnOffs := #[
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x39a94,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x63948,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x388b8,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x5ed84
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let hexK := String.ofList (Nat.toDigits 16 k)
    let decs := offs.map fun off => mkIdent (`CryptoVerification.SpqrV1.ProtoRepr |>.str s!"spqrUnchunked93Bin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let d0 := decs[0]!; let d1 := decs[1]!; let d2 := decs[2]!; let d3 := decs[3]!
    let f0 := fnOffs[0]!; let f1 := fnOffs[1]!; let f2 := fnOffs[2]!; let f3 := fnOffs[3]!
    let bIds := blks.map fun bi => mkIdent (Name.mkSimple s!"blkPC_{bi}_rebase_fetch_0x{hexK}")
    let b0 := bIds[0]!; let b1 := bIds[1]!; let b2 := bIds[2]!; let b3 := bIds[3]!
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := unchunked93_fetch_entry_prog $hfn (fun b H => $fetchEntry (b := b) (H := H) $f0 (by decide) $d0) (fun b H => $fetchEntry (b := b) (H := H) $f1 (by decide) $d1) (fun b H => $fetchEntry (b := b) (H := H) $f2 (by decide) $d2) (fun b H => $fetchEntry (b := b) (H := H) $f3 (by decide) $d3) (fun [LibsignalPlacement] H => $b0 _ H) (fun [LibsignalPlacement] H => $b1 _ H) (fun [LibsignalPlacement] H => $b2 _ H) (fun [LibsignalPlacement] H => $b3 _ H)))
    else
      evalTactic (← `(tactic| have := unchunked93_fetch_add_prog $hfn (k := $kq) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f0 (by decide) $d0) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f1 (by decide) $d1) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f2 (by decide) $d2) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f3 (by decide) $d3) (fun [LibsignalPlacement] H => $b0 _ H) (fun [LibsignalPlacement] H => $b1 _ H) (fun [LibsignalPlacement] H => $b2 _ H) (fun [LibsignalPlacement] H => $b3 _ H)))

theorem unchunked5Unpacked_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {a : BitVec 64}
    {epoch : BitVec 64} {auth : Option AuthenticatorPB} {f3 f4 f5 : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hm : m ⊨ unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ R) :
    OptAuthBounds g.auth auth ∧ VecU8FieldBounds f3 ∧ VecU8FieldBounds f4 ∧ VecU8FieldBounds f5 := by
  unfold unchunked5Unpacked at hm
  have ha : m ⊨ optAuthPayload A g.auth (a + 72#64) auth ∗
      ((a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
       ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
       ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
       ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ ((a + 120#64) ↦₆₄ epoch) ∗ R) := by convert hm using 1; ac_rfl
  have hf3 : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
       ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
       ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
       ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗ ((a + 120#64) ↦₆₄ epoch) ∗ R) := by convert hm using 1; ac_rfl
  have hf4 : m ⊨ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
       ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗
       ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
       ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗ ((a + 120#64) ↦₆₄ epoch) ∗ R) := by convert hm using 1; ac_rfl
  have hf5 : m ⊨ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
       ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
       ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗
       ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗ ((a + 120#64) ↦₆₄ epoch) ∗ R) := by convert hm using 1; ac_rfl
  exact ⟨optAuthPayload_bounds ha, vecU8Buf_fieldBounds hf3, vecU8Buf_fieldBounds hf4, vecU8Buf_fieldBounds hf5⟩

theorem step_unchunked93_epoch (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked93Entry prog entry)
    (g : Unchunked5PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hauth_b : OptAuthBounds g.auth auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if auth.isSome then entry + 56#64 else entry + 188#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) →
      EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm
        ((unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked93_fetches_range hfn 0 56
  obtain ⟨hcap_beq, hcap_bne, _⟩ := hauth_b
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch auth f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗ ((a + 120#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  by_cases hep : epoch = 0#64
  · apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen]) (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem step_unchunked93_auth_none (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked93Entry prog entry)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8)) (hauth : auth = none)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 188#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth
  unchunked93_fetches_range hfn 188 196
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP
  apply SepWPp.of_sepWP (mid := entry + 196#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem step_unchunked93_auth_some (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked93Entry prog entry)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hauth : auth = some au) (hauth_b : OptAuthBounds g.auth auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth
  unchunked93_fetches_range hfn 56 184
  obtain ⟨_, _, hroot_beq, hroot_bne, hmac_beq, hmac_bne⟩ := hauth_b.2.2 au rfl
  have hauth_fit : optAuthenticatorPBFieldEncodedLen (some au) < 2 ^ 64 := by
    unfold unchunked2EncodedLen at hfit; omega
  have hbody_lt : authenticatorPBEncodedLen au < 2 ^ 64 := by dsimp [optAuthenticatorPBFieldEncodedLen] at hauth_fit; omega
  have htot := bv_optAuthField_some au
  have hcmp := cmp_ls_false_of_lt (vlen := varintLen (BitVec.ofNat 64 (authenticatorPBEncodedLen au)))
    (tot := optAuthenticatorPBFieldEncodedLen (some au)) (by dsimp [optAuthenticatorPBFieldEncodedLen]; omega) hauth_fit
  rcases hcmp with ⟨hcmp1, hcmp2, hcmp3, hcmp4, hcmp5⟩
  obtain ⟨hadd_final, hccf1, hccf2, hccf3, hccf4⟩ :=
    adds_no_overflow_of_eq (a := optAuthenticatorPBFieldEncodedLen (some au)) (b := u64VarintFieldEncodedLen epoch)
      (c := unchunked2EncodedLen epoch (some au)) rfl hfit
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch (some au) f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ g.auth.rootKey.cap) ∗ ((a + 80#64) ↦₆₄ g.auth.rootKey.ptr) ∗ ((a + 88#64) ↦₆₄ BitVec.ofNat 64 au.rootKey.length) ∗
      vecU8Buf A g.auth.rootKey.cap g.auth.rootKey.ptr au.rootKey ∗
      ((a + 96#64) ↦₆₄ g.auth.macKey.cap) ∗ ((a + 104#64) ↦₆₄ g.auth.macKey.ptr) ∗ ((a + 112#64) ↦₆₄ BitVec.ofNat 64 au.macKey.length) ∗
      vecU8Buf A g.auth.macKey.cap g.auth.macKey.ptr au.macKey ∗ ((a + 120#64) ↦₆₄ epoch) := by
    simp only [unchunked5Unpacked, optAuthCap, optAuthPayload, arm64_norm]
  rw [hP1]
  cases hre : au.rootKey.isEmpty with
  | true =>
    have hr_len : au.rootKey.length = 0 := List.isEmpty_iff.mp hre |> congrArg List.length
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_00 : authenticatorPBEncodedLen au = 0 := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre, hme]
      have hopt_00 : optAuthenticatorPBFieldEncodedLen (some au) = 2 := by
        simp [optAuthenticatorPBFieldEncodedLen, hbody_00, varintLen]
      rw [hopt_00] at hadd_final hccf1 hccf2
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      have hbody_01 : bytesFieldEncodedLen au.macKey = authenticatorPBEncodedLen au := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre]
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc_r := bv_bytesField_nonempty hre
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_10 : bytesFieldEncodedLen au.rootKey = authenticatorPBEncodedLen au := by simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hme]
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
        adds_no_overflow_of_eq (a := bytesFieldEncodedLen au.macKey) (b := bytesFieldEncodedLen au.rootKey) (c := authenticatorPBEncodedLen au) rfl hbody_lt
      apply SepWPp.of_sepWP (mid := entry + 196#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem step_unchunked93_f3 (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked93Entry prog entry)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hf3_b : VecU8FieldBounds f3) (hfit : unchunked3EncodedLen epoch auth f3 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 196#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 240#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked93_fetches_range hfn 196 240
  obtain ⟨_, hf3_beq, hf3_bne⟩ := hf3_b
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch auth f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗ ((a + 120#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f3.isEmpty with
  | true =>
    have hf3_len : f3.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked2EncodedLen epoch auth = unchunked3EncodedLen epoch auth f3 := by
      simp [unchunked2EncodedLen, unchunked3EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := entry + 240#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f3) (b := unchunked2EncodedLen epoch auth) (c := unchunked3EncodedLen epoch auth f3) rfl hfit
    apply SepWPp.of_sepWP (mid := entry + 240#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem step_unchunked93_f4 (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked93Entry prog entry)
    (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hf4_b : VecU8FieldBounds f4) (hfit : unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 240#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3))
    (hP : P = unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 284#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked93_fetches_range hfn 240 284
  obtain ⟨_, hf4_beq, hf4_bne⟩ := hf4_b
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch auth f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗ ((a + 120#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f4.isEmpty with
  | true =>
    have hf4_len : f4.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked3EncodedLen epoch auth f3 = unchunked4EncodedLen epoch auth f3 f4 := by
      simp [unchunked3EncodedLen, unchunked4EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := entry + 284#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f4) (b := unchunked3EncodedLen epoch auth f3) (c := unchunked4EncodedLen epoch auth f3 f4) rfl hfit
    apply SepWPp.of_sepWP (mid := entry + 284#64); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

theorem step_unchunked93_f5 (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked93Entry prog entry)
    (g : Unchunked5PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8))
    (hf5_b : VecU8FieldBounds f5) (hfit : unchunked5EncodedLen epoch auth f3 f4 f5 < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 284#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗ ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked5EncodedLen epoch auth f3 f4 f5) →
      CalleeSavedPreserved s0 sf → Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  unchunked93_fetches_range hfn 284 336
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  obtain ⟨_, hf5_beq, hf5_bne⟩ := hf5_b
  subst hP
  have hP1 : unchunked5Unpacked A g a epoch auth f3 f4 f5 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗ vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
      ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗ vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
      ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗ ((a + 120#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f5.isEmpty with
  | true =>
    have hf5_len : f5.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked4EncodedLen epoch auth f3 f4 = unchunked5EncodedLen epoch auth f3 f4 f5 := by
      simp [unchunked4EncodedLen, unchunked5EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by epochEncLen_cc_close)
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f5) (b := unchunked4EncodedLen epoch auth f3 f4) (c := unchunked5EncodedLen epoch auth f3 f4 f5) rfl hfit
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr); wp_steps; apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by epochEncLen_cc_close)

/-- Shared `subroutine_ok` proof for all functions in the 93-insn group. -/
theorem unchunked93_entry_pinned_ok (prog : Program) (A : RustAlloc)
    (entry : BitVec 64) (hfn : IsUnchunked93Entry prog entry) :
    subroutine_ok prog entry (unchunked5EncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, epoch, auth, f3, f4, f5⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [unchunked5EncodedLenPinnedSpec, unchunked5PinnedAt_eq_unpacked,
    unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have hfit4 : unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64 := by
    unfold unchunked5EncodedLen unchunked4EncodedLen at *; omega
  have hfit3 : unchunked3EncodedLen epoch auth f3 < 2 ^ 64 := by
    unfold unchunked4EncodedLen unchunked3EncodedLen at *; omega
  have hfit2 : unchunked2EncodedLen epoch auth < 2 ^ 64 := by
    unfold unchunked3EncodedLen unchunked2EncodedLen at *; omega
  obtain ⟨hauth_b, hf3_b, hf4_b, hf5_b⟩ := unchunked5Unpacked_bounds hpre
  refine ⟨(unchunked5Unpacked A g a epoch auth f3 f4 f5 ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rw [sepConj_emp]; convert hpre using 1; ac_rfl, ?_⟩
  refine step_unchunked93_epoch (F := R) prog A entry hfn g a s0.sp v16 v8 epoch auth f3 f4 f5 hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp := ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine step_unchunked93_auth_none (F := FSave) prog A entry hfn g a epoch none f3 f4 f5 rfl hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine step_unchunked93_f3 (F := FSave) prog A entry hfn g a epoch none f3 f4 f5 hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    refine step_unchunked93_f4 (F := FSave) prog A entry hfn g a epoch none f3 f4 f5 hf4_b hfit4 hpc3 hrun3 hx0_3 hx8_3 (by dsimp [FSave]; ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
    have hsp4' : s4.sp = s0.sp - 16#64 := by rw [hsp4, hsp3, hsp2, hsp1]
    have hcs4' : EpochEncLenCalleeSaved s0 s4 := hcs1.trans (hcs2.trans (hcs3.trans hcs4))
    refine step_unchunked93_f5 (F := R) prog A entry hfn g a s0.sp epoch none f3 f4 f5 hf5_b hfit hpc4 hrun4 hsp4' halign hx0_4 hx8_4 hcs4' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f; rw [sepConj_emp] at hm_f
    simp only [unchunked5EncodedLenPinnedSpec, unchunked5PinnedAt_eq_unpacked, unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr4, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  · simp only [Option.isSome_some, ↓reduceIte] at hpc1
    refine step_unchunked93_auth_some (F := FSave) prog A entry hfn g a epoch (some au) au f3 f4 f5 rfl hauth_b hfit2 hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    refine step_unchunked93_f3 (F := FSave) prog A entry hfn g a epoch (some au) f3 f4 f5 hf3_b hfit3 hpc2 hrun2 hx0_2 hx8_2 (by dsimp [FSave]; ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
    refine step_unchunked93_f4 (F := FSave) prog A entry hfn g a epoch (some au) f3 f4 f5 hf4_b hfit4 hpc3 hrun3 hx0_3 hx8_3 (by dsimp [FSave]; ac_rfl) ?_
    intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
    have hsp4' : s4.sp = s0.sp - 16#64 := by rw [hsp4, hsp3, hsp2, hsp1]
    have hcs4' : EpochEncLenCalleeSaved s0 s4 := hcs1.trans (hcs2.trans (hcs3.trans hcs4))
    refine step_unchunked93_f5 (F := R) prog A entry hfn g a s0.sp epoch (some au) f3 f4 f5 hf5_b hfit hpc4 hrun4 hsp4' halign hx0_4 hx8_4 hcs4' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f; rw [sepConj_emp] at hm_f
    simp only [unchunked5EncodedLenPinnedSpec, unchunked5PinnedAt_eq_unpacked, unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr4, htr3, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

theorem unchunked93_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn :
      (tripleRatchetProgAtExt b ext).fnAddr ct1SentEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr ct1SentEncodedLenLocal2Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr ct1SentEkReceivedEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr ct1SentEkReceivedEncodedLenLocal2Name = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (unchunked5EncodedLenPinnedSpec A) :=
  unchunked93_entry_pinned_ok _ A entry (Or.inl ⟨b, ext, rfl, hfn⟩)

theorem unchunked5EncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (unchunked5EncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (unchunked5EncodedLenSpec A) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, epoch, auth, f3, f4, f5⟩ R s0 hpc hrun hpre hsp
  simp only [unchunked5EncodedLenSpec, unchunked5At_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome ⟨a, g, epoch, auth, f3, f4, f5⟩ R s0 hpc hrun hpre hsp).mono_outcome
    (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [unchunked5EncodedLenSpec, unchunked5At_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### Instantiations for `Ct1Sent` and `Ct1SentEkReceived` (`[local#1, #2]`) -/

def Ct1SentEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncodedLenLocal1Name) (ct1SentEncodedLenPinnedSpec A)
def Ct1SentEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncodedLenLocal1Name) (ct1SentEncodedLenSpec A)
def Ct1SentEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct1SentEncodedLenLocal1Name) (ct1SentEncodedLenPinnedSpec A)
def Ct1SentEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct1SentEncodedLenLocal1Name) (ct1SentEncodedLenSpec A)
def Ct1SentEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncodedLenLocal2Name) (ct1SentEncodedLenPinnedSpec A)
def Ct1SentEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncodedLenLocal2Name) (ct1SentEncodedLenSpec A)
def Ct1SentEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct1SentEncodedLenLocal2Name) (ct1SentEncodedLenPinnedSpec A)
def Ct1SentEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct1SentEncodedLenLocal2Name) (ct1SentEncodedLenSpec A)

theorem ct1SentEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked93_entry_pinned_ok_ext b A ext _ (Or.inl rfl))
theorem ct1SentEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEncodedLenLocal1OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked5EncodedLen_ok_of_pinned (unchunked93_entry_pinned_ok_ext b A ext _ (Or.inl rfl)))
theorem ct1SentEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEncodedLenLocal1PinnedOk b C A ctl abs :=
  ct1SentEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct1SentEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEncodedLenLocal1Ok b C A ctl abs :=
  ct1SentEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct1SentEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEncodedLenLocal2PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked93_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inl rfl)))
theorem ct1SentEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEncodedLenLocal2OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked5EncodedLen_ok_of_pinned (unchunked93_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inl rfl))))
theorem ct1SentEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEncodedLenLocal2PinnedOk b C A ctl abs :=
  ct1SentEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct1SentEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEncodedLenLocal2Ok b C A ctl abs :=
  ct1SentEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)

def Ct1SentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_180).rebase (blkPl_180).base (Rust.withPanics ext)) (blkPl_180).base (ct1SentEncodedLenPinnedSpec A)
def Ct1SentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_180).rebase (blkPl_180).base (Rust.withPanics ext)) (blkPl_180).base (ct1SentEncodedLenSpec A)
def Ct1SentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def Ct1SentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)
def Ct1SentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_408).rebase (blkPl_408).base (Rust.withPanics ext)) (blkPl_408).base (ct1SentEncodedLenPinnedSpec A)
def Ct1SentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_408).rebase (blkPl_408).base (Rust.withPanics ext)) (blkPl_408).base (ct1SentEncodedLenSpec A)
def Ct1SentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def Ct1SentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

theorem ct1SentEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked93_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩))
theorem ct1SentEncodedLen_local1_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEncodedLenLocal1PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked5EncodedLen_ok_of_pinned (unchunked93_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩)))
theorem ct1SentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ct1SentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ct1SentEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEncodedLenLocal1PlacedOk C A ctl abs :=
  ct1SentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ct1SentEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEncodedLenLocal2PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked93_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))
theorem ct1SentEncodedLen_local2_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEncodedLenLocal2PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked5EncodedLen_ok_of_pinned (unchunked93_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)))
theorem ct1SentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ct1SentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ct1SentEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEncodedLenLocal2PlacedOk C A ctl abs :=
  ct1SentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def Ct1SentEkReceivedEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEkReceivedEncodedLenLocal1Name) (ct1SentEkReceivedEncodedLenPinnedSpec A)
def Ct1SentEkReceivedEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEkReceivedEncodedLenLocal1Name) (ct1SentEkReceivedEncodedLenSpec A)
def Ct1SentEkReceivedEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct1SentEkReceivedEncodedLenLocal1Name) (ct1SentEkReceivedEncodedLenPinnedSpec A)
def Ct1SentEkReceivedEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct1SentEkReceivedEncodedLenLocal1Name) (ct1SentEkReceivedEncodedLenSpec A)
def Ct1SentEkReceivedEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEkReceivedEncodedLenLocal2Name) (ct1SentEkReceivedEncodedLenPinnedSpec A)
def Ct1SentEkReceivedEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEkReceivedEncodedLenLocal2Name) (ct1SentEkReceivedEncodedLenSpec A)
def Ct1SentEkReceivedEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct1SentEkReceivedEncodedLenLocal2Name) (ct1SentEkReceivedEncodedLenPinnedSpec A)
def Ct1SentEkReceivedEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct1SentEkReceivedEncodedLenLocal2Name) (ct1SentEkReceivedEncodedLenSpec A)

theorem ct1SentEkReceivedEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked93_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl))))
theorem ct1SentEkReceivedEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal1OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked5EncodedLen_ok_of_pinned (unchunked93_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl)))))
theorem ct1SentEkReceivedEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal1PinnedOk b C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct1SentEkReceivedEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal1Ok b C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct1SentEkReceivedEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal2PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked93_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr rfl))))
theorem ct1SentEkReceivedEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal2OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked5EncodedLen_ok_of_pinned (unchunked93_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr rfl)))))
theorem ct1SentEkReceivedEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal2PinnedOk b C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct1SentEkReceivedEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal2Ok b C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)

def Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_162).rebase (blkPl_162).base (Rust.withPanics ext)) (blkPl_162).base (ct1SentEkReceivedEncodedLenPinnedSpec A)
def Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_162).rebase (blkPl_162).base (Rust.withPanics ext)) (blkPl_162).base (ct1SentEkReceivedEncodedLenSpec A)
def Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def Ct1SentEkReceivedEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)
def Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_387).rebase (blkPl_387).base (Rust.withPanics ext)) (blkPl_387).base (ct1SentEkReceivedEncodedLenPinnedSpec A)
def Ct1SentEkReceivedEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_387).rebase (blkPl_387).base (Rust.withPanics ext)) (blkPl_387).base (ct1SentEkReceivedEncodedLenSpec A)
def Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)
def Ct1SentEkReceivedEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  Ct1SentEkReceivedEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

theorem ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked93_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))
theorem ct1SentEkReceivedEncodedLen_local1_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal1PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked5EncodedLen_ok_of_pinned (unchunked93_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)))
theorem ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ct1SentEkReceivedEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked93_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩))
theorem ct1SentEkReceivedEncodedLen_local2_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal2PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked5EncodedLen_ok_of_pinned (unchunked93_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩)))
theorem ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ct1SentEkReceivedEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct1SentEkReceivedEncodedLenLocal2PlacedOk C A ctl abs :=
  ct1SentEkReceivedEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end CryptoVerification.SpqrV1.ProtoRepr
