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
# Verification of 59- and 71-Instruction `V1State.Unchunked.*::encoded_len` Leaves

Parametric symbolic execution and `[local#1]` / `[local#2]` instantiations for the 59-instruction
(`KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent`) and 71-instruction (`EkSent`, `HeaderReceived`)
`V1State.Unchunked.*::encoded_len` leaf subroutines.
-/

@[expose] public section


namespace CryptoVerification
set_option maxRecDepth 2000000
gen_ls_blk 163
gen_ls_blk 172
gen_ls_blk 175
gen_ls_blk 189
gen_ls_blk 193
gen_ls_blk 389
gen_ls_blk 400
gen_ls_blk 404
gen_ls_blk 415
gen_ls_blk 424
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

/-! ## Part 1: 59-Instruction Group (`KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent`) -/

/-- Entry address predicate for all 6 functions in the 59-insn group. -/
def IsUnchunked59Entry (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ b abs, prog = tripleRatchetProgAtExt b abs ∧
    ((tripleRatchetProgAtExt b abs).fnAddr keysUnsampledEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr keysUnsampledEncodedLenLocal2Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr noHeaderReceivedEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr noHeaderReceivedEncodedLenLocal2Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr ct2SentEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr ct2SentEncodedLenLocal2Name = entry)) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    (prog = (@blkPC_172).rebase (@blkPl_172 inst).base H ∧ entry = (@blkPl_172 inst).base) ∨
    (prog = (@blkPC_400).rebase (@blkPl_400 inst).base H ∧ entry = (@blkPl_400 inst).base) ∨
    (prog = (@blkPC_193).rebase (@blkPl_193 inst).base H ∧ entry = (@blkPl_193 inst).base) ∨
    (prog = (@blkPC_424).rebase (@blkPl_424 inst).base H ∧ entry = (@blkPl_424 inst).base) ∨
    (prog = (@blkPC_163).rebase (@blkPl_163 inst).base H ∧ entry = (@blkPl_163 inst).base) ∨
    (prog = (@blkPC_389).rebase (@blkPl_389 inst).base H ∧ entry = (@blkPl_389 inst).base))

theorem unchunked59_fetch_entry {f : BitVec 64 → Option Instr}
    {a1 a2 a3 a4 a5 a6 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry ∨ a3 = entry ∨ a4 = entry ∨ a5 = entry ∨ a6 = entry)
    {ins : Instr}
    (h1 : f a1 = some ins) (h2 : f a2 = some ins) (h3 : f a3 = some ins)
    (h4 : f a4 = some ins) (h5 : f a5 = some ins) (h6 : f a6 = some ins) :
    f entry = some ins := by
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem unchunked59_fetch_add {f : BitVec 64 → Option Instr}
    {a1 a2 a3 a4 a5 a6 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry ∨ a3 = entry ∨ a4 = entry ∨ a5 = entry ∨ a6 = entry)
    {k : Nat} {ins : Instr}
    (h1 : f (a1 + BitVec.ofNat 64 k) = some ins)
    (h2 : f (a2 + BitVec.ofNat 64 k) = some ins)
    (h3 : f (a3 + BitVec.ofNat 64 k) = some ins)
    (h4 : f (a4 + BitVec.ofNat 64 k) = some ins)
    (h5 : f (a5 + BitVec.ofNat 64 k) = some ins)
    (h6 : f (a6 + BitVec.ofNat 64 k) = some ins) :
    f (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem unchunked59_fetch_entry_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsUnchunked59Entry prog entry) {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr keysUnsampledEncodedLenLocal1Name) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr keysUnsampledEncodedLenLocal2Name) = some ins)
    (h3 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr noHeaderReceivedEncodedLenLocal1Name) = some ins)
    (h4 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr noHeaderReceivedEncodedLenLocal2Name) = some ins)
    (h5 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct2SentEncodedLenLocal1Name) = some ins)
    (h6 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct2SentEncodedLenLocal2Name) = some ins)
    (hb1 : ∀ [LibsignalPlacement] H, ((blkPC_172).rebase (blkPl_172).base H).fetch ((blkPl_172).base + 0#64) = some ins)
    (hb2 : ∀ [LibsignalPlacement] H, ((blkPC_400).rebase (blkPl_400).base H).fetch ((blkPl_400).base + 0#64) = some ins)
    (hb3 : ∀ [LibsignalPlacement] H, ((blkPC_193).rebase (blkPl_193).base H).fetch ((blkPl_193).base + 0#64) = some ins)
    (hb4 : ∀ [LibsignalPlacement] H, ((blkPC_424).rebase (blkPl_424).base H).fetch ((blkPl_424).base + 0#64) = some ins)
    (hb5 : ∀ [LibsignalPlacement] H, ((blkPC_163).rebase (blkPl_163).base H).fetch ((blkPl_163).base + 0#64) = some ins)
    (hb6 : ∀ [LibsignalPlacement] H, ((blkPC_389).rebase (blkPl_389).base H).fetch ((blkPl_389).base + 0#64) = some ins) :
    prog.fetch entry = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · exact h3 b _
  · exact h4 b _
  · exact h5 b _
  · exact h6 b _
  · simpa using @hb1 inst H
  · simpa using @hb2 inst H
  · simpa using @hb3 inst H
  · simpa using @hb4 inst H
  · simpa using @hb5 inst H
  · simpa using @hb6 inst H

theorem unchunked59_fetch_add_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsUnchunked59Entry prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr keysUnsampledEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr keysUnsampledEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (h3 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr noHeaderReceivedEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h4 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr noHeaderReceivedEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (h5 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct2SentEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h6 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ct2SentEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (hb1 : ∀ [LibsignalPlacement] H, ((blkPC_172).rebase (blkPl_172).base H).fetch ((blkPl_172).base + BitVec.ofNat 64 k) = some ins)
    (hb2 : ∀ [LibsignalPlacement] H, ((blkPC_400).rebase (blkPl_400).base H).fetch ((blkPl_400).base + BitVec.ofNat 64 k) = some ins)
    (hb3 : ∀ [LibsignalPlacement] H, ((blkPC_193).rebase (blkPl_193).base H).fetch ((blkPl_193).base + BitVec.ofNat 64 k) = some ins)
    (hb4 : ∀ [LibsignalPlacement] H, ((blkPC_424).rebase (blkPl_424).base H).fetch ((blkPl_424).base + BitVec.ofNat 64 k) = some ins)
    (hb5 : ∀ [LibsignalPlacement] H, ((blkPC_163).rebase (blkPl_163).base H).fetch ((blkPl_163).base + BitVec.ofNat 64 k) = some ins)
    (hb6 : ∀ [LibsignalPlacement] H, ((blkPC_389).rebase (blkPl_389).base H).fetch ((blkPl_389).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨inst, H, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact h1 b _
  · exact h2 b _
  · exact h3 b _
  · exact h4 b _
  · exact h5 b _
  · exact h6 b _
  · exact @hb1 inst H
  · exact @hb2 inst H
  · exact @hb3 inst H
  · exact @hb4 inst H
  · exact @hb5 inst H
  · exact @hb6 inst H

open Lean Elab Tactic in
elab "unchunked59_fetches_range " hfn:ident kStart:num kEnd:num : tactic => do
  let blks := #[172, 400, 193, 424, 163, 389]
  let offs := #[0x38d84, 0x613cc, 0x3a478, 0x6796c, 0x38a2c, 0x5f2f0]
  let fnOffs := #[
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x38d84,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x613cc,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x3a478,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x6796c,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x38a2c,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x5f2f0
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let hexK := String.ofList (Nat.toDigits 16 k)
    let decs := offs.map fun off => mkIdent (`CryptoVerification.SpqrV1.ProtoRepr |>.str s!"spqrUnchunked59Bin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let d0 := decs[0]!; let d1 := decs[1]!; let d2 := decs[2]!; let d3 := decs[3]!; let d4 := decs[4]!; let d5 := decs[5]!
    let f0 := fnOffs[0]!; let f1 := fnOffs[1]!; let f2 := fnOffs[2]!; let f3 := fnOffs[3]!; let f4 := fnOffs[4]!; let f5 := fnOffs[5]!
    let bIds := blks.map fun bi => mkIdent (Name.mkSimple s!"blkPC_{bi}_rebase_fetch_0x{hexK}")
    let b0 := bIds[0]!; let b1 := bIds[1]!; let b2 := bIds[2]!; let b3 := bIds[3]!; let b4 := bIds[4]!; let b5 := bIds[5]!
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := unchunked59_fetch_entry_prog $hfn (fun b H => $fetchEntry (b := b) (H := H) $f0 (by decide) $d0) (fun b H => $fetchEntry (b := b) (H := H) $f1 (by decide) $d1) (fun b H => $fetchEntry (b := b) (H := H) $f2 (by decide) $d2) (fun b H => $fetchEntry (b := b) (H := H) $f3 (by decide) $d3) (fun b H => $fetchEntry (b := b) (H := H) $f4 (by decide) $d4) (fun b H => $fetchEntry (b := b) (H := H) $f5 (by decide) $d5) (fun [LibsignalPlacement] H => $b0 _ H) (fun [LibsignalPlacement] H => $b1 _ H) (fun [LibsignalPlacement] H => $b2 _ H) (fun [LibsignalPlacement] H => $b3 _ H) (fun [LibsignalPlacement] H => $b4 _ H) (fun [LibsignalPlacement] H => $b5 _ H)))
    else
      evalTactic (← `(tactic| have := unchunked59_fetch_add_prog $hfn (k := $kq) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f0 (by decide) $d0) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f1 (by decide) $d1) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f2 (by decide) $d2) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f3 (by decide) $d3) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f4 (by decide) $d4) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f5 (by decide) $d5) (fun [LibsignalPlacement] H => $b0 _ H) (fun [LibsignalPlacement] H => $b1 _ H) (fun [LibsignalPlacement] H => $b2 _ H) (fun [LibsignalPlacement] H => $b3 _ H) (fun [LibsignalPlacement] H => $b4 _ H) (fun [LibsignalPlacement] H => $b5 _ H)))

theorem unchunked2Unpacked_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {a : BitVec 64}
    {epoch : BitVec 64} {auth : Option AuthenticatorPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ unchunked2Unpacked A g a epoch auth ∗ R) :
    OptAuthBounds g auth := by
  unfold unchunked2Unpacked at hm
  have ha : m ⊨ optAuthPayload A g a auth ∗ ((a ↦₆₄ optAuthCap g auth) ∗ ((a + 48#64) ↦₆₄ epoch) ∗ R) := by
    convert hm using 1; ac_rfl
  exact optAuthPayload_bounds ha

/-- Prologue + `epoch` field length (`+0x000..+0x034`), branching to `+0x038` (`entry + 56#64`)
    when `auth.isSome` or `+0x0c0` (`entry + 192#64`) when `auth = none`. -/
theorem step_unchunked59_epoch (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked59Entry prog entry) (g : Unchunked2PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (hauth_b : OptAuthBounds g auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked2Unpacked A g a epoch auth ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (if auth.isSome then entry + 56#64 else entry + 192#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) → EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm ((unchunked2Unpacked A g a epoch auth ∗
        ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked59_fetches_range hfn 0 56
  obtain ⟨hcap_beq, hcap_bne, _⟩ := hauth_b; subst hP
  have hP1 : unchunked2Unpacked A g a epoch auth =
      (a ↦₆₄ optAuthCap g auth) ∗ optAuthPayload A g a auth ∗ ((a + 48#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  by_cases hep : epoch = 0#64
  · apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 192#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen])
      (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 192#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-- `auth = none` path (`+0x0c0..+0x0c4` -> `+0x0b8..+0x0bc: ldp, ret`). -/
theorem step_unchunked59_auth_none (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked59Entry prog entry) (g : Unchunked2PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (hauth : auth = none)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 192#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked2Unpacked A g a epoch auth ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      CalleeSavedPreserved s0 sf → Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  subst hauth; unchunked59_fetches_range hfn 184 200
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP; apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-- `auth = some au` path (`+0x038..+0x0bc: ldp, ret`). -/
theorem step_unchunked59_auth_some (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked59Entry prog entry) (g : Unchunked2PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB)
    (hauth : auth = some au) (hauth_b : OptAuthBounds g auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked2Unpacked A g a epoch auth ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      CalleeSavedPreserved s0 sf → Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  subst hauth; unchunked59_fetches_range hfn 56 192
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
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
  have hP1 : unchunked2Unpacked A g a epoch (some au) =
      (a ↦₆₄ g.rootKey.cap) ∗ ((a + 8#64) ↦₆₄ g.rootKey.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 au.rootKey.length) ∗ vecU8Buf A g.rootKey.cap g.rootKey.ptr au.rootKey ∗
      ((a + 24#64) ↦₆₄ g.macKey.cap) ∗ ((a + 32#64) ↦₆₄ g.macKey.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 au.macKey.length) ∗ vecU8Buf A g.macKey.cap g.macKey.ptr au.macKey ∗
      ((a + 48#64) ↦₆₄ epoch) := by
    simp only [unchunked2Unpacked, optAuthCap, optAuthPayload, arm64_norm]
  rw [hP1]
  cases hre : au.rootKey.isEmpty with
  | true =>
    have hr_len : au.rootKey.length = 0 := List.isEmpty_iff.mp hre |> congrArg List.length
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_00 : authenticatorPBEncodedLen au = 0 := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre, hme]
      have hopt_00 : optAuthenticatorPBFieldEncodedLen (some au) = 2 := by
        simp [optAuthenticatorPBFieldEncodedLen, hbody_00, varintLen]
      rw [hopt_00] at hadd_final hccf1 hccf2
      apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      apply SepWPp.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by epochEncLen_cc_close)
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      have hbody_01 : bytesFieldEncodedLen au.macKey = authenticatorPBEncodedLen au := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre]
      apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      apply SepWPp.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by epochEncLen_cc_close)
  | false =>
    have henc_r := bv_bytesField_nonempty hre
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_10 : bytesFieldEncodedLen au.rootKey = authenticatorPBEncodedLen au := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hme]
      apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      apply SepWPp.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by epochEncLen_cc_close)
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
        adds_no_overflow_of_eq (a := bytesFieldEncodedLen au.macKey)
          (b := bytesFieldEncodedLen au.rootKey) (c := authenticatorPBEncodedLen au) rfl hbody_lt
      apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      apply SepWPp.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by epochEncLen_cc_close)

/-- Shared `subroutine_ok` proof for all functions in the 59-insn group. -/
theorem unchunked59_entry_pinned_ok (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked59Entry prog entry) :
    subroutine_ok prog entry (unchunked2EncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, epoch, auth⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [unchunked2EncodedLenPinnedSpec, unchunked2PinnedAt_eq_unpacked,
    unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have hmem0 : s0.mem ⊨
      (unchunked2Unpacked A g a epoch auth ∗
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre using 1; ac_rfl
  have hauth_b := unchunked2Unpacked_bounds hpre
  refine ⟨(unchunked2Unpacked A g a epoch auth ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_unchunked59_epoch (F := R) prog A entry hfn g a s0.sp v16 v8 epoch auth
    hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine step_unchunked59_auth_none (F := R) prog A entry hfn g a s0.sp epoch none rfl
      hpc1 hrun1 hsp1 halign hx8_1 hcs1 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked2EncodedLenPinnedSpec, unchunked2PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  · simp only [Option.isSome_some, ↓reduceIte] at hpc1
    refine step_unchunked59_auth_some (F := R) prog A entry hfn g a s0.sp epoch (some au) au
      rfl hauth_b hfit hpc1 hrun1 hsp1 halign hx0_1 hx8_1 hcs1 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked2EncodedLenPinnedSpec, unchunked2PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

theorem unchunked59_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr keysUnsampledEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr keysUnsampledEncodedLenLocal2Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedEncodedLenLocal2Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr ct2SentEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr ct2SentEncodedLenLocal2Name = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (unchunked2EncodedLenPinnedSpec A) :=
  unchunked59_entry_pinned_ok _ A entry (Or.inl ⟨b, ext, rfl, hfn⟩)

theorem unchunked2EncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (unchunked2EncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (unchunked2EncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, epoch, auth⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [unchunked2EncodedLenSpec, unchunked2At_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, epoch, auth⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [unchunked2EncodedLenSpec, unchunked2At_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### Instantiations for `KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent` (`[local#1, #2]`) -/

private theorem subroutine_ok_repack {G1 G2 : Type} {prog : Program} {entry : BitVec 64}
    {S1 : Spec G1} {S2 : Spec G2} (f : G2 → G1)
    (hpre : ∀ x s, S2.pre x s = S1.pre (f x) s)
    (hpost : ∀ x s0 sf, S2.post x s0 sf = S1.post (f x) s0 sf)
    (hok : subroutine_ok prog entry S1)
    (honPanic : ∀ x s0 sf, S2.onPanic x s0 sf = S1.onPanic (f x) s0 sf := by intros; rfl)
    (honExit : ∀ x c s0 sf, S2.onExit x c s0 sf = S1.onExit (f x) c s0 sf := by intros; rfl)
    (honOom : ∀ x s0 sf, S2.onOom x s0 sf = S1.onOom (f x) s0 sf := by intros; rfl) :
    subroutine_ok prog entry S2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hsp => ?_
  rw [hpre] at hpre0
  refine hok.mono_outcome (f x) R s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost0⟩ | ⟨hpan, hmpan⟩ | ⟨code, hex, hmex⟩ | ⟨hoom, hmoom⟩
  · rw [← hpost] at hpost0; exact Or.inl ⟨hret, hcc, hpost0⟩
  · rw [← honPanic] at hmpan; exact Or.inr (Or.inl ⟨hpan, hmpan⟩)
  · rw [← honExit] at hmex; exact Or.inr (Or.inr (Or.inl ⟨code, hex, hmex⟩))
  · rw [← honOom] at hmoom; exact Or.inr (Or.inr (Or.inr ⟨hoom, hmoom⟩))

def KeysUnsampledEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr keysUnsampledEncodedLenLocal1Name) (keysUnsampledEncodedLenPinnedSpec A)
def KeysUnsampledEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr keysUnsampledEncodedLenLocal1Name) (keysUnsampledEncodedLenSpec A)
def KeysUnsampledEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr keysUnsampledEncodedLenLocal1Name) (keysUnsampledEncodedLenPinnedSpec A)
def KeysUnsampledEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr keysUnsampledEncodedLenLocal1Name) (keysUnsampledEncodedLenSpec A)
def KeysUnsampledEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr keysUnsampledEncodedLenLocal2Name) (keysUnsampledEncodedLenPinnedSpec A)
def KeysUnsampledEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr keysUnsampledEncodedLenLocal2Name) (keysUnsampledEncodedLenSpec A)
def KeysUnsampledEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr keysUnsampledEncodedLenLocal2Name) (keysUnsampledEncodedLenPinnedSpec A)
def KeysUnsampledEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr keysUnsampledEncodedLenLocal2Name) (keysUnsampledEncodedLenSpec A)
def KeysUnsampledEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_172).rebase (blkPl_172).base (Rust.withPanics ext)) (blkPl_172).base (keysUnsampledEncodedLenPinnedSpec A)
def KeysUnsampledEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_172).rebase (blkPl_172).base (Rust.withPanics ext)) (blkPl_172).base (keysUnsampledEncodedLenSpec A)
def KeysUnsampledEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_172).rebase (blkPl_172).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_172).base (keysUnsampledEncodedLenPinnedSpec A)
def KeysUnsampledEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_172).rebase (blkPl_172).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_172).base (keysUnsampledEncodedLenSpec A)
def KeysUnsampledEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_400).rebase (blkPl_400).base (Rust.withPanics ext)) (blkPl_400).base (keysUnsampledEncodedLenPinnedSpec A)
def KeysUnsampledEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_400).rebase (blkPl_400).base (Rust.withPanics ext)) (blkPl_400).base (keysUnsampledEncodedLenSpec A)
def KeysUnsampledEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_400).rebase (blkPl_400).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_400).base (keysUnsampledEncodedLenPinnedSpec A)
def KeysUnsampledEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_400).rebase (blkPl_400).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_400).base (keysUnsampledEncodedLenSpec A)

theorem keysUnsampledEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : KeysUnsampledEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inl rfl))
theorem keysUnsampledEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : KeysUnsampledEncodedLenLocal1OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inl rfl)))
theorem keysUnsampledEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : KeysUnsampledEncodedLenLocal1PinnedOk b C A ctl abs :=
  keysUnsampledEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem keysUnsampledEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : KeysUnsampledEncodedLenLocal1Ok b C A ctl abs :=
  keysUnsampledEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem keysUnsampledEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : KeysUnsampledEncodedLenLocal2PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inl rfl)))
theorem keysUnsampledEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : KeysUnsampledEncodedLenLocal2OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inl rfl))))
theorem keysUnsampledEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : KeysUnsampledEncodedLenLocal2PinnedOk b C A ctl abs :=
  keysUnsampledEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem keysUnsampledEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : KeysUnsampledEncodedLenLocal2Ok b C A ctl abs :=
  keysUnsampledEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem keysUnsampledEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : KeysUnsampledEncodedLenLocal1PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩))
theorem keysUnsampledEncodedLen_local1_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : KeysUnsampledEncodedLenLocal1PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩)))
theorem keysUnsampledEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : KeysUnsampledEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem keysUnsampledEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : KeysUnsampledEncodedLenLocal1PlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem keysUnsampledEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : KeysUnsampledEncodedLenLocal2PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))
theorem keysUnsampledEncodedLen_local2_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : KeysUnsampledEncodedLenLocal2PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)))
theorem keysUnsampledEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : KeysUnsampledEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem keysUnsampledEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : KeysUnsampledEncodedLenLocal2PlacedOk C A ctl abs :=
  keysUnsampledEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def NoHeaderReceivedEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedEncodedLenLocal1Name) (noHeaderReceivedEncodedLenPinnedSpec A)
def NoHeaderReceivedEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedEncodedLenLocal1Name) (noHeaderReceivedEncodedLenSpec A)
def NoHeaderReceivedEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr noHeaderReceivedEncodedLenLocal1Name) (noHeaderReceivedEncodedLenPinnedSpec A)
def NoHeaderReceivedEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr noHeaderReceivedEncodedLenLocal1Name) (noHeaderReceivedEncodedLenSpec A)
def NoHeaderReceivedEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedEncodedLenLocal2Name) (noHeaderReceivedEncodedLenPinnedSpec A)
def NoHeaderReceivedEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr noHeaderReceivedEncodedLenLocal2Name) (noHeaderReceivedEncodedLenSpec A)
def NoHeaderReceivedEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr noHeaderReceivedEncodedLenLocal2Name) (noHeaderReceivedEncodedLenPinnedSpec A)
def NoHeaderReceivedEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr noHeaderReceivedEncodedLenLocal2Name) (noHeaderReceivedEncodedLenSpec A)
def NoHeaderReceivedEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_193).rebase (blkPl_193).base (Rust.withPanics ext)) (blkPl_193).base (noHeaderReceivedEncodedLenPinnedSpec A)
def NoHeaderReceivedEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_193).rebase (blkPl_193).base (Rust.withPanics ext)) (blkPl_193).base (noHeaderReceivedEncodedLenSpec A)
def NoHeaderReceivedEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_193).rebase (blkPl_193).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_193).base (noHeaderReceivedEncodedLenPinnedSpec A)
def NoHeaderReceivedEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_193).rebase (blkPl_193).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_193).base (noHeaderReceivedEncodedLenSpec A)
def NoHeaderReceivedEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_424).rebase (blkPl_424).base (Rust.withPanics ext)) (blkPl_424).base (noHeaderReceivedEncodedLenPinnedSpec A)
def NoHeaderReceivedEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_424).rebase (blkPl_424).base (Rust.withPanics ext)) (blkPl_424).base (noHeaderReceivedEncodedLenSpec A)
def NoHeaderReceivedEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_424).rebase (blkPl_424).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_424).base (noHeaderReceivedEncodedLenPinnedSpec A)
def NoHeaderReceivedEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_424).rebase (blkPl_424).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_424).base (noHeaderReceivedEncodedLenSpec A)

theorem noHeaderReceivedEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl))))
theorem noHeaderReceivedEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal1OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl)))))
theorem noHeaderReceivedEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal1PinnedOk b C A ctl abs :=
  noHeaderReceivedEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem noHeaderReceivedEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal1Ok b C A ctl abs :=
  noHeaderReceivedEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem noHeaderReceivedEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal2PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
theorem noHeaderReceivedEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal2OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
theorem noHeaderReceivedEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal2PinnedOk b C A ctl abs :=
  noHeaderReceivedEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem noHeaderReceivedEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal2Ok b C A ctl abs :=
  noHeaderReceivedEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))
theorem noHeaderReceivedEncodedLen_local1_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal1PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)))
theorem noHeaderReceivedEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem noHeaderReceivedEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal2PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩))
theorem noHeaderReceivedEncodedLen_local2_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal2PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩)))
theorem noHeaderReceivedEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem noHeaderReceivedEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : NoHeaderReceivedEncodedLenLocal2PlacedOk C A ctl abs :=
  noHeaderReceivedEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def Ct2SentEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct2SentEncodedLenLocal1Name) (ct2SentEncodedLenPinnedSpec A)
def Ct2SentEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct2SentEncodedLenLocal1Name) (ct2SentEncodedLenSpec A)
def Ct2SentEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct2SentEncodedLenLocal1Name) (ct2SentEncodedLenPinnedSpec A)
def Ct2SentEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct2SentEncodedLenLocal1Name) (ct2SentEncodedLenSpec A)
def Ct2SentEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct2SentEncodedLenLocal2Name) (ct2SentEncodedLenPinnedSpec A)
def Ct2SentEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ct2SentEncodedLenLocal2Name) (ct2SentEncodedLenSpec A)
def Ct2SentEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct2SentEncodedLenLocal2Name) (ct2SentEncodedLenPinnedSpec A)
def Ct2SentEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ct2SentEncodedLenLocal2Name) (ct2SentEncodedLenSpec A)
def Ct2SentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_163).rebase (blkPl_163).base (Rust.withPanics ext)) (blkPl_163).base (ct2SentEncodedLenPinnedSpec A)
def Ct2SentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_163).rebase (blkPl_163).base (Rust.withPanics ext)) (blkPl_163).base (ct2SentEncodedLenSpec A)
def Ct2SentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_163).rebase (blkPl_163).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_163).base (ct2SentEncodedLenPinnedSpec A)
def Ct2SentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_163).rebase (blkPl_163).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_163).base (ct2SentEncodedLenSpec A)
def Ct2SentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_389).rebase (blkPl_389).base (Rust.withPanics ext)) (blkPl_389).base (ct2SentEncodedLenPinnedSpec A)
def Ct2SentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_389).rebase (blkPl_389).base (Rust.withPanics ext)) (blkPl_389).base (ct2SentEncodedLenSpec A)
def Ct2SentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_389).rebase (blkPl_389).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_389).base (ct2SentEncodedLenPinnedSpec A)
def Ct2SentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_389).rebase (blkPl_389).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_389).base (ct2SentEncodedLenSpec A)

theorem ct2SentEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct2SentEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
theorem ct2SentEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct2SentEncodedLenLocal1OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
theorem ct2SentEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct2SentEncodedLenLocal1PinnedOk b C A ctl abs :=
  ct2SentEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct2SentEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct2SentEncodedLenLocal1Ok b C A ctl abs :=
  ct2SentEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct2SentEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct2SentEncodedLenLocal2PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
theorem ct2SentEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Ct2SentEncodedLenLocal2OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
theorem ct2SentEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct2SentEncodedLenLocal2PinnedOk b C A ctl abs :=
  ct2SentEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct2SentEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct2SentEncodedLenLocal2Ok b C A ctl abs :=
  ct2SentEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ct2SentEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct2SentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩))
theorem ct2SentEncodedLen_local1_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct2SentEncodedLenLocal1PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)))
theorem ct2SentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct2SentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ct2SentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ct2SentEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct2SentEncodedLenLocal1PlacedOk C A ctl abs :=
  ct2SentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ct2SentEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct2SentEncodedLenLocal2PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩))
theorem ct2SentEncodedLen_local2_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Ct2SentEncodedLenLocal2PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked2EncodedLen_ok_of_pinned (unchunked59_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))⟩)))
theorem ct2SentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct2SentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ct2SentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ct2SentEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Ct2SentEncodedLenLocal2PlacedOk C A ctl abs :=
  ct2SentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## Part 2: 71-Instruction Group (`EkSent`, `HeaderReceived`) -/

/-- Entry address predicate for all 4 functions in the 71-insn group. -/
def IsUnchunked71Entry (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ b abs, prog = tripleRatchetProgAtExt b abs ∧
    ((tripleRatchetProgAtExt b abs).fnAddr ekSentEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr ekSentEncodedLenLocal2Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr headerReceivedEncodedLenLocal1Name = entry ∨
     (tripleRatchetProgAtExt b abs).fnAddr headerReceivedEncodedLenLocal2Name = entry)) ∨
  (∃ (inst : LibsignalPlacement) (H : String → Option (State → State)),
    (prog = (@blkPC_189).rebase (@blkPl_189 inst).base H ∧ entry = (@blkPl_189 inst).base) ∨
    (prog = (@blkPC_415).rebase (@blkPl_415 inst).base H ∧ entry = (@blkPl_415 inst).base) ∨
    (prog = (@blkPC_175).rebase (@blkPl_175 inst).base H ∧ entry = (@blkPl_175 inst).base) ∨
    (prog = (@blkPC_404).rebase (@blkPl_404 inst).base H ∧ entry = (@blkPl_404 inst).base))

theorem unchunked71_fetch_entry {f : BitVec 64 → Option Instr}
    {a1 a2 a3 a4 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry ∨ a3 = entry ∨ a4 = entry)
    {ins : Instr}
    (h1 : f a1 = some ins) (h2 : f a2 = some ins)
    (h3 : f a3 = some ins) (h4 : f a4 = some ins) :
    f entry = some ins := by
  rcases hfn with rfl | rfl | rfl | rfl <;> assumption

theorem unchunked71_fetch_add {f : BitVec 64 → Option Instr}
    {a1 a2 a3 a4 entry : BitVec 64}
    (hfn : a1 = entry ∨ a2 = entry ∨ a3 = entry ∨ a4 = entry)
    {k : Nat} {ins : Instr}
    (h1 : f (a1 + BitVec.ofNat 64 k) = some ins)
    (h2 : f (a2 + BitVec.ofNat 64 k) = some ins)
    (h3 : f (a3 + BitVec.ofNat 64 k) = some ins)
    (h4 : f (a4 + BitVec.ofNat 64 k) = some ins) :
    f (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with rfl | rfl | rfl | rfl <;> assumption

theorem unchunked71_fetch_entry_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsUnchunked71Entry prog entry) {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ekSentEncodedLenLocal1Name) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ekSentEncodedLenLocal2Name) = some ins)
    (h3 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr headerReceivedEncodedLenLocal1Name) = some ins)
    (h4 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr headerReceivedEncodedLenLocal2Name) = some ins)
    (hb1 : ∀ [LibsignalPlacement] H, ((blkPC_189).rebase (blkPl_189).base H).fetch ((blkPl_189).base + 0#64) = some ins)
    (hb2 : ∀ [LibsignalPlacement] H, ((blkPC_415).rebase (blkPl_415).base H).fetch ((blkPl_415).base + 0#64) = some ins)
    (hb3 : ∀ [LibsignalPlacement] H, ((blkPC_175).rebase (blkPl_175).base H).fetch ((blkPl_175).base + 0#64) = some ins)
    (hb4 : ∀ [LibsignalPlacement] H, ((blkPC_404).rebase (blkPl_404).base H).fetch ((blkPl_404).base + 0#64) = some ins) :
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

theorem unchunked71_fetch_add_prog {prog : Program} {entry : BitVec 64}
    (hfn : IsUnchunked71Entry prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ekSentEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr ekSentEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (h3 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr headerReceivedEncodedLenLocal1Name + BitVec.ofNat 64 k) = some ins)
    (h4 : ∀ b H, (libsignalSessionCode.rebase b H).fetch ((libsignalSessionCode.rebase b H).fnAddr headerReceivedEncodedLenLocal2Name + BitVec.ofNat 64 k) = some ins)
    (hb1 : ∀ [LibsignalPlacement] H, ((blkPC_189).rebase (blkPl_189).base H).fetch ((blkPl_189).base + BitVec.ofNat 64 k) = some ins)
    (hb2 : ∀ [LibsignalPlacement] H, ((blkPC_415).rebase (blkPl_415).base H).fetch ((blkPl_415).base + BitVec.ofNat 64 k) = some ins)
    (hb3 : ∀ [LibsignalPlacement] H, ((blkPC_175).rebase (blkPl_175).base H).fetch ((blkPl_175).base + BitVec.ofNat 64 k) = some ins)
    (hb4 : ∀ [LibsignalPlacement] H, ((blkPC_404).rebase (blkPl_404).base H).fetch ((blkPl_404).base + BitVec.ofNat 64 k) = some ins) :
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
elab "unchunked71_fetches_range " hfn:ident kStart:num kEnd:num : tactic => do
  let blks := #[189, 415, 175, 404]
  let offs := #[0x3a1cc, 0x64d94, 0x38fe0, 0x626c4]
  let fnOffs := #[
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x3a1cc,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x64d94,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x38fe0,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x626c4
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let hexK := String.ofList (Nat.toDigits 16 k)
    let decs := offs.map fun off => mkIdent (`CryptoVerification.SpqrV1.ProtoRepr |>.str s!"spqrUnchunked71Bin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let d0 := decs[0]!; let d1 := decs[1]!; let d2 := decs[2]!; let d3 := decs[3]!
    let f0 := fnOffs[0]!; let f1 := fnOffs[1]!; let f2 := fnOffs[2]!; let f3 := fnOffs[3]!
    let bIds := blks.map fun bi => mkIdent (Name.mkSimple s!"blkPC_{bi}_rebase_fetch_0x{hexK}")
    let b0 := bIds[0]!; let b1 := bIds[1]!; let b2 := bIds[2]!; let b3 := bIds[3]!
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := unchunked71_fetch_entry_prog $hfn (fun b H => $fetchEntry (b := b) (H := H) $f0 (by decide) $d0) (fun b H => $fetchEntry (b := b) (H := H) $f1 (by decide) $d1) (fun b H => $fetchEntry (b := b) (H := H) $f2 (by decide) $d2) (fun b H => $fetchEntry (b := b) (H := H) $f3 (by decide) $d3) (fun [LibsignalPlacement] H => $b0 _ H) (fun [LibsignalPlacement] H => $b1 _ H) (fun [LibsignalPlacement] H => $b2 _ H) (fun [LibsignalPlacement] H => $b3 _ H)))
    else
      evalTactic (← `(tactic| have := unchunked71_fetch_add_prog $hfn (k := $kq) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f0 (by decide) $d0) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f1 (by decide) $d1) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f2 (by decide) $d2) (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f3 (by decide) $d3) (fun [LibsignalPlacement] H => $b0 _ H) (fun [LibsignalPlacement] H => $b1 _ H) (fun [LibsignalPlacement] H => $b2 _ H) (fun [LibsignalPlacement] H => $b3 _ H)))

theorem unchunked3Unpacked_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {a : BitVec 64}
    {epoch : BitVec 64} {auth : Option AuthenticatorPB} {f3 : List (BitVec 8)} {R : SepProp} {m : Memory}
    (hm : m ⊨ unchunked3Unpacked A g a epoch auth f3 ∗ R) :
    OptAuthBounds g.auth auth ∧ VecU8FieldBounds f3 := by
  unfold unchunked3Unpacked at hm
  have ha : m ⊨ optAuthPayload A g.auth (a + 24#64) auth ∗
      ((a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
       vecU8Buf A g.f3.cap g.f3.ptr f3 ∗ ((a + 24#64) ↦₆₄ optAuthCap g.auth auth) ∗ ((a + 72#64) ↦₆₄ epoch) ∗ R) := by
    convert hm using 1; ac_rfl
  have hf3 : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
       ((a + 24#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 24#64) auth ∗ ((a + 72#64) ↦₆₄ epoch) ∗ R) := by
    convert hm using 1; ac_rfl
  exact ⟨optAuthPayload_bounds ha, vecU8Buf_fieldBounds hf3⟩

/-- Prologue + `epoch` field length (`+0x000..+0x034`), branching to `+0x038` (`entry + 56#64`)
    when `auth.isSome` or `+0x0bc` (`entry + 188#64`) when `auth = none`. -/
theorem step_unchunked71_epoch (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked71Entry prog entry) (g : Unchunked3PBGhost) (a sp v16 v8 : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8))
    (hauth_b : OptAuthBounds g.auth auth)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (unchunked3Unpacked A g a epoch auth f3 ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (if auth.isSome then entry + 56#64 else entry + 188#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch) → EpochEncLenCalleeSaved s sm →
      SepWPp prog ret sm ((unchunked3Unpacked A g a epoch auth f3 ∗
        ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  unchunked71_fetches_range hfn 0 56
  obtain ⟨hcap_beq, hcap_bne, _⟩ := hauth_b; subst hP
  have hP1 : unchunked3Unpacked A g a epoch auth f3 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr f3 ∗ ((a + 24#64) ↦₆₄ optAuthCap g.auth auth) ∗
      optAuthPayload A g.auth (a + 24#64) auth ∗ ((a + 72#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  by_cases hep : epoch = 0#64
  · apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [u64VarintFieldEncodedLen])
      (by simp_all [EpochEncLenCalleeSaved])
  · have hep_beq : (epoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep
    have hep_bne : (epoch != 0#64) = true := bne_iff_ne.mpr hep
    have henc := bv_u64VarintField_nonzero hep
    apply SepWPp.of_sepWP (mid := if auth.isSome then entry + 56#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases auth <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases auth <;> simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EpochEncLenCalleeSaved])

/-- `auth = none` path (`+0x0bc..+0x0c0` -> `+0x0c4` = `entry + 196#64`). -/
theorem step_unchunked71_auth_none (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked71Entry prog entry) (g : Unchunked3PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8)) (hauth : auth = none)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 188#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked3Unpacked A g a epoch auth f3 ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth; unchunked71_fetches_range hfn 188 196
  have hlen_eq : unchunked2EncodedLen epoch none = u64VarintFieldEncodedLen epoch := by
    simp [unchunked2EncodedLen, optAuthenticatorPBFieldEncodedLen]
  subst hP; apply SepWPp.of_sepWP (mid := entry + 196#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- `auth = some au` path (`+0x038..+0x0b4` -> `+0x0c4` = `entry + 196#64`). -/
theorem step_unchunked71_auth_some (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked71Entry prog entry) (g : Unchunked3PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (au : AuthenticatorPB) (f3 : List (BitVec 8))
    (hauth : auth = some au) (hauth_b : OptAuthBounds g.auth auth)
    (hfit : unchunked2EncodedLen epoch auth < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (u64VarintFieldEncodedLen epoch))
    (hP : P = unchunked3Unpacked A g a epoch auth f3 ∗ F)
    (hnext : ∀ sm : State, sm.pc = entry + 196#64 → sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace →
      sm.readReg64 .x0 = a → sm.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) →
      EpochEncLenCalleeSaved s sm → SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hauth; unchunked71_fetches_range hfn 56 184
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
  have hP1 : unchunked3Unpacked A g a epoch (some au) f3 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗ vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ g.auth.rootKey.cap) ∗ ((a + 32#64) ↦₆₄ g.auth.rootKey.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 au.rootKey.length) ∗ vecU8Buf A g.auth.rootKey.cap g.auth.rootKey.ptr au.rootKey ∗
      ((a + 48#64) ↦₆₄ g.auth.macKey.cap) ∗ ((a + 56#64) ↦₆₄ g.auth.macKey.ptr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 au.macKey.length) ∗ vecU8Buf A g.auth.macKey.cap g.auth.macKey.ptr au.macKey ∗
      ((a + 72#64) ↦₆₄ epoch) := by
    simp only [unchunked3Unpacked, optAuthCap, optAuthPayload, arm64_norm]
  rw [hP1]
  cases hre : au.rootKey.isEmpty with
  | true =>
    have hr_len : au.rootKey.length = 0 := List.isEmpty_iff.mp hre |> congrArg List.length
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_00 : authenticatorPBEncodedLen au = 0 := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre, hme]
      have hopt_00 : optAuthenticatorPBFieldEncodedLen (some au) = 2 := by
        simp [optAuthenticatorPBFieldEncodedLen, hbody_00, varintLen]
      rw [hopt_00] at hadd_final hccf1 hccf2
      apply SepWPp.of_sepWP (mid := entry + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      have hbody_01 : bytesFieldEncodedLen au.macKey = authenticatorPBEncodedLen au := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hre]
      apply SepWPp.of_sepWP (mid := entry + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
  | false =>
    have henc_r := bv_bytesField_nonempty hre
    cases hme : au.macKey.isEmpty with
    | true =>
      have hm_len : au.macKey.length = 0 := List.isEmpty_iff.mp hme |> congrArg List.length
      have hbody_10 : bytesFieldEncodedLen au.rootKey = authenticatorPBEncodedLen au := by
        simp [authenticatorPBEncodedLen, bytesFieldEncodedLen, hme]
      apply SepWPp.of_sepWP (mid := entry + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])
    | false =>
      have henc_m := bv_bytesField_nonempty hme
      obtain ⟨hadd_body, hcc1, hcc2, hcc3, hcc4⟩ :=
        adds_no_overflow_of_eq (a := bytesFieldEncodedLen au.macKey)
          (b := bytesFieldEncodedLen au.rootKey)
          (c := authenticatorPBEncodedLen au) rfl hbody_lt
      apply SepWPp.of_sepWP (mid := entry + 196#64)
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      rw [← hP1]
      exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EpochEncLenCalleeSaved])

/-- Tag-3 `f3: Vec<u8>` field length + epilogue (`+0x0c4..+0x0f4: ldp, ret`). -/
theorem step_unchunked71_f3 (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked71Entry prog entry)
    (g : Unchunked3PBGhost) (a sp : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8))
    (hf3_b : VecU8FieldBounds f3)
    (hfit : unchunked3EncodedLen epoch auth f3 < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 196#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth))
    (hcs : EpochEncLenCalleeSaved s0 s)
    (hP : P = (unchunked3Unpacked A g a epoch auth f3 ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) →
      CalleeSavedPreserved s0 sf → Q sf P) :
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  unchunked71_fetches_range hfn 196 248
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  obtain ⟨_, hf3_beq, hf3_bne⟩ := hf3_b
  subst hP
  have hP1 : unchunked3Unpacked A g a epoch auth f3 =
      (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
      ((a + 24#64) ↦₆₄ optAuthCap g.auth auth) ∗
      optAuthPayload A g.auth (a + 24#64) auth ∗
      ((a + 72#64) ↦₆₄ epoch) := rfl
  rw [hP1]
  cases hfe : f3.isEmpty with
  | true =>
    have hf_len : f3.length = 0 := List.isEmpty_iff.mp hfe |> congrArg List.length
    have htot_eq : unchunked2EncodedLen epoch auth = unchunked3EncodedLen epoch auth f3 := by
      simp [unchunked2EncodedLen, unchunked3EncodedLen, bytesFieldEncodedLen, hfe]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)
  | false =>
    have henc := bv_bytesField_nonempty hfe
    obtain ⟨hadd, hcc1, hcc2, hcc3, hcc4⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen f3)
        (b := unchunked2EncodedLen epoch auth)
        (c := unchunked3EncodedLen epoch auth f3) rfl hfit
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPp.done (by simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

/-- Shared `subroutine_ok` proof for all functions in the 71-insn group. -/
theorem unchunked71_entry_pinned_ok (prog : Program) (A : RustAlloc) (entry : BitVec 64)
    (hfn : IsUnchunked71Entry prog entry) :
    subroutine_ok prog entry (unchunked3EncodedLenPinnedSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, epoch, auth, f3⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [unchunked3EncodedLenPinnedSpec, unchunked3PinnedAt_eq_unpacked,
    unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have hfit2 : unchunked2EncodedLen epoch auth < 2 ^ 64 := by
    unfold unchunked3EncodedLen unchunked2EncodedLen at *; omega
  have hmem0 : s0.mem ⊨
      (unchunked3Unpacked A g a epoch auth f3 ∗
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre using 1; ac_rfl
  obtain ⟨hauth_b, hf3_b⟩ := unchunked3Unpacked_bounds hpre
  refine ⟨(unchunked3Unpacked A g a epoch auth f3 ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_unchunked71_epoch (F := R) prog A entry hfn g a s0.sp v16 v8 epoch auth f3
    hauth_b hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  rcases auth with _ | au
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine step_unchunked71_auth_none (F := FSave) prog A entry hfn g a epoch none f3 rfl
      hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    have hsp2' : s2.sp = s0.sp - 16#64 := by rw [hsp2, hsp1]
    have hcs2' : EpochEncLenCalleeSaved s0 s2 := hcs1.trans hcs2
    refine step_unchunked71_f3 (F := R) prog A entry hfn g a s0.sp epoch none f3
      hf3_b hfit hpc2 hrun2 hsp2' halign hx0_2 hx8_2 hcs2' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked3EncodedLenPinnedSpec, unchunked3PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl
  · simp only [Option.isSome_some, ↓reduceIte] at hpc1
    refine step_unchunked71_auth_some (F := FSave) prog A entry hfn g a epoch (some au) au f3
      rfl hauth_b hfit2 hpc1 hrun1 hx0_1 hx8_1 (by dsimp [FSave]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
    have hsp2' : s2.sp = s0.sp - 16#64 := by rw [hsp2, hsp1]
    have hcs2' : EpochEncLenCalleeSaved s0 s2 := hcs1.trans hcs2
    refine step_unchunked71_f3 (F := R) prog A entry hfn g a s0.sp epoch (some au) f3
      hf3_b hfit hpc2 hrun2 hsp2' halign hx0_2 hx8_2 hcs2' rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [sepConj_emp] at hm_f
    simp only [unchunked3EncodedLenPinnedSpec, unchunked3PinnedAt_eq_unpacked,
      unchunkedEncodedLenStack, stackAt_epochEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, by rw [htrf, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; ac_rfl

theorem unchunked71_entry_pinned_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (entry : BitVec 64)
    (hfn : (tripleRatchetProgAtExt b ext).fnAddr ekSentEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr ekSentEncodedLenLocal2Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr headerReceivedEncodedLenLocal1Name = entry ∨
      (tripleRatchetProgAtExt b ext).fnAddr headerReceivedEncodedLenLocal2Name = entry) :
    subroutine_ok (tripleRatchetProgAtExt b ext) entry (unchunked3EncodedLenPinnedSpec A) :=
  unchunked71_entry_pinned_ok _ A entry (Or.inl ⟨b, ext, rfl, hfn⟩)

theorem unchunked3EncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (unchunked3EncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (unchunked3EncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, epoch, auth, f3⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [unchunked3EncodedLenSpec, unchunked3At_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, epoch, auth, f3⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [unchunked3EncodedLenSpec, unchunked3At_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ### Instantiations for `EkSent` and `HeaderReceived` (`[local#1, #2]`) -/

def EkSentEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekSentEncodedLenLocal1Name) (ekSentEncodedLenPinnedSpec A)
def EkSentEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekSentEncodedLenLocal1Name) (ekSentEncodedLenSpec A)
def EkSentEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ekSentEncodedLenLocal1Name) (ekSentEncodedLenPinnedSpec A)
def EkSentEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ekSentEncodedLenLocal1Name) (ekSentEncodedLenSpec A)
def EkSentEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekSentEncodedLenLocal2Name) (ekSentEncodedLenPinnedSpec A)
def EkSentEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekSentEncodedLenLocal2Name) (ekSentEncodedLenSpec A)
def EkSentEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ekSentEncodedLenLocal2Name) (ekSentEncodedLenPinnedSpec A)
def EkSentEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ekSentEncodedLenLocal2Name) (ekSentEncodedLenSpec A)
def EkSentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_189).rebase (blkPl_189).base (Rust.withPanics ext)) (blkPl_189).base (ekSentEncodedLenPinnedSpec A)
def EkSentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_189).rebase (blkPl_189).base (Rust.withPanics ext)) (blkPl_189).base (ekSentEncodedLenSpec A)
def EkSentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_189).rebase (blkPl_189).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_189).base (ekSentEncodedLenPinnedSpec A)
def EkSentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_189).rebase (blkPl_189).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_189).base (ekSentEncodedLenSpec A)
def EkSentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_415).rebase (blkPl_415).base (Rust.withPanics ext)) (blkPl_415).base (ekSentEncodedLenPinnedSpec A)
def EkSentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_415).rebase (blkPl_415).base (Rust.withPanics ext)) (blkPl_415).base (ekSentEncodedLenSpec A)
def EkSentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_415).rebase (blkPl_415).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_415).base (ekSentEncodedLenPinnedSpec A)
def EkSentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_415).rebase (blkPl_415).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_415).base (ekSentEncodedLenSpec A)

theorem ekSentEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : EkSentEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked71_entry_pinned_ok_ext b A ext _ (Or.inl rfl))
theorem ekSentEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : EkSentEncodedLenLocal1OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked3EncodedLen_ok_of_pinned (unchunked71_entry_pinned_ok_ext b A ext _ (Or.inl rfl)))
theorem ekSentEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentEncodedLenLocal1PinnedOk b C A ctl abs :=
  ekSentEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ekSentEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentEncodedLenLocal1Ok b C A ctl abs :=
  ekSentEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ekSentEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : EkSentEncodedLenLocal2PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked71_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inl rfl)))
theorem ekSentEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : EkSentEncodedLenLocal2OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked3EncodedLen_ok_of_pinned (unchunked71_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inl rfl))))
theorem ekSentEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentEncodedLenLocal2PinnedOk b C A ctl abs :=
  ekSentEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ekSentEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentEncodedLenLocal2Ok b C A ctl abs :=
  ekSentEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem ekSentEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : EkSentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked71_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩))
theorem ekSentEncodedLen_local1_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : EkSentEncodedLenLocal1PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked3EncodedLen_ok_of_pinned (unchunked71_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inl ⟨rfl, rfl⟩⟩)))
theorem ekSentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  ekSentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ekSentEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentEncodedLenLocal1PlacedOk C A ctl abs :=
  ekSentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ekSentEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : EkSentEncodedLenLocal2PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked71_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩))
theorem ekSentEncodedLen_local2_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : EkSentEncodedLenLocal2PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.dk⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked3EncodedLen_ok_of_pinned (unchunked71_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)))
theorem ekSentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  ekSentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem ekSentEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : EkSentEncodedLenLocal2PlacedOk C A ctl abs :=
  ekSentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

def HeaderReceivedEncodedLenLocal1PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr headerReceivedEncodedLenLocal1Name) (headerReceivedEncodedLenPinnedSpec A)
def HeaderReceivedEncodedLenLocal1OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr headerReceivedEncodedLenLocal1Name) (headerReceivedEncodedLenSpec A)
def HeaderReceivedEncodedLenLocal1PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr headerReceivedEncodedLenLocal1Name) (headerReceivedEncodedLenPinnedSpec A)
def HeaderReceivedEncodedLenLocal1Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr headerReceivedEncodedLenLocal1Name) (headerReceivedEncodedLenSpec A)
def HeaderReceivedEncodedLenLocal2PinnedOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr headerReceivedEncodedLenLocal2Name) (headerReceivedEncodedLenPinnedSpec A)
def HeaderReceivedEncodedLenLocal2OkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr headerReceivedEncodedLenLocal2Name) (headerReceivedEncodedLenSpec A)
def HeaderReceivedEncodedLenLocal2PinnedOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr headerReceivedEncodedLenLocal2Name) (headerReceivedEncodedLenPinnedSpec A)
def HeaderReceivedEncodedLenLocal2Ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr headerReceivedEncodedLenLocal2Name) (headerReceivedEncodedLenSpec A)
def HeaderReceivedEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_175).rebase (blkPl_175).base (Rust.withPanics ext)) (blkPl_175).base (headerReceivedEncodedLenPinnedSpec A)
def HeaderReceivedEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_175).rebase (blkPl_175).base (Rust.withPanics ext)) (blkPl_175).base (headerReceivedEncodedLenSpec A)
def HeaderReceivedEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_175).rebase (blkPl_175).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_175).base (headerReceivedEncodedLenPinnedSpec A)
def HeaderReceivedEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_175).rebase (blkPl_175).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_175).base (headerReceivedEncodedLenSpec A)
def HeaderReceivedEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_404).rebase (blkPl_404).base (Rust.withPanics ext)) (blkPl_404).base (headerReceivedEncodedLenPinnedSpec A)
def HeaderReceivedEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_404).rebase (blkPl_404).base (Rust.withPanics ext)) (blkPl_404).base (headerReceivedEncodedLenSpec A)
def HeaderReceivedEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_404).rebase (blkPl_404).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_404).base (headerReceivedEncodedLenPinnedSpec A)
def HeaderReceivedEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_404).rebase (blkPl_404).base (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_404).base (headerReceivedEncodedLenSpec A)

theorem headerReceivedEncodedLen_local1_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : HeaderReceivedEncodedLenLocal1PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked71_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl))))
theorem headerReceivedEncodedLen_local1_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : HeaderReceivedEncodedLenLocal1OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked3EncodedLen_ok_of_pinned (unchunked71_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inl rfl)))))
theorem headerReceivedEncodedLen_local1_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderReceivedEncodedLenLocal1PinnedOk b C A ctl abs :=
  headerReceivedEncodedLen_local1_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem headerReceivedEncodedLen_local1_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderReceivedEncodedLenLocal1Ok b C A ctl abs :=
  headerReceivedEncodedLen_local1_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem headerReceivedEncodedLen_local2_pinned_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : HeaderReceivedEncodedLenLocal2PinnedOkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked71_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr rfl))))
theorem headerReceivedEncodedLen_local2_ok_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : HeaderReceivedEncodedLenLocal2OkExt b A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked3EncodedLen_ok_of_pinned (unchunked71_entry_pinned_ok_ext b A ext _ (Or.inr (Or.inr (Or.inr rfl)))))
theorem headerReceivedEncodedLen_local2_pinned_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderReceivedEncodedLenLocal2PinnedOk b C A ctl abs :=
  headerReceivedEncodedLen_local2_pinned_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem headerReceivedEncodedLen_local2_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderReceivedEncodedLenLocal2Ok b C A ctl abs :=
  headerReceivedEncodedLen_local2_ok_ext b A (tripleRatchetExterns C ctl abs)
theorem headerReceivedEncodedLen_local1_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : HeaderReceivedEncodedLenLocal1PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked71_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩))
theorem headerReceivedEncodedLen_local1_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : HeaderReceivedEncodedLenLocal1PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked3EncodedLen_ok_of_pinned (unchunked71_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)))
theorem headerReceivedEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderReceivedEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem headerReceivedEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderReceivedEncodedLenLocal1PlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem headerReceivedEncodedLen_local2_pinned_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : HeaderReceivedEncodedLenLocal2PinnedPlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked71_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩))
theorem headerReceivedEncodedLen_local2_placed_ok_ext [inst : LibsignalPlacement] (A : RustAlloc) (ext : String → Option (State → State)) : HeaderReceivedEncodedLenLocal2PlacedOkExt A ext :=
  subroutine_ok_repack (fun x => ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr⟩) (fun _ _ => rfl) (fun _ _ _ => rfl) (unchunked3EncodedLen_ok_of_pinned (unchunked71_entry_pinned_ok _ A _ (Or.inr ⟨inst, Rust.withPanics ext, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩)))
theorem headerReceivedEncodedLen_local2_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderReceivedEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)
theorem headerReceivedEncodedLen_local2_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : HeaderReceivedEncodedLenLocal2PlacedOk C A ctl abs :=
  headerReceivedEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end CryptoVerification.SpqrV1.ProtoRepr
