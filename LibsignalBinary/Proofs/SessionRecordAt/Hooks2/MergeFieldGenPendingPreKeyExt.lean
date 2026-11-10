/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergePendingPreKey
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
/-!
# `SessionStructure::merge_field` Tag 9 (`pending_pre_key`)

Verifies `SessionStructure::merge_field` (`0x5ca4`, Block `15`) on protobuf tag 9
(`pending_pre_key`, `GenField.pending`) on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPendingPreKey

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (OkAt allocPanic)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem mergeField_fnOff_pendingPreKey :
    CryptoVerification.libsignalSessionCode.fnOff mergeFieldName = num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") :=
  (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")

open Lean Elab Tactic in
local elab "mf9_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn := mkIdent (.str `CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPendingPreKey "mergeField_fnOff_pendingPreKey")
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `CryptoVerification.E2E.Record.DeserializeSeed
      s!"pendingPreKeyBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

/-! ## Pure field and payload lemmas for tag 9 (`pending_pre_key`) -/

private theorem genField_tag_eq_9_iff (fl : GenField) :
    fl.tag = 9 ↔ ∃ k, fl = .pending k := by
  cases fl <;> simp [GenField.tag]

private theorem lenField_two_eq_pendingPreKey {k : List (BitVec 8)} (hk : k.length = 33) :
    lenField 2 k = 18#8 :: 33#8 :: k := by
  unfold lenField
  rw [hk]
  rfl

private theorem pending_payload_eq_pendingPreKey {k : List (BitVec 8)} (hk : k.length = 33) :
    (GenField.pending k).payload =
      35#8 :: 18#8 :: 33#8 :: k := by
  dsimp only [GenField.payload]
  rw [lenField_two_eq_pendingPreKey hk, List.length_cons, List.length_cons, hk]
  rfl

private theorem pending_payload_length_pendingPreKey {k : List (BitVec 8)} (hk : k.length = 33) :
    (GenField.pending k).payload.length = 36 := by
  rw [pending_payload_eq_pendingPreKey hk, List.length_cons, List.length_cons, List.length_cons, hk]

private theorem mergeBytes_pending_eq_pendingPreKey {k : List (BitVec 8)} (hk : k.length = 33)
    (tail : List (BitVec 8)) :
    mergeBytes .lengthDelimited (33#8 :: k ++ tail) =
      some (k, tail) := by
  have h := mergeBytes_encode k tail (by omega)
  rw [hk] at h
  exact h

/-! ## Rodata jump-table byte load at `0x4901c + 8 = 0x49024` -/

private theorem rodata_jump_tag9_pendingPreKey {s : State} (hF : sessionImg0.FrozenLoaded s) :
    s.mem.read8 (sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) = 0xb5#8 ∧
      s.mem.canRead (sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) 1 = true := by
  have hhb := loads_rodata_holdsBytes E2E.Record.loads_sessionImg0 hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) (n := 1) (bs := [0xb5#8])
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel) rfl
    (by rfl_kernel)
  exact ⟨(holdsBytes_cons_iff.mp hhb).1.1, (memSlice_of_holdsBytes_ro hhb).1⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] SepWP in
private theorem step_ldr8_ro_pendingPreKey {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {pc pc' : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 8}
    {r : Reg} {v64 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hread : s.mem.read8 ea = v)
    (hcan : s.mem.canRead ea 1 = true)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) =
      (s.writeReg64 r v64).setPC pc')
    (hnext : SepWP prog target_pc ((s.writeReg64 r v64).setPC pc') P post) :
    SepWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .B8 false rt addr) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldr .W32 .B8 false rt addr) s = (s.writeReg64 r v64).setPC pc' := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  apply hnext R
  exact hm

/-! ## Layout splits (`prostSSGAt`, `stackAt`, `sliceCursorAt`) -/

private def prostSSGRest_pendingPreKey (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

private theorem memRegion_40_split_pending_pendingPreKey (ss : BitVec 64) :
    memRegion (ss + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (ss + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (ss + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (ss + 0x110#64) ↦₃₂ w110) ∗
      memRegion (ss + 0x114#64) 4 ∗
      (∃∗ w118 : BitVec 64, (ss + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (ss + 0x120#64) ↦₃₂ w120) ∗
      memRegion (ss + 0x124#64) 4 := by
  rw [memRegion_split' (b := ss + 0x100#64) (b' := ss + 0x108#64) (n := 8) (k := 32) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x108#64) (b' := ss + 0x110#64) (n := 8) (k := 24) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x110#64) (b' := ss + 0x114#64) (n := 4) (k := 20) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x114#64) (b' := ss + 0x118#64) (n := 4) (k := 16) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x118#64) (b' := ss + 0x120#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x120#64) (b' := ss + 0x124#64) (n := 4) (k := 4) rfl (by bv_lin) (by decide),
      ProofLib.memRegion_eight (ss + 0x100#64), ProofLib.memRegion_eight (ss + 0x108#64),
      ProofLib.memRegion_four (ss + 0x110#64), ProofLib.memRegion_eight (ss + 0x118#64),
      ProofLib.memRegion_four (ss + 0x120#64)]

private theorem prostSSGAt_pending_none_unfold_pendingPreKey (A : RustAlloc) (ss : BitVec 64) (v : SSG)
    (hp : v.pending = none) :
    prostSSGAt A ss v =
      ((ss + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (∃∗ w100 : BitVec 64, (ss + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (ss + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (ss + 0x110#64) ↦₃₂ w110) ∗
      memRegion (ss + 0x114#64) 4 ∗
      (∃∗ w118 : BitVec 64, (ss + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (ss + 0x120#64) ↦₃₂ w120) ∗
      memRegion (ss + 0x124#64) 4 ∗
      prostSSGRest_pendingPreKey A ss v := by
  unfold prostSSGAt prostSSGRest_pendingPreKey
  rw [hp, memRegion_40_split_pending_pendingPreKey ss]
  dsimp only [noneCap]
  ac_rfl

private theorem emptyVec_pending_eq_vecU8At_pendingPreKey (A : RustAlloc) (ss : BitVec 64) :
    ((ss + 0xf8#64) ↦₆₄ 0#64) ∗ ((ss + 0x100#64) ↦₆₄ 1#64) ∗ ((ss + 0x108#64) ↦₆₄ 0#64) =
      vecU8At A (ss + 0xf8#64) 0#64 1#64 [] := by
  have h100 : ss + 0xf8#64 + 8#64 = ss + 0x100#64 := by bv_lin
  have h108 : ss + 0xf8#64 + 16#64 = ss + 0x108#64 := by bv_lin
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  dsimp only [vecU8At, vecHeader]
  have hite : (if (0#64 : BitVec 64) = 0 then emp else
      A.live (1#64) (0#64).toNat 1 ∗ 1#64 ↦ₛ [] ∗
        memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
          ((0#64 : BitVec 64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
  rw [h100, h108, eq_true hp, hite, pure_true, emp_sepConj, sepConj_emp, List.length_nil]

private theorem prostSSGAt_pending_some_fold_pendingPreKey (A : RustAlloc) (ss cap' ptr' : BitVec 64)
    (v : SSG) (k : List (BitVec 8)) :
    vecU8At A (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x114#64) 4 ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 0x124#64) 4 ∗ prostSSGRest_pendingPreKey A ss v ⊢
      prostSSGAt A ss (v.apply (.pending k)) := by
  have hv : vecU8At A (ss + 0xf8#64) cap' ptr' k ⊢ vecU8 A (ss + 0xf8#64) k := by
    unfold vecU8
    exact Entails.trans
      (Entails.sepExists_intro (P := fun ptr => vecU8At A (ss + 0xf8#64) cap' ptr k) ptr')
      (Entails.sepExists_intro (P := fun cap => ∃∗ ptr, vecU8At A (ss + 0xf8#64) cap ptr k) cap')
  refine Entails.trans (sepConj_mono_left hv) ?_
  unfold prostSSGAt prostSSGRest_pendingPreKey SSG.apply
  dsimp only
  apply Entails.of_eq
  ac_rfl

private abbrev mergeFieldSubStack_pendingPreKey : Nat := 16144
private abbrev mergeFieldSubStackX_pendingPreKey : Nat := 32528

private theorem stackAt_split_top_pendingPreKey (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = stackAt (sp - BitVec.ofNat 64 d) n ∗ memRegion (sp - BitVec.ofNat 64 d) d := by
  simp only [stackAt]
  rw [memRegion_split' (n := n) (k := d) rfl rfl h]
  have e1 : sp - BitVec.ofNat 64 (n + d) = sp - BitVec.ofNat 64 d - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + d) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 d := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

private theorem stackAt_split_bottom_pendingPreKey (sp : BitVec 64) (N n d : Nat) (hN : N = n + d := by decide)
    (h : n + d ≤ 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) d ∗ stackAt sp n := by
  subst hN
  simp only [stackAt]
  rw [show n + d = d + n by omega,
    memRegion_split' (n := d) (k := n) (by omega) rfl (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

private theorem stackAt_mergeField_split_pendingPreKey (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStack =
      stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey ∗
      memRegion (sp0 - 240#64) 160 ∗
      cells (sp0 - 80#64) 10 := by
  have htop := stackAt_split_top_pendingPreKey sp0 mergeFieldSubStack_pendingPreKey 240 (by decide)
  change stackAt sp0 mergeFieldStack =
    stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey ∗ memRegion (sp0 - 240#64) 240 at htop
  rw [htop,
      memRegion_split' (b := sp0 - 240#64) (b' := sp0 - 80#64) (n := 160) (k := 80)
        rfl (by bv_lin) (by decide),
      show (80 : Nat) = 8 * 10 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 80#64) 10 (by decide)]

private theorem stackAt_mergeField_unfold_pendingPreKey (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStack =
      ∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64,
      ∃∗ v56 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64,
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64,
      ∃∗ v8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
        ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
        ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
        ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
        memRegion (sp0 - 240#64) 160 ∗
        stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey := by
  have h1 : stackAt sp0 mergeFieldStack =
      cells (sp0 - 80#64) 10 ∗
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey) := by
    rw [stackAt_mergeField_split_pendingPreKey sp0]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin, show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin, show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin, show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin, show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin, sepConj_assoc]

private theorem stackAt_mergeField_fold_pendingPreKey (sp0 : BitVec 64)
    (v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) :
    ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
      ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
      ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
      ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
      ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
      memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey ⊢
      stackAt sp0 mergeFieldStack := by
  have h1 : stackAt sp0 mergeFieldStack =
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey) ∗
      cells (sp0 - 80#64) 10 := by
    rw [stackAt_mergeField_split_pendingPreKey sp0]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin, show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin, show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin, show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin, show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin]
  refine Entails.trans (Q := (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey) ∗
    (((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
     ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
     ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
     ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
     ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8)))
    (by apply Entails.of_eq; ac_rfl) ?_
  refine sepConj_mono_right ?_
  iterate 9 (refine sepConj_mono (Entails.sepExists_intro _) ?_)
  exact Entails.sepExists_intro v8

private theorem stackAt_mergeField_split_pendingPreKeyX (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey ∗
      memRegion (sp0 - 240#64) 160 ∗
      cells (sp0 - 80#64) 10 := by
  have htop := stackAt_split_top_pendingPreKey sp0 mergeFieldSubStackX_pendingPreKey 240 (by decide)
  change stackAt sp0 mergeFieldStackX =
    stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey ∗ memRegion (sp0 - 240#64) 240 at htop
  rw [htop,
      memRegion_split' (b := sp0 - 240#64) (b' := sp0 - 80#64) (n := 160) (k := 80)
        rfl (by bv_lin) (by decide),
      show (80 : Nat) = 8 * 10 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 80#64) 10 (by decide)]

private theorem stackAt_mergeField_unfold_pendingPreKeyX (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      ∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64,
      ∃∗ v56 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64,
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64,
      ∃∗ v8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
        ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
        ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
        ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
        memRegion (sp0 - 240#64) 160 ∗
        stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey := by
  have h1 : stackAt sp0 mergeFieldStackX =
      cells (sp0 - 80#64) 10 ∗
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey) := by
    rw [stackAt_mergeField_split_pendingPreKeyX sp0]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin, show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin, show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin, show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin, show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin, sepConj_assoc]

private theorem stackAt_mergeField_fold_pendingPreKeyX (sp0 : BitVec 64)
    (v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) :
    ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
      ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
      ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
      ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
      ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
      memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey ⊢
      stackAt sp0 mergeFieldStackX := by
  have h1 : stackAt sp0 mergeFieldStackX =
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey) ∗
      cells (sp0 - 80#64) 10 := by
    rw [stackAt_mergeField_split_pendingPreKeyX sp0]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin, show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin, show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin, show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin, show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin]
  refine Entails.trans (Q := (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey) ∗
    (((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
     ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
     ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
     ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
     ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8)))
    (by apply Entails.of_eq; ac_rfl) ?_
  refine sepConj_mono_right ?_
  iterate 9 (refine sepConj_mono (Entails.sepExists_intro _) ?_)
  exact Entails.sepExists_intro v8

private theorem stackAt_sub_to_bytesMerge_pendingPreKey (sp : BitVec 64) :
    stackAt sp mergeFieldSubStack_pendingPreKey =
      memRegion (sp - BitVec.ofNat 64 mergeFieldSubStack_pendingPreKey) 7648 ∗
      stackAt sp Prost.bytesMergeStack :=
  stackAt_split_bottom_pendingPreKey sp mergeFieldSubStack_pendingPreKey Prost.bytesMergeStack 7648 rfl (by decide)

private theorem stackAt_sub_to_bytesMerge_pendingPreKeyX (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX_pendingPreKey =
      memRegion (sp - BitVec.ofNat 64 mergeFieldSubStackX_pendingPreKey) 7648 ∗
      stackAt sp Prost.X.bytesMergeStackW :=
  stackAt_split_bottom_pendingPreKey sp mergeFieldSubStackX_pendingPreKey Prost.X.bytesMergeStackW 7648 rfl (by decide)

private theorem sliceCursorAt_pending_unfold_pendingPreKey (slot ptr : BitVec 64) {k : List (BitVec 8)}
    (hk : k.length = 33) (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenField.pending k).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (36 + tail.length)) ∗
      (ptr ↦₈ 35#8) ∗ ((ptr + 1#64) ↦₈ 18#8) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k ++ tail)) := by
  unfold Prost.sliceCursorAt
  have hlen : ((GenField.pending k).payload ++ tail).length = 36 + tail.length := by
    rw [List.length_append, pending_payload_length_pendingPreKey hk]
  rw [hlen, pending_payload_eq_pendingPreKey hk]
  simp only [List.cons_append, pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin]

private theorem sliceCursorAt_inner_fold_pendingPreKey (slot ptr : BitVec 64) {k : List (BitVec 8)}
    (hk : k.length = 33) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 2#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (34 + tail.length)) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k ++ tail)) =
      Prost.sliceCursorAt slot (ptr + 2#64) (33#8 :: k ++ tail) := by
  unfold Prost.sliceCursorAt
  have hlen : (33#8 :: k ++ tail).length = 34 + tail.length := by
    rw [List.length_append, List.length_cons, hk]
  rw [hlen]

private theorem sliceCursorAfter_inner_unfold_pendingPreKey (slot ptr : BitVec 64) {k : List (BitVec 8)}
    (hk : k.length = 33) (tail : List (BitVec 8)) :
    Prost.sliceCursorAfter slot (ptr + 2#64) (33#8 :: k ++ tail) tail =
      (slot ↦₆₄ (ptr + 36#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k ++ tail)) := by
  unfold Prost.sliceCursorAfter
  have hsub : (33#8 :: k ++ tail).length - tail.length = 34 := by
    rw [List.length_append, List.length_cons, hk]; omega
  have hadd : ptr + 2#64 + BitVec.ofNat 64 34 = ptr + 36#64 := by bv_lin
  rw [hsub, hadd]

private theorem sliceCursorAfter_pending_fold_pendingPreKey (slot ptr : BitVec 64) {k : List (BitVec 8)}
    (hk : k.length = 33) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 36#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 35#8) ∗ ((ptr + 1#64) ↦₈ 18#8) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k ++ tail)) =
      Prost.sliceCursorAfter slot ptr ((GenField.pending k).payload ++ tail) tail := by
  unfold Prost.sliceCursorAfter
  have hsub : ((GenField.pending k).payload ++ tail).length - tail.length = 36 := by
    rw [List.length_append, pending_payload_length_pendingPreKey hk]; omega
  rw [hsub, pending_payload_eq_pendingPreKey hk]
  simp only [List.cons_append, pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin]

/-! ## Pure BitVec, branch, and address helpers for tag 9 -/

private theorem adrp_rodata_sym_4601c_pendingPreKey (b : BitVec 64) (hb : b &&& 4095#64 = 0#64) :
    (b + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") + 40#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" - page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 712)) = b + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
  simp only [hb, arm64_norm]

private theorem wt_and_ff_eq_pendingPreKey (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    r2.truncate 32 &&& 255#32 = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat] at h ⊢
  change (r2.toNat % 4294967296 &&& (2 ^ 8 - 1)) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem wt_and_ff_64_eq_pendingPreKey (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 r2) &&& 255#64) = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat] at h ⊢
  change (((r2.toNat % 4294967296) % 18446744073709551616 &&& (2 ^ 8 - 1)) % 4294967296) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem len36_ne_zero_pendingPreKey {n : Nat} (h : 36 + n < 2 ^ 62) :
    (BitVec.ofNat 64 (36 + n) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h1
  omega

private theorem len36_sub_one_pendingPreKey {n : Nat} (_h : 36 + n < 2 ^ 62) :
    BitVec.ofNat 64 (36 + n) - 1#64 = BitVec.ofNat 64 (35 + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

private theorem len36_add_neg1_pendingPreKey {n : Nat} (h : 36 + n < 2 ^ 62) :
    BitVec.ofNat 64 (36 + n) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 (35 + n) := by
  rw [show (bv% (2 ^ 64 - 1)) = -1#64 by rfl, ← BitVec.sub_eq_add_neg]
  exact len36_sub_one_pendingPreKey h

private theorem len35_sub_35_pendingPreKey {n : Nat} (_h : 36 + n < 2 ^ 62) :
    BitVec.ofNat 64 (35 + n) - 35#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

private theorem len35_add_neg35_pendingPreKey {n : Nat} (h : 36 + n < 2 ^ 62) :
    BitVec.ofNat 64 (35 + n) + bv% (2 ^ 64 - 35) = BitVec.ofNat 64 n := by
  rw [show (bv% (2 ^ 64 - 35)) = -35#64 by rfl, ← BitVec.sub_eq_add_neg]
  exact len35_sub_35_pendingPreKey h

private theorem len35_ult_35_pendingPreKey {n : Nat} (h : 36 + n < 2 ^ 62) :
    BitVec.ult (BitVec.ofNat 64 (35 + n)) 35#64 = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

private theorem len35_ule_35_pendingPreKey {n : Nat} (h : 36 + n < 2 ^ 62) :
    BitVec.ule 35#64 (BitVec.ofNat 64 (35 + n)) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

private theorem len35_ule_tail_pendingPreKey {n : Nat} (h : 36 + n < 2 ^ 62) :
    BitVec.ule (BitVec.ofNat 64 (35 + n)) (BitVec.ofNat 64 n) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

private theorem tail_ult_len35_pendingPreKey {n : Nat} (h : 36 + n < 2 ^ 62) :
    BitVec.ult (BitVec.ofNat 64 n) (BitVec.ofNat 64 (35 + n)) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega

private theorem len35_ult_tail_pendingPreKey {n : Nat} (h : 36 + n < 2 ^ 62) :
    BitVec.ult (BitVec.ofNat 64 (35 + n)) (BitVec.ofNat 64 n) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

private theorem len35_sub_tail_pendingPreKey {n : Nat} (_h : 36 + n < 2 ^ 62) :
    BitVec.ofNat 64 (35 + n) - BitVec.ofNat 64 n = 35#64 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

private theorem len35_sub_one_pendingPreKey {n : Nat} (_h : 36 + n < 2 ^ 62) :
    BitVec.ofNat 64 (35 + n) - 1#64 = BitVec.ofNat 64 (34 + n) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

private theorem len35_add_neg1_pendingPreKey {n : Nat} (h : 36 + n < 2 ^ 62) :
    BitVec.ofNat 64 (35 + n) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 (34 + n) := by
  rw [show (bv% (2 ^ 64 - 1)) = -1#64 by rfl, ← BitVec.sub_eq_add_neg]; exact len35_sub_one_pendingPreKey h

private theorem bytesMerge_ok_sub_pendingPreKey {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Prost.BytesMergeOk sessionImg0 C A0 ctl abs) :
    subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
      (Prost.bytesMergeSpec A0 sessionImg0) := by
  have heq : (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr Prost.bytesMergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"),
      (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact h

private theorem of_sepWP_frozen_pendingPreKey {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_frozen hfl hsym h

private theorem call_frame_inv_pendingPreKey {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, (spec.inImage img).onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  exact ProofLib.SepWPp.call_inImage_frame hcall hfl hsym hpc hrun hsp hlr hspec hφ hP hexit hpanic
    hnext (fun sf _ _ hpost => by
      change sf.mem ⊨ (spec.inImage img).onOom x s sf ∗ _ at hpost
      rw [hoom sf] at hpost
      exact (not_satisfies_false_sepConj hpost).elim)

private theorem pre_to_bytesMerge_pendingPreKey (ss : BitVec 64) (v : SSG)
    (bufRef slot ptr : BitVec 64) {k : List (BitVec 8)} (hk : k.length = 33) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 248#64) ↦₆₄ 0#64 ∗ (ss + 256#64) ↦₆₄ 1#64 ∗ (ss + 264#64) ↦₆₄ 0#64 ∗
      (ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A0 ss v ∗
      bufRef ↦₆₄ slot ∗ slot ↦₆₄ (ptr + 2#64) ∗ (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (34 + tail.length) ∗
      ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗ (ptr + 2#64) ↦ₛ (33#8 :: k ++ tail) ∗
      (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey) =
    (vecU8At A0 (ss + 248#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot (ptr + 2#64) (33#8 :: k ++ tail) ∗ A0.pool ∗
      stackAt (sp0 - 240#64) Prost.bytesMergeStack) ∗
    ((ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A0 ss v ∗
      ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗
      (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      memRegion (sp0 - 240#64 - 16144#64) 7648) := by
  have hpool : A0.pool = emp := rfl
  rw [← emptyVec_pending_eq_vecU8At_pendingPreKey A0 ss,
      ← sliceCursorAt_inner_fold_pendingPreKey slot ptr hk tail,
      stackAt_sub_to_bytesMerge_pendingPreKey (sp0 - 240#64),
      hpool, emp_sepConj]
  ac_rfl

private theorem post_of_bytesMerge_pendingPreKey (ss : BitVec 64) (v : SSG)
    (bufRef slot ptr : BitVec 64) {k : List (BitVec 8)} (hk : k.length = 33) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64)
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) :
    (Prost.bytesMergeRawSpec A0).post
      ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
        ptr + 2#64, 33#8 :: k ++ tail⟩ sm sf ∗
    ((ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A0 ss v ∗
      ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗
      (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      memRegion (sp0 - 240#64 - 16144#64) 7648) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ⌜Prost.BytesMergeCapOk cap' tail.length⌝ ∗
        vecU8At A0 (ss + 248#64) cap' ptr' k ∗
        (ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
        (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A0 ss v ∗
        bufRef ↦₆₄ slot ∗ slot ↦₆₄ (ptr + 36#64) ∗ (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
        ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗ (ptr + 2#64) ↦ₛ (33#8 :: k ++ tail) ∗
        (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
        (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
        (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
        stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey) := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.bytesMergeRawSpec]
  rw [mergeBytes_pending_eq_pendingPreKey hk tail]
  dsimp only
  rw [hsp,
      sliceCursorAfter_inner_unfold_pendingPreKey slot ptr hk tail,
      stackAt_sub_to_bytesMerge_pendingPreKey (sp0 - 240#64),
      hpool, emp_sepConj]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_pendingPreKey (ss cap' ptr' : BitVec 64) (v : SSG)
    (bufRef slot ptr : BitVec 64) {k : List (BitVec 8)} (hk : k.length = 33) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
      (ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A0 ss v ∗
      bufRef ↦₆₄ slot ∗ slot ↦₆₄ (ptr + 36#64) ∗ (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗ (ptr + 2#64) ↦ₛ (33#8 :: k ++ tail) ∗
      (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey) ⊢
    prostSSGAt A0 ss (v.apply (GenField.pending k)) ∗
      bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenField.pending k).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStack := by
  rw [← sliceCursorAfter_pending_fold_pendingPreKey slot ptr hk tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
      ((ss + 272#64) ↦₃₂ 0#32) ∗ memRegion (ss + 276#64) 4 ∗
      ((ss + 280#64) ↦₆₄ 0#64) ∗ ((ss + 288#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A0 ss v) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (ptr + 36#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 35#8) ∗ ((ptr + 1#64) ↦₈ 18#8) ∗ ((ptr + 2#64) ↦ₛ (33#8 :: k ++ tail))) ∗
    (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗ ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w118) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗ ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_pendingPreKey))
    (by apply Entails.of_eq; ac_rfl) ?_
  refine sepConj_mono (prostSSGAt_pending_some_fold_pendingPreKey A0 ss cap' ptr' v k) ?_
  refine sepConj_mono_right (sepConj_mono_right ?_)
  exact stackAt_mergeField_fold_pendingPreKey sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19

private theorem end_trace_pendingPreKey (sf s0 : State) (bufRef : BitVec 64) (tail_len : Nat)
    (htr : sf.trace = s0.trace) :
    ((((((((((((((((sf.writeReg64 (Reg.gpr 9#5) 0#64).writeReg64 (Reg.gpr 3#5) bufRef).writeReg64 (Reg.gpr 2#5) (BitVec.ofNat 64 tail_len)).writeReg64 (Reg.gpr 0#5) 0#64).writeReg64
      (Reg.gpr 20#5) (s0.readReg64 (Reg.gpr 20#5))).writeReg64 (Reg.gpr 19#5) (s0.readReg64 (Reg.gpr 19#5))).writeReg64 (Reg.gpr 25#5) (s0.readReg64 (Reg.gpr 25#5))).writeReg64
      (Reg.gpr 22#5) (s0.readReg64 (Reg.gpr 22#5))).writeReg64 (Reg.gpr 21#5) (s0.readReg64 (Reg.gpr 21#5))).writeReg64 (Reg.gpr 24#5) (s0.readReg64 (Reg.gpr 24#5))).writeReg64
      (Reg.gpr 23#5) (s0.readReg64 (Reg.gpr 23#5))).writeReg64 (Reg.gpr 29#5) (s0.readReg64 (Reg.gpr 29#5))).writeReg64 (Reg.gpr 30#5) (s0.readReg64 (Reg.gpr 30#5))).writeReg64 Reg.sp s0.sp).setPState
      (subsPState64 (BitVec.ofNat 64 tail_len) (BitVec.ofNat 64 tail_len))).setPC (s0.readReg64 (Reg.gpr 30#5))).trace = s0.trace := by
  simp only [wp_norm, arm64_norm, htr]

private theorem end_x0_pendingPreKey (sf s0 : State) (bufRef : BitVec 64) (tail_len : Nat) :
    ((((((((((((((((sf.writeReg64 (Reg.gpr 9#5) 0#64).writeReg64 (Reg.gpr 3#5) bufRef).writeReg64 (Reg.gpr 2#5) (BitVec.ofNat 64 tail_len)).writeReg64 (Reg.gpr 0#5) 0#64).writeReg64
      (Reg.gpr 20#5) (s0.readReg64 (Reg.gpr 20#5))).writeReg64 (Reg.gpr 19#5) (s0.readReg64 (Reg.gpr 19#5))).writeReg64 (Reg.gpr 25#5) (s0.readReg64 (Reg.gpr 25#5))).writeReg64
      (Reg.gpr 22#5) (s0.readReg64 (Reg.gpr 22#5))).writeReg64 (Reg.gpr 21#5) (s0.readReg64 (Reg.gpr 21#5))).writeReg64 (Reg.gpr 24#5) (s0.readReg64 (Reg.gpr 24#5))).writeReg64
      (Reg.gpr 23#5) (s0.readReg64 (Reg.gpr 23#5))).writeReg64 (Reg.gpr 29#5) (s0.readReg64 (Reg.gpr 29#5))).writeReg64 (Reg.gpr 30#5) (s0.readReg64 (Reg.gpr 30#5))).writeReg64 Reg.sp s0.sp).setPState
      (subsPState64 (BitVec.ofNat 64 tail_len) (BitVec.ofNat 64 tail_len))).setPC (s0.readReg64 (Reg.gpr 30#5))).readReg64 Reg.x0 = 0#64 := by
  simp only [wp_norm, arm64_norm]

private theorem allowPanic_call_pendingPreKey {s_call s0 sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  have h1 : allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    unfold allocFailedIn; rw [htr]; exact id
  exact allowPanic_frame h1 hm


private theorem rodata_jump_tag9_pendingPreKey_ext {img : Obj.Image} {s : State}
    (hLoads : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    s.mem.read8 (img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) = 0xb5#8 ∧
      s.mem.canRead (img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) 1 = true := by
  have hhb := loads_rodata_holdsBytes hLoads hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) (n := 1) (bs := [0xb5#8])
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel) rfl
    (by rfl_kernel)
  exact ⟨(holdsBytes_cons_iff.mp hhb).1.1, (memSlice_of_holdsBytes_ro hhb).1⟩

private theorem bytesMerge_ok_sub_pendingPreKey_extW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : Prost.X.BytesMergeOkW img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
      (Prost.X.bytesMergeSpecW A img) := by
  have heq : (SP2Ext img.base ext).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) =
      (SP2Ext img.base ext).fnAddr Prost.bytesMergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"),
      (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact h

private theorem pre_to_bytesMerge_pendingPreKey_extW {A : RustAlloc} (ss : BitVec 64) (v : SSG)
    (bufRef slot ptr : BitVec 64) {k : List (BitVec 8)} (hk : k.length = 33) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 248#64) ↦₆₄ 0#64 ∗ (ss + 256#64) ↦₆₄ 1#64 ∗ (ss + 264#64) ↦₆₄ 0#64 ∗
      (ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A ss v ∗
      bufRef ↦₆₄ slot ∗ slot ↦₆₄ (ptr + 2#64) ∗ (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (34 + tail.length) ∗
      ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗ (ptr + 2#64) ↦ₛ (33#8 :: k ++ tail) ∗
      A.pool ∗
      (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey) =
    (vecU8At A (ss + 248#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot (ptr + 2#64) (33#8 :: k ++ tail) ∗ A.pool ∗
      stackAt (sp0 - 240#64) Prost.X.bytesMergeStackW) ∗
    ((ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A ss v ∗
      ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗
      (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      memRegion (sp0 - 240#64 - BitVec.ofNat 64 mergeFieldSubStackX_pendingPreKey) 7648) := by
  rw [← emptyVec_pending_eq_vecU8At_pendingPreKey A ss,
      ← sliceCursorAt_inner_fold_pendingPreKey slot ptr hk tail,
      stackAt_sub_to_bytesMerge_pendingPreKeyX (sp0 - 240#64)]
  ac_rfl

private theorem post_of_bytesMerge_pendingPreKey_extW {A : RustAlloc} (ss : BitVec 64) (v : SSG)
    (bufRef slot ptr : BitVec 64) {k : List (BitVec 8)} (hk : k.length = 33) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64)
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) :
    (Prost.X.bytesMergeRawSpecW A).post
      ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
        ptr + 2#64, 33#8 :: k ++ tail⟩ sm sf ∗
    ((ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A ss v ∗
      ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗
      (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      memRegion (sp0 - 240#64 - BitVec.ofNat 64 mergeFieldSubStackX_pendingPreKey) 7648) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        vecU8At A (ss + 248#64) cap' ptr' k ∗
        (ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
        (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A ss v ∗
        bufRef ↦₆₄ slot ∗ slot ↦₆₄ (ptr + 36#64) ∗ (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
        ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗ (ptr + 2#64) ↦ₛ (33#8 :: k ++ tail) ∗
        A.pool ∗
        (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
        (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
        (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
        stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey) := by
  dsimp only [Prost.X.bytesMergeRawSpecW]
  rw [mergeBytes_pending_eq_pendingPreKey hk tail]
  dsimp only
  rw [hsp,
      sliceCursorAfter_inner_unfold_pendingPreKey slot ptr hk tail,
      stackAt_sub_to_bytesMerge_pendingPreKeyX (sp0 - 240#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

private theorem final_post_entails_pendingPreKey_extW {A : RustAlloc} (ss cap' ptr' : BitVec 64) (v : SSG)
    (bufRef slot ptr : BitVec 64) {k : List (BitVec 8)} (hk : k.length = 33) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A (ss + 248#64) cap' ptr' k ∗
      (ss + 272#64) ↦₃₂ 0#32 ∗ memRegion (ss + 276#64) 4 ∗ (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗ memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A ss v ∗
      bufRef ↦₆₄ slot ∗ slot ↦₆₄ (ptr + 36#64) ∗ (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      ptr ↦₈ 35#8 ∗ (ptr + 1#64) ↦₈ 18#8 ∗ (ptr + 2#64) ↦ₛ (33#8 :: k ++ tail) ∗
      A.pool ∗
      (sp0 - 80#64) ↦₆₄ r29 ∗ (sp0 - 72#64) ↦₆₄ r30 ∗ (sp0 - 64#64) ↦₆₄ r25 ∗ (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗ (sp0 - 40#64) ↦₆₄ r23 ∗ (sp0 - 32#64) ↦₆₄ r22 ∗ (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗ (sp0 - 8#64) ↦₆₄ r19 ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey) ⊢
    prostSSGAt A ss (v.apply (GenField.pending k)) ∗
      bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenField.pending k).payload ++ tail) tail ∗
      A.pool ∗
      stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_pending_fold_pendingPreKey slot ptr hk tail]
  refine Entails.trans (Q :=
    (vecU8At A (ss + 248#64) cap' ptr' k ∗
      ((ss + 272#64) ↦₃₂ 0#32) ∗ memRegion (ss + 276#64) 4 ∗
      ((ss + 280#64) ↦₆₄ 0#64) ∗ ((ss + 288#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 292#64) 4 ∗ prostSSGRest_pendingPreKey A ss v) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (ptr + 36#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 35#8) ∗ ((ptr + 1#64) ↦₈ 18#8) ∗ ((ptr + 2#64) ↦ₛ (33#8 :: k ++ tail))) ∗
    A.pool ∗
    (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗ ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w118) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗ ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗ memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX_pendingPreKey))
    (by apply Entails.of_eq; ac_rfl) ?_
  refine sepConj_mono (prostSSGAt_pending_some_fold_pendingPreKey A ss cap' ptr' v k) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  exact stackAt_mergeField_fold_pendingPreKeyX sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19

theorem mergeFieldGenPendingPreKey_ok_extWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtWA img A ext) :
    MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 9) := by
  dsimp only [MergeFieldGenOkAtWA, OkAtX]
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨(mergeFieldGenSpecAtWA A img (fun fl => fl.tag = 9)).pre
    ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ s0, R, hpre, ?_⟩
  clear hpre
  dsimp only [mergeFieldGenSpecAtWA]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag, hOk, hFresh, hlen, hF0, hsym0⟩ => ?_
  obtain ⟨k, rfl⟩ := (genField_tag_eq_9_iff fld).mp htag
  have hk : k.length = 33 := hOk
  have hp : v.pending = none := hFresh
  dsimp only [GenField.tag, GenField.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  rw [List.length_append, pending_payload_length_pendingPreKey hk] at hlen
  rw [State.spAligned] at hsp_align
  have hb : img.base &&& 4095#64 = 0#64 :=
    base_aligned_of_loads hLoads
  have hcall := bytesMerge_ok_sub_pendingPreKey_extW hC.2.2.1
  mf9_fetches_range img.base (Rust.withPanics ext) 0x000 0x03c
  mf9_fetches_range img.base (Rust.withPanics ext) 0x314 0x368
  mf9_fetches_range img.base (Rust.withPanics ext) 0x708 0x718
  mf9_fetches_range img.base (Rust.withPanics ext) 0x758 0x7a0
  mf9_fetches_range img.base (Rust.withPanics ext) 0x7f4 0x844
  mf9_fetches_range img.base (Rust.withPanics ext) 0x8e4 0x8f0
  mf9_fetches_range img.base (Rust.withPanics ext) 0x92c 0x934
  dsimp only [SP2Ext, contractProg] at hpc hcall ⊢
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_pendingPreKey (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_pendingPreKey (s0.readReg64 .x2) hx2
  have hlen36_ne0 : (BitVec.ofNat 64 (36 + tail.length) == 0#64) = false := len36_ne_zero_pendingPreKey hlen
  have hlen36_sub1 : BitVec.ofNat 64 (36 + tail.length) - 1#64 = BitVec.ofNat 64 (35 + tail.length) := len36_sub_one_pendingPreKey hlen
  have hlen36_add_neg1 : BitVec.ofNat 64 (36 + tail.length) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 (35 + tail.length) := len36_add_neg1_pendingPreKey hlen
  have hlen35_sub35 : BitVec.ofNat 64 (35 + tail.length) - 35#64 = BitVec.ofNat 64 tail.length := len35_sub_35_pendingPreKey hlen
  have hlen35_add_neg35 : BitVec.ofNat 64 (35 + tail.length) + bv% (2 ^ 64 - 35) = BitVec.ofNat 64 tail.length := len35_add_neg35_pendingPreKey hlen
  have hlen35_ult35 : BitVec.ult (BitVec.ofNat 64 (35 + tail.length)) 35#64 = false := len35_ult_35_pendingPreKey hlen
  have hlen35_ule35 : BitVec.ule 35#64 (BitVec.ofNat 64 (35 + tail.length)) = true := len35_ule_35_pendingPreKey hlen
  have hlen35_ult_tail : BitVec.ult (BitVec.ofNat 64 (35 + tail.length)) (BitVec.ofNat 64 tail.length) = false := len35_ult_tail_pendingPreKey hlen
  have hlen35_sub_tail : BitVec.ofNat 64 (35 + tail.length) - BitVec.ofNat 64 tail.length = 35#64 := len35_sub_tail_pendingPreKey hlen
  have hlen35_ule_tail : BitVec.ule (BitVec.ofNat 64 (35 + tail.length)) (BitVec.ofNat 64 tail.length) = false := len35_ule_tail_pendingPreKey hlen
  have htail_ult_len35 : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 (35 + tail.length)) = true := tail_ult_len35_pendingPreKey hlen
  have hlen35_sub1 : BitVec.ofNat 64 (35 + tail.length) - 1#64 = BitVec.ofNat 64 (34 + tail.length) := len35_sub_one_pendingPreKey hlen
  have hlen35_add_neg1 : BitVec.ofNat 64 (35 + tail.length) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 (34 + tail.length) := len35_add_neg1_pendingPreKey hlen
  have hadrp :
      (((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr mergeFieldName + 40#64) &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" - page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 712)) = img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")]
    exact adrp_rodata_sym_4601c_pendingPreKey img.base hb
  have hfetch_0x34 := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := img.base) (H := Rust.withPanics ext)
    (k := 52) mergeField_fnOff_pendingPreKey (by decide)
    (ls_decode% CryptoVerification.E2E.Record.DeserializeSeed.pendingPreKeyBin (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 52))
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr mergeFieldName = entry
  examples_hide_fetches
  conv =>
    arg 4
    rw [prostSSGAt_pending_none_unfold_pendingPreKey A ss v hp,
        sliceCursorAt_pending_unfold_pendingPreKey slot ptr hk tail,
        stackAt_mergeField_unfold_pendingPreKeyX s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => SepWPp.exists_elim fun v80 =>
    SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
    SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
    SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
    SepWPp.exists_elim fun v8 => ?_
  apply of_sepWP_frozen_pendingPreKey hF0 hsym0 (mid := entry + bv% (52))
  iterate 13 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hF1 hsym1
  obtain ⟨hread9, hcan9⟩ := rodata_jump_tag9_pendingPreKey_ext hLoads hF1
  apply of_sepWP_frozen_pendingPreKey hF1 hsym1 (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
  refine step_ldr8_ro_pendingPreKey (pc := entry + bv% (52)) (pc' := entry + bv% (56))
    (r := Reg.gpr 11#5) (v64 := 181#64)
    rfl (by simp only [wp_norm, arm64_norm, hrun]) hfetch_0x34 rfl
    (ea := img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) (wb := none)
    (by simp only [evalAddrMode, wp_norm, arm64_norm])
    hread9 hcan9 (by simp only [applyWriteback, wp_norm, arm64_norm]) ?_
  iterate 35 wp_step
  iterate 26 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hF2 hsym2
  refine call_frame_inv_pendingPreKey
    (x := ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      ptr + 2#64, 33#8 :: k ++ tail⟩)
    (T := vecU8At A (ss + 248#64) 0#64 1#64 [] ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot (ptr + 2#64) (33#8 :: k ++ tail) ∗
      A.pool ∗
      stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW)
    hcall hF2 hsym2
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm]; rfl)
    (by rw [List.length_cons, List.length_append, hk]; omega)
    (pre_to_bytesMerge_pendingPreKey_extW (A := A) ss v bufRef slot ptr hk tail s0.sp
      (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) w118
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [Prost.X.bytesMergeRawSpecW, allocPanic] at hm ⊢
      exact allowPanic_call_pendingPreKey (by simp only [wp_norm, arm64_norm]) hm) ?_
  intro sf hpcf hrunf hspf hcsf _ _
  simp only [wp_norm, arm64_norm] at hpcf
  have hsp_sf : sf.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm] using hspf
  have hx21_sf : sf.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
  have hx24_sf : sf.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.1
  have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
  have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
  have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
  rw [post_of_bytesMerge_pendingPreKey_extW (A := A) ss v bufRef slot ptr hk tail s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 25#5)) w118
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
    _ sf (by simp only [wp_norm, arm64_norm])]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun htr_sf => SepWPp.pure_elim fun hx0_sf => ?_
  have htr_sf' : sf.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm] using htr_sf
  have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = false := by
    simp [BitVec.ult]
  have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = true := by
    simp [BitVec.ule]
  apply SepWPp.of_sepWP_ret
  iterate 19 wp_step
  apply SepWP.fold (final_post_entails_pendingPreKey_extW (A := A) ss cap' ptr' v bufRef slot ptr hk tail s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 25#5)) w118
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
    (sepConj_emp _).symm
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
  refine ⟨fun hmf => ?_,
    by simp only [wp_norm, arm64_norm],
    by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hx26_sf, hx27_sf, hx28_sf, hvregs_sf, and_self]⟩
  rw [end_trace_pendingPreKey sf s0 bufRef tail.length htr_sf',
      end_x0_pendingPreKey sf s0 bufRef tail.length]
  simp only [and_self, pure_true, emp_sepConj]
  rw [sepConj_emp] at hmf
  exact hmf

private theorem mergeFieldGenSpecAtWA_A0_pendingPreKey (img : Obj.Image) (P : GenField → Prop) :
    mergeFieldGenSpecAtWA A0 img P = mergeFieldGenSpecAtW img P := by
  have hp : A0.pool = emp := rfl
  unfold mergeFieldGenSpecAtWA mergeFieldGenSpecAtW
  congr 1
  · funext x s; simp only [hp, emp_sepConj]
  · funext x s sf; simp only [hp, emp_sepConj]

theorem mergeFieldGenPendingPreKey_ok_extW (img : Obj.Image)
    (ext : String → Option (State → State)) (hLoads : Obj.Loads libsignalSessionImage img)
    (hC : DeserializeCalleesAtW img ext) :
    MergeFieldGenOkAtW img ext (fun fl => fl.tag = 9) := by
  unfold MergeFieldGenOkAtW
  rw [← mergeFieldGenSpecAtWA_A0_pendingPreKey]
  exact mergeFieldGenPendingPreKey_ok_extWA img A0 ext hLoads hC

/-! ## Relocatable `[LibsignalPlacement]` proof for tag 9 (`pending_pre_key`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_MergeFieldGenPendingPreKeyExt_Placed : True := trivial

private theorem sepWP_intro_rodata_tag9_placed_pendingPreKey_ext [LibsignalPlacement]
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog target_pc s (((lsmpl.ρ mergeFieldRodataSym + 8#64) ↦₈ᵣ 181#8) ∗ P) post) :
    SepWP prog target_pc s P post := by
  refine ProofLib.SepWP.of_reaches_pc fun R hm => ?_
  refine ProofLib.SepWP.to_reaches_pc h ?_
  rw [sepConj_assoc]
  exact lsro8_intro hcrl.2 (by lsro_addr) (by decide +kernel) hm

private theorem sepWP_drop_left_pendingPreKey_ext {prog : Program} {target_pc : BitVec 64}
    {s : State} {Drop P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P post) : SepWP prog target_pc s (Drop ∗ P) post := by
  refine ProofLib.SepWP.of_reaches_pc fun R hm => ?_
  rw [sepConj_assoc] at hm
  exact ProofLib.SepWP.to_reaches_pc h (Satisfies.of_sep_right hm)

private theorem call_frame_lscro_pendingPreKey_ext {α : Type} {prog : Program} {pl : MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec))
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre_in : s.mem ⊨ (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre_in hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    rw [hoom sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

/-- Relocatable `SessionStructure::merge_field` (Block `15`, `lsProg_15 H`) on tag 9
(`pending_pre_key`, `GenField.pending`) at `mergeFieldStackX`. -/
theorem mergeFieldGenPendingPreKey_placed_okW [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeFieldGenPlacedOkW H (fun fl => fl.tag = 9) := by
  unfold MergeFieldGenPlacedOkW
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  refine ⟨_, R, hpre_raw, ?_⟩
  clear hpre hpre_raw
  dsimp only [mergeFieldGenRawSpecW]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag, hOk, hFresh, hlen⟩ => ?_
  obtain ⟨k, rfl⟩ := (genField_tag_eq_9_iff fld).mp htag
  have hk : k.length = 33 := hOk
  have hp : v.pending = none := hFresh
  dsimp only [GenField.tag, GenField.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  rw [List.length_append, pending_payload_length_pendingPreKey hk] at hlen
  rw [State.spAligned] at hsp_align
  have hcall : subroutine_ok (lsProg_15 H) (lsmpl.base 7) (Prost.X.bytesMergePlacedSpecW A0) :=
    ls_call_ro_of_block (callerProg := lsProg_15 H) hC.2.2.1
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_pendingPreKey (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_pendingPreKey (s0.readReg64 .x2) hx2
  have hlen36_ne0 : (BitVec.ofNat 64 (36 + tail.length) == 0#64) = false := len36_ne_zero_pendingPreKey hlen
  have hlen36_sub1 : BitVec.ofNat 64 (36 + tail.length) - 1#64 = BitVec.ofNat 64 (35 + tail.length) := len36_sub_one_pendingPreKey hlen
  have hlen36_add_neg1 : BitVec.ofNat 64 (36 + tail.length) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 (35 + tail.length) := len36_add_neg1_pendingPreKey hlen
  have hlen35_sub35 : BitVec.ofNat 64 (35 + tail.length) - 35#64 = BitVec.ofNat 64 tail.length := len35_sub_35_pendingPreKey hlen
  have hlen35_add_neg35 : BitVec.ofNat 64 (35 + tail.length) + bv% (2 ^ 64 - 35) = BitVec.ofNat 64 tail.length := len35_add_neg35_pendingPreKey hlen
  have hlen35_ult35 : BitVec.ult (BitVec.ofNat 64 (35 + tail.length)) 35#64 = false := len35_ult_35_pendingPreKey hlen
  have hlen35_ule35 : BitVec.ule 35#64 (BitVec.ofNat 64 (35 + tail.length)) = true := len35_ule_35_pendingPreKey hlen
  have hlen35_ult_tail : BitVec.ult (BitVec.ofNat 64 (35 + tail.length)) (BitVec.ofNat 64 tail.length) = false := len35_ult_tail_pendingPreKey hlen
  have hlen35_sub_tail : BitVec.ofNat 64 (35 + tail.length) - BitVec.ofNat 64 tail.length = 35#64 := len35_sub_tail_pendingPreKey hlen
  have hlen35_ule_tail : BitVec.ule (BitVec.ofNat 64 (35 + tail.length)) (BitVec.ofNat 64 tail.length) = false := len35_ule_tail_pendingPreKey hlen
  have htail_ult_len35 : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 (35 + tail.length)) = true := tail_ult_len35_pendingPreKey hlen
  have hlen35_sub1 : BitVec.ofNat 64 (35 + tail.length) - 1#64 = BitVec.ofNat 64 (34 + tail.length) := len35_sub_one_pendingPreKey hlen
  have hlen35_add_neg1 : BitVec.ofNat 64 (35 + tail.length) + bv% (2 ^ 64 - 1) = BitVec.ofNat 64 (34 + tail.length) := len35_add_neg1_pendingPreKey hlen
  conv =>
    arg 4
    rw [prostSSGAt_pending_none_unfold_pendingPreKey A0 ss v hp,
        sliceCursorAt_pending_unfold_pendingPreKey slot ptr hk tail,
        stackAt_mergeField_unfold_pendingPreKeyX s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => SepWPp.exists_elim fun v80 =>
    SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
    SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
    SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
    SepWPp.exists_elim fun v8 => ?_
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0
  apply sepWP_intro_rodata_tag9_placed_pendingPreKey_ext hcrl0
  wp_steps
  apply sepWP_drop_left_pendingPreKey_ext
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcrl2
  refine call_frame_lscro_pendingPreKey_ext
    (x := ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      ptr + 2#64, 33#8 :: k ++ tail⟩)
    (ret_pc := (blkPl_15).base + 2116#64)
    (T := vecU8At A0 (ss + 248#64) 0#64 1#64 [] ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot (ptr + 2#64) (33#8 :: k ++ tail) ∗
      A0.pool ∗
      stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW)
    hcall hcrl2
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm]; rfl)
    (by rw [List.length_cons, List.length_append, hk]; omega)
    (by
      have hpre_eq := pre_to_bytesMerge_pendingPreKey_extW (A := A0) ss v bufRef slot ptr hk tail s0.sp
        (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
        (s0.readReg64 (Reg.gpr 25#5)) w118
        (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
        (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
        (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
      conv at hpre_eq => lhs; simp only [show A0.pool = emp from rfl, emp_sepConj]
      exact hpre_eq)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [Prost.X.bytesMergeRawSpecW, allocPanic] at hm ⊢
      exact allowPanic_call_pendingPreKey (by simp only [wp_norm, arm64_norm]) hm) ?_
  intro sf hpcf hrunf hspf hcsf _hcrl3
  have hsp_sf : sf.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm] using hspf
  have hx21_sf : sf.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
  have hx24_sf : sf.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.1
  have hx26_sf : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
  have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
  have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
  rw [post_of_bytesMerge_pendingPreKey_extW (A := A0) ss v bufRef slot ptr hk tail s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 25#5)) w118
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
    _ sf (by simp only [wp_norm, arm64_norm])]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun htr_sf => SepWPp.pure_elim fun hx0_sf => ?_
  have htr_sf' : sf.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm] using htr_sf
  have hx0_sf' : sf.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf
  have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = false := by
    simp [BitVec.ult]
  have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) = true := by
    simp [BitVec.ule]
  apply SepWPp.of_sepWP_ret
  iterate 19 wp_step
  apply SepWP.fold (final_post_entails_pendingPreKey_extW (A := A0) ss cap' ptr' v bufRef slot ptr hk tail s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 25#5)) w118
    (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
    (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
    (sepConj_emp _).symm
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
  refine ⟨fun hmf => ?_,
    by simp only [wp_norm, arm64_norm],
    by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hx26_sf, hx27_sf, hx28_sf, hvregs_sf, and_self]⟩
  rw [end_trace_pendingPreKey sf s0 bufRef tail.length htr_sf',
      end_x0_pendingPreKey sf s0 bufRef tail.length]
  simp only [and_self, pure_true, emp_sepConj]
  rw [sepConj_emp, show A0.pool = emp from rfl, emp_sepConj] at hmf
  exact hmf

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPendingPreKey
