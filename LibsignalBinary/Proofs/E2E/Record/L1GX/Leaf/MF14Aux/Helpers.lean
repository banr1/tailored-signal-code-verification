/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF14Aux.Pure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv

/-!
# Stepping, call, and layout helpers for `merge_field` tag 14

Supporting lemmas for the `pending_kyber_pre_key` arm of `SessionStructure::merge_field`
(`0x581c`): `.rodata` jump-table lookup, `decode_varint_slice` / `int32::merge` / `bytes::merge`
subroutine framing, stack-budget splits, and input slice cursor unfolding.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.Record.Serialization (allocPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem mergeField_fnOff_mf14 :
    CryptoVerification.libsignalSessionCode.fnOff mergeFieldName = 0x581c :=
  CryptoVerification.libsignalSessionCode_fnOff_0x581c

/-! ## Jump-table byte at `.rodata + 0x79029` -/

theorem rodata_jump_tag14_mf14 {s : State} (hF : sessionImg0.FrozenLoaded s) :
    s.mem.read8 (sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) = 0x4c#8 ∧
      s.mem.canRead (sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) 1 = true := by
  have hhb := loads_rodata_holdsBytes E2E.Record.loads_sessionImg0 hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) (n := 1) (bs := [0x4c#8])
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel) rfl (by
      rfl_kernel)
  exact ⟨(holdsBytes_cons_iff.mp hhb).1.1, (memSlice_of_holdsBytes_ro hhb).1⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] SepWP in
theorem step_ldr8_ro_mf14 {prog : Program} {target_pc : BitVec 64}
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

theorem adrp_rodata_mf14 (b : BitVec 64) (hb : b &&& 4095#64 = 0#64) :
    (b + 0x581c#64 + 40#64 &&& 18446744073709547520#64) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" - 0x5000) = b + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
  simp only [hb, arm64_norm]

/-! ## Subroutine entry lemmas -/

theorem decodeVarintSlice_ok_sub_mf14 {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Prost.DecodeVarintSliceOk sessionImg0.base C A0 ctl abs) :
    subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + 118436#64)
      (Prost.decodeVarintSliceSpec A0) := by
  have heq : (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName + 118436#64 =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr Prost.decodeVarintSliceName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.libsignalSessionCode_fnOff_0x581c,
      CryptoVerification.libsignalSessionCode_fnOff_0x226c0]
    bv_omega
  rw [heq]; exact h

theorem int32Merge_ok_sub_mf14 {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Prost.Int32MergeOk sessionImg0.base C A0 ctl abs) :
    subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName +
        18446744073709540264#64)
      (Prost.int32MergeSpec A0) := by
  have heq : (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName +
      18446744073709540264#64 =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr Prost.int32MergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.libsignalSessionCode_fnOff_0x581c,
      CryptoVerification.libsignalSessionCode_fnOff_0x2bc4]
    bv_omega
  rw [heq]; exact h

theorem bytesMerge_ok_sub_mf14 {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Prost.BytesMergeOk sessionImg0 C A0 ctl abs) :
    subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      ((tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName +
        18446744073709539180#64)
      (Prost.bytesMergeSpec A0 sessionImg0) := by
  have heq : (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName +
      18446744073709539180#64 =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr Prost.bytesMergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.libsignalSessionCode_fnOff_0x581c,
      CryptoVerification.libsignalSessionCode_fnOff_0x2788]
    bv_omega
  rw [heq]; exact h

/-! ## Allocation-panic call framing -/

theorem of_sepWP_frozen_mf14 {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_frozen hfl hsym h

/-- Frames a subroutine call whose error path triggers `allocPanic`, threading `FrozenLoaded` and `symtab`. -/
theorem call_alloc_mf14 {α β : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s s0 : State} {P R : SepProp} {Q : State → SepProp → Prop} {y : β}
    (hcall : subroutine_ok prog entry spec)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)))
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)) := by
  refine SepWPp.call_wpp_frozen hcall (x := x) (F := F) hfl hsym hpc hrun hsp hlr
    (fun R' hm => ?_)
    (fun sf code R' _ hpost => by rw [hexit] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm _ _ hm' => ?_)
    hnext
    (hoom := fun sf R' _ hpost => by rw [hoom] at hpost; exact (not_satisfies_false_sepConj hpost).elim)
  · rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  · rw [hpan] at hm'
    dsimp only [allocPanic]
    rw [sepConj_assoc] at hm'
    have h2 : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]; exact hm'
    exact allowPanic_frame (fun h => by simpa only [allocFailedIn, htr] using h) h2

/-! ## Stack-region splits -/

abbrev mergeFieldSubStack_mf14 : Nat := 16144

theorem stackAt_split_top_mf14 (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = stackAt (sp - BitVec.ofNat 64 d) n ∗
      memRegion (sp - BitVec.ofNat 64 d) d := by
  simp only [stackAt]
  rw [memRegion_split' (n := n) (k := d) rfl rfl h]
  have e1 : sp - BitVec.ofNat 64 (n + d) = sp - BitVec.ofNat 64 d - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + d) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 d := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

theorem stackAt_split_bottom_mf14 (sp : BitVec 64) (N n d : Nat) (hN : N = n + d := by decide)
    (h : n + d ≤ 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) d ∗ stackAt sp n := by
  subst hN
  simp only [stackAt]
  rw [show n + d = d + n by omega,
    memRegion_split' (n := d) (k := n) (by omega) rfl (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem stackAt_mergeField_split_mf14 (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStack =
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗
      memRegion (sp0 - 240#64) 160 ∗
      cells (sp0 - 80#64) 10 := by
  have htop := stackAt_split_top_mf14 sp0 mergeFieldSubStack_mf14 240 (by decide)
  change stackAt sp0 mergeFieldStack =
    stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ∗ memRegion (sp0 - 240#64) 240 at htop
  rw [htop,
      memRegion_split' (b := sp0 - 240#64) (b' := sp0 - 80#64) (n := 160) (k := 80)
        rfl (by bv_lin) (by decide),
      show (80 : Nat) = 8 * 10 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 80#64) 10 (by decide)]

theorem memRegion160_split_mf14 (sp0 : BitVec 64) :
    memRegion (sp0 - 240#64) 160 =
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 232#64) 24 ∗ memRegion (sp0 - 208#64) 128 := by
  rw [memRegion_split' (b := sp0 - 240#64) (b' := sp0 - 232#64) (n := 8) (k := 152)
        rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 232#64) (b' := sp0 - 208#64) (n := 24) (k := 128)
        rfl (by bv_lin) (by decide)]

theorem stackAt_sub_to_decode_mf14 (sp : BitVec 64) :
    stackAt sp mergeFieldSubStack_mf14 =
      memRegion (sp - 16144#64) 7872 ∗ stackAt sp Prost.decodeVarintSliceStack :=
  stackAt_split_bottom_mf14 sp mergeFieldSubStack_mf14 Prost.decodeVarintSliceStack 7872

theorem stackAt_sub_to_int32Merge_mf14 (sp : BitVec 64) :
    stackAt sp mergeFieldSubStack_mf14 =
      memRegion (sp - 16144#64) 7792 ∗ stackAt sp Prost.int32MergeStack :=
  stackAt_split_bottom_mf14 sp mergeFieldSubStack_mf14 Prost.int32MergeStack 7792

theorem stackAt_sub_to_bytesMerge_mf14 (sp : BitVec 64) :
    stackAt sp mergeFieldSubStack_mf14 =
      memRegion (sp - 16144#64) 7648 ∗ stackAt sp Prost.bytesMergeStack :=
  stackAt_split_bottom_mf14 sp mergeFieldSubStack_mf14 Prost.bytesMergeStack 7648

theorem stackAt_mergeField_unfold_mf14 (sp0 : BitVec 64) :
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
        memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 232#64) 24 ∗
        memRegion (sp0 - 208#64) 128 ∗
        memRegion (sp0 - 240#64 - 16144#64) 7872 ∗
        stackAt (sp0 - 240#64) Prost.decodeVarintSliceStack := by
  have h1 : stackAt sp0 mergeFieldStack =
      cells (sp0 - 80#64) 10 ∗
      (memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 232#64) 24 ∗
        memRegion (sp0 - 208#64) 128 ∗
        memRegion (sp0 - 240#64 - 16144#64) 7872 ∗
        stackAt (sp0 - 240#64) Prost.decodeVarintSliceStack) := by
    rw [stackAt_mergeField_split_mf14 sp0, memRegion160_split_mf14 sp0,
      stackAt_sub_to_decode_mf14 (sp0 - 240#64)]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin,
    sepConj_assoc]

theorem stackAt_mergeField_fold_mf14 (sp0 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) :
    ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
      ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
      ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
      ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
      ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
      memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 ⊢
      stackAt sp0 mergeFieldStack := by
  have h1 : stackAt sp0 mergeFieldStack =
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStack_mf14) ∗
      cells (sp0 - 80#64) 10 := by
    rw [stackAt_mergeField_split_mf14 sp0]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin]
  refine Entails.trans (Q :=
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStack_mf14) ∗
    (((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
     ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
     ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
     ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
     ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8)))
    (by apply Entails.of_eq; ac_rfl) ?_
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_intro v80) ?_
  refine sepConj_mono (Entails.sepExists_intro v72) ?_
  refine sepConj_mono (Entails.sepExists_intro v64) ?_
  refine sepConj_mono (Entails.sepExists_intro v56) ?_
  refine sepConj_mono (Entails.sepExists_intro v48) ?_
  refine sepConj_mono (Entails.sepExists_intro v40) ?_
  refine sepConj_mono (Entails.sepExists_intro v32) ?_
  refine sepConj_mono (Entails.sepExists_intro v24) ?_
  refine sepConj_mono (Entails.sepExists_intro v16) ?_
  exact Entails.sepExists_intro v8

theorem decode_to_bytesMerge_stack_mf14 (sp : BitVec 64) :
    memRegion (sp - 16144#64) 7872 ∗ stackAt sp Prost.decodeVarintSliceStack =
      memRegion (sp - 16144#64) 7648 ∗ stackAt sp Prost.bytesMergeStack := by
  rw [← stackAt_sub_to_decode_mf14, stackAt_sub_to_bytesMerge_mf14]

theorem decode_to_int32Merge_stack_mf14 (sp : BitVec 64) :
    memRegion (sp - 16144#64) 7872 ∗ stackAt sp Prost.decodeVarintSliceStack =
      memRegion (sp - 16144#64) 7792 ∗ stackAt sp Prost.int32MergeStack := by
  rw [← stackAt_sub_to_decode_mf14, stackAt_sub_to_int32Merge_mf14]

theorem int32Merge_to_bytesMerge_stack_mf14 (sp : BitVec 64) :
    memRegion (sp - 16144#64) 7792 ∗ stackAt sp Prost.int32MergeStack =
      memRegion (sp - 16144#64) 7648 ∗ stackAt sp Prost.bytesMergeStack := by
  rw [← stackAt_sub_to_int32Merge_mf14, stackAt_sub_to_bytesMerge_mf14]

/-- Splits the zeroed 64-bit slot at `sp0 - 232` into two 32-bit halves for `ldr w8, [sp, #8]`. -/
theorem pointsTo64_zero_split32_mf14 (sp0 : BitVec 64) :
    ((sp0 - 232#64) ↦₆₄ 0#64) =
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) := by
  have hs := pointsTo64_split32 (sp0 - 232#64) 0#64
  have ha : (sp0 - 232#64) + 4#64 = sp0 - 228#64 := by bv_omega
  simpa [ha] using hs

theorem cells24_entails_memRegion24_mf14 (sp0 w1 w2 : BitVec 64) :
    ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ w1) ∗ ((sp0 - 216#64) ↦₆₄ w2) ⊢
    memRegion (sp0 - 232#64) 24 := by
  rw [← sepConj_assoc, ← pointsTo64_zero_split32_mf14 sp0]
  rw [memRegion_split' (b := sp0 - 232#64) (b' := sp0 - 224#64) (n := 8) (k := 16)
        rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 224#64) (b' := sp0 - 216#64) (n := 8) (k := 8)
        rfl (by bv_lin) (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  exact sepConj_mono (Entails.sepExists_right 0#64 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (Entails.sepExists_right w2 (Entails.refl _)))

theorem memRegion160_fold_mf14 (sp0 : BitVec 64) :
    memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 232#64) 24 ∗ memRegion (sp0 - 208#64) 128 =
      memRegion (sp0 - 240#64) 160 :=
  (memRegion160_split_mf14 sp0).symm

/-! ## Payload slice cursors (`i = 0`) -/

theorem sliceCursorAt_kyber_unfold_mf14 (slot ptr : BitVec 64) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1574 + tail.length)) ∗
      (ptr ↦ₛ (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)) := by
  unfold Prost.sliceCursorAt
  rw [kyber_payload_tail_length hct, kyber_payload_tail_eq hct]

theorem bytes_kyber_split_mf14 (ptr : BitVec 64) (ib : List (BitVec 8)) :
    (ptr ↦ₛ (164#8 :: 12#8 :: 18#8 :: ib)) =
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ptr + 3#64) ↦ₛ ib) := by
  simp only [pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + 1#64 = ptr + 3#64 by bv_lin]

theorem sliceCursorAfter_inner_unfold_mf14 (slot ptr : BitVec 64) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAfter slot (ptr + 3#64) (innerBytes ct tail) tail =
      (slot ↦₆₄ (ptr + 1574#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) := by
  unfold Prost.sliceCursorAfter
  have hsub : (innerBytes ct tail).length - tail.length = 1571 := by
    rw [innerBytes_length hct]; omega
  have hadd : ptr + 3#64 + BitVec.ofNat 64 1571 = ptr + 1574#64 := by bv_lin
  rw [hsub, hadd]

theorem sliceCursorAt_inner_fold_mf14 (slot ptr : BitVec 64) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 3#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1571 + tail.length)) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) =
      Prost.sliceCursorAt slot (ptr + 3#64) (innerBytes ct tail) := by
  unfold Prost.sliceCursorAt
  rw [innerBytes_length hct]

theorem sliceCursorAfter_kyber_fold_mf14 (slot ptr : BitVec 64) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 1574#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) =
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) tail := by
  unfold Prost.sliceCursorAfter
  have hsub : ((GenFieldX.kyber 0#32 ct).payload ++ tail).length - tail.length = 1574 := by
    rw [kyber_payload_tail_length hct]; omega
  rw [hsub, kyber_payload_tail_eq hct, bytes_kyber_split_mf14]

theorem decode_kyber_result_mf14 {ct : List (BitVec 8)} (_hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ret : BitVec 64) :
    Prost.varintSliceResultAt A0 ret (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)
      (decodeVarint (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 1572) ∗
        ((ret + 16#64) ↦₆₄ 2#64) := by
  rw [decodeVarint_kyber]
  dsimp only [Prost.varintSliceResultAt]
  have : (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail).length -
      (18#8 :: innerBytes ct tail).length = 2 := by
    simp only [List.length_cons]; omega
  rw [this]

/-! ## Payload slice cursors (`i ≠ 0`) -/

/-- Slice pointer to the inner tag-2 key `0x12` after `int32::merge` consumes `pre_key_id`. -/
def kyberPtr2 (ptr : BitVec 64) (i : BitVec 32) : BitVec 64 :=
  ptr + 3#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length

theorem sliceCursorAt_kyber_ne_unfold_mf14 (slot ptr : BitVec 64) {i : BitVec 32} (hi : i ≠ 0#32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenFieldX.kyber i ct).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      (ptr ↦ₛ (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)) := by
  unfold Prost.sliceCursorAt
  rw [kyber_ne_payload_tail_length hi hct, kyber_ne_payload_tail_eq hi hct]

theorem bytes_kyber_ne_split_mf14 (ptr : BitVec 64) (i : BitVec 32) (ib : List (BitVec 8)) :
    (ptr ↦ₛ (kyberB0 i :: 12#8 :: 8#8 :: ib)) =
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ ib) := by
  simp only [pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + 1#64 = ptr + 3#64 by bv_lin]

theorem decode_kyber_ne_result_mf14 (i : BitVec 32) {ct : List (BitVec 8)} (_hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ret : BitVec 64) :
    Prost.varintSliceResultAt A0 ret (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)
      (decodeVarint (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)) =
      (ret ↦₆₄ 0#64) ∗
        ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((ret + 16#64) ↦₆₄ 2#64) := by
  rw [decodeVarint_kyber_ne]
  dsimp only [Prost.varintSliceResultAt]
  have : (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail).length -
      (8#8 :: kyberIdBytes i ct tail).length = 2 := by
    simp only [List.length_cons]; omega
  rw [this]

theorem sliceCursorAt_kyberId_fold_mf14 (slot ptr : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 3#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) =
      Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) := by
  unfold Prost.sliceCursorAt
  rw [kyberIdBytes_length i hct]

theorem sliceCursorAfter_kyberId_unfold_mf14 (slot ptr : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAfter slot (ptr + 3#64) (kyberIdBytes i ct tail)
        (18#8 :: innerBytes ct tail) =
      (slot ↦₆₄ kyberPtr2 ptr i) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + tail.length)) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) := by
  unfold Prost.sliceCursorAfter kyberIdBytes kyberPtr2
  have hsub : (encodeVarint (i.setWidth 64) ++ 18#8 :: innerBytes ct tail).length -
      (18#8 :: innerBytes ct tail).length = (encodeVarint (i.setWidth 64)).length := by
    rw [List.length_append]; omega
  have hlen : (18#8 :: innerBytes ct tail).length = 1572 + tail.length := by
    rw [List.length_cons, innerBytes_length hct]; omega
  rw [hsub, hlen, pointsToBytes_append, pointsToBytes_cons]

theorem sliceCursorAt_inner_ne_fold_mf14 (slot ptr : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (kyberPtr2 ptr i + 1#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1571 + tail.length)) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) =
      Prost.sliceCursorAt slot (kyberPtr2 ptr i + 1#64) (innerBytes ct tail) := by
  unfold Prost.sliceCursorAt
  rw [innerBytes_length hct]

theorem sliceCursorAfter_inner_ne_unfold_mf14 (slot ptr : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAfter slot (kyberPtr2 ptr i + 1#64) (innerBytes ct tail) tail =
      (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) := by
  unfold Prost.sliceCursorAfter
  have hsub : (innerBytes ct tail).length - tail.length = 1571 := by
    rw [innerBytes_length hct]; omega
  have hadd : kyberPtr2 ptr i + 1#64 + BitVec.ofNat 64 1571 = kyberPtr2 ptr i + 1572#64 := by bv_lin
  rw [hsub, hadd]

theorem sliceCursorAfter_kyber_ne_fold_mf14 (slot ptr : BitVec 64) {i : BitVec 32} (hi : i ≠ 0#32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) =
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber i ct).payload ++ tail) tail := by
  unfold Prost.sliceCursorAfter
  have hsub : ((GenFieldX.kyber i ct).payload ++ tail).length - tail.length =
      1575 + (encodeVarint (i.setWidth 64)).length := by
    rw [kyber_ne_payload_tail_length hi hct]; omega
  have hptr : ptr + BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length) =
      kyberPtr2 ptr i + 1572#64 := by
    unfold kyberPtr2
    rw [BitVec.ofNat_add]
    bv_lin
  rw [hsub, hptr, kyber_ne_payload_tail_eq hi hct, bytes_kyber_ne_split_mf14]
  unfold kyberIdBytes
  rw [pointsToBytes_append, pointsToBytes_cons, ← kyberPtr2]

/-! ## Length arithmetic -/

theorem bv_ofNat_add_eq {a b n : Nat} (_h : a + b + n < 2 ^ 32) :
    BitVec.ofNat 64 (a + b + n) = BitVec.ofNat 64 (a + n) + BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem len_sub_mf14 {a b n : Nat} (hb : b ≤ a) (_h : a + n < 2 ^ 32) :
    BitVec.ofNat 64 (a + n) - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
