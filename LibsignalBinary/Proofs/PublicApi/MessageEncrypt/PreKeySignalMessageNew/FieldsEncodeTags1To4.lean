/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeDecodes
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarint
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::new` Field Encoding: Tags 1–3

Shared register/frame invariants, `encode_varint` and `memcpy` call helpers, and symbolic execution
steps for protobuf tags 1 (`pre_key_id`), 2 (`base_key`), and 3 (`identity_key`) (`+0x25c..+0x35c`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open ProofLib.ProgramReflection
open EncodeVarintNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

abbrev preKeyMsgNewName : String :=
  "<libsignal_protocol::protocol::PreKeySignalMessage>::new"

theorem preKeyMsgNew_fnAddr_eq_trap (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = b + 0x15130#64 := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x15130]

theorem preKeyMsgNew_add_encVarint_eq_trap (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 18446744073709477744#64 =
      (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      libsignalSessionCode_fnOff_0x15130, libsignalSessionCode_fnOff_0x30a0]
  bv_omega

theorem preKeyMsgNew_fnAddr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName = b + 0x15130#64 := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x15130]

theorem preKeyMsgNew_add_encVarint_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 18446744073709477744#64 =
      (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    libsignalSessionCode_fnOff_0x15130, libsignalSessionCode_fnOff_0x30a0, BitVec.add_assoc]
  rfl

/-! ## Frame Pointer and `serialized` Address Normalization -/

@[simp, arm64_norm, wp_norm]
theorem fp_sub_48_eq (sp : BitVec 64) :
    (sp + 272#64) + 18446744073709551568#64 = sp + 224#64 := by
  rw [BitVec.add_assoc]; rfl

@[simp, arm64_norm, wp_norm]
theorem fp_sub_48_sub_eq (sp : BitVec 64) :
    (sp + 272#64) - 48#64 = sp + 224#64 := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

@[simp, arm64_norm, wp_norm]
theorem fp_sub_40_eq (sp : BitVec 64) :
    (sp + 272#64) + 18446744073709551576#64 = (sp + 224#64) + 8#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

@[simp, arm64_norm, wp_norm]
theorem fp_sub_32_eq (sp : BitVec 64) :
    (sp + 272#64) + 18446744073709551584#64 = (sp + 224#64) + 16#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem sp0_sub_96_eq_sp_add_272 (sp0 : BitVec 64) :
    sp0 - 0x60#64 = (sp0 - 0x170#64) + 272#64 := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

/-! ## Call and Stack Helpers for Field Encoding -/

theorem cap_sub_len_ult_false {bs : List (BitVec 8)} {n : Nat} {cap : BitVec 64}
    (hle : bs.length + n ≤ cap.toNat) :
    (cap - BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 n) = false := by
  have hcap := cap.isLt
  have hbs : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat]; omega
  have hsub : (cap - BitVec.ofNat 64 bs.length).toNat = cap.toNat - bs.length := by
    rw [BitVec.toNat_sub_of_le]
    · exact congrArg (cap.toNat - ·) hbs
    · rw [BitVec.le_def]; omega
  simp only [BitVec.ult_eq_decide, hsub, hn, decide_eq_false_iff_not]
  omega

theorem cap_sub_len_ule_true {bs : List (BitVec 8)} {n : Nat} {cap : BitVec 64}
    (hle : bs.length + n ≤ cap.toNat) :
    (BitVec.ofNat 64 n).ule (cap - BitVec.ofNat 64 bs.length) = true := by
  have hcap := cap.isLt
  have hbs : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat]; omega
  have hsub : (cap - BitVec.ofNat 64 bs.length).toNat = cap.toNat - bs.length := by
    rw [BitVec.toNat_sub_of_le]
    · exact congrArg (cap.toNat - ·) hbs
    · rw [BitVec.le_def]; omega
  simp only [BitVec.ule_eq_decide, hsub, hn, decide_eq_true_eq]
  omega

theorem bv_len_add_slice (bs payload : List (BitVec 8)) :
    BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length =
      BitVec.ofNat 64 (bs ++ payload).length := by
  simp [List.length_append, BitVec.ofNat_add]

theorem boxU8Buf_nonempty_eq (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) :
    boxU8Buf A ptr bs =
      (ptr ↦ₛ bs) ∗ (⌜ptr ≠ 0#64 ∧ bs.length < 2 ^ 63⌝ ∗ A.live ptr bs.length 1) := by
  simp only [boxU8Buf, hne, ↓reduceIte]
  ac_rfl

/-- Callee-saved registers preserved across all eight field-encoding blocks. -/
def PreKeyMsgTagRegs (s0 s : State) : Prop :=
  s.readReg64 .x19 = s0.readReg64 .x19 ∧
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.readReg64 .fp = s0.readReg64 .fp ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem PreKeyMsgTagRegs.trans {s0 s1 s2 : State} (h1 : PreKeyMsgTagRegs s0 s1) (h2 : PreKeyMsgTagRegs s1 s2) :
    PreKeyMsgTagRegs s0 s2 := by
  reg_chain

theorem PreKeyMsgTagRegs.of_calleeSaved {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    PreKeyMsgTagRegs s0 s1 := by
  reg_chain

theorem preKeyMsgCommonRegs_of_tagRegs {x : PreKeyMsgNewCall} {g : PreKeyMsgFrameGhost} {s0 s sf : State}
    (h : preKeyMsgCommonRegs x g s0 s)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s.sp)
    (htr : sf.trace = s.trace)
    (hregs : PreKeyMsgTagRegs s sf) :
    preKeyMsgCommonRegs x g s0 sf := by
  have hsf_al : sf.spAligned = true := by simpa only [State.spAligned, hsp] using h.2.2.2.1
  exact ⟨hrun, by reg_chain, h.2.2.1, hsf_al, by reg_chain⟩

theorem stackAt_preKeyMsgSubStack_eq_encodeVarint (sp : BitVec 64) :
    stackAt sp preKeyMsgSubStack =
      stackAt sp encodeVarintStack ∗
      memRegion (sp - 7824#64) 3568 := by
  unfold stackAt
  rw [memRegion_split'
    (b := sp - BitVec.ofNat 64 preKeyMsgSubStack)
    (b' := sp - BitVec.ofNat 64 encodeVarintStack)
    (n := 3568)
    (k := encodeVarintStack)
    (by decide)
    (by
      change sp - 4256#64 = sp - 7824#64 + 3568#64
      exact (bv_sub_add_lit sp 7824 3568).symm)
    (by decide)]
  exact sepConj_comm _ _

theorem stackAt_preKeyMsgSubStack_eq_allocHook (sp : BitVec 64) :
    stackAt sp preKeyMsgSubStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 7824#64) 3728 := by
  unfold stackAt
  rw [memRegion_split' (b := sp - BitVec.ofNat 64 preKeyMsgSubStack)
    (b' := sp - BitVec.ofNat 64 allocHookStack) (n := 3728) (k := allocHookStack) (by decide)
    (by change sp - 4096#64 = sp - 7824#64 + 3728#64; exact (bv_sub_add_lit sp 7824 3728).symm)
    (by decide)]
  exact sepConj_comm _ _

theorem call_noPanic {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf R', sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr
    (fun R hm => ?_) hexit
    (fun sf hpan ⟨R', hpost⟩ => (hpanic sf R' hpan hpost).elim)
    hnext
    (hoom := fun sf R' hoom_st hpost => (hoom sf (F ∗ R') hoom_st hpost).elim)
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

theorem step_call_encVarint_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    (hle : bs.length + (encodeVarint val).length ≤ cap.toNat)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 18446744073709477744#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp)
    (halign : s0.spAligned = true)
    (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr)
    (hregs : PreKeyMsgTagRegs s_init s0)
    (hx0 : s0.readReg64 .x0 = val)
    (hx1 : s0.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = tr →
      PreKeyMsgTagRegs s_init sf →
      SepWPp (tripleRatchetProgAtExt b ext) ret sf
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
          vecU8Buf A cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s0 P Q Qp := by
  rw [preKeyMsgNew_add_encVarint_eq_trap] at hpc
  subst hsp
  refine call_noPanic (x := ⟨val, v, cap, ptr, bs⟩)
    (F := memRegion (s0.sp - 7824#64) 3568 ∗ F)
    (encodeVarintNoGrow_fnAddr_ok_trap b A ext)
    hpc hrun halign rfl rfl ⟨hx0, hx1, hle⟩
    (by
      rw [hP, stackAt_preKeyMsgSubStack_eq_encodeVarint s0.sp, vecU8At_eq_header_sep_buf, vecHeader]
      ac_rfl)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [encodeVarintNoGrowSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htrf => ?_
  have heq :
      (vecU8At A v cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt s0.sp encodeVarintStack) ∗
        memRegion (s0.sp - 7824#64) 3568 ∗ F =
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
        vecU8Buf A cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt s0.sp preKeyMsgSubStack) ∗ F) := by
    rw [stackAt_preKeyMsgSubStack_eq_encodeVarint s0.sp, vecU8At_eq_header_sep_buf, vecHeader]
    ac_rfl
  rw [heq]
  exact hnext sf (hpcf.trans hlr) hrunf hspf (htrf.trans htr) (by reg_chain)

theorem step_call_encVarint (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    (hle : bs.length + (encodeVarint val).length ≤ cap.toNat)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 18446744073709477744#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp)
    (halign : s0.spAligned = true)
    (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr)
    (hregs : PreKeyMsgTagRegs s_init s0)
    (hx0 : s0.readReg64 .x0 = val)
    (hx1 : s0.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = tr →
      PreKeyMsgTagRegs s_init sf →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sf
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
          vecU8Buf A cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s0 P Q Qp :=
  step_call_encVarint_trap b A (tripleRatchetExterns C ctl abs) val v cap ptr sp ret_pc bs tr s_init hle hpc hrun hsp halign hlr htr hregs hx0 hx1 hP hnext

theorem hookSat_memcpy_of_withPanics {ext : String → Option (State → State)}
    (hmemcpy : Rust.withPanics ext "memcpy" = some hookMemcpy) :
    HookSat ext memcpyName (sessionMemcpySpec allocHookStack) :=
  ⟨hookMemcpy, by simpa [Rust.withPanics, Rust.isPanicSymbol, memcpyName] using hmemcpy,
    hookMemcpy_trace_ok allocHookStack⟩

theorem preKeyMsg_memcpy_ok_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + bv% (ls_off% "memcpy" - 0x15130))
      (sessionMemcpySpec allocHookStack) := by
  rcases hMc with ⟨fn, hfn, hsat⟩
  exact hook_ok_at_raw libsignalSessionCode_fnOff_0x15130 (k := num% (ls_off% "memcpy" - 0x15130))
    rfl (by decide) (ls_hook% "memcpy")
    ⟨fn, by simp [Rust.withPanics, Rust.isPanicSymbol, memcpyName] at hfn ⊢; exact hfn, hsat⟩

theorem step_call_memcpy_ext (b : BitVec 64) (ext : String → Option (State → State))
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (dst src sp ret_pc v23 v26 : BitVec 64) (payload : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + bv% (ls_off% "memcpy" - 0x15130))
    (hrun : s0.status = .Running) (hsp : s0.sp = sp) (halign : s0.spAligned = true)
    (hlr : s0.readReg64 .lr = ret_pc) (htr : s0.trace = tr) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx23 : s0.readReg64 .x23 = v23) (hx26 : s0.readReg64 .x26 = v26)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = payload.length)
    (hP : P = (memRegion dst payload.length ∗ (src ↦ₛ payload) ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = tr → PreKeyMsgTagRegs s_init sf → sf.readReg64 .x23 = v23 →
      sf.readReg64 .x26 = v26 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sf
        (((dst ↦ₛ payload) ∗ (src ↦ₛ payload) ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s0 P Q Qp := by
  subst hsp
  refine call_noPanic (x := (dst, src, payload))
    (φ := (s0.readReg64 .x2).toNat = payload.length ∧ s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src)
    (T := memRegion dst payload.length ∗ (src ↦ₛ payload) ∗ stackAt s0.sp allocHookStack)
    (F := memRegion (s0.sp - 7824#64) 3728 ∗ F)
    (preKeyMsg_memcpy_ok_ext hMc) hpc hrun halign rfl
    (by dsimp only [sessionMemcpySpec, libcMemcpySpec]; ac_rfl) ⟨hx2, hx0, hx1⟩
    (by rw [hP, stackAt_preKeyMsgSubStack_eq_allocHook s0.sp]; ac_rfl)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [sessionMemcpySpec, libcMemcpySpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, htrf⟩ => ?_
  have heq :
      ((dst ↦ₛ payload) ∗ (src ↦ₛ payload) ∗ stackAt s0.sp allocHookStack) ∗
        (memRegion (s0.sp - 7824#64) 3728 ∗ F) =
      (((dst ↦ₛ payload) ∗ (src ↦ₛ payload) ∗ stackAt s0.sp preKeyMsgSubStack) ∗ F) := by
    rw [stackAt_preKeyMsgSubStack_eq_allocHook s0.sp]; ac_rfl
  rw [heq]
  exact hnext sf (hpcf.trans hlr) hrunf hspf (htrf.trans htr)
    (by reg_chain) (by reg_chain) (by reg_chain)

theorem preKeyMsg_memcpy_ok_trap {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : Rust.withPanics ext "memcpy" = some hookMemcpy) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + bv% (ls_off% "memcpy" - 0x15130)) framelessMemcpySpec :=
  hook_ok_at_raw libsignalSessionCode_fnOff_0x15130 (k := num% (ls_off% "memcpy" - 0x15130)) rfl (by decide)
    (ls_hook% "memcpy") ⟨hookMemcpy, hmemcpy, framelessMemcpy_hookOk⟩

theorem preKeyMsg_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + bv% (ls_off% "memcpy" - 0x15130)) framelessMemcpySpec :=
  hook_ok_at_raw libsignalSessionCode_fnOff_0x15130 (k := num% (ls_off% "memcpy" - 0x15130)) rfl (by decide)
    (ls_hook% "memcpy") ⟨hookMemcpy, rfl, framelessMemcpy_hookOk⟩

theorem step_call_memcpy_trap (b : BitVec 64)
    (ext : String → Option (State → State))
    (hmemcpy : Rust.withPanics ext "memcpy" = some hookMemcpy)
    (dst src sp ret_pc v23 v26 : BitVec 64) (payload : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + bv% (ls_off% "memcpy" - 0x15130))
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp)
    (halign : s0.spAligned = true)
    (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr)
    (hregs : PreKeyMsgTagRegs s_init s0)
    (hx23 : s0.readReg64 .x23 = v23)
    (hx26 : s0.readReg64 .x26 = v26)
    (hx0 : s0.readReg64 .x0 = dst)
    (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = payload.length)
    (hP : P = (memRegion dst payload.length ∗ (src ↦ₛ payload)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = tr →
      PreKeyMsgTagRegs s_init sf →
      sf.readReg64 .x23 = v23 →
      sf.readReg64 .x26 = v26 →
      SepWPp (tripleRatchetProgAtExt b ext) ret sf
        (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s0 P Q Qp := by
  subst hsp
  refine call_noPanic (x := (dst, src, payload)) (F := F)
    (preKeyMsg_memcpy_ok_trap hmemcpy) hpc hrun halign rfl rfl ⟨hx0, hx1, hx2⟩ hP
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [framelessMemcpySpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, htrf⟩ => ?_
  simpa only [sepConj_assoc] using hnext sf (hpcf.trans hlr) hrunf hspf (htrf.trans htr)
    (by reg_chain) (by reg_chain) (by reg_chain)

theorem step_call_memcpy (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (dst src sp ret_pc v23 v26 : BitVec 64) (payload : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + bv% (ls_off% "memcpy" - 0x15130))
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp)
    (halign : s0.spAligned = true)
    (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr)
    (hregs : PreKeyMsgTagRegs s_init s0)
    (hx23 : s0.readReg64 .x23 = v23)
    (hx26 : s0.readReg64 .x26 = v26)
    (hx0 : s0.readReg64 .x0 = dst)
    (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = payload.length)
    (hP : P = (memRegion dst payload.length ∗ (src ↦ₛ payload)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = tr →
      PreKeyMsgTagRegs s_init sf →
      sf.readReg64 .x23 = v23 →
      sf.readReg64 .x26 = v26 →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sf
        (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s0 P Q Qp :=
  step_call_memcpy_trap b (tripleRatchetExterns C ctl abs) rfl dst src sp ret_pc v23 v26 payload tr s_init hpc hrun hsp halign hlr htr hregs hx23 hx26 hx0 hx1 hx2 hP hnext

/-! ## Tag 1 (`pre_key_id`, `+0x25c..+0x2a0`) -/

theorem step_preKeyMsg_tag1_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 604#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix0 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 672#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf604 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 604)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1538c
  have hf608 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 608)
    libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15390
  rcases hwf with ⟨hser_lt, _, hpk_val, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  subst hP
  cases hpk : x.preKeyId with
  | none =>
    have hf668 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 668)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153cc
    simp only [hpk, Option.isSome, Bool.false_eq_true, ↓reduceIte] at hx20
    have hw20 : s.readReg32 .x20 = 0#32 := by simpa [State.readReg32] using hx20
    have hser1 : serPrefix1 x = serPrefix0 x := by
      simp [serPrefix1, hpk, LibsignalSessionApi.Prost.uint32Field]
    have h1_len_bv : BitVec.ofNat 64 (serPrefix1 x).length = 1#64 := by
      simp [hser1, h0_len]
    revert hpc hnext hf604 hf608 hf668
    generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry0
    intro hpc hnext hf604 hf608 hf668
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry0 + 672#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [← hser1]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [h1_len_bv]; simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
  | some pid =>
    have hf612 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 612) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15394
    have hf616 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 616) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15398
    have hf620 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 620) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1539c
    have hf624 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 624) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153a0
    have hf628 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 628) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153a4
    have hf632 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 632) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153a8
    have hf636 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 636) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153ac
    have hf640 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 640) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153b0
    have hf644 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 644) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153b4
    have hf648 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 648) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153b8
    have hf652 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 652) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153bc
    have hf656 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 656) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153c0
    simp only [hpk, Option.isSome, ↓reduceIte] at hx20
    rw [hpk_val pid hpk] at hx25
    have hw20 : s.readReg32 .x20 = 1#32 := by simpa [State.readReg32] using hx20
    have hw25 : s.readReg32 .x25 = pid := by simpa [State.readReg32] using hx25
    have hser1 : (serPrefix0 x ++ [0x08#8]) ++ encodeVarint (pid.zeroExtend 64) = serPrefix1 x := by
      simp [serPrefix1, hpk, prost_uint32Field_some, prost_key_1_0, List.append_assoc]
    have h1_len : (serPrefix1 x).length = 2 + (encodeVarint (pid.zeroExtend 64)).length := by
      rw [← hser1, List.length_append, List.length_append, h0_len, List.length_singleton]
    have hvar_pos : 1 ≤ (encodeVarint (pid.zeroExtend 64)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hlt0 : (serPrefix0 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      omega
    have hbeq0 := cap_beq_len_false hlt0
    have h0_len_bv : BitVec.ofNat 64 (serPrefix0 x).length = 1#64 := by simp [h0_len]
    rw [h0_len_bv] at hbeq0
    have hle_var : (serPrefix0 x ++ [0x08#8]).length + (encodeVarint (pid.zeroExtend 64)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, h0_len, List.length_singleton]; omega
    rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) hlt0,
      h0_len_bv]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    revert hpc hf604 hf608 hf612 hf616 hf620 hf624 hf628 hf632 hf636 hf640 hf644 hf648 hf652 hf656
    generalize h_entry1 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry1
    intro hpc hf604 hf608 hf612 hf616 hf620 hf624 hf628 hf632 hf636 hf640 hf644 hf648 hf652 hf656
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry1 + 18446744073709477744#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [← h_entry1]; clear h_entry1
    have hsnoc := vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) 8#8 hlt0
    rw [h0_len_bv] at hsnoc
    rw [hsnoc]
    refine step_call_encVarint_trap b A ext (pid.zeroExtend 64) (sp + 224#64)
      (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 660#64)
      (serPrefix0 x ++ [8#8]) s.trace s hle_var (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp [h0_len])
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hregs1 => ?_
    have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
    rw [hser1]
    have hf660 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 660)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153c4
    have hf664 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
      (H := Rust.withPanics (ext)) (k := 664)
      libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153c8
    revert hnext hpcf1 hf660 hf664
    generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry2
    intro hnext hpcf1 hf660 hf664
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry2 + 672#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag1 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 604#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix0 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 672#64 →
      sm.status = .Running →
      sm.sp = sp →
      sm.trace = s.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_preKeyMsg_tag1_trap b A (tripleRatchetExterns C ctl abs) x g sp hwf hpc hrun hsp halign hfp hx20 hx25 hP hnext

theorem bv_len_beq_zero_false {bs : List (BitVec 8)} (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 64) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

/-! ## Tag 2 (`base_key`, `+0x2a0..+0x300`) -/

theorem step_preKeyMsg_tag2_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 672#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length)
    (hx24 : s.readReg64 .x24 = 33#64) (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
      boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 768#64 →
      sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
          boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hbk_len : x.baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbk_bv : BitVec.ofNat 64 x.baseKey.serialize.length = 33#64 := by simp [hbk_len]
  have hser2 : (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) ++ x.baseKey.serialize = serPrefix2 x := by
    rw [serPrefix2, prost_bytesField_some 2 x.baseKey.serialize (by omega), prost_key_2_2, hbk_bv]
    simp only [← List.append_assoc, List.singleton_append]
  have hvar33_len : (encodeVarint 33#64).length = 1 := by rw [encodeVarint_33]; rfl
  have h2_len : (serPrefix2 x).length = (serPrefix1 x).length + 1 + 1 + 33 := by
    rw [← hser2, List.length_append, List.length_append, List.length_cons, hvar33_len, hbk_len]
  have hlt1 : (serPrefix1 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq1 := cap_beq_len_false hlt1
  have hle_var : (serPrefix1 x ++ [0x12#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton, hvar33_len]; omega
  have hle_slice : (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length +
      x.baseKey.serialize.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons, hvar33_len, hbk_len]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) hlt1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  have hf672 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 672) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153d0
  have hf676 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 676) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153d4
  have hf680 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 680) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153d8
  have hf684 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 684) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153dc
  have hf688 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 688) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153e0
  have hf692 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 692) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153e4
  have hf696 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 696) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153e8
  have hf700 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 700) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153ec
  have hf704 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 704) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153f0
  have hf708 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 708) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153f4
  have hf712 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 712) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153f8
  revert hpc hf672 hf676 hf680 hf684 hf688 hf692 hf696 hf700 hf704 hf708 hf712
  generalize h_entry1 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry1
  intro hpc hf672 hf676 hf680 hf684 hf688 hf692 hf696 hf700 hf704 hf708 hf712
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry1 + 18446744073709477744#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [← h_entry1]; clear h_entry1
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) 18#8 hlt1,
    bv_len_add_one (serPrefix1 x) 18#8]
  refine step_call_encVarint_trap b A ext 33#64 (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 716#64)
    (serPrefix1 x ++ [18#8]) s.trace s hle_var
    (F := boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx24_1 : sf1.readReg64 .x24 = 33#64 := by reg_chain
  have hx28_1 : sf1.readReg64 .x28 = g.bkSerPtr := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  rw [hbk_bv] at hult1 hule1
  have hbk_ne : x.baseKey.serialize ≠ [] := by intro h; simp [h] at hbk_len
  rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length hle_slice hcap_pos,
    boxU8Buf_nonempty_eq A g.bkSerPtr x.baseKey.serialize hbk_ne]
  have hf716 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 716) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x153fc
  have hf720 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 720) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15400
  have hf724 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 724) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15404
  have hf728 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 728) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15408
  have hf732 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 732) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1540c
  have hf736 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 736) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15410
  have hf740 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 740) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15414
  have hf744 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 744) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15418
  have hf748 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 748) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1541c
  have hf752 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 752) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15420
  have hf756 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 756) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15424
  revert hpcf1 hf716 hf720 hf724 hf728 hf732 hf736 hf740 hf744 hf748 hf752 hf756
  generalize h_entry2 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry2
  intro hpcf1 hf716 hf720 hf724 hf728 hf732 hf736 hf740 hf744 hf748 hf752 hf756
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry2 + bv% (ls_off% "memcpy" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [← h_entry2]; clear h_entry2
  refine step_call_memcpy_ext b ext hMc
    (g.serPtr + BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length)
    g.bkSerPtr sp ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 760#64)
    (BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length)
    (BitVec.ofNat 64 x.model.serialized.length) x.baseKey.serialize s.trace s
    (F := ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
      vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length ∗
      A.pool ∗
      (⌜g.bkSerPtr ≠ 0#64 ∧ x.baseKey.serialize.length < 2 ^ 63⌝ ∗ A.live g.bkSerPtr x.baseKey.serialize.length 1) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf2 hpcf2 hrunf2 hspf2 htrf2 hregs2 hx23_2 hx26_2 => ?_
  have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx24_2 : sf2.readReg64 .x24 = 33#64 := by reg_chain
  simp only [arm64_norm] at hx23_2 hx24_2
  have hadd_len : BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length + 33#64 =
      BitVec.ofNat 64 (serPrefix2 x).length := by
    simp only [h2_len, List.length_append, List.length_cons, hvar33_len, BitVec.ofNat_add]
    ac_rfl
  clear h2_len
  have hpost_eq :
      (((g.serPtr + BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ↦ₛ x.baseKey.serialize) ∗
        (g.bkSerPtr ↦ₛ x.baseKey.serialize) ∗ stackAt sp preKeyMsgSubStack) ∗
      (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
        vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length ∗
        A.pool ∗
        (⌜g.bkSerPtr ≠ 0#64 ∧ x.baseKey.serialize.length < 2 ^ 63⌝ ∗
          A.live g.bkSerPtr x.baseKey.serialize.length 1) ∗ F) =
      ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
    rw [← hser2,
      ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize hcap_pos,
      boxU8Buf_nonempty_eq A g.bkSerPtr x.baseKey.serialize hbk_ne]
    ac_rfl
  rw [hpost_eq]
  have hf760 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 760) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15428
  have hf764 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 764) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1542c
  revert hnext hpcf2 hf760 hf764
  generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry3
  intro hnext hpcf2 hf760 hf764
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry3 + 768#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag2_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hmemcpy : Rust.withPanics ext "memcpy" = some hookMemcpy)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 672#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length)
    (hx24 : s.readReg64 .x24 = 33#64) (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
      boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 768#64 →
      sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
          boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp :=
  step_preKeyMsg_tag2_ext b A ext (hookSat_memcpy_of_withPanics hmemcpy) x g sp hwf
    hpc hrun hsp halign hfp hx1 hx24 hx28 hP hnext

theorem step_preKeyMsg_tag2 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost)
    (sp : BitVec 64) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 672#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length)
    (hx24 : s.readReg64 .x24 = 33#64) (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
      boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 768#64 →
      sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length → PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
          boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_preKeyMsg_tag2_trap b A (tripleRatchetExterns C ctl abs) rfl x g sp hwf hpc hrun hsp halign hfp hx1 hx24 hx28 hP hnext

/-! ## Tag 3 (`identity_key`, `+0x300..+0x35c`) -/

theorem step_preKeyMsg_tag3_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 768#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64) (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
      boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 860#64 →
      sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
          boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  rcases hwf with ⟨hser_lt, _⟩
  have hik_len : x.ik.serialize.length = 33 := by simp [IdentityKey.serialize, PublicKey.serialize]
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hik_bv : BitVec.ofNat 64 x.ik.serialize.length = 33#64 := by simp [hik_len]
  have hser3 : (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) ++ x.ik.serialize = serPrefix3 x := by
    rw [serPrefix3, prost_bytesField_some 3 x.ik.serialize (by omega), prost_key_3_2, hik_bv]
    simp only [← List.append_assoc, List.singleton_append]
  have hvar33_len : (encodeVarint 33#64).length = 1 := by rw [encodeVarint_33]; rfl
  have h3_len : (serPrefix3 x).length = (serPrefix2 x).length + 1 + 1 + 33 := by
    rw [← hser3, List.length_append, List.length_append, List.length_cons, hvar33_len, hik_len]
  have hlt2 : (serPrefix2 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq2 := cap_beq_len_false hlt2
  have hle_var : (serPrefix2 x ++ [26#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton, hvar33_len]; omega
  have hle_slice : (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length +
      x.ik.serialize.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons, hvar33_len, hik_len]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) hlt2]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  have hf768 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 768) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15430
  have hf772 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 772) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15434
  have hf776 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 776) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15438
  have hf780 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 780) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1543c
  have hf784 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 784) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15440
  have hf788 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 788) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15444
  have hf792 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 792) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15448
  have hf796 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 796) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1544c
  have hf800 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 800) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15450
  have hf804 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 804) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15454
  revert hpc hf768 hf772 hf776 hf780 hf784 hf788 hf792 hf796 hf800 hf804
  generalize h_entry1 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry1
  intro hpc hf768 hf772 hf776 hf780 hf784 hf788 hf792 hf796 hf800 hf804
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry1 + 18446744073709477744#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [← h_entry1]; clear h_entry1
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) 26#8 hlt2,
    bv_len_add_one (serPrefix2 x) 26#8]
  refine step_call_encVarint_trap b A ext 33#64 (sp + 224#64)
    (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 808#64)
    (serPrefix2 x ++ [26#8]) s.trace s hle_var
    (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx22_1 : sf1.readReg64 .x22 = 33#64 := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  rw [hik_bv] at hult1 hule1
  have hik_ne : x.ik.serialize ≠ [] := by intro h; simp [h] at hik_len
  rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length hle_slice hcap_pos,
    boxU8Buf_nonempty_eq A g.ikSerPtr x.ik.serialize hik_ne]
  have hf808 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 808) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15458
  have hf812 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 812) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1545c
  have hf816 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 816) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15460
  have hf820 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 820) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15464
  have hf824 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 824) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15468
  have hf828 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 828) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1546c
  have hf832 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 832) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15470
  have hf836 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 836) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15474
  have hf840 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 840) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15478
  have hf844 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 844) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x1547c
  have hf848 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 848) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15480
  revert hpcf1 hf808 hf812 hf816 hf820 hf824 hf828 hf832 hf836 hf840 hf844 hf848
  generalize h_entry2 : (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry2
  intro hpcf1 hf808 hf812 hf816 hf820 hf824 hf828 hf832 hf836 hf840 hf844 hf848
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry2 + bv% (ls_off% "memcpy" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [← h_entry2]; clear h_entry2
  refine step_call_memcpy_ext b ext hMc
    (g.serPtr + BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length)
    g.ikSerPtr sp ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 852#64)
    (BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length)
    (BitVec.ofNat 64 x.model.serialized.length) x.ik.serialize s.trace s
    (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
      vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length ∗
      A.pool ∗
      (⌜g.ikSerPtr ≠ 0#64 ∧ x.ik.serialize.length < 2 ^ 63⌝ ∗ A.live g.ikSerPtr x.ik.serialize.length 1) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign1)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf2 hpcf2 hrunf2 hspf2 htrf2 hregs2 hx23_2 hx26_2 => ?_
  have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx22_2 : sf2.readReg64 .x22 = 33#64 := by reg_chain
  simp only [arm64_norm] at hx23_2 hx22_2
  have hadd_len : BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length + 33#64 =
      BitVec.ofNat 64 (serPrefix3 x).length := by
    simp only [h3_len, List.length_append, List.length_cons, hvar33_len, BitVec.ofNat_add]
    ac_rfl
  clear h3_len
  have hpost_eq :
      (((g.serPtr + BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ↦ₛ x.ik.serialize) ∗
        (g.ikSerPtr ↦ₛ x.ik.serialize) ∗ stackAt sp preKeyMsgSubStack) ∗
      (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
        vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length ∗
        A.pool ∗
        (⌜g.ikSerPtr ≠ 0#64 ∧ x.ik.serialize.length < 2 ^ 63⌝ ∗
          A.live g.ikSerPtr x.ik.serialize.length 1) ∗ F) =
      ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
        boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
    rw [← hser3,
      ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize hcap_pos,
      boxU8Buf_nonempty_eq A g.ikSerPtr x.ik.serialize hik_ne]
    ac_rfl
  rw [hpost_eq]
  have hf852 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 852) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15484
  have hf856 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 856) libsignalSessionCode_fnOff_0x15130 (by decide) preKeyMsgNewBin_decode_0x15488
  revert hnext hpcf2 hf852 hf856
  generalize (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry3
  intro hnext hpcf2 hf852 hf856
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry3 + 860#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag3_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hmemcpy : Rust.withPanics ext "memcpy" = some hookMemcpy)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 768#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64) (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
      boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 860#64 →
      sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
          boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp :=
  step_preKeyMsg_tag3_ext b A ext (hookSat_memcpy_of_withPanics hmemcpy) x g sp hwf
    hpc hrun hsp halign hfp hx22 hx23 hx26 hP hnext

theorem step_preKeyMsg_tag3 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost)
    (sp : BitVec 64) (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 768#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 272#64) (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
      boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 860#64 →
      sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length → PreKeyMsgTagRegs s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
          boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_preKeyMsg_tag3_trap b A (tripleRatchetExterns C ctl abs) rfl x g sp hwf hpc hrun hsp halign hfp hx22 hx23 hx26 hP hnext

/-! ## Relocatable Placement Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

def EncodePanicPost (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem SepWPp.of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl h

private theorem subroutine_ok_withLsCl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCl lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCl] at hpre
  rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre'⟩ := hpre
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, hout, _⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre' hsp hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
  · exact Or.inr hrest

def encodeVarintNoGrowPlacedSpec (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat ∧ x.cap.toNat < 2 ^ 61⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeVarintStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗
      A.pool ∗ stackAt s0.sp encodeVarintStack
  onPanic := (encodeVarintSpec A).onPanic

theorem encodeVarintNoGrow_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [encodeVarintNoGrowPlacedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hle, hcap⟩, hpre⟩
  have hpre_ev : s0.mem ⊨ (withLsCodeLoaded lsmpl (encodeVarintSpec A)).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded, encodeVarintSpec]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inr (by omega)⟩, hpre⟩
  refine (CryptoVerification.LibsignalTripleRatchet.Prost.encode_varint_placed_ok
    hshim halloc hrealloc hpanic).mono_outcome x R s0 hpc hrun hpre_ev hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodeVarintSpec] at hpost
    dsimp only [withLsCodeLoaded, encodeVarintNoGrowPlacedSpec]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨cap', ptr', hpost⟩
    have hpull :
        ((⌜sf.trace = s0.trace⌝ ∗
          (⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
            vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
          A.pool ∗ stackAt s0.sp encodeVarintStack) ∗ R) =
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ((⌜sf.trace = s0.trace⌝ ∗
            vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val) ∗
            A.pool ∗ stackAt s0.sp encodeVarintStack) ∗ R) := by ac_rfl
    rw [hpull, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨_, hno⟩, hpost⟩
    obtain ⟨rfl, rfl⟩ := hno hle
    exact hpost
  · exact Or.inr hrest

theorem step_call_encVarint_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (s_base s_init : State)
    (hle : bs.length + (encodeVarint val).length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 61)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_10).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = s_base.trace) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx0 : s0.readReg64 .x0 = val) (hx1 : s0.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = s_base.trace → LibsignalCodeLoaded lsmpl sf.mem → PreKeyMsgTagRegs s_init sf →
      SepWPp (lsProg_41 H) ret sf
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
          vecU8Buf A cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s0 P Q (EncodePanicPost s_base) := by
  subst hsp
  have henc := ls_subroutine_ok_cl_of_block (callerProg := lsProg_41 H)
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc hpanic)
  refine SepWPp.call (x := ⟨val, v, cap, ptr, bs⟩)
    (F := memRegion (s0.sp - 7824#64) 3568 ∗ F)
    henc hpc hrun halign hlr ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by
      simpa only [withLsCl, encodeVarintNoGrowPlacedSpec, encodeVarintSpec, htr, allocFailedIn]
        using allowPanic_frame id hm) ?_
  · intro R' hm
    dsimp only [withLsCl, encodeVarintNoGrowPlacedSpec]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hle, hcap⟩, ?_⟩
    have heq0 : P ∗ R' = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt s0.sp encodeVarintStack) ∗
        ((memRegion (s0.sp - 7824#64) 3568 ∗ F) ∗ R') := by
      rw [hP, stackAt_preKeyMsgSubStack_eq_encodeVarint s0.sp, vecU8At_eq_header_sep_buf, vecHeader]
      ac_rfl
    exact heq0 ▸ hm
  intro sf hpcf hrunf hspf hcsf
  dsimp only [withLsCl, encodeVarintNoGrowPlacedSpec]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hclf => ?_
  refine SepWPp.pure_elim fun htrf => ?_
  have heq1 :
      vecU8At A v cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt s0.sp encodeVarintStack ∗
        memRegion (s0.sp - 7824#64) 3568 ∗ F =
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
        vecU8Buf A cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt s0.sp preKeyMsgSubStack) ∗ F) := by
    rw [stackAt_preKeyMsgSubStack_eq_encodeVarint s0.sp, vecU8At_eq_header_sep_buf, vecHeader]
    ac_rfl
  rw [heq1]
  exact hnext sf hpcf hrunf hspf (htrf.trans htr) hclf (by reg_chain)

theorem step_call_memcpy_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (dst src sp ret_pc v23 v26 : BitVec 64) (payload : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsρ "memcpy") (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx23 : s0.readReg64 .x23 = v23) (hx26 : s0.readReg64 .x26 = v26)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = payload.length)
    (hP : P = (memRegion dst payload.length ∗ (src ↦ₛ payload)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = tr → LibsignalCodeLoaded lsmpl sf.mem → PreKeyMsgTagRegs s_init sf →
      sf.readReg64 .x23 = v23 → sf.readReg64 .x26 = v26 →
      SepWPp (lsProg_41 H) ret sf (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) Q Qp) :
    SepWPp (lsProg_41 H) ret s0 P Q Qp := by
  subst hsp
  have hmc := ls_hook_ok_of_mem (prog := lsProg_41 H) (sym := "memcpy") hmemcpy
  intro R hm hL
  have hpre : s0.mem ⊨ framelessMemcpySpec.pre (dst, src, payload) s0 ∗ (F ∗ R) := by
    dsimp only [framelessMemcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    rw [hP, sepConj_assoc] at hm; exact hm
  obtain ⟨sf, hsteps, hout, _⟩ :=
    hmc.no_fault_before_outcome (dst, src, payload) (F ∗ R) s0 hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcf, _, hrunf⟩, ⟨hspf, hcsf⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [framelessMemcpySpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨_, htrf⟩, hpost⟩
    rw [hlr] at hpcf
    have hpost' : sf.mem ⊨ (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) ∗ R := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sf', hsteps', hout'⟩ :=
      hnext sf hpcf hrunf hspf (htrf.trans htr) (hcl.of_keepsFrozen hsteps.keepsFrozen)
        (by reg_chain) (by reg_chain) (by reg_chain) R hpost' (hsteps.codeLoaded hL)
    exact ⟨sf', hsteps.trans hsteps', hout'⟩
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem step_preKeyMsg_tag1_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 604#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix0 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 672#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length → PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _, hpk_val, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  subst hP
  cases hpk : x.preKeyId with
  | none =>
    simp only [hpk, Option.isSome, Bool.false_eq_true, ↓reduceIte] at hx20
    have hw20 : s.readReg32 .x20 = 0#32 := by simpa [State.readReg32] using hx20
    have hser1 : serPrefix1 x = serPrefix0 x := by simp [serPrefix1, hpk, LibsignalSessionApi.Prost.uint32Field]
    have h1_len_bv : BitVec.ofNat 64 (serPrefix1 x).length = 1#64 := by simp [hser1, h0_len]
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_41).base + 672#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1; rw [← hser1]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by rw [h1_len_bv]; simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
  | some pid =>
    simp only [hpk, Option.isSome, ↓reduceIte] at hx20
    rw [hpk_val pid hpk] at hx25
    have hw20 : s.readReg32 .x20 = 1#32 := by simpa [State.readReg32] using hx20
    have hw25 : s.readReg32 .x25 = pid := by simpa [State.readReg32] using hx25
    have hser1 : (serPrefix0 x ++ [0x08#8]) ++ encodeVarint (pid.zeroExtend 64) = serPrefix1 x := by
      simp [serPrefix1, hpk, prost_uint32Field_some, prost_key_1_0, List.append_assoc]
    have h1_len : (serPrefix1 x).length = 2 + (encodeVarint (pid.zeroExtend 64)).length := by
      rw [← hser1, List.length_append, List.length_append, h0_len, List.length_singleton]
    have hvar_pos : 1 ≤ (encodeVarint (pid.zeroExtend 64)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hlt0 : (serPrefix0 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq0 := cap_beq_len_false hlt0
    have h0_len_bv : BitVec.ofNat 64 (serPrefix0 x).length = 1#64 := by simp [h0_len]
    rw [h0_len_bv] at hbeq0
    have hle_var : (serPrefix0 x ++ [0x08#8]).length + (encodeVarint (pid.zeroExtend 64)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, h0_len, List.length_singleton]; omega
    rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) hlt0, h0_len_bv]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
    intro hcl0
    have hsnoc := vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) 8#8 hlt0
    rw [h0_len_bv] at hsnoc; rw [hsnoc]
    refine step_call_encVarint_placed hshim halloc hrealloc hpanic
      (pid.zeroExtend 64) (sp + 224#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((blkPl_41).base + 660#64) (serPrefix0 x ++ [8#8]) s_base s hle_var (by omega)
      (F := F) hcl0
      (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp [h0_len])
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
    have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
    rw [hser1]
    apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 672#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag2_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 672#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length)
    (hx24 : s.readReg64 .x24 = 33#64) (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
      boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 768#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
          boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hbk_len : x.baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbk_bv : BitVec.ofNat 64 x.baseKey.serialize.length = 33#64 := by simp [hbk_len]
  have hser2 : (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) ++ x.baseKey.serialize = serPrefix2 x := by
    rw [serPrefix2, prost_bytesField_some 2 x.baseKey.serialize (by omega), prost_key_2_2, hbk_bv]
    simp only [← List.append_assoc, List.singleton_append]
  have hvar33_len : (encodeVarint 33#64).length = 1 := by rw [encodeVarint_33]; rfl
  have h2_len : (serPrefix2 x).length = (serPrefix1 x).length + 1 + 1 + 33 := by
    rw [← hser2, List.length_append, List.length_append, List.length_cons, hvar33_len, hbk_len]
  have hlt1 : (serPrefix1 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq1 := cap_beq_len_false hlt1
  have hle_var : (serPrefix1 x ++ [0x12#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton, hvar33_len]; omega
  have hle_slice : (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length +
      x.baseKey.serialize.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons, hvar33_len, hbk_len]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) hlt1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) 18#8 hlt1,
    bv_len_add_one (serPrefix1 x) 18#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    33#64 (sp + 224#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 716#64) (serPrefix1 x ++ [18#8]) s_base s hle_var (by omega)
    (F := boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx24_1 : sf1.readReg64 .x24 = 33#64 := by reg_chain
  have hx28_1 : sf1.readReg64 .x28 = g.bkSerPtr := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  rw [hbk_bv] at hult1 hule1
  have hbk_ne : x.baseKey.serialize ≠ [] := by intro h; simp [h] at hbk_len
  rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length hle_slice hcap_pos,
    boxU8Buf_nonempty_eq A g.bkSerPtr x.baseKey.serialize hbk_ne]
  apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ "memcpy"); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hclf1'
  refine step_call_memcpy_placed hmemcpy
    (g.serPtr + BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length)
    g.bkSerPtr sp ((blkPl_41).base + 760#64)
    (BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length)
    (BitVec.ofNat 64 x.model.serialized.length)
    x.baseKey.serialize s_base.trace s
    (F := ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
      vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack ∗
      (⌜g.bkSerPtr ≠ 0#64 ∧ x.baseKey.serialize.length < 2 ^ 63⌝ ∗ A.live g.bkSerPtr x.baseKey.serialize.length 1) ∗ F)
    hclf1' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf2 hpcf2 hrunf2 hspf2 htrf2 hclf2 hregs2 hx23_2 hx26_2 => ?_
  have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx24_2 : sf2.readReg64 .x24 = 33#64 := by reg_chain
  simp only [arm64_norm] at hx23_2 hx24_2
  have hadd_len : BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length + 33#64 =
      BitVec.ofNat 64 (serPrefix2 x).length := by
    simp only [h2_len, List.length_append, List.length_cons, hvar33_len, BitVec.ofNat_add]; ac_rfl
  clear h2_len
  have hpost_eq :
      (((g.serPtr + BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ↦ₛ x.baseKey.serialize) ∗
        (g.bkSerPtr ↦ₛ x.baseKey.serialize)) ∗
      (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
        vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack ∗
        (⌜g.bkSerPtr ≠ 0#64 ∧ x.baseKey.serialize.length < 2 ^ 63⌝ ∗
          A.live g.bkSerPtr x.baseKey.serialize.length 1) ∗ F) =
      ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
    rw [← hser2,
      ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize hcap_pos,
      boxU8Buf_nonempty_eq A g.bkSerPtr x.baseKey.serialize hbk_ne]; ac_rfl
  rw [hpost_eq]
  apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 768#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl3
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl3
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag3_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 768#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
      boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 860#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
          boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hik_len : x.ik.serialize.length = 33 := by simp [IdentityKey.serialize, PublicKey.serialize]
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hik_bv : BitVec.ofNat 64 x.ik.serialize.length = 33#64 := by simp [hik_len]
  have hser3 : (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) ++ x.ik.serialize = serPrefix3 x := by
    rw [serPrefix3, prost_bytesField_some 3 x.ik.serialize (by omega), prost_key_3_2, hik_bv]
    simp only [← List.append_assoc, List.singleton_append]
  have hvar33_len : (encodeVarint 33#64).length = 1 := by rw [encodeVarint_33]; rfl
  have h3_len : (serPrefix3 x).length = (serPrefix2 x).length + 1 + 1 + 33 := by
    rw [← hser3, List.length_append, List.length_append, List.length_cons, hvar33_len, hik_len]
  have hlt2 : (serPrefix2 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq2 := cap_beq_len_false hlt2
  have hle_var : (serPrefix2 x ++ [26#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton, hvar33_len]; omega
  have hle_slice : (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length +
      x.ik.serialize.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons, hvar33_len, hik_len]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) hlt2]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) 26#8 hlt2,
    bv_len_add_one (serPrefix2 x) 26#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    33#64 (sp + 224#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 808#64) (serPrefix2 x ++ [26#8]) s_base s hle_var (by omega)
    (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗ F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx22_1 : sf1.readReg64 .x22 = 33#64 := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  rw [hik_bv] at hult1 hule1
  have hik_ne : x.ik.serialize ≠ [] := by intro h; simp [h] at hik_len
  rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length hle_slice hcap_pos,
    boxU8Buf_nonempty_eq A g.ikSerPtr x.ik.serialize hik_ne]
  apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ "memcpy"); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hclf1'
  refine step_call_memcpy_placed hmemcpy
    (g.serPtr + BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length)
    g.ikSerPtr sp ((blkPl_41).base + 852#64)
    (BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length)
    (BitVec.ofNat 64 x.model.serialized.length)
    x.ik.serialize s_base.trace s
    (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
      vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack ∗
      (⌜g.ikSerPtr ≠ 0#64 ∧ x.ik.serialize.length < 2 ^ 63⌝ ∗ A.live g.ikSerPtr x.ik.serialize.length 1) ∗ F)
    hclf1' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign1)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf2 hpcf2 hrunf2 hspf2 htrf2 hclf2 hregs2 hx23_2 hx26_2 => ?_
  have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx22_2 : sf2.readReg64 .x22 = 33#64 := by reg_chain
  simp only [arm64_norm] at hx23_2 hx22_2
  have hadd_len : BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length + 33#64 =
      BitVec.ofNat 64 (serPrefix3 x).length := by
    simp only [h3_len, List.length_append, List.length_cons, hvar33_len, BitVec.ofNat_add]; ac_rfl
  clear h3_len
  have hpost_eq :
      (((g.serPtr + BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ↦ₛ x.ik.serialize) ∗
        (g.ikSerPtr ↦ₛ x.ik.serialize)) ∗
      (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
        vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack ∗
        (⌜g.ikSerPtr ≠ 0#64 ∧ x.ik.serialize.length < 2 ^ 63⌝ ∗
          A.live g.ikSerPtr x.ik.serialize.length 1) ∗ F) =
      ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
        boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
    rw [← hser3,
      ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize hcap_pos,
      boxU8Buf_nonempty_eq A g.ikSerPtr x.ik.serialize hik_ne]; ac_rfl
  rw [hpost_eq]
  apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 860#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl3
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl3
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

end Placed

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
