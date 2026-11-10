/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGetLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPop
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `KeyHistory::add` Proofs for `<spqr::chain::Chain>::recv_key`

Proves the three `KeyHistory::add` sub-phases (`+496`, `+520`, `+408` to `+448`) and their
relocatable `[LibsignalPlacement]` counterparts for `<spqr::chain::Chain>::recv_key` (Block `366`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc
open AgreeStateSimp NextKeyInternalFacts ChainNewFacts ChainAddEpochFacts ChainSendKeyFacts
open CryptoVerification.CodeLayout
open RecvKeyDecodes

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  nextKeyInternal_fnOff chainRecvKey_fnOff doReserve7_fnOff
  shim_fnOff alloc_fnOff dealloc_fnOff handleError_fnOff
  panicAddOverflow_fnOff panicSubOverflow_fnOff
  corePanic_fnOff assertFailedUsize_fnOff expectFailed_fnOff sliceIndexFail_fnOff
  libsignalSessionCode_fnOff_0x5a99c libsignalSessionCode_fnOff_0x4dca8 libsignalSessionCode_fnOff_0x5b4d8
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow") (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow") (ls_hook% "core::panicking::panic_const::panic_const_sub_overflow")
  (ls_stub% "core::panicking::assert_failed::<usize, usize>") (ls_hook% "core::panicking::assert_failed::<usize, usize>")
  (ls_stub% "core::panicking::panic") (ls_hook% "core::panicking::panic")
  (ls_stub% "core::option::expect_failed") (ls_hook% "core::option::expect_failed")
  (ls_stub% "core::slice::index::slice_index_fail") (ls_hook% "core::slice::index::slice_index_fail")

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AgreeStateSimp.sp_setPC_pre AgreeStateSimp.sp_setMem_setPC_pre
  AgreeStateSimp.readReg64_setPC_pre AgreeStateSimp.readReg64_setMem_setPC_pre
  AgreeStateSimp.readReg32_setPC_pre AgreeStateSimp.readReg32_setMem_setPC_pre

/-! ## Stack, `do_reserve_and_handle [local#7]`, and Arithmetic Helpers -/

theorem stackAt_nextKeyInternalX_doReserve_split (sp : BitVec 64) :
    stackAt sp nextKeyInternalStackX =
      memRegion (sp - BitVec.ofNat 64 nextKeyInternalStackX) 12352 ∗
        stackAt sp doReserveStack := by
  change memRegion (sp - BitVec.ofNat 64 16560) 16560 =
    memRegion (sp - BitVec.ofNat 64 16560) 12352 ∗
      memRegion (sp - BitVec.ofNat 64 4208) 4208
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16560) (n := 12352) (k := 4208)
    (b' := sp - BitVec.ofNat 64 4208) rfl (by bv_omega) (by decide)

theorem reserveCap_props {cap len additional : Nat}
    (hlen : len + 64 < 2 ^ 62) (hadd : additional ≤ 32) (hneed : ¬ (len + additional ≤ cap)) :
    let newCap := reserveCap cap len additional
    newCap + 1 ≤ 2 ^ 63 ∧
    len + additional ≤ (BitVec.ofNat 64 newCap).toNat ∧
    (BitVec.ofNat 64 newCap).toNat < 2 ^ 63 := by
  intro newCap
  have hbound : newCap + 1 ≤ 2 ^ 63 := by dsimp [newCap, reserveCap]; omega
  have htoNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hbound, ?_, ?_⟩
  · rw [htoNat]; dsimp [newCap, reserveCap]; omega
  · rw [htoNat]; omega

theorem call_doReserve_inImage {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {prog : Program} {entry target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry ((doReserveSpec A).inImage img))
    (arg : DoReserveCall) (ret_pc : BitVec 64) (x : ChainRecvKeyGhost) (s0 s : State)
    {P F R : SepProp} {post : State → SepProp → Prop}
    (hF : ImgCallInv img s) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = arg.v)
    (hx1 : (s.readReg64 .x1).toNat = arg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = arg.additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap arg.cap.toNat arg.bs.length arg.additional + 1 ≤ 2 ^ 63)
    (hpre : P ⊢ vecU8At A arg.v arg.cap arg.ptr arg.bs ∗ A.pool ∗ stackAt s.sp doReserveStack ∗ F)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → ImgCallInv img sf → sf.trace = s0.trace →
      SepWPp prog target_pc sf
        (vecU8At A arg.v (BitVec.ofNat 64 (reserveCap arg.cap.toNat arg.bs.length arg.additional)) p' arg.bs ∗
          A.pool ∗ stackAt sf.sp doReserveStack ∗ F)
        post (recvKeyPanic hkdf A x s0 R)) :
    SepWPp prog target_pc s P post (recvKeyPanic hkdf A x s0 R) := by
  refine ProofLib.SepWPp.call_wpp_frozen (x := arg) (F := F)
    hcall hF.1 hF.2 hpc hrun hsp_align hlr
    (fun R' hm0 => by
      have hm := Satisfies.mono (sepConj_mono_left hpre) hm0
      dsimp only [Spec.inImage, doReserveSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hF.1, hF.2⟩, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, by simpa only [sepConj_assoc] using hm⟩)
    (fun _ _ _ _ hpost => by
      dsimp only [Spec.inImage, doReserveSpec] at hpost
      exact not_satisfies_false_sepConj hpost)
    (fun sm _ _ hm' => by
      dsimp only [Spec.inImage, doReserveSpec] at hm'
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm'
      rcases hm' with ⟨⟨hoom, hpre⟩, hm'⟩
      have hoom0 : allocFailedIn s0 sm := by unfold allocFailedIn at hoom ⊢; rw [← htr]; exact hoom
      have hpre0 : s0.trace <+: sm.trace := by rw [← htr]; exact hpre
      rw [← sepConj_assoc] at hm'
      exact allowPanic_recvKey_oom ⟨hoom0, hpre0⟩ hm')
    (fun sm hpcm hrunm hspm hcsm hfz hsym => by
      dsimp only [Spec.inImage, doReserveSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htrm => ?_
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun p' => ?_
      rw [← hspm]; simp only [sepConj_assoc]
      exact hnext sm p' hpcm hrunm hspm hcsm ⟨hfz, hsym⟩ (htrm.trans htr))
    (fun _ _ _ hpost => by
      dsimp only [Spec.inImage, doReserveSpec] at hpost
      exact (not_satisfies_false_sepConj hpost).elim)

/-- Pack an unpacked `vecU8At` back into `vecU8At A a cap ptr bs`. -/
theorem vecU8At_pack_raw (A : RustAlloc) (a cap ptr : BitVec 64) (bs : Bytes)
    (hle : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs.length ⊢
      vecU8At A a cap ptr bs :=
  vecU8At_pack_prev A a cap ptr bs hle hcap hptr

/-- Fold `vecU8Rest` after `Vec::clear` (`str xzr, [a + 16]`). -/
theorem vecU8Rest_clear_entails (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes)
    (hle : bs.length ≤ cap.toNat) :
    (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs.length ⊢
      (ptr ↦ₛ ([] : Bytes)) ∗ vecU8Rest A cap ptr 0 := by
  unfold vecU8Rest
  by_cases h0 : cap = 0#64
  · subst h0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs
    simp only [↓reduceIte, List.length_nil]
    exact Entails.refl _
  · simp only [h0, ↓reduceIte, pointsToBytes_nil, emp_sepConj, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero]
    rw [show (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
        A.live ptr cap.toNat 1 ∗ ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl]
    refine sepConj_mono_right ?_
    rw [ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
      (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) (by bv_omega) (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion _ _)

theorem add_check4_props {len : Nat} {cap : BitVec 64}
    (hle : len ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    (BitVec.ofNat 64 len).toNat = len ∧
    (cap - BitVec.ofNat 64 len).ule 3#64 = !decide (len + 4 ≤ cap.toNat) ∧
    (3#64).ult (cap - BitVec.ofNat 64 len) = decide (len + 4 ≤ cap.toNat) := by
  have hlen_toNat : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub_toNat : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_toNat]
    · rw [BitVec.le_def, hlen_toNat]; exact hle
  refine ⟨hlen_toNat, ?_, ?_⟩
  · rw [BitVec.ule_eq_decide, hsub_toNat]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    by_cases h : len + 4 ≤ cap.toNat
    · rw [decide_eq_true h, decide_eq_false (by omega : ¬ (cap.toNat - len ≤ 3))]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega : cap.toNat - len ≤ 3)]; rfl
  · rw [BitVec.ult_eq_decide, hsub_toNat]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    by_cases h : len + 4 ≤ cap.toNat
    · rw [decide_eq_true h, decide_eq_true (by omega : 3 < cap.toNat - len)]
    · rw [decide_eq_false h, decide_eq_false (by omega : ¬ (3 < cap.toNat - len))]

theorem add_check32_props {len : Nat} {cap1 : BitVec 64}
    (hle4 : len + 4 ≤ cap1.toNat) (hcap1 : cap1.toNat < 2 ^ 63) :
    BitVec.ofNat 64 len + 4#64 = BitVec.ofNat 64 (len + 4) ∧
    (BitVec.ofNat 64 (len + 4)).toNat = len + 4 ∧
    (31#64).ult (cap1 - BitVec.ofNat 64 (len + 4)) = decide (len + 36 ≤ cap1.toNat) ∧
    (cap1 - BitVec.ofNat 64 (len + 4)).ule 31#64 = !decide (len + 36 ≤ cap1.toNat) := by
  have hadd4 : BitVec.ofNat 64 len + 4#64 = BitVec.ofNat 64 (len + 4) := by bv_omega
  have hlen4_toNat : (BitVec.ofNat 64 (len + 4)).toNat = len + 4 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub_toNat : (cap1 - BitVec.ofNat 64 (len + 4)).toNat = cap1.toNat - (len + 4) := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen4_toNat]
    · rw [BitVec.le_def, hlen4_toNat]; exact hle4
  refine ⟨hadd4, hlen4_toNat, ?_, ?_⟩
  · rw [BitVec.ult_eq_decide, hsub_toNat]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    by_cases h : len + 36 ≤ cap1.toNat
    · rw [decide_eq_true h, decide_eq_true (by omega : 31 < cap1.toNat - (len + 4))]
    · rw [decide_eq_false h, decide_eq_false (by omega : ¬ (31 < cap1.toNat - (len + 4)))]
  · rw [BitVec.ule_eq_decide, hsub_toNat]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    by_cases h : len + 36 ≤ cap1.toNat
    · rw [decide_eq_true h, decide_eq_false (by omega : ¬ (cap1.toNat - (len + 4) ≤ 31))]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega : cap1.toNat - (len + 4) ≤ 31)]; rfl

theorem advance_hdr_props {ctr atIdx : BitVec 32} (hlt : ctr.toNat < atIdx.toNat) :
    ctr ≠ 0xffffffff#32 ∧
    BitVec.uaddOverflow ctr 1#32 = false ∧
    (ctr + 1#32 == 0#32) = false ∧
    (ctr + 1#32 != 0#32) = true ∧
    (ctr + 1#32).toNat = ctr.toNat + 1 ∧
    atIdx.ule (ctr + 1#32) = !decide (ctr.toNat + 1 < atIdx.toNat) ∧
    (ctr + 1#32).ult atIdx = decide (ctr.toNat + 1 < atIdx.toNat) := by
  have hat := atIdx.isLt
  have hctr_ne : ctr ≠ 0xffffffff#32 := by
    intro h; subst h; change 4294967295 < atIdx.toNat at hlt; omega
  have htoNat1 : (ctr + 1#32).toNat = ctr.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : (ctr + 1#32 == 0#32) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have := congrArg BitVec.toNat h
    simp only [htoNat1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at this
    omega
  refine ⟨hctr_ne, ?_, hne0, by simp [bne, hne0], htoNat1, ?_, ?_⟩
  · simp only [BitVec.uaddOverflow, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact decide_eq_false (by omega)
  · rw [BitVec.ule_eq_decide, htoNat1]
    by_cases h : ctr.toNat + 1 < atIdx.toNat
    · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl
  · rw [BitVec.ult_eq_decide, htoNat1]

theorem advance_ooo_props (ctr1 atIdx : BitVec 32) (params : ChainParamsPB) :
    let maxOoo := params.maxOooKeysOrDefault
    BitVec.uaddOverflow ctr1 maxOoo = decide (ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32) ∧
    BitVec.ult (ctr1 + maxOoo) ctr1 = decide (ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32) ∧
    BitVec.ult (ctr1 + maxOoo) maxOoo = decide (ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32) ∧
    BitVec.ult (ctr1 + maxOoo) atIdx = !decide (ctr1 + maxOoo ≥ atIdx) ∧
    BitVec.ule atIdx (ctr1 + maxOoo) = decide (ctr1 + maxOoo ≥ atIdx) := by
  intro maxOoo
  have hc := ctr1.isLt
  have hm := maxOoo.isLt
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · by_cases h : ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32
    · rw [decide_eq_true h]
      simp only [BitVec.ult, BitVec.toNat_add, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega : ctr1.toNat + maxOoo.toNat - 2 ^ 32 < 2 ^ 32)]
      exact decide_eq_true (by omega)
    · rw [decide_eq_false h]
      simp only [BitVec.ult, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact decide_eq_false (by omega)
  · by_cases h : ctr1.toNat + maxOoo.toNat ≥ 2 ^ 32
    · rw [decide_eq_true h]
      simp only [BitVec.ult, BitVec.toNat_add, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega : ctr1.toNat + maxOoo.toNat - 2 ^ 32 < 2 ^ 32)]
      exact decide_eq_true (by omega)
    · rw [decide_eq_false h]
      simp only [BitVec.ult, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact decide_eq_false (by omega)
  · rw [BitVec.ult_eq_decide]
    by_cases h : ctr1 + maxOoo ≥ atIdx
    · have h' := BitVec.le_def.mp h
      rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
    · have h' : ¬ (atIdx.toNat ≤ (ctr1 + maxOoo).toNat) := fun hle => h (BitVec.le_def.mpr hle)
      rw [decide_eq_false h, decide_eq_true (by omega)]; rfl
  · rw [BitVec.ule_eq_decide]
    by_cases h : ctr1 + maxOoo ≥ atIdx
    · rw [decide_eq_true h, decide_eq_true (BitVec.le_def.mp h)]
    · rw [decide_eq_false h, decide_eq_false (fun hle => h (BitVec.le_def.mpr hle))]

/-! ## `KeyHistory::add` Sub-Phases (`+408..+448`, `+520..+448`, `+496..+448`) -/

set_option maxHeartbeats 800000 in
/-- Phase 3 of `KeyHistory::add` at `+408` (`0x60a68..0x60a8c`):
copies the 32-byte `key` from `[sp + 12 .. sp + 44)` into `ptr1 + (prev.data.length + 4)`,
stores `prev.data.length + 36` into `[epPtr + 0x60]`, loads `w8 = ctr1` from `[epPtr + 0x68]`,
checks `cmn w8, #0x1` (`false` since `ctr1.toNat < x.index.toNat`), and reaches `+448` (`0x60a90`). -/
theorem recvKey_write_key_from_408 {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (cap1 ptr1 : BitVec 64)
    (prev : KeyHistory) (next1 key : Bytes) (ctr1 : BitVec 32)
    (hgt1 : ctr1.toNat < x.index.toNat)
    (hkey_len : key.length = 32)
    (hadd36 : prev.data.length + 36 ≤ cap1.toNat)
    (hcap1 : cap1.toNat < 2 ^ 63) (hptr1 : ptr1 ≠ 0)
    (h_cont : ∀ (s' : State),
      RecvKeyStateInv img s0 s' →
      s'.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 448#64 →
      (s'.readReg64 (.gpr 8#5)).setWidth 32 = ctr1 →
      s'.readReg64 (.gpr 19#5) = x.out →
      (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
      s'.readReg64 (.gpr 21#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
      s'.readReg64 (.gpr 22#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
      (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
      s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
      let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
      let prev' := prev.add (ctr1, key) x.self.params
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (s0.readReg64 (.gpr 30#5)) s'
        (memRegion x.out 32 ∗
          chainOuterRecvAt A x epochIndex hi_ep gce ∗
          ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
          ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
          ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
          (gce.recv.next.ptr ↦ₛ next1) ∗
          vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
          ((epPtr + 0x50#64) ↦₆₄ cap1) ∗
          ((epPtr + 0x58#64) ↦₆₄ ptr1) ∗
          ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev'.data.length) ∗
          (ptr1 ↦ₛ prev'.data) ∗
          vecU8Rest A cap1 ptr1 prev'.data.length ∗
          ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
          memRegion (epPtr + 0x6c#64) 4 ∗
          stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
          memRegion (s0.sp - 120#64) 36 ∗
          recvKeyFrameRestAt s0 c3 ∗
          A.pool ∗
          memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
        (recvKeyPostCore extra hkdf A x s0)
        (recvKeyPanic hkdf A x s0 R))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 408#64)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (prev.data.length + 4))
    (hx9 : s.readReg64 (.gpr 9#5) = ptr1)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
        (gce.recv.next.ptr ↦ₛ next1) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
        vecU8At A (epPtr + 0x50#64) cap1 ptr1 (prev.data ++ toBEBytes 4 ctr1) ∗
        ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        ((s0.sp - 120#64) ↦₃₂ ctr1) ∗
        ((s0.sp - 116#64) ↦ₛ key) ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
      (recvKeyPostCore extra hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base (Rust.withPanics ext) hfn 0x5b4d8 1248
  clear hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have ⟨_, hovf1, hbeq0, hbne0, _, _, _⟩ := advance_hdr_props hgt1
  have hlen_be4 : (prev.data ++ toBEBytes 4 ctr1).length = prev.data.length + 4 := by
    rw [List.length_append, NextKeyInternalFacts.toBEBytes_4_length]
  have hadd32 : (prev.data ++ toBEBytes 4 ctr1).length + 32 ≤ cap1.toNat := by omega
  have hadd_bv : BitVec.ofNat 64 (prev.data.length + 4) + 32#64 = BitVec.ofNat 64 (prev.data.length + 36) := by
    bv_omega
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  have hunpack := vecU8At_unpack_for_key32 A (epPtr + 0x50#64) cap1 ptr1 (prev.data ++ toBEBytes 4 ctr1) hadd32
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  rw [ha58, ha60, hlen_be4] at hunpack
  refine SepWPp.fold hunpack (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro u0; apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2; apply SepWPp.exists_elim; intro u3
  obtain ⟨k0, k1, k2, k3, hkey_pack⟩ := exists_cells4_of_length_32 hkey_len
  have hkey_sp : ((s0.sp - 116#64) ↦ₛ key) =
      ((s0.sp - 116#64) ↦₆₄ k0) ∗ ((s0.sp - 108#64) ↦₆₄ k1) ∗
      ((s0.sp - 100#64) ↦₆₄ k2) ∗ ((s0.sp - 92#64) ↦₆₄ k3) := by
    have h := hkey_pack (s0.sp - 116#64)
    rw [show s0.sp - 116#64 + 8#64 = s0.sp - 108#64 by bv_kernel,
        show s0.sp - 116#64 + 16#64 = s0.sp - 100#64 by bv_kernel,
        show s0.sp - 116#64 + 24#64 = s0.sp - 92#64 by bv_kernel] at h
    exact h
  refine SepWPp.fold (Entails.of_eq hkey_sp) (by sep_focus) ?_
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx8; wp_norm_hyp hx9; wp_norm_hyp hx19; wp_norm_hyp hw20
  wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp htrace
  wp_norm_hyp hovf1; wp_norm_hyp hbeq0; wp_norm_hyp hbne0; wp_norm_hyp hadd_bv
  refine SepWPp.of_sepWP_inImage (mid := entry_addr + 448#64) hF ?_
  wp_steps
  refine SepWP.fold (pointsTo32_cells4_entails_memRegion_36_sp120 s0.sp ctr1 k0 k1 k2 k3) (by sep_focus) ?_
  have hpack := vecU8At_pack_append_key32 A (epPtr + 0x50#64) cap1 ptr1
    (prev.data ++ toBEBytes 4 ctr1) key k0 k1 k2 k3 hkey_len hkey_pack hadd32 hcap1 hptr1
  rw [ha58, ha60, hlen_be4, show prev.data.length + 4 + 32 = prev.data.length + 36 by omega] at hpack
  refine SepWP.fold hpack (by sep_focus) ?_
  have hunpack_end := vecU8At_unpack A (epPtr + 0x50#64) cap1 ptr1 ((prev.data ++ toBEBytes 4 ctr1) ++ key)
  rw [ha58, ha60] at hunpack_end
  refine SepWP.fold hunpack_end (by sep_focus) ?_
  refine NextKeyInternalFacts.SepWP.pure_left_focus _ (by sep_focus) fun _ => ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyStateInv img s0 _ :=
    ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
     by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
  refine SepWPp.mono_pre _ ?_
    (h_cont _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
  change _ ⊢
    memRegion x.out 32 ∗
      chainOuterRecvAt A x epochIndex hi_ep gce ∗
      ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
      ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
      ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
      (gce.recv.next.ptr ↦ₛ next1) ∗
      vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
      ((epPtr + 0x50#64) ↦₆₄ cap1) ∗
      ((epPtr + 0x58#64) ↦₆₄ ptr1) ∗
      ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 ((prev.data ++ toBEBytes 4 ctr1) ++ key).length) ∗
      (ptr1 ↦ₛ ((prev.data ++ toBEBytes 4 ctr1) ++ key)) ∗
      vecU8Rest A cap1 ptr1 ((prev.data ++ toBEBytes 4 ctr1) ++ key).length ∗
      ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
      memRegion (epPtr + 0x6c#64) 4 ∗
      stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
      memRegion (s0.sp - 120#64) 36 ∗
      recvKeyFrameRestAt s0 c3 ∗
      A.pool ∗
      memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra
  sep_frame

set_option maxHeartbeats 800000 in
/-- Phase 2 of `KeyHistory::add` at `+520` (`0x60ad8..0x60b14` -> `+408` -> `+448`):
stores `rev32Trunc ctr1` (`toBEBytes 4 ctr1`) at `ptr1 + prev.data.length`, updates `[epPtr + 0x60]`
to `prev.data.length + 4`, reserves 32 bytes if `cap1 - (prev.data.length + 4) ≤ 31`, and transitions
to `recvKey_write_key_from_408`. -/
theorem recvKey_add_from_520 {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdoRes : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr doReserve7Name)
      ((doReserveSpec A).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (cap1 ptr1 : BitVec 64)
    (prev : KeyHistory) (next1 key : Bytes) (ctr1 : BitVec 32)
    (hgt1 : ctr1.toNat < x.index.toNat)
    (hkey_len : key.length = 32)
    (hp_fit : prev.data.length + 128 < 2 ^ 62)
    (hadd4 : prev.data.length + 4 ≤ cap1.toNat)
    (hcap1 : cap1.toNat < 2 ^ 63) (hptr1 : ptr1 ≠ 0)
    (h_cont : ∀ (cap2 ptr2 : BitVec 64),
      (prev.add (ctr1, key) x.self.params).data.length ≤ cap2.toNat →
      cap2.toNat < 2 ^ 63 → ptr2 ≠ 0 →
      ∀ (s' : State),
        RecvKeyStateInv img s0 s' →
        s'.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 448#64 →
        (s'.readReg64 (.gpr 8#5)).setWidth 32 = ctr1 →
        s'.readReg64 (.gpr 19#5) = x.out →
        (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s'.readReg64 (.gpr 21#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
        s'.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
        s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let prev' := prev.add (ctr1, key) x.self.params
        SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
          (s0.readReg64 (.gpr 30#5)) s'
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
            ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
            ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
            (gce.recv.next.ptr ↦ₛ next1) ∗
            vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
            ((epPtr + 0x50#64) ↦₆₄ cap2) ∗
            ((epPtr + 0x58#64) ↦₆₄ ptr2) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev'.data.length) ∗
            (ptr2 ↦ₛ prev'.data) ∗
            vecU8Rest A cap2 ptr2 prev'.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool ∗
            memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
          (recvKeyPostCore extra hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 520#64)
    (hx1 : s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 prev.data.length)
    (hx10 : s.readReg64 (.gpr 10#5) = cap1)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64)
    (hw25 : (s.readReg64 (.gpr 25#5)).setWidth 32 = ctr1) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
        (gce.recv.next.ptr ↦ₛ next1) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
        vecU8At A (epPtr + 0x50#64) cap1 ptr1 prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        ((s0.sp - 120#64) ↦₃₂ ctr1) ∗
        ((s0.sp - 116#64) ↦ₛ key) ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
      (recvKeyPostCore extra hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base (Rust.withPanics ext) hfn 0x5b4d8 1248
  have h_doRes := sub_ok_at_rebase_bv (name := chainRecvKeyName) (callee := doReserve7Name)
    (k := 0x4dca8#64 - 0x5b4d8#64) (by rw [chainRecvKey_fnOff, doReserve7_fnOff]; rfl) hdoRes
  have h_w408 := @recvKey_write_key_from_408 extra img hkdf A ext x s0 c3 R epochIndex hi_ep gce
  clear hdoRes hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have ⟨hadd4_bv, hlen4_toNat, hult31, hule31⟩ := add_check32_props hadd4 hcap1
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  have hunpack := vecU8At_unpack_for_u32 A (epPtr + 0x50#64) cap1 ptr1 prev.data hadd4
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  rw [ha58, ha60] at hunpack
  refine SepWPp.fold hunpack (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro w0
  have hpack4 := vecU8At_pack_append_u32_be A (epPtr + 0x50#64) cap1 ptr1 prev.data ctr1 hadd4 hcap1 hptr1
  rw [ha58, ha60] at hpack4
  have hadd_len : (prev.add (ctr1, key) x.self.params).data.length = prev.data.length + 36 := by
    simp only [KeyHistory.add, List.length_append, NextKeyInternalFacts.toBEBytes_4_length, hkey_len]
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx1; wp_norm_hyp hx10; wp_norm_hyp hx19; wp_norm_hyp hw20
  wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp hw25; wp_norm_hyp htrace
  wp_norm_hyp hadd4_bv; wp_norm_hyp hult31; wp_norm_hyp hule31
  by_cases hhi : prev.data.length + 36 ≤ cap1.toNat
  · have hhi_t : decide (prev.data.length + 36 ≤ cap1.toNat) = true := decide_eq_true hhi
    wp_norm_hyp hhi_t
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 408#64) hF ?_
    wp_steps
    refine SepWP.fold hpack4 (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyStateInv img s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
    have hle_out : (prev.add (ctr1, key) x.self.params).data.length ≤ cap1.toNat := by omega
    refine SepWPp.mono_pre _ ?_
      (h_w408 cap1 ptr1 prev next1 key ctr1 hgt1 hkey_len hhi hcap1 hptr1
        (h_cont cap1 ptr1 hle_out hcap1 hptr1) _ hinv'
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have hhi_f : decide (prev.data.length + 36 ≤ cap1.toNat) = false := decide_eq_false hhi
    wp_norm_hyp hhi_f
    have hlen_be4 : (prev.data ++ toBEBytes 4 ctr1).length = prev.data.length + 4 := by
      rw [List.length_append, NextKeyInternalFacts.toBEBytes_4_length]
    have hneed32 : ¬ ((prev.data ++ toBEBytes 4 ctr1).length + 32 ≤ cap1.toNat) := by omega
    have ⟨hres_bound, hnew_ge, hnew_lt⟩ :=
      reserveCap_props (cap := cap1.toNat) (len := (prev.data ++ toBEBytes 4 ctr1).length) (additional := 32)
        (by omega) (by decide) hneed32
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + (0x4dca8#64 - 0x5b4d8#64)) hF ?_
    wp_steps
    refine SepWP.fold hpack4 (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64))) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF1
    let arg32 : DoReserveCall := ⟨epPtr + 0x50#64, cap1, ptr1, prev.data ++ toBEBytes 4 ctr1, 32⟩
    refine call_doReserve_inImage h_doRes arg32 (entry_addr + 576#64) x s0 _ hF1
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [State.spAligned, arm64_norm, hsp] at hsp0_align ⊢; revert hsp0_align; bv_kernel)
      (by wp_norm_goal)
      (by simp only [arm64_norm, htrace])
      (by dsimp [arg32, epPtr]; wp_norm_goal)
      (by dsimp [arg32]; rw [hlen_be4, ← hlen4_toNat]; wp_norm_goal)
      (by dsimp [arg32]; wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) hres_bound
      (by simp only [arm64_norm, hsp]; sep_frame) ?_
    intro sf p' hpc_sf hrun_sf hsp_sf hcs_sf hF_sf htr_sf
    simp only [arm64_norm, hsp] at hsp_sf
    have hsp_sf_align : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    rcases hcs_sf with ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩
    simp only [arm64_norm] at hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hvregs_sf
    let cap2 := BitVec.ofNat 64 (reserveCap cap1.toNat (prev.data ++ toBEBytes 4 ctr1).length 32)
    have hadd36' : prev.data.length + 36 ≤ cap2.toNat := by dsimp [cap2]; omega
    have hcap2 : cap2.toNat < 2 ^ 63 := hnew_lt
    have hunpack2 := vecU8At_unpack A (epPtr + 0x50#64) cap2 p' (prev.data ++ toBEBytes 4 ctr1)
    rw [ha58, ha60] at hunpack2
    refine SepWPp.fold hunpack2 (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, _, hp'_ne⟩
    have hpack2 := vecU8At_pack_raw A (epPtr + 0x50#64) cap2 p' (prev.data ++ toBEBytes 4 ctr1)
      (by omega) hcap2 hp'_ne
    rw [ha58, ha60] at hpack2
    wp_norm_hyp hpc_sf; wp_norm_hyp hrun_sf; wp_norm_hyp hsp_sf_align; wp_norm_hyp hsp_sf
    wp_norm_hyp hx22_sf; wp_norm_hyp hlen_be4
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 408#64) hF_sf ?_
    wp_steps
    refine SepWP.fold hpack2 (by sep_focus) ?_
    have hstack_back :
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 nextKeyInternalStackX) 12352 ∗
          stackAt sf.sp doReserveStack =
          stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
      rw [hsp_sf, ← stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64)]
    refine SepWP.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2
    have hinv2 : RecvKeyStateInv img s0 _ :=
      ⟨hF2, by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26, ← hx26_sf]; wp_norm_goal,
       by rw [← hx27, ← hx27_sf]; wp_norm_goal,
       by rw [← hx28, ← hx28_sf]; wp_norm_goal,
       htr_sf,
       by rw [← hvregs, ← hvregs_sf]; wp_norm_goal⟩
    have hle_out : (prev.add (ctr1, key) x.self.params).data.length ≤ cap2.toNat := by omega
    refine SepWPp.mono_pre _ ?_
      (h_w408 cap2 p' prev next1 key ctr1 hgt1 hkey_len hadd36' hcap2 hp'_ne
        (h_cont cap2 p' hle_out hcap2 hp'_ne) _ hinv2
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by rw [← hx19, ← hx19_sf]; wp_norm_goal)
        (by rw [← hw20, ← hx20_sf]; wp_norm_goal)
        (by rw [← hx21, ← hx21_sf]; wp_norm_goal)
        (by wp_norm_goal)
        (by rw [← hw23, ← hx23_sf]; wp_norm_goal)
        (by rw [← hx24, ← hx24_sf]; wp_norm_goal))
    sep_frame

set_option maxHeartbeats 800000 in
/-- Phase 1 of `KeyHistory::add` at `+496` (`0x60ac0..0x60b34` -> `+520` -> `+408` -> `+448`):
loads `x1 = prev.data.length`, `x10 = prevPin.cap`, `w25 = ctr1`, reserves 4 bytes if
`prevPin.cap - prev.data.length ≤ 3`, and transitions to `recvKey_add_from_520`. -/
theorem recvKey_add_from_496 {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdoRes : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr doReserve7Name)
      ((doReserveSpec A).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin)
    (prev : KeyHistory) (next1 key : Bytes) (ctr1 : BitVec 32)
    (hgt1 : ctr1.toNat < x.index.toNat)
    (hkey_len : key.length = 32)
    (hp_fit : prev.data.length + 128 < 2 ^ 62)
    (hp_le : prev.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0)
    (h_cont : ∀ (cap2 ptr2 : BitVec 64),
      (prev.add (ctr1, key) x.self.params).data.length ≤ cap2.toNat →
      cap2.toNat < 2 ^ 63 → ptr2 ≠ 0 →
      ∀ (s' : State),
        RecvKeyStateInv img s0 s' →
        s'.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 448#64 →
        (s'.readReg64 (.gpr 8#5)).setWidth 32 = ctr1 →
        s'.readReg64 (.gpr 19#5) = x.out →
        (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s'.readReg64 (.gpr 21#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
        s'.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
        s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let prev' := prev.add (ctr1, key) x.self.params
        SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
          (s0.readReg64 (.gpr 30#5)) s'
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
            ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
            ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
            (gce.recv.next.ptr ↦ₛ next1) ∗
            vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
            ((epPtr + 0x50#64) ↦₆₄ cap2) ∗
            ((epPtr + 0x58#64) ↦₆₄ ptr2) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev'.data.length) ∗
            (ptr2 ↦ₛ prev'.data) ∗
            vecU8Rest A cap2 ptr2 prev'.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool ∗
            memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
          (recvKeyPostCore extra hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 496#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
        (gce.recv.next.ptr ↦ₛ next1) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev.data.length) ∗
        (prevPin.ptr ↦ₛ prev.data) ∗
        vecU8Rest A prevPin.cap prevPin.ptr prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        ((s0.sp - 120#64) ↦₃₂ ctr1) ∗
        ((s0.sp - 116#64) ↦ₛ key) ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
      (recvKeyPostCore extra hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base (Rust.withPanics ext) hfn 0x5b4d8 1248
  have h_doRes := sub_ok_at_rebase_bv (name := chainRecvKeyName) (callee := doReserve7Name)
    (k := 0x4dca8#64 - 0x5b4d8#64) (by rw [chainRecvKey_fnOff, doReserve7_fnOff]; rfl) hdoRes
  have h_add520 := @recvKey_add_from_520 extra img hkdf A ext hdoRes x s0 c3 R epochIndex hi_ep gce
  clear hdoRes hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have ⟨hlen_toNat, hule3, hult3⟩ := add_check4_props hp_le hp_cap
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  have hpack0 := vecU8At_pack_raw A (epPtr + 0x50#64) prevPin.cap prevPin.ptr prev.data hp_le hp_cap hp_ptr
  rw [ha58, ha60] at hpack0
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp htrace
  wp_norm_hyp hule3; wp_norm_hyp hult3
  by_cases hadd4 : prev.data.length + 4 ≤ prevPin.cap.toNat
  · have hadd4_t : decide (prev.data.length + 4 ≤ prevPin.cap.toNat) = true := decide_eq_true hadd4
    wp_norm_hyp hadd4_t
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 520#64) hF ?_
    wp_steps
    refine SepWP.fold hpack0 (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyStateInv img s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
    refine SepWPp.mono_pre _ ?_
      (h_add520 prevPin.cap prevPin.ptr prev next1 key ctr1 hgt1 hkey_len hp_fit hadd4 hp_cap hp_ptr h_cont
        _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have hadd4_f : decide (prev.data.length + 4 ≤ prevPin.cap.toNat) = false := decide_eq_false hadd4
    wp_norm_hyp hadd4_f
    have ⟨hres_bound, hnew_ge, hnew_lt⟩ :=
      reserveCap_props (cap := prevPin.cap.toNat) (len := prev.data.length) (additional := 4)
        (by omega) (by decide) hadd4
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + (0x4dca8#64 - 0x5b4d8#64)) hF ?_
    wp_steps
    refine SepWP.fold hpack0 (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64))) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF1
    let arg4 : DoReserveCall := ⟨epPtr + 0x50#64, prevPin.cap, prevPin.ptr, prev.data, 4⟩
    refine call_doReserve_inImage h_doRes arg4 (entry_addr + 604#64) x s0 _ hF1
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [State.spAligned, arm64_norm, hsp] at hsp0_align ⊢; revert hsp0_align; bv_kernel)
      (by wp_norm_goal)
      (by simp only [arm64_norm, htrace])
      (by dsimp [arg4, epPtr]; wp_norm_goal)
      (by dsimp [arg4]; rw [← hlen_toNat]; wp_norm_goal)
      (by dsimp [arg4]; wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) hres_bound
      (by simp only [arm64_norm, hsp]; sep_frame) ?_
    intro sf p' hpc_sf hrun_sf hsp_sf hcs_sf hF_sf htr_sf
    simp only [arm64_norm, hsp] at hsp_sf
    have hsp_sf_align : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    rcases hcs_sf with ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩
    simp only [arm64_norm] at hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hvregs_sf
    let cap1 := BitVec.ofNat 64 (reserveCap prevPin.cap.toNat prev.data.length 4)
    have hadd4' : prev.data.length + 4 ≤ cap1.toNat := hnew_ge
    have hcap1 : cap1.toNat < 2 ^ 63 := hnew_lt
    have hunpack1 := vecU8At_unpack A (epPtr + 0x50#64) cap1 p' prev.data
    rw [ha58, ha60] at hunpack1
    refine SepWPp.fold hunpack1 (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, _, hp'_ne⟩
    have hpack1 := vecU8At_pack_raw A (epPtr + 0x50#64) cap1 p' prev.data
      (by omega) hcap1 hp'_ne
    rw [ha58, ha60] at hpack1
    wp_norm_hyp hpc_sf; wp_norm_hyp hrun_sf; wp_norm_hyp hsp_sf_align; wp_norm_hyp hsp_sf; wp_norm_hyp hx22_sf
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 520#64) hF_sf ?_
    wp_steps
    refine SepWP.fold hpack1 (by sep_focus) ?_
    have hstack_back :
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 nextKeyInternalStackX) 12352 ∗
          stackAt sf.sp doReserveStack =
          stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
      rw [hsp_sf, ← stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64)]
    refine SepWP.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2
    have hinv2 : RecvKeyStateInv img s0 _ :=
      ⟨hF2, by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26, ← hx26_sf]; wp_norm_goal,
       by rw [← hx27, ← hx27_sf]; wp_norm_goal,
       by rw [← hx28, ← hx28_sf]; wp_norm_goal,
       htr_sf,
       by rw [← hvregs, ← hvregs_sf]; wp_norm_goal⟩
    refine SepWPp.mono_pre _ ?_
      (h_add520 cap1 p' prev next1 key ctr1 hgt1 hkey_len hp_fit hadd4' hcap1 hp'_ne h_cont
        _ hinv2 (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by rw [← hx19, ← hx19_sf]; wp_norm_goal)
        (by rw [← hw20, ← hx20_sf]; wp_norm_goal)
        (by rw [← hx21, ← hx21_sf]; wp_norm_goal)
        (by wp_norm_goal)
        (by rw [← hw23, ← hx23_sf]; wp_norm_goal)
        (by rw [← hx24, ← hx24_sf]; wp_norm_goal)
        (by simp only [arm64_norm, hx25_sf]))
    sep_frame

/-! ## Relocatable `[LibsignalPlacement]` `KeyHistory::add` Sub-Phases (`blkPC_366`) -/

theorem call_doReserve_lsCallInv [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {prog : Program} {entry target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCallInv lsmpl (doReserveSpec A)))
    (arg : DoReserveCall) (ret_pc : BitVec 64) (x : ChainRecvKeyGhost) (s0 s : State)
    {P F R : SepProp} {post : State → SepProp → Prop}
    (hF : LsCallInv lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = arg.v)
    (hx1 : (s.readReg64 .x1).toNat = arg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = arg.additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap arg.cap.toNat arg.bs.length arg.additional + 1 ≤ 2 ^ 63)
    (hpre : P ⊢ vecU8At A arg.v arg.cap arg.ptr arg.bs ∗ A.pool ∗ stackAt s.sp doReserveStack ∗ F)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → LsCallInv lsmpl sf.mem → sf.trace = s0.trace →
      SepWPp prog target_pc sf
        (vecU8At A arg.v (BitVec.ofNat 64 (reserveCap arg.cap.toNat arg.bs.length arg.additional)) p' arg.bs ∗
          A.pool ∗ stackAt sf.sp doReserveStack ∗ F)
        post (recvKeyPanic hkdf A x s0 R)) :
    SepWPp prog target_pc s P post (recvKeyPanic hkdf A x s0 R) := by
  refine SepWPp.call_allowPanic_lsCallInv_mid (x := arg) (F := F) (R := R)
    (Qpan := (chainRecvKeySpecX hkdf A).onPanic x s0)
    hcall hF hpc hrun hsp_align hlr
    (fun R' hm0 => by
      have hm := Satisfies.mono (sepConj_mono_left hpre) hm0
      dsimp only [doReserveSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, by simpa only [sepConj_assoc] using hm⟩)
    (fun sf => by
      dsimp only [doReserveSpec, chainRecvKeySpecX]
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hoom, hpre_tr⟩ => ?_
      have hoom0 : allocFailedIn s0 sf := by unfold allocFailedIn at hoom ⊢; rw [← htr]; exact hoom
      have hpre0 : s0.trace <+: sf.trace := by rw [← htr]; exact hpre_tr
      exact Entails.pure_right (Or.inr ⟨hoom0, hpre0⟩) (entails_anyHeap _))
    ⟨fun _ _ => rfl, fun _ => rfl⟩
    (fun sm hpcm hrunm hspm hcsm hF_m => by
      dsimp only [doReserveSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htrm => ?_
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun p' => ?_
      rw [← hspm]; simp only [sepConj_assoc]
      exact hnext sm p' hpcm hrunm hspm hcsm hF_m (htrm.trans htr))

set_option maxHeartbeats 800000 in
theorem recvKey_write_key_from_408_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (cap1 ptr1 : BitVec 64)
    (prev : KeyHistory) (next1 key : Bytes) (ctr1 : BitVec 32)
    (hgt1 : ctr1.toNat < x.index.toNat)
    (hkey_len : key.length = 32)
    (hadd36 : prev.data.length + 36 ≤ cap1.toNat)
    (hcap1 : cap1.toNat < 2 ^ 63) (hptr1 : ptr1 ≠ 0)
    (h_cont : ∀ (s' : State),
      RecvKeyPlacedStateInv lsmpl s0 s' →
      s'.pc = (blkPl_366).base + 448#64 →
      (s'.readReg64 (.gpr 8#5)).setWidth 32 = ctr1 →
      s'.readReg64 (.gpr 19#5) = x.out →
      (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
      s'.readReg64 (.gpr 21#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
      s'.readReg64 (.gpr 22#5) =
        x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
      (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
      s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
      let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
      let prev' := prev.add (ctr1, key) x.self.params
      SepWPp ((blkPC_366).rebase (blkPl_366).base H)
        (s0.readReg64 (.gpr 30#5)) s'
        (memRegion x.out 32 ∗
          chainOuterRecvAt A x epochIndex hi_ep gce ∗
          ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
          ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
          ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
          (gce.recv.next.ptr ↦ₛ next1) ∗
          vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
          ((epPtr + 0x50#64) ↦₆₄ cap1) ∗
          ((epPtr + 0x58#64) ↦₆₄ ptr1) ∗
          ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev'.data.length) ∗
          (ptr1 ↦ₛ prev'.data) ∗
          vecU8Rest A cap1 ptr1 prev'.data.length ∗
          ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
          memRegion (epPtr + 0x6c#64) 4 ∗
          stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
          memRegion (s0.sp - 120#64) 36 ∗
          recvKeyFrameRestAt s0 c3 ∗
          A.pool)
        (recvKeyPost hkdf A x s0)
        (recvKeyPanic hkdf A x s0 R))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 408#64)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (prev.data.length + 4))
    (hx9 : s.readReg64 (.gpr 9#5) = ptr1)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
        (gce.recv.next.ptr ↦ₛ next1) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
        vecU8At A (epPtr + 0x50#64) cap1 ptr1 (prev.data ++ toBEBytes 4 ctr1) ∗
        ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        ((s0.sp - 120#64) ↦₃₂ ctr1) ∗
        ((s0.sp - 116#64) ↦ₛ key) ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have ⟨_, hovf1, hbeq0, hbne0, _, _, _⟩ := advance_hdr_props hgt1
  have hlen_be4 : (prev.data ++ toBEBytes 4 ctr1).length = prev.data.length + 4 := by
    rw [List.length_append, NextKeyInternalFacts.toBEBytes_4_length]
  have hadd32 : (prev.data ++ toBEBytes 4 ctr1).length + 32 ≤ cap1.toNat := by omega
  have hadd_bv : BitVec.ofNat 64 (prev.data.length + 4) + 32#64 = BitVec.ofNat 64 (prev.data.length + 36) := by
    bv_omega
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  have hunpack := vecU8At_unpack_for_key32 A (epPtr + 0x50#64) cap1 ptr1 (prev.data ++ toBEBytes 4 ctr1) hadd32
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  rw [ha58, ha60, hlen_be4] at hunpack
  refine SepWPp.fold hunpack (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro u0; apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2; apply SepWPp.exists_elim; intro u3
  obtain ⟨k0, k1, k2, k3, hkey_pack⟩ := exists_cells4_of_length_32 hkey_len
  have hkey_sp : ((s0.sp - 116#64) ↦ₛ key) =
      ((s0.sp - 116#64) ↦₆₄ k0) ∗ ((s0.sp - 108#64) ↦₆₄ k1) ∗
      ((s0.sp - 100#64) ↦₆₄ k2) ∗ ((s0.sp - 92#64) ↦₆₄ k3) := by
    have h := hkey_pack (s0.sp - 116#64)
    rw [show s0.sp - 116#64 + 8#64 = s0.sp - 108#64 by bv_kernel,
        show s0.sp - 116#64 + 16#64 = s0.sp - 100#64 by bv_kernel,
        show s0.sp - 116#64 + 24#64 = s0.sp - 92#64 by bv_kernel] at h
    exact h
  refine SepWPp.fold (Entails.of_eq hkey_sp) (by sep_focus) ?_
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx8; wp_norm_hyp hx9; wp_norm_hyp hx19; wp_norm_hyp hw20
  wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp htrace
  wp_norm_hyp hovf1; wp_norm_hyp hbeq0; wp_norm_hyp hbne0; wp_norm_hyp hadd_bv
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 448#64) hF ?_
  wp_steps
  refine SepWP.fold (pointsTo32_cells4_entails_memRegion_36_sp120 s0.sp ctr1 k0 k1 k2 k3) (by sep_focus) ?_
  have hpack := vecU8At_pack_append_key32 A (epPtr + 0x50#64) cap1 ptr1
    (prev.data ++ toBEBytes 4 ctr1) key k0 k1 k2 k3 hkey_len hkey_pack hadd32 hcap1 hptr1
  rw [ha58, ha60, hlen_be4, show prev.data.length + 4 + 32 = prev.data.length + 36 by omega] at hpack
  refine SepWP.fold hpack (by sep_focus) ?_
  have hunpack_end := vecU8At_unpack A (epPtr + 0x50#64) cap1 ptr1 ((prev.data ++ toBEBytes 4 ctr1) ++ key)
  rw [ha58, ha60] at hunpack_end
  refine SepWP.fold hunpack_end (by sep_focus) ?_
  refine NextKeyInternalFacts.SepWP.pure_left_focus _ (by sep_focus) fun _ => ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
    ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
     by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
  refine SepWPp.mono_pre _ ?_
    (h_cont _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
  change _ ⊢
    memRegion x.out 32 ∗
      chainOuterRecvAt A x epochIndex hi_ep gce ∗
      ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
      ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
      ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
      (gce.recv.next.ptr ↦ₛ next1) ∗
      vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
      ((epPtr + 0x50#64) ↦₆₄ cap1) ∗
      ((epPtr + 0x58#64) ↦₆₄ ptr1) ∗
      ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 ((prev.data ++ toBEBytes 4 ctr1) ++ key).length) ∗
      (ptr1 ↦ₛ ((prev.data ++ toBEBytes 4 ctr1) ++ key)) ∗
      vecU8Rest A cap1 ptr1 ((prev.data ++ toBEBytes 4 ctr1) ++ key).length ∗
      ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
      memRegion (epPtr + 0x6c#64) 4 ∗
      stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
      memRegion (s0.sp - 120#64) 36 ∗
      recvKeyFrameRestAt s0 c3 ∗
      A.pool
  sep_frame

set_option maxHeartbeats 800000 in
theorem recvKey_add_from_520_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (doReserveSpec A)))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (cap1 ptr1 : BitVec 64)
    (prev : KeyHistory) (next1 key : Bytes) (ctr1 : BitVec 32)
    (hgt1 : ctr1.toNat < x.index.toNat)
    (hkey_len : key.length = 32)
    (hp_fit : prev.data.length + 128 < 2 ^ 62)
    (hadd4 : prev.data.length + 4 ≤ cap1.toNat)
    (hcap1 : cap1.toNat < 2 ^ 63) (hptr1 : ptr1 ≠ 0)
    (h_cont : ∀ (cap2 ptr2 : BitVec 64),
      (prev.add (ctr1, key) x.self.params).data.length ≤ cap2.toNat →
      cap2.toNat < 2 ^ 63 → ptr2 ≠ 0 →
      ∀ (s' : State),
        RecvKeyPlacedStateInv lsmpl s0 s' →
        s'.pc = (blkPl_366).base + 448#64 →
        (s'.readReg64 (.gpr 8#5)).setWidth 32 = ctr1 →
        s'.readReg64 (.gpr 19#5) = x.out →
        (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s'.readReg64 (.gpr 21#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
        s'.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
        s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let prev' := prev.add (ctr1, key) x.self.params
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s'
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
            ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
            ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
            (gce.recv.next.ptr ↦ₛ next1) ∗
            vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
            ((epPtr + 0x50#64) ↦₆₄ cap2) ∗
            ((epPtr + 0x58#64) ↦₆₄ ptr2) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev'.data.length) ∗
            (ptr2 ↦ₛ prev'.data) ∗
            vecU8Rest A cap2 ptr2 prev'.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool)
          (recvKeyPost hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 520#64)
    (hx1 : s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 prev.data.length)
    (hx10 : s.readReg64 (.gpr 10#5) = cap1)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64)
    (hw25 : (s.readReg64 (.gpr 25#5)).setWidth 32 = ctr1) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
        (gce.recv.next.ptr ↦ₛ next1) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
        vecU8At A (epPtr + 0x50#64) cap1 ptr1 prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        ((s0.sp - 120#64) ↦₃₂ ctr1) ∗
        ((s0.sp - 116#64) ↦ₛ key) ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr
  have h_w408 := @recvKey_write_key_from_408_placed _ hkdf A H x s0 c3 R epochIndex hi_ep gce
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have ⟨hadd4_bv, hlen4_toNat, hult31, hule31⟩ := add_check32_props hadd4 hcap1
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  have hunpack := vecU8At_unpack_for_u32 A (epPtr + 0x50#64) cap1 ptr1 prev.data hadd4
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  rw [ha58, ha60] at hunpack
  refine SepWPp.fold hunpack (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro w0
  have hpack4 := vecU8At_pack_append_u32_be A (epPtr + 0x50#64) cap1 ptr1 prev.data ctr1 hadd4 hcap1 hptr1
  rw [ha58, ha60] at hpack4
  have hadd_len : (prev.add (ctr1, key) x.self.params).data.length = prev.data.length + 36 := by
    simp only [KeyHistory.add, List.length_append, NextKeyInternalFacts.toBEBytes_4_length, hkey_len]
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx1; wp_norm_hyp hx10; wp_norm_hyp hx19; wp_norm_hyp hw20
  wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp hw25; wp_norm_hyp htrace
  wp_norm_hyp hadd4_bv; wp_norm_hyp hult31; wp_norm_hyp hule31
  by_cases hhi : prev.data.length + 36 ≤ cap1.toNat
  · have hhi_t : decide (prev.data.length + 36 ≤ cap1.toNat) = true := decide_eq_true hhi
    wp_norm_hyp hhi_t
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 408#64) hF ?_
    wp_steps
    refine SepWP.fold hpack4 (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
    have hle_out : (prev.add (ctr1, key) x.self.params).data.length ≤ cap1.toNat := by omega
    refine SepWPp.mono_pre _ ?_
      (h_w408 cap1 ptr1 prev next1 key ctr1 hgt1 hkey_len hhi hcap1 hptr1
        (h_cont cap1 ptr1 hle_out hcap1 hptr1) _ hinv'
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have hhi_f : decide (prev.data.length + 36 ≤ cap1.toNat) = false := decide_eq_false hhi
    wp_norm_hyp hhi_f
    have hlen_be4 : (prev.data ++ toBEBytes 4 ctr1).length = prev.data.length + 4 := by
      rw [List.length_append, NextKeyInternalFacts.toBEBytes_4_length]
    have hneed32 : ¬ ((prev.data ++ toBEBytes 4 ctr1).length + 32 ≤ cap1.toNat) := by omega
    have ⟨hres_bound, hnew_ge, hnew_lt⟩ :=
      reserveCap_props (cap := cap1.toNat) (len := (prev.data ++ toBEBytes 4 ctr1).length) (additional := 32)
        (by omega) (by decide) hneed32
    refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 320) hF ?_
    wp_steps
    refine SepWP.fold hpack4 (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64))) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF1
    let arg32 : DoReserveCall := ⟨epPtr + 0x50#64, cap1, ptr1, prev.data ++ toBEBytes 4 ctr1, 32⟩
    refine call_doReserve_lsCallInv hdoRes arg32 ((blkPl_366).base + 576#64) x s0 _ hF1
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [State.spAligned, arm64_norm, hsp] at hsp0_align ⊢; revert hsp0_align; bv_kernel)
      (by wp_norm_goal)
      (by simp only [arm64_norm, htrace])
      (by dsimp [arg32, epPtr]; wp_norm_goal)
      (by dsimp [arg32]; rw [hlen_be4, ← hlen4_toNat]; wp_norm_goal)
      (by dsimp [arg32]; wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) hres_bound
      (by simp only [arm64_norm, hsp]; sep_frame) ?_
    intro sf p' hpc_sf hrun_sf hsp_sf hcs_sf hF_sf htr_sf
    simp only [arm64_norm, hsp] at hsp_sf
    have hsp_sf_align : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    rcases hcs_sf with ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩
    simp only [arm64_norm] at hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hvregs_sf
    let cap2 := BitVec.ofNat 64 (reserveCap cap1.toNat (prev.data ++ toBEBytes 4 ctr1).length 32)
    have hadd36' : prev.data.length + 36 ≤ cap2.toNat := by dsimp [cap2]; omega
    have hcap2 : cap2.toNat < 2 ^ 63 := hnew_lt
    have hunpack2 := vecU8At_unpack A (epPtr + 0x50#64) cap2 p' (prev.data ++ toBEBytes 4 ctr1)
    rw [ha58, ha60] at hunpack2
    refine SepWPp.fold hunpack2 (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, _, hp'_ne⟩
    have hpack2 := vecU8At_pack_raw A (epPtr + 0x50#64) cap2 p' (prev.data ++ toBEBytes 4 ctr1)
      (by omega) hcap2 hp'_ne
    rw [ha58, ha60] at hpack2
    wp_norm_hyp hpc_sf; wp_norm_hyp hrun_sf; wp_norm_hyp hsp_sf_align; wp_norm_hyp hsp_sf
    wp_norm_hyp hx22_sf; wp_norm_hyp hlen_be4
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 408#64) hF_sf ?_
    wp_steps
    refine SepWP.fold hpack2 (by sep_focus) ?_
    have hstack_back :
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 nextKeyInternalStackX) 12352 ∗
          stackAt sf.sp doReserveStack =
          stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
      rw [hsp_sf, ← stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64)]
    refine SepWP.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2
    have hinv2 : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF2, by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26, ← hx26_sf]; wp_norm_goal,
       by rw [← hx27, ← hx27_sf]; wp_norm_goal,
       by rw [← hx28, ← hx28_sf]; wp_norm_goal,
       htr_sf,
       by rw [← hvregs, ← hvregs_sf]; wp_norm_goal⟩
    have hle_out : (prev.add (ctr1, key) x.self.params).data.length ≤ cap2.toNat := by omega
    refine SepWPp.mono_pre _ ?_
      (h_w408 cap2 p' prev next1 key ctr1 hgt1 hkey_len hadd36' hcap2 hp'_ne
        (h_cont cap2 p' hle_out hcap2 hp'_ne) _ hinv2
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by rw [← hx19, ← hx19_sf]; wp_norm_goal)
        (by rw [← hw20, ← hx20_sf]; wp_norm_goal)
        (by rw [← hx21, ← hx21_sf]; wp_norm_goal)
        (by wp_norm_goal)
        (by rw [← hw23, ← hx23_sf]; wp_norm_goal)
        (by rw [← hx24, ← hx24_sf]; wp_norm_goal))
    sep_frame

set_option maxHeartbeats 800000 in
theorem recvKey_add_from_496_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (doReserveSpec A)))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevPin : VecPin)
    (prev : KeyHistory) (next1 key : Bytes) (ctr1 : BitVec 32)
    (hgt1 : ctr1.toNat < x.index.toNat)
    (hkey_len : key.length = 32)
    (hp_fit : prev.data.length + 128 < 2 ^ 62)
    (hp_le : prev.data.length ≤ prevPin.cap.toNat)
    (hp_cap : prevPin.cap.toNat < 2 ^ 63) (hp_ptr : prevPin.ptr ≠ 0)
    (h_cont : ∀ (cap2 ptr2 : BitVec 64),
      (prev.add (ctr1, key) x.self.params).data.length ≤ cap2.toNat →
      cap2.toNat < 2 ^ 63 → ptr2 ≠ 0 →
      ∀ (s' : State),
        RecvKeyPlacedStateInv lsmpl s0 s' →
        s'.pc = (blkPl_366).base + 448#64 →
        (s'.readReg64 (.gpr 8#5)).setWidth 32 = ctr1 →
        s'.readReg64 (.gpr 19#5) = x.out →
        (s'.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s'.readReg64 (.gpr 21#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64 →
        s'.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        (s'.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault →
        s'.readReg64 (.gpr 24#5) = s0.sp - 120#64 →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let prev' := prev.add (ctr1, key) x.self.params
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s'
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
            ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
            ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
            (gce.recv.next.ptr ↦ₛ next1) ∗
            vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
            ((epPtr + 0x50#64) ↦₆₄ cap2) ∗
            ((epPtr + 0x58#64) ↦₆₄ ptr2) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev'.data.length) ∗
            (ptr2 ↦ₛ prev'.data) ∗
            vecU8Rest A cap2 ptr2 prev'.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool)
          (recvKeyPost hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 496#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x68#64)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hw23 : (s.readReg64 (.gpr 23#5)).setWidth 32 = x.self.params.maxOooKeysOrDefault)
    (hx24 : s.readReg64 (.gpr 24#5) = s0.sp - 120#64) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 next1.length) ∗
        (gce.recv.next.ptr ↦ₛ next1) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr next1.length ∗
        ((epPtr + 0x50#64) ↦₆₄ prevPin.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ prevPin.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 prev.data.length) ∗
        (prevPin.ptr ↦ₛ prev.data) ∗
        vecU8Rest A prevPin.cap prevPin.ptr prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ ctr1) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        ((s0.sp - 120#64) ↦₃₂ ctr1) ∗
        ((s0.sp - 116#64) ↦ₛ key) ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr
  have h_add520 := @recvKey_add_from_520_placed _ hkdf A H hdoRes x s0 c3 R epochIndex hi_ep gce
  dsimp only [s_idx, epPtr]; clear s_idx epPtr
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  have ⟨hlen_toNat, hule3, hult3⟩ := add_check4_props hp_le hp_cap
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  have hpack0 := vecU8At_pack_raw A (epPtr + 0x50#64) prevPin.cap prevPin.ptr prev.data hp_le hp_cap hp_ptr
  rw [ha58, ha60] at hpack0
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hw23; wp_norm_hyp hx24; wp_norm_hyp htrace
  wp_norm_hyp hule3; wp_norm_hyp hult3
  by_cases hadd4 : prev.data.length + 4 ≤ prevPin.cap.toNat
  · have hadd4_t : decide (prev.data.length + 4 ≤ prevPin.cap.toNat) = true := decide_eq_true hadd4
    wp_norm_hyp hadd4_t
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 520#64) hF ?_
    wp_steps
    refine SepWP.fold hpack0 (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
    refine SepWPp.mono_pre _ ?_
      (h_add520 prevPin.cap prevPin.ptr prev next1 key ctr1 hgt1 hkey_len hp_fit hadd4 hp_cap hp_ptr h_cont
        _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have hadd4_f : decide (prev.data.length + 4 ≤ prevPin.cap.toNat) = false := decide_eq_false hadd4
    wp_norm_hyp hadd4_f
    have ⟨hres_bound, hnew_ge, hnew_lt⟩ :=
      reserveCap_props (cap := prevPin.cap.toNat) (len := prev.data.length) (additional := 4)
        (by omega) (by decide) hadd4
    refine SepWPp.of_sepWP_lsCallInv (mid := lsmpl.base 320) hF ?_
    wp_steps
    refine SepWP.fold hpack0 (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64))) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF1
    let arg4 : DoReserveCall := ⟨epPtr + 0x50#64, prevPin.cap, prevPin.ptr, prev.data, 4⟩
    refine call_doReserve_lsCallInv hdoRes arg4 ((blkPl_366).base + 604#64) x s0 _ hF1
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [State.spAligned, arm64_norm, hsp] at hsp0_align ⊢; revert hsp0_align; bv_kernel)
      (by wp_norm_goal)
      (by simp only [arm64_norm, htrace])
      (by dsimp [arg4, epPtr]; wp_norm_goal)
      (by dsimp [arg4]; rw [← hlen_toNat]; wp_norm_goal)
      (by dsimp [arg4]; wp_norm_goal)
      (by wp_norm_goal) (by wp_norm_goal) hres_bound
      (by simp only [arm64_norm, hsp]; sep_frame) ?_
    intro sf p' hpc_sf hrun_sf hsp_sf hcs_sf hF_sf htr_sf
    simp only [arm64_norm, hsp] at hsp_sf
    have hsp_sf_align : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    rcases hcs_sf with ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx25_sf, hx26_sf, hx27_sf, hx28_sf, _, hvregs_sf⟩
    simp only [arm64_norm] at hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf hx25_sf hx26_sf hx27_sf hx28_sf hvregs_sf
    let cap1 := BitVec.ofNat 64 (reserveCap prevPin.cap.toNat prev.data.length 4)
    have hadd4' : prev.data.length + 4 ≤ cap1.toNat := hnew_ge
    have hcap1 : cap1.toNat < 2 ^ 63 := hnew_lt
    have hunpack1 := vecU8At_unpack A (epPtr + 0x50#64) cap1 p' prev.data
    rw [ha58, ha60] at hunpack1
    refine SepWPp.fold hunpack1 (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, _, hp'_ne⟩
    have hpack1 := vecU8At_pack_raw A (epPtr + 0x50#64) cap1 p' prev.data
      (by omega) hcap1 hp'_ne
    rw [ha58, ha60] at hpack1
    wp_norm_hyp hpc_sf; wp_norm_hyp hrun_sf; wp_norm_hyp hsp_sf_align; wp_norm_hyp hsp_sf; wp_norm_hyp hx22_sf
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 520#64) hF_sf ?_
    wp_steps
    refine SepWP.fold hpack1 (by sep_focus) ?_
    have hstack_back :
        memRegion (s0.sp - 128#64 - BitVec.ofNat 64 nextKeyInternalStackX) 12352 ∗
          stackAt sf.sp doReserveStack =
          stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
      rw [hsp_sf, ← stackAt_nextKeyInternalX_doReserve_split (s0.sp - 128#64)]
    refine SepWP.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF2
    have hinv2 : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF2, by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26, ← hx26_sf]; wp_norm_goal,
       by rw [← hx27, ← hx27_sf]; wp_norm_goal,
       by rw [← hx28, ← hx28_sf]; wp_norm_goal,
       htr_sf,
       by rw [← hvregs, ← hvregs_sf]; wp_norm_goal⟩
    refine SepWPp.mono_pre _ ?_
      (h_add520 cap1 p' prev next1 key ctr1 hgt1 hkey_len hp_fit hadd4' hcap1 hp'_ne h_cont
        _ hinv2 (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by rw [← hx19, ← hx19_sf]; wp_norm_goal)
        (by rw [← hw20, ← hx20_sf]; wp_norm_goal)
        (by rw [← hx21, ← hx21_sf]; wp_norm_goal)
        (by wp_norm_goal)
        (by rw [← hw23, ← hx23_sf]; wp_norm_goal)
        (by rw [← hx24, ← hx24_sf]; wp_norm_goal)
        (by simp only [arm64_norm, hx25_sf]))
    sep_frame

end CryptoVerification.SpqrV1.ChainProofs
