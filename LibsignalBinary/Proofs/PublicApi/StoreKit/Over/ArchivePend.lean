/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveAux
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import ProofLib.SepLogic.WPp

/-!
# Entry Prefix and Pending-Key Clearing of `archive_current_state_inner`

Verifies `<SessionRecord>::archive_current_state_inner` from function entry through clearing and
deallocating `pending_pre_key` (`+0xf8`) and `pending_kyber_pre_key` (`+0x128`), `encoded_len`,
`__rust_alloc` (with OOM panic handling), and `encode_raw`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes libsignalSessionCode_tree archiveBin
  [(ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner") →
   (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner" + 0x19c)]

/-- Function-relative byte offset of `bl __rust_no_alloc_shim_is_unstable_v2` in `archive_current_state_inner`. -/
abbrev archiveShimCutOff : BitVec 64 :=
  code_call_off% libsignalSessionCode archiveCurrentStateInnerName
    "__rustc::__rust_no_alloc_shim_is_unstable_v2"

/-- Function-relative byte offset of `bl encode_raw` in `archive_current_state_inner`. -/
abbrev archiveEncodeRawCutOff : BitVec 64 :=
  code_call_off% libsignalSessionCode archiveCurrentStateInnerName encodeRawName

/-- Panic postcondition of `subroutine_ok_inImage_of_sepWPpIn` on `allocPanic` with frame `R`. -/
abbrev archiveQp (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

/-- Spatial state right after `bl __rust_no_alloc_shim_is_unstable_v2` in `archive_current_state_inner`. -/
def archiveMidShimPre (A : RustAlloc) (s0 : State)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8))
    (c0 c1 c2 c3 v464 : BitVec 64) (v112 : BitVec 128)
    (Fprev : SepProp) : SepProp :=
  stackAt (s0.sp - 464#64) serializeSubStackX ∗
    sessionStateReprAt A (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess) ∗
    ((recPtr + 32#64) ↦ₛ bs336) ∗
    ((recPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    (recPtr ↦₆₄ prevCap) ∗
    ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
    ((recPtr + 16#64) ↦₆₄ 0#64) ∗
    A.pool ∗
    ((s0.sp - 464#64) ↦₆₄ v464) ∗
    ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
    ((s0.sp - 96#64) ↦₆₄ c0) ∗
    ((s0.sp - 88#64) ↦₆₄ c1) ∗
    ((s0.sp - 80#64) ↦₆₄ c2) ∗
    ((s0.sp - 72#64) ↦₆₄ c3) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    Fprev

/-- Spatial state right after `bl encode_raw` in `archive_current_state_inner`. -/
def archiveMidRawPre (A : RustAlloc) (s0 : State)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8))
    (capEnc ptrEnc c0 v464 : BitVec 64) (v112 : BitVec 128)
    (Fprev : SepProp) : SepProp :=
  stackAt (s0.sp - 464#64) serializeSubStackX ∗
    vecU8At A (s0.sp - 88#64) capEnc ptrEnc
      (encSessionMem (clearPendingGhost G) (clearPending sess)) ∗
    sessionStateReprAt A (s0.sp - 456#64) (clearPendingGhost G) (clearPending sess) ∗
    ((recPtr + 32#64) ↦ₛ bs336) ∗
    ((recPtr + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    (recPtr ↦₆₄ prevCap) ∗
    ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
    ((recPtr + 16#64) ↦₆₄ 0#64) ∗
    A.pool ∗
    ((s0.sp - 464#64) ↦₆₄ v464) ∗
    ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
    ((s0.sp - 96#64) ↦₆₄ c0) ∗
    ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗
    ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
    Fprev

/-! ## Signed-Comparison and `tailPinDealloc` Helpers -/

theorem tailPinDealloc_of_slt_true (A : RustAlloc) {cap ptr : BitVec 64}
    (h : cap.slt 1#64 = true) :
    tailPinDealloc A cap ptr = emp := by
  simp [tailPinDealloc, h]

theorem tailPinDealloc_of_slt_false (A : RustAlloc) {cap ptr : BitVec 64}
    (h : cap.slt 1#64 = false) :
    tailPinDealloc A cap ptr =
      (⌜1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  simp [tailPinDealloc, h]

theorem cap_slt_conds_of_true {cap : BitVec 64} (h : cap.slt 1#64 = true) :
    (0#64).slt cap = false ∧ cap.sle 0#64 = true ∧ (1#64).sle cap = false := by
  have hz : (0#64).toInt = 0 := rfl
  have ho : (1#64).toInt = 1 := rfl
  rw [BitVec.slt_iff_toInt_lt, ho] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [Bool.eq_false_iff]; intro hc; rw [BitVec.slt_iff_toInt_lt, hz] at hc; omega
  · rw [BitVec.sle_iff_toInt_le, hz]; omega
  · rw [Bool.eq_false_iff]; intro hc; rw [BitVec.sle_iff_toInt_le, ho] at hc; omega

theorem cap_slt_conds_of_false {cap : BitVec 64} (h : cap.slt 1#64 = false) :
    (0#64).slt cap = true ∧ cap.sle 0#64 = false ∧ (1#64).sle cap = true := by
  have hz : (0#64).toInt = 0 := rfl
  have ho : (1#64).toInt = 1 := rfl
  have hn : ¬ (cap.toInt < 1) := by
    intro hc
    have h' : cap.slt 1#64 = true := BitVec.slt_iff_toInt_lt.mpr (by rw [ho]; exact hc)
    rw [h] at h'; contradiction
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.slt_iff_toInt_lt, hz]; omega
  · rw [Bool.eq_false_iff]; intro hc; rw [BitVec.sle_iff_toInt_le, hz] at hc; omega
  · rw [BitVec.sle_iff_toInt_le, ho]; omega

theorem heap_split_tt (A : RustAlloc) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {pPtr kPtr : BitVec 64}
    (hheap : sessionAtHeap A G sess ⊢
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        tailPinDealloc A (optTailCap G.pending) pPtr ∗
        tailPinDealloc A (optTailCap G.kyber) kPtr)
    (hps : (optTailCap G.pending).slt 1#64 = true)
    (hks : (optTailCap G.kyber).slt 1#64 = true) :
    sessionAtHeap A G sess ⊢ sessionAtHeap A (clearPendingGhost G) (clearPending sess) := by
  refine Entails.trans hheap ?_
  rw [tailPinDealloc_of_slt_true A hps, tailPinDealloc_of_slt_true A hks, emp_sepConj, sepConj_emp]
  exact Entails.refl _

theorem heap_split_tf (A : RustAlloc) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {pPtr kPtr : BitVec 64}
    (hheap : sessionAtHeap A G sess ⊢
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        tailPinDealloc A (optTailCap G.pending) pPtr ∗
        tailPinDealloc A (optTailCap G.kyber) kPtr)
    (hps : (optTailCap G.pending).slt 1#64 = true)
    (hks : (optTailCap G.kyber).slt 1#64 = false) :
    sessionAtHeap A G sess ⊢
      ⌜1 ≤ (optTailCap G.kyber).toNat ∧ (optTailCap G.kyber).toNat < 2 ^ 63⌝ ∗
        (A.live kPtr (optTailCap G.kyber).toNat 1 ∗ memRegion kPtr (optTailCap G.kyber).toNat ∗
          sessionAtHeap A (clearPendingGhost G) (clearPending sess)) := by
  refine Entails.trans hheap ?_
  rw [tailPinDealloc_of_slt_true A hps, tailPinDealloc_of_slt_false A hks, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

theorem heap_split_ft (A : RustAlloc) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {pPtr kPtr : BitVec 64}
    (hheap : sessionAtHeap A G sess ⊢
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        tailPinDealloc A (optTailCap G.pending) pPtr ∗
        tailPinDealloc A (optTailCap G.kyber) kPtr)
    (hps : (optTailCap G.pending).slt 1#64 = false)
    (hks : (optTailCap G.kyber).slt 1#64 = true) :
    sessionAtHeap A G sess ⊢
      ⌜1 ≤ (optTailCap G.pending).toNat ∧ (optTailCap G.pending).toNat < 2 ^ 63⌝ ∗
        (A.live pPtr (optTailCap G.pending).toNat 1 ∗ memRegion pPtr (optTailCap G.pending).toNat ∗
          sessionAtHeap A (clearPendingGhost G) (clearPending sess)) := by
  refine Entails.trans hheap ?_
  rw [tailPinDealloc_of_slt_false A hps, tailPinDealloc_of_slt_true A hks, sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

theorem heap_split_ff (A : RustAlloc) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {pPtr kPtr : BitVec 64}
    (hheap : sessionAtHeap A G sess ⊢
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        tailPinDealloc A (optTailCap G.pending) pPtr ∗
        tailPinDealloc A (optTailCap G.kyber) kPtr)
    (hps : (optTailCap G.pending).slt 1#64 = false)
    (hks : (optTailCap G.kyber).slt 1#64 = false) :
    sessionAtHeap A G sess ⊢
      ⌜(1 ≤ (optTailCap G.pending).toNat ∧ (optTailCap G.pending).toNat < 2 ^ 63) ∧
        (1 ≤ (optTailCap G.kyber).toNat ∧ (optTailCap G.kyber).toNat < 2 ^ 63)⌝ ∗
        (A.live pPtr (optTailCap G.pending).toNat 1 ∗ memRegion pPtr (optTailCap G.pending).toNat ∗
          A.live kPtr (optTailCap G.kyber).toNat 1 ∗ memRegion kPtr (optTailCap G.kyber).toNat ∗
          sessionAtHeap A (clearPendingGhost G) (clearPending sess)) := by
  refine Entails.trans hheap ?_
  rw [tailPinDealloc_of_slt_false A hps, tailPinDealloc_of_slt_false A hks]
  have hpull :
      sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
        (⌜1 ≤ (optTailCap G.pending).toNat ∧ (optTailCap G.pending).toNat < 2 ^ 63⌝ ∗
          A.live pPtr (optTailCap G.pending).toNat 1 ∗ memRegion pPtr (optTailCap G.pending).toNat) ∗
        (⌜1 ≤ (optTailCap G.kyber).toNat ∧ (optTailCap G.kyber).toNat < 2 ^ 63⌝ ∗
          A.live kPtr (optTailCap G.kyber).toNat 1 ∗ memRegion kPtr (optTailCap G.kyber).toNat) =
      ⌜1 ≤ (optTailCap G.pending).toNat ∧ (optTailCap G.pending).toNat < 2 ^ 63⌝ ∗
        ⌜1 ≤ (optTailCap G.kyber).toNat ∧ (optTailCap G.kyber).toNat < 2 ^ 63⌝ ∗
        (A.live pPtr (optTailCap G.pending).toNat 1 ∗ memRegion pPtr (optTailCap G.pending).toNat ∗
          A.live kPtr (optTailCap G.kyber).toNat 1 ∗ memRegion kPtr (optTailCap G.kyber).toNat ∗
          sessionAtHeap A (clearPendingGhost G) (clearPending sess)) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hp
  apply Entails.pure_left; intro hk
  exact Entails.pure_right ⟨hp, hk⟩ (Entails.refl _)

/-! ## Entry to Allocator-Shim Return -/

set_option maxHeartbeats 800000 in
theorem archive_clear_to_shim_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (Fprev R : SepProp)
    (s0 : State)
    (Q : State → SepProp → Prop)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 : BitVec 64) (v112 : BitVec 128)
    (hcont : ∀ (sf : State) (bs336 : List (BitVec 8)),
      bs336.length = 336 →
      sf.pc = (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName + (archiveShimCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 .lr) sf
        (archiveMidShimPre A s0 recPtr prevCap prevPtr G sess bs336 c0 c1 c2 c3 v464 v112 Fprev)
        Q (archiveQp s0 R)) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 .lr) s0
      ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
        sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
        stackAt (s0.sp - 464#64) serializeSubStackX ∗
        ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
        memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ Fprev)
      Q (archiveQp s0 R) := by
  have hfn : libsignalSessionCode.fnOff archiveCurrentStateInnerName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner") :=
    libsignalSessionCode_fnOff_archive
  have hmemcpy := memcpy_arch_okX (img := img) (A := A) (ext := ext) hC
  have hdealloc := dealloc_arch_okX (img := img) (A := A) (ext := ext) hC
  have hshim := shim_arch_okX (img := img) (A := A) (ext := ext) hC
  have hlen := sessionLen_arch_okX A img.base ext
  code_fetches_from CryptoVerification.libsignalSessionCode
    archiveBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    0 0x54
  code_fetches_from CryptoVerification.libsignalSessionCode
    archiveBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    0x84 0xd8
  examples_generalize_entry
  examples_hide_fetches
  apply SepWPpIn.of_sepWP
    (mid := entry +
      bv% (ls_off% "memcpy" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
  refine SepWP.fold (sessionAt_unpack_rec_genX A recPtr G sess) (by sep_focus) ?_
  apply sepWP_exists_left_sepX; intro bs336
  apply sepWP_pure_left_sepX; rintro ⟨hbs336, hcap, hinl⟩
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_lt_not_noneCapX hcap
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rw [← hbs336]
  wppin_callc hmemcpy (memcpySubSpecX.inImage img) (s0.sp - 448#64, recPtr + 32#64, bs336)
  obtain ⟨a, pPtr, pRest, kPtr, kTail, ha, hpRest, hkTail, hbs_eq, hinl', hheap⟩ :=
    bs336_split_gen A hinl
  have hsplit448 : ((s0.sp - 448#64) ↦ₛ bs336) ⊢
      (((s0.sp - 448#64) ↦ₛ a) ∗
        ((s0.sp - 208#64) ↦₆₄ optTailCap G.pending) ∗ ((s0.sp - 200#64) ↦₆₄ pPtr) ∗
        ((s0.sp - 192#64) ↦ₛ pRest) ∗
        ((s0.sp - 160#64) ↦₆₄ optTailCap G.kyber) ∗ ((s0.sp - 152#64) ↦₆₄ kPtr) ∗
        ((s0.sp - 144#64) ↦ₛ kTail)) := by
    rw [hbs_eq, bytes448_split_genX s0.sp a pRest kTail _ _ _ _ ha hpRest]
    exact Entails.refl _
  have hpack_clear := sessionAt_pack_456_clearX A s0.sp G sess ha hpRest hinl'
  have hn_pos : 0 < (encSessionMem (clearPendingGhost G) (clearPending sess)).length :=
    encSessionMem_length_pos _ _
  have hlen_enc' : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 4294967296 :=
    hlen_enc
  have hn_toNat : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat =
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hn_b63 : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).getLsbD 63 = false := by
    rw [BitVec.getLsbD_ofNat]
    simp only [Nat.reduceLT, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (by omega)
  have hn_ne0 : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length == 0#64) = false := by
    apply beq_false_of_ne; intro heq
    have h1 : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat = 0 :=
      congrArg BitVec.toNat heq
    rw [hn_toNat] at h1; omega
  by_cases hps : (optTailCap G.pending).slt 1#64 = true
  · obtain ⟨hps_gt0, hps_le0, hps_ge1⟩ := cap_slt_conds_of_true hps
    by_cases hks : (optTailCap G.kyber).slt 1#64 = true
    · obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_true hks
      apply SepWPpIn.of_sepWP
        (mid := entry +
          bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
            ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold (heap_split_tt A hheap hps hks) (by sep_focus) ?_
      wp_steps
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      wp_call hlen ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wppin_callc hshim (shimSubSpecX.inImage img) ()
      refine SepWPpIn.weaken_pre (Entails.of_eq (by unfold archiveMidShimPre; ac_rfl))
        (hcont _ bs336 hbs336 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*]))
    · have hks' : (optTailCap G.kyber).slt 1#64 = false := Bool.eq_false_iff.mpr hks
      obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_false hks'
      apply SepWPpIn.of_sepWP
        (mid := entry +
          bv% (ls_off% "__rustc::__rust_dealloc" -
            ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold (heap_split_tf A hheap hps hks') (by sep_focus) ?_
      apply sepWP_pure_left_sepX; rintro ⟨hk_pos, hk_lt⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hex_k : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_k : (optTailCap G.kyber).toNat + 1 ≤ 2 ^ 63 := by omega
      wppin_callc hdealloc ((rustDeallocSubSpecX A).inImage img) (kPtr, (optTailCap G.kyber).toNat, 1)
      apply SepWPpIn.of_sepWP
        (mid := entry +
          bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
            ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      wp_steps
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      wp_call hlen ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wppin_callc hshim (shimSubSpecX.inImage img) ()
      refine SepWPpIn.weaken_pre (Entails.of_eq (by unfold archiveMidShimPre; ac_rfl))
        (hcont _ bs336 hbs336 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*]))
  · have hps' : (optTailCap G.pending).slt 1#64 = false := Bool.eq_false_iff.mpr hps
    obtain ⟨hps_gt0, hps_le0, hps_ge1⟩ := cap_slt_conds_of_false hps'
    by_cases hks : (optTailCap G.kyber).slt 1#64 = true
    · obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_true hks
      apply SepWPpIn.of_sepWP
        (mid := entry +
          bv% (ls_off% "__rustc::__rust_dealloc" -
            ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold (heap_split_ft A hheap hps' hks) (by sep_focus) ?_
      apply sepWP_pure_left_sepX; rintro ⟨hp_pos, hp_lt⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hex_p : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_p : (optTailCap G.pending).toNat + 1 ≤ 2 ^ 63 := by omega
      wppin_callc hdealloc ((rustDeallocSubSpecX A).inImage img) (pPtr, (optTailCap G.pending).toNat, 1)
      apply SepWPpIn.of_sepWP
        (mid := entry +
          bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
            ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      wp_steps
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      wp_call hlen ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wppin_callc hshim (shimSubSpecX.inImage img) ()
      refine SepWPpIn.weaken_pre (Entails.of_eq (by unfold archiveMidShimPre; ac_rfl))
        (hcont _ bs336 hbs336 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*]))
    · have hks' : (optTailCap G.kyber).slt 1#64 = false := Bool.eq_false_iff.mpr hks
      obtain ⟨hks_gt0, hks_le0, hks_ge1⟩ := cap_slt_conds_of_false hks'
      apply SepWPpIn.of_sepWP
        (mid := entry +
          bv% (ls_off% "__rustc::__rust_dealloc" -
            ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      refine SepWP.fold hsplit448 (by sep_focus) ?_
      refine SepWP.fold (heap_split_ff A hheap hps' hks') (by sep_focus) ?_
      apply sepWP_pure_left_sepX; rintro ⟨⟨hp_pos, hp_lt⟩, ⟨hk_pos, hk_lt⟩⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hex_p : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_p : (optTailCap G.pending).toNat + 1 ≤ 2 ^ 63 := by omega
      wppin_callc hdealloc ((rustDeallocSubSpecX A).inImage img) (pPtr, (optTailCap G.pending).toNat, 1)
      apply SepWPpIn.of_sepWP
        (mid := entry +
          bv% (ls_off% "__rustc::__rust_dealloc" -
            ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hex_k : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsz_k : (optTailCap G.kyber).toNat + 1 ≤ 2 ^ 63 := by omega
      wppin_callc hdealloc ((rustDeallocSubSpecX A).inImage img) (kPtr, (optTailCap G.kyber).toNat, 1)
      apply SepWPpIn.of_sepWP
        (mid := entry +
          bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
            ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      wp_steps
      refine SepWP.fold hpack_clear (by sep_focus) ?_
      wp_call hlen ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess⟩
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      wppin_callc hshim (shimSubSpecX.inImage img) ()
      refine SepWPpIn.weaken_pre (Entails.of_eq (by unfold archiveMidShimPre; ac_rfl))
        (hcont _ bs336 hbs336 (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
          (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*]))

/-! ## Allocator-Shim Return to `encode_raw` Return -/

set_option maxHeartbeats 800000 in
theorem archive_shim_to_raw_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (hRaw : EncodeRawOkX img A ext)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (bs336 : List (BitVec 8))
    (Fprev R : SepProp)
    (s0 s2 : State)
    (Q : State → SepProp → Prop)
    (hsp_align : s0.spAligned = true)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (c0 c1 c2 c3 v464 : BitVec 64) (v112 : BitVec 128)
    (hpc2 : s2.pc = (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName + (archiveShimCutOff + 4#64))
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 464#64)
    (htr2 : s2.trace = s0.trace)
    (hx19 : s2.readReg64 .x19 = recPtr)
    (hx20 : s2.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length)
    (hx23 : s2.readReg64 .x23 = 0#64)
    (hx24 : s2.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s2.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s2.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s2.readReg64 .x28 = s0.readReg64 .x28)
    (hx29 : s2.readReg64 .x29 = s0.sp - 64#64)
    (hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hcont : ∀ (sf : State) (capEnc ptrEnc : BitVec 64),
      sf.pc = (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName + (archiveEncodeRawCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x21 = s0.sp - 112#64 →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 .lr) sf
        (archiveMidRawPre A s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 Fprev)
        Q (archiveQp s0 R)) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 .lr) s2
      (archiveMidShimPre A s0 recPtr prevCap prevPtr G sess bs336 c0 c1 c2 c3 v464 v112 Fprev)
      Q (archiveQp s0 R) := by
  have hfn : libsignalSessionCode.fnOff archiveCurrentStateInnerName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner") :=
    libsignalSessionCode_fnOff_archive
  have halloc := alloc_arch_okX (img := img) (A := A) (ext := ext) hC
  have hpanic := archive_panic_at_handle_errorX (b := img.base) (ext := ext)
  have hraw := encodeRaw_arch_okX hRaw
  code_fetches_from CryptoVerification.libsignalSessionCode
    archiveBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    0xd4 0x74
  code_fetches_from CryptoVerification.libsignalSessionCode
    archiveBin img.base (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    0x15c 0x40
  revert hpc2 hcont
  have hpc_anchor :
      ({ s0 with pc := (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName } : State).pc =
        (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName := rfl
  examples_generalize_entry
  clear hpc_anchor
  intro hpc2 hcont
  simp only [archiveShimCutOff, arm64_norm] at hpc2
  examples_hide_fetches
  unfold archiveMidShimPre
  have hn_pos : 0 < (encSessionMem (clearPendingGhost G) (clearPending sess)).length :=
    encSessionMem_length_pos _ _
  have hn_toNat : (BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length).toNat =
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply SepWPpIn.of_sepWP
    (mid := entry +
      bv% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hex_pow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hsz_le : (encSessionMem (clearPendingGhost G) (clearPending sess)).length + 1 ≤ 2 ^ 63 := by
    omega
  have hsz_le' :
      (encSessionMem (clearPendingGhost G) (clearPending sess)).length ≤ 9223372036854775807 := by
    omega
  wppin_callc halloc ((rustAllocSubSpecX A).inImage img)
    ((encSessionMem (clearPendingGhost G) (clearPending sess)).length, 1)
  by_cases hp0 : sf.readReg64 .x0 = 0#64
  · have hp0_zero : sf.readReg64 .x0 = 0 := hp0
    conv => arg 5; simp only [hp0_zero, ↓reduceIte, sepConj_assoc]
    refine SepWPpIn.pure_elim fun htr_fail => ?_
    apply SepWPpIn.of_sepWP
      (mid := entry +
        bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPpIn.panic (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_eq
          (by simp only [Rust.panicked, htr_fail, htr2, wp_norm, arm64_norm])) hm
  · have hp0' : sf.readReg64 .x0 ≠ 0 := hp0
    have hp0_beq : (sf.readReg64 .x0 == 0#64) = false := beq_false_of_ne hp0
    conv => arg 5; simp only [hp0', ↓reduceIte, sepConj_assoc]
    refine SepWPpIn.pure_elim fun ⟨halign, htr_alloc⟩ => ?_
    apply SepWPpIn.of_sepWP
      (mid := entry +
        bv% (2 ^ 64 +
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") -
          (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")))
    wp_steps
    refine SepWP.fold
      (vecU8At_nil_88X A s0.sp (sf.readReg64 .x0)
        (encSessionMem (clearPendingGhost G) (clearPending sess)).length
        hn_pos (by omega) hp0')
      (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hraw_lt : ([] : List (BitVec 8)).length +
        (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32 := by
      simp only [List.length_nil, Nat.zero_add]; exact hlen_enc
    wppin_callc hraw ((encodeRawSubSpecX A).inImage img)
      ⟨s0.sp - 456#64, clearPendingGhost G, clearPending sess, s0.sp - 88#64,
        BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length,
        sf.readReg64 .x0, []⟩
    refine SepWPpIn.weaken_pre (Entails.of_eq (by unfold archiveMidRawPre; ac_rfl))
      (hcont _ _ _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [*]))

/-- Combined prefix from `archive_current_state_inner` entry through `encode_raw` return. -/
theorem archive_head_to_raw_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (hRaw : EncodeRawOkX img A ext)
    (recPtr prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    (Fprev R : SepProp)
    (s0 : State)
    (Q : State → SepProp → Prop)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = recPtr)
    (hlen_enc : (encSessionMem (clearPendingGhost G) (clearPending sess)).length < 2 ^ 32)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 : BitVec 64) (v112 : BitVec 128)
    (hcont : ∀ (sf : State) (bs336 : List (BitVec 8)) (capEnc ptrEnc : BitVec 64),
      bs336.length = 336 →
      sf.pc = (SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName + (archiveEncodeRawCutOff + 4#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 464#64 →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = recPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 (encSessionMem (clearPendingGhost G) (clearPending sess)).length →
      sf.readReg64 .x21 = s0.sp - 112#64 →
      sf.readReg64 .x23 = 0#64 →
      sf.readReg64 .x24 = s0.readReg64 .x24 →
      sf.readReg64 .x25 = s0.readReg64 .x25 →
      sf.readReg64 .x26 = s0.readReg64 .x26 →
      sf.readReg64 .x27 = s0.readReg64 .x27 →
      sf.readReg64 .x28 = s0.readReg64 .x28 →
      sf.readReg64 .x29 = s0.sp - 64#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 .lr) sf
        (archiveMidRawPre A s0 recPtr prevCap prevPtr G sess bs336 capEnc ptrEnc c0 v464 v112 Fprev)
        Q (archiveQp s0 R)) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 .lr) s0
      ((recPtr ↦₆₄ prevCap) ∗ ((recPtr + 8#64) ↦₆₄ prevPtr) ∗ ((recPtr + 16#64) ↦₆₄ 0#64) ∗
        sessionStateReprAt A (recPtr + 0x18#64) G sess ∗ A.pool ∗
        stackAt (s0.sp - 464#64) serializeSubStackX ∗
        ((s0.sp - 464#64) ↦₆₄ v464) ∗ ((s0.sp - 456#64) ↦₆₄ v456) ∗
        memRegion (s0.sp - 448#64) 336 ∗ ((s0.sp - 112#64) ↦₁₂₈ v112) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗ Fprev)
      Q (archiveQp s0 R) :=
  archive_clear_to_shim_cps hC recPtr prevCap prevPtr G sess Fprev R s0 Q
    hpc hrun hsp_align hx0 hlen_enc c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v464 v456 v112
    fun s2 bs336 hbs336 hpc2 hrun2 hsp2 htr2 hx19 hx20 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs2 =>
      archive_shim_to_raw_cps hC hRaw recPtr prevCap prevPtr G sess bs336 Fprev R s0 s2 Q
        hsp_align hlen_enc c0 c1 c2 c3 v464 v112
        hpc2 hrun2 hsp2 htr2 hx19 hx20 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs2
        fun sf capEnc ptrEnc => hcont sf bs336 capEnc ptrEnc hbs336

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
