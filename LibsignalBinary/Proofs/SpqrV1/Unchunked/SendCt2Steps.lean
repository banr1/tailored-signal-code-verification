/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<Ct1SentEkReceived>::send_ct2`: Stepping Helpers and Segments 1, 2, and 4

**Checked by Lean.**

Provides stack/memory splitting helpers and proves fixed-base Segments 1, 2, and 4
for `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ChainProofs CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L29b
open NextKeyInternalFacts AgreeStateSimp DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length ctLabel_length

theorem mlkemEncaps2_fnOff :
    libsignalSessionCode.fnOff mlkemEncaps2Name =
      num% (ls_off% "libcrux_ml_kem::mlkem768::incremental::encapsulate2") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_stub% "libcrux_ml_kem::mlkem768::incremental::encapsulate2")

theorem doReserve7_fnOff :
    libsignalSessionCode.fnOff doReserve7Name =
      num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")

theorem sliceConcat_fnOff' :
    libsignalSessionCode.fnOff sliceConcatName =
      num% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]")

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  unchunkedCt1SentEkReceivedSendCt2_fnOff
  sliceConcat_fnOff' doReserve7_fnOff mlkemEncaps2_fnOff
  MacHdrFacts.libcruxHmac_fnOff dealloc_fnOff
  (ls_lemma% fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")
  (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")
  (ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_hook% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::encapsulate2")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::encapsulate2")
  (ls_stub% "libcrux_hmac::hmac")
  (ls_hook% "libcrux_hmac::hmac")

/-! ## Callee Wrappers -/

/-- `libcrux_ml_kem::mlkem768::incremental::encapsulate2` (`0x78c20`) at a relative call offset. -/
theorem mlkem_encaps2_ok_at_ext (b : BitVec 64) (K : MlKem)
    (ext : String → Option (State → State))
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff mlkemEncaps2Name := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (mlkemEncaps2Spec K) :=
  hook_ok_at (hname := mlkemEncaps2Name) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hencaps2

/-- Specialized `libcrux_hmac::hmac` contract when `key.length < 2^32` and `data.length < 2^32`
are already known at the call site, reducing `onPanic` to `allocFailedIn`. -/
def libcruxHmacSafeSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec LibcruxHmacCall where
  pre x s :=
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A x.ret (hmacWith F x.key x.data) ∗ A.pool ∗ stackAt s0.sp extHookStack
  onPanic _ s0 sf :=
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem libcrux_hmac_safe_ok_at_ext (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (ext : String → Option (State → State))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff libcruxHmacName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (libcruxHmacSafeSpec F A) := by
  have hraw := libcrux_hmac_ok_at_ext b F A ext hhmac name k hk
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [libcruxHmacSafeSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hk_lt, hd_lt⟩, hmem⟩
  have hpre' : s0.mem ⊨ (libcruxHmacSpec F A).pre x s0 ∗ R := by
    dsimp only [libcruxHmacSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hmem⟩
  refine hraw.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [libcruxHmacSpec, libcruxHmacSafeSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.2.2, hpost.2⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [libcruxHmacSpec, libcruxHmacSafeSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨haf | hk_ge | hd_ge, hpref⟩, hmem'⟩
    · exact ⟨⟨haf, hpref⟩, hmem'⟩
    · omega
    · omega
  · exact Or.inr (Or.inr hex)

theorem SepWPp.call_allowPanic_mid {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧ (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call hcall hpc hrun hsp_align hlr hpre ?_ ?_ hnext ?_
  · intro sf code R' _ hpost
    rw [hexit_eq.1] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sf _ hm'
    exact Satisfies.mono (sepConj_mono_left (hpan sf)) hm'
  · intro sf R' _ hpost
    rw [hexit_eq.2] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

open Lean Elab Tactic in
elab "wpp_call_sendCt2 " hcall:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  evalTactic (← `(tactic| (
    apply (SepWPp.call_allowPanic_mid $hcall (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "wpp_call_sendCt2: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR'
    try simp (config := { decide := true }) only [
      bytesAt_true, bytesAt_false,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm, *]
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact onPanic_entails_of_trace_eq (by wp_norm_lhs))
    wp_focus_close (wp_unfold_specs; exact ⟨fun _ _ => rfl, fun _ => rfl⟩)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

/-! ## Stack and Memory Splitting Helpers -/

/-- Split `stackAt sp unchunkedSendCt2Stack` (`336 + extHookStack = 16720` bytes) into its frame slots:
- `stackAt (sp - 336#64) extHookStack` (`16384`B below `sp - 336`)
- `memRegion (sp - 336#64) 8` (`[sp1 + 0, sp1 + 8)`)
- 6 cells at `sp - 328#64 .. sp - 288#64` (`[sp1 + 8, sp1 + 56)`: `es.cap, ek.cap, epoch, ct1.cap, ct1.ptr, ct1.len`)
- `memRegion (sp - 280#64) 8` (`[sp1 + 56, sp1 + 64)`)
- `(sp - 272#64) ↦₆₄ s64 ∗ memRegion (sp - 264#64) 120` (`[sp1 + 64, sp1 + 192)`, 128B buffer)
- `memRegion (sp - 144#64) 24` (`[sp1 + 192, sp1 + 216)`, `x29 - 48`, `slice_concat_3` sret)
- `(sp - 120#64) ↦₆₄ e0` (`[sp1 + 216, sp1 + 224)`, `x29 - 24`, `epoch.to_be_bytes()`)
- `memRegion (sp - 112#64) 16` (`[sp1 + 224, sp1 + 240)`)
- 12 callee-save cells at `sp - 96#64 .. sp - 8#64` (`[sp1 + 240, sp1 + 336)`). -/
theorem stackAt_unchunkedSendCt2_split (sp : BitVec 64) :
    stackAt sp unchunkedSendCt2Stack =
      stackAt (sp - 336#64) extHookStack ∗
      memRegion (sp - 336#64) 8 ∗
      (∃∗ l0 : BitVec 64, ∃∗ l1 : BitVec 64, ∃∗ l2 : BitVec 64,
       ∃∗ l3 : BitVec 64, ∃∗ l4 : BitVec 64, ∃∗ l5 : BitVec 64,
        ((sp - 328#64) ↦₆₄ l0) ∗ ((sp - 320#64) ↦₆₄ l1) ∗
        ((sp - 312#64) ↦₆₄ l2) ∗ ((sp - 304#64) ↦₆₄ l3) ∗
        ((sp - 296#64) ↦₆₄ l4) ∗ ((sp - 288#64) ↦₆₄ l5)) ∗
      memRegion (sp - 280#64) 8 ∗
      (∃∗ s64 : BitVec 64, (sp - 272#64) ↦₆₄ s64) ∗
      memRegion (sp - 264#64) 120 ∗
      memRegion (sp - 144#64) 24 ∗
      (∃∗ e0 : BitVec 64, (sp - 120#64) ↦₆₄ e0) ∗
      memRegion (sp - 112#64) 16 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  change memRegion (sp - BitVec.ofNat 64 16720) 16720 =
    memRegion (sp - 336#64 - BitVec.ofNat 64 16384) 16384 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16720) (n := 16384) (k := 336)
      (b' := sp - 336#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 336#64) (n := 8) (k := 328)
      (b' := sp - 328#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 328#64) (n := 48) (k := 280)
      (b' := sp - 280#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 280#64) (n := 8) (k := 272)
      (b' := sp - 272#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 8) (k := 264)
      (b' := sp - 264#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 264#64) (n := 120) (k := 144)
      (b' := sp - 144#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 144#64) (n := 24) (k := 120)
      (b' := sp - 120#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 112)
      (b' := sp - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 112#64) (n := 16) (k := 96)
      (b' := sp - 96#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16720) 16384 ∗
    (memRegion (sp - 336#64) 8 ∗
      (memRegion (sp - 328#64) (8 * 6) ∗
        (memRegion (sp - 280#64) 8 ∗
          (memRegion (sp - 272#64) 8 ∗
            (memRegion (sp - 264#64) 120 ∗
              (memRegion (sp - 144#64) 24 ∗
                (memRegion (sp - 120#64) 8 ∗
                  (memRegion (sp - 112#64) 16 ∗ memRegion (sp - 96#64) (8 * 12))))))))) = _
  rw [ProofLib.memRegion_cells (sp - 328#64) 6 (by decide),
    ProofLib.memRegion_eight (sp - 272#64),
    ProofLib.memRegion_eight (sp - 120#64),
    ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]
  have hsub : sp - 336#64 - BitVec.ofNat 64 16384 = sp - BitVec.ofNat 64 16720 := by bv_kernel
  have hc6 : cells (sp - 328#64) 6 =
      (∃∗ l0 : BitVec 64, ∃∗ l1 : BitVec 64, ∃∗ l2 : BitVec 64,
       ∃∗ l3 : BitVec 64, ∃∗ l4 : BitVec 64, ∃∗ l5 : BitVec 64,
        ((sp - 328#64) ↦₆₄ l0) ∗ ((sp - 320#64) ↦₆₄ l1) ∗
        ((sp - 312#64) ↦₆₄ l2) ∗ ((sp - 304#64) ↦₆₄ l3) ∗
        ((sp - 296#64) ↦₆₄ l4) ∗ ((sp - 288#64) ↦₆₄ l5)) := by
    cells_unfold
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
    cells_unfold
  rw [hsub, hc6, hc12]

theorem fold_sp_272_128 (sp v : BitVec 64) :
    ((sp - 272#64) ↦₆₄ v) ∗ memRegion (sp - 264#64) 120 ⊢ memRegion (sp - 272#64) 128 := by
  rw [ProofLib.memRegion_split' (b := sp - 272#64) (n := 8) (k := 120)
        (b' := sp - 264#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (Drop.pointsTo64_entails_memRegion (sp - 272#64) v)

theorem stackAt_extHook_eq_allocHook (sp0 : BitVec 64) :
    stackAt (sp0 - 336#64) extHookStack =
      memRegion (sp0 - 16720#64) 12288 ∗ stackAt (sp0 - 336#64) allocHookStack := by
  change memRegion ((sp0 - 336#64) - 16384#64) 16384 =
    memRegion (sp0 - 16720#64) 12288 ∗ memRegion ((sp0 - 336#64) - 4096#64) 4096
  have h1 : (sp0 - 336#64) - 16384#64 = sp0 - 16720#64 := by bv_omega
  rw [h1, ProofLib.memRegion_split' (b := sp0 - 16720#64) (n := 12288) (k := 4096)
        (b' := (sp0 - 336#64) - 4096#64) rfl (by bv_omega) (by decide)]

theorem stackAt_extHook_eq_doReserve (sp0 : BitVec 64) :
    stackAt (sp0 - 336#64) extHookStack =
      memRegion (sp0 - 16720#64) 12176 ∗ stackAt (sp0 - 336#64) doReserveStack := by
  change memRegion ((sp0 - 336#64) - 16384#64) 16384 =
    memRegion (sp0 - 16720#64) 12176 ∗ memRegion ((sp0 - 336#64) - 4208#64) 4208
  have h1 : (sp0 - 336#64) - 16384#64 = sp0 - 16720#64 := by bv_omega
  rw [h1, ProofLib.memRegion_split' (b := sp0 - 16720#64) (n := 12176) (k := 4208)
        (b' := (sp0 - 336#64) - 4208#64) rfl (by bv_omega) (by decide)]

/-- Heap portion of `vecU8At A a cap ptr bs`. -/
def vecU8HeapAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_cells_heap (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  unfold vecU8At vecHeader vecU8HeapAt
  ac_rfl

/-- Unpack `vecU8 A a bs` into its 3 header words `(a, a+8, a+16)` and `vecU8HeapAt A cap ptr bs`. -/
theorem vecU8_entails_cells_and_heap (A : RustAlloc) (a : BitVec 64) (bs : Bytes) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A a cap ptr bs]
  have hb : vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ vecU8HeapAt A cap ptr bs := by
    unfold vecU8HeapAt
    apply Entails.pure_left; intro h
    exact Entails.pure_right h (Entails.pure_right h (Entails.refl _))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hb))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem fold_vecU8At_sp_304 (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : Bytes) :
    ((sp - 304#64) ↦₆₄ cap) ∗ ((sp - 296#64) ↦₆₄ ptr) ∗
      ((sp - 288#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8HeapAt A cap ptr bs ⊢
      vecU8At A (sp - 304#64) cap ptr bs := by
  rw [vecU8At_eq_cells_heap A (sp - 304#64) cap ptr bs]
  have h1 : (sp - 304#64) + 8#64 = sp - 296#64 := by bv_omega
  have h2 : (sp - 304#64) + 16#64 = sp - 288#64 := by bv_omega
  rw [h1, h2]
  exact Entails.of_eq (by ac_rfl)

theorem fold_stA_48_80 (stA v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    ((stA + 48#64) ↦₆₄ v0) ∗ ((stA + 56#64) ↦₆₄ v1) ∗
      ((stA + 64#64) ↦₆₄ v2) ∗ ((stA + 72#64) ↦₆₄ v3) ∗
      ((stA + 80#64) ↦₆₄ v4) ∗ ((stA + 88#64) ↦₆₄ v5) ∗
      ((stA + 96#64) ↦₆₄ v6) ∗ ((stA + 104#64) ↦₆₄ v7) ∗
      ((stA + 112#64) ↦₆₄ v8) ∗ ((stA + 120#64) ↦₆₄ v9) ⊢
      memRegion (stA + 48#64) 80 := by
  have ha1 : (stA + 48#64) + 8#64 = stA + 56#64 := by bv_omega
  have ha2 : (stA + 48#64) + 16#64 = stA + 64#64 := by bv_omega
  have ha3 : (stA + 48#64) + 24#64 = stA + 72#64 := by bv_omega
  have ha4 : (stA + 48#64) + 32#64 = stA + 80#64 := by bv_omega
  have ha5 : (stA + 48#64) + 40#64 = stA + 88#64 := by bv_omega
  have ha6 : (stA + 48#64) + 48#64 = stA + 96#64 := by bv_omega
  have ha7 : (stA + 48#64) + 56#64 = stA + 104#64 := by bv_omega
  have ha8 : (stA + 48#64) + 64#64 = stA + 112#64 := by bv_omega
  have ha9 : (stA + 48#64) + 72#64 = stA + 120#64 := by bv_omega
  change _ ⊢ memRegion (stA + 48#64) (8 * 10)
  rw [ProofLib.memRegion_cells (stA + 48#64) 10 (by decide)]
  dsimp only [cells]
  simp only [BitVec.add_zero, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
        (Entails.sepExists_right v9 (Entails.of_eq (by ac_rfl)))))))))))

/-- Callee-save slots saved at `sp - 96#64 .. sp - 8#64` by the prologue (`0x5e404..0x5e418`). -/
def sendCt2CalleeSavedAt (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

abbrev sendCt2PostQ (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (x : UnchunkedSendCt2Ghost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (unchunkedCt1SentEkReceivedSendCt2Spec A F K b).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev sendCt2PostQp (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (x : UnchunkedSendCt2Ghost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (unchunkedCt1SentEkReceivedSendCt2Spec A F K b).onPanic x s0 sf ∗ R)

theorem SepWPp.of_sepWP_mid {prog : Program} {retPC mid : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun s' P' => SepWPp prog retPC s' P' Q Qp)) :
    SepWPp prog retPC s P Q Qp :=
  SepWPp.of_sepWP h

theorem shim_ok_at_sendCt2 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      noAllocShimSpec := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
      bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      (tripleRatchetProgAtExt b ext).fnAddr shimName := by
    dsimp only [tripleRatchetProgAtExt, shimName]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, unchunkedCt1SentEkReceivedSendCt2_fnOff]
    simp only [arm64_norm]
  rw [hrel]; exact hA.shim

theorem alloc_ok_at_sendCt2 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (rustAllocSpec A) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
      bv% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      (tripleRatchetProgAtExt b ext).fnAddr allocName := by
    dsimp only [tripleRatchetProgAtExt, allocName]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, unchunkedCt1SentEkReceivedSendCt2_fnOff]
    simp only [arm64_norm]
  rw [hrel]; exact hA.alloc

theorem dealloc_ok_at_sendCt2 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (rustDeallocSpec A) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
      bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.LibsignalTripleRatchet.deallocName := by
    dsimp only [tripleRatchetProgAtExt, CryptoVerification.LibsignalTripleRatchet.deallocName]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, unchunkedCt1SentEkReceivedSendCt2_fnOff]
    simp only [arm64_norm]
  rw [hrel]; exact hA.dealloc

theorem memcpy_ok_at_sendCt2 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "memcpy" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (withStack sessionMemcpyRegionSpec extHookStack) := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
      bv% (ls_off% "memcpy" -
        ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      (tripleRatchetProgAtExt b ext).fnAddr memcpyName := by
    dsimp only [tripleRatchetProgAtExt, memcpyName]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, unchunkedCt1SentEkReceivedSendCt2_fnOff]
    simp only [arm64_norm]
  rw [hrel]; exact hA.session_memcpy_region extHookStack (by decide) (by decide)

theorem doReserve7_ok_at_sendCt2 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        (bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") -
          bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")))
      (doReserveSpec A) := by
  have hrel :
      (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        (bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") -
          bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")) =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve7Name := by
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      unchunkedCt1SentEkReceivedSendCt2_fnOff, doReserve7_fnOff]
    bv_omega
  rw [hrel]; exact do_reserve_7_ok_ext_4k hA

theorem sliceConcat3_ok_at_sendCt2 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sliceConcatName) (sliceConcat3Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (sliceConcat3Spec A) := by
  have hrel :
      (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      (tripleRatchetProgAtExt b ext).fnAddr sliceConcatName := by
    dsimp only [tripleRatchetProgAtExt]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      unchunkedCt1SentEkReceivedSendCt2_fnOff, sliceConcat_fnOff']
    bv_omega
  rw [hrel]; exact hconcat3

theorem panic_at_handle_error_sendCt2 (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext unchunkedCt1SentEkReceivedSendCt2Name
    (num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))

/-! ## Segment 1: Prologue (`0x5e400 → 0x5e488`) -/

set_option maxHeartbeats 800000 in
theorem send_ct2_prologue_to_scan {b : BitVec 64} {ext : String → Option (State → State)}
    {F : ShaCompress} (A : RustAlloc)
    (outA stA : BitVec 64)
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr : BitVec 64)
    (l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64)
    (s0 : State) (Frame : SepProp)
    (hes_len : st.es.length = 2080)
    (hek_len : st.ek.length = 1152)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
    (hrun : s0.status = .Running)
    (hsp : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = outA)
    (hx1 : s0.readReg64 .x1 = stA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
      s0
      ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
        ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
        ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
        ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
        ((stA + 48#64) ↦₆₄ esCap) ∗ ((stA + 56#64) ↦₆₄ esPtr) ∗
        ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
        ((stA + 72#64) ↦₆₄ ekCap) ∗ ((stA + 80#64) ↦₆₄ ekPtr) ∗
        ((stA + 88#64) ↦₆₄ BitVec.ofNat 64 st.ek.length) ∗
        ((stA + 96#64) ↦₆₄ ct1Cap) ∗ ((stA + 104#64) ↦₆₄ ct1Ptr) ∗
        ((stA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
        ((stA + 120#64) ↦₆₄ st.epoch) ∗
        vecU8HeapAt A ct1Cap ct1Ptr st.ct1 ∗
        ((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
        ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
        ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5) ∗
        ((s0.sp - 272#64) ↦₆₄ s64) ∗ memRegion (s0.sp - 264#64) 120 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗
        Frame)
      (fun sf Pf =>
        Pf = ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
          ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
          ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
          ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
          memRegion (stA + 48#64) 80 ∗
          ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
          ((s0.sp - 312#64) ↦₆₄ st.epoch) ∗
          vecU8At A (s0.sp - 304#64) ct1Cap ct1Ptr st.ct1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          ((s0.sp - 120#64) ↦₆₄ e0) ∗
          sendCt2CalleeSavedAt s0 ∗
          Frame) ∧
        sf.sp = s0.sp - 336#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        sf.readReg64 .x8 = esPtr + 1536#64 ∧
        sf.readReg64 .x9 = 512#64 ∧
        sf.readReg64 .x10 = 2#64 ∧
        sf.readReg64 .x11 = 65534#64 ∧
        sf.readReg64 .x13 = 65535#64 ∧
        sf.readReg64 .x19 = esPtr ∧
        sf.readReg64 .x20 = ekPtr ∧
        sf.readReg64 .x23 = outA ∧
        sf.readReg64 .x24 = stA ∧
        sf.readReg64 .x25 = mkPtr ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 st.auth.macKey.length ∧
        sf.readReg64 .x27 = 1152#64 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  simp only [wp_norm, arm64_norm] at hx0 hx1
  send_ct2_fetches b (Rust.withPanics ext) 136
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  rw [hes_len, hek_len]
  wp_steps
  refine SepWP.fold (fold_stA_48_80 stA esCap esPtr 2080#64 ekCap ekPtr 1152#64
    ct1Cap ct1Ptr (BitVec.ofNat 64 st.ct1.length) st.epoch) (by sep_focus) ?_
  refine SepWP.fold (fold_vecU8At_sp_304 A s0.sp ct1Cap ct1Ptr st.ct1) (by sep_focus) ?_
  refine SepWP.fold (fold_sp_272_128 s0.sp 2080#64) (by sep_focus) ?_
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  unfold sendCt2CalleeSavedAt
  refine ⟨by ac_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [State.sp, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x13, Reg.x19, Reg.x20,
      Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29,
      arm64_norm, hx0, hx1]

/-! ## Segment 4: `ct1.reserve(128)` (`0x5e690 → 0x5e6a4`) -/

theorem vecU8HeapAt_expose_nonempty (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 := by
  dsimp only [vecU8HeapAt]
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr_ne⟩
  have hcap_ne : cap ≠ 0 := by
    intro h0; subst h0
    have hle0 : bs.length ≤ 0 := hle
    omega
  simp only [hcap_ne, ↓reduceIte]
  refine Entails.pure_right ⟨hle, hmax, hptr_ne, hcap_ne⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem vecU8HeapAt_expose_of_ne_zero (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap_ne : cap ≠ 0#64) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 := by
  dsimp only [vecU8HeapAt]
  have hcap_ne' : cap ≠ 0 := hcap_ne
  simp only [hcap_ne', ↓reduceIte]
  exact Entails.of_eq (by ac_rfl)

theorem le_of_not_ule_sub_len {cap : BitVec 64} {len : Nat}
    (hle : len ≤ cap.toNat) (hmax : cap.toNat < 2 ^ 63)
    (h : ¬ (cap - BitVec.ofNat 64 len).ule 127#64 = true) :
    len + 128 ≤ cap.toNat := by
  have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le] at h
  · rw [hlen_bv] at h
    change ¬ (cap.toNat - len ≤ 127) at h; omega
  · rw [BitVec.le_def, hlen_bv]; exact hle

theorem cap_ne_zero_of_add_128_le {cap : BitVec 64} {len : Nat}
    (h : len + 128 ≤ cap.toNat) : cap ≠ 0#64 := by
  intro h0; subst h0; simp at h

theorem reserveCap_bound_of_ule_sub_len {cap : BitVec 64} {len : Nat}
    (hle : len ≤ cap.toNat) (hlen : len < 2 ^ 32)
    (h : (cap - BitVec.ofNat 64 len).ule 127#64 = true) :
    reserveCap cap.toNat len 128 + 1 ≤ 2 ^ 63 := by
  have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le] at h
  · rw [hlen_bv] at h
    change cap.toNat - len ≤ 127 at h
    dsimp only [reserveCap]
    omega
  · rw [BitVec.le_def, hlen_bv]; exact hle

theorem reserveCap_ge_add_128 {cap len : Nat}
    (hbound : reserveCap cap len 128 + 1 ≤ 2 ^ 63) :
    len + 128 ≤ (BitVec.ofNat 64 (reserveCap cap len 128)).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only [reserveCap]
  omega

theorem reserveCap_ne_zero_len {cap len : Nat}
    (hbound : reserveCap cap len 128 + 1 ≤ 2 ^ 63) :
    BitVec.ofNat 64 (reserveCap cap len 128) ≠ 0#64 := by
  intro h0
  have h1 := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  change reserveCap cap len 128 = 0 at h1
  dsimp only [reserveCap] at h1
  omega

theorem vecU8At_expose_sp_304_of_ne_zero (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap_ne : cap ≠ 0#64) :
    vecU8At A (sp - 304#64) cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 304#64) ↦₆₄ cap) ∗
        ((sp - 296#64) ↦₆₄ ptr) ∗
        ((sp - 288#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by
  rw [vecU8At_eq_cells_heap A (sp - 304#64) cap ptr bs]
  have h1 : (sp - 304#64) + 8#64 = sp - 296#64 := by bv_omega
  have h2 : (sp - 304#64) + 16#64 = sp - 288#64 := by bv_omega
  rw [h1, h2]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_of_ne_zero A cap ptr bs hcap_ne)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem vecU8At_expose_sp_304_cells_heap (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp - 304#64) cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 304#64) ↦₆₄ cap) ∗
        ((sp - 296#64) ↦₆₄ ptr) ∗
        ((sp - 288#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  rw [vecU8At_eq_cells_heap A (sp - 304#64) cap ptr bs]
  have h1 : (sp - 304#64) + 8#64 = sp - 296#64 := by bv_omega
  have h2 : (sp - 304#64) + 16#64 = sp - 288#64 := by bv_omega
  rw [h1, h2]
  have hb : vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ vecU8HeapAt A cap ptr bs := by
    unfold vecU8HeapAt
    apply Entails.pure_left; intro h
    exact Entails.pure_right h (Entails.pure_right h (Entails.refl _))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hb))) ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
theorem send_ct2_reserve_ct1_wpp {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (x : UnchunkedSendCt2Ghost F)
    (cap_ct1 ptr_ct1 : BitVec 64) (s0 st : State) (F_frame R : SepProp)
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 656#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64),
      cap_ct1' ≠ 0#64 → x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 → ptr_ct1' ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 676#64 →
      st'.status = .Running → st'.sp = s0.sp - 336#64 → st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length →
      st'.readReg64 .x19 = st.readReg64 .x19 → st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x23 = st.readReg64 .x23 → st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 → st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 → st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        (((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗ A.pool ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        (sendCt2PostQ A F K b x s0 R) (sendCt2PostQp A F K b x s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (vecU8At A (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (sendCt2PostQ A F K b x s0 R) (sendCt2PostQp A F K b x s0 R) := by
  have h_res := doReserve7_ok_at_sendCt2 hA
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm
  unfold tripleRatchetProgAtExt at hpc h_res hcont ⊢
  send_ct2_fetches_range b (Rust.withPanics ext) 656 20
  send_ct2_fetches_range b (Rust.withPanics ext) 1036 28
  clear hA
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      unchunkedCt1SentEkReceivedSendCt2Name = entry
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.fold (vecU8At_expose_sp_304_cells_heap A s0.sp cap_ct1 ptr_ct1 x.st.ct1) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hct1_le, hct1_lt, hptr_ct1_ne⟩
  by_cases hls : ¬ (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true
  · have hls_f : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = false :=
      Bool.eq_false_iff.mpr hls
    have hge128 : x.st.ct1.length + 128 ≤ cap_ct1.toNat :=
      le_of_not_ule_sub_len hct1_le hct1_lt hls
    have hcap_ct1_ne : cap_ct1 ≠ 0#64 := cap_ne_zero_of_add_128_le hge128
    refine SepWPp.fold (vecU8HeapAt_expose_of_ne_zero A cap_ct1 ptr_ct1 x.st.ct1 hcap_ct1_ne) (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
    refine SepWPp.of_sepWP_mid (mid := entry + 676#64) ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ cap_ct1 ptr_ct1 hcap_ct1_ne hge128 hct1_lt hptr_ct1_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hls_t : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true := Classical.not_not.mp hls
    have hbound := reserveCap_bound_of_ule_sub_len hct1_le hct1_lt32 hls_t
    refine SepWPp.of_sepWP_mid
      (mid := entry + (bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") -
        bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))) ?_
    wp_steps
    refine SepWP.fold (fold_vecU8At_sp_304 A s0.sp cap_ct1 ptr_ct1 x.st.ct1) (by sep_focus) ?_
    have hstack_res :
        stackAt (s0.sp - 336#64) extHookStack ⊢
          memRegion (s0.sp - 16720#64) 12176 ∗ stackAt (s0.sp - 336#64) doReserveStack :=
      Entails.of_eq (stackAt_extHook_eq_doReserve s0.sp)
    refine SepWP.fold hstack_res (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    wpp_call_sendCt2 h_res
      (⟨s0.sp - 304#64, cap_ct1, ptr_ct1, x.st.ct1, 128⟩ : DoReserveCall)
    let ptr_ct1' := w
    have hcap_ct1'_ne : BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128) ≠ 0#64 :=
      reserveCap_ne_zero_len hbound
    refine SepWPp.fold
      (vecU8At_expose_sp_304_of_ne_zero A s0.sp
        (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128))
        ptr_ct1' x.st.ct1 hcap_ct1'_ne)
      (by sep_focus) ?_
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨_, hmax_ct1', hptr_ct1'_ne⟩
    have hge128' :
        x.st.ct1.length + 128 ≤ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat :=
      reserveCap_ge_add_128 hbound
    refine SepWPp.of_sepWP_mid (mid := entry + 676#64) ?_
    wp_steps
    have hstack_back :
        memRegion (s0.sp - 16720#64) 12176 ∗ stackAt st.sp doReserveStack ⊢
          stackAt (s0.sp - 336#64) extHookStack := by
      rw [hsp, ← stackAt_extHook_eq_doReserve s0.sp]
      exact Entails.refl _
    refine SepWP.fold hstack_back (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.rw_pre (by ac_rfl)
      (hcont _ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ptr_ct1'
        hcap_ct1'_ne hge128' hmax_ct1' hptr_ct1'_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))

/-! ## Segment 2: Scan and Optional Endianness Flip (`0x5e488 → 0x5e628`) -/

theorem call_rustAlloc {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustAllocSpec A))
    (size align : Nat) (hlay : LayoutOk size align)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 Reg.x0).toNat = size) (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        (((if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size) ∗
          A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (size, align)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm; rw [hsplit] at hm; dsimp only [rustAllocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustAllocSpec]; rw [hsp, htrace]
    have hassoc :
        (A.pool ∗ stackAt sp_call allocHookStack ∗
          (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)) ∗ Frame =
        (((if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
           else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
             A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size) ∗
          A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) := by ac_rfl
    rw [hassoc]; exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf

/-- Conditional heap ownership of the working `es` buffer after `0x5e488 → 0x5e628`. -/
def sendCt2EsWorkAt (A : RustAlloc) (esPtr esWorkPtr : BitVec 64) (es : Bytes) : SepProp :=
  if issue1275NeedsFlip ((es.drop 1536).take 512) then
    ⌜esWorkPtr ≠ 0#64⌝ ∗ (esPtr ↦ₛ es) ∗
      (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes es) ∗ A.live esWorkPtr 2080 1
  else
    ⌜esWorkPtr = esPtr⌝ ∗ (esPtr ↦ₛ es)

set_option maxHeartbeats 1200000 in
/-- Allocate 2080-byte working buffer and `memcpy` `es` into it (`0x5e5d8 → 0x5e604` + OOM). -/
theorem send_ct2_5d8_to_604_wpp {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (x : UnchunkedSendCt2Ghost F) (esPtr : BitVec 64)
    (s0 st : State) (F_frame R : SepProp) (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x1d8#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0) (hx19 : st.readReg64 .x19 = esPtr)
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64), esWorkPtr ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64 →
      st'.status = .Running → st'.sp = s0.sp - 336#64 → st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 → st'.readReg64 .x8 = 0#64 →
      st'.readReg64 .x19 = esPtr → st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 → st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 → st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 → st'.readReg64 .x28 = 2080#64 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ x.st.es) ∗
          A.live esWorkPtr 2080 1 ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        (sendCt2PostQ A F K b x s0 R) (sendCt2PostQp A F K b x s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (sendCt2PostQ A F K b x s0 R) (sendCt2PostQp A F K b x s0 R) := by
  have hshim := shim_ok_at_sendCt2 hA
  have halloc := alloc_ok_at_sendCt2 hA
  have hmemcpy := memcpy_ok_at_sendCt2 hA
  have hpan := panic_at_handle_error_sendCt2 b ext
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19
  unfold tripleRatchetProgAtExt at hpc hshim halloc hmemcpy hpan hcont ⊢
  send_ct2_fetches_range b (Rust.withPanics ext) 472 44
  send_ct2_fetches_range b (Rust.withPanics ext) 1112 12
  clear hA
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      unchunkedCt1SentEkReceivedSendCt2Name = entry
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.of_sepWP_mid (mid := entry + 488#64) ?_
  wp_steps; wp_apply; wp_steps
  have hstack_alloc :
      stackAt (s0.sp - 336#64) extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine SepWP.fold hstack_alloc (by sep_focus) ?_
  have hlay_2080 : LayoutOk 2080 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine call_rustAlloc halloc 2080 1 hlay_2080
    (s0 := s0) (ret_pc := entry + 488#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  by_cases hoom : sf1.readReg64 (Reg.gpr 0#5) = 0
  · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_oom => ?_
    refine SepWPp.of_sepWP_mid
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")) ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    dsimp only [sendCt2PostQp, unchunkedCt1SentEkReceivedSendCt2Spec]
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htr_ok⟩ => ?_
    have hoom_false : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
    refine SepWPp.of_sepWP_mid (mid := entry + 0x204#64) ?_
    have hstack_back :
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
          stackAt (s0.sp - 336#64) extHookStack :=
      Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
    refine SepWP.fold hstack_back (by sep_focus) ?_
    have hmr_es :
        memRegion (sf1.readReg64 (Reg.gpr 0#5)) 2080 ⊢
          memRegion (sf1.readReg64 (Reg.gpr 0#5)) x.st.es.length := by
      rw [hes_len]; exact Entails.refl _
    refine SepWP.fold hmr_es (by sep_focus) ?_
    have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1
    simp only [wp_norm, arm64_norm] at hsp1_norm
    wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.rw_pre (by rw [hsp1]; sep_ac_rfl)
      (hcont _ (sf1.readReg64 (Reg.gpr 0#5)) hoom
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [Reg.x8, wp_norm, arm64_norm, *]) (by simp only [Reg.x19, wp_norm, arm64_norm, *])
        (by simp only [Reg.x20, wp_norm, arm64_norm, *]) (by simp only [Reg.x22, wp_norm, arm64_norm, *])
        (by simp only [Reg.x23, wp_norm, arm64_norm, *]) (by simp only [Reg.x24, wp_norm, arm64_norm, *])
        (by simp only [Reg.x25, wp_norm, arm64_norm, *]) (by simp only [Reg.x26, wp_norm, arm64_norm, *])
        (by simp only [Reg.x27, wp_norm, arm64_norm, *]) (by simp only [Reg.x28, wp_norm, arm64_norm, *])
        (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

set_option maxHeartbeats 1200000 in
theorem send_ct2_scan_to_628_wpp {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (x : UnchunkedSendCt2Ghost F) (esPtr : BitVec 64)
    (s0 st : State) (F_frame R : SepProp) (hb : b &&& 0xfff#64 = 0#64)
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true) (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64) (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64) (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64) (hx19 : st.readReg64 .x19 = esPtr)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64 →
      st'.status = .Running → st'.sp = s0.sp - 336#64 → st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr → st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64) →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 → st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 → st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)) →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        (sendCt2EsWorkAt A esPtr esWorkPtr x.st.es ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        (sendCt2PostQ A F K b x s0 R) (sendCt2PostQp A F K b x s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (sendCt2PostQ A F K b x s0 R) (sendCt2PostQp A F K b x s0 R) := by
  have hlen512 : ((x.st.es.drop 1536).take 512).length = 512 := by
    rw [List.length_take, List.length_drop, hes_len]; rfl
  have hbs_ne : (x.st.es.drop 1536).take 512 ≠ [] := by intro hnil; rw [hnil] at hlen512; contradiction
  have hbs_mod : ((x.st.es.drop 1536).take 512).length % 2 = 0 := by rw [hlen512]
  have hbs_le : ((x.st.es.drop 1536).take 512).length ≤ 512 := by omega
  have hrem_eq : (512#64 : BitVec 64) = BitVec.ofNat 64 ((x.st.es.drop 1536).take 512).length := by rw [hlen512]
  have hpre_eq :
      ((esPtr ↦ₛ x.st.es) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) =
      (((esPtr + 1536#64) ↦ₛ ((x.st.es.drop 1536).take 512)) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
    rw [es_scan_split esPtr x.st.es hes_len]; ac_rfl
  by_cases hflip : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = false
  · refine SepWPp.of_sepWP_mid
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64) ?_
    rw [hpre_eq]
    refine SepWP.mono
      (scan_loop_false_ok (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hb hbs_ne hbs_mod hbs_le hrem_eq hflip hpc hrun hx8 hx9 hx10 hx11 hx13 hx28) ?_
    rintro sf Pf hpc_sf hrun_sf ⟨hPf, hx21_sf, hx22_sf, hx28_sf, hsaved⟩
    have hwork : (esPtr ↦ₛ x.st.es) ⊢ sendCt2EsWorkAt A esPtr esPtr x.st.es := by
      unfold sendCt2EsWorkAt; simp only [hflip, Bool.false_eq_true, ↓reduceIte]
      exact Entails.pure_right trivial (Entails.refl _)
    have hPf_back : Pf ⊢
        sendCt2EsWorkAt A esPtr esPtr x.st.es ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf, ← hpre_eq]; exact sepConj_mono_left hwork
    refine SepWPp.fold hPf_back (sepConj_emp _).symm (SepWPp.rw_pre (sepConj_emp _) ?_)
    exact hcont sf esPtr hpc_sf hrun_sf
      (hsaved.sp.trans hsp) (hsaved.trace.trans htr) (hsaved.vregs.trans hvregs) (hsaved.x19.trans hx19) hsaved.x20
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx21_sf]) (hx22_sf.trans hx19)
      hsaved.x23 hsaved.x24 hsaved.x25 hsaved.x26 hsaved.x27
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx28_sf]) hsaved.x29
  · have hflip_t : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = true :=
      Bool.eq_true_of_not_eq_false hflip
    refine SepWPp.of_sepWP_mid
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x1d8#64) ?_
    rw [hpre_eq]
    refine SepWP.mono
      (scan_loop_true_ok (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hb hbs_ne hbs_mod hbs_le hrem_eq hflip_t hpc hrun hx8 hx9 hx10 hx11 hx13) ?_
    rintro s5d8 P5d8 hpc_5d8 hrun_5d8 ⟨hP5d8, hsaved1⟩
    have hP5d8_eq : P5d8 =
        (esPtr ↦ₛ x.st.es) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗
          (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ F_frame) := by
      rw [hP5d8, ← hpre_eq]; ac_rfl
    rw [hP5d8_eq]
    refine send_ct2_5d8_to_604_wpp hA x esPtr s0 s5d8 (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ F_frame) R
      hes_len hpc_5d8 hrun_5d8 (hsaved1.sp.trans hsp) hsp_s0 (hsaved1.trace.trans htr)
      (hsaved1.vregs.trans hvregs) (hsaved1.x19.trans hx19) ?_
    intro s604 esWorkPtr hwork_ne hpc604 hrun604 hsp604 htr604 hvregs604 hx8_604 hx19_604 hx20_604 hx22_604 hx23_604 hx24_604 hx25_604 hx26_604 hx27_604 hx28_604 hx29_604
    refine SepWPp.of_sepWP_mid
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64) ?_
    have h2048_len : (x.st.es.take 2048).length = 2048 := by rw [List.length_take, hes_len]; rfl
    have h2048_ne : x.st.es.take 2048 ≠ [] := by intro hnil; rw [hnil] at h2048_len; contradiction
    have h2048_mod : (x.st.es.take 2048).length % 2 = 0 := by rw [h2048_len]
    have h2048_sum : (0#64 : BitVec 64).toNat + (x.st.es.take 2048).length = 2048 := by rw [h2048_len]; rfl
    have hsplit_swap :
        (esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗
          (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ F_frame) =
        (((esWorkPtr + 0#64) ↦ₛ (x.st.es.take 2048)) ∗
          (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
            (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
            ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
      rw [es_swap_split esWorkPtr x.st.es hes_len]; ac_rfl
    rw [hsplit_swap]
    refine SepWP.mono
      (swap_loop_ok esWorkPtr (x.st.es.take 2048) 0#64 s604
        (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
          (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        h2048_ne h2048_mod h2048_sum hpc604 hrun604 hx22_604 hx8_604) ?_
    rintro st' Pf2 hpc' hrun' ⟨hPf2, hx21', hsaved2⟩
    have hwork :
        (esPtr ↦ₛ x.st.es) ∗
          (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1 ⊢
          sendCt2EsWorkAt A esPtr esWorkPtr x.st.es := by
      unfold sendCt2EsWorkAt; simp only [hflip_t, ↓reduceIte]
      exact Entails.pure_right hwork_ne (Entails.of_eq (by ac_rfl))
    have hpost_ent : Pf2 ⊢
        sendCt2EsWorkAt A esPtr esWorkPtr x.st.es ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf2, ← sepConj_assoc, es_swap_join _ _ hes_len]
      refine Entails.trans (Entails.of_eq (show _ =
        ((esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1) ∗
          (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) by ac_rfl)) ?_
      exact sepConj_mono_left hwork
    refine SepWPp.fold hpost_ent (sepConj_emp _).symm (SepWPp.rw_pre (sepConj_emp _) ?_)
    exact hcont st' esWorkPtr hpc' hrun'
      (hsaved2.sp.trans hsp604) (hsaved2.trace.trans htr604) (hsaved2.vregs.trans hvregs604)
      (hsaved2.x19.trans hx19_604)
      ((hsaved2.x20.trans hx20_604).trans hsaved1.x20)
      (by simp only [hflip_t, ↓reduceIte, hx21'])
      (hsaved2.x22.trans hx22_604)
      ((hsaved2.x23.trans hx23_604).trans hsaved1.x23)
      ((hsaved2.x24.trans hx24_604).trans hsaved1.x24)
      ((hsaved2.x25.trans hx25_604).trans hsaved1.x25)
      ((hsaved2.x26.trans hx26_604).trans hsaved1.x26)
      ((hsaved2.x27.trans hx27_604).trans hsaved1.x27)
      (by simp only [hflip_t, ↓reduceIte, hsaved2.x28.trans hx28_604])
      ((hsaved2.x29.trans hx29_604).trans hsaved1.x29)

end CryptoVerification.SpqrV1.Unchunked

