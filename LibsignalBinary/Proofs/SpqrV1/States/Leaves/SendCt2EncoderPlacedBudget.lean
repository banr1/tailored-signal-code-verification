/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# `spqr::v1::chunked::send_ct::send_ct2_encoder` (Budget-Threaded, Block `382`)

Two-envelope (`SendCt2EncoderPreEnv` / `SendCt2EncoderPostEnv`), single-envelope, and exact
`[LibsignalPlacement]` contracts (`send_ct2_encoder_placed_{cl_ext,ok_x}*`) and framed call rules
for `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`, `85` instructions).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_382 blkPl_382
  lsProg_382 ls_subroutine_ok_of_block lsmpl lsρ
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (Bytes PolyEncoder spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (send_ct2_encoder)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.SpqrV1.Alloc (
  spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
  spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (encodeBytesResult encodeBytesStackX)
open CryptoVerification.SpqrV1.States.Leaves (
  SendCt2EncoderGhost bv_sub_sub encodeBytesResult_of_expectEncodeBytes_ok
  fold_sendCt2SavedCells of_sepWP_lscl
  sendCt2EncoderStack sendCt2SavedCells
  sp_sub_496_add_8 sp_sub_504_add_16 sp_sub_504_add_8
  sp_sub_512_add_16 sp_sub_512_add_24 sp_sub_512_add_32 sp_sub_512_add_432 sp_sub_512_add_8
  sp_sub_80_add_16 sp_sub_80_add_24 sp_sub_80_add_32 sp_sub_80_add_40 sp_sub_80_add_48
  sp_sub_80_add_56 sp_sub_80_add_64 sp_sub_80_add_72 sp_sub_80_add_8 sp_sub_80_add_80
  sp_sub_80_sub_432
  stackAt_encodeBytesX_from_allocHook stackAt_encodeBytesX_to_allocHook
  stackAt_sendCt2Encoder_split subroutine_ok_withLsCodeLoaded_of_left vecU8Tail
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  SeqEnv fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
  rustCliReallocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (
  doReserveRawSpec do_reserve_7_raw_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (
  encodeBytesAllocEvents encodeBytesSpec encodeBytesSpecX
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget (encode_bytes_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  SendCt2EncoderBytesEnv SendCt2EncoderBytesPostEnv SendCt2EncoderBytesPreEnv
  SendCt2EncoderEnv SendCt2EncoderPlacedOkX SendCt2EncoderPlacedOkXOfEnv
  SendCt2EncoderPlacedOkXOfPrePostEnv SendCt2EncoderPostEnv SendCt2EncoderPreEnv
  sendCt2EncoderBytesEnv_nonempty sendCt2EncoderBytesPreEnv_nonempty
  sendCt2EncoderConcatEvents sendCt2EncoderEnv_nonempty sendCt2EncoderPreEnv_nonempty
  sendCt2EncoderSpec sendCt2EncoderSpecOfEnv sendCt2EncoderSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlacedBudget (
  sepWP_call_frozen_noPanic sepWPp_call_frozen_noPanic sepWPp_call_noPanic sepWPp_exists_left
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux (
  SendCt2EncoderExactEnv call_memcpy_bytes_budget call_noAllocShim_budget
  call_rustAllocNoOom_budget encodeBytesSpecX_cl_of_encodeBytesSpec_cl
  freeOnlyEvs_sendCt2FreeEvs hookSat_sessionMemcpyBudget_of_region
  hookSat_sessionShimBudget_of_noAllocShim sendCt2Cap1 sendCt2Cap2
  sendCt2EncoderEvents sendCt2EncoderExactEnv_nonempty sendCt2FreeEvs
  sendCt2InitEvs sendCt2MacEvs stepEvents_sendCt2EncoderEvents
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux2 (
  send_ct2_encoder_finish_placed_budget send_ct2_encoder_mac_placed_budget
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  sp_sub_80_sub_432 sp_sub_512_add_432
  sp_sub_512_add_8 sp_sub_512_add_16 sp_sub_512_add_24 sp_sub_512_add_32
  sp_sub_504_add_8 sp_sub_504_add_16 sp_sub_496_add_8
  sp_sub_80_add_8 sp_sub_80_add_16 sp_sub_80_add_24 sp_sub_80_add_32
  sp_sub_80_add_40 sp_sub_80_add_48 sp_sub_80_add_56 sp_sub_80_add_64
  sp_sub_80_add_72 sp_sub_80_add_80

/-! ## 1. Re-Exports & Exact Prefix/Post Envelope Inclusion Lemmas -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  sendCt2EncoderConcatEvents SendCt2EncoderBytesPreEnv SendCt2EncoderBytesPostEnv
  SendCt2EncoderBytesEnv sendCt2EncoderBytesPreEnv_nonempty
)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  sendCt2EncoderBytesEnv_nonempty SendCt2EncoderPreEnv SendCt2EncoderPostEnv
  SendCt2EncoderEnv sendCt2EncoderPreEnv_nonempty
)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  sendCt2EncoderEnv_nonempty sendCt2EncoderSpecOfPrePostEnv
  sendCt2EncoderSpecOfEnv sendCt2EncoderSpec
)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  SendCt2EncoderPlacedOkXOfPrePostEnv SendCt2EncoderPlacedOkXOfEnv SendCt2EncoderPlacedOkX
)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux (
  sendCt2InitEvs sendCt2Cap1 sendCt2MacEvs sendCt2Cap2 sendCt2FreeEvs
)

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux (
  sendCt2EncoderEvents SendCt2EncoderExactEnv sendCt2EncoderExactEnv_nonempty
)

/-- Exact allocation-phase prefix event trace of `spqr::v1::chunked::send_ct::send_ct2_encoder`
    (Block `382`), prior to the trailing `Vec<u8>` buffer drop (`sendCt2FreeEvs`). -/
def sendCt2EncoderAllocPrefixEvents (ct2 mac : Bytes) : List AllocEvent :=
  (sendCt2InitEvs ct2 ++ sendCt2MacEvs ct2 mac) ++
    encodeBytesAllocEvents (ct2.length + mac.length)

/-- `sendCt2InitEvs ct2 ++ sendCt2MacEvs ct2 mac` equals `Batch2DefsPlacedBudget`'s length-indexed
    `sendCt2EncoderConcatEvents ct2.length mac.length`. -/
theorem sendCt2InitEvs_append_macEvs_eq_concatEvents (ct2 mac : Bytes) :
    sendCt2InitEvs ct2 ++ sendCt2MacEvs ct2 mac =
      sendCt2EncoderConcatEvents ct2.length mac.length := by
  unfold sendCt2InitEvs sendCt2MacEvs sendCt2Cap1 sendCt2EncoderConcatEvents
  by_cases hct2 : ct2 = [] <;> by_cases hmac : mac = []
  · subst hct2; subst hmac; rfl
  · subst hct2
    have hm0 : mac.length ≠ 0 := mt List.length_eq_zero_iff.mp hmac
    simp only [hmac, hm0, List.length_nil, ↓reduceIte, List.nil_append]
  · subst hmac
    have hc0 : ct2.length ≠ 0 := mt List.length_eq_zero_iff.mp hct2
    simp only [hct2, hc0, List.length_nil, ↓reduceIte, List.append_nil]
  · have hc0 : ct2.length ≠ 0 := mt List.length_eq_zero_iff.mp hct2
    have hm0 : mac.length ≠ 0 := mt List.length_eq_zero_iff.mp hmac
    simp only [hct2, hmac, hc0, hm0, ↓reduceIte]

/-- Decomposition of the full `sendCt2EncoderEvents` trace into `sendCt2EncoderAllocPrefixEvents`
    followed by `sendCt2FreeEvs`. -/
theorem sendCt2EncoderEvents_eq_prefix_append_free (ct2 mac : Bytes) :
    sendCt2EncoderEvents ct2 mac =
      sendCt2EncoderAllocPrefixEvents ct2 mac ++ sendCt2FreeEvs (sendCt2Cap2 ct2 mac) := by
  unfold sendCt2EncoderEvents sendCt2EncoderAllocPrefixEvents
  exact (List.append_assoc _ _ _).symm

/-- `sendCt2EncoderAllocPrefixEvents` inhabits `Batch2DefsPlacedBudget.SendCt2EncoderPreEnv`. -/
theorem sendCt2EncoderAllocPrefixEvents_in_preEnv (x : SendCt2EncoderGhost) :
    SendCt2EncoderPreEnv x (sendCt2EncoderAllocPrefixEvents x.ct2 x.mac) := by
  unfold SendCt2EncoderPreEnv SendCt2EncoderBytesPreEnv sendCt2EncoderAllocPrefixEvents
  exact SeqEnv.append (sendCt2InitEvs_append_macEvs_eq_concatEvents x.ct2 x.mac) rfl

/-- `sendCt2EncoderEvents` inhabits `Batch2DefsPlacedBudget.SendCt2EncoderPostEnv`. -/
theorem sendCt2EncoderEvents_in_postEnv (x : SendCt2EncoderGhost) :
    SendCt2EncoderPostEnv x (sendCt2EncoderEvents x.ct2 x.mac) := by
  rw [sendCt2EncoderEvents_eq_prefix_append_free]
  exact SeqEnv.append (sendCt2EncoderAllocPrefixEvents_in_preEnv x)
    (freeOnlyEvs_sendCt2FreeEvs (sendCt2Cap2 x.ct2 x.mac))

/-- Split `FitsEvents M lim st (sendCt2EncoderAllocPrefixEvents ct2 mac)` into sequential
    `FitsEvents` obligations for initial allocation, MAC reservation, and `encode_bytes`,
    with zero `FitsEvents` requirement on the trailing deallocation. -/
theorem fitsEvents_sendCt2EncoderAllocPrefixEvents_split {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {ct2 mac : Bytes}
    (h : FitsEvents M lim st (sendCt2EncoderAllocPrefixEvents ct2 mac)) :
    let st1 := M.stepEvents (sendCt2InitEvs ct2) st
    let st2 := M.stepEvents (sendCt2MacEvs ct2 mac) st1
    FitsEvents M lim st (sendCt2InitEvs ct2) ∧
    FitsEvents M lim st1 (sendCt2MacEvs ct2 mac) ∧
    FitsEvents M lim st2 (encodeBytesAllocEvents (ct2.length + mac.length)) := by
  unfold sendCt2EncoderAllocPrefixEvents at h
  rcases (fitsEvents_append M lim _ _ st).mp h with ⟨h12, h3⟩
  rcases (fitsEvents_append M lim _ _ st).mp h12 with ⟨h1, h2⟩
  rw [M.stepEvents_append] at h3
  exact ⟨h1, h2, h3⟩

/-! ## 2. Relocatable `[LibsignalPlacement]` Contracts for Block `382` -/

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable `spqr::v1::chunked::send_ct::send_ct2_encoder`
    (Block `382`, `85` instructions) given `withLsCodeLoaded` contracts for `do_reserve_7`
    (Block `320`) and `encode_bytes` (Block `417`). -/
theorem send_ct2_encoder_placed_cl_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {PreEnv PostEnv : SendCt2EncoderGhost → List AllocEvent → Prop}
    (hPre : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 →
      PreEnv x (sendCt2EncoderAllocPrefixEvents x.ct2 x.mac))
    (hPost : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 →
      PostEnv x (sendCt2EncoderEvents x.ct2 x.mac))
    (hdr7 : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)))
    (henc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkXOfPrePostEnv M A lim PreEnv PostEnv ext := by
  unfold SendCt2EncoderPlacedOkXOfPrePostEnv
  have hshim : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
    spqr_hook_ok_of_mem (sym := spqrRustNoAllocShimSym) hshim_sat
  have halloc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
    spqr_hook_ok_of_mem (sym := spqrRustAllocSym) halloc_sat
  have halloc_nooom := subroutine_ok_allocNoOom_of_budget halloc
  have hdealloc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc_sat
  have hmemcpy : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec :=
    spqr_hook_ok_of_mem (sym := "memcpy") hmemcpy_sat
  have henc_call : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpecX A lim)) :=
    encodeBytesSpecX_cl_of_encodeBytesSpec_cl henc
  apply subroutine_ok_withLsCodeLoaded_of_left
  simp only [lsProg_382] at hdr7 henc_call hshim halloc halloc_nooom hdealloc hmemcpy ⊢
  unfold sendCt2EncoderSpecOfPrePostEnv
  conv => arg 3; arg 1; ext x s; simp only [stackAt_sendCt2Encoder_split]
  cells_unfold
  wpp_init x s0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  rcases x with ⟨⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩, st0⟩
  dsimp only [BitVec.ofNat_eq_ofNat] at *
  obtain ⟨henc_res, hlen_le⟩ := encodeBytesResult_of_expectEncodeBytes_ok
    ‹send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc›
  have hPre_x : PreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩
      (sendCt2EncoderAllocPrefixEvents ct2 mac) :=
    hPre ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ hlen_le
  have hPost_x : PostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩
      (sendCt2EncoderEvents ct2 mac) :=
    hPost ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ hlen_le
  have hFit : FitsEnv M lim st0 (PreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩) := by assumption
  have hfit_all : FitsEvents M lim st0 (sendCt2EncoderAllocPrefixEvents ct2 mac) := hFit _ hPre_x
  obtain ⟨hfit_init, hfit_mac, hfit_enc⟩ :=
    fitsEvents_sendCt2EncoderAllocPrefixEvents_split hfit_all
  have hst_all := (stepEvents_sendCt2EncoderEvents M ct2 mac st0).symm
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := ‹(s0.sp &&& 15#64 == 0#64) = true›
  have hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 512#64 hsp0_align (by decide)
  have hlen_app : (ct2 ++ mac).length = ct2.length + mac.length := List.length_append
  by_cases hct2_nil : ct2 = []
  · subst hct2_nil
    have hct2_z : (BitVec.ofNat 64 ([] : Bytes).length == 0#64) = true := rfl
    have henc_nil :
        emp ⊢ ((1#64 : BitVec 64) ↦ₛ ([] : Bytes)) ∗ vecU8Tail A.repAlloc 0#64 1#64 [] := by
      unfold vecU8Tail
      simp [pointsToBytes_nil]
      exact Entails.refl emp
    by_cases hmac_nil : mac = []
    · subst hmac_nil
      have hmac_z : (BitVec.ofNat 64 ([] : Bytes).length == 0#64) = true := rfl
      apply of_sepWP_lscl hcl0 (mid := (blkPl_382).base + 100#64)
      wp_steps_sync_pool ((blkPl_382).base + 100#64)
      refine SepWP.fold (Entails.trans (Entails.of_eq (emp_sepConj _).symm)
        (sepConj_mono_left henc_nil)) (sepConj_emp _).symm ?_
      rw [sepConj_emp]
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl1
      exact send_ct2_encoder_finish_placed_budget henc_call hmemcpy hdealloc
        outA ct2Ptr macPtr [] [] outEnc
        0#64 1#64 0#64 _ st0 st0 PostEnv hPost_x
        henc_res hlen_le (by decide) (by decide)
        (by simpa [sendCt2InitEvs, sendCt2MacEvs] using hfit_enc)
        (by simpa [sendCt2InitEvs, sendCt2MacEvs, sendCt2Cap2, sendCt2Cap1] using hst_all)
        hcl1 hsp0_align hfsp_align
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [List.append_nil]; sep_focus)
        (by dsimp only [Reg.lr, Reg.x30] at *; assumption)
    · have hmac_pos : 0 < mac.length := List.length_pos_iff.mpr hmac_nil
      have hmac_ne0 : BitVec.ofNat 64 mac.length ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        change mac.length = 0 at this; omega
      have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = false := beq_false_of_ne hmac_ne0
      apply of_sepWP_lscl hcl0 (mid := (blkPl_382).base + 208#64)
      wp_steps_sync_pool ((blkPl_382).base + 208#64)
      refine SepWP.fold (Entails.trans (Entails.of_eq (emp_sepConj _).symm)
        (sepConj_mono_left henc_nil)) (sepConj_emp _).symm ?_
      rw [sepConj_emp]
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl1
      exact send_ct2_encoder_mac_placed_budget hdr7 henc_call hmemcpy hdealloc
        outA ct2Ptr macPtr [] mac outEnc
        0#64 1#64 _ st0 st0 PostEnv hPost_x
        henc_res hlen_le hmac_nil rfl (by decide)
        (by simpa [sendCt2InitEvs] using hfit_mac)
        (by simpa [sendCt2InitEvs] using hfit_enc)
        (by simpa [sendCt2InitEvs, sendCt2Cap2, sendCt2Cap1, hmac_nil] using hst_all)
        hcl1 hsp0_align hfsp_align
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x23, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by sep_focus)
        (by dsimp only [Reg.lr, Reg.x30] at *; assumption)
  · have hct2_pos : 0 < ct2.length := List.length_pos_iff.mpr hct2_nil
    have hct2_toNat : (BitVec.ofNat 64 ct2.length).toNat = ct2.length := Nat.mod_eq_of_lt (by omega)
    have hct2_ne0 : BitVec.ofNat 64 ct2.length ≠ 0#64 := by
      intro h0; have := congrArg BitVec.toNat h0; rw [hct2_toNat] at this
      change ct2.length = 0 at this; omega
    have hct2_z : (BitVec.ofNat 64 ct2.length == 0#64) = false := beq_false_of_ne hct2_ne0
    have hrlay_ct2 : RustLayoutOk ct2.length 1 := ⟨⟨hct2_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
    have hinit_eq : sendCt2InitEvs ct2 = rustAllocEvents ct2.length 1 := by
      simp [sendCt2InitEvs, hct2_nil]
    have hfit_init' : FitsEvents M lim st0 (rustAllocEvents ct2.length 1) := by
      rwa [← hinit_eq]
    apply of_sepWP_lscl hcl0 (mid := (blkPl_382).base + 68#64)
    wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
    refine call_noAllocShim_budget hshim st0
      (s0 := s0) (ret_pc := _) (target_pc := (blkPl_382).base + 68#64)
      (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, *]) hfsp_align
      rfl (by simp only [arm64_norm, *])
      (by sep_focus)
      (fun sf0 hpc0 hrun0 hsp0 hcs0 htr0 => ?_)
    simp only [Reg.lr, arm64_norm] at hpc0
    rcases hcs0 with ⟨hx19_0, hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hfp_0, hvregs_0⟩
    simp only [arm64_norm, *] at hx19_0 hx20_0 hx21_0 hx22_0 hx23_0 hx24_0 hx25_0 hx26_0 hx27_0 hx28_0 hfp_0 hvregs_0
    wp_steps_sync_pool (lsρ spqrRustAllocSym)
    refine SepWP.fold (stackAt_encodeBytesX_to_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
    refine call_rustAllocNoOom_budget halloc_nooom ct2.length 1 st0 hrlay_ct2 hfit_init'
      (s0 := s0) (ret_pc := (blkPl_382).base + 68#64) (target_pc := (blkPl_382).base + 68#64)
      (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hfsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, hct2_toNat, *])
      (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hoom => ?_)
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    wp_conv_pre => rw [← hinit_eq]
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hcl1
    dsimp only [Reg.x0] at hoom
    have hoom_false : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
    have hjoin_ct2 :
        A.live (sf1.readReg64 (Reg.gpr 0#5)) ct2.length 1 ∗
          (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ ct2) ⊢
        (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ ct2) ∗
          vecU8Tail A.repAlloc (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) ct2 := by
      unfold vecU8Tail
      dsimp only [RustCliAllocBudget.repAlloc]
      simp only [hct2_z, Bool.false_eq_true, ↓reduceIte, hct2_toNat, Nat.sub_self,
        ProofLib.memRegion_zero, sepConj_emp]
      exact Entails.of_eq (sepConj_comm _ _)
    let st1 := M.stepEvents (sendCt2InitEvs ct2) st0
    by_cases hmac_nil : mac = []
    · have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = true := by subst hmac_nil; rfl
      apply of_sepWP_lscl hcl1 (mid := (blkPl_382).base + 100#64)
      refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ "memcpy")
      refine call_memcpy_bytes_budget hmemcpy
        (sf1.readReg64 (Reg.gpr 0#5)) ct2Ptr ct2 st1
        (s0 := s0) (ret_pc := _) (target_pc := (blkPl_382).base + 100#64)
        (sp_call := s0.sp - 512#64)
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *]) hfsp_align
        rfl (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *])
        (by simp only [Reg.x1, arm64_norm, *])
        (by simp only [Reg.x2, arm64_norm, hct2_toNat, *])
        (by sep_focus)
        (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
      simp only [Reg.lr, arm64_norm] at hpc2
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      wp_steps_sync_pool ((blkPl_382).base + 100#64)
      subst hmac_nil
      refine SepWP.fold hjoin_ct2 (by sep_focus) ?_
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro hcl2
      exact send_ct2_encoder_finish_placed_budget henc_call hmemcpy hdealloc
        outA ct2Ptr macPtr ct2 [] outEnc
        (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) (BitVec.ofNat 64 ct2.length) _
        st0 st1 PostEnv hPost_x
        henc_res hlen_le (by rw [List.append_nil, hct2_toNat]) (by rw [hct2_toNat]; omega)
        (by simpa [sendCt2MacEvs] using hfit_enc)
        (by simpa [sendCt2MacEvs, sendCt2Cap2, sendCt2Cap1, hct2_nil, hct2_toNat] using hst_all)
        hcl2 hsp0_align hfsp_align
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [List.append_nil]; sep_focus)
        (by dsimp only [Reg.lr, Reg.x30] at *; assumption)
    · have hmac_pos : 0 < mac.length := List.length_pos_iff.mpr hmac_nil
      have hmac_ne0 : BitVec.ofNat 64 mac.length ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        change mac.length = 0 at this; omega
      have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = false := beq_false_of_ne hmac_ne0
      apply of_sepWP_lscl hcl1 (mid := (blkPl_382).base + 208#64)
      refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
      wp_steps_sync_pool (lsρ "memcpy")
      refine call_memcpy_bytes_budget hmemcpy
        (sf1.readReg64 (Reg.gpr 0#5)) ct2Ptr ct2 st1
        (s0 := s0) (ret_pc := _) (target_pc := (blkPl_382).base + 208#64)
        (sp_call := s0.sp - 512#64)
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *]) hfsp_align
        rfl (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *])
        (by simp only [Reg.x1, arm64_norm, *])
        (by simp only [Reg.x2, arm64_norm, hct2_toNat, *])
        (by sep_focus)
        (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
      simp only [Reg.lr, arm64_norm] at hpc2
      rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      wp_steps_sync_pool ((blkPl_382).base + 208#64)
      refine SepWP.fold hjoin_ct2 (by sep_focus) ?_
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro hcl2
      exact send_ct2_encoder_mac_placed_budget hdr7 henc_call hmemcpy hdealloc
        outA ct2Ptr macPtr ct2 mac outEnc
        (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) _
        st0 st1 PostEnv hPost_x
        henc_res hlen_le hmac_nil hct2_toNat hoom
        hfit_mac hfit_enc
        (by simpa [sendCt2Cap2, sendCt2Cap1, hmac_nil, hct2_nil, hct2_toNat] using hst_all)
        hcl2 hsp0_align hfsp_align
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x23, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by sep_focus)
        (by dsimp only [Reg.lr, Reg.x30] at *; assumption)

/-- Canonical two-envelope (`SendCt2EncoderPreEnv` / `SendCt2EncoderPostEnv`) relocatable
    `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`) given `withLsCodeLoaded`
    contracts for `do_reserve_7` (Block `320`) and `encode_bytes` (Block `417`). -/
theorem send_ct2_encoder_placed_cl_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdr7 : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)))
    (henc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkX M A lim ext :=
  send_ct2_encoder_placed_cl_ext_ofPrePostEnv
    (fun x _ => sendCt2EncoderAllocPrefixEvents_in_preEnv x)
    (fun x _ => sendCt2EncoderEvents_in_postEnv x)
    hdr7 henc hshim_sat halloc_sat hdealloc_sat hmemcpy_sat

/-- Single-envelope (`Env`) relocatable `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`)
    for `Batch2DefsPlacedBudget.SendCt2EncoderPlacedOkXOfEnv`. -/
theorem send_ct2_encoder_placed_cl_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop}
    (hEnv : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 → Env x (sendCt2EncoderEvents x.ct2 x.mac))
    (hdr7 : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)))
    (henc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkXOfEnv M A lim Env ext :=
  SendCt2EncoderBudgetAux2.send_ct2_encoder_placed_cl_ext_ofEnv
    hEnv hdr7 henc hshim_sat halloc_sat hdealloc_sat hmemcpy_sat

theorem send_ct2_encoder_placed_cl_ext_exact [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdr7 : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec M A lim)))
    (henc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkXOfEnv M A lim SendCt2EncoderExactEnv ext :=
  send_ct2_encoder_placed_cl_ext_ofEnv (fun _ _ => rfl)
    hdr7 henc hshim_sat halloc_sat hdealloc_sat hmemcpy_sat

/-- Two-envelope (`PreEnv` / `PostEnv`) closed `[LibsignalPlacement]` contract for
    `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`), discharging both
    `do_reserve_and_handle [local#7]` (Block `320`) and `<PolyEncoder as Encoder>::encode_bytes`
    (Block `417`) from `HookSat` hypotheses. -/
theorem send_ct2_encoder_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {PreEnv PostEnv : SendCt2EncoderGhost → List AllocEvent → Prop}
    (hPre : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 →
      PreEnv x (sendCt2EncoderAllocPrefixEvents x.ct2 x.mac))
    (hPost : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 →
      PostEnv x (sendCt2EncoderEvents x.ct2 x.mac))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkXOfPrePostEnv M A lim PreEnv PostEnv ext :=
  send_ct2_encoder_placed_cl_ext_ofPrePostEnv hPre hPost
    (ls_subroutine_ok_of_block (i := 382) (j := 320)
      (do_reserve_7_raw_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (i := 382) (j := 417)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (encode_bytes_placed_ok_ext
          (hookSat_sessionShimBudget_of_noAllocShim hshim)
          halloc
          (hookSat_sessionMemcpyBudget_of_region hmemcpy))))
    hshim halloc hdealloc hmemcpy

/-- Canonical closed `[LibsignalPlacement]` contract for
    `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`), proving
    `Batch2DefsPlacedBudget.SendCt2EncoderPlacedOkX M A lim ext` from `HookSat` hypotheses. -/
theorem send_ct2_encoder_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkX M A lim ext :=
  send_ct2_encoder_placed_ok_x_ofPrePostEnv
    (fun x _ => sendCt2EncoderAllocPrefixEvents_in_preEnv x)
    (fun x _ => sendCt2EncoderEvents_in_postEnv x)
    h_panic hshim halloc hrealloc hdealloc hmemcpy

/-- Single-envelope (`Env`) closed `[LibsignalPlacement]` contract for
    `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`). -/
theorem send_ct2_encoder_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop}
    (hEnv : ∀ x, (x.ct2 ++ x.mac).length ≤ 1048576 → Env x (sendCt2EncoderEvents x.ct2 x.mac))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec) :
    SendCt2EncoderPlacedOkXOfEnv M A lim Env ext :=
  SendCt2EncoderBudgetAux2.send_ct2_encoder_placed_ok_x_ofEnv
    hEnv h_panic hshim halloc hrealloc hdealloc hmemcpy

/-! ## 3. Framed Call Rules for `sendCt2EncoderSpecOfPrePostEnv` & `sendCt2EncoderSpec` -/

/-- Two-envelope (`PreEnv` / `PostEnv`) framed call rule for plain
    `sendCt2EncoderSpecOfPrePostEnv M A lim PreEnv PostEnv` (Block `382`). -/
theorem call_sendCt2Encoder_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : SendCt2EncoderGhost → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sendCt2EncoderSpecOfPrePostEnv M A lim PreEnv PostEnv))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (PreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) := by
  apply SepWP.done hpc hrun
  refine sepWPp_call_noPanic hcall (x := (⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [sendCt2EncoderSpecOfPrePostEnv]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc, hfit,
      by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩, hm⟩
  · dsimp only [sendCt2EncoderSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply sepWPp_exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hevs⟩ => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        (polyEncoderAt A.repAlloc outA enc ∗
          ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗
            (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hevs

/-- Single-envelope (`Env`) framed call rule for plain `sendCt2EncoderSpecOfEnv M A lim Env`. -/
theorem call_sendCt2Encoder_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sendCt2EncoderSpecOfEnv M A lim Env))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2Encoder_ofPrePostEnv hcall outA ct2Ptr macPtr ct2 mac enc st_b hct2_ptr hmac_ptr henc
    hfit hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4 hsplit hnext hlr_ls

theorem call_sendCt2Encoder [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (sendCt2EncoderSpec M A lim))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (SendCt2EncoderPreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SendCt2EncoderPostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P (fun sm Pm => SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2Encoder_ofPrePostEnv hcall outA ct2Ptr macPtr ct2 mac enc st_b hct2_ptr hmac_ptr henc
    hfit hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4 hsplit hnext hlr_ls

/-- Two-envelope (`PreEnv` / `PostEnv`) framed relocatable call rule for
    `withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim PreEnv PostEnv)` (Block `382`). -/
theorem call_sendCt2Encoder_cl_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : SendCt2EncoderGhost → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim PreEnv PostEnv)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (PreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
        post Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc, hfit,
      by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩, hm⟩
  · dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply sepWPp_exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hevs⟩ => ?_
    have hassoc :
        (polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        (polyEncoderAt A.repAlloc outA enc ∗
          ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗
            (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hevs hcl_sf

/-- Single-envelope (`Env`) framed relocatable call rule for
    `withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfEnv M A lim Env)` (Block `382`). -/
theorem call_sendCt2Encoder_cl_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfEnv M A lim Env)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
        post Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2Encoder_cl_ofPrePostEnv hcall outA ct2Ptr macPtr ct2 mac enc st_b hct2_ptr hmac_ptr
    henc hfit hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4 hsplit hnext hlr_ls

theorem call_sendCt2Encoder_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (SendCt2EncoderPreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SendCt2EncoderPostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
        post Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Qp) :=
  call_sendCt2Encoder_cl_ofPrePostEnv hcall outA ct2Ptr macPtr ct2 mac enc st_b hct2_ptr hmac_ptr
    henc hfit hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4 hsplit hnext hlr_ls

/-- Pure-`SepWP` two-envelope (`PreEnv` / `PostEnv`) framed relocatable call rule for Block `382`. -/
theorem call_sendCt2Encoder_cl_sepWP_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : SendCt2EncoderGhost → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim PreEnv PostEnv)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (PreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWP_call_frozen_noPanic (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩, st_b)) (F := Frame)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv]
    rw [hsp, sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc, hfit,
      by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩, hm⟩
  · dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_left; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr, hevs⟩ => ?_
    have hassoc :
        (polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame =
        (polyEncoderAt A.repAlloc outA enc ∗
          ((ct2Ptr ↦ₛ ct2) ∗ ((macPtr ↦ₛ mac) ∗
            (A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack)))) ∗ Frame := by
      sep_ac_rfl
    rw [← hassoc]
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hevs hcl_sf

/-- Single-envelope (`Env`) pure-`SepWP` framed relocatable call rule for Block `382`. -/
theorem call_sendCt2Encoder_cl_sepWP_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SendCt2EncoderGhost → List AllocEvent → Prop} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfEnv M A lim Env)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      Env ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) :=
  call_sendCt2Encoder_cl_sepWP_ofPrePostEnv hcall outA ct2Ptr macPtr ct2 mac enc st_b hct2_ptr
    hmac_ptr henc hfit hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4 hsplit hnext hlr_ls

/-- Canonical `sendCt2EncoderSpec M A lim` (`SendCt2EncoderPreEnv` / `SendCt2EncoderPostEnv`)
    pure-`SepWP` framed relocatable call rule for Block `382`. -/
theorem call_sendCt2Encoder_cl_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder) (st_b : M.σ)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfit : FitsEnv M lim st_b (SendCt2EncoderPreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = ct2Ptr) (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_b s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SendCt2EncoderPostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog entry s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) :=
  call_sendCt2Encoder_cl_sepWP_ofPrePostEnv hcall outA ct2Ptr macPtr ct2 mac enc st_b hct2_ptr
    hmac_ptr henc hfit hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4 hsplit hnext hlr_ls

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderPlacedBudget
