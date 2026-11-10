/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Phase23Placed
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Placed Handshake `bytes::merge [local#5]` Verification

Verifies `[LibsignalPlacement]` `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#5]`
(Block `514`, `888` B) against the unified `bytesMerge3RawSpecBoth` contract and specializes to
`bytesMerge3RawSpec`, `bytesMerge3ProtoRawSpec`, and Block-`518` caller contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  bytesMerge3PlacedSpec
  bytesMerge3ProtoPlacedSpec
  BytesMerge6PlacedOkExt
  BytesMerge6ProtoPlacedOkExt
)

/-- Unified outer (`bytesMerge3Stack`) specification supporting both `BytesMergeCapOk` (`< 2 ^ 63`)
and unconstrained-capacity `< 2 ^ 62` (`W`). -/
def bytesMerge3RawSpecBoth (A : RustAlloc) : Spec BytesMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      (BytesMergeCapOk x.valCap x.bs.length ∨ x.bs.length < 2 ^ 62)⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMerge3Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk x.valCap x.bs.length → BytesMergeCapOk cap' rest.length⌝ ∗
              vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev MergePost3Both (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpecBoth A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanic3Both (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpecBoth A).onPanic x s0 sf ∗ R)

theorem SepWPp.to_subroutineOutcome3Both_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P (MergePost3Both A x s0 R) (MergePanic3Both A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A)) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem SepWPp.lift_merge3Both {prog : Program} {A : RustAlloc}
    {x : BytesMergeGhost} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergePostXBoth A x s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))
      (MergePanicXBoth A x s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))) :
    SepWPp prog (s0.readReg64 .lr) s (memRegion (s0.sp - 33120#64) 48 ∗ P)
      (MergePost3Both A x s0 R) (MergePanic3Both A x s0 R) := by
  intro F hm hL
  have hm' : s.mem ⊨ P ∗ (memRegion (s0.sp - 33120#64) 48 ∗ F) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h (memRegion (s0.sp - 33120#64) 48 ∗ F) hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, memRegion (s0.sp - 33120#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf, ?_, hsp, hcs⟩⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 33120#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmr
    have hp := hpost hmr'
    dsimp only [bytesMergeRawSpecXBoth, bytesMerge3RawSpecBoth] at hp ⊢
    rw [stackAt_bytesMerge3_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hp
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, memRegion (s0.sp - 33120#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf, ?_⟩)⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 33120#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmr
    have hp := hpanic hmr'
    dsimp only [bytesMergeRawSpecXBoth, bytesMerge3RawSpecBoth] at hp ⊢
    rw [← sepConj_assoc] at hp
    exact allowPanic_frame id hp
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## 1. Phase 1 (`+0x000..+0x074`) and `bytes_merge_6_both_placed_ok_of_contracts` (Block `514`) -/

set_option maxHeartbeats 600000 in
/-- Relocatable `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
(Block `514`) meets `withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A)` under `[LibsignalPlacement]`. -/
theorem bytes_merge_6_both_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpySpec)
    (hshim : subroutine_ok (lsProg_514 H) (lsρ lsRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_514 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpecWithStack A extHookStack)))
    (hpanic : (lsProg_514 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hDecodeVarint5 : subroutine_ok (lsProg_514 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A)))
    (hBytesFromVec : subroutine_ok (lsProg_514 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_514 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX A tmpPtr v v.length))) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A)) := by
  intro x R s0 hpc hrun hpre hsp_align hL
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMerge3RawSpecBoth, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcapInv⟩, hm⟩ := hpre
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue6_err_0x07c_placed _ A H x s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R) hmerge
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue6_decodeErrorFrom_0x074_placed _ A H hdef x s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R) w hw hmerge
  have h094_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0))
      (hle : len.toNat ≤ rest0.length) =>
    @phase2_6_from_0x094_placed _ A H hmc hshim halloc hpanic hBytesFromVec hReserve
      hVtableDrop x s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R) len rest0 hwt hvar hle hbs_len hcapInv
  clear hBytesFromVec hReserve hVtableDrop
  apply SepWPp.to_subroutineOutcome3Both_placed hsp_align hm hL
  rw [stackAt_bytesMerge3_entry s0.sp]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
      stackAt (s0.sp - 224#64) decodeVarint2StackX ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0, hwt]
      decide
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 515)
    wp_steps
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.bm_call_frame_lscl
      (x := ({ bufRef := x.bufRef, slot := x.slot, ptr := x.ptr, bs := x.bs } : DecodeVarintSlowGhost))
      (T := (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarint2StackX)
      hDecodeVarint5 hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp_align]) rfl
      (by simp (config := { decide := true }) only [decodeVarint2SpecX, arm64_norm])
      hbs_len
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => by
        simp only [bytesMerge3RawSpecBoth, withLsCl, decodeVarint2SpecX,
          State.trace_setPC, State.trace_writeReg64, allocFailedIn] at hm ⊢
        exact allowPanic_frame id hm) ?_
    intro sf_dv hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, hvregsf⟩ := hcsf
    simp (config := { decide := true }) only [arm64_norm, hx1, hx2] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvregsf
    simp (config := { decide := true }) only [decodeVarint2SpecX, wp_norm, arm64_norm]
    rw [stackAt_varint2_to_slice s0.sp]
    rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
    · dsimp only
      have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.readReg64 .x0 = 1#64⌝ ∗ ⌜sf_dv.trace = s0.trace⌝ ∗ ⌜sf_dv.readReg64 .x1 ≠ 0#64⌝ ∗
          (memRegion (s0.sp - 33120#64) 48 ∗
            decodeErrorAtStackLen A (sf_dv.readReg64 .x1) 0 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          ac_rfl)) ?_
      refine SepWPp.pure_elim fun hx0_sf => ?_
      refine SepWPp.pure_elim fun htr => ?_
      refine SepWPp.pure_elim fun hx1_sf => ?_
      apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_514).base + 124#64)
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hcl2 hro2
      exact SepWPp.lift_merge3Both (herr_exit hmerge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact hx1_sf)
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self]))
    · dsimp only
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
      have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine SepWPp.weaken_pre (P' :=
        ⌜sf_dv.readReg64 .x0 = 0#64 ∧ sf_dv.readReg64 .x1 = len⌝ ∗ ⌜sf_dv.trace = s0.trace⌝ ∗
          (memRegion (s0.sp - 33120#64) 48 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 216#64) 48 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
        (Entails.of_eq (by
          dsimp only [savedRegsStack, Reg.x0, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x29, Reg.x30]
          ac_rfl)) ?_
      refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
      refine SepWPp.pure_elim fun htr => ?_
      dsimp only [sliceCursorAfter]
      apply SepWPp.bm_of_sepWP_lscl hclf hrof
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then (blkPl_514).base + 148#64 else (blkPl_514).base + 80#64)
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hcl2 hro2
      by_cases hule : len.ule (BitVec.ofNat 64 rest0.length) = false
      · simp only [hule, Bool.false_eq_true, ↓reduceIte] at hcl2 hro2 ⊢
        have hlt : rest0.length < len.toNat := by simp [BitVec.ule, hrest0_toNat] at hule; omega
        have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_lengthDelimited_underflow hwt hvar hlt
        refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
          (memRegion (s0.sp - 33120#64) 48 ∗
            vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
            (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
            stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
            memRegion (s0.sp - 224#64) 8 ∗
            memRegion (s0.sp - 168#64) 104 ∗
            savedRegsStack s0.sp s0))
          (Entails.of_eq (by ac_rfl)) ?_
        refine SepWPp.unfold_memRegion_216 fun w216 => ?_
        apply SepWPp.bm_of_sepWP_lscl hcl2 hro2 (mid := (blkPl_514).base + 116#64)
        wp_steps
        apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        intro hcl3 hro3
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3Both (hde_exit 0x8000000000000007#64 (by simp [KindNoHeap]) hmerge
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hcl3 hro3))
        exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
      · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
          Bool.eq_true_of_not_eq_false hule
        simp only [hule_eq, ↓reduceIte] at hcl2 hro2 ⊢
        have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3Both (h094_exit len rest0 hwt hvar hle
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hcl2 hro2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f])))
        exact Entails.of_eq (by ac_rfl)
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]
    rw [stackAt_varint2_to_slice s0.sp]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (memRegion (s0.sp - 33120#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_514).base + 116#64)
    wp_steps
    apply SepWP.fold (fold_memRegion_40_bytes (s0.sp - 216#64)
      (BitVec.ofNat 8 x.wt.toNat) 2#8) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3Both (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hcl1 hro1))
    exact Entails.of_eq (by dsimp only [savedRegsStack]; simp (config := { decide := true }) only [arm64_norm]; ac_rfl)

/-! ## 2. Specializations to `bytesMerge3RawSpec` & `bytesMerge3ProtoRawSpec` and Leaf Closure -/

theorem bytes_merge_6_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpySpec)
    (hshim : subroutine_ok (lsProg_514 H) (lsρ lsRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_514 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpecWithStack A extHookStack)))
    (hpanic : (lsProg_514 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hDecodeVarint5 : subroutine_ok (lsProg_514 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A)))
    (hBytesFromVec : subroutine_ok (lsProg_514 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_514 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX A tmpPtr v v.length))) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)) := by
  have hok := bytes_merge_6_both_placed_ok_of_contracts hdef hmc hshim halloc hpanic hDecodeVarint5
    hBytesFromVec hReserve hVtableDrop
  intro x R s0 hpc hrun hpre hal hL
  obtain ⟨hcro, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMerge3RawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcapOk⟩, _⟩ := hpre0
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A)).pre x s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpec, bytesMerge3RawSpecBoth] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by simp only [hw0, hx1, hx2, hbs_len, hcapOk, true_or, and_self])) hpre
  obtain ⟨sf, hs, hout⟩ := hok x R s0 hpc hrun hpre' hal hL
  refine ⟨sf, hs, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecBoth, bytesMerge3RawSpec] at hpost ⊢
    rcases hmb : mergeBytes x.wt x.bs with _ | ⟨v, rest⟩
    · simpa only [hmb] using hpost
    · simp only [hmb, hcapOk, true_implies] at hpost ⊢
      exact hpost
  · exact Or.inr hfail

theorem bytes_merge_6_proto_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdef : subroutine_ok (lsProg_514 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hmc : subroutine_ok (lsProg_514 H) (lsρ "memcpy") framelessMemcpySpec)
    (hshim : subroutine_ok (lsProg_514 H) (lsρ lsRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_514 H) (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpecWithStack A extHookStack)))
    (hpanic : (lsProg_514 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked)
    (hDecodeVarint5 : subroutine_ok (lsProg_514 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A)))
    (hBytesFromVec : subroutine_ok (lsProg_514 H) (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok (lsProg_514 H) (lsmpl.base 517)
      (withLsCl lsmpl (doReserve1VecSpecX A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (lsProg_514 H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX A tmpPtr v v.length))) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A)) := by
  have hok := bytes_merge_6_placed_ok_of_contracts hdef hmc hshim halloc hpanic hDecodeVarint5
    hBytesFromVec hReserve hVtableDrop
  intro x R s0 hpc hrun hpre hal hL
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)).pre x.toCodec s0 ∗ R := by
    simpa only [withLsCodeRoLoaded, bytesMerge3ProtoRawSpec, bytesMerge3RawSpec,
      BytesMergeProtoGhost.toCodec, protoWireTypeToCodec_toNat] using hpre
  obtain ⟨sf, hs, hout⟩ := hok x.toCodec R s0 hpc hrun hpre' hal hL
  refine ⟨sf, hs, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, bytesMerge3ProtoRawSpec, bytesMerge3RawSpec,
      BytesMergeProtoGhost.toCodec] at hpost ⊢
    rw [proto_mergeBytes_toOption]
    exact hpost
  · exact Or.inr hfail

private theorem bm6_sessionShim_of_noAllocShim {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym noAllocShimSpec) :
    HookSat H sym sessionShimSpec := by
  obtain ⟨f, hf, hsat⟩ := h
  refine ⟨f, hf, ?_⟩
  intro x R s0 hrun hpre hal
  dsimp only [sessionShimSpec] at hpre
  have hpre' : s0.mem ⊨ noAllocShimSpec.pre () s0 ∗ R := by
    dsimp only [noAllocShimSpec]
    simpa only [pure_true, emp_sepConj] using hpre
  obtain ⟨hret, hcc, hpost⟩ := hsat () R s0 hrun hpre' hal
  exact ⟨hret, hcc, hpost⟩

theorem bm6_decodeErrorFrom_placed_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (withLsCodeLoaded lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (decode_error_from_placed_ok_x (bm6_sessionShim_of_noAllocShim hshim) halloc hpanic_alloc)

theorem bm6_decodeVarint5_placed_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_515 H) (blkPl_515).base
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A)) := by
  have hFrom := bm6_decodeErrorFrom_placed_of_hooks hshim halloc hpanic_alloc
  exact decodeVarint5_placed_ok_of_contracts_x hFrom
    (decodeVarintSlowGen_lscl_ok_of_session2
      (decode_varint_slow_placed_ok_with_stack
        (errStack := decodeErrorHookStackX) (by decide)
        (ls_subroutine_ok_cl_of_block
          (callerProg := (blkPC_293).rebase (blkPl_293).base H) hFrom)))

theorem bm6_vtableDrop_placed_of_dealloc [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide)
    (tmpPtr : BitVec 64) (v : List (BitVec 8)) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecX A tmpPtr v v.length)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded
    (bytesVtableDrop_placed_ok_of_drops
      (promotableEvenDrop_placed_ok_of_dealloc (hookStack := extHookStack) (by decide)
        (rustDeallocExternWithStack_of_rustDealloc
          (ls_hook_ok_rustDealloc hdealloc) (by decide) (by decide)))
      (promotableOddDrop_placed_ok_of_dealloc (hookStack := extHookStack) (by decide)
        (rustDeallocExternWithStack_of_rustDealloc
          (ls_hook_ok_rustDealloc hdealloc) (by decide) (by decide)))
      hi tmpPtr v v.length)

theorem bytes_merge_6_both_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A)) :=
  bytes_merge_6_both_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (bm6_decodeErrorFrom_placed_of_hooks hshim halloc hpanic_alloc))
    (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) hmc)
    (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) hshim)
    (subroutine_ok_withLsCl_of_plain
      (rustAllocWithStack_of_rustAlloc
        (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) halloc) (by decide) (by decide)))
    ((ls_externAt?_of_mem (prog := lsProg_514 H) (i := 514) (H := H) (sym := lsHandleErrorSym)).trans hpanic_raw)
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (bm6_decodeVarint5_placed_of_hooks hshim halloc hpanic_alloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_514 H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (do_reserve_10_vec1_placed_ok hpanic_raw hshim halloc hrealloc))
    (bm6_vtableDrop_placed_of_dealloc (callerProg := lsProg_514 H) hdealloc)

theorem bytes_merge_6_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)) :=
  bytes_merge_6_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (bm6_decodeErrorFrom_placed_of_hooks hshim halloc hpanic_alloc))
    (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) hmc)
    (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) hshim)
    (subroutine_ok_withLsCl_of_plain
      (rustAllocWithStack_of_rustAlloc
        (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) halloc) (by decide) (by decide)))
    ((ls_externAt?_of_mem (prog := lsProg_514 H) (i := 514) (H := H) (sym := lsHandleErrorSym)).trans hpanic_raw)
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (bm6_decodeVarint5_placed_of_hooks hshim halloc hpanic_alloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_514 H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (do_reserve_10_vec1_placed_ok hpanic_raw hshim halloc hrealloc))
    (bm6_vtableDrop_placed_of_dealloc (callerProg := lsProg_514 H) hdealloc)

theorem bytes_merge_6_proto_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A)) :=
  bytes_merge_6_proto_placed_ok_of_contracts
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (bm6_decodeErrorFrom_placed_of_hooks hshim halloc hpanic_alloc))
    (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) hmc)
    (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) hshim)
    (subroutine_ok_withLsCl_of_plain
      (rustAllocWithStack_of_rustAlloc
        (ls_hook_ok_of_mem (prog := lsProg_514 H) (i := 514) halloc) (by decide) (by decide)))
    ((ls_externAt?_of_mem (prog := lsProg_514 H) (i := 514) (H := H) (sym := lsHandleErrorSym)).trans hpanic_raw)
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (bm6_decodeVarint5_placed_of_hooks hshim halloc hpanic_alloc))
    (ls_subroutine_ok_cl_of_plain (callerProg := lsProg_514 H)
      (bytesFromVec_placed_ok H))
    (ls_subroutine_ok_cl_of_block (callerProg := lsProg_514 H)
      (do_reserve_10_vec1_placed_ok hpanic_raw hshim halloc hrealloc))
    (bm6_vtableDrop_placed_of_dealloc (callerProg := lsProg_514 H) hdealloc)

/-- Lift a `withLsCodeRoLoaded` contract on `lsProg_514 H` to any caller block program at `lsmpl.base 514`. -/
theorem bytes_merge_6_cro_of_514 [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] {spec : Spec α}
    (hcallee : subroutine_ok (lsProg_514 H) (blkPl_514).base (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514) (withLsCodeRoLoaded lsmpl spec) :=
  keys_ls_subroutine_ok_of_block_cro (callerProg := callerProg) hcallee hi

theorem subroutine_ok_withLsCl_of_cro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hro : ∀ m, LibsignalCodeLoaded lsmpl m → LibsignalRoLoaded lsmpl m) :
    subroutine_ok prog entry (withLsCl lsmpl spec) := by
  intro x R s0 hpc hrun hpre hal hL
  obtain ⟨hcl, hm⟩ := extract_withLsCodeLoaded hpre
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm _ (⌜LibsignalCodeRoLoaded _ _⌝), satisfies_pure_sepConj]
    exact ⟨⟨hcl, hro s0.mem hcl⟩, hm⟩
  obtain ⟨sf, hs, hout⟩ := h x R s0 hpc hrun hpre' hal hL
  have hcl_f : LibsignalCodeLoaded lsmpl sf.mem :=
    fun i hi hmut X O svc => hs.codeLoaded (hcl i hi hmut X O svc)
  refine ⟨sf, hs, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp1, hp2⟩ | ⟨c, he1, he2⟩ | ⟨ho1, ho2⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, withLsCl, withLsCodeLoaded] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl_f, hpost⟩
  · exact Or.inr (Or.inl ⟨hp1, hp2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he1, he2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho1, ho2⟩))

theorem bytes_merge_6_placed_ok_cro [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)) :=
  bytes_merge_6_cro_of_514
    (bytes_merge_6_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw) hi

theorem bytes_merge_6_proto_placed_ok_cro [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A)) :=
  bytes_merge_6_cro_of_514
    (bytes_merge_6_proto_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw) hi

/-- Relocatable `[LibsignalPlacement]` contract for `bytes::merge [local#5]` (Block `514`) on `lsProg_518 ext`. -/
def BytesMerge6Placed514OkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 514)
    (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A))

/-- Relocatable `[LibsignalPlacement]` `Proto.mergeBytes` contract for `bytes::merge [local#5]` (Block `514`) on `lsProg_518 ext`. -/
def BytesMerge6ProtoPlaced514OkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 514)
    (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A))

abbrev bytesMerge6_placed_ok := @bytes_merge_6_placed_ok

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
