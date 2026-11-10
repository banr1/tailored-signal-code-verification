/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergePhase23W
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Merge -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.HandshakeProstDecode
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1

/-!
# Handshake `bytes::merge [local#6]` Unconstrained-Capacity (`< 2 ^ 62`) Verification

Verifies `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]` against
`bytesMerge3SpecW A img` (`x.bs.length < 2 ^ 62`, without `BytesMergeCapOk`) on
`tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bytesMerge6_fnOff decodeVarint5_fnOff doReserve10_fnOff
  bytesMerge6Off decodeVarint5Off doReserve10Off
  bm6DoReserve10RelOff bm6DecodeVarint5RelOff
  bm6DecodeErrorFromRelOff bm6MemcpyRelOff bm6MemcpyRelNat bm6ShimRelOff bm6ShimRelNat
  bm6AllocRelOff bm6AllocRelNat bm6HandleErrorRelOff bm6HandleErrorRelNat bm6BytesFromVecRelOff
  bm6Off050 bm6Off074 bm6Off07c bm6Off094 bm6Off0e4 bm6Off1b8
  bm6Off210 bm6Off220 bm6Off230 bm6Off254 bm6Off29c bm6Off2c0

/-! ## `MergePost3W` / `MergePanic3W` Lifting Lemmas -/

abbrev MergePost3W (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpecW A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev MergePanic3W (A : RustAlloc) (x : BytesMergeGhost) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpecW A).onPanic x s0 sf ∗ R)

theorem SepWPp.to_subroutineOutcome3W {prog : Program} {A : RustAlloc} {img : Obj.Image}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P (MergePost3W A x s0 R) (MergePanic3W A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (bytesMerge3SpecW A img) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

theorem SepWPp.lift_merge3W {prog : Program} {A : RustAlloc}
    {x : BytesMergeGhost} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .lr) s P
      (MergePostXW A x s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))
      (MergePanicXW A x s0 (memRegion (s0.sp - 33120#64) 48 ∗ R))) :
    SepWPp prog (s0.readReg64 .lr) s (memRegion (s0.sp - 33120#64) 48 ∗ P)
      (MergePost3W A x s0 R) (MergePanic3W A x s0 R) := by
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
    dsimp only [bytesMergeRawSpecXW, bytesMerge3RawSpecW] at hp ⊢
    rw [stackAt_bytesMerge3_eq s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hp
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, memRegion (s0.sp - 33120#64) 48 ∗ P_f,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf, ?_⟩)⟩
    intro hmr
    have hmr' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 33120#64) 48 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmr
    have hp := hpanic hmr'
    dsimp only [bytesMergeRawSpecXW, bytesMerge3RawSpecW] at hp ⊢
    rw [← sepConj_assoc] at hp
    exact allowPanic_frame id hp
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## Phase 1 (`+0x000..+0x074`) and `bytes_merge_6_ok_ext_w` -/

set_option maxHeartbeats 600000 in
theorem bytes_merge_6_ok_of_contractsW {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge6Name + bm6DecodeErrorFromRelOff)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge6Name + bm6MemcpyRelOff)
      (session2MemcpySpecBMX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge6Name + bm6ShimRelOff)
      (session2ShimSpecBMX.inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge6Name + bm6AllocRelOff)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge6Name + bm6HandleErrorRelOff) =
      some Rust.panicked)
    (hDecodeVarint5 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarint5Name)
      ((decodeVarint2SpecX A).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve10 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserve10Name)
      ((doReserve1VecSpecX A).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecX A tmpPtr v v.length).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge6Name)
      (bytesMerge3SpecW A img) := by
  refine ProofLib.subroutine_ok_of_sepWPp fun x R s0 hpc hrun hpre hsp_align => ?_
  rw [bytesMerge3SpecW, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hfl, hsym⟩, hpre⟩ := hpre
  rw [bytesMerge3RawSpecW, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hw0, hx1, hx2, hbs_len⟩, hm⟩ := hpre
  have hbs_len63 : x.bs.length < 2 ^ 63 := by omega
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hcall_dv5 : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMerge6Name + bm6DecodeVarint5RelOff)
      ((decodeVarint2SpecX A).inImage img) := by
    rw [bm6_add_decodeVarint5_eq_fnAddr]
    exact hDecodeVarint5
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue6_err_0x07cW img A H x s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R) hmerge
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue6_decodeErrorFrom_0x074W img A H hdef x s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R) w hw hmerge
  have h094_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0))
      (hle : len.toNat ≤ rest0.length) =>
    @phase2_6_from_0x094W img A H himg hmc hshim halloc hpanic hBytesFromVec hReserve10
      hVtableSlot hVtableDrop x s0 s (memRegion (s0.sp - 33120#64) 48 ∗ R) len rest0 hwt hvar hle hbs_len
  clear hDecodeVarint5 hBytesFromVec hReserve10 hVtableDrop
  refine ⟨_, R, hm, ?_⟩
  change SepWPp _ (s0.readReg64 .lr) s0 _ (MergePost3W A x s0 R) (MergePanic3W A x s0 R)
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
  merge6_fetches_H img.base H bytesMerge6_fnOff 0 116
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMerge6Name = entry
  examples_hide_fetches
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0, hwt]
      decide
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bm6DecodeVarint5RelOff)
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
    intro hfl1 hsym1
    refine SepWPp.bm_call_frame_inv
      (x := ({ bufRef := x.bufRef, slot := x.slot, ptr := x.ptr, bs := x.bs } : DecodeVarintSlowGhost))
      (T := (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarint2StackX)
      hcall_dv5 hfl1 hsym1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp_align]) rfl
      (by simp (config := { decide := true }) only [decodeVarint2SpecX, arm64_norm])
      hbs_len63
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => by
        simp only [bytesMerge3RawSpecW, Spec.inImage, decodeVarint2SpecX,
          State.trace_setPC, State.trace_writeReg64, allocFailedIn] at hm ⊢
        exact allowPanic_frame id hm) ?_
    intro sf_dv hpcf hrunf hspf hcsf hflf hsymf
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
      apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bm6Off07c)
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hfl2 hsym2
      exact SepWPp.lift_merge3W (herr_exit hmerge
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
      apply SepWPp.bm_of_sepWP_inv hflf hsymf
        (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then entry + bm6Off094 else entry + bm6Off050)
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      intro hfl2 hsym2
      by_cases hule : len.ule (BitVec.ofNat 64 rest0.length) = false
      · simp only [hule, Bool.false_eq_true, ↓reduceIte] at hfl2 hsym2 ⊢
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
        apply SepWPp.bm_of_sepWP_inv hfl2 hsym2 (mid := entry + bm6Off074)
        wp_steps
        apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
        intro hfl3 hsym3
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3W (hde_exit 0x8000000000000007#64 (by simp [KindNoHeap]) hmerge
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hfl3 hsym3))
        exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
      · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
          Bool.eq_true_of_not_eq_false hule
        simp only [hule_eq, ↓reduceIte] at hfl2 hsym2 ⊢
        have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
        refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3W (h094_exit len rest0 hwt hvar hle
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf, hx1_sf, h20f, hule_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, hvregsf, and_self])
          hfl2 hsym2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
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
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bm6Off074)
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
    intro hfl1 hsym1
    refine SepWPp.weaken_pre ?_ (SepWPp.lift_merge3W (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hfl1 hsym1))
    exact Entails.of_eq (by dsimp only [savedRegsStack]; simp (config := { decide := true }) only [arm64_norm]; ac_rfl)

private theorem bm6_shim_ok_at_ext_xW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge6Name + bm6ShimRelOff)
      (session2ShimSpecBMX.inImage img) := by
  have h := hA.shim_ok_at bytesMerge6Name bm6ShimRelNat decodeVarintSliceStackX (by decide) (by decide)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((withStack sessionShimSpec decodeVarintSliceStackX).inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, withStack, sessionShimSpec, session2ShimSpecBMX] at hpre ⊢
    simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr hfail

private theorem bm6_memcpy_ok_at_ext_xW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge6Name + bm6MemcpyRelOff)
      (session2MemcpySpecBMX.inImage img) := by
  have h := hA.session_memcpy_region_ok_at bytesMerge6Name bm6MemcpyRelNat decodeVarintSliceStackX (by decide) (by decide)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((withStack sessionMemcpyRegionSpec decodeVarintSliceStackX).inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecBMX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hfail
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecBMX] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hfail

/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]`
meets `bytesMerge3SpecW A img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem bytes_merge_6_ok_ext_w {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContractsX img A ext)
    (hDecodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hDecodeVarint5 : DecodeVarint5OkExtX img A ext)
    (hBytesFromVec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve10 : DoReserve10VecOkExtX img A ext)
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecX A tmpPtr v v.length).inImage img)) :
    BytesMerge6OkExtW img A ext := by
  have hdef : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge6Name + bm6DecodeErrorFromRelOff)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img) := by
    rw [bm6_add_decodeErrorFrom_eq_fnAddr]
    exact hDecodeErrorFrom
  exact bytes_merge_6_ok_of_contractsW himg hdef
    (bm6_memcpy_ok_at_ext_xW hAlloc)
    (bm6_shim_ok_at_ext_xW hAlloc)
    (hAlloc.alloc_ok_at bytesMerge6Name bm6AllocRelNat)
    (panic_at_handle_error_ext img.base ext bytesMerge6Name bm6HandleErrorRelNat)
    hDecodeVarint5 hBytesFromVec hReserve10 hVtableSlot hVtableDrop

theorem bytes_merge_6_ok_ext_w_of_leaf {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContractsX img A ext)
    (hDecodeVarint5 : DecodeVarint5OkExtX img A ext := bm6_decodeVarint5_of_alloc hAlloc) :
    BytesMerge6OkExtW img A ext :=
  bytes_merge_6_ok_ext_w himg hAlloc (bm6_decodeErrorFrom_of_alloc hAlloc) hDecodeVarint5
    (CryptoVerification.LibsignalTripleRatchet.bytesFromVecOk_ext himg rfl)
    (do_reserve_10_vec_ok_ext_x hAlloc)
    CryptoVerification.LibsignalTripleRatchet.bytesVtableSlotLoaded
    (fun tmpPtr v => CryptoVerification.LibsignalTripleRatchet.bytesVtableDrop_base_ok_ext_x hAlloc tmpPtr v v.length)

/-- Top-level `bytes::merge [local#6]` (`< 2 ^ 62` W contract) closed from `himg` and `hAlloc`. -/
theorem bytes_merge_6_ok_ext_w_of_alloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContractsX img A ext) :
    BytesMerge6OkExtW img A ext :=
  bytes_merge_6_ok_ext_w_of_leaf himg hAlloc (bm6_decodeVarint5_of_alloc hAlloc)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  bytesMerge3RawSpecW
  bytesMerge3SpecW
  BytesMerge6OkExtW
  bytes_merge_6_ok_of_contractsW
  bytes_merge_6_ok_ext_w
  bytes_merge_6_ok_ext_w_of_leaf
  bytes_merge_6_ok_ext_w_of_alloc
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
