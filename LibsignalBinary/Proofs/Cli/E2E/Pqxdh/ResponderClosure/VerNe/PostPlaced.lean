/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Post
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Version-Mismatch `+0x1e04` Composition

Relocatable (`[LibsignalFullPlacement]`) composition `overVerNe_1e04_cli_placed_of_loop`
(`(blkPl_518).base + 0x1e04 → s0.readReg64 .x30`) on `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Stack and spatial fold helpers -/

private theorem stackAt_sub_eq_post_pl (sp : BitVec 64) (big small : Nat)
    (h1 : small ≤ big := by decide) (h2 : big ≤ 2 ^ 64 := by decide) :
    stackAt sp big = memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le h1] at h

private theorem slot3e0_344_fold_post_pl (sp w : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ w) ∗ memRegion (sp + 0x3e8#64) 336 ⊢ memRegion (sp + 0x3e0#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 336) (b' := sp + 0x3e8#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)

private theorem stack_bottom_join_post_pl (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - overDecStackX) ∗
    memRegion (sp - BitVec.ofNat 64 overDecStackX) (overDecStackX - growOneSpeStack) =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) :=
  (ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 rootStack)
    (n := rootStack - overDecStackX)
    (k := overDecStackX - growOneSpeStack)
    (b' := sp - BitVec.ofNat 64 overDecStackX)
    (by decide) (by dsimp only [rootStack, overDecStackX]; bv_omega) (by decide)).symm

/-! ## `+0x1e04 → s0.readReg64 .x30` composition -/

set_option maxHeartbeats 800000 in
/-- Composes `OverVerNe1e04CliA0PlacedStmtGen` at `(blkPl_518).base + 0x1e04` from
`OverVerNe1e04To1e78CliPlacedStmt`, `OverPrevLoopCliPlacedStmtGen`, and
`OverVerNeTail2cfcCliPlacedStmt`. -/
theorem overVerNe_1e04_cli_placed_of_loop [LibsignalFullPlacement] {trackVRegs : Bool}
    (hS1 : OverVerNe1e04To1e78CliPlacedStmt)
    (hLoop : OverPrevLoopCliPlacedStmtGen trackVRegs)
    (hTail : OverVerNeTail2cfcCliPlacedStmt) :
    OverVerNe1e04CliA0PlacedStmtGen trackVRegs := by
  intro ext s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0
    hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc G₁ recG st _hver4
    hsp_root hfr1 hF1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1
  have hstk_dec := stackAt_sub_eq_post_pl s.sp rootStack overDecStackX
  have hstk_grow := stackAt_sub_eq_post_pl s.sp overDecStackX growOneSpeStack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_dec) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have hs1 := hS1 (A := A0) ext
    s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
    hfr1 hF1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1
  refine SepWPp.bind_sepWPp_frame_raw hs1 (by sep_focus)
    fun s6b P_6b hpc6b hrun6b
      ⟨⟨errsPtr, hP6b⟩, hs6b_sp, htr6b, hx19_6b, hx29_6b, hvregs_6b, hF6b⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP6b) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow.symm) (by sep_focus) ?_
  dsimp only [overScratch]
  have hsp6b_align : (s6b.sp &&& 15#64 == 0#64) = true := by rw [hs6b_sp]; exact hsp_align
  have hsp6b_le : overDecStackX ≤ s6b.sp.toNat := by
    rw [hs6b_sp]; exact Nat.le_trans (by decide : overDecStackX ≤ rootStack) hsp_root
  have hx29_6b' : s6b.readReg64 .x29 = s6b.sp + 0xc70#64 := by rw [hx29_6b, hs6b_sp]
  have hloop := hLoop ext s0 s6b coroPtr prevCap prevPtr errsPtr ud0
    0x8000000000000006#64 msgVer enc hcap hver_ne hEnc
    hF6b hpc6b hrun6b hsp6b_align hsp6b_le htr6b hx19_6b hx29_6b'
  rw [hs6b_sp] at hloop
  refine SepWPp.bind_sepWPp_frame_raw hloop (by sep_focus)
    fun s7 P_7 hpc7 hrun7
      ⟨hP7, hs7_sp, htr7, hx19_7, _, hopt_7_6b, hF7⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP7) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk_grow) (by sep_focus) ?_
  have htail := hTail (A := A0) ext
    s0 s s7 coroPtr ctxPtr outPtr errsPtr prevCap prevPtr msgVer msgVer b_2c0 enc recG st
    hF7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7
  refine SepWPp.bind_sepWPp_frame_raw htail (by sep_focus)
    fun sf P_f hpcf hrunf ⟨hPf, hspf, htrf, hcc, hFf, hvregs_f_7⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hPf) ?_
  refine P3P4.SepWPp.weaken_frame
    (slot3e0_344_fold_post_pl s.sp 0xffffffffffffffff#64) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_bottom_join_post_pl s.sp)) (by sep_focus) ?_
  have herrs_ex :
      ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ⊢
      ∃∗ errsCap : BitVec 64, ∃∗ errsPtr' : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr') ∗
        ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
    Entails.sepExists_right 4#64
      (Entails.sepExists_right errsPtr (Entails.sepExists_right 2#64 (Entails.refl _)))
  refine P3P4.SepWPp.weaken_frame herrs_ex (by sep_focus) ?_
  have hopt_f_1 : optVRegsEq trackVRegs sf s1 :=
    optVRegsEq_trans
      (optVRegsEq_trans (optVRegsEq_of_vregs_eq trackVRegs hvregs_6b) hopt_7_6b)
      (optVRegsEq_of_vregs_eq trackVRegs hvregs_f_7)
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨⟨prevPtr + 24#64, ?_⟩, hspf, htrf, hcc, hFf, hopt_f_1⟩
  dsimp only [stageP3ErrPostPrevEmptyPlaced, overScratch, SessionState.recordError]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
