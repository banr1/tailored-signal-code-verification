/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPost
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymBlocks
import ProofLib.SepLogic.WPp

/-!
# Symbolic Execution of `get_signed_pre_key::{closure#0}`

Composes the prologue, `decimal`, `Dir::get`, and the `.readErr`, `.missing`, `.decodeErr`, and
`.found` branches to prove `spkGetPollInnerSpec`.
-/

/-!
# Symbolic Execution of `get_signed_pre_key::{closure#0}`

Composes the prologue, `decimal`, `Dir::get`, and the `.readErr`, `.missing`, `.decodeErr`, and
`.found` branches to prove `spkGetPollInnerSpec`.
-/

/-!
# Symbolic Execution of `get_signed_pre_key::{closure#0}`

Composes the prologue, `decimal`, `Dir::get`, and the `.readErr`, `.missing`, `.decodeErr`, and
`.found` branches to prove `spkGetPollInnerSpec`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CliSpkPollNorm

/-! ## Top-level symbolic execution composition for `spkGetPollInnerSpec` -/

private theorem entails_pure_pre {P Spatial F : SepProp} {φ : Prop}
    (hφ : φ)
    (hS : P ⊢ Spatial ∗ F := by
      try simp only [words11At, words6At, spkSavedAt,
        sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
        sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
      sep_frame) :
    P ⊢ (⌜φ⌝ ∗ Spatial) ∗ F :=
  Entails.trans hS (sepConj_mono_left (Entails.pure_right hφ (Entails.refl _)))

private theorem sepWPp_pull_pure {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {Body F : SepProp} {post Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (Body ∗ F) post Qp) :
    SepWPp prog ret s ((⌜φ⌝ ∗ Body) ∗ F) post Qp := by
  rw [sepConj_assoc]
  exact SepWPp.pure_elim h

private theorem sepWPp_pull_pure2 {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {W Det Tail F : SepProp} {post Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s ((W ∗ (Det ∗ Tail)) ∗ F) post Qp) :
    SepWPp prog ret s ((W ∗ ((⌜φ⌝ ∗ Det) ∗ Tail)) ∗ F) post Qp := by
  have heq : (W ∗ ((⌜φ⌝ ∗ Det) ∗ Tail)) ∗ F =
      ⌜φ⌝ ∗ ((W ∗ (Det ∗ Tail)) ∗ F) := by ac_rfl
  rw [heq]
  exact SepWPp.pure_elim h

private theorem sepWPp_elim_exists {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Body : α → SepProp} {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v : α, SepWPp prog ret s (Body v ∗ Rest) post Qp) :
    SepWPp prog ret s ((∃∗ v : α, Body v) ∗ Rest) post Qp := by
  rw [sepExists_sepConj_left]
  exact SepWPp.exists_elim h

private theorem sepWPp_exists_mid {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Acc : SepProp} {Body : α → SepProp} {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v : α, SepWPp prog ret s (Acc ∗ (Body v ∗ Rest)) post Qp) :
    SepWPp prog ret s (Acc ∗ ((∃∗ v : α, Body v) ∗ Rest)) post Qp := by
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  exact SepWPp.exists_elim h

private theorem sepWPp_shift {prog : Program} {ret : BitVec 64} {s : State}
    {Acc C Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s ((Acc ∗ C) ∗ Rest) post Qp) :
    SepWPp prog ret s (Acc ∗ (C ∗ Rest)) post Qp := by
  have heq : Acc ∗ (C ∗ Rest) = (Acc ∗ C) ∗ Rest := (sepConj_assoc Acc C Rest).symm
  rw [heq]
  exact h

private theorem sepWPp_mid_5 {prog : Program} {ret : BitVec 64} {s : State}
    {Acc : SepProp}
    {B : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v0 v1 v2 v3 v4 : BitVec 64,
      SepWPp prog ret s (Acc ∗ (B v0 v1 v2 v3 v4 ∗ Rest)) post Qp) :
    SepWPp prog ret s
      (Acc ∗ ((∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, B v0 v1 v2 v3 v4) ∗ Rest)) post Qp :=
  sepWPp_exists_mid fun v0 => sepWPp_exists_mid fun v1 => sepWPp_exists_mid fun v2 =>
    sepWPp_exists_mid fun v3 => sepWPp_exists_mid fun v4 => h v0 v1 v2 v3 v4

private theorem sepWPp_mid_6 {prog : Program} {ret : BitVec 64} {s : State}
    {Acc : SepProp}
    {B : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v0 v1 v2 v3 v4 v5 : BitVec 64,
      SepWPp prog ret s (Acc ∗ (B v0 v1 v2 v3 v4 v5 ∗ Rest)) post Qp) :
    SepWPp prog ret s
      (Acc ∗ ((∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
          B v0 v1 v2 v3 v4 v5) ∗ Rest)) post Qp :=
  sepWPp_exists_mid fun v0 => sepWPp_exists_mid fun v1 => sepWPp_exists_mid fun v2 =>
    sepWPp_exists_mid fun v3 => sepWPp_exists_mid fun v4 => sepWPp_exists_mid fun v5 =>
    h v0 v1 v2 v3 v4 v5

private theorem sepWPp_mid_11 {prog : Program} {ret : BitVec 64} {s : State}
    {Acc : SepProp}
    {B : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : BitVec 64,
      SepWPp prog ret s (Acc ∗ (B v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ∗ Rest)) post Qp) :
    SepWPp prog ret s
      (Acc ∗ ((∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64,
          B v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) ∗ Rest)) post Qp :=
  sepWPp_exists_mid fun v0 => sepWPp_exists_mid fun v1 => sepWPp_exists_mid fun v2 =>
    sepWPp_exists_mid fun v3 => sepWPp_exists_mid fun v4 => sepWPp_exists_mid fun v5 =>
    sepWPp_exists_mid fun v6 => sepWPp_exists_mid fun v7 => sepWPp_exists_mid fun v8 =>
    sepWPp_exists_mid fun v9 => sepWPp_exists_mid fun v10 =>
    h v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10

private theorem sepWP_elim_words6_exists {prog : Program} {pc : BitVec 64} {s : State}
    {a : BitVec 64} {Rest F : SepProp} {post : State → SepProp → Prop}
    (h : ∀ e0 e1 e2 e3 e4 e5 : BitVec 64,
      SepWP prog pc s ((words6At a e0 e1 e2 e3 e4 e5 ∗ Rest) ∗ F) post) :
    SepWP prog pc s
      (((∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64,
          words6At a e0 e1 e2 e3 e4 e5) ∗ Rest) ∗ F) post := by
  simp only [sepExists_sepConj_left]
  exact SepWP.exists_elim fun e0 => SepWP.exists_elim fun e1 =>
    SepWP.exists_elim fun e2 => SepWP.exists_elim fun e3 =>
    SepWP.exists_elim fun e4 => SepWP.exists_elim fun e5 => h e0 e1 e2 e3 e4 e5

private theorem sp_aligned_of_eq {s1 s2 : State} (halign : s1.spAligned = true)
    (hsp : s2.sp = s1.sp) : s2.spAligned = true := by
  simp only [State.spAligned, hsp] at halign ⊢
  exact halign

private theorem sepWPp_call_cells {α : Type}
    {img : Obj.Image} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {calleeStk : Nat} {x0 : PkPollGhost} {R0 : SepProp}
    {entry ret_pc : BitVec 64} {spec : Spec α} {g : α}
    {s0 s : State} {P F : SepProp}
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext) entry (spec.inImage img))
    (hinv : ImgCallInv img s)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htr : s.trace = s0.trace)
    (hpan_eq : ∀ sf, spec.onPanic g s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (hexit_eq : ∀ code sf, spec.onExit g code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom g s sf = ⌜False⌝)
    (hP : P ⊢ spec.pre g s ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ImgCallInv img sf →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
        (spec.post g s sf ∗ F)
        (spkPostQ rd pathOk A calleeStk x0 R0 s0)
        (spkPanicQp rd pathOk A calleeStk x0 R0 s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spkPostQ rd pathOk A calleeStk x0 R0 s0)
      (spkPanicQp rd pathOk A calleeStk x0 R0 s0) := by
  refine SepWPp.call_inImage (x := g) hcall hinv hpc hrun hsp hlr
    (fun R hm => by
      rw [← sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hP) hm)
    (fun sf code R' _ hex => by
      rw [hexit_eq] at hex
      exact not_satisfies_false_sepConj hex)
    (fun sf _ hm => by
      rw [hpan_eq] at hm
      exact close_panic_subgoal htr hm)
    hnext
    (h_no_oom := fun R' sf _ ho => by
      rw [hoom_eq] at ho
      exact (not_satisfies_false_sepConj ho).elim)

theorem spkGetPollInner_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk : Nat}
    (hC : AllocContractsX img A ext)
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeSignedPreKeySpec A img))
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (dropSpeWordSpec A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hhi : max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)) ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName)
      ((spkGetPollInnerSpec rd pathOk A
        (max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)))).inImage img) := by
  set calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
  have hDecimalCells := decimal_cells_ok hDecimal hFs (calleeStk := calleeStk) (by omega) hhi
  have hDirGetCells : ∀ F0 : FsFiles,
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName + dirGetRelOff)
        ((dirGetCellsSpec rd pathOk A F0 calleeStk).inImage img) :=
    fun F0 => dirGet_cells_ok (F0 := F0) hGet (calleeStk := calleeStk) (by omega) hhi
  have hDecodeCells := decodeSpk_cells_ok hDec (calleeStk := calleeStk) (by omega) hhi
  have hDeallocCells := deallocBuf_cells_ok hC (calleeStk := calleeStk) (by omega) hhi
  have hDropCells := dropSpeWord_cells_ok hDrop (calleeStk := calleeStk) (by omega) hhi
  apply subroutine_ok_of_sepWPp_init
  intro x R s0 hpc hrun hpre hsp_align
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (spkGetPollInnerSpec rd pathOk A calleeStk).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, hpre⟩
  dsimp only [spkGetPollInnerSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hsize⟩, hmem⟩
  refine ⟨_, hmem, ?_⟩
  rw [cells_48_split s0.sp]
  dsimp only [spkScratch15]
  have hfront :
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        dirAt A x.self x.dir ∗ memRegion x.out 88 ∗
        A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗
        (spkPollSlack s0.sp ∗
          (cells (s0.sp - 376#64) 5 ∗ cells (s0.sp - 336#64) 5 ∗ cells (s0.sp - 296#64) 5) ∗
          cells (s0.sp - 248#64) 5 ∗
          cells (s0.sp - 200#64) 6 ∗ cells (s0.sp - 152#64) 5 ∗
          cells (s0.sp - 96#64) 6 ∗ cells (s0.sp - 48#64) 6) =
      (x.fut ↦₆₄ x.self) ∗
        memRegion x.out 88 ∗
        cells (s0.sp - 376#64) 5 ∗ cells (s0.sp - 336#64) 5 ∗ cells (s0.sp - 296#64) 5 ∗
        cells (s0.sp - 248#64) 5 ∗ cells (s0.sp - 200#64) 6 ∗ cells (s0.sp - 152#64) 5 ∗
        cells (s0.sp - 96#64) 6 ∗ cells (s0.sp - 48#64) 6 ∗
        (((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
          dirAt A x.self x.dir ∗ A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗
          spkPollSlack s0.sp) := by ac_rfl
  rw [hfront]
  rw [memRegion_88_cells x.out]
  refine sepWPp_mid_11 fun _ _ _ _ _ _ _ _ _ _ _ => sepWPp_shift ?_
  rw [cells_sub_5_376_eq]
  refine sepWPp_mid_5 fun _ a1 a2 a3 a4 => sepWPp_shift ?_
  rw [cells_sub_5_336_eq]
  refine sepWPp_mid_5 fun b0 b1 _ _ _ => sepWPp_shift ?_
  rw [cells_sub_5_296_eq]
  refine sepWPp_mid_5 fun _ _ _ _ _ => sepWPp_shift ?_
  rw [cells_sub_5_248_eq]
  refine sepWPp_mid_5 fun _ _ _ _ _ => sepWPp_shift ?_
  rw [cells_sub_6_200_eq]
  refine sepWPp_mid_6 fun _ _ _ _ _ _ => sepWPp_shift ?_
  rw [cells_sub_5_152_eq]
  refine sepWPp_mid_5 fun _ _ _ _ _ => sepWPp_shift ?_
  rw [cells_sub_6_96_eq]
  refine sepWPp_mid_6 fun _ _ _ _ _ _ => sepWPp_shift ?_
  rw [cells_sub_6_48_eq]
  refine sepWPp_mid_6 fun _ _ _ _ _ _ => ?_
  apply sepWPp_frame_cut hinv0 (step_entry_to_decimal hpc hrun hsp_align hx0 hx8)
  rintro sm1 hpcm1 hrunm1 hspm1 hinv_sm1
    ⟨hsp1, hvr1, htr1, hfiles1, hx0_1, hx1_1, hx30_1, hx19_1, hx20_1, hx21_1, hx27_1, hx29_1⟩
  refine sepWPp_call_cells (pathOk := pathOk)
    (g := (x.id, s0.sp - 248#64, _, _, _, s0.sp - 384#64))
    hDecimalCells hinv_sm1 hpcm1 hrunm1 hspm1 hx30_1 htr1
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (entails_pure_pre ⟨hx0_1, hx1_1, hsp1⟩) ?_
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1 hinv_sf1
  rcases csp_regs hcs_sf1 with
    ⟨hx19_f1, hx20_f1, hx21_f1, _, _, _, _, _, hx27_f1, _, hx29_f1, hvr_f1⟩
  dsimp only [decimalCellsSpec]
  refine sepWPp_elim_exists fun nCap => sepWPp_elim_exists fun nPtr => ?_
  apply sepWPp_pull_pure
  rintro ⟨htr_sf1, hfiles_sf1⟩
  apply sepWPp_frame_cut hinv_sf1
    (step_68_to_dirGet (x := x) hpc_sf1 hrun_sf1 (sp_aligned_of_eq hspm1 hsp_sf1)
      (hsp_sf1.trans hsp1) (hx21_f1.trans hx21_1) (hx29_f1.trans hx29_1))
  rintro sm2 hpcm2 hrunm2 hspm2 hinv_sm2
    ⟨hsp2, hvr2, htr2, hfiles2, hx0_2, hx1_2, hx2_2, hx3_2, hx30_2,
      hx19_2, hx20_2, hx22_2, hx27_2, hx29_2⟩
  have htr_sm2 : sm2.trace = s0.trace := htr2.trans (htr_sf1.trans htr1)
  have hfiles_sm2 : sm2.fs.files = s0.fs.files := hfiles2.trans (hfiles_sf1.trans hfiles1)
  refine sepWPp_call_cells
    (g := (s0.sp - 200#64, x.self, x.dir, nCap, nPtr, x.id, _, _, _, _, _, _, s0.sp - 384#64))
    (hDirGetCells s0.fs.files) hinv_sm2 hpcm2 hrunm2 hspm2 hx30_2 htr_sm2
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (entails_pure_pre ⟨hx0_2, hx1_2, hx2_2, hx3_2, hsp2, hfiles_sm2, hname⟩) ?_
  intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2 hinv_sf2
  rcases csp_regs hcs_sf2 with
    ⟨hx19_f2, hx20_f2, _, hx22_f2, _, _, _, _, hx27_f2, _, hx29_f2, hvr_f2⟩
  have hsp_f2 : sf2.sp = s0.sp - 384#64 := hsp_sf2.trans hsp2
  have halign_f2 : sf2.spAligned = true := sp_aligned_of_eq hspm2 hsp_sf2
  have hvr_s0_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
    hvr_f2.trans (hvr2.trans (hvr_f1.trans hvr1))
  have hx19_s0_f2 : sf2.readReg64 .x19 = x.fut := hx19_f2.trans (hx19_2.trans (hx19_f1.trans hx19_1))
  have hx20_s0_f2 : sf2.readReg64 .x20 = x.out := hx20_f2.trans (hx20_2.trans (hx20_f1.trans hx20_1))
  have hx22_s0_f2 : sf2.readReg64 .x22 = nPtr := hx22_f2.trans hx22_2
  have hx27_s0_f2 : sf2.readReg64 .x27 = s0.sp - 200#64 :=
    hx27_f2.trans (hx27_2.trans (hx27_f1.trans hx27_1))
  have hx29_s0_f2 : sf2.readReg64 .x29 = s0.sp - 96#64 := hx29_f2.trans hx29_2
  dsimp only [dirGetCellsSpec]
  refine sepWPp_elim_exists fun gr => sepWPp_elim_exists fun g0 => sepWPp_elim_exists fun g1 =>
    sepWPp_elim_exists fun g2 => sepWPp_elim_exists fun g3 => sepWPp_elim_exists fun g4 =>
    sepWPp_elim_exists fun g5 => ?_
  apply sepWPp_pull_pure
  rintro ⟨hgr, htr_f2⟩
  rcases gr with ⟨⟩ | (_ | ⟨b, bs⟩)
  · -- `gr = .error ()`
    dsimp only [dirGetDetached]
    apply sepWPp_pull_pure2
    intro hg0
    apply SepWPp.of_sepWP_ret
    apply sepWP_frame_cut hinv_sf2
      (step_readErr_88_to_280 hg0 hpc_sf2 hrun_sf2 halign_f2 hsp_f2 hx27_s0_f2 hx29_s0_f2)
    rintro sm3 hpcm3 hrunm3 hspm3 hinv_sm3
      ⟨hsp3, hvr3, htr3, hx19_3, hx20_3, hx22_3, hx25_3, hx23_3, hx24_3, hx21_3⟩
    apply sepWP_frame_cut hinv_sm3
      (freeName_280_to_344 hDeallocCells hinv_sm3 hpcm3 hrunm3 hspm3 hsp3
        (hx22_3.trans hx22_s0_f2))
    rintro sm4 hpcm4 hrunm4 hspm4 _
      ⟨hsp4, hvr4, htr4, hx19_4, hx20_4, hx26_4, hx25_4, hx23_4, hx24_4, hx21_4⟩
    have hansA :
        PkAns.readErr =
            pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sm4.trace = s0.trace :=
      ⟨by rw [← hgr]; rfl, htr4.trans (htr3.trans (htr_f2.trans htr_sm2))⟩
    exact epilogue_ok hpcm4 hrunm4 hspm4 hsp4
      (hvr4.trans (hvr3.trans hvr_s0_f2))
      (hx19_4.trans (hx19_3.trans hx19_s0_f2))
      (hx20_4.trans (hx20_3.trans hx20_s0_f2))
      hx26_4
      (hx25_4.trans hx25_3)
      (hx23_4.trans hx23_3)
      (hx24_4.trans hx24_3)
      (hx21_4.trans hx21_3)
      (readErr88_pack_cells A x.out g0 g1 g2 g3 g4 g5 _ _ _ _)
      hansA
  · -- `gr = .ok []`
    dsimp only [dirGetDetached]
    apply sepWPp_pull_pure2
    rintro ⟨hg0, hg3⟩
    apply SepWPp.of_sepWP_ret
    apply sepWP_frame_cut hinv_sf2
      (step_missing_88_to_200 hDeallocCells hinv_sf2 hg0 hg3
        hpc_sf2 hrun_sf2 halign_f2 hsp_f2 hx29_s0_f2)
    rintro sm3 hpcm3 hrunm3 hspm3 hinv_sm3
      ⟨hsp3, hvr3, htr3, hx19_3, hx20_3, hx22_3, _, hx29_3, hx26_3⟩
    apply sepWP_frame_cut hinv_sm3
      (freeName_200_to_220 hDeallocCells hinv_sm3 hpcm3 hrunm3 hspm3 hsp3
        (hx22_3.trans hx22_s0_f2))
    rintro sm4 hpcm4 hrunm4 hspm4 hinv_sm4 ⟨hsp4, hcs4, htr4⟩
    rcases csp_regs hcs4 with
      ⟨hx19_4, hx20_4, _, _, _, _, _, hx26_4, _, _, hx29_4, hvr4⟩
    apply sepWP_frame_cut hinv_sm4
      (step_missing_220_to_344 hpcm4 hrunm4 hspm4 hsp4
        (hx29_4.trans hx29_3) (hx26_4.trans hx26_3))
    rintro sm5 hpcm5 hrunm5 hspm5 _
      ⟨hsp5, hvr5, htr5, hx19_5, hx20_5, hx26_5, hx25_5, hx23_5, hx24_5, hx21_5⟩
    have hansB :
        PkAns.missing =
            pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sm5.trace = s0.trace :=
      ⟨by rw [← hgr]; rfl,
        htr5.trans (htr4.trans (htr3.trans (htr_f2.trans htr_sm2)))⟩
    exact epilogue_ok (D := emp) hpcm5 hrunm5 hspm5 hsp5
      (hvr5.trans (hvr4.trans (hvr3.trans hvr_s0_f2)))
      (hx19_5.trans (hx19_4.trans (hx19_3.trans hx19_s0_f2)))
      (hx20_5.trans (hx20_4.trans (hx20_3.trans hx20_s0_f2)))
      hx26_5 hx25_5 hx23_5 hx24_5 hx21_5
      (by rw [sepConj_emp]; exact missing88_pack_cells A x.out _ _ _ b0 b1 a1 a2 a3 a4)
      hansB
  · -- `gr = .ok (b :: bs)`
    have hlen_lt : (b :: bs).length < 2 ^ 32 := hsize (b :: bs) hgr.symm
    dsimp only [dirGetDetached]
    apply sepWPp_pull_pure2
    rintro ⟨hg0, hg3⟩
    apply sepWPp_frame_cut hinv_sf2
      (step_88_to_decodeSpk hg0 hg3 hlen_lt hpc_sf2 hrun_sf2 halign_f2 hsp_f2 hx29_s0_f2)
    rintro sm3 hpcm3 hrunm3 hspm3 hinv_sm3
      ⟨hsp3, hvr3, htr3, hx0_3, hx1_3, hx2_3, hx30_3,
        hx19_3, hx20_3, hx22_3, hx23_3, hx24_3, hx27_3, hx29_3⟩
    have htr_sm3 : sm3.trace = s0.trace := htr3.trans (htr_f2.trans htr_sm2)
    refine sepWPp_call_cells (pathOk := pathOk)
      (g := (s0.sp - 200#64, g1, g2, b :: bs, _, _, _, _, _, _, _, _, _, _, _, s0.sp - 384#64))
      hDecodeCells hinv_sm3 hpcm3 hrunm3 hspm3 hx30_3 htr_sm3
      (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      (entails_pure_pre ⟨hx0_3, hx1_3, hx2_3, hsp3, Nat.zero_lt_succ _, hlen_lt⟩) ?_
    intro sf3 hpc_sf3 hrun_sf3 hsp_sf3 hcs_sf3 hinv_sf3
    rcases csp_regs hcs_sf3 with
      ⟨hx19_f3, hx20_f3, _, hx22_f3, hx23_f3, hx24_f3, _, _, hx27_f3, _, hx29_f3, hvr_f3⟩
    have hsp_f3 : sf3.sp = s0.sp - 384#64 := hsp_sf3.trans hsp3
    have halign_f3 : sf3.spAligned = true := sp_aligned_of_eq hspm3 hsp_sf3
    have hvr_s0_f3 : calleeSavedVRegs sf3 = calleeSavedVRegs s0 :=
      hvr_f3.trans (hvr3.trans hvr_s0_f2)
    have hx19_s0_f3 : sf3.readReg64 .x19 = x.fut :=
      hx19_f3.trans (hx19_3.trans hx19_s0_f2)
    have hx20_s0_f3 : sf3.readReg64 .x20 = x.out :=
      hx20_f3.trans (hx20_3.trans hx20_s0_f2)
    have hx22_s0_f3 : sf3.readReg64 .x22 = nPtr :=
      hx22_f3.trans (hx22_3.trans hx22_s0_f2)
    have hx27_s0_f3 : sf3.readReg64 .x27 = s0.sp - 200#64 :=
      hx27_f3.trans (hx27_3.trans hx27_s0_f2)
    have hx29_s0_f3 : sf3.readReg64 .x29 = s0.sp - 96#64 := hx29_f3.trans hx29_3
    dsimp only [decodeSpkCellsSpec]
    refine sepWPp_elim_exists fun w0 => sepWPp_elim_exists fun w1 =>
      sepWPp_elim_exists fun w2 => sepWPp_elim_exists fun w3 =>
      sepWPp_elim_exists fun w4 => sepWPp_elim_exists fun w5 =>
      sepWPp_elim_exists fun w6 => sepWPp_elim_exists fun w7 =>
      sepWPp_elim_exists fun w8 => sepWPp_elim_exists fun w9 =>
      sepWPp_elim_exists fun w10 => ?_
    apply sepWPp_pull_pure
    intro htr_f3
    have htr_s0_f3 : sf3.trace = s0.trace := htr_f3.trans htr_sm3
    rcases hdes : SignedPreKeyRecord.deserialize (b :: bs) with e | r
    · -- `.error e`
      dsimp only [decodeSpkDetached]
      apply sepWPp_pull_pure2
      intro hw0
      apply SepWPp.of_sepWP_ret
      apply sepWP_frame_cut hinv_sf3
        (step_decodeErr_124_to_280 hDeallocCells hinv_sf3 hw0
          hpc_sf3 hrun_sf3 halign_f3 hsp_f3
          (hx23_f3.trans hx23_3) (hx24_f3.trans hx24_3) hx27_s0_f3 hx29_s0_f3)
      rintro sm4 hpcm4 hrunm4 hspm4 hinv_sm4
        ⟨hsp4, hvr4, htr4, hx19_4, hx20_4, hx22_4, hx25_4, hx23_4, hx24_4, hx21_4⟩
      apply sepWP_frame_cut hinv_sm4
        (freeName_280_to_344 hDeallocCells hinv_sm4 hpcm4 hrunm4 hspm4 hsp4
          (hx22_4.trans hx22_s0_f3))
      rintro sm5 hpcm5 hrunm5 hspm5 _
        ⟨hsp5, hvr5, htr5, hx19_5, hx20_5, hx26_5, hx25_5, hx23_5, hx24_5, hx21_5⟩
      have hansC1 :
          PkAns.decodeErr e =
              pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sm5.trace = s0.trace := by
        refine ⟨?_, htr5.trans (htr4.trans htr_s0_f3)⟩
        rw [← hgr]; dsimp only [pkAnsOf]; rw [hdes]
      exact epilogue_ok hpcm5 hrunm5 hspm5 hsp5
        (hvr5.trans (hvr4.trans hvr_s0_f3))
        (hx19_5.trans (hx19_4.trans hx19_s0_f3))
        (hx20_5.trans (hx20_4.trans hx20_s0_f3))
        hx26_5
        (hx25_5.trans hx25_4)
        (hx23_5.trans hx23_4)
        (hx24_5.trans hx24_4)
        (hx21_5.trans hx21_4)
        (decodeErr88_pack_cells A x.out e w1 w2 w3 w4 w5 w6 _ _ _ _)
        hansC1
    · -- `.ok r`
      dsimp only [decodeSpkDetached]
      apply sepWPp_pull_pure2
      intro hw0
      apply SepWPp.of_sepWP_ret
      apply sepWP_frame_cut hinv_sf3
        (step_found_124_to_180 hw0 hpc_sf3 hrun_sf3 halign_f3 hsp_f3 hx27_s0_f3 hx29_s0_f3)
      rintro sm4 hpcm4 hrunm4 hspm4 hinv_sm4
        ⟨hsp4, hvr4, htr4, hx19_4, hx20_4, hx22_4, hx23_4, hx24_4, hx29_4,
          hx26_4, hx25_4, hx28_4, hx21_4⟩
      apply sepWP_frame_cut hinv_sm4
        (freeBytes_180_to_200 hDeallocCells hinv_sm4 hpcm4 hrunm4 hspm4 hsp4
          (hx23_4.trans (hx23_f3.trans hx23_3)) (hx24_4.trans (hx24_f3.trans hx24_3)))
      rintro sm5 hpcm5 hrunm5 hspm5 hinv_sm5 ⟨hsp5, hcs5, htr5⟩
      rcases csp_regs hcs5 with
        ⟨hx19_5, hx20_5, hx21_5, hx22_5, _, _, hx25_5, hx26_5, _, hx28_5, hx29_5, hvr5⟩
      apply sepWP_frame_cut hinv_sm5
        (freeName_200_to_220 hDeallocCells hinv_sm5 hpcm5 hrunm5 hspm5 hsp5
          (hx22_5.trans (hx22_4.trans hx22_s0_f3)))
      rintro sm6 hpcm6 hrunm6 hspm6 hinv_sm6 ⟨hsp6, hcs6, htr6⟩
      rcases csp_regs hcs6 with
        ⟨hx19_6, hx20_6, hx21_6, _, _, _, hx25_6, hx26_6, _, hx28_6, hx29_6, hvr6⟩
      apply sepWP_frame_cut hinv_sm6
        (step_found_220_to_344 hDropCells hinv_sm6 hw0 hpcm6 hrunm6 hspm6 hsp6
          (hx29_6.trans (hx29_5.trans hx29_4))
          (hx26_6.trans (hx26_5.trans hx26_4))
          (hx25_6.trans (hx25_5.trans hx25_4))
          (hx28_6.trans (hx28_5.trans hx28_4))
          (hx21_6.trans (hx21_5.trans hx21_4)))
      rintro sm7 hpcm7 hrunm7 hspm7 _
        ⟨hsp7, hvr7, htr7, hx19_7, hx20_7, hx26_7, hx25_7, hx23_7, hx24_7, hx21_7⟩
      apply sepWP_elim_words6_exists
      intro _ _ _ _ _ _
      have hansC2 :
          PkAns.found r =
              pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sm7.trace = s0.trace := by
        refine ⟨?_, htr7.trans (htr6.trans (htr5.trans (htr4.trans htr_s0_f3)))⟩
        rw [← hgr]; dsimp only [pkAnsOf]; rw [hdes]
      exact epilogue_ok hpcm7 hrunm7 hspm7 hsp7
        (hvr7.trans (hvr6.trans (hvr5.trans (hvr4.trans hvr_s0_f3))))
        (hx19_7.trans (hx19_6.trans (hx19_5.trans (hx19_4.trans hx19_s0_f3))))
        (hx20_7.trans (hx20_6.trans (hx20_5.trans (hx20_4.trans hx20_s0_f3))))
        hx26_7 hx25_7 hx23_7 hx24_7 hx21_7
        (found88_pack_cells A x.out r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10)
        hansC2

end CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
