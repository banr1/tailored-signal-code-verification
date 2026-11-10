/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.Hoare.Safety

/-!
# Budget Envelopes, `read_file` Call, and `Ok` Branch for `read_bundle::{closure#0}`

Allocator event envelopes (`BundleReadAfterReadEnv`, `BundleReadTailEnv`, `BundleReadEnv`), the
`read_file` call-site lemma, the tail-deallocation epilogue, and the `Ok(bs)` branch for Block `563`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalHooks LibsignalPlacement lsmpl lsρ
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles FsInv LibsignalCodeRoLoaded NoFsEv TraceFsSound sepWPp_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsReadFileSym lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (
  BundleReadGhost ReadFileGhost ReadRule getResultAt ioVecAt subroutine_ok_withFsInv
  withFsInv withFsInv_post_elim withFsInv_pre_intro
)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_563 blkPC_563 blkPl_563 lsProg_563)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.BundleRead.Helpers (
  frame_80_pack ok_result_intro slot24_pack sret_32_unpack stackAt_frame_80_eq stackAt_split_sub
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
  RustLayoutOk SeqEnv rustAllocEvents rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsXCliPlaced ReadFileRuleEnv bundleReadSpecPlaced readFileSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Allocator Event Envelopes -/

/-- Allocator events emitted after `read_file` returns in `read_bundle::{closure#0}` (`FreeOnlyEvs` on `Ok`, or a 22-byte allocation plus path deallocation on `Err`). -/
def BundleReadAfterReadEnv (rd : ReadRule) (files : FsFiles) (p : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  match rd files p with
  | .ok _ => FreeOnlyEvs evs
  | .error () => SeqEnv (· = rustAllocEvents 22 1) FreeOnlyEvs evs

/-- Tail allocator events of `read_bundle::{closure#0}` after `path` returns (`read_file` followed by `BundleReadAfterReadEnv`). -/
def BundleReadTailEnv (rd : ReadRule)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd)
    (files : FsFiles) (p : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (ReadEnv files p) (BundleReadAfterReadEnv rd files p) evs

/-- Full allocator event envelope of `read_bundle::{closure#0}` parameterized by `PathEnv` and `ReadEnv`. -/
def BundleReadEnv (rd : ReadRule)
    (PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd)
    (files : FsFiles) (dir name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (PathEnv dir name)
    (BundleReadTailEnv rd ReadEnv files (dir ++ [0x2f#8] ++ name)) evs

theorem stepEvents_append_eq {M : AllocCostModel} (evs₁ evs₂ : List AllocEvent) (st : M.σ) :
    M.stepEvents evs₂ (M.stepEvents evs₁ st) = M.stepEvents (evs₁ ++ evs₂) st := by
  simp [AllocCostModel.stepEvents, List.foldl_append]

theorem fitsEvents_22_of_afterRead_err {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rd : ReadRule} {files : FsFiles} {p : List (BitVec 8)}
    (herr : Except.error () = rd files p)
    (hfit : FitsEnv M lim st (BundleReadAfterReadEnv rd files p)) :
    FitsEvents M lim st (rustAllocEvents 22 1) := by
  unfold BundleReadAfterReadEnv at hfit
  rw [← herr] at hfit
  exact FitsEnv.eq_iff.mp hfit.seq_left

theorem bundleReadEnv_ok_end {rd : ReadRule}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {dir name bs : List (BitVec 8)}
    {evs_p evs_r evs_d : List AllocEvent}
    (hp : PathEnv dir name evs_p)
    (hr : ReadEnv files (dir ++ [0x2f#8] ++ name) evs_r)
    (hok : Except.ok bs = rd files (dir ++ [0x2f#8] ++ name))
    (hd : FreeOnlyEvs evs_d) :
    BundleReadEnv rd PathEnv ReadEnv files dir name ((evs_p ++ evs_r) ++ evs_d) := by
  rw [List.append_assoc]
  refine SeqEnv.append hp (SeqEnv.append hr ?_)
  unfold BundleReadAfterReadEnv
  rw [← hok]
  exact hd

theorem bundleReadEnv_err_end {rd : ReadRule}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {dir name : List (BitVec 8)}
    {evs_p evs_r evs_d : List AllocEvent}
    (hp : PathEnv dir name evs_p)
    (hr : ReadEnv files (dir ++ [0x2f#8] ++ name) evs_r)
    (herr : Except.error () = rd files (dir ++ [0x2f#8] ++ name))
    (hd : FreeOnlyEvs evs_d) :
    BundleReadEnv rd PathEnv ReadEnv files dir name
      (((evs_p ++ evs_r) ++ rustAllocEvents 22 1) ++ evs_d) := by
  simp only [List.append_assoc]
  refine SeqEnv.append hp (SeqEnv.append hr ?_)
  unfold BundleReadAfterReadEnv
  rw [← herr]
  exact SeqEnv.append rfl hd

/-! ## Separation-Logic Normalization Helpers -/

theorem bind_sepWP_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (h : let st := s; SepWP prog ret st P Q) :
    SepWP prog ret s P Q := h

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setMem_local (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem fs_setMem_local (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem readReg64_setPState_local (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem readVReg128_setPState_local (s : State) (ps : PState) (v : BitVec 5) :
    (s.setPState ps).readVReg128 v = s.readVReg128 v := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).sp = s.sp := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem mem_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).mem = s.mem := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem status_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).status = s.status := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem trace_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).trace = s.trace := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem symtab_setPState_local (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setPState_local (s : State) (ps : PState) :
    calleeSavedVRegs (s.setPState ps) = calleeSavedVRegs s := rfl

theorem sepWPp_mono_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem sepWPp_exists_pre {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, SepWPp prog ret s (P a) Q Qp) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hm⟩ := hm
  exact h a R hm hL

theorem rustLayoutOk_of_pos_lt63 {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    RustLayoutOk n 1 :=
  ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩

theorem sp_pop_80_eq (sp0 : BitVec 64) : (sp0 - 80#64) + 80#64 = sp0 :=
  BitVec.sub_add_cancel sp0 80#64

theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl _

theorem satisfies_of_eq {m : Memory} {P Q : SepProp} (h : P = Q) (hm : m ⊨ P) :
    m ⊨ Q :=
  h ▸ hm

theorem satisfies_mono_rev {m : Memory} {P Q : SepProp} (hm : m ⊨ P) (h : P ⊢ Q) :
    m ⊨ Q :=
  Satisfies.mono h hm

theorem cs_hi_of_eq {s1 s2 : State}
    (h21 : s1.readReg64 .x21 = s2.readReg64 .x21)
    (h22 : s1.readReg64 .x22 = s2.readReg64 .x22)
    (h23 : s1.readReg64 .x23 = s2.readReg64 .x23)
    (h24 : s1.readReg64 .x24 = s2.readReg64 .x24)
    (h25 : s1.readReg64 .x25 = s2.readReg64 .x25)
    (h26 : s1.readReg64 .x26 = s2.readReg64 .x26)
    (h27 : s1.readReg64 .x27 = s2.readReg64 .x27)
    (h28 : s1.readReg64 .x28 = s2.readReg64 .x28) :
    ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s1.readReg64 (.gpr ⟨n, by omega⟩) = s2.readReg64 (.gpr ⟨n, by omega⟩) := by
  intro n hn
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 := by omega
  all_goals assumption

theorem cs_hi_of_preserved {s1 s2 : State} (h : CalleeSavedPreserved s1 s2) :
    ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s2.readReg64 (.gpr ⟨n, by omega⟩) = s1.readReg64 (.gpr ⟨n, by omega⟩) :=
  cs_hi_of_eq h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1

theorem cs_hi_trans {s1 s2 s3 : State}
    (h12 : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s1.readReg64 (.gpr ⟨n, by omega⟩) = s2.readReg64 (.gpr ⟨n, by omega⟩))
    (h23 : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s2.readReg64 (.gpr ⟨n, by omega⟩) = s3.readReg64 (.gpr ⟨n, by omega⟩)) :
    ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s1.readReg64 (.gpr ⟨n, by omega⟩) = s3.readReg64 (.gpr ⟨n, by omega⟩) :=
  fun n hn => (h12 n hn).trans (h23 n hn)

/-! ## Budget-Threaded `read_file` Call Step -/

abbrev ReadCallHypPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (readStk : Nat)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd) : Prop :=
  subroutine_ok (lsProg_563 H) (lsρ lsReadFileSym)
    (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv))

/-- Executes `bl signal_session_io::read_file` at `+40` on Block `563`, threading `A.pool lim st` and preserving `FsInv F0 T0`. -/
theorem readCall_step_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hRead : ReadCallHypPlaced A lim H rd pathOk readStk ReadEnv)
    (hFs : TraceFsSound (lsProg_563 H))
    (F0 : FsFiles) (T0 : List TraceEvent)
    {ret : BitVec 64} {s : State} {st : M.σ}
    {pathPtr retSlot : BitVec 64} {p : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hPC : s.pc = (blkPl_563).base + 40#64)
    (hRun : s.status = .Running)
    (hAl : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : FsInv F0 T0 s)
    (htr : s.trace = T0)
    (hx0 : s.readReg64 .x0 = pathPtr)
    (hx1 : (s.readReg64 .x1).toNat = p.length)
    (hx8 : s.readReg64 .x8 = retSlot)
    (hlen : p.length < 2 ^ 32)
    (hpOk : pathOk p)
    (hfit : FitsEnv M lim st (ReadEnv F0 p))
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_563).base + 44#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.spAligned = true →
      CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      FsInv F0 T0 sf →
      ∀ evs : List AllocEvent,
      ReadEnv F0 p evs →
      ∀ r : Except Unit (List (BitVec 8)),
      (r = rd F0 p ∧ sf.trace = T0) →
      SepWPp (lsProg_563 H) ret sf
        (ioVecAt A.repAlloc retSlot r ∗ (pathPtr ↦ₛ p) ∗ stackAt s.sp readStk ∗
          A.pool lim (M.stepEvents evs st) sf ∗ F) Q Qp) :
    SepWPp (lsProg_563 H) ret s
      (((pathPtr ↦ₛ p) ∗ memRegion retSlot 24 ∗ stackAt s.sp readStk ∗ A.pool lim st s) ∗ F) Q Qp := by
  apply sepWPp_seq_lscro hcrl (mid := lsρ lsReadFileSym)
  wp_steps_sync_pool (lsρ lsReadFileSym)
  apply bind_sepWP_state; intro s1
  refine SepWP.done ?_ ?_ ?_
  · simp only [s1, wp_norm, arm64_norm]
  · simp only [s1, wp_norm, arm64_norm, hRun]
  · intro hcrl1 R hm1 hL
    have hpc1 : s1.pc = lsρ lsReadFileSym := by simp only [s1, wp_norm, arm64_norm]
    have hlr1 : s1.readReg64 .lr = (blkPl_563).base + 44#64 := by
      simp only [s1, wp_norm, arm64_norm]
    have hs_files : s.fs.files = F0 :=
      hinv.files_eq (by simp [htr] : s.trace = T0 ++ []) (by simp [NoFsEv])
    have hs1_files : s1.fs.files = F0 := by simpa [s1, wp_norm, arm64_norm] using hs_files
    have hLift : subroutine_ok (lsProg_563 H) (lsρ lsReadFileSym)
        (withFsInv (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)) F0 T0) :=
      subroutine_ok_withFsInv hFs hRead F0 T0
    let g : ReadFileGhost := { pathA := pathPtr, path := p, ret := retSlot }
    obtain ⟨sm, hsteps_call, hout, -⟩ :=
      hLift.no_fault_before_outcome (g, st) (F ∗ R) s1
        hpc1
        (by simp [s1, wp_norm, arm64_norm, hRun])
        (withFsInv_pre_intro
          ⟨[], by simp [s1, wp_norm, arm64_norm, htr], fun _ => hs1_files⟩
          (by
            have hmem1 : s1.mem ⊨
                (readFileSpecPlaced rd pathOk A lim readStk ReadEnv).pre (g, st) s1 ∗ (F ∗ R) := by
              dsimp only [readFileSpecPlaced]
              rw [sepConj_assoc, satisfies_pure_sepConj]
              refine ⟨⟨by simpa [s1, g, wp_norm, arm64_norm] using hx0,
                by simpa [s1, g, wp_norm, arm64_norm] using hx1,
                by simpa [s1, g, wp_norm, arm64_norm] using hx8,
                hlen, hpOk, hs1_files ▸ hfit⟩, ?_⟩
              have hsp1 : s1.sp = s.sp := by simp [s1, wp_norm, arm64_norm]
              rw [hsp1]
              refine satisfies_of_eq ?_ hm1
              dsimp only [g]
              sep_ac_rfl
            exact satisfies_lscro_pre hcrl1 hmem1))
        (by simpa [State.spAligned, s1, wp_norm, arm64_norm] using hAl)
        hL
    rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ |
      ⟨_, hpost⟩
    · obtain ⟨hinv_sm, hpost_rf⟩ := withFsInv_post_elim hpost
      dsimp only [withLsCodeRoLoaded, readFileSpecPlaced] at hpost_rf
      simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpost_rf
      obtain ⟨evs, hpost_evs⟩ := hpost_rf
      rw [satisfies_pure_sepConj] at hpost_evs
      obtain ⟨hevs_raw, hpost_r0⟩ := hpost_evs
      have hevs : ReadEnv F0 p evs := by simpa [g, hs1_files] using hevs_raw
      rw [satisfies_sepExists] at hpost_r0
      obtain ⟨r, hpost_r⟩ := hpost_r0
      rw [satisfies_pure_sepConj] at hpost_r
      obtain ⟨⟨hr1, hr2⟩, hmem_sm⟩ := hpost_r
      have hr_out : r = rd F0 p ∧ sm.trace = T0 :=
        ⟨hr1.trans (by simp [g, hs1_files]),
          hr2.trans (by simpa [s1, wp_norm, arm64_norm] using htr)⟩
      rw [hlr1] at hpcm
      have hsp_eq : sm.sp = s.sp := hspm.trans (by simp [s1, wp_norm, arm64_norm])
      have hsp_al_sm : sm.spAligned = true := by simpa [State.spAligned, hsp_eq] using hAl
      have hcs_s : CalleeSavedPreserved s sm := by
        simpa [CalleeSavedPreserved, s1, wp_norm, arm64_norm] using hcsm
      have hmem_sm' : sm.mem ⊨
          (ioVecAt A.repAlloc retSlot r ∗ (pathPtr ↦ₛ p) ∗ stackAt s.sp readStk ∗
            A.pool lim (M.stepEvents evs st) sm ∗ F) ∗ R := by
        have hsp1 : s1.sp = s.sp := by simp [s1, wp_norm, arm64_norm]
        rw [hsp1] at hmem_sm
        refine satisfies_of_eq ?_ hmem_sm
        dsimp only [g]
        sep_ac_rfl
      obtain ⟨sf, hsteps_rest, hout_rest⟩ :=
        hnext sm hpcm hrunm hsp_eq hsp_al_sm hcs_s
          (hcrl1.of_keepsFrozen hsteps_call.keepsFrozen)
          hinv_sm evs hevs r hr_out R hmem_sm' (hsteps_call.codeLoaded hL)
      exact ⟨sf, hsteps_call.trans hsteps_rest, hout_rest⟩
    · dsimp only [withFsInv, withLsCodeRoLoaded, readFileSpecPlaced] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact (not_satisfies_false_sepConj hpost.2).elim
    · dsimp only [withFsInv, withLsCodeRoLoaded, readFileSpecPlaced] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact (not_satisfies_false_sepConj hpost.2).elim
    · dsimp only [withFsInv, withLsCodeRoLoaded, readFileSpecPlaced] at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      exact (not_satisfies_false_sepConj hpost.2).elim

/-! ## Tail-Deallocation Epilogue and `Ok(bs)` Branch -/

/-- Non-zero-capacity epilogue (`+84 .. +108` on Block `563`): deallocates `path`, restores callee-saved registers and `sp`, and returns. -/
theorem tail_dealloc_step_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {BundleEnv : FsFiles → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 0x50 + extHookStack ≤ stk)
    (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {st0 st_pre : M.σ} {evs_pre : List AllocEvent}
    {s0 s : State}
    {pathCap pathPtr : BitVec 64} {r : Except Unit (List (BitVec 8))}
    {F : SepProp}
    (hPC : s.pc = (blkPl_563).base + 84#64)
    (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hAl0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx19_s : s.readReg64 .x19 = pathPtr)
    (hx1_s : s.readReg64 .x1 = pathCap)
    (hcap_pos : 0 < pathCap.toNat)
    (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hr_out : r = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace)
    (hst_pre : st_pre = M.stepEvents evs_pre st0)
    (hevs_end : ∀ evs_d, FreeOnlyEvs evs_d →
      BundleEnv s0.fs.files x.dir x.name (evs_pre ++ evs_d)) :
    SepWPp (lsProg_563 H) (s0.readReg64 .lr) s
      (((getResultAt A.repAlloc x.ret r ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s) ∗ F))
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk).post (x, st0) s0 sf ∗ F)
      (fun sf Qp =>
        Qp = (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk).onPanic (x, st0) s0 sf ∗ F) := by
  have hAl_frame : (s0.sp - 80#64) &&& 15#64 = 0#64 := by
    have hal : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned] using hAl0
    bv_bits
  have hsplit_hk : stackAt (s0.sp - 80#64) (stk - 80) =
      memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        stackAt (s0.sp - 80#64) extHookStack :=
    stackAt_split_sub (s0.sp - 80#64) (stk - 80) extHookStack (by omega) (by omega)
  apply sepWPp_seq_lscro hcrl (mid := lsρ lsRustDeallocSymCli)
  wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
  apply bind_sepWP_state; intro s1
  refine SepWP.done ?_ ?_ ?_
  · simp [s1, wp_norm, arm64_norm]
  · simp [s1, wp_norm, arm64_norm, hRun]
  · intro hcrl1 R hm1 hL1
    have hsp1 : s1.sp = s0.sp - 80#64 := by simp [s1, wp_norm, arm64_norm, hsp]
    have htr_s1 : s1.trace = s.trace := by simp [s1, wp_norm, arm64_norm]
    let restDealloc : SepProp :=
      getResultAt A.repAlloc x.ret r ∗
        bytesAt x.dirRo x.dirA x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion ((s0.sp - 80#64) - BitVec.ofNat 64 (stk - 80)) ((stk - 80) - extHookStack) ∗
        memRegion (s0.sp - 80#64) 24 ∗
        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
        (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗ F
    have hm1_d : s1.mem ⊨
        (A.pool lim st_pre s1 ∗ A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          stackAt s1.sp extHookStack) ∗ restDealloc ∗ R := by
      rw [hsp1]
      have hm1' := hm1
      simp only [List.length_append, List.length_cons, List.length_nil] at hm1' ⊢
      rw [hsplit_hk] at hm1'
      refine satisfies_of_eq ?_ hm1'
      dsimp only [restDealloc]
      simp only [List.length_append, List.length_cons, List.length_nil]
      sep_ac_rfl
    obtain ⟨sd, hsteps_d, hout_d, -⟩ :=
      (dealloc_lscro_of_cli hC).no_fault_before_outcome
        (pathPtr, pathCap.toNat, 1, st_pre) (restDealloc ∗ R) s1
        (by simp [s1, wp_norm, arm64_norm])
        (by simp [s1, wp_norm, arm64_norm, hRun])
        (satisfies_lscro_pre hcrl1 (by
          dsimp only [rustDeallocExternSpecWithStack,
            LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
            rustCliDeallocBudgetExternSpecWithStack]
          simp only [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨by simp [s1, wp_norm, arm64_norm],
             by simp [s1, wp_norm, arm64_norm, hx1_s],
             rfl,
             rustLayoutOk_of_pos_lt63 hcap_pos hcap_lt,
             ⟨563, by decide, 96, by decide, by simp only [s1, wp_norm, arm64_norm]; rfl⟩⟩,
            by simpa [sepConj_assoc] using hm1_d⟩))
        (by simpa [State.spAligned, hsp1] using hAl_frame)
        hL1
    rcases hout_d with ⟨⟨hpcsd, hsp_d0, hrunsd⟩, ⟨hspsd, hcssd⟩, hpost_d⟩ | ⟨_, hpost_d⟩ |
        ⟨_, _, hpost_d⟩ | ⟨_, hpost_d⟩
    · dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          rustCliDeallocBudgetExternSpecWithStack] at hpost_d
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost_d
      obtain ⟨htr_sd, hmem_sd⟩ := hpost_d
      replace hpcsd : sd.pc = (blkPl_563).base + 96#64 :=
        hpcsd.trans (by simp [s1, wp_norm, arm64_norm])
      have hspd : sd.sp = s0.sp - 80#64 := hspsd.trans hsp1
      clear hsp_d0 hspsd
      have hcrl_d : LibsignalCodeRoLoaded lsmpl sd.mem :=
        hcrl1.of_keepsFrozen hsteps_d.keepsFrozen
      have hLd := hsteps_d.codeLoaded hL1
      let evs_d := rustDeallocEvents pathCap.toNat 1
      let evs_all := evs_pre ++ evs_d
      have hst_all : M.stepEvents evs_d st_pre = M.stepEvents evs_all st0 := by
        rw [hst_pre]
        exact stepEvents_append_eq evs_pre evs_d st0
      have hmd_ep : sd.mem ⊨
          (((getResultAt A.repAlloc x.ret r ∗
            bytesAt x.dirRo x.dirA x.dir ∗
            bytesAt x.nameRo x.nameA x.name ∗
            stackAt (s0.sp - 80#64) (stk - 80) ∗
            memRegion (s0.sp - 80#64) 24 ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.pool lim (M.stepEvents evs_all st0) sd) ∗ F) ∗ R) := by
        have hmem_sd' := hmem_sd
        have hst_all' : M.stepEvents (rustDeallocEvents pathCap.toNat 1) st_pre =
            M.stepEvents evs_all st0 := hst_all
        rw [hsp1, hst_all'] at hmem_sd'
        rw [hsplit_hk]
        refine satisfies_of_eq ?_ hmem_sd'
        dsimp only [restDealloc]
        simp only [List.length_append, List.length_cons, List.length_nil]
        sep_ac_rfl
      have hwp_ep :
          SepWPp (lsProg_563 H) (s0.readReg64 .lr) sd
            (((getResultAt A.repAlloc x.ret r ∗
              bytesAt x.dirRo x.dirA x.dir ∗
              bytesAt x.nameRo x.nameA x.name ∗
              stackAt (s0.sp - 80#64) (stk - 80) ∗
              memRegion (s0.sp - 80#64) 24 ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
              (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.pool lim (M.stepEvents evs_all st0) sd) ∗ F))
            (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
              Q = (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk).post (x, st0) s0 sf ∗ F)
            (fun sf Qp =>
              Qp = (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk).onPanic (x, st0) s0 sf ∗ F) := by
        apply sepWPp_seq_lscro hcrl_d (mid := s0.readReg64 .lr)
        wp_conv_pre => rw [← hspd]
        wp_steps_sync_pool (s0.readReg64 .lr)
        apply bind_sepWP_state; intro sf
        refine SepWP.done ?_ ?_ ?_
        · simp [sf, wp_norm, arm64_norm]
        · simp [sf, wp_norm, arm64_norm, hrunsd]
        · intro _ R_ep hm_ep _hL_ep
          have hpack80 := frame_80_pack (s0.sp - 80#64) pathCap pathPtr
            (BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length)
            (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x20) (s0.readReg64 .x19)
          have hstk80 : stackAt s0.sp stk =
              stackAt (s0.sp - 80#64) (stk - 80) ∗ memRegion (s0.sp - 80#64) 80 :=
            stackAt_frame_80_eq s0.sp stk (by omega) hstk_le
          have htr_sf : sf.trace = sd.trace := by simp [sf, wp_norm, arm64_norm]
          have hr_final :
              r = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ sf.trace = s0.trace ∧
                BundleEnv s0.fs.files x.dir x.name evs_all :=
            ⟨hr_out.1, htr_sf.trans (htr_sd.trans (htr_s1.trans hr_out.2)),
              hevs_end evs_d (FreeOnlyEvs.singleton 1 pathCap.toNat)⟩
          refine ⟨sf, Steps.refl sf,
            Or.inl ⟨by simp [sf, wp_norm, arm64_norm], by simp [sf, wp_norm, arm64_norm, hrunsd], _, ?_,
              by simp [sf, wp_norm, arm64_norm], ?_, rfl⟩⟩
          · have hm_ep' : sf.mem ⊨
                (((getResultAt A.repAlloc x.ret r ∗
                  bytesAt x.dirRo x.dirA x.dir ∗
                  bytesAt x.nameRo x.nameA x.name ∗
                  (stackAt (s0.sp - 80#64) (stk - 80) ∗
                    (memRegion (s0.sp - 80#64) 24 ∗
                      (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                      (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                      (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                      (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                      (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                      (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                      (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19))) ∗
                  A.pool lim (M.stepEvents evs_all st0) sf) ∗ F) ∗ R_ep) := by
              refine satisfies_of_eq ?_ hm_ep
              simp only [hspd, List.length_append, List.length_cons, List.length_nil]
              sep_ac_rfl
            have h1 :
                (stackAt (s0.sp - 80#64) (stk - 80) ∗
                  (memRegion (s0.sp - 80#64) 24 ∗
                    (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                    (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                    (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                    (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                    (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                    (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                    (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19))) ⊢
                stackAt s0.sp stk := by
              rw [hstk80]
              exact sepConj_mono_right hpack80
            have hpost_ent :
                ((getResultAt A.repAlloc x.ret r ∗
                  bytesAt x.dirRo x.dirA x.dir ∗
                  bytesAt x.nameRo x.nameA x.name ∗
                  (stackAt (s0.sp - 80#64) (stk - 80) ∗
                    (memRegion (s0.sp - 80#64) 24 ∗
                      (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
                      (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
                      (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
                      (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
                      (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                      (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
                      (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19))) ∗
                  A.pool lim (M.stepEvents evs_all st0) sf) ∗ F) ⊢
                (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk).post (x, st0) s0 sf ∗ F := by
              dsimp only [bundleReadSpecPlaced, withLsCodeRoLoaded]
              refine Entails.trans
                (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_left h1))))) ?_
              have hre :
                  ((getResultAt A.repAlloc x.ret r ∗
                    bytesAt x.dirRo x.dirA x.dir ∗
                    bytesAt x.nameRo x.nameA x.name ∗
                    stackAt s0.sp stk ∗
                    A.pool lim (M.stepEvents evs_all st0) sf) ∗ F) =
                  (getResultAt A.repAlloc x.ret r ∗
                    (bytesAt x.dirRo x.dirA x.dir ∗
                      bytesAt x.nameRo x.nameA x.name ∗
                      stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs_all st0) sf)) ∗ F := by
                sep_ac_rfl
              rw [hre]
              refine sepConj_mono_left ?_
              refine Entails.sepExists_right evs_all ?_
              exact sepConj_mono_left
                (Entails.sepExists_right r (Entails.pure_right hr_final (Entails.refl _)))
            exact Satisfies.mono (sepConj_mono_left hpost_ent) hm_ep'
          · have hcs_sf_s0 :=
              cs_hi_trans
                (cs_hi_of_eq (s1 := sf) (s2 := sd)
                  (by simp [sf, wp_norm, arm64_norm]) (by simp [sf, wp_norm, arm64_norm])
                  (by simp [sf, wp_norm, arm64_norm]) (by simp [sf, wp_norm, arm64_norm])
                  (by simp [sf, wp_norm, arm64_norm]) (by simp [sf, wp_norm, arm64_norm])
                  (by simp [sf, wp_norm, arm64_norm]) (by simp [sf, wp_norm, arm64_norm]))
                (cs_hi_trans (cs_hi_of_preserved hcssd)
                  (cs_hi_trans
                    (cs_hi_of_eq (s1 := s1) (s2 := s)
                      (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                      (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                      (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm])
                      (by simp [s1, wp_norm, arm64_norm]) (by simp [s1, wp_norm, arm64_norm]))
                    hcs_hi))
            unfold CalleeSavedPreserved at hcssd ⊢
            refine ⟨by simp [sf, wp_norm, arm64_norm],
              by simp [sf, wp_norm, arm64_norm],
              hcs_sf_s0 21 ⟨by omega, by omega⟩,
              hcs_sf_s0 22 ⟨by omega, by omega⟩,
              hcs_sf_s0 23 ⟨by omega, by omega⟩,
              hcs_sf_s0 24 ⟨by omega, by omega⟩,
              hcs_sf_s0 25 ⟨by omega, by omega⟩,
              hcs_sf_s0 26 ⟨by omega, by omega⟩,
              hcs_sf_s0 27 ⟨by omega, by omega⟩,
              hcs_sf_s0 28 ⟨by omega, by omega⟩,
              by simp [sf, wp_norm, arm64_norm],
              ((by simp [sf, calleeSavedVRegs, wp_norm, arm64_norm] :
                calleeSavedVRegs sf = calleeSavedVRegs sd).trans
                (hcssd.2.2.2.2.2.2.2.2.2.2.2.trans
                  ((by simp [s1, calleeSavedVRegs, wp_norm, arm64_norm] :
                    calleeSavedVRegs s1 = calleeSavedVRegs s).trans hvregs)))⟩
      obtain ⟨sf, hsteps_ep, hout_ep⟩ := hwp_ep R hmd_ep hLd
      exact ⟨sf, hsteps_d.trans hsteps_ep, hout_ep⟩
    · exact (not_satisfies_false_sepConj hpost_d).elim
    · exact (not_satisfies_false_sepConj hpost_d).elim
    · exact (not_satisfies_false_sepConj hpost_d).elim

set_option maxHeartbeats 800000 in
/-- `Ok(bs)` branch (`+44 .. +84` on Block `563`): stores `(okTagVec, cap, ptr, len)` at `x.ret` and enters `tail_dealloc_step_p`. -/
theorem ok_branch_step_p [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {BundleEnv : FsFiles → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hstk : 0x50 + extHookStack ≤ stk)
    (hstk_le : stk ≤ 2 ^ 64)
    {x : BundleReadGhost} {st0 st_pre : M.σ} {evs_pre : List AllocEvent}
    {s0 s : State}
    {pathCap pathPtr : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp}
    (hPC : s.pc = (blkPl_563).base + 44#64)
    (hRun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (hAl0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx19_s : s.readReg64 .x19 = pathPtr)
    (hx20_s : s.readReg64 .x20 = x.ret)
    (hcap_pos : 0 < pathCap.toNat)
    (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hcs_hi : ∀ n : Nat, (hn : 21 ≤ n ∧ n ≤ 28) →
      s.readReg64 (.gpr ⟨n, by omega⟩) = s0.readReg64 (.gpr ⟨n, by omega⟩))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hr_out : Except.ok bs = rd s0.fs.files (x.dir ++ [0x2f#8] ++ x.name) ∧ s.trace = s0.trace)
    (hst_pre : st_pre = M.stepEvents evs_pre st0)
    (hevs_end : ∀ evs_d, FreeOnlyEvs evs_d →
      BundleEnv s0.fs.files x.dir x.name (evs_pre ++ evs_d)) :
    SepWPp (lsProg_563 H) (s0.readReg64 .lr) s
      (((vecU8 A.repAlloc (s0.sp - 80#64) bs ∗
          memRegion x.ret 48 ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s) ∗ F))
      (fun sf Q => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        Q = (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk).post (x, st0) s0 sf ∗ F)
      (fun sf Qp =>
        Qp = (bundleReadSpecPlaced rd pathOk A lim BundleEnv stk).onPanic (x, st0) s0 sf ∗ F) := by
  dsimp only [vecU8, vecU8At, vecHeader, RustCliAllocBudget.repAlloc]
  simp only [sepExists_sepConj_left]
  apply sepWPp_exists_pre; intro vecCap
  apply sepWPp_exists_pre; intro vecPtr
  apply sepWPp_mono_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (sret_32_unpack x.ret))))
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWPp_exists_pre; intro w3
  apply sepWPp_exists_pre; intro w2
  apply sepWPp_exists_pre; intro w1
  apply sepWPp_exists_pre; intro w0 R hm hL
  have hpure_vec :
      bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0 := by
    have hm' : s.mem ⊨ ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
        ((((s0.sp - 80#64) ↦₆₄ vecCap) ∗ (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
          (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if vecCap = 0 then emp
           else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
             memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length)) ∗
          ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
            ((x.ret + 24#64) ↦₆₄ w3) ∗ memRegion (x.ret + 32#64) 16) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s ∗ F) ∗ R) := by
      refine satisfies_of_eq ?_ hm
      sep_ac_rfl
    rw [satisfies_pure_sepConj] at hm'
    exact hm'.1
  have hnot_err : (vecCap + 1#64 == 0#64) = false := by
    apply beq_false_of_ne
    intro heq
    have hnat := congrArg BitVec.toNat heq
    simp [BitVec.toNat_add] at hnat
    omega
  have heq_cond : ConditionHolds CondCode.EQ (AddWithCarry64 vecCap 1#64 false).2 = false := by
    have _ : vecCap.toNat < 2 ^ 63 := hpure_vec.2.1
    simp only [ConditionHolds, AddWithCarry64]
    bv_bits
  have hcap_ne : pathCap ≠ 0#64 := by intro heq; subst heq; simp at hcap_pos
  have hcap_ne0 : (pathCap == 0#64) = false := beq_false_of_ne hcap_ne
  have _ := And.intro heq_cond (And.intro hnot_err (And.intro hcap_ne hcap_ne0))
  have hm_flat : s.mem ⊨
      (((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
        ((x.ret + 24#64) ↦₆₄ w3) ∗ memRegion (x.ret + 32#64) 16 ∗
        ((s0.sp - 80#64) ↦₆₄ vecCap) ∗
        (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
        (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
        (if vecCap = 0 then emp
         else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
           memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length)) ∗
        bytesAt x.dirRo x.dirA x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 80#64) (stk - 80) ∗
        (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
        (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
        (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
        (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
        (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
        (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
        A.pool lim st_pre s ∗ F) ∗ R) := by
    refine satisfies_of_eq ?_ hm
    simp only [List.length_append, List.length_cons, List.length_nil]
    sep_ac_rfl
  simp only [arm64_norm] at hx20_s
  refine (?_ : SepWPp (lsProg_563 H)
    (s0.readReg64 .lr) s _ _ _) R hm_flat hL
  apply sepWPp_seq_lscro hcrl (mid := (blkPl_563).base + 84#64)
  wp_steps_sync_pool ((blkPl_563).base + 84#64)
  apply bind_sepWP_state; intro s_mid
  refine SepWP.done ?_ ?_ ?_
  · simp [s_mid, wp_norm, arm64_norm]
  · simp [s_mid, wp_norm, arm64_norm, hRun]
  · intro hcrl_mid R' hm_mid hL_mid
    have hs_mid_sp : s_mid.sp = s0.sp - 80#64 := by simp [s_mid, wp_norm, arm64_norm, hsp]
    have hs_mid_x1 : s_mid.readReg64 .x1 = pathCap := by simp [s_mid, wp_norm, arm64_norm]
    have hs_mid_x19 : s_mid.readReg64 .x19 = pathPtr := by
      simp [s_mid, wp_norm, arm64_norm, hx19_s]
    have hs_mid_tr : s_mid.trace = s.trace := by simp [s_mid, wp_norm, arm64_norm]
    have hpack_ok :
        ((((s0.sp - 80#64) ↦₆₄ vecCap) ∗
          (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
          (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
          (if vecCap = 0 then emp
           else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
             memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
          ((x.ret ↦₆₄ okTagVec) ∗ ((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
            ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ memRegion (x.ret + 32#64) 16) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) ⊢
        (getResultAt A.repAlloc x.ret (.ok bs) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) := by
      have hre1 :
          ((((s0.sp - 80#64) ↦₆₄ vecCap) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
            (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
            (if vecCap = 0 then emp
             else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
               memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
            ((x.ret ↦₆₄ okTagVec) ∗ ((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
              ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ memRegion (x.ret + 32#64) 16)) =
          ((x.ret ↦₆₄ okTagVec) ∗
            (((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
              ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
              ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
              (if vecCap = 0 then emp
               else A.repAlloc.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
                 memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
            memRegion (x.ret + 32#64) 16) ∗
          (((s0.sp - 80#64) ↦₆₄ vecCap) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
            (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) := by
        dsimp only [RustCliAllocBudget.repAlloc]
        sep_ac_rfl
      have hboth := sepConj_mono (ok_result_intro A.repAlloc x.ret vecCap vecPtr bs)
        (slot24_pack (s0.sp - 80#64) vecCap vecPtr (BitVec.ofNat 64 bs.length))
      rw [← hre1] at hboth
      have hall := sepConj_mono_left
        (Q := bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) hboth
      have hre2 :
          (getResultAt A.repAlloc x.ret (.ok bs) ∗ memRegion (s0.sp - 80#64) 24) ∗
            (bytesAt x.dirRo x.dirA x.dir ∗
              bytesAt x.nameRo x.nameA x.name ∗
              stackAt (s0.sp - 80#64) (stk - 80) ∗
              (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
              (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
              (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
              (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
              (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
              (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
              A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
              A.pool lim st_pre s_mid) =
          getResultAt A.repAlloc x.ret (.ok bs) ∗
            bytesAt x.dirRo x.dirA x.dir ∗
            bytesAt x.nameRo x.nameA x.name ∗
            stackAt (s0.sp - 80#64) (stk - 80) ∗
            memRegion (s0.sp - 80#64) 24 ∗
            (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
            (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
            (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
            (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
            (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
            (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
            (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
            A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
            A.pool lim st_pre s_mid := by
        sep_ac_rfl
      rw [hre2] at hall
      simpa [sepConj_assoc] using hall
    have hm_mid_orig : s_mid.mem ⊨
        ((((((s0.sp - 80#64) ↦₆₄ vecCap) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ vecPtr) ∗
            (((s0.sp - 80#64) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ⌜bs.length ≤ vecCap.toNat ∧ vecCap.toNat < 2 ^ 63 ∧ vecPtr ≠ 0⌝ ∗
            (if vecCap = 0 then emp
             else A.live vecPtr vecCap.toNat 1 ∗ (vecPtr ↦ₛ bs) ∗
               memRegion (vecPtr + BitVec.ofNat 64 bs.length) (vecCap.toNat - bs.length))) ∗
          ((x.ret ↦₆₄ okTagVec) ∗ ((x.ret + 8#64) ↦₆₄ vecCap) ∗ ((x.ret + 16#64) ↦₆₄ vecPtr) ∗
            ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ memRegion (x.ret + 32#64) 16) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) ∗ F) ∗ R') := by
      refine satisfies_of_eq ?_ hm_mid
      dsimp only [s_mid, okTagVec]
      simp only [arm64_norm, List.length_append, List.length_cons]
      sep_ac_rfl
    have hm_norm : s_mid.mem ⊨
        ((getResultAt A.repAlloc x.ret (.ok bs) ∗
          bytesAt x.dirRo x.dirA x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 80#64) (stk - 80) ∗
          memRegion (s0.sp - 80#64) 24 ∗
          (((s0.sp - 80#64) + 24#64) ↦₆₄ pathCap) ∗
          (((s0.sp - 80#64) + 32#64) ↦₆₄ pathPtr) ∗
          (((s0.sp - 80#64) + 40#64) ↦₆₄ BitVec.ofNat 64 (x.dir ++ [0x2f#8] ++ x.name).length) ∗
          (((s0.sp - 80#64) + 48#64) ↦₆₄ s0.readReg64 .fp) ∗
          (((s0.sp - 80#64) + 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          (((s0.sp - 80#64) + 64#64) ↦₆₄ s0.readReg64 .x20) ∗
          (((s0.sp - 80#64) + 72#64) ↦₆₄ s0.readReg64 .x19) ∗
          A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
          A.pool lim st_pre s_mid) ∗ F) ∗ R' :=
      satisfies_mono_rev hm_mid_orig
        (sepConj_mono_left (Q := R') (sepConj_mono_left (Q := F) hpack_ok))
    exact
      (tail_dealloc_step_p hC hstk hstk_le
        (by simp [s_mid, wp_norm, arm64_norm])
        (by simp [s_mid, wp_norm, arm64_norm, hRun])
        hs_mid_sp hAl0
        hcrl_mid
        hs_mid_x19 hs_mid_x1 hcap_pos hcap_lt
        (cs_hi_trans
          (cs_hi_of_eq
            (by simp [s_mid, wp_norm, arm64_norm]) (by simp [s_mid, wp_norm, arm64_norm])
            (by simp [s_mid, wp_norm, arm64_norm]) (by simp [s_mid, wp_norm, arm64_norm])
            (by simp [s_mid, wp_norm, arm64_norm]) (by simp [s_mid, wp_norm, arm64_norm])
            (by simp [s_mid, wp_norm, arm64_norm]) (by simp [s_mid, wp_norm, arm64_norm]))
          hcs_hi)
        ((by simp [s_mid, wp_norm, arm64_norm] :
          calleeSavedVRegs s_mid = calleeSavedVRegs s).trans hvregs)
        ⟨hr_out.1, hs_mid_tr.trans hr_out.2⟩
        hst_pre hevs_end)
      R' hm_norm hL_mid

theorem satisfies_vecU8_unpack {A : RustAlloc} {m : Memory} {a : BitVec 64}
    {p : List (BitVec 8)} {Q : SepProp}
    (hp : 0 < p.length)
    (hm : m ⊨ vecU8 A a p ∗ Q) :
    ∃ cap ptr : BitVec 64,
      0 < cap.toNat ∧ p.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧
      (m ⊨ (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 p.length)) ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ p) ∗
          memRegion (ptr + BitVec.ofNat 64 p.length) (cap.toNat - p.length))) ∗ Q) := by
  dsimp only [vecU8, vecU8At, vecHeader] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨cap, hm⟩ := hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨ptr, hm⟩ := hm
  have hpure : p.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 := by
    have hm' : m ⊨ ⌜p.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 p.length)) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ p) ∗
             memRegion (ptr + BitVec.ofNat 64 p.length) (cap.toNat - p.length))) ∗ Q) := by
      refine satisfies_of_eq ?_ hm
      sep_ac_rfl
    rw [satisfies_pure_sepConj] at hm'
    exact hm'.1
  have hpos : 0 < cap.toNat := Nat.lt_of_lt_of_le hp hpure.1
  have hne : cap ≠ 0 := by intro h0; subst h0; simp at hpos
  simp only [hne, ↓reduceIte] at hm
  refine ⟨cap, ptr, hpos, hpure.1, hpure.2.1, hpure.2.2, ?_⟩
  have hm'' : m ⊨ ⌜p.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 p.length)) ∗
        (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ p) ∗
          memRegion (ptr + BitVec.ofNat 64 p.length) (cap.toNat - p.length))) ∗ Q) := by
    refine satisfies_of_eq ?_ hm
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hm''
  exact hm''.2

theorem buf22_reassoc_14_8 (buf d0 d1 : BitVec 64) :
    ((buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6) ⊢
      ∃∗ d2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) := by
  have h16 : memRegion buf 8 ∗ memRegion (buf + 8#64) 8 = memRegion buf 16 :=
    (memRegion_split buf 8 8 (by decide)).symm
  have h22 : memRegion buf 16 ∗ memRegion (buf + 16#64) 6 = memRegion buf 22 :=
    (memRegion_split buf 16 6 (by decide)).symm
  have h14_8 : memRegion buf 22 = memRegion buf 14 ∗ memRegion (buf + 14#64) 8 :=
    memRegion_split buf 14 8 (by decide)
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion buf d0)
      (sepConj_mono_left (pointsTo64_entails_memRegion (buf + 8#64) d1))) ?_
  rw [← sepConj_assoc, h16, h22, h14_8, ProofLib.memRegion_eight (buf + 14#64),
    sepExists_sepConj_right]
  exact Entails.refl _

theorem buf22_reassoc_14_8_rest (buf d0 d1 : BitVec 64) (Q : SepProp) :
    ((buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6 ∗ Q) ⊢
    ((∃∗ d2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2)) ∗ Q) := by
  simpa [sepConj_assoc] using sepConj_mono_left (Q := Q) (buf22_reassoc_14_8 buf d0 d1)

theorem buf22_merge_14_8 (buf d2 : BitVec 64) :
    (memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2)) ⊢ memRegion buf 22 := by
  rw [show (22 : Nat) = 14 + 8 from rfl, memRegion_split buf 14 8 (by decide)]
  exact sepConj_mono_right (pointsTo64_entails_memRegion (buf + 14#64) d2)

end LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
