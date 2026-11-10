/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5IfacePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSitesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MovesLayout
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Frame Open/Close and `memcpy` Helpers for `main` M5 Moves (Block `617`)

Relocatable `[LibsignalPlacement]` `locals` open/mid/close bridges (`m5CellsPlaced` to
`m5LoopCellsPlaced … 0`) and `.keepsFs` `memcpy` call helper on Block `617`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SpqrV1.Alloc

namespace M5MovesHelpers

/-! ## 1. Placed `locals` Open / Mid / Close Bridges (`m5CellsPlaced` → `m5LoopCellsPlaced … 0`) -/

/-- Untouched uninitialized stack sub-gaps inside `locals fsp` during M5's payload moves:
`[0x20, 0x50)`, `[0x60, 0x78)`, and `[0x450, 0x480)`. -/
def m5LocalsRestPlaced (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x20#64) 0x30 ∗
    memRegion (fsp + 0x60#64) 0x18 ∗
    memRegion (fsp + 0x450#64) 0x30

/-- Existential bundle produced when opening `locals fsp (m5CellsPlaced A fsp inPtr g out)`. -/
structure M5OpenVarsPlaced where
  ws : StoresWords
  dstWs : StoresWords
  outCap : BitVec 64
  outPtr : BitVec 64
  u00 : BitVec 64
  u08 : BitVec 64
  u10 : BitVec 64
  u18 : BitVec 64
  u58 : BitVec 64

/-- Opens `locals fsp (m5CellsPlaced A fsp inPtr g out)` into the spill cells (`0x00..0x18`,
`0x50`, `0x58`), `memcpy` source/destination slices, `dstWs` words at `fsp + 0x310`, `storesHeap`,
`ownedBytes`, and `m5LocalsRestPlaced`. -/
theorem m5_locals_open_placed (A : RustAlloc) (fsp inPtr : BitVec 64)
    (g : StoresGhost) (out : List (BitVec 8)) :
    locals fsp (m5CellsPlaced A fsp inPtr g out) ⊢
      ∃∗ v : M5OpenVarsPlaced,
        (fsp ↦₆₄ v.u00) ∗
          ((fsp + 0x08#64) ↦₆₄ v.u08) ∗
          ((fsp + 0x10#64) ↦₆₄ v.u10) ∗
          ((fsp + 0x18#64) ↦₆₄ v.u18) ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ((fsp + 0x58#64) ↦₆₄ v.u58) ∗
          memRegion (fsp + 0x78#64) 0x140 ∗
          ((fsp + 0x1b8#64) ↦ₛ storesBytes v.ws) ∗
          ((fsp + 0x2f8#64) ↦₆₄ v.outCap) ∗
          ((fsp + 0x300#64) ↦₆₄ v.outPtr) ∗
          ((fsp + 0x308#64) ↦₆₄ BitVec.ofNat 64 out.length) ∗
          storesStackAt (fsp + 0x310#64) v.dstWs ∗
          m5LocalsRestPlaced fsp ∗
          storesHeap A v.ws g ∗
          ownedBytes A v.outCap v.outPtr (BitVec.ofNat 64 out.length) out := by
  have g0 :
      memRegion (fsp + 0#64) 0x50 =
        memRegion fsp 8 ∗
          memRegion (fsp + 0x08#64) 8 ∗
          memRegion (fsp + 0x10#64) 8 ∗
          memRegion (fsp + 0x18#64) 8 ∗
          memRegion (fsp + 0x20#64) 0x30 := by
    have s1 := memRegion_split fsp 0x08 0x48 (by decide)
    have s2 := memRegion_split (fsp + 0x08#64) 8 0x40 (by decide)
    have s3 := memRegion_split (fsp + 0x10#64) 8 0x38 (by decide)
    have s4 := memRegion_split (fsp + 0x18#64) 8 0x30 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2 s3 s4
    rw [BitVec.add_zero, s1, s2, s3, s4]
  have g1 :
      memRegion (fsp + 0x58#64) 0x160 =
        memRegion (fsp + 0x58#64) 8 ∗
          memRegion (fsp + 0x60#64) 0x18 ∗
          memRegion (fsp + 0x78#64) 0x140 := by
    have s1 := memRegion_split (fsp + 0x58#64) 0x08 0x158 (by decide)
    have s2 := memRegion_split (fsp + 0x60#64) 0x18 0x140 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2
    rw [s1, s2]
  have g2 :
      memRegion (fsp + 0x310#64) 0x170 =
        memRegion (fsp + 0x310#64) 0x140 ∗ memRegion (fsp + 0x450#64) 0x30 := by
    have s := memRegion_split (fsp + 0x310#64) 0x140 0x30 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at s
    exact s
  dsimp only [locals, m5CellsPlaced, localsFrom, cell, runResSize, runOkAt]
  change (memRegion (fsp + 0#64) 0x50 ∗
    ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
    (memRegion (fsp + 0x58#64) 0x160 ∗
      (storesAt A (fsp + 0x1b8#64) g ∗ vecU8 A (fsp + 0x1b8#64 + 0x140#64) out) ∗
      memRegion (fsp + 0x310#64) 0x170)) ⊢ _
  have h2f8 : fsp + 0x1b8#64 + 0x140#64 = fsp + 0x2f8#64 := by bv_arith
  rw [g0, g1, g2, h2f8,
      ProofLib.memRegion_eight fsp,
      ProofLib.memRegion_eight (fsp + 0x08#64),
      ProofLib.memRegion_eight (fsp + 0x10#64),
      ProofLib.memRegion_eight (fsp + 0x18#64),
      ProofLib.memRegion_eight (fsp + 0x58#64)]
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono
            (sepConj_mono
              (storesAt_unpack A (fsp + 0x1b8#64) g)
              (vecU8_unpack_ownedBytes A (fsp + 0x2f8#64) out))
            (sepConj_mono_left (memRegion_320_entails_exists_storesWords (fsp + 0x310#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro dstWs
  apply Entails.sepExists_elim; intro outCap
  apply Entails.sepExists_elim; intro outPtr
  apply Entails.sepExists_elim; intro ws
  apply Entails.sepExists_elim; intro u58
  apply Entails.sepExists_elim; intro u18
  apply Entails.sepExists_elim; intro u10
  apply Entails.sepExists_elim; intro u08
  apply Entails.sepExists_elim; intro u00
  refine Entails.sepExists_right ⟨ws, dstWs, outCap, outPtr, u00, u08, u10, u18, u58⟩ ?_
  rw [storesStackAt_eq_bytes (fsp + 0x1b8#64) ws]
  have h300 : fsp + 0x2f8#64 + 0x08#64 = fsp + 0x300#64 := by bv_arith
  have h308 : fsp + 0x2f8#64 + 0x10#64 = fsp + 0x308#64 := by bv_arith
  rw [h300, h308]
  unfold m5LocalsRestPlaced
  exact Entails.of_eq (by ac_rfl)

/-- Right before `M+0x8a4`'s `memcpy(fsp + 0x1c8 ← fsp + 0x310, 320)`, merge `[0x1c8, 0x2f8)` with
`[0x2f8, 0x308)` into `memRegion (fsp + 0x1c8) 0x140`, expose `(fsp + 0x310) ↦ₛ storesBytes ws`, and
pack dead scratch regions (`[0x60, 0x1c8)` and `[0x308, 0x310)`) together with `m5LocalsRestPlaced`
into `m5PreMemcpy2RestPlaced fsp`. -/
def m5PreMemcpy2RestPlaced (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x20#64) 0x30 ∗
    memRegion (fsp + 0x60#64) 0x168 ∗
    memRegion (fsp + 0x308#64) 0x08 ∗
    memRegion (fsp + 0x450#64) 0x30

theorem m5_pre_second_memcpy_placed (fsp outCap outPtr outLen : BitVec 64) (ws : StoresWords) :
    storesStackAt (fsp + 0x78#64) ws ∗
      memRegion (fsp + 0x1b8#64) 0x08 ∗
      ((fsp + 0x1c0#64) ↦₆₄ 8#64) ∗
      memRegion (fsp + 0x1c8#64) 0x130 ∗
      ((fsp + 0x2f8#64) ↦₆₄ outCap) ∗
      ((fsp + 0x300#64) ↦₆₄ outPtr) ∗
      ((fsp + 0x308#64) ↦₆₄ outLen) ∗
      storesStackAt (fsp + 0x310#64) ws ∗
      m5LocalsRestPlaced fsp ⊢
      memRegion (fsp + 0x1c8#64) 0x140 ∗
        ((fsp + 0x310#64) ↦ₛ storesBytes ws) ∗
        m5PreMemcpy2RestPlaced fsp := by
  unfold m5LocalsRestPlaced m5PreMemcpy2RestPlaced
  rw [storesStackAt_eq_bytes (fsp + 0x310#64) ws]
  refine Entails.trans
    (sepConj_mono (storesStackAt_entails_memRegion (fsp + 0x78#64) ws)
      (sepConj_mono_right
        (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x1c0#64) 8#64)
          (sepConj_mono_right
            (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x2f8#64) outCap)
              (sepConj_mono (pointsTo64_entails_memRegion (fsp + 0x300#64) outPtr)
                (sepConj_mono_left (pointsTo64_entails_memRegion (fsp + 0x308#64) outLen)))))))) ?_
  have mDst :
      memRegion (fsp + 0x1c8#64) 0x140 =
        memRegion (fsp + 0x1c8#64) 0x130 ∗
          memRegion (fsp + 0x2f8#64) 0x08 ∗
          memRegion (fsp + 0x300#64) 0x08 := by
    have s1 := memRegion_split (fsp + 0x1c8#64) 0x130 0x10 (by decide)
    have s2 := memRegion_split (fsp + 0x2f8#64) 0x08 0x08 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2
    rw [s1, s2]
  have mMid :
      memRegion (fsp + 0x60#64) 0x168 =
        memRegion (fsp + 0x60#64) 0x18 ∗
          memRegion (fsp + 0x78#64) 0x140 ∗
          memRegion (fsp + 0x1b8#64) 0x08 ∗
          memRegion (fsp + 0x1c0#64) 0x08 := by
    have s1 := memRegion_split (fsp + 0x60#64) 0x18 0x150 (by decide)
    have s2 := memRegion_split (fsp + 0x78#64) 0x140 0x10 (by decide)
    have s3 := memRegion_split (fsp + 0x1b8#64) 0x08 0x08 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2 s3
    rw [s1, s2, s3]
  rw [mDst, mMid]
  exact Entails.of_eq (by ac_rfl)

/-- After `M+0x8a4`'s `memcpy(fsp + 0x1c8 ← fsp + 0x310, 320)` and `M+0x8b4`'s `str x8, [sp, #0x58]`,
reassemble `locals fsp (m5LoopCellsPlaced A fsp outCap outPtr outLen inCap inPtr g 0)`. -/
theorem m5_locals_close_placed (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr v58 : BitVec 64)
    (ws : StoresWords) (g : StoresGhost) :
    (fsp ↦₆₄ outLen) ∗
      ((fsp + 0x08#64) ↦₆₄ outCap) ∗
      ((fsp + 0x10#64) ↦₆₄ inCap) ∗
      ((fsp + 0x18#64) ↦₆₄ outPtr) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ((fsp + 0x58#64) ↦₆₄ v58) ∗
      ((fsp + 0x1c8#64) ↦ₛ storesBytes ws) ∗
      ((fsp + 0x310#64) ↦ₛ storesBytes ws) ∗
      m5PreMemcpy2RestPlaced fsp ∗
      storesHeap A ws g ⊢
      locals fsp (m5LoopCellsPlaced A fsp outCap outPtr outLen inCap inPtr g 0) := by
  rw [m5LoopCellsPlaced_zero_eq, ← storesStackAt_eq_bytes (fsp + 0x1c8#64) ws]
  have hsrc : ((fsp + 0x310#64) ↦ₛ storesBytes ws) ⊢ memRegion (fsp + 0x310#64) 0x140 := by
    have h := pointsToBytes_entails_memRegion (storesBytes ws) (fsp + 0x310#64)
      (by simp [storesBytes_length])
    rwa [storesBytes_length] at h
  have hv58 : ((fsp + 0x58#64) ↦₆₄ v58) ⊢ memRegion (fsp + 0x58#64) 0x08 :=
    pointsTo64_entails_memRegion (fsp + 0x58#64) v58
  refine Entails.trans
    (Entails.of_eq (show
      (fsp ↦₆₄ outLen) ∗ ((fsp + 0x08#64) ↦₆₄ outCap) ∗
        ((fsp + 0x10#64) ↦₆₄ inCap) ∗ ((fsp + 0x18#64) ↦₆₄ outPtr) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗ ((fsp + 0x58#64) ↦₆₄ v58) ∗
        storesStackAt (fsp + 0x1c8#64) ws ∗ ((fsp + 0x310#64) ↦ₛ storesBytes ws) ∗
        m5PreMemcpy2RestPlaced fsp ∗ storesHeap A ws g =
      (storesStackAt (fsp + 0x1c8#64) ws ∗ storesHeap A ws g) ∗
        ((fsp + 0x310#64) ↦ₛ storesBytes ws) ∗
        ((fsp + 0x58#64) ↦₆₄ v58) ∗
        ((fsp ↦₆₄ outLen) ∗ ((fsp + 0x08#64) ↦₆₄ outCap) ∗
          ((fsp + 0x10#64) ↦₆₄ inCap) ∗ ((fsp + 0x18#64) ↦₆₄ outPtr) ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗ m5PreMemcpy2RestPlaced fsp) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono (storesAt_repack A (fsp + 0x1c8#64) ws g)
      (sepConj_mono hsrc (sepConj_mono_left hv58))) ?_
  unfold m5PreMemcpy2RestPlaced
  have mMid58 :
      memRegion (fsp + 0x58#64) 0x170 =
        memRegion (fsp + 0x58#64) 0x08 ∗ memRegion (fsp + 0x60#64) 0x168 := by
    have s1 := memRegion_split (fsp + 0x58#64) 0x08 0x168 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1
    exact s1
  have mTail :
      memRegion (fsp + 0x308#64) 0x178 =
        memRegion (fsp + 0x308#64) 0x08 ∗
          memRegion (fsp + 0x310#64) 0x140 ∗
          memRegion (fsp + 0x450#64) 0x30 := by
    have s1 := memRegion_split (fsp + 0x308#64) 0x08 0x170 (by decide)
    have s2 := memRegion_split (fsp + 0x310#64) 0x140 0x30 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at s1 s2
    rw [s1, s2]
  dsimp only [locals, m6CellsPlaced, cell, List.cons_append, List.nil_append, localsFrom]
  simp only [Nat.reduceAdd, Nat.reduceSub]
  rw [BitVec.add_zero, mMid58, mTail,
      memRegion_zero fsp,
      memRegion_zero (fsp + 0x08#64),
      memRegion_zero (fsp + 0x10#64),
      memRegion_zero (fsp + 0x18#64)]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. `.keepsFs` `memcpy` Call-Site Helper for `main` on Block `617` -/

theorem sepWP_seq_placed_frame [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P_in P P' F : SepProp} {post : State → Prop}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (hP : P_in ⊢ P ∗ F)
    (h : SepWP prog mid s P (fun s1 P1 => post s1 ∧ P1 = P') (fun _ => ⌜False⌝))
    (hk : ∀ s1 : State, CodeOk s1.mem → s1.pc = mid → s1.status = .Running → post s1 →
      SepWPp prog ret s1 (P' ∗ F) Q Qp oom) :
    SepWPp prog ret s P_in Q Qp oom := by
  intro R hm hL
  have hm0 : s.mem ⊨ P ∗ (F ∗ R) := by
    simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hP) hm
  rcases h.elim hm0 hL with ⟨s1, hsteps, ⟨hpc1, hrun1, P1, hm1, hpost1, rfl⟩ | ⟨_, hfalse⟩⟩
  · obtain ⟨sf, hsteps2, hout⟩ :=
      hk s1 (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) hpc1 hrun1 hpost1 R
        (by simpa only [sepConj_assoc] using hm1) (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout⟩
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem main_sessionMemcpyRegionFs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hA : AllocContractsFsPlaced A H) :
    subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl (withStack sessionMemcpyRegionSpec extHookStack).keepsFs) :=
  hA.session_memcpy_region_rocl (prog := lsProg_617 H) (i := 617)
    extHookStack (by decide) (by decide)

/-- Step a `bl memcpy` call in `main` under `(withStack sessionMemcpyRegionSpec extHookStack).keepsFs`,
preserving `fs`, `trace`, `sp`, `CalleeSavedPreserved`, and `CodeOk`, and copying `src ↦ₛ bs`
into `memRegion dst bs.length`. -/
theorem step_memcpy_region_fs_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {prog : Program} {memcpyTarget fsp retPc ret dst src : BitVec 64} {bs : List (BitVec 8)}
    {fs0 : FsState} {tr0 : List TraceEvent}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hmc : subroutine_ok prog memcpyTarget
      (withLsRoCl lsmpl (withStack sessionMemcpyRegionSpec extHookStack).keepsFs))
    (hinv : CodeOk s.mem)
    (hpc : s.pc = memcpyTarget)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hal : s.spAligned = true)
    (hlr : s.readReg64 .lr = retPc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hfs : s.fs = fs0)
    (htr : s.trace = tr0)
    (hP : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack ∗ F)
    (hk : ∀ sm : State,
      CodeOk sm.mem →
      sm.pc = retPc →
      sm.status = .Running →
      sm.sp = fsp →
      CalleeSavedPreserved s sm →
      sm.fs = fs0 →
      sm.trace = tr0 →
      SepWPp prog ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt fsp extHookStack ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp prog ret s P Q Qp (mainOom s0) := by
  refine main_call_rocl (dst, src, bs) hmc hinv hpc hrun hal hlr
    (F := F)
    (hP := ?_)
    (hpanic := fun _ _ _ hp => by
      dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec] at hp
      exact (not_satisfies_false_sepConj hp).elim)
    (hexit := fun _ _ _ _ he => by
      dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec] at he
      exact not_satisfies_false_sepConj he)
    (hoom := fun _ _ _ ho => by
      dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec] at ho
      exact (not_satisfies_false_sepConj ho).elim)
    (hnext := ?_)
  · dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp]
    refine Entails.trans hP ?_
    have hpure :
        ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ =
        (emp : SepProp) := by
      simp [hx0, hx1, hx2]
    rw [hpure, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec]
    rw [hsp]
    have hpure_pull :
        ((⌜sm.fs = s.fs⌝ ∗
          (⌜sm.readReg64 .x0 = dst ∧ sm.trace = s.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗
          stackAt fsp extHookStack) ∗ F) =
        ⌜sm.fs = s.fs⌝ ∗
          (⌜sm.readReg64 .x0 = dst ∧ sm.trace = s.trace⌝ ∗
            (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ stackAt fsp extHookStack ∗ F)) := by
      ac_rfl
    rw [hpure_pull]
    refine SepWPp.pure_elim fun hfsm => ?_
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    exact hk sm hinv_m hpcm hrunm hspm hcsm (hfsm.trans hfs) (htrm.trans htr)

end M5MovesHelpers

end CryptoVerification.SignalSession.Cli.MainHops
