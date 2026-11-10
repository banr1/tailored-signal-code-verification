/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common

/-!
# Relocatable `.keepsFs` Call Wrappers for `main` Hop M5 (Block `617`)

Provides `.keepsFs` `SepWPp` call wrappers on Block `617` (`mProgPlaced H`) for the allocator shim,
`__rust_alloc`, writable and read-only `memcpy`, `do_reserve_and_handle`, `write_file`, and
`__rust_dealloc`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops.LoopDrop

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint DoReserveNorm
open CryptoVerification.SignalSession.Cli.Path.Helpers

/-- Call `__rust_no_alloc_shim_is_unstable_v2` with full sub-stack `stackAt fsp (stk - mainFrameSize)`. -/
theorem m5_call_shim_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {stk retOff : Nat}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ lsRustNoAllocShimSymCli)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hP : P ⊢ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := ())
    (hA.shim_rocl (prog := lsProg_617 H) (i := 617) extHookStack (by decide) (by decide))
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, withStack, sessionShimSpec]
    rw [emp_sepConj, hsp]
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    dsimp only [Spec.keepsFs, withStack, sessionShimSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun htr => ?_
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    refine SepWPp.weaken_pre ?_ (hnext sm hbase hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)

/-- Call `__rust_alloc(size, 1)` with full sub-stack `stackAt fsp (stk - mainFrameSize)`. -/
theorem m5_call_alloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {stk size retOff : Nat}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hs0tr : s0.trace = [])
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hlay : LayoutOk size 1)
    (hpc : s.pc = lsρ lsRustAllocSymCli)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : (s.readReg64 .x0).toNat = size)
    (hx1 : (s.readReg64 .x1).toNat = 1)
    (hP : P ⊢ A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hoom_next : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.readReg64 .x0 = 0#64 →
      allocFailedIn s0 sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp (mainOom s0))
    (halloc_next : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.readReg64 .x0 ≠ 0#64 →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (size, 1)) (main_alloc_fs_placed_ok hA)
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hlay⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, rustAllocSpecWithStack]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    by_cases h0 : sm.readReg64 .x0 = 0#64
    · simp only [BitVec.ofNat_eq_ofNat, h0, ↓reduceIte, sepConj_assoc]
      have hpure :
          A.pool ∗ stackAt fsp extHookStack ∗ ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - extHookStack) ∗ F =
          ⌜sm.trace = s.trace ++ [allocFailedEvent]⌝ ∗
            (A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗ F) := by
        rw [hsplit]; ac_rfl
      rw [hpure]
      refine SepWPp.pure_elim fun htr => ?_
      have haf : allocFailedIn s0 sm :=
        allocFailedIn_mono_left (by simp [hs0tr]) (allocFailedIn_of_eq htr).1
      exact hoom_next sm hbase h0 haf
    · simp only [BitVec.ofNat_eq_ofNat, h0, ↓reduceIte, sepConj_assoc]
      have hpure :
          A.pool ∗ stackAt fsp extHookStack ∗
            ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - extHookStack) ∗ F =
          ⌜(sm.readReg64 .x0).toNat % 1 = 0 ∧ sm.trace = s.trace⌝ ∗
            (A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
              A.live (sm.readReg64 .x0) size 1 ∗ memRegion (sm.readReg64 .x0) size ∗ F) := by
        rw [hsplit]; ac_rfl
      rw [hpure]
      refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
      exact halloc_next sm hbase h0 hfs htr hcsm

/-- Call `memcpy(dst, src, bs.length)` with writable `(src ↦ₛ bs)` and `.keepsFs`. -/
theorem m5_call_memcpy_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {stk retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ memcpyName)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hP : P ⊢ memRegion dst bs.length ∗ (src ↦ₛ bs) ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (dst, src, bs))
    (hA.session_memcpy_region_rocl (prog := lsProg_617 H) (i := 617) extHookStack (by decide) (by decide))
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm hbase hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)

/-- Call `memcpy(dst, src, bs.length)` with read-only `(src ↦ᵣ bs)` (`MainMemcpyROFsPlaced`) at `M+0x894`. -/
theorem m5_call_memcpy_ro_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {stk retOff : Nat}
    {dst src : BitVec 64} {bs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : MainMemcpyROFsPlaced H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ memcpyName)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hlen : bs.length ≤ 2 ^ 64)
    (hP : P ⊢ memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        ((dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (dst, src, bs)) hro
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionROSpec]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlen⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, withStack, sessionMemcpyRegionROSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm hbase hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)

/-- Call `do_reserve_and_handle [local#11]` (`hc.reserve1`, `.keepsFs`), discharging its OOM panic
internally via `hs0tr` + `hpanic`. -/
theorem m5_call_reserve1_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser}
    {hookStack resStack stk additional retOff : Nat}
    {v curCap curPtr : BitVec 64} {curBs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hs0tr : s0.trace = [])
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hstk : mainFrameSize + resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    (hpc : s.pc = lsmpl.base 561)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P ⊢ vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      InMainPlaced CodeOk s0 sm retOff →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional))
          newPtr curBs ∗ A.pool ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := resStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (main_reserve1_placed_ok hc) hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - resStack) ∗ F)
    ?_ (hpanic := ?_) (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, doReserveSpecOf]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf R' _ hp
    dsimp only [Spec.keepsFs, doReserveSpecOf, doReserveSpec] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    exact hpanic sf _ (allocFailedIn_mono_left (by simp [hs0tr]) hp.1.1)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, doReserveSpecOf]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun htr => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm newPtr hbase hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)

/-- Call `write_file(pathA, path, buf, bs)` (`hio.writeFile`). -/
theorem m5_call_write_file_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {io : IoModel}
    {hookStack stk retOff : Nat}
    {pathA buf : BitVec 64} {path bs : List (BitVec 8)}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hio : MainIoPlaced A H io hookStack)
    (hstk : mainFrameSize + hookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = lsρ lsWriteFileSym)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = pathA)
    (hx1 : (s.readReg64 .x1).toNat = path.length)
    (hx2 : s.readReg64 .x2 = buf)
    (hx3 : (s.readReg64 .x3).toNat = bs.length)
    (hlen : path.length < 2 ^ 32)
    (hok : io.pathOk path)
    (hP : P ⊢ (pathA ↦ₛ path) ∗ (buf ↦ₛ bs) ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      (match io.wr s.fs.files path bs with
       | some F' => sm.readReg64 .x0 = 0#64 ∧ sm.fs.files = F'
       | none => sm.readReg64 .x0 = 1#64 ∧ sm.fs.files = s.fs.files) →
      s.trace <+: sm.trace →
      ProcessOutcome.traceStreamBytes .stdout sm.trace =
        ProcessOutcome.traceStreamBytes .stdout s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        ((pathA ↦ₛ path) ∗ (buf ↦ₛ bs) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := hookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := WriteFileGhost.mk pathA path buf bs)
    (main_writeFile_placed_ok hio) hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - hookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [writeFileSpecPlaced]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hx3, hlen, hok⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [writeFileSpecPlaced]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hwr, htr, hout⟩ => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm hbase hwr htr hout hcsm)
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)

/-- Call `__rust_dealloc(ptr, size, align)` (`hA.dealloc`, `.keepsFs`). -/
theorem m5_call_dealloc_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {stk size align retOff : Nat}
    {ptr : BitVec 64}
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hstk : mainFrameSize + extHookStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hlay : LayoutOk size align)
    (hpc : s.pc = lsρ lsRustDeallocSymCli)
    (hrun : s.status = .Running)
    (hinv : CodeOk s.mem)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hfp : s.readReg64 .fp = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hs0_align : s0.spAligned = true)
    (hlr : s.readReg64 .lr = mPcPlaced retOff)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hP : P ⊢ A.live ptr size align ∗ memRegion ptr size ∗ A.pool ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm retOff →
      sm.fs = s.fs →
      sm.trace = s.trace →
      CalleeSavedPreserved s sm →
      SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) sm
        (A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hal : s.spAligned = true := by
    simp only [State.spAligned, hsp, mainFrameSize]
    exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs0_align
  have hsplit := stackAt_split_ge fsp (n := extHookStack) (m := stk - mainFrameSize)
    (by m5_omega) (by m5_omega)
  refine main_call_rocl (x := (ptr, size, align)) (main_dealloc_fs_placed_ok hA)
    hinv hpc hrun hal hlr
    (F := memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
      (stk - mainFrameSize - extHookStack) ∗ F)
    ?_ (hnext := ?_)
  · refine Entails.trans hP ?_
    rw [hsplit]
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    simp only [hsp, sepConj_assoc]
    apply Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sm hinv_m hpcm hrunm hspm hcsm
    have hbase : InMainPlaced CodeOk s0 sm retOff :=
      { pc := hpcm, run := hrunm, sp := hspm.trans hsp,
        fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hfp, inv := hinv_m,
        vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hvregs, spAligned := hs0_align }
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun hfs => ?_
    refine SepWPp.pure_elim fun htr => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm hbase hfs htr hcsm)
    rw [hsplit]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
