/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5DropStepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Write-Error Cleanup Path `m5_drop_placed` (Block `617`)

Verifies `main`'s write-error cleanup path (`M+0xbcc / 0xbdc / 0xbf4 → M+0xc5c → M+0xf70`) on
Block `617` under `[LibsignalPlacement]`, dropping the temporary path, active `Dir` entries/buffer,
and remaining `Dir`s into `AtM6Placed … false`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout
open M5DropPlacedHelpers

/-! ## 1. Step B: Current `Dir` Buffer Cleanup `0xbf4 → 0xc5c` -/

theorem m5_cur_dir_to_c5c_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks}
    {ret : BitVec 64} {s0 s : State} {stk k : Nat}
    {outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64}
    {g : StoresGhost} {curEntries : List (List (BitVec 8) × List (BitVec 8))}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hA : AllocContractsFsPlaced A H)
    (hext : mainFrameSize + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64)
    (hne : curEntries ≠ [])
    (hs : InMainPlaced CodeOk s0 s 0xbf4)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 curEntries.length)
    (hnext : ∀ sm : State,
      InMainPlaced CodeOk s0 sm 0xc5c →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 22#5) = 1#64 →
      sm.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (k + 1) →
      sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      sm.readReg64 (.gpr 25#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x1c8#64 →
      sm.fs = s.fs → sm.trace = s.trace →
      SepWPp (mProgPlaced H) ret sm
        (locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5ErrCellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
          A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (vecBuf A 48 8 (dirEntryAt A) curCap curPtr curEntries ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m5ErrCellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize)
            outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
        A.pool ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
      Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hsp : s.sp = fsp := hs.sp
  unfold vecBuf
  simp only [sepConj_assoc]
  apply SepWPp.pure_elim
  rintro ⟨hlen, hcap_lt, _⟩
  have hpos : 0 < curEntries.length := List.length_pos_of_ne_nil hne
  have hcap_ne : curCap ≠ 0#64 := by
    intro hc0; subst hc0; change curEntries.length ≤ 0 at hlen; omega
  have hcap_ne0 : curCap ≠ 0 := hcap_ne
  simp only [hcap_ne0, ite_false, sepConj_assoc]
  obtain ⟨Ctx, hopen⟩ :=
    m5ErrCellsPlaced_open_spills A s.sp outCap outPtr outLen inCap inPtr curCap curPtr g k
  refine SepWPp.weaken_pre (Entails.of_eq (show
    A.live curPtr (curCap.toNat * 48) 8 ∗
      arrayAt (dirEntryAt A) 48 curPtr curEntries ∗
      memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
        ((curCap.toNat - curEntries.length) * 48) ∗
      locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
      A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗ F =
    ((s.sp + 32#64) ↦₆₄ curCap) ∗
      ((s.sp + 40#64) ↦₆₄ curPtr) ∗
      ((s.sp + 48#64) ↦₆₄ (s.sp + 0x1c8#64)) ∗
      (((s.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        (arrayAt (dirEntryAt A) 48 curPtr curEntries ∗
          A.pool ∗ stackAt s.sp (stk - mainFrameSize) ∗
          (A.live curPtr (curCap.toNat * 48) 8 ∗
            memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
              ((curCap.toNat - curEntries.length) * 48) ∗
            Ctx ∗ F))) by
      dsimp +zetaDelta only [fsp]
      rw [← hs.sp, hopen]
      ac_rfl)) ?_
  apply seq_sepWP_pl (mid := mPcPlaced (0xc04 + 12))
  refine step_bf4_pre_placed (fnBase := (blkPl_617).base) hs.pc hs.run hs.spAligned_state
    m5_drop_fetch_placed m5_drop_fetch_placed
    m5_drop_fetch_placed m5_drop_fetch_placed ?_
  intro s1 hpcm1 hrunm1 hsp1 hfp1 hm1 hsym1 hv1 hfs1 htr1
    hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 _ _
  have hs1 : InMainPlaced CodeOk s0 s1 (0xc04 + 12) :=
    InMainPlaced.step_pure hs hpcm1 hrunm1 hsp1 hfp1 hm1
      (by simp only [calleeSavedVRegs, hv1])
  refine SepWPp.weaken_pre (P' :=
    arrayAt (dirEntryAt A) 48 curPtr curEntries ∗
      A.pool ∗ stackAt s1.sp (stk - mainFrameSize) ∗
      (A.live curPtr (curCap.toNat * 48) 8 ∗
        memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
          ((curCap.toNat - curEntries.length) * 48) ∗
        locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗ F))
    (Entails.of_eq (by
      dsimp +zetaDelta only [fsp]
      rw [hsp1, ← hs.sp, hopen]
      ac_rfl)) ?_
  refine m5_drop_loop_body_0xc04_placed hA hext hstk64 hne (by omega) hs1
    (hx20_1.trans hx20) hx21_1 ?_
  intro s2 hs2 hkeeps hfs2 htr2
  have hx19_2 : s2.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) :=
    (hkeeps 19#5 (by decide) (by decide) (by decide) (by decide)).trans hx19_1
  have hx22_2 : s2.readReg64 (.gpr 22#5) = curPtr :=
    (hkeeps 22#5 (by decide) (by decide) (by decide) (by decide)).trans hx22_1
  have hx23_2 : s2.readReg64 (.gpr 23#5) = curCap :=
    (hkeeps 23#5 (by decide) (by decide) (by decide) (by decide)).trans hx23_1
  have hx24_2 : s2.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) :=
    (hkeeps 24#5 (by decide) (by decide) (by decide) (by decide)).trans hx24_1
  have hx25_2 : s2.readReg64 (.gpr 25#5) = fsp + 0x1c8#64 :=
    (hkeeps 25#5 (by decide) (by decide) (by decide) (by decide)).trans
      (hx25_1.trans (congrArg (· + 0x1c8#64) hsp))
  have hbuf_merge :
      memRegion curPtr (curEntries.length * 48) ∗
        memRegion (curPtr + BitVec.ofNat 64 (curEntries.length * 48))
          ((curCap.toNat - curEntries.length) * 48) =
        memRegion curPtr (curCap.toNat * 48) :=
    (ProofLib.memRegion_split' (by omega) rfl (by omega)).symm
  have hlay := layoutOk_dirBuf_of_cap_ne_zero hcap_ne hcap_lt
  let bl : BitVec 64 := (lsρ lsRustDeallocSymCli - (blkPl_617).base) - 3152#64
  have hbl : (blkPl_617).base + 3152#64 + bl = lsρ lsRustDeallocSymCli :=
    mPcPlaced_bl_dealloc 3152
  apply seq_sepWP_pl (mid := (blkPl_617).base + 3152#64 + bl)
  refine step_c3c_dealloc_placed (fnBase := (blkPl_617).base) (bl := bl)
    hs2.pc hs2.run hx22_2 hx23_2 hcap_ne
    m5_drop_fetch_placed m5_drop_fetch_placed
    m5_drop_fetch_placed m5_drop_fetch_placed
    m5_drop_fetch_placed m5_drop_fetch_placed ?_
  intro s2' hpcm2 hrunm2 hsp2' hfp2' hm2' hsym2' hv2' hfs2' htr2'
    hlr2' hx0_2 hx1_2 hx2_2 hx19_2' hx24_2' hx25_2' _ _
  refine step_dealloc_placed (sub := stk - mainFrameSize)
    (F := locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗ F)
    hA (by omega) (by omega)
    (codeOk_pure hs2.inv hm2') (hpcm2.trans hbl) hrunm2
    (by simpa only [State.spAligned, hsp2'] using hs2.spAligned_state)
    hlr2' hx0_2
    ((congrArg BitVec.toNat hx1_2).trans (mul48_toNat_of_lt curCap hcap_lt))
    (by rw [hx2_2]; decide)
    hlay
    ?_ ?_
  · exact Entails.of_eq (by
      rw [hsp2', hs2.sp, hs1.sp, ← hbuf_merge]
      ac_rfl)
  · intro s3 hpcm3 hrunm3 hspm3 hcsm3 hinv3 hfs3 htr3
    have hs3 : InMainPlaced CodeOk s0 s3 0xc54 :=
      hs2.mk_step hpcm3 hrunm3 (hspm3.trans hsp2')
        (hcsm3.2.2.2.2.2.2.2.2.2.2.1.trans hfp2') hinv3
        (hcsm3.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [calleeSavedVRegs, hv2']))
    refine SepWPp.weaken_pre (P' :=
      ((s3.sp + 56#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
        (((s.sp + 32#64) ↦₆₄ curCap) ∗
          ((s.sp + 40#64) ↦₆₄ curPtr) ∗
          ((s.sp + 48#64) ↦₆₄ (s.sp + 0x1c8#64)) ∗
          Ctx ∗ A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗ F))
      (Entails.of_eq (by
        dsimp +zetaDelta only [fsp]
        rw [hs3.sp, hsp2', hs2.sp, ← hs.sp, hopen]
        ac_rfl)) ?_
    apply seq_sepWP_pl (mid := mPcPlaced 0xc5c)
    refine step_c54_post_placed (fnBase := (blkPl_617).base) hs3.pc hs3.run hs3.spAligned_state
      m5_drop_fetch_placed m5_drop_fetch_placed ?_
    intro s4 hpcm4 hrunm4 hsp4 hfp4 hm4 hsym4 hv4 hfs4 htr4
      hx19_4 hx22_4 hx23_4 hx24_4 hx25_4 _ _
    refine SepWPp.weaken_pre (P' :=
      locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) ∗
        A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗ F)
      (Entails.of_eq (by
        dsimp +zetaDelta only [fsp]
        rw [hs3.sp, ← hs.sp, hopen]
        ac_rfl)) ?_
    exact hnext s4
      (InMainPlaced.step_pure hs3 hpcm4 hrunm4 hsp4 hfp4 hm4
        (by simp only [calleeSavedVRegs, hv4]))
      (hx19_4.trans (hcsm3.1.trans (hx19_2'.trans hx19_2)))
      hx22_4
      hx23_4
      (hx24_4.trans (hcsm3.2.2.2.2.2.1.trans (hx24_2'.trans hx24_2)))
      (hx25_4.trans (hcsm3.2.2.2.2.2.2.1.trans (hx25_2'.trans hx25_2)))
      (hfs4.trans (hfs3.trans (hfs2'.trans (hfs2.trans hfs1))))
      (htr4.trans (htr3.trans (htr2'.trans (htr2.trans htr1))))

/-! ## 2. Top-Level Write-Error Cleanup `m5_drop_placed` and `m5_drop_for_m5_placed` -/

theorem m5_drop_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks}
    {io : IoModel} {F0 : FsFiles} {tr0 : List TraceEvent}
    {g : StoresGhost} {s0 s : State} {stk n k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {out inp : List (BitVec 8)}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {curEntries : List (List (BitVec 8) × List (BitVec 8))}
    {e : M5ErrEntryPlaced}
    {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hext : mainFrameSize + extHookStack ≤ stk)
    (herr : M5LoopErrPlaced CodeOk io F0 tr0 g s0 s n buf k curEntries e)
    (hnext : ∀ sm : State,
      AtM6Placed CodeOk s0 sm false n buf →
      sm.fs = s.fs →
      sm.trace = s.trace →
      commitFiles io.wr F0 g.writes = none →
      tr0 <+: sm.trace →
      ProcessOutcome.traceStreamBytes .stdout sm.trace =
        ProcessOutcome.traceStreamBytes .stdout tr0 →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) sm
        (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap outPtr
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (m5ErrMemPlaced A s0 stk n outCap outPtr inCap inPtr buf curCap curPtr out inp ps g k curEntries e)
      Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hk : k < 8 := herr.hk
  let Rest : SepProp :=
    ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      mainSaved s0 ∗ anyHeap
  refine sepWPp_with_stk_le_two_pow_64 (s0 := s0) (stk := stk)
    (F := e.heap A ∗ vecBuf A 48 8 (dirEntryAt A) curCap curPtr curEntries ∗
      ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
      ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
      argsBuf A (BitVec.ofNat 64 n) buf ps ∗
      locals fsp (m5ErrCellsPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr g k) ∗
      A.pool ∗ anyHeap)
    (by omega)
    (Entails.of_eq (by unfold m5ErrMemPlaced; ac_rfl)) ?_
  intro hstk64
  refine SepWPp.weaken_pre (P' :=
    e.heap A ∗
      locals fsp (m5ErrCellsPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr g k) ∗
      A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗
      (vecBuf A 48 8 (dirEntryAt A) curCap curPtr curEntries ∗ Rest))
    (Entails.of_eq (by unfold m5ErrMemPlaced Rest; ac_rfl)) ?_
  refine m5_err_to_bf4_placed hA hext hstk64 hk herr.base herr.errRegs ?_
  intro s1 hs1 hx19_1 hx20_1 hx24_1 hfs1 htr1
  rw [herr.x19] at hx19_1
  rw [herr.x20] at hx20_1
  rw [herr.x24] at hx24_1
  refine SepWPp.weaken_pre (P' :=
    vecBuf A 48 8 (dirEntryAt A) curCap curPtr curEntries ∗
      locals fsp (m5ErrCellsPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr g k) ∗
      A.pool ∗ stackAt fsp (stk - mainFrameSize) ∗ Rest)
    (Entails.of_eq (by ac_rfl)) ?_
  refine m5_cur_dir_to_c5c_placed hA hext hstk64 herr.hne hs1 hx20_1 ?_
  intro s2 hs2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2 hfs2 htr2
  rw [hx19_1] at hx19_2
  rw [hx24_1] at hx24_2
  by_cases hk7 : k = 7
  · subst hk7
    apply seq_sepWP_pl (mid := mPcPlaced 0xf70)
    refine step_c5c_eq8_placed (fnBase := (blkPl_617).base) hs2.pc hs2.run hx23_2
      m5_drop_fetch_placed m5_drop_fetch_placed ?_
    intro s3 hpcm3 hrunm3 hsp3 hfp3 hm3 hsym3 hv3 hfs3 htr3
      hx19_3 hx22_3 hx24_3 _ _
    have hs3 : InMainPlaced CodeOk s0 s3 0xf70 :=
      InMainPlaced.step_pure hs2 hpcm3 hrunm3 hsp3 hfp3 hm3
        (by simp only [calleeSavedVRegs, hv3])
    have hlen8 : (storesDirs g).length ≤ 8 := Nat.le_of_eq (storesDirs_length g)
    have hdrop8 : (storesDirs g).drop 8 = [] := List.drop_of_length_le hlen8
    have hforget :
        locals fsp (m5ErrCellsPlaced A fsp outCap outPtr (BitVec.ofNat 64 out.length)
          inCap inPtr curCap curPtr g 7) ⊢
        locals fsp (m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) := by
      unfold m5ErrCellsPlaced
      have h71 : 7 + 1 = 8 := rfl
      rw [h71, hdrop8, dirsAt_nil,
        show (emp : SepProp) = memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * 8)) (0x28 * (8 - 8))
          from (memRegion_zero _).symm]
      exact locals_m5ErrCellsPlaced_forget_to_m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr (fsp + 456#64) 8#64 (m := 8) (by decide)
    refine SepWPp.weaken_pre (P' :=
      ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        locals fsp (m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap)
      (Entails.trans (sepConj_mono_left hforget)
        (Entails.of_eq (by unfold Rest; ac_rfl))) ?_
    have htr_eq : s3.trace = s.trace := htr3.trans (htr2.trans htr1)
    have hfs_eq : s3.fs = s.fs := hfs3.trans (hfs2.trans hfs1)
    exact hnext s3
      { base := hs3
        w22 := by
          have hw := hx22_3.trans hx22_2
          rw [hw]; decide
        x19 := hx19_3.trans hx19_2
        x24 := hx24_3.trans hx24_2 }
      hfs_eq htr_eq herr.commitNone
      (htr_eq.symm ▸ herr.trace)
      (by rw [htr_eq]; exact herr.stdout)
  · have hne8 : BitVec.ofNat 64 (k + 1) ≠ 8#64 :=
      ofNat_ne_of_ne_lt (by omega) (by omega) (by decide)
    apply seq_sepWP_pl (mid := mPcPlaced 0xc70)
    refine step_c5c_ne8_placed (fnBase := (blkPl_617).base) hs2.pc hs2.run hx23_2 hx25_2 hne8
      m5_drop_fetch_placed m5_drop_fetch_placed
      m5_drop_fetch_placed m5_drop_fetch_placed
      m5_drop_fetch_placed ?_
    intro s3 hpcm3 hrunm3 hsp3 hfp3 hm3 hsym3 hv3 hfs3 htr3
      hx19_3 hx22_3 hx23_3 hx24_3 hx26_3 _ _
    have hs3 : InMainPlaced CodeOk s0 s3 0xc70 :=
      InMainPlaced.step_pure hs2 hpcm3 hrunm3 hsp3 hfp3 hm3
        (by simp only [calleeSavedVRegs, hv3])
    let pre9 : List (Nat × Nat × SepProp) :=
      [cell fsp 0x0 (BitVec.ofNat 64 out.length), cell fsp 0x8 outCap, cell fsp 0x10 inCap,
       cell fsp 0x18 outPtr, cell fsp 0x20 curCap, cell fsp 0x28 curPtr,
       cell fsp 0x30 (fsp + 0x1c8#64), cell fsp 0x38 (BitVec.ofNat 64 (k + 1)), cell fsp 0x50 inPtr]
    have hfoc := m5ErrCellsPlaced_focus_tail A fsp outCap outPtr (BitVec.ofNat 64 out.length)
      inCap inPtr curCap curPtr g k
    refine SepWPp.weaken_pre (P' :=
      dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)) ∗
        A.pool ∗ stackAt s3.sp (stk - mainFrameSize) ∗ anyHeap ∗
        (localsCtx fsp 0 pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1))) [] ∗
          ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
          argsBuf A (BitVec.ofNat 64 n) buf ps ∗
          mainSaved s0))
      (Entails.of_eq (by
        rw [hfoc, hs3.sp]
        dsimp +zetaDelta only [fsp, Rest]
        ac_rfl)) ?_
    refine m5_drop_dirs_tail_placed (m := k + 1) (by omega) (by omega)
      (by simp [storesDirs_length]) hA hext hstk64 hs3
      (hx23_3.trans (by
        have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
        clear * - hk_cases
        rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (dsimp +zetaDelta only [fsp]; bv_omega)))
      hx26_3 ?_
    intro sm hsm hx19_m hx22_m hx24_m hfs_m htr_m
    have hunfoc :
        memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) (0x28 * (8 - (k + 1))) ∗
          localsCtx fsp 0 pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1))) [] ⊢
        locals fsp (m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) := by
      rw [← locals_focus fsp pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1)))
        (memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) (0x28 * (8 - (k + 1)))) []]
      exact locals_m5ErrCellsPlaced_forget_to_m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length)
        inCap inPtr curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1)) (by omega)
    refine SepWPp.weaken_pre (P' :=
      ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
        argsBuf A (BitVec.ofNat 64 n) buf ps ∗
        mainSaved s0 ∗
        locals fsp (m6CellsPlaced fsp outCap outPtr (BitVec.ofNat 64 out.length) inCap inPtr) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) ?_ ?_
    · refine Entails.trans (Entails.of_eq (show
        memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) (0x28 * (8 - (k + 1))) ∗
          A.pool ∗ stackAt s3.sp (stk - mainFrameSize) ∗ anyHeap ∗
          (localsCtx fsp 0 pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1))) [] ∗
            ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0) =
        (memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) (0x28 * (8 - (k + 1))) ∗
          localsCtx fsp 0 pre9 (0x1c8 + 0x28 * (k + 1)) (0x28 * (8 - (k + 1))) []) ∗
          (ownedBytes A outCap outPtr (BitVec.ofNat 64 out.length) out ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 inp.length) inp ∗
            argsBuf A (BitVec.ofNat 64 n) buf ps ∗ mainSaved s0 ∗
            stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) by
          rw [hs3.sp]; dsimp +zetaDelta only [fsp]; ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hunfoc) ?_
      exact Entails.of_eq (by ac_rfl)
    · have htr_eq : sm.trace = s.trace := htr_m.trans (htr3.trans (htr2.trans htr1))
      have hfs_eq : sm.fs = s.fs := hfs_m.trans (hfs3.trans (hfs2.trans hfs1))
      exact hnext sm
        { base := hsm
          w22 := by
            have hw := hx22_m.trans (hx22_3.trans hx22_2)
            rw [hw]; decide
          x19 := hx19_m.trans (hx19_3.trans hx19_2)
          x24 := hx24_m.trans (hx24_3.trans hx24_2) }
        hfs_eq htr_eq herr.commitNone
        (htr_eq.symm ▸ herr.trace)
        (by rw [htr_eq]; exact herr.stdout)

/-- Direct continuation wrapper matching `main_m5_proof_placed`'s `hnext` obligation when a `write_file`
call in `main`'s M5 commit loop exits on `Err`. -/
theorem m5_drop_for_m5_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks}
    {io : IoModel} {i : Inputs} {c : CallV} {g : StoresGhost}
    {out : List (BitVec 8)} {s0 s sErr : State} {stk k : Nat}
    {outCap outPtr inCap inPtr buf curCap curPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))}
    {curEntries : List (List (BitVec 8) × List (BitVec 8))}
    {e : M5ErrEntryPlaced}
    {Q Qp : State → SepProp → Prop}
    (hA : AllocContractsFsPlaced A H)
    (hext : mainFrameSize + extHookStack ≤ stk)
    (herr : M5LoopErrPlaced CodeOk io s.fs.files s.trace g s0 sErr i.argv.length buf k curEntries e)
    (hnext : ∀ (s' : State) (ok : Bool) (outCap' outPtr' : BitVec 64),
      (match commitFiles io.wr s.fs.files g.writes with
       | some F => ok = true ∧ s'.fs.files = F
       | none => ok = false) →
      s.trace <+: s'.trace →
      ProcessOutcome.traceStreamBytes .stdout s'.trace =
        ProcessOutcome.traceStreamBytes .stdout s.trace →
      AtM6Placed CodeOk s0 s' ok i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A outCap' outPtr' (BitVec.ofNat 64 out.length) out ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m6CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) outCap' outPtr'
              (BitVec.ofNat 64 out.length) inCap inPtr) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) sErr
      (m5ErrMemPlaced A s0 stk i.argv.length outCap outPtr inCap inPtr buf curCap curPtr
        out (inputOf i c) ps g k curEntries e)
      Q Qp (mainOom s0) := by
  refine m5_drop_placed hA hext herr ?_
  intro sm hatM6 _ _ hcommit htr hstdout
  exact hnext sm false outCap outPtr (by rw [hcommit]) htr hstdout hatM6

end CryptoVerification.SignalSession.Cli.MainHops
