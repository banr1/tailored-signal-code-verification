/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrTailPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4ErrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4StepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WP.Structural
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Entry, Over-Cap, and Post-`run` Helpers for `main_m4` (Block `617`)

`VmPreserved`-carrying straight-line steppers and entry/tail assembly lemmas on Block `617` for
`M4PlacedBudget`: the `IsSendOverCap` clean exit (`M+0x5dc → M+0x650`), setup to `bl run`
(`M+0x5dc → lsmpl.base 579`), and post-`run` `Err` / `Ok` tails (`M+0x7a4`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser utf8)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli
  (RunAnswer StoresGhost cliInputs cliStaticsPlaced coinsStaticsPlaced)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkLib_eq_617 blkPC_617 blkPl_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AtM4P1EndPlaced AtM4P2EndPlaced AtM4Placed AtM4RunCallPlaced AtM4SetupPlaced CallV CallW
   HistOkTight InMainPlaced LsCodeInv RunCall addrWords argsBuf callAt callHeap
   calleeSavedPreserved_of_regs cell coinsInstalledPlaced coinsLitSym coinsOf inputOf locals
   localsBound localsEnd localsFrom locals_forget_cell m4CellsPlaced m5CellsPlaced mPcPlaced
   mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize mainLitsBlk617 mainOom mainSaved
   ownedBytes parseArgs runOkAt runResAt runResSize sepWPp_seq_codeOk stackAt_split_ge storesAt)
open CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
  (entails_pure_elim_left entails_pure_intro_left ownedBytes_pure)
open CryptoVerification.SignalSession.Cli.MainHops.M4Placed
  (dirLit0Sym dirLit1Sym dirLit2Sym dirLit3Sym dirLit4Sym dirLit5Sym dirLit6Sym m4CallWords
   m4CallWords_pack m4Gaps m4OpenStoresPlaced_pack m4OpenStoresWordsPlaced m4RestFramePlaced
   m4Slot m4UninitP1 m4UninitP2 m4UninitP3 m4WrittenP1Placed m4WrittenP2Placed m4WrittenP3Placed
   m4_locals_close_err_cell_placed m4_locals_close_ok_placed m4_locals_open_placed m4_resSlot_merge
   m4_uninit_split m4_writtenPlaced_pack ownedBytesRest ownedBytes_split runOkAt_open)
open CryptoVerification.SignalSession.Coins
  (coinsLeftPlaced coinsLeftSym coinsNextPlaced coinsNextSym)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudgetAux

open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (runSpecAnyPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget
  (ExitKPlaced MainCalleesBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrTailPlacedBudget
  (step_dealloc_in_0x650_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4ErrPlacedBudget
  (m4_step_err_block_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlacedBudget
  (ExitKPoolPlaced exitKPoolPlaced_of_exitKPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem m4_sepWPp_exists_left_p {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx hL

theorem m4_allocFailedIn_of_start_trace_eq_p {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf) : allocFailedIn s0 sf := by
  unfold allocFailedIn at h ⊢
  rwa [htr] at h

theorem m4_histOkTight_of_eq_p {i : Inputs} {sf sf' : State}
    (htr : sf'.trace = sf.trace) (hfs : sf'.fs = sf.fs) (h : HistOkTight i sf) :
    HistOkTight i sf' :=
  ⟨by rw [hfs]; exact h.1, by rw [htr]; exact h.2⟩

private theorem sepWPp_seq_codeOk_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_617).rebase (blkPl_617).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm =>
          ∀ m_real : Memory,
            ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            CodeOk (sm'.setMem m_real).mem →
            SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret (sm'.setMem m_real) Pm Q Qp oom)) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) ret s Pre Q Qp oom := by
  refine sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := mid) hinv ?_
  apply sepWP_seg_ls_vm
    (Q := (blkPC_617).rebase (blkPl_617).base (hooksException H))
    blkLib_eq_617 (mid := mid)
  intro m_strip
  refine SepWP.mono (hseg m_strip) fun sm' Pm hpc_m' hrun_m' hcont m_real hnsp => ?_
  exact SepWP.done hpc_m' hrun_m' (hcont m_real hnsp)

/-! ## 1. `M+0x5dc → M+0x650`: `IsSendOverCap` Clean Exit (`code = 1`) -/

set_option maxHeartbeats 800000 in
/-- On `c = .send peer` with `1_000_000 < i.stdin.length`, `M+0x5dc .. M+0x61c` installs `coins`,
detects `x27 > 0xf4240`, sets `w26 = 1`, and jumps to `M+0x650` (`step_dealloc_in_0x650_pool_placed`)
to drop `input`, `Call`, and `args` before exiting with code `1`, retaining `A.pool`. -/
theorem m4_sendOverCap_pool_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat}
    {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some (.send peer))
    (hover : 1_000_000 < i.stdin.length)
    (hs : AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk
      (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        s'.trace = s.trace) Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
          (inputOf i (.send peer)) ∗
        callHeap A.repAlloc w (.send peer) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) := by
  let _ := hsp; let _ := hs0tr; let _ := hparse; let _ := hpanic
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hin_eq : inputOf i (.send peer) = i.stdin := rfl
  refine sepWPp_weaken_pre (Entails.of_eq (show _ =
    ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
      (inputOf i (.send peer)) ∗
    callHeap A.repAlloc w (.send peer) ∗
    (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
      ArgvFrame ∗
      mainSaved s0 ∗
      locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) ∗
      stackAt fsp (stk - mainFrameSize) ∗
      A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617) by sep_ac_rfl)) ?_
  rw [ownedBytes_pure A.repAlloc inCap inPtr
    (BitVec.ofNat 64 (inputOf i (.send peer)).length) (inputOf i (.send peer)), sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, hin_le, hinCap_lt, _⟩ => ?_
  rw [hin_eq] at hin_le
  have hinCap_ne : inCap ≠ 0#64 := fun h0 => by
    subst h0; simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hin_le; omega
  have hinCap_bne : (inCap != 0#64) = true := bne_iff_ne.mpr hinCap_ne
  have hinCap_beq : (inCap == 0#64) = false := beq_eq_false_iff_ne.mpr hinCap_ne
  have hgt_ule : (BitVec.ofNat 64 i.stdin.length).ule 1000000#64 = false := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, decide_eq_false_iff_not]
    omega
  have hgt_ult : (1000000#64).ult (BitVec.ofNat 64 i.stdin.length) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, decide_eq_true_eq]
    omega
  have hch_pure :
      callHeap A.repAlloc w (.send peer) =
        (⌜w.w0 = 0x8000000000000002#64⌝ ∗ callHeap A.repAlloc w (.send peer)) := by
    dsimp only [callHeap]
    apply ProofLib.sepProp_ext
    · exact entails_pure_elim_left fun hp =>
        entails_pure_intro_left hp (entails_pure_intro_left hp (Entails.refl _))
    · exact entails_pure_elim_left fun _ => Entails.refl _
  refine sepWPp_weaken_pre (Entails.of_eq (show _ =
    callHeap A.repAlloc w (.send peer) ∗
    (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
        (inputOf i (.send peer)) ∗
      ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
      ArgvFrame ∗
      mainSaved s0 ∗
      locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) ∗
      stackAt fsp (stk - mainFrameSize) ∗
      A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617) by sep_ac_rfl)) ?_
  rw [hch_pure, sepConj_assoc]
  refine SepWPp.pure_elim fun hw0_eq => ?_
  have hloc_focus :
      locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) =
      ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
        ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion fsp 0x40 ∗
        memRegion (fsp + 0x60#64) 0x168 ∗
        memRegion (fsp + 0x1d0#64) (0x480 - 0x1d0) := by
    simp only [locals, localsFrom, Nat.reduceAdd, Nat.reduceSub,
      ProofLib.memRegion_zero, emp_sepConj]
    sep_ac_rfl
  dsimp only [cliStaticsPlaced, coinsStaticsPlaced, coinsNextPlaced, coinsLeftPlaced,
    coinsNextSym, coinsLeftSym]
  rw [hloc_focus]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine m4_sepWPp_exists_left_p fun vLeft => ?_
  refine m4_sepWPp_exists_left_p fun vNext => ?_
  have hpc : s.pc = (blkPl_617).base + 1500#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hsp_eq : s.sp = fsp := hs.base.sp
  have hx0 := hs.x0
  have hx19 := hs.x19
  have hx20 := hs.x20
  have hx21 := hs.w5
  have hx22 := hs.w2
  have hx23 := hs.x23
  have hx24 := hs.x24
  have hx25 := hs.w0
  have hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 i.stdin.length := by
    simpa only [hin_eq] using hs.x27
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1616#64) hs.base.inv
    fun _m_strip => ?_
  have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro _m_real hnsp_650 hinv_650
  have hin_650 : InMainPlaced CodeOk s0 _ 0x650 :=
    InMainPlaced.mk_step hs.base
      (by simp only [mPcPlaced_eq, arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      hinv_650
      (by simp only [calleeSavedVRegs, arm64_norm])
  have hvm_650 : VmPreserved s _ :=
    ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
      by simp only [arm64_norm], fun a => congrFun hnsp_650.2.1 a,
      LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩
  have hpool_eq : A.pool lim st s = A.pool lim st _ := (A.pool_of_vmPreserved hvm_650).symm
  refine sepWPp_weaken_pre ?_
    (step_dealloc_in_0x650_pool_placed (ms := st) (n := i.argv.length) (code := 1)
      (c := .send peer) (w := w) (buf := buf) (inCap := inCap) (inPtr := inPtr)
      (inLen := BitVec.ofNat 64 (inputOf i (.send peer)).length)
      (inBs := inputOf i (.send peer)) (ps := ps)
      hc hstk hstk64 hin_650 hinCap_ne
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hx23])
      (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25])
      (by simp only [arm64_norm])
      (fun s' htr' hfs' =>
        ⟨rfl,
         by rw [hfs']; simpa only [arm64_norm] using hs.fs,
         htr'.trans (by simp only [arm64_norm])⟩)
      hexit)
  have hloc_back :
      ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
        ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion fsp 0x40 ∗
        memRegion (fsp + 0x60#64) 0x168 ∗
        memRegion (fsp + 0x1d0#64) (0x480 - 0x1d0) ⊢
      locals fsp
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] := by
    rw [← hloc_focus]
    change locals fsp
        ([cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ++
          [cell fsp 0x1c8 (BitVec.ofNat 64 (coinsOf i).length)] ++ []) ⊢
      locals fsp
        ([cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] ++ [])
    exact locals_forget_cell fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
      0x1c8 (BitVec.ofNat 64 (coinsOf i).length) []
  rw [hpool_eq]
  refine Entails.trans (Entails.of_eq (show _ =
    ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
      (inputOf i (.send peer)) ∗
    callHeap A.repAlloc w (.send peer) ∗
    argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
    mainSaved s0 ∗
    (((fsp + 0x58#64) ↦₆₄ w.w1) ∗
      ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
      ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
      ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
      ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      memRegion fsp 0x40 ∗
      memRegion (fsp + 0x60#64) 0x168 ∗
      memRegion (fsp + 0x1d0#64) (0x480 - 0x1d0)) ∗
    stackAt fsp (stk - mainFrameSize) ∗
    A.pool lim st _ ∗
    (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
      ArgvFrame ∗
      (lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ coinsPtr) ∗
      (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
      tokenInitPlacedAt ∗
      lsLogOff ∗
      mainLitsBlk617) by sep_ac_rfl)) ?_
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono hloc_back
            (sepConj_mono_right
              (sepConj_mono_right (ProofLib.entails_anyHeap _)))))))

/-! ## 2. `VmPreserved`-Carrying Steppers `M+0x5dc → M+0x678 → signal_session::run` -/

set_option maxHeartbeats 800000 in
private theorem m4_entry_to_setup_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {A : CryptoVerification.RustHeap.RustAlloc}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State} {ret : BitVec 64}
    {buf coinsCap coinsPtr inCap : BitVec 64} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hin_lt63 : (inputOf i c).length < 2 ^ 63)
    (hk : ∀ s_setup : State,
      AtM4SetupPlaced CodeOk s0 s_setup w i.argv.length buf inCap (inputOf i c).length →
      s_setup.sp = s.sp →
      s_setup.trace = s.trace →
      s_setup.fs = s.fs →
      VmPreserved s s_setup →
      SepWPp (mProgPlaced H) ret s_setup
        ((coinsNextPlaced ↦₆₄ coinsPtr) ∗
          (coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
          ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
          callHeap A w c ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (coinsStaticsPlaced ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        callHeap A w c ∗ F)
      Q Qp oom := by
  have hpc : s.pc = (blkPl_617).base + 1500#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hx0 := hs.x0
  have hx19 := hs.x19
  have hx21 := hs.w5
  have hx22 := hs.w2
  have hx23 := hs.x23
  have hx24 := hs.x24
  have hx25 := hs.w0
  have hx26 := hs.w6
  have hx27 := hs.x27
  dsimp only [coinsStaticsPlaced, coinsNextPlaced, coinsLeftPlaced, coinsNextSym, coinsLeftSym]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine m4_sepWPp_exists_left_p fun vLeft => ?_
  refine m4_sepWPp_exists_left_p fun vNext => ?_
  cases c with
  | keygen me k =>
    have hch_pure :
        callHeap A w (.keygen me k) =
          (⌜w.w0 = 0x8000000000000000#64⌝ ∗ callHeap A w (.keygen me k)) := by
      dsimp only [callHeap]
      apply ProofLib.sepProp_ext
      · exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp.1 (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      callHeap A w (.keygen me k) ∗
      ((lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ vNext) ∗
        (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ vLeft) ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗ F) by sep_ac_rfl)) ?_
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    rw [mProgPlaced_eq]
    refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1656#64) hs.base.inv
      fun _m_strip => ?_
    have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro _m_real hnsp hinv_s
    refine sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
          by simp only [arm64_norm], fun a => congrFun hnsp.2.1 a,
          LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩)
    exact
      { base := InMainPlaced.mk_step hs.base
          (by simp only [mPcPlaced_eq, arm64_norm, *])
          (by simp only [arm64_norm, hrun])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv_s
          (by simp only [calleeSavedVRegs, arm64_norm])
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm, hx21]
        x22 := by simp only [arm64_norm, hx22]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x25 := by simp only [arm64_norm, hx25]
        x26 := by simp only [arm64_norm, hx26]
        x27 := by simp only [arm64_norm, hx27] }
  | init peer bundle =>
    have hch_pure :
        callHeap A w (.init peer bundle) =
          (⌜w.w0.toNat < 2 ^ 63⌝ ∗ callHeap A w (.init peer bundle)) := by
      dsimp only [callHeap, addrWords, ownedBytes]
      apply ProofLib.sepProp_ext
      · rw [sepConj_assoc, sepConj_assoc]
        exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp.2.2.1 (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      callHeap A w (.init peer bundle) ∗
      ((lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ vNext) ∗
        (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ vLeft) ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗ F) by sep_ac_rfl)) ?_
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_lt => ?_
    have hw0_beq : (w.w0 == 0x8000000000000002#64) = false := by
      rw [beq_eq_false_iff_ne]; bv_omega
    have hw0_bne : (w.w0 != 0x8000000000000002#64) = true := by
      rw [bne_iff_ne]; bv_omega
    have hw0_sub_beq : (w.w0 - 0x8000000000000002#64 == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; bv_omega
    have hw0_sub_bne : (w.w0 - 0x8000000000000002#64 != 0#64) = true := by
      rw [bne_iff_ne]; bv_omega
    rw [mProgPlaced_eq]
    refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1656#64) hs.base.inv
      fun _m_strip => ?_
    have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro _m_real hnsp hinv_s
    refine sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
          by simp only [arm64_norm], fun a => congrFun hnsp.2.1 a,
          LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩)
    exact
      { base := InMainPlaced.mk_step hs.base
          (by simp only [mPcPlaced_eq, arm64_norm, *])
          (by simp only [arm64_norm, hrun])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv_s
          (by simp only [calleeSavedVRegs, arm64_norm])
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm, hx21]
        x22 := by simp only [arm64_norm, hx22]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x25 := by simp only [arm64_norm, hx25]
        x26 := by simp only [arm64_norm, hx26]
        x27 := by simp only [arm64_norm, hx27] }
  | send peer =>
    have hle_cap : i.stdin.length ≤ 1_000_000 := hnot_over peer rfl
    have hin_eq : inputOf i (.send peer) = i.stdin := rfl
    rw [hin_eq] at hin_lt63 hx27
    have hls_ule : (BitVec.ofNat 64 i.stdin.length).ule 1000000#64 = true := by
      simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod, decide_eq_true_eq]
      omega
    have hls_ult : (1000000#64).ult (BitVec.ofNat 64 i.stdin.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod, decide_eq_false_iff_not]
      omega
    have hch_pure :
        callHeap A w (.send peer) =
          (⌜w.w0 = 0x8000000000000002#64⌝ ∗ callHeap A w (.send peer)) := by
      dsimp only [callHeap]
      apply ProofLib.sepProp_ext
      · exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      callHeap A w (.send peer) ∗
      ((lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ vNext) ∗
        (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ vLeft) ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗ F) by sep_ac_rfl)) ?_
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    rw [mProgPlaced_eq]
    refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1656#64) hs.base.inv
      fun _m_strip => ?_
    have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro _m_real hnsp hinv_s
    refine sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
          by simp only [arm64_norm], fun a => congrFun hnsp.2.1 a,
          LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩)
    exact
      { base := InMainPlaced.mk_step hs.base
          (by simp only [mPcPlaced_eq, arm64_norm, *])
          (by simp only [arm64_norm, hrun])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv_s
          (by simp only [calleeSavedVRegs, arm64_norm])
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm, hx21]
        x22 := by simp only [arm64_norm, hx22]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x25 := by simp only [arm64_norm, hx25]
        x26 := by simp only [arm64_norm, hx26]
        x27 := by simpa only [hin_eq, arm64_norm] using hx27 }
  | recv peer =>
    have hch_pure :
        callHeap A w (.recv peer) =
          (⌜w.w0 = 0x8000000000000003#64⌝ ∗ callHeap A w (.recv peer)) := by
      dsimp only [callHeap]
      apply ProofLib.sepProp_ext
      · exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      callHeap A w (.recv peer) ∗
      ((lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ vNext) ∗
        (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ vLeft) ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗ F) by sep_ac_rfl)) ?_
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    rw [mProgPlaced_eq]
    refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1656#64) hs.base.inv
      fun _m_strip => ?_
    have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro _m_real hnsp hinv_s
    refine sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
          by simp only [arm64_norm], fun a => congrFun hnsp.2.1 a,
          LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩)
    exact
      { base := InMainPlaced.mk_step hs.base
          (by simp only [mPcPlaced_eq, arm64_norm, *])
          (by simp only [arm64_norm, hrun])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv_s
          (by simp only [calleeSavedVRegs, arm64_norm])
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm, hx21]
        x22 := by simp only [arm64_norm, hx22]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x25 := by simp only [arm64_norm, hx25]
        x26 := by simp only [arm64_norm, hx26]
        x27 := by simp only [arm64_norm, hx27] }

private theorem m4_step_part1_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {ret : BitVec 64} {w : CallW} {n : Nat}
    {buf inCap inPtr : BitVec 64} {inLen : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hs : AtM4SetupPlaced CodeOk s0 s w n buf inCap inLen)
    (hk : ∀ s1 : State,
      AtM4P1EndPlaced CodeOk s0 s1 w n buf inCap inPtr inLen →
      s1.trace = s.trace →
      s1.fs = s.fs →
      VmPreserved s s1 →
      SepWPp (mProgPlaced H) ret s1
        (((s.sp + 0x40#64) ↦₆₄ w.w3) ∗
          ((s.sp + 0x48#64) ↦₆₄ w.w4) ∗
          ((s.sp + 0x50#64) ↦₆₄ inPtr) ∗
          ((s.sp + 0x58#64) ↦₆₄ w.w1) ∗
          m4WrittenP1Placed s.sp w ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (((s.sp + 0x40#64) ↦₆₄ w.w3) ∗
        ((s.sp + 0x48#64) ↦₆₄ w.w4) ∗
        ((s.sp + 0x50#64) ↦₆₄ inPtr) ∗
        ((s.sp + 0x58#64) ↦₆₄ w.w1) ∗
        m4UninitP1 s.sp ∗ F)
      Q Qp oom := by
  have hpc : s.pc = (blkPl_617).base + 1656#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hx19 := hs.x19
  have hx21 := hs.x21
  have hx22 := hs.x22
  have hx23 := hs.x23
  have hx24 := hs.x24
  have hx25 := hs.x25
  have hx26 := hs.x26
  have hx27 := hs.x27
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1788#64) hs.base.inv
    fun _m_strip => ?_
  have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
  dsimp only [m4UninitP1, m4Slot]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v78
  apply SepWP.exists_left; intro v80
  apply SepWP.exists_left; intro v88
  apply SepWP.exists_left; intro v90
  apply SepWP.exists_left; intro va8
  apply SepWP.exists_left; intro v328
  apply SepWP.exists_left; intro v350
  apply SepWP.exists_left; intro v358
  apply SepWP.exists_left; intro v378
  apply SepWP.exists_left; intro v380
  apply SepWP.exists_left; intro v3a0
  apply SepWP.exists_left; intro v3a8
  apply SepWP.exists_left; intro v3c8
  apply SepWP.exists_left; intro v3d0
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro _m_real hnsp hinv1
  refine sepWPp_weaken_pre ?_
    (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
        by simp only [arm64_norm], fun a => congrFun hnsp.2.1 a,
      LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩)
  · dsimp only [m4WrittenP1Placed, dirLit0Sym, dirLit1Sym, dirLit2Sym, dirLit3Sym]
    exact Entails.of_eq (by sep_ac_rfl)
  · exact
      { base := InMainPlaced.mk_step hs.base
          (by simp only [mPcPlaced_eq, arm64_norm])
          (by simp only [arm64_norm, hrun])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv1
          (by simp only [calleeSavedVRegs, arm64_norm])
        x0 := by simp only [arm64_norm]
        x1 := by simp only [arm64_norm]
        x2 := by simp only [arm64_norm]
        x3 := by simp only [arm64_norm]
        x4 := by simp only [arm64_norm]
        x8 := by simp only [arm64_norm]
        x10 := by simp only [arm64_norm]
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm, hx21]
        x22 := by simp only [arm64_norm]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x27 := by simp only [arm64_norm, hx27] }

private theorem m4_step_part2_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {ret : BitVec 64} {w : CallW} {n : Nat}
    {buf inCap inPtr : BitVec 64} {inLen : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hs : AtM4P1EndPlaced CodeOk s0 s w n buf inCap inPtr inLen)
    (hk : ∀ s2 : State,
      AtM4P2EndPlaced CodeOk s0 s2 n buf inCap inPtr inLen →
      s2.trace = s.trace →
      s2.fs = s.fs →
      VmPreserved s s2 →
      SepWPp (mProgPlaced H) ret s2
        (m4WrittenP2Placed s.sp w ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (m4UninitP2 s.sp ∗ F)
      Q Qp oom := by
  have hpc : s.pc = (blkPl_617).base + 1788#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hx0 : s.readReg64 (.gpr 0#5) = s.sp + 0x1b8#64 := hs.x0
  have hx1 : s.readReg64 (.gpr 1#5) = s.sp + 0x78#64 := hs.x1
  have hx2 : s.readReg64 (.gpr 2#5) = s.sp + 0x310#64 := hs.x2
  have hx3 : s.readReg64 (.gpr 3#5) = inPtr := hs.x3
  have hx4 : s.readReg64 (.gpr 4#5) = BitVec.ofNat 64 inLen := hs.x4
  have hx8 := hs.x8
  have hx10 := hs.x10
  have hx19 := hs.x19
  have hx21 := hs.x21
  have hx22 := hs.x22
  have hx23 := hs.x23
  have hx24 := hs.x24
  have hx27 := hs.x27
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1864#64) hs.base.inv
    fun _m_strip => ?_
  have hpc_strip : (s.setMem _m_strip).pc = (blkPl_617).base + 1788#64 := hpc
  have hrun_strip : (s.setMem _m_strip).status = .Running := hrun
  have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
  dsimp only [m4UninitP2, m4Slot]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v98
  apply SepWP.exists_left; intro va0
  apply SepWP.exists_left; intro v318
  apply SepWP.exists_left; intro v340
  apply SepWP.exists_left; intro v368
  apply SepWP.exists_left; intro v390
  apply SepWP.exists_left; intro v3b8
  apply SepWP.exists_left; intro v3e0
  apply SepWP.exists_left; intro v3f0
  apply SepWP.exists_left; intro v408
  apply SepWP.exists_left; intro v418
  apply SepWP.exists_left; intro v420
  apply SepWP.exists_left; intro v430
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro _m_real hnsp hinv2
  refine sepWPp_weaken_pre ?_
    (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
        by simp only [arm64_norm], fun a => congrFun hnsp.2.1 a,
      LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩)
  · dsimp only [m4WrittenP2Placed, dirLit4Sym, dirLit5Sym]
    exact Entails.of_eq (by sep_ac_rfl)
  · exact
      { base := InMainPlaced.mk_step hs.base
          (by simp only [mPcPlaced_eq, arm64_norm])
          (by simp only [arm64_norm, hrun])
          (by simp only [arm64_norm])
          (by simp only [arm64_norm])
          hinv2
          (by simp only [calleeSavedVRegs, arm64_norm])
        x0 := by simp only [arm64_norm, hx0]
        x1 := by simp only [arm64_norm, hx1]
        x2 := by simp only [arm64_norm, hx2]
        x3 := by simp only [arm64_norm, hx3]
        x4 := by simp only [arm64_norm, hx4]
        x9 := by simp only [arm64_norm]
        x10 := by simp only [arm64_norm, hx10]
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm]
        x22 := by simp only [arm64_norm, hx22]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x27 := by simp only [arm64_norm, hx27] }

private theorem m4_step_part3_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {ret : BitVec 64} {n : Nat}
    {buf inCap inPtr : BitVec 64} {inLen : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hs : AtM4P2EndPlaced CodeOk s0 s n buf inCap inPtr inLen)
    (hk : ∀ s3 : State,
      AtM4RunCallPlaced CodeOk s0 s3 n buf inCap inPtr inLen →
      s3.sp = s.sp →
      s3.trace = s.trace →
      s3.fs = s.fs →
      VmPreserved s s3 →
      SepWPp (mProgPlaced H) ret s3
        (m4WrittenP3Placed s.sp ∗ F)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (m4UninitP3 s.sp ∗ F)
      Q Qp oom := by
  have hpc : s.pc = (blkPl_617).base + 1864#64 := hs.base.pc
  have hrun : s.status = .Running := hs.base.run
  have hsp_al : s.spAligned = true := hs.base.spAligned_state
  have hx0 : s.readReg64 (.gpr 0#5) = s.sp + 0x1b8#64 := hs.x0
  have hx1 : s.readReg64 (.gpr 1#5) = s.sp + 0x78#64 := hs.x1
  have hx2 : s.readReg64 (.gpr 2#5) = s.sp + 0x310#64 := hs.x2
  have hx3 : s.readReg64 (.gpr 3#5) = inPtr := hs.x3
  have hx4 : s.readReg64 (.gpr 4#5) = BitVec.ofNat 64 inLen := hs.x4
  have hx9 := hs.x9
  have hx10 := hs.x10
  have hx19 := hs.x19
  have hx21 := hs.x21
  have hx22 := hs.x22
  have hx23 := hs.x23
  have hx24 := hs.x24
  have hx27 := hs.x27
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := lsmpl.base 579) hs.base.inv
    fun _m_strip => ?_
  have hpc_strip : (s.setMem _m_strip).pc = (blkPl_617).base + 1864#64 := hpc
  have hrun_strip : (s.setMem _m_strip).status = .Running := hrun
  have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
  dsimp only [m4UninitP3, m4Slot]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro v310
  apply SepWP.exists_left; intro v320
  apply SepWP.exists_left; intro v330
  apply SepWP.exists_left; intro v338
  apply SepWP.exists_left; intro v348
  apply SepWP.exists_left; intro v360
  apply SepWP.exists_left; intro v370
  apply SepWP.exists_left; intro v388
  apply SepWP.exists_left; intro v398
  apply SepWP.exists_left; intro v3b0
  apply SepWP.exists_left; intro v3c0
  apply SepWP.exists_left; intro v3d8
  apply SepWP.exists_left; intro v3e8
  apply SepWP.exists_left; intro v3f8
  apply SepWP.exists_left; intro v400
  apply SepWP.exists_left; intro v410
  apply SepWP.exists_left; intro v428
  apply SepWP.exists_left; intro v438
  apply SepWP.exists_left; intro v440
  apply SepWP.exists_left; intro v448
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro _m_real hnsp hinv3
  refine sepWPp_weaken_pre ?_
    (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
        by simp only [arm64_norm], fun a => congrFun hnsp.2.1 a,
      LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩)
  · dsimp only [m4WrittenP3Placed, dirLit6Sym]
    exact Entails.of_eq (by sep_ac_rfl)
  · exact
      { pc := by simp only [arm64_norm, *]
        lr := by simp only [mPcPlaced_eq, arm64_norm]
        run := by simp only [arm64_norm, hrun]
        sp := (by simp only [arm64_norm] : _ = s.sp).trans hs.base.sp
        fp := (by simp only [arm64_norm] : _ = s.readReg64 .fp).trans hs.base.fp
        inv := hinv3
        vregs := by
          simp only [calleeSavedVRegs, arm64_norm]
          exact hs.base.vregs
        spAligned := by simpa only [State.spAligned, arm64_norm] using hsp_al
        x0 := by simp only [arm64_norm, hx0]
        x1 := by simp only [arm64_norm, hx1]
        x2 := by simp only [arm64_norm, hx2]
        x3 := by simp only [arm64_norm, hx3]
        x4 := by simp only [arm64_norm, hx4]
        x19 := by simp only [arm64_norm, hx19]
        x21 := by simp only [arm64_norm, hx21]
        x22 := by simp only [arm64_norm, hx22]
        x23 := by simp only [arm64_norm, hx23]
        x24 := by simp only [arm64_norm, hx24]
        x27 := by simp only [arm64_norm, hx27] }

/-! ## 3. `M+0x5dc → signal_session::run` (`lsmpl.base 579`) Packaging -/

set_option maxHeartbeats 1200000 in
theorem m4_to_run_call_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {Run : Inputs → RunAnswer → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {ArgvFrame : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hk : ∀ (s3 : State),
      let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
      let g_run : RunCall :=
        { i := i, c := c, a := a, res := fsp + 0x1b8#64, call := fsp + 0x78#64,
          stores := fsp + 0x310#64, inp := inPtr, coins := coinsPtr }
      let frameRun : SepProp :=
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
          anyHeap
      AtM4RunCallPlaced CodeOk s0 s3 i.argv.length buf inCap inPtr (inputOf i c).length →
      s3.sp = fsp → s3.trace = s.trace → s3.trace = s0.trace → s3.fs = s.fs →
      SepWPp (mProgPlaced H) ret s3
        ((runSpecAnyPlaced CodeOk A lim uuidParse Run (fun _ => True) resStack).pre
            (g_run, st) s3 ∗ frameRun)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        ArgvFrame ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hsp0 : s.sp = fsp := hs.base.sp
  have hres_le : resStack ≤ stk - mainFrameSize := by omega
  have hstk_split := stackAt_split_ge fsp hres_le (by omega)
  refine sepWPp_weaken_pre (Entails.of_eq (show _ =
    ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
    (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
      callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
      ArgvFrame ∗
      mainSaved s0 ∗
      locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) ∗
      stackAt fsp (stk - mainFrameSize) ∗
      A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617) by sep_ac_rfl)) ?_
  rw [ownedBytes_pure A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c),
    sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, hin_le, hinCap_lt, _⟩ => ?_
  have hin_lt63 : (inputOf i c).length < 2 ^ 63 := Nat.lt_of_le_of_lt hin_le hinCap_lt
  let restKeep : SepProp :=
    (coinsPtr ↦ₛ coinsOf i) ∗
    (inPtr ↦ₛ inputOf i c) ∗
    ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
    argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
    mainSaved s0 ∗
    m4Gaps fsp ∗
    memRegion (fsp + 0x1b8#64) 0x10 ∗
    memRegion (fsp + 0x1d0#64) 0x140 ∗
    memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
    stackAt fsp resStack ∗
    A.pool lim st s ∗
    tokenInitPlacedAt ∗
    lsLogOff ∗
    mainLitsBlk617 ∗
    ownedBytesRest A.repAlloc coinsCap coinsPtr (coinsOf i) ∗
    ArgvFrame
  have hpre_entry :
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        (ownedBytes A.repAlloc coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          callHeap A.repAlloc w c ∗ argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          ArgvFrame ∗
          mainSaved s0 ∗
          locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) ∗
          stackAt fsp (stk - mainFrameSize) ∗
          A.pool lim st s ∗ cliStaticsPlaced ∗ mainLitsBlk617) ⊢
      coinsStaticsPlaced ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        callHeap A.repAlloc w c ∗
        (((fsp + 0x40#64) ↦₆₄ w.w3) ∗
          ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
          m4UninitP1 fsp ∗ m4UninitP2 fsp ∗ m4UninitP3 fsp ∗ restKeep) := by
    have hloc :
        locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) ⊢
          m4Gaps fsp ∗
          ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
          ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
          ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
          memRegion (fsp + 0x1b8#64) 0x10 ∗
          memRegion (fsp + 0x1d0#64) 0x140 ∗
          (m4UninitP1 fsp ∗ m4UninitP2 fsp ∗ m4UninitP3 fsp) :=
      Entails.trans (m4_locals_open_placed fsp w inPtr (coinsOf i).length)
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_right
                    (sepConj_mono_right
                      (sepConj_mono_right (m4_uninit_split fsp)))))))))
    refine Entails.trans
      (sepConj_mono (ownedBytes_split A.repAlloc inCap inPtr (inputOf i c))
        (sepConj_mono (ownedBytes_split A.repAlloc coinsCap coinsPtr (coinsOf i))
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono hloc
                    (sepConj_mono (Entails.of_eq hstk_split) (Entails.refl _))))))))) ?_
    rw [hsp0]
    dsimp only [cliStaticsPlaced, restKeep]
    exact Entails.of_eq (by sep_ac_rfl)
  refine sepWPp_weaken_pre hpre_entry ?_
  clear hpre_entry
  refine m4_entry_to_setup_vm hs hnot_over hin_lt63
    fun s_setup hs_setup hsp_setup htr_setup hfs_setup hvm0 => ?_
  have hsp_s0 : s_setup.sp = fsp := hsp_setup.trans hsp0
  refine sepWPp_weaken_pre
    (P' := ((s_setup.sp + 0x40#64) ↦₆₄ w.w3) ∗
      ((s_setup.sp + 0x48#64) ↦₆₄ w.w4) ∗
      ((s_setup.sp + 0x50#64) ↦₆₄ inPtr) ∗
      ((s_setup.sp + 0x58#64) ↦₆₄ w.w1) ∗
      m4UninitP1 s_setup.sp ∗
      (m4UninitP2 fsp ∗ m4UninitP3 fsp ∗
        (coinsNextPlaced ↦₆₄ coinsPtr) ∗
        (coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        callHeap A.repAlloc w c ∗ restKeep))
    (by rw [hsp0, hsp_s0]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine m4_step_part1_vm hs_setup fun s1 hs1 htr1 hfs1 hvm1 => ?_
  have hsp1 : s1.sp = fsp := hs1.base.sp
  refine sepWPp_weaken_pre
    (P' := m4UninitP2 s1.sp ∗
      (m4UninitP3 fsp ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
        ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
        m4WrittenP1Placed fsp w ∗
        (coinsNextPlaced ↦₆₄ coinsPtr) ∗
        (coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        callHeap A.repAlloc w c ∗ restKeep))
    (by rw [hsp_s0, hsp1]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine m4_step_part2_vm hs1 fun s2 hs2 htr2 hfs2 hvm2 => ?_
  have hsp2 : s2.sp = fsp := hs2.base.sp
  refine sepWPp_weaken_pre
    (P' := m4UninitP3 s2.sp ∗
      (m4WrittenP2Placed fsp w ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
        ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
        m4WrittenP1Placed fsp w ∗
        (coinsNextPlaced ↦₆₄ coinsPtr) ∗
        (coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        callHeap A.repAlloc w c ∗ restKeep))
    (by rw [hsp1, hsp2]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine m4_step_part3_vm hs2 fun s3 hs3 _ htr3 hfs3 hvm3 => ?_
  have hsp3 : s3.sp = fsp := hs3.sp
  have htr3_s : s3.trace = s.trace := htr3.trans (htr2.trans (htr1.trans htr_setup))
  have htr3_0 : s3.trace = s0.trace := htr3_s.trans hs.trace
  have hfs3_s : s3.fs = s.fs := hfs3.trans (hfs2.trans (hfs1.trans hfs_setup))
  have hpool3 : A.pool lim st s = A.pool lim st s3 :=
    (A.pool_of_vmPreserved hvm0).symm.trans
      ((A.pool_of_vmPreserved hvm1).symm.trans
        ((A.pool_of_vmPreserved hvm2).symm.trans (A.pool_of_vmPreserved hvm3).symm))
  let g_run : RunCall :=
    { i := i, c := c, a := a, res := fsp + 0x1b8#64, call := fsp + 0x78#64,
      stores := fsp + 0x310#64, inp := inPtr, coins := coinsPtr }
  let frameRun : SepProp :=
    m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
      anyHeap
  have hpure_run :
      CodeOk s3.mem ∧
        Run g_run.i g_run.a ∧
        parseArgs uuidParse (g_run.i.argv.map bytesOfString) = some g_run.c ∧
        s3.readReg64 .x0 = g_run.res ∧
        s3.readReg64 .x1 = g_run.call ∧
        s3.readReg64 .x2 = g_run.stores ∧
        s3.readReg64 .x3 = g_run.inp ∧
        s3.readReg64 .x4 = BitVec.ofNat 64 (inputOf g_run.i g_run.c).length ∧
        s3.fs.files = (initFsState (cliInputs g_run.i)).files ∧
        ProcessOutcome.traceStreamBytes .stdout s3.trace = [] ∧
        resStack ≤ s3.sp.toNat ∧
        LsRetAddr624 (s3.readReg64 .x30) := by
    dsimp only [g_run]
    refine ⟨hs3.inv, hRun, hparse, ?_, ?_, ?_, hs3.x3, hs3.x4, ?_, ?_, ?_, ?_⟩
    · rw [hs3.x0, hsp3]
    · rw [hs3.x1, hsp3]
    · rw [hs3.x2, hsp3]
    · rw [hfs3_s]; exact hs.fs
    · rw [htr3_0, hs0tr]; rfl
    · rw [hsp3]
      have : 1248 + resStack ≤ stk := by
        dsimp only [mainFrameSize] at hstk
        omega
      dsimp only [fsp, mainFrameSize]
      have := s0.sp.isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    · change LsRetAddr624 (s3.readReg64 .lr)
      rw [hs3.lr, mPcPlaced_eq]
      exact lsRetAddr624_blockPlacement_base_add 617 0x7a4#64 (by decide) (by decide)
  have hpre_run :
      m4WrittenP3Placed s2.sp ∗
        (m4WrittenP2Placed fsp w ∗
          ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
          ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
          m4WrittenP1Placed fsp w ∗
          (coinsNextPlaced ↦₆₄ coinsPtr) ∗
          (coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
          ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
          callHeap A.repAlloc w c ∗ restKeep) ⊢
      (runSpecAnyPlaced CodeOk A lim uuidParse Run (fun _ => True) resStack).pre (g_run, st) s3 ∗
        frameRun := by
    rw [hsp2]
    let leakBundle : SepProp :=
      (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617 ∗
        ownedBytesRest A.repAlloc coinsCap coinsPtr (coinsOf i) ∗
        ArgvFrame
    have hrearr1 :
        m4WrittenP3Placed fsp ∗
          (m4WrittenP2Placed fsp w ∗
            ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
            ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
            ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
            m4WrittenP1Placed fsp w ∗
            (coinsNextPlaced ↦₆₄ coinsPtr) ∗
            (coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            callHeap A.repAlloc w c ∗ restKeep) =
        (((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
          memRegion (fsp + 0x1b8#64) 0x10 ∗
          memRegion (fsp + 0x1d0#64) 0x140) ∗
        ((m4WrittenP1Placed fsp w ∗ m4WrittenP2Placed fsp w ∗ m4WrittenP3Placed fsp) ∗
          callHeap A.repAlloc w c ∗ mainLitsBlk617) ∗
        coinsInstalledPlaced coinsPtr (coinsOf i) ∗
        m4RestFramePlaced fsp w ∗
        (inPtr ↦ₛ inputOf i c) ∗
        tokenInitPlacedAt ∗
        lsLogOff ∗
        A.pool lim st s3 ∗
        stackAt fsp resStack ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
        (ownedBytesRest A.repAlloc coinsCap coinsPtr (coinsOf i) ∗ ArgvFrame) := by
      dsimp only [restKeep, coinsInstalledPlaced, m4RestFramePlaced]
      rw [hpool3]
      sep_ac_rfl
    have hpack_mid :
        (m4WrittenP1Placed fsp w ∗ m4WrittenP2Placed fsp w ∗ m4WrittenP3Placed fsp) ∗
          callHeap A.repAlloc w c ∗ mainLitsBlk617 ⊢
        callAt A.repAlloc (fsp + 0x78#64) c ∗
          storesAt A.repAlloc (fsp + 0x310#64) StoresGhost.opened ∗
          (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617 := by
      rw [m4_writtenPlaced_pack fsp w]
      have hmid_eq :
          (m4CallWords fsp w ∗ m4OpenStoresWordsPlaced fsp) ∗ callHeap A.repAlloc w c ∗
              mainLitsBlk617 =
            (m4CallWords fsp w ∗ callHeap A.repAlloc w c) ∗
              (m4OpenStoresWordsPlaced fsp ∗ mainLitsBlk617) := by
        sep_ac_rfl
      rw [hmid_eq]
      exact sepConj_mono (m4CallWords_pack A.repAlloc fsp w c) (m4OpenStoresPlaced_pack A.repAlloc fsp)
    rw [hrearr1]
    refine Entails.trans
      (sepConj_mono (m4_resSlot_merge fsp (BitVec.ofNat 64 (coinsOf i).length))
        (sepConj_mono hpack_mid (Entails.refl _))) ?_
    have hrearr2 :
        memRegion (fsp + 0x1b8#64) runResSize ∗
          (callAt A.repAlloc (fsp + 0x78#64) c ∗
            storesAt A.repAlloc (fsp + 0x310#64) StoresGhost.opened ∗
            (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617) ∗
          coinsInstalledPlaced coinsPtr (coinsOf i) ∗
          m4RestFramePlaced fsp w ∗
          (inPtr ↦ₛ inputOf i c) ∗
          tokenInitPlacedAt ∗
          lsLogOff ∗
          A.pool lim st s3 ∗
          stackAt fsp resStack ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - resStack) ∗
          (ownedBytesRest A.repAlloc coinsCap coinsPtr (coinsOf i) ∗ ArgvFrame) =
        (memRegion (fsp + 0x1b8#64) runResSize ∗
          callAt A.repAlloc (fsp + 0x78#64) c ∗
          storesAt A.repAlloc (fsp + 0x310#64) StoresGhost.opened ∗
          (inPtr ↦ₛ inputOf i c) ∗
          coinsInstalledPlaced coinsPtr (coinsOf i) ∗
          tokenInitPlacedAt ∗
          lsLogOff ∗
          A.pool lim st s3 ∗
          stackAt fsp resStack) ∗
        (m4RestFramePlaced fsp w ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ownedBytesRest A.repAlloc inCap inPtr (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - resStack) ∗
          leakBundle) := by
      dsimp only [leakBundle]
      sep_ac_rfl
    rw [hrearr2]
    dsimp only [runSpecAnyPlaced, g_run, frameRun]
    refine sepConj_mono (Entails.pure_right hpure_run ?_)
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right (ProofLib.entails_anyHeap leakBundle)))))))
    rw [hsp3]
    exact Entails.refl _
  exact sepWPp_weaken_pre hpre_run (hk s3 hs3 hsp3 htr3_s htr3_0 hfs3_s)

/-! ## 4. Post-`run` `Err` & `Ok` Tails (`M+0x7a4 → M+0xb24` / `M+0x7b0`) -/

private theorem m4_step_check_err_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hs : InMainPlaced CodeOk s0 s 0x7a4)
    (hk : ∀ s' : State,
      InMainPlaced CodeOk s0 s' 0xb24 →
      CalleeSavedPreserved s s' →
      s'.trace = s.trace →
      s'.fs = s.fs →
      VmPreserved s s' →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (((s.sp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (((s.sp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ F)
      Q Qp (mainOom s0) := by
  have hpc : s.pc = (blkPl_617).base + 1956#64 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp_al : s.spAligned = true := hs.spAligned_state
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 2852#64) hs.inv
    fun _m_strip => ?_
  have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro _m_real hnsp hinv'
  exact hk _
    (InMainPlaced.mk_step hs
      (by simp only [mPcPlaced_eq, arm64_norm])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      hinv'
      (by simp only [calleeSavedVRegs, arm64_norm]))
    (calleeSavedPreserved_of_regs
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [calleeSavedVRegs, arm64_norm]))
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
      by simp only [arm64_norm], fun a => congrFun hnsp.2.1 a,
      LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩

private theorem m4_step_check_ok_vm [LibsignalPlacement] {CodeOk : Memory → Prop}
    [hCI : LsCodeInv CodeOk]
    {H : LibsignalHooks} {s0 s : State} {cap : BitVec 64} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hs : InMainPlaced CodeOk s0 s 0x7a4)
    (hcap : cap.toNat < 2 ^ 63)
    (hk : ∀ s' : State,
      InMainPlaced CodeOk s0 s' 0x7b0 →
      CalleeSavedPreserved s s' →
      s'.trace = s.trace →
      s'.fs = s.fs →
      VmPreserved s s' →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (((s.sp + 0x1b8#64) ↦₆₄ cap) ∗ F)
        Q Qp (mainOom s0)) :
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (((s.sp + 0x1b8#64) ↦₆₄ cap) ∗ F)
      Q Qp (mainOom s0) := by
  have hneq : (cap + 1#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    bv_omega
  have hneq2 : (cap == 0xffffffffffffffff#64) = false := by
    rw [beq_eq_false_iff_ne]
    bv_omega
  have hpc : s.pc = (blkPl_617).base + 1956#64 := hs.pc
  have hrun : s.status = .Running := hs.run
  have hsp_al : s.spAligned = true := hs.spAligned_state
  rw [mProgPlaced_eq]
  refine sepWPp_seq_codeOk_vm (CodeOk := CodeOk) (mid := (blkPl_617).base + 1968#64) hs.inv
    fun _m_strip => ?_
  have hal_strip : (s.setMem _m_strip).spAligned = true := hsp_al
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro _m_real hnsp hinv'
  exact hk _
    (InMainPlaced.mk_step hs
      (by simp only [mPcPlaced_eq, arm64_norm])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      hinv'
      (by simp only [calleeSavedVRegs, arm64_norm]))
    (calleeSavedPreserved_of_regs
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [calleeSavedVRegs, arm64_norm]))
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩,
      by simp only [arm64_norm], fun a => congrFun hnsp.2.1 a,
      LibsignalBinary.Heap.FdsHiFrame.of_fs_eq (by simp only [arm64_norm])⟩

theorem m4_err_tail_pool_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {uuidParse : UuidParser}
    {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 sf : State}
    {stk hookStack resStack : Nat} {buf inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs_7a4 : InMainPlaced CodeOk s0 sf 0x7a4)
    (hsp_f : sf.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hx19_f : sf.readReg64 (.gpr 19#5) = buf)
    (hx23_f : sf.readReg64 (.gpr 23#5) = inCap)
    (hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hG : ∀ s_exit, s_exit.trace = sf.trace → s_exit.fs = sf.fs → G 1 s_exit)
    (hexit : ExitKPoolPlaced CodeOk H A lim s0 stk G Q Qp) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) sf
      (runResAt A.repAlloc wrOk (fsp + 0x1b8#64) (some none) ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st sf ∗ anyHeap)
      Q Qp (mainOom s0) := by
  dsimp only [runResAt]
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hstk64' : stk ≤ 2 ^ 64 := by omega
  have hext_le : mainFrameSize + max extHookStack hookStack ≤ stk := by omega
  have h1c0 : fsp + 0x1b8#64 + 8#64 = fsp + 0x1c0#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [h1c0]
  refine sepWPp_weaken_pre
    (P' := ((sf.sp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (memRegion (fsp + 0x1c0#64) (runResSize - 8) ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st sf ∗ anyHeap))
    (by rw [hsp_f]; dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine m4_step_check_err_vm hs_7a4 fun s_err hs_b24 hcs_err htr_err hfs_err hvm_err => ?_
  have hx23_err : s_err.readReg64 (.gpr 23#5) = inCap := hcs_err.2.2.2.2.1.trans hx23_f
  have hx24_err : s_err.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
    hcs_err.2.2.2.2.2.1.trans hx24_f
  have hx19_err : s_err.readReg64 (.gpr 19#5) = buf := hcs_err.1.trans hx19_f
  have hpool_err : A.pool lim st sf = A.pool lim st s_err :=
    (A.pool_of_vmPreserved hvm_err).symm
  have hclose_err :
      ((sf.sp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        (memRegion (fsp + 0x1c0#64) (runResSize - 8) ∗
          m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st sf ∗ anyHeap) ⊢
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        locals fsp [cell fsp 0x50 inPtr] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s_err ∗ anyHeap := by
    rw [hsp_f, hpool_err]
    have hord :
        ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          (memRegion (fsp + 0x1c0#64) (runResSize - 8) ∗
            m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length)
              (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s_err ∗ anyHeap) =
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            memRegion (fsp + 0x78#64) 56 ∗
            ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            memRegion (fsp + 0x1c0#64) (runResSize - 8) ∗
            memRegion (fsp + 0x310#64) 320) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s_err ∗ anyHeap := by
      sep_ac_rfl
    rw [hord]
    exact sepConj_mono_right
      (sepConj_mono_left (m4_locals_close_err_cell_placed fsp w inPtr 0xffffffffffffffff#64))
  refine sepWPp_weaken_pre hclose_err ?_
  exact m4_step_err_block_pool_placed (st := st) (ps := ps) hc hext_le hstk64' hs_b24 hx23_err
    hx24_err hx19_err
    (fun s_exit htr_ex hfs_ex => hG s_exit (htr_ex.trans htr_err) (hfs_ex.trans hfs_err))
    hexit

theorem m4_err_tail_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {uuidParse : UuidParser}
    {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 sf : State}
    {stk hookStack resStack : Nat} {buf inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs_7a4 : InMainPlaced CodeOk s0 sf 0x7a4)
    (hsp_f : sf.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hx19_f : sf.readReg64 (.gpr 19#5) = buf)
    (hx23_f : sf.readReg64 (.gpr 23#5) = inCap)
    (hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hG : ∀ s_exit, s_exit.trace = sf.trace → s_exit.fs = sf.fs → G 1 s_exit)
    (hexit : ExitKPlaced CodeOk H A s0 stk G Q Qp) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) sf
      (runResAt A.repAlloc wrOk (fsp + 0x1b8#64) (some none) ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st sf ∗ anyHeap)
      Q Qp (mainOom s0) :=
  m4_err_tail_pool_placed hc hstk hstk64 hs_7a4 hsp_f hx19_f hx23_f hx24_f hG
    (exitKPoolPlaced_of_exitKPlaced (lim := lim) hexit)

theorem m4_ok_tail_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {i : Inputs} {c : CallV} {w : CallW} {g : StoresGhost} {out : List (BitVec 8)}
    {s0 sf : State} {stk : Nat} {buf inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    (hs_7a4 : InMainPlaced CodeOk s0 sf 0x7a4)
    (hsp_f : sf.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (hx19_f : sf.readReg64 (.gpr 19#5) = buf)
    (hx21_f : sf.readReg64 (.gpr 21#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64)
    (hx22_f : sf.readReg64 (.gpr 22#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64)
    (hx23_f : sf.readReg64 (.gpr 23#5) = inCap)
    (hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx27_f : sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length)
    (hk : ∀ s' : State,
      InMainPlaced CodeOk s0 s' 0x7b0 →
      s'.readReg64 (.gpr 19#5) = buf →
      s'.readReg64 (.gpr 21#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x310#64 →
      s'.readReg64 (.gpr 22#5) = s0.sp - BitVec.ofNat 64 mainFrameSize + 0x78#64 →
      s'.readReg64 (.gpr 23#5) = inCap →
      s'.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length →
      s'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length →
      s'.trace = sf.trace →
      s'.fs = sf.fs →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A.repAlloc (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st s' ∗ anyHeap)
        Q Qp (mainOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) sf
      (runOkAt A.repAlloc (fsp + 0x1b8#64) g out ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st sf ∗ anyHeap)
      Q Qp (mainOom s0) := by
  dsimp only
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  refine sepWPp_weaken_pre (sepConj_mono_left (runOkAt_open A.repAlloc (fsp + 0x1b8#64) g out)) ?_
  rw [sepExists_sepConj_left]
  apply m4_sepWPp_exists_left_p; intro cap
  rw [sepExists_sepConj_left]
  apply m4_sepWPp_exists_left_p; intro R_ok
  rw [sepConj_assoc]
  apply SepWPp.pure_left
  rintro ⟨hcap_lt, hclose_ok⟩
  refine sepWPp_weaken_pre
    (P' := ((sf.sp + 0x1b8#64) ↦₆₄ cap) ∗
      (R_ok ∗ m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st sf ∗ anyHeap))
    (by rw [hsp_f]; dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine m4_step_check_ok_vm hs_7a4 hcap_lt fun s' hs_7b0 hcs_ok htr_ok hfs_ok hvm_ok => ?_
  have hpool_ok : A.pool lim st sf = A.pool lim st s' :=
    (A.pool_of_vmPreserved hvm_ok).symm
  have hclose_m5 :
      ((sf.sp + 0x1b8#64) ↦₆₄ cap) ∗
        (R_ok ∗ m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
          ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st sf ∗ anyHeap) ⊢
      ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗
        locals fsp (m5CellsPlaced A.repAlloc fsp inPtr g out) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s' ∗ anyHeap := by
    rw [hsp_f, hpool_ok]
    have hord1 :
        ((fsp + 0x1b8#64) ↦₆₄ cap) ∗
          (R_ok ∗ m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
            ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length)
              (inputOf i c) ∗
            argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s' ∗ anyHeap) =
        ownedBytes A.repAlloc inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            memRegion (fsp + 0x78#64) 56 ∗
            (((fsp + 0x1b8#64) ↦₆₄ cap) ∗ R_ok) ∗
            memRegion (fsp + 0x310#64) 320) ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s' ∗ anyHeap := by
      sep_ac_rfl
    rw [hord1]
    exact sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_left
            (Entails.trans
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_left hclose_ok))))
              (m4_locals_close_ok_placed A.repAlloc fsp w inPtr g out)))))
  refine sepWPp_weaken_pre hclose_m5 ?_
  exact hk s' hs_7b0
    (hcs_ok.1.trans hx19_f)
    (hcs_ok.2.2.1.trans hx21_f)
    (hcs_ok.2.2.2.1.trans hx22_f)
    (hcs_ok.2.2.2.2.1.trans hx23_f)
    (hcs_ok.2.2.2.2.2.1.trans hx24_f)
    (hcs_ok.2.2.2.2.2.2.2.2.1.trans hx27_f)
    htr_ok hfs_ok

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4PlacedBudgetAux
