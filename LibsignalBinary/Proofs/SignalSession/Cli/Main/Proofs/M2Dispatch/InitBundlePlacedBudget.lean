/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitBundlePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Relocatable `init` Bundle Allocation & Copy (`M+0x274`, Block `617`)

Read-only `argv` byte-splitting helpers and budget-threaded verification of `init`'s pre-key bundle
allocation (`try_allocate_in`), `memcpy` from read-only `argv[3]`, and temporary `Vec<&str>`
deallocation under `FitsEvents`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitBundlePlacedBudget

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser)
open CryptoVerification.RustHeap (LayoutOk RustAlloc)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AtCallPlaced CallV CallW InMainPlaced LsCodeInv addrWords argsBuf
   callCellsPlaced callHeap locals mPcPlaced_eq mProgPlaced mProgPlaced_eq mainFrameSize mainSaved
   ownedBytes parseArgs sepWPp_seq_codeOk)
open CryptoVerification.SignalSession.Cli.MainHops.Proofs
  (fsp_align_of_spAligned hi32_or_lo32 m2LocalsRest main_call_keepsFs_placed
   pointsTo32_pair_entails_memRegion8 pointsTo64_zero_split32
   pure_intro_entails stackAt_split_ge)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AddressRO.AllocRoPlacedBudget
  (memcpy2_ro_rocl session2MemcpyROBudgetSpecX)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (argvAtROP)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (MainCalleesROBlk617)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CliStrictPlaced (cStrAtRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget
  (TryAllocateInEnv tryAllocateInEvents tryAllocateInSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (tryAllocateInRustSpecOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.TailPlacedBudget
  (step_ok_tail_548_gen_placed)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Shared Read-Only `argv` Byte-Splitting Helpers -/

theorem cStrAtRO_split (p : BitVec 64) (bs : List (BitVec 8)) :
    cStrAtRO p bs = (p ↦ᵣ bs) ∗ ((p + BitVec.ofNat 64 bs.length) ↦₈ᵣ 0#8) := by
  dsimp only [cStrAtRO]
  rw [ProofLib.pointsToBytesRO_append, ProofLib.pointsToBytesRO_cons,
    ProofLib.pointsToBytesRO_nil, sepConj_emp]

theorem bytes4_eq_pointsTo32RO (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦ᵣ [b0, b1, b2, b3]) = (a ↦₃₂ᵣ (b3 ++ b2 ++ b1 ++ b0)) :=
  ProofLib.pointsToBytesRO4_eq_pointsTo32RO a b0 b1 b2 b3

theorem bytes6_eq_pointsTo32_16RO (a : BitVec 64) (b0 b1 b2 b3 b4 b5 : BitVec 8) :
    (a ↦ᵣ [b0, b1, b2, b3, b4, b5]) =
      (a ↦₃₂ᵣ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₁₆ᵣ (b5 ++ b4)) := by
  rw [show [b0, b1, b2, b3, b4, b5] = [b0, b1, b2, b3] ++ [b4, b5] from rfl,
    ProofLib.pointsToBytesRO_append, show ([b0, b1, b2, b3] : List (BitVec 8)).length = 4 from rfl,
    ProofLib.pointsToBytesRO4_eq_pointsTo32RO, ProofLib.pointsToBytesRO2_eq_pointsTo16RO]

private theorem pool_congr_vm {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {s' : State}
    (hbs : s'.brkStart = s.brkStart) (hbrk : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0) (hphys : s'.physMemAvail = s.physMemAvail)
    (hperm : ∀ a : BitVec 64, s'.mem.perm a = s.mem.perm a)
    (hfs : s'.fs = s.fs := by first | rfl | simp +zetaDelta only [wp_norm, arm64_norm]) :
    A.pool lim st s' = A.pool lim st s :=
  A.pool_of_vmPreserved ⟨⟨hbs, hbrk, htp⟩, hphys, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

private theorem peek_sepWPp_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ s', s' = s → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  h s rfl

private theorem cells3_to_memRegion_24 (a : BitVec 64) (v0 v1 v2 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ⊢ memRegion a 24 := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
    ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion a v0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) v1)
      (pointsTo64_entails_memRegion (a + 16#64) v2))

private theorem cells32_64_to_memRegion_32 (a : BitVec 64) (u0 u1 : BitVec 32)
    (v1 v2 v3 : BitVec 64) :
    (a ↦₃₂ u0) ∗ ((a + 4#64) ↦₃₂ u1) ∗ ((a + 8#64) ↦₆₄ v1) ∗
      ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢ memRegion a 32 := by
  rw [show (32 : Nat) = 8 + 24 by rfl, ProofLib.memRegion_split a 8 24 (by decide)]
  refine Entails.trans (Entails.of_eq (show
    (a ↦₃₂ u0) ∗ ((a + 4#64) ↦₃₂ u1) ∗ ((a + 8#64) ↦₆₄ v1) ∗
      ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) =
    ((a ↦₃₂ u0) ∗ ((a + 4#64) ↦₃₂ u1)) ∗
      (((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3))
    by sep_ac_rfl)) (sepConj_mono (pointsTo32_pair_entails_memRegion8 a u0 u1) ?_)
  have hc3 := cells3_to_memRegion_24 (a + 8#64) v1 v2 v3
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hc3

private theorem ownedBytes_exact (A : RustAlloc) {p' : BitVec 64} {bs : List (BitVec 8)}
    (hpos : 0 < bs.length) (hle : bs.length ≤ 16384) (hp' : p' ≠ 0#64) :
    A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      ownedBytes A (BitVec.ofNat 64 bs.length) p' (BitVec.ofNat 64 bs.length) bs := by
  have htn : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0; have h := congrArg BitVec.toNat h0; rw [htn] at h
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz] at h; omega
  dsimp only [ownedBytes]
  simp only [hne0, ↓reduceIte, htn, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  exact pure_intro_entails ⟨trivial, Nat.le_refl _, by omega, hp'⟩ (Entails.refl _)

/-- Deterministic `AllocEvent` envelope of `step_init_bundle_274_placed`'s `try_allocate_in` call
on `argv[3]` (`bs3`). -/
def InitBundleAllocEnv (bs3 : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = rustAllocEvents bs3.length 1

set_option maxHeartbeats 800000 in
theorem step_init_bundle_274_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 w3 w4 w1 devw : BitVec 64}
    {peer : AddrV} {g : AddrGhost} {bs1 bs2 bs3 : List (BitVec 8)}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hbs3_pos : 0 < bs3.length) (hbs3_le : bs3.length ≤ 16384)
    (hfit : FitsEvents M lim st (rustAllocEvents bs3.length 1))
    (hparse_ok : parseArgs uuidParse (i.argv.map bytesOfString) = some (.init peer bs3))
    (hs : InMainPlaced CodeOk s0 s 0x274)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length)
    (hx27 : s.readReg64 (.gpr 27#5) = p3)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hnext : ∀ (s' : State) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
          argvAtROP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim
            (M.stepEvents (rustDeallocEvents (vcap.toNat * 16) 8)
              (M.stepEvents (rustAllocEvents bs3.length 1) st)) s' ∗
          Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x1b8#64) ↦₆₄ g.name.cap) ∗ ((fsp + 0x1c0#64) ↦₆₄ g.name.ptr) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 peer.name.length) ∗ ((fsp + 0x1d0#64) ↦₆₄ devw) ∗
        addrWords A.repAlloc peer g.name.cap g.name.ptr (BitVec.ofNat 64 peer.name.length) devw ∗
        argsBuf A.repAlloc vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        m2LocalsRest fsp ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ Statics)
      Q Qp oom := by
  dsimp only
  have htry : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsmpl.base 588)
      (withLsRoCl lsmpl (tryAllocateInRustSpecOf resStack A lim).keepsFs) := hc.tryAllocateIn3
  have hmemcpy : subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
      (withLsRoCl lsmpl session2MemcpyROBudgetSpecX.keepsFs) :=
    memcpy2_ro_rocl (prog := lsProg_617 H) (i := 617) hc.allocFs (by decide)
  have hres_le : resStack ≤ stk - mainFrameSize := by omega
  have hext_le : extHookStack ≤ stk - mainFrameSize := by
    dsimp only [mainFrameSize, extHookStack] at hstk ⊢; omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  have htn3 : (BitVec.ofNat 64 bs3.length).toNat = bs3.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne3 : (BitVec.ofNat 64 bs3.length == 0#64) = false := by
    apply beq_false_of_ne; intro h0; have h := congrArg BitVec.toNat h0
    rw [htn3] at h
    have hz : (0#64).toNat = 0 := rfl
    rw [hz] at h; omega
  rw [stackAt_split_ge (s0.sp - BitVec.ofNat 64 mainFrameSize) hres_le hsub64]
  obtain ⟨hpc, hrun, hsp, hfp, hinv, hvregs, hsp0⟩ := hs
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  have hfsp_align0 := fsp_align_of_spAligned hsp0
  generalize hfsp : s0.sp - BitVec.ofNat 64 mainFrameSize = fsp at hsp hfsp_align0 ⊢
  have hfit_try : FitsEnv M lim st
      (TryAllocateInEnv ⟨fsp + 0x1b8#64, BitVec.ofNat 64 bs3.length, 1#64, 1#64⟩) := by
    intro evs hevs
    dsimp only [TryAllocateInEnv, tryAllocateInEvents] at hevs
    rw [htn3, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mul_one] at hevs
    rwa [hevs]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsmpl.base 588) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine main_call_keepsFs_placed (CodeOk := CodeOk)
    (x := (⟨fsp + 0x1b8#64, BitVec.ofNat 64 bs3.length, 1#64, 1#64⟩, st)) (k_ret := 0x290)
    (F := ((fsp + 0x1d0#64) ↦₆₄ devw) ∗
      addrWords A.repAlloc peer g.name.cap g.name.ptr (BitVec.ofNat 64 peer.name.length) devw ∗
      argsBuf A.repAlloc vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
      argvAtROP (s0.readReg64 .x1)
        ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
      mainSaved s0 ∗
      ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
      m2LocalsRest fsp ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - resStack) ∗ Statics)
    htry hinv1
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
    (by simp only [arm64_norm, *])
    (hP := ?_) (hnext := ?_)
  · dsimp only [tryAllocateInRustSpecOf, tryAllocateInSpecOf]
    conv => arg 2; rw [pool_congr_vm A lim st s (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm])]
    have hc3 : ((fsp + 0x1b8#64) ↦₆₄ g.name.cap) ∗ ((fsp + 0x1c0#64) ↦₆₄ g.name.ptr) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 peer.name.length) ⊢
        memRegion (fsp + 0x1b8#64) 24 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        cells3_to_memRegion_24 (fsp + 0x1b8#64) g.name.cap g.name.ptr
          (BitVec.ofNat 64 peer.name.length)
    have hlay3 : LayoutOk ((BitVec.ofNat 64 bs3.length).toNat * (1#64 : BitVec 64).toNat)
        (1#64 : BitVec 64).toNat := by
      rw [htn3, show (1#64 : BitVec 64).toNat = 1 from rfl]
      exact ⟨by omega, ⟨0, rfl⟩, by omega⟩
    have hrust3 : RustLayoutOk ((BitVec.ofNat 64 bs3.length).toNat * (1#64 : BitVec 64).toNat)
        (1#64 : BitVec 64).toNat := ⟨hlay3, by decide⟩
    have hn3_pos : 0 < (BitVec.ofNat 64 bs3.length).toNat := by rw [htn3]; exact hbs3_pos
    have hstr_pos : 0 < (1#64 : BitVec 64).toNat := by decide
    refine Entails.trans ?_
      (sepConj_mono_left (pure_intro_entails
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          hn3_pos, hstr_pos, hrust3, hfit_try⟩ (Entails.refl _)))
    have hgrp3 : ∀ (C0 C1 C2 R : SepProp), C0 ∗ C1 ∗ C2 ∗ R ⊢ (C0 ∗ C1 ∗ C2) ∗ R :=
      fun _ _ _ _ => Entails.of_eq (by sep_ac_rfl)
    exact Entails.trans (hgrp3 _ _ _ _)
      (Entails.trans (sepConj_mono_left hc3)
        (Entails.of_eq (by simp only [arm64_norm, hsp]; sep_ac_rfl)))
  intro sm1 hin1 hcs1 hfs1
  dsimp only [tryAllocateInRustSpecOf, tryAllocateInSpecOf]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun p' => ?_
  have hx19_1 : sm1.readReg64 (.gpr 19#5) = buf := hcs1.1.trans (by simp only [arm64_norm, *])
  have hx20_1 : sm1.readReg64 (.gpr 20#5) = vptr := hcs1.2.1.trans (by simp only [arm64_norm, *])
  have hx21_1 : sm1.readReg64 (.gpr 21#5) = g.name.ptr := hcs1.2.2.1.trans (by simp only [arm64_norm, *])
  have hx22_1 : sm1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 peer.name.length :=
    hcs1.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx23_1 : sm1.readReg64 (.gpr 23#5) = vcap := hcs1.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx24_1 : sm1.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
    hcs1.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx25_1 : sm1.readReg64 (.gpr 25#5) = g.name.cap :=
    hcs1.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx26_1 : sm1.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length :=
    hcs1.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx27_1 : sm1.readReg64 (.gpr 27#5) = p3 :=
    hcs1.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx28_1 : sm1.readReg64 (.gpr 28#5) = devw :=
    hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  obtain ⟨hpc1, hrun1, hsp1, hfp1, hinv1', hvregs1, _⟩ := hin1
  rw [hfsp] at hsp1
  rw [mPcPlaced_eq] at hpc1
  have hpure_pull : ∀ (C0 C1 C2 P0 R1 R2 : SepProp),
      (C0 ∗ C1 ∗ C2 ∗ P0 ∗ R1) ∗ R2 = P0 ∗ (C0 ∗ C1 ∗ C2 ∗ R1 ∗ R2) :=
    fun _ _ _ _ _ _ => by sep_ac_rfl
  rw [hpure_pull]
  refine SepWPp.pure_elim fun ⟨hp'_ne, _, htr1, hevs⟩ => ?_
  have hevs_eq : evs = rustAllocEvents bs3.length 1 := by
    dsimp only [TryAllocateInEnv, tryAllocateInEvents] at hevs
    rw [htn3, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mul_one] at hevs
    exact hevs
  subst hevs_eq
  let st1 := M.stepEvents (rustAllocEvents bs3.length 1) st
  have htr1' : sm1.trace = s0.trace :=
    (by simpa only [arm64_norm] using htr1 : sm1.trace = s.trace).trans htr
  have hfs1' : sm1.fs = s0.fs :=
    (by simpa only [arm64_norm] using hfs1 : sm1.fs = s.fs).trans hfs
  have h1_nat : (1#64 : BitVec 64).toNat = 1 := rfl
  simp only [h1_nat, Nat.mul_one, htn3, BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hsp]
  have hstk_perm : ∀ (C0 C1 C2 LV MR PL S0 D AW AB1 AB2 AV MS W3 W4 W1 M2 STX ST : SepProp),
      C0 ∗ C1 ∗ C2 ∗ LV ∗ MR ∗ PL ∗ S0 ∗
        D ∗ AW ∗ AB1 ∗ AB2 ∗ AV ∗ MS ∗ W3 ∗ W4 ∗ W1 ∗ M2 ∗ STX ∗ ST =
      C0 ∗ C1 ∗ C2 ∗ LV ∗ MR ∗ PL ∗ (STX ∗ S0) ∗
        D ∗ AW ∗ AB1 ∗ AB2 ∗ AV ∗ MS ∗ W3 ∗ W4 ∗ W1 ∗ M2 ∗ ST :=
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by sep_ac_rfl
  rw [hstk_perm, ← stackAt_split_ge fsp hres_le hsub64, stackAt_split_ge fsp hext_le hsub64]
  have hc0_split : ((fsp + 440#64) ↦₆₄ 0#64) =
      ((fsp + 0x1b8#64) ↦₃₂ 0#32) ∗ (((fsp + 0x1b8#64) + 4#64) ↦₃₂ 0#32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_zero_split32 (fsp + 0x1b8#64)
  rw [hc0_split]
  dsimp only [argvAtROP]
  rw [cStrAtRO_split p3 bs3]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ memcpyName) hinv1'
  wp_steps_sync_pool (lsρ memcpyName)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv2
  refine peek_sepWPp_state fun s_mc hs_mc => ?_
  refine main_call_keepsFs_placed (CodeOk := CodeOk) (x := (p', p3, bs3)) (k_ret := 0x2c0)
    (F := ((fsp + 0x1b8#64) ↦₃₂ 0#32) ∗ (((fsp + 0x1b8#64) + 4#64) ↦₃₂ 0#32) ∗
      ((fsp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗ ((fsp + 0x1c8#64) ↦₆₄ p') ∗
      ((fsp + 0x1d0#64) ↦₆₄ devw) ∗ A.live p' bs3.length 1 ∗
      addrWords A.repAlloc peer g.name.cap g.name.ptr (BitVec.ofNat 64 peer.name.length) devw ∗
      argsBuf A.repAlloc vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
      argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
      ((s0.readReg64 .x1) ↦₆₄ᵣ p0) ∗ cStrAtRO p0 (bytesOfString "libsignal-cli") ∗
      ((s0.readReg64 .x1 + 8#64) ↦₆₄ᵣ p1) ∗ cStrAtRO p1 bs1 ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64) ↦₆₄ᵣ p2) ∗ cStrAtRO p2 bs2 ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ p3) ∗
      ((p3 + BitVec.ofNat 64 bs3.length) ↦₈ᵣ 0#8) ∗
      ((s0.readReg64 .x1 + 8#64 + 8#64 + 8#64 + 8#64) ↦₆₄ᵣ 0#64) ∗
      mainSaved s0 ∗
      ((fsp + 0x40#64) ↦₆₄ devw) ∗ ((fsp + 0x48#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      ((fsp + 0x58#64) ↦₆₄ g.name.ptr) ∗ m2LocalsRest fsp ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
        (stk - mainFrameSize - extHookStack) ∗ A.pool lim st1 s_mc ∗ Statics)
    hmemcpy hinv2
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [calleeSavedVRegs, arm64_norm, *]) hsp0
    (by simp only [arm64_norm, *])
    (hP := ?_) (hnext := ?_)
  · dsimp only [session2MemcpyROBudgetSpecX]
    refine Entails.trans ?_
      (sepConj_mono_left (pure_intro_entails
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *]⟩ (Entails.refl _)))
    rw [hs_mc]
    exact Entails.of_eq (by simp only [arm64_norm, hsp1]; sep_ac_rfl)
  intro sm2 hin2 hcs2 hfs2
  dsimp only [session2MemcpyROBudgetSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, htr2, hvm2⟩ => ?_
  have hx19_2 : sm2.readReg64 (.gpr 19#5) = buf := hcs2.1.trans (by simp only [arm64_norm, *])
  have hx20_2 : sm2.readReg64 (.gpr 20#5) = vptr := hcs2.2.1.trans (by simp only [arm64_norm, *])
  have hx21_2 : sm2.readReg64 (.gpr 21#5) = p' := hcs2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx22_2 : sm2.readReg64 (.gpr 22#5) = BitVec.ofNat 64 peer.name.length :=
    hcs2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx23_2 : sm2.readReg64 (.gpr 23#5) = vcap := hcs2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx24_2 : sm2.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
    hcs2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx25_2 : sm2.readReg64 (.gpr 25#5) = g.name.cap :=
    hcs2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have hx26_2 : sm2.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length :=
    hcs2.2.2.2.2.2.2.2.1.trans (by simp only [arm64_norm, *])
  have htr2' : sm2.trace = s0.trace :=
    htr2.trans ((by simp only [arm64_norm, *] : _ = sm1.trace).trans htr1')
  have hfs2' : sm2.fs = s0.fs :=
    hfs2.trans ((by simp only [arm64_norm, *] : _ = sm1.fs).trans hfs1')
  rw [← hs_mc] at hvm2
  have hpool_sm2 : A.pool lim st1 s_mc = A.pool lim st1 sm2 :=
    (A.pool_of_vmPreserved hvm2).symm
  rw [hpool_sm2]
  obtain ⟨hpc2, hrun2, hsp2, hfp2, hinv2', hvregs2, _⟩ := hin2
  rw [hfsp] at hsp2
  rw [mPcPlaced_eq] at hpc2
  simp only [arm64_norm, hsp1]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x550#64) hinv2'
  wp_steps_sync_pool ((blkPl_617).base + 0x550#64)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv3
  have hin3 : InMainPlaced CodeOk s0 _ 0x550 := {
    pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
    run := by simp only [arm64_norm, *]
    sp := by simp only [arm64_norm, *]
    fp := by simp only [arm64_norm, *]
    inv := hinv3
    vregs := by simp only [calleeSavedVRegs, arm64_norm, *]
    spAligned := hsp0 }
  let w : CallW := ⟨g.name.cap, g.name.ptr, BitVec.ofNat 64 peer.name.length, devw,
    BitVec.ofNat 64 bs3.length, p', BitVec.ofNat 64 bs3.length⟩
  rw [← mProgPlaced_eq]
  refine SepWPp.weaken_pre ?_
    (step_ok_tail_548_gen_placed (hookStack := hookStack) (resStack := resStack) (st := st1)
      (buf := buf) (vcap := vcap) (vptr := vptr)
      (w := w) (c := .init peer bs3) (ps := [(p1, bs1), (p2, bs2), (p3, bs3)])
      (ArgvFrame := argvAtROP (s0.readReg64 .x1)
        ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]))
      (Statics := Statics)
      hc.allocFs hstk hstk64 hparse_ok hin3
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, w, *]) (by simp only [arm64_norm, w, *])
      (by simp only [arm64_norm, w, *]) (by simp only [arm64_norm, w, *]; exact hi32_or_lo32 p')
      hvcap (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hnext)
  dsimp only [w, callHeap]
  rw [hfsp]
  have hrhs : ∀ (AB_V AW OB AB_B AV MS W3 W4 W1 M32 R : SepProp),
      M32 ∗ OB ∗ (AB_V ∗ AW ∗ AB_B ∗ AV ∗ MS ∗ W3 ∗ W4 ∗ W1 ∗ R) ⊢
        AB_V ∗ (AW ∗ OB) ∗ AB_B ∗ AV ∗ MS ∗ W3 ∗ W4 ∗ W1 ∗ M32 ∗ R :=
    fun _ _ _ _ _ _ _ _ _ _ _ => Entails.of_eq (by sep_ac_rfl)
  refine Entails.trans ?_ (hrhs _ _ _ _ _ _ _ _ _ _ _)
  dsimp only [argvAtROP]
  rw [cStrAtRO_split p3 bs3, stackAt_split_ge fsp hext_le hsub64]
  have hown := ownedBytes_exact A.repAlloc hbs3_pos hbs3_le hp'_ne
  rw [A.repAlloc_live_norm] at hown
  have h32 := cells32_64_to_memRegion_32 (fsp + 0x1b8#64) 0#32 0#32
    (BitVec.ofNat 64 bs3.length) p' devw
  simp only [BitVec.add_assoc, BitVec.reduceAdd, show Reg.x1 = Reg.gpr 1#5 from rfl] at h32 ⊢
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h32 (sepConj_mono_left hown))

theorem step_init_bundle_274_placed_any_st [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {M : AllocCostModel} {H : LibsignalHooks} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ}
    {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
    {stk hookStack resStack : Nat} {buf vcap vptr p0 p1 p2 p3 w3 w4 w1 devw : BitVec 64}
    {peer : AddrV} {g : AddrGhost} {bs1 bs2 bs3 : List (BitVec 8)}
    {Statics : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesROBlk617 A lim H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hbs3_pos : 0 < bs3.length) (hbs3_le : bs3.length ≤ 16384)
    (hfit : FitsEvents M lim st (rustAllocEvents bs3.length 1))
    (hparse_ok : parseArgs uuidParse (i.argv.map bytesOfString) = some (.init peer bs3))
    (hs : InMainPlaced CodeOk s0 s 0x274)
    (hx19 : s.readReg64 (.gpr 19#5) = buf) (hx20 : s.readReg64 (.gpr 20#5) = vptr)
    (hx23 : s.readReg64 (.gpr 23#5) = vcap)
    (hx24 : s.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : s.readReg64 (.gpr 25#5) = g.name.cap)
    (hx26 : s.readReg64 (.gpr 26#5) = BitVec.ofNat 64 bs3.length)
    (hx27 : s.readReg64 (.gpr 27#5) = p3)
    (hvcap : vcap ≠ 0#64) (htr : s.trace = s0.trace) (hfs : s.fs = s0.fs)
    (hnext : ∀ (s' : State) (st' : M.σ) (w : CallW) (c : CallV),
      parseArgs uuidParse (i.argv.map bytesOfString) = some c →
      AtCallPlaced CodeOk s0 s' w i.argv.length buf →
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (callHeap A.repAlloc w c ∗
          argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
          argvAtROP (s0.readReg64 .x1)
            ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool lim st' s' ∗ Statics)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x1b8#64) ↦₆₄ g.name.cap) ∗ ((fsp + 0x1c0#64) ↦₆₄ g.name.ptr) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 peer.name.length) ∗ ((fsp + 0x1d0#64) ↦₆₄ devw) ∗
        addrWords A.repAlloc peer g.name.cap g.name.ptr (BitVec.ofNat 64 peer.name.length) devw ∗
        argsBuf A.repAlloc vcap vptr [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        argsBuf A.repAlloc (BitVec.ofNat 64 i.argv.length) buf [(p1, bs1), (p2, bs2), (p3, bs3)] ∗
        argvAtROP (s0.readReg64 .x1)
          ((p0, bytesOfString "libsignal-cli") :: [(p1, bs1), (p2, bs2), (p3, bs3)]) ∗
        mainSaved s0 ∗
        ((fsp + 0x40#64) ↦₆₄ w3) ∗ ((fsp + 0x48#64) ↦₆₄ w4) ∗ ((fsp + 0x58#64) ↦₆₄ w1) ∗
        m2LocalsRest fsp ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool lim st s ∗ Statics)
      Q Qp oom :=
  step_init_bundle_274_placed hc hstk hstk64 hbs3_pos hbs3_le hfit hparse_ok hs
    hx19 hx20 hx23 hx24 hx25 hx26 hx27 hvcap htr hfs fun s' w' c' hp ha =>
      hnext s' _ w' c' hp ha

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Dispatch.InitBundlePlacedBudget
