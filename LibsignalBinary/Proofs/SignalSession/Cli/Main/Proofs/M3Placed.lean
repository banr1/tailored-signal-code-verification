/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ReadPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Relocatable `main` Hop M3 (`M+0x568 → M+0x5dc`, Block `617`)

Verifies `main`'s third hop on Block `617` under `[LibsignalPlacement]`: tag dispatch between empty
input (`keygen` / `init` at `M+0x57c`) and `read_stdin` (`send` / `recv` at `M+0x59c`), followed by
`read_file("coins")` (`M+0x5b0 → M+0x5dc`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open M3Helpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 800000 in
private theorem step_empty_in_0x57c_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser}
    {io : IoModel} {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf p0 : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i))
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (htag_le1 : ¬ (1 < c.tag))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x57c)
    (hst_tr : st.trace = s.trace)
    (hst_fs : st.fs = s0.fs)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPlacedRet CodeOk H A s0 ret stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64),
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      ProofLib.SepWPp (mProgPlaced H) ret s'
        (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret st
      (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hc1 := locals_carve_cell fsp
    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 [cell fsp 0x58 w.w1]
  rw [show callCellsPlaced fsp w =
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] ++ [cell fsp 0x58 w.w1] by rfl,
    hc1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun c50 => ?_
  rw [show [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] ++ cell fsp 0x50 c50 :: [cell fsp 0x58 w.w1] =
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] by rfl]
  have hc2 := locals_carve_cell fsp
    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] 0x60 []
  rw [List.append_nil] at hc2; rw [hc2]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun c60 => ?_
  have hc3 := locals_carve_cell fsp
    ([cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] ++
      [cell fsp 0x60 c60]) 0x68 []
  rw [List.append_nil] at hc3; rw [hc3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun c68 => ?_
  have hc4 := locals_carve_cell fsp
    ([cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] ++
      [cell fsp 0x60 c60] ++ [cell fsp 0x68 c68]) 0x70 []
  rw [List.append_nil] at hc4; rw [hc4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun c70 => ?_
  have hloc_open :
      locals fsp
        ([cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 c50, cell fsp 0x58 w.w1] ++
          [cell fsp 0x60 c60] ++ [cell fsp 0x68 c68] ++ [cell fsp 0x70 c70]) =
      ((fsp + 0x50#64) ↦₆₄ c50) ∗ ((fsp + 0x60#64) ↦₆₄ c60) ∗
        ((fsp + 0x68#64) ↦₆₄ c68) ∗ ((fsp + 0x70#64) ↦₆₄ c70) ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
        memRegion (fsp + 0x78#64) (0x480 - 0x78) := by
    simp only [locals, localsFrom, List.nil_append, List.cons_append,
      Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero, emp_sepConj]
    ac_rfl
  rw [hloc_open]
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x5b0#64) hinv
  wp_steps
  apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
  intro hinv1
  have hin1 : InMainPlaced CodeOk s0 _ 0x5b0 := {
    inv := hinv1
    pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
    run := by simp only [arm64_norm, *]
    sp := by (try simp only [arm64_norm]); exact hst.sp
    fp := by (try simp only [arm64_norm]); exact hst.fp
    vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hst.vregs
    spAligned := hst.spAligned
  }
  have hin_nil : inputOf i c = [] := by simp only [inputOf, htag_le1, ↓reduceIte]
  refine SepWPp.weaken_pre ?_
    (step_from_0x5b0_placed (inOk := true) (inCap := 0#64) (inPtr := 1#64) (x27 := 0#64)
      (c := c) (w := w) (p0 := p0) (ps := ps) hc hio hstk hstk64 hcoinsOk hcoins hs_tr hin1
      (by (try simp only [arm64_norm, hx19]); try rfl)
      (by (try simp only [arm64_norm, hx20]); try rfl)
      (by (try simp only [arm64_norm, hx22]); try rfl)
      (by (try simp only [arm64_norm]); try rfl)
      (by (try simp only [arm64_norm, hx24]); try rfl)
      (by (try simp only [arm64_norm, hx25]); try rfl)
      (by (try simp only [arm64_norm, hx26]); try rfl)
      (by (try simp only [arm64_norm]); try rfl)
      (by (try simp only [arm64_norm, hw5_orr]); try rfl)
      (by (try simp only [arm64_norm, hst_fs, hs0fs]); try rfl)
      (by (try simp only [arm64_norm, hst_tr]); try rfl) hpanic hexit hnext)
  have hloc_close :
      ((fsp + 0x50#64) ↦₆₄ 1#64) ∗ ((fsp + 0x60#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x68#64) ↦₆₄ 1#64) ∗ ((fsp + 0x70#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
        memRegion (fsp + 0x78#64) (0x480 - 0x78) ⊢
      locals fsp
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1] := by
    have hpack :
        locals fsp
          [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1,
           cell fsp 0x60 0#64, cell fsp 0x68 1#64, cell fsp 0x70 0#64] =
        ((fsp + 0x50#64) ↦₆₄ 1#64) ∗ ((fsp + 0x60#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x68#64) ↦₆₄ 1#64) ∗ ((fsp + 0x70#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
          ((fsp + 0x58#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
          memRegion (fsp + 0x78#64) (0x480 - 0x78) := by
      simp only [locals, localsFrom, Nat.reduceAdd, Nat.reduceSub, ProofLib.memRegion_zero,
        emp_sepConj]
      ac_rfl
    rw [← hpack]
    have hf1 := locals_forget_cell fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1,
       cell fsp 0x60 0#64, cell fsp 0x68 1#64] 0x70 0#64 []
    have hf2 := locals_forget_cell fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1,
       cell fsp 0x60 0#64] 0x68 1#64 []
    have hf3 := locals_forget_cell fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 1#64, cell fsp 0x58 w.w1]
      0x60 0#64 []
    simp only [List.append_nil, List.cons_append, List.nil_append] at hf1 hf2 hf3
    exact Entails.trans hf1 (Entails.trans hf2 hf3)
  have hin_inv : emp ⊢ inInvOpt true A i c 0#64 1#64 0#64 := by
    dsimp only [inInvOpt, inInv]
    rw [hin_nil]
    exact entails_pure_intro_left (Nat.zero_le _)
      (entails_pure_intro_left rfl (emp_entails_ownedBytes_nil A))
  refine Entails.trans (Entails.of_eq (show _ =
    emp ∗
      (((fsp + 0x50#64) ↦₆₄ 1#64) ∗ ((fsp + 0x60#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x68#64) ↦₆₄ 1#64) ∗ ((fsp + 0x70#64) ↦₆₄ 0#64) ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗ ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗ memRegion fsp 0x40 ∗
        memRegion (fsp + 0x78#64) (0x480 - 0x78)) ∗
      (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗
        A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617) by simp only [emp_sepConj]; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hin_inv (sepConj_mono_left hloc_close)) ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Relocatable proof of `main_m3` (`M+0x568 → M+0x5dc`) under `[LibsignalPlacement]`. -/
theorem main_m3_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i)) (hs0tr : s0.trace = [])
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hs : AtCallPlaced CodeOk s0 s w i.argv.length buf)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPlacedRet CodeOk H A s0 ret stk
      (fun code s' => code = 2 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        (¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length)) ∧ s'.trace = s.trace)
      Q Qp)
    (hnext : ∀ (s' : State) (coinsCap coinsPtr inCap inPtr : BitVec 64),
      (inputOf i c).length ≤ stdinCapBytes →
      AtM4Placed CodeOk i s0 s' w c i.argv.length buf coinsCap coinsPtr inCap →
      ProofLib.SepWPp (mProgPlaced H) ret s'
        (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
        Q Qp oom) :
    ProofLib.SepWPp (mProgPlaced H) ret s
      (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  let _ := hs0tr
  let _ := hparse
  have hw5_orr : (s.readReg64 (.gpr 28#5) ||| s.readReg64 (.gpr 21#5)) = w.w5 := by
    have hz := zext32_eq_self_of_lt hs.x21lo
    simpa only [hz] using hs.w5
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
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    have hcond : ConditionHolds .MI (subsPState64 0x8000000000000000#64 0#64) = true := by
      rw [conditionHolds_mi_subsPState64]; rfl
    have hult : (1#64).ult 0#64 = false := rfl
    have hpc := hs.base.pc; have hrun := hs.base.run; have hinv := hs.base.inv
    have hx25 := hs.w0
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x57c#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x57c := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, hrun]
      sp := by (try simp only [arm64_norm]); exact hs.base.sp
      fp := by (try simp only [arm64_norm]); exact hs.base.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hs.base.vregs
      spAligned := hs.base.spAligned
    }
    exact step_empty_in_0x57c_placed hc hio hstk hstk64 hs0fs hcoinsOk hcoins
      (by simp [CallV.tag]) hs.trace hin1
      (by (try simp only [arm64_norm]); try rfl)
      (by (try simp only [arm64_norm, hs.fs]); try rfl)
      (by (try simp only [arm64_norm, hs.x19]); try rfl)
      (by simp only [arm64_norm, CallV.tag, *])
      (by (try simp only [arm64_norm, hs.w2]); try rfl)
      (by (try simp only [arm64_norm, hs.x24]); try rfl)
      (by (try simp only [arm64_norm, hs.w0]); try rfl)
      (by (try simp only [arm64_norm, hs.w6]); try rfl)
      (by (try simp only [arm64_norm, hw5_orr]); try rfl)
      hpanic hexit hnext
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
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_lt => ?_
    have hmsb := msb_false_of_lt hw0_lt
    have hcond : ConditionHolds .MI (subsPState64 w.w0 0#64) = false :=
      (conditionHolds_mi_subsPState64 w.w0 0#64).trans hmsb
    have hult : (1#64).ult 1#64 = false := rfl
    have hpc := hs.base.pc; have hrun := hs.base.run; have hinv := hs.base.inv
    have hx25 := hs.w0
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x57c#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x57c := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, hrun]
      sp := by (try simp only [arm64_norm]); exact hs.base.sp
      fp := by (try simp only [arm64_norm]); exact hs.base.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hs.base.vregs
      spAligned := hs.base.spAligned
    }
    exact step_empty_in_0x57c_placed hc hio hstk hstk64 hs0fs hcoinsOk hcoins
      (by simp [CallV.tag]) hs.trace hin1
      (by (try simp only [arm64_norm]); try rfl)
      (by (try simp only [arm64_norm, hs.fs]); try rfl)
      (by (try simp only [arm64_norm, hs.x19]); try rfl)
      (by simp only [arm64_norm, CallV.tag, *])
      (by (try simp only [arm64_norm, hs.w2]); try rfl)
      (by (try simp only [arm64_norm, hs.x24]); try rfl)
      (by (try simp only [arm64_norm, hs.w0]); try rfl)
      (by (try simp only [arm64_norm, hs.w6]); try rfl)
      (by (try simp only [arm64_norm, hw5_orr]); try rfl)
      hpanic hexit hnext
  | send peer =>
    have hch_pure :
        callHeap A w (.send peer) =
          (⌜w.w0 = 0x8000000000000002#64⌝ ∗ callHeap A w (.send peer)) := by
      dsimp only [callHeap]
      apply ProofLib.sepProp_ext
      · exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    have hcond : ConditionHolds .MI (subsPState64 0x8000000000000002#64 0#64) = true := by
      rw [conditionHolds_mi_subsPState64]; rfl
    have hult : (1#64).ult 2#64 = true := rfl
    have hpc := hs.base.pc; have hrun := hs.base.run; have hinv := hs.base.inv
    have hx25 := hs.w0
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x59c#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x59c := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, hrun]
      sp := by (try simp only [arm64_norm]); exact hs.base.sp
      fp := by (try simp only [arm64_norm]); exact hs.base.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hs.base.vregs
      spAligned := hs.base.spAligned
    }
    exact step_stdin_0x59c_placed hc hio hstk hstk64 hs0fs hstdin hcoinsOk hcoins
      (by simp [CallV.tag]) hs.trace hin1
      (by (try simp only [arm64_norm]); try rfl)
      (by (try simp only [arm64_norm, hs.fs]); try rfl)
      (by (try simp only [arm64_norm, hs.x19]); try rfl)
      (by simp only [arm64_norm, CallV.tag, *])
      (by (try simp only [arm64_norm, hs.w2]); try rfl)
      (by (try simp only [arm64_norm, hs.x24]); try rfl)
      (by (try simp only [arm64_norm, hs.w0]); try rfl)
      (by (try simp only [arm64_norm, hs.w6]); try rfl)
      (by (try simp only [arm64_norm, hw5_orr]); try rfl)
      hpanic hexit hnext
  | recv peer =>
    have hch_pure :
        callHeap A w (.recv peer) =
          (⌜w.w0 = 0x8000000000000003#64⌝ ∗ callHeap A w (.recv peer)) := by
      dsimp only [callHeap]
      apply ProofLib.sepProp_ext
      · exact entails_pure_elim_left fun hp =>
          entails_pure_intro_left hp (entails_pure_intro_left hp (Entails.refl _))
      · exact entails_pure_elim_left fun _ => Entails.refl _
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    have hcond : ConditionHolds .MI (subsPState64 0x8000000000000003#64 0#64) = true := by
      rw [conditionHolds_mi_subsPState64]; rfl
    have hult : (1#64).ult 3#64 = true := rfl
    have hpc := hs.base.pc; have hrun := hs.base.run; have hinv := hs.base.inv
    have hx25 := hs.w0
    rw [mPcPlaced_eq] at hpc
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x59c#64) hinv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv1
    have hin1 : InMainPlaced CodeOk s0 _ 0x59c := {
      inv := hinv1
      pc := by rw [mPcPlaced_eq]; simp only [arm64_norm, *]
      run := by simp only [arm64_norm, hrun]
      sp := by (try simp only [arm64_norm]); exact hs.base.sp
      fp := by (try simp only [arm64_norm]); exact hs.base.fp
      vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hs.base.vregs
      spAligned := hs.base.spAligned
    }
    exact step_stdin_0x59c_placed hc hio hstk hstk64 hs0fs hstdin hcoinsOk hcoins
      (by simp [CallV.tag]) hs.trace hin1
      (by (try simp only [arm64_norm]); try rfl)
      (by (try simp only [arm64_norm, hs.fs]); try rfl)
      (by (try simp only [arm64_norm, hs.x19]); try rfl)
      (by simp only [arm64_norm, CallV.tag, *])
      (by (try simp only [arm64_norm, hs.w2]); try rfl)
      (by (try simp only [arm64_norm, hs.x24]); try rfl)
      (by (try simp only [arm64_norm, hs.w0]); try rfl)
      (by (try simp only [arm64_norm, hs.w6]); try rfl)
      (by (try simp only [arm64_norm, hw5_orr]); try rfl)
      hpanic hexit hnext

end CryptoVerification.SignalSession.Cli.MainHops
