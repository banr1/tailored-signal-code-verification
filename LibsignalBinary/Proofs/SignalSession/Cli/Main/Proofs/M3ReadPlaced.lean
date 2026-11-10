/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.IoSitesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Iface
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import all Init.Data.String.Defs

/-!
# Relocatable `read_stdin` and `read_file("coins")` Continuations for `main` Hop M3

Verifies `M+0x59c` (`read_stdin`) and `M+0x5b0 .. M+0x5d8` (`read_file("coins")` and error-branch
dispatch to `M+0x624`) on Block `617` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops.M3Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.SignalSession.Cli.MainHops

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Input invariant: `x27 = (inputOf i c).length` with `ownedBytes A inCap inPtr inLen (inputOf i c)`. -/
def inInv (A : RustAlloc) (i : Inputs) (c : CallV) (inCap inPtr x27 : BitVec 64) : SepProp :=
  ⌜x27 = BitVec.ofNat 64 (inputOf i c).length⌝ ∗
    ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c)

/-- Optional input invariant after `read_stdin` (`inOk = true` carries `(inputOf i c).length ≤ stdinCapBytes`
and `inInv`; `inOk = false` carries `inCap = -1` and `1 < c.tag ∧ stdinCapBytes < i.stdin.length`). -/
def inInvOpt (inOk : Bool) (A : RustAlloc) (i : Inputs) (c : CallV)
    (inCap inPtr x27 : BitVec 64) : SepProp :=
  match inOk with
  | true => ⌜(inputOf i c).length ≤ stdinCapBytes⌝ ∗ inInv A i c inCap inPtr x27
  | false => ⌜inCap = 0xffffffffffffffff#64 ∧ 1 < c.tag ∧ stdinCapBytes < i.stdin.length⌝

set_option maxHeartbeats 1200000 in
/-- Unified continuation across `read_file("coins")` (`M+0x5b0 .. M+0x5d8`) and both error tests
on Block `617` under `[LibsignalPlacement]`. -/
theorem step_from_0x5b0_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {ret : BitVec 64} {stk hookStack resStack : Nat}
    {buf p0 inCap inPtr x27 : BitVec 64} {inOk : Bool}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x5b0)
    (hx19 : st.readReg64 (.gpr 19#5) = buf)
    (hx20 : st.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag)
    (hx22 : st.readReg64 (.gpr 22#5) = w.w2)
    (hx23 : st.readReg64 (.gpr 23#5) = inCap)
    (hx24 : st.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length)
    (hx25 : st.readReg64 (.gpr 25#5) = w.w0)
    (hx26 : st.readReg64 (.gpr 26#5) = w.w6)
    (hx27 : st.readReg64 (.gpr 27#5) = x27)
    (hw5_orr : (st.readReg64 (.gpr 28#5) ||| st.readReg64 (.gpr 21#5)) = w.w5)
    (hfiles : st.fs.files = (initFsState (cliInputs i)).files)
    (hst_tr : st.trace = s.trace)
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
      (inInvOpt inOk A i c inCap inPtr x27 ∗
        callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          [cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x40 w.w3,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x48 w.w4,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x50 inPtr,
           cell (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x58 w.w1] ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  have hlen_st : s0.trace.length ≤ st.trace.length := by
    rw [hst_tr, hs_tr]
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hread := main_readFile_placed_ok hio
  have hsub_le : hookStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  have hcarve_open :=
    (locals_carve_region fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
      0x1b8 24 []).trans
    (locals_focus fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
      0x1b8 24 (memRegion (fsp + 0x1b8#64) 24) [])
  rw [List.append_nil] at hcarve_open
  rw [hcarve_open, mainLitsBlk617_eq]
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsReadFileSym) hinv
  wp_steps
  apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
  intro hinv1
  refine main_call_rocl (CodeOk := CodeOk)
    (spec := readFileLitSpecPlaced io A hookStack)
    ({ pathA := lsρ coinsLitSym, path := utf8 "coins", ret := fsp + 0x1b8#64 } : ReadFileLitGhost)
    hread
    hinv1 (by (try simp only [arm64_norm, *]); try rfl) (by (try simp only [arm64_norm, *]); try rfl)
    (by simp only [arm64_norm]; exact hal)
    (ret_pc := (blkPl_617).base + 0x5c8#64) (by (try simp only [arm64_norm, *]); try rfl)
    (hpanic := fun sf_p R' _ hp => by
      try dsimp only [readFileLitSpecPlaced] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      apply hpanic
      have h1 := hp.1.1
      refine allocFailedIn_mono_left ?_ h1
      simp only [arm64_norm]
      exact hlen_st)
    (F := inInvOpt inOk A i c inCap inPtr x27 ∗ callHeap A w c ∗
      argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      mainSaved s0 ∗
      localsCtx fsp 0
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
        0x1b8 24 [] ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      cliStaticsPlaced ∗ mainLitsBlk617Rest)
    ?_ (hnext := ?_)
  · dsimp only [readFileLitSpecPlaced]
    simp only [arm64_norm, hsp]
    rw [stackAt_sub_split fsp hsub_le hsub64]
    apply entails_pure_intro_left ⟨by decide +kernel, by decide +kernel, hcoinsOk⟩
    exact Entails.of_eq (by ac_rfl)
  · intro sf hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [readFileLitSpecPlaced]
    have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by rw [hcs_f.1]; simp only [arm64_norm, hx19]
    have hx20_f : sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag := by
      rw [hcs_f.2.1]; simp only [arm64_norm, hx20]
    have hx21_f : sf.readReg64 (.gpr 21#5) = w.w5 := by
      rw [hcs_f.2.2.1]; simp only [arm64_norm]
    have hx22_f : sf.readReg64 (.gpr 22#5) = w.w2 := by
      rw [hcs_f.2.2.2.1]; simp only [arm64_norm, hx22]
    have hx23_f : sf.readReg64 (.gpr 23#5) = inCap := by
      rw [hcs_f.2.2.2.2.1]; simp only [arm64_norm, hx23]
    have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length := by
      rw [hcs_f.2.2.2.2.2.1]; simp only [arm64_norm, hx24]
    have hx25_f : sf.readReg64 (.gpr 25#5) = w.w0 := by
      rw [hcs_f.2.2.2.2.2.2.1]; simp only [arm64_norm, hx25]
    have hx26_f : sf.readReg64 (.gpr 26#5) = w.w6 := by
      rw [hcs_f.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hx26]
    have hx27_f : sf.readReg64 (.gpr 27#5) = x27 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hx27]
    have hsp_sf : sf.sp = fsp := by rw [hsp_f]; simp only [arm64_norm, hsp]
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf, fsp, mainFrameSize]
      exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hst.spAligned
    have hfp_sf : sf.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hst.fp]
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.2]; simp only [calleeSavedVRegs, arm64_norm, hst.vregs]
    have hsp_pre : (_ : State).sp = fsp := hsp_f.symm.trans hsp_sf
    rw [hsp_pre]
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    refine SepWPp.exists_elim fun rCoins => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hfiles_f, hrd_rf, htr_sf⟩ => ?_
    have hfiles_sf : sf.fs.files = (initFsState (cliInputs i)).files :=
      hfiles_f.trans (by simp only [arm64_norm, hfiles])
    have hrd_rf' : rCoins = io.rd (initFsState (cliInputs i)).files (utf8 "coins") := by
      simpa only [arm64_norm, hfiles] using hrd_rf
    cases rCoins with
    | ok cBs =>
      have hc_eq : cBs = coinsOf i := by
        rcases hcoins _ hrd_rf'.symm with hok_c | ⟨herr_c, -⟩
        · exact Except.ok.inj hok_c
        · cases herr_c
      subst hc_eq
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (vecU8_to_ownedBytes A (fsp + 0x1b8#64) (coinsOf i))) ?_
      rw [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun coinsCap => ?_
      rw [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun coinsPtr => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            inInvOpt inOk A i c inCap inPtr x27 ∗
            (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ stackAt fsp hookStack ∗ A.pool ∗
            (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
              argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
              mainSaved s0 ∗
              localsCtx fsp 0
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                0x1b8 24 [] ∗
              memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                (stk - mainFrameSize - hookStack) ∗
              cliStaticsPlaced ∗ mainLitsBlk617Rest)) by ac_rfl)) ?_
      rw [ownedBytes_pure A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i),
        sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, _, hcoins_lt, _⟩ => ?_
      have hcoins_nzero := beq_add_one_zero_false_of_lt hcoins_lt
      cases inOk with
      | true =>
        dsimp only [inInvOpt, inInv]
        refine SepWPp.weaken_pre (Entails.of_eq (show _ =
          ⌜(inputOf i c).length ≤ stdinCapBytes⌝ ∗
            (⌜x27 = BitVec.ofNat 64 (inputOf i c).length⌝ ∗
              (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
                ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
                ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
                ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
                (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ stackAt fsp hookStack ∗ A.pool ∗
                (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
                  argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
                  mainSaved s0 ∗
                  localsCtx fsp 0
                    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                    0x1b8 24 [] ∗
                  memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                    (stk - mainFrameSize - hookStack) ∗
                  cliStaticsPlaced ∗ mainLitsBlk617Rest))) by ac_rfl)) ?_
        refine SepWPp.pure_elim fun hin_cap_le => ?_
        refine SepWPp.pure_elim fun hx27_len => ?_
        rw [ownedBytes_pure A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c),
          sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨_, _, hin_lt, _⟩ => ?_
        have hin_nzero := beq_add_one_zero_false_of_lt hin_lt
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x5dc#64) hinv_f
        wp_steps
        apply SepWP.done
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, *]); try rfl)
        intro hinv_5dc
        have hin_5dc : InMainPlaced CodeOk s0 _ 0x5dc := {
          inv := hinv_5dc
          pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
          run := by simp only [arm64_norm, *]
          sp := by (try simp only [arm64_norm]); exact hsp_sf
          fp := by (try simp only [arm64_norm]); exact hfp_sf
          vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
          spAligned := hst.spAligned
        }
        have hatM4 : AtM4Placed CodeOk i s0 _ w c i.argv.length buf coinsCap coinsPtr inCap := {
          base := hin_5dc
          x0 := by simp only [arm64_norm]
          x1 := by simp only [arm64_norm]
          x19 := by simp only [arm64_norm, hx19_f]
          x20 := by simp only [arm64_norm, hx20_f]
          x23 := by simp only [arm64_norm, hx23_f]
          x24 := by simp only [arm64_norm, hx24_f]
          x27 := by simp only [arm64_norm, hx27_f, hx27_len]
          w0 := by simp only [arm64_norm, hx25_f]
          w2 := by simp only [arm64_norm, hx22_f]
          w5 := by simp only [arm64_norm, hx21_f]
          w6 := by simp only [arm64_norm, hx26_f]
          fs := by simp only [arm64_norm, hfiles_sf]
          trace := by
            simp only [arm64_norm]
            exact htr_sf.trans ((by simp only [arm64_norm] : _ = st.trace).trans (hst_tr.trans hs_tr))
        }
        refine SepWPp.weaken_pre ?_ (hnext _ coinsCap coinsPtr inCap inPtr hin_cap_le hatM4)
        have hm4_merge :
            ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
              localsCtx fsp 0
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                0x1b8 24 [] ⊢
              locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) := by
          have h24 :
              ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ⊢
                memRegion (fsp + 0x1b8#64) 16 := by
            rw [memRegion_split (fsp + 0x1b8#64) 8 8 (by decide),
              show (fsp + 0x1b8#64) + 8#64 = fsp + 0x1c0#64 by rw [BitVec.add_assoc]; rfl]
            exact sepConj_mono
              (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
          have hctx_eq :
              memRegion (fsp + 0x1b8#64) 16 ∗
                ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
                localsCtx fsp 0
                  [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                  0x1b8 24 [] =
                locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) := by
            simp only [locals, localsFrom, localsCtx, Nat.reduceAdd, Nat.reduceSub]
            rw [ProofLib.memRegion_split' (b := fsp + 0x60#64) (b' := fsp + 0x1b8#64)
              (N := 0x168) (n := 0x158) (k := 16) (by decide) (by rw [BitVec.add_assoc]; rfl)
              (by decide)]
            ac_rfl
          rw [← hctx_eq, ← sepConj_assoc]
          exact sepConj_mono_left h24
        rw [stackAt_sub_split fsp hsub_le hsub64, mainLitsBlk617_eq]
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            localsCtx fsp 0
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
              0x1b8 24 []) ∗
          (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗
            (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
            A.pool ∗ cliStaticsPlaced ∗
            ((lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617Rest)) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hm4_merge) ?_
        exact Entails.of_eq (by ac_rfl)
      | false =>
        dsimp only [inInvOpt]
        refine SepWPp.weaken_pre (Entails.of_eq (show _ =
          ⌜inCap = 0xffffffffffffffff#64 ∧ 1 < c.tag ∧ stdinCapBytes < i.stdin.length⌝ ∗
            (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
              ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
              (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ stackAt fsp hookStack ∗ A.pool ∗
              (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
                argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
                mainSaved s0 ∗
                localsCtx fsp 0
                  [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                  0x1b8 24 [] ∗
                memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
                  (stk - mainFrameSize - hookStack) ∗
                cliStaticsPlaced ∗ mainLitsBlk617Rest)) by ac_rfl)) ?_
        refine SepWPp.pure_elim fun ⟨hin_neg1, htag_gt1, hstdin_gt⟩ => ?_
        subst hin_neg1
        apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x624#64) hinv_f
        wp_steps
        apply SepWP.done
          (by (try simp only [arm64_norm, *]); try rfl)
          (by (try simp only [arm64_norm, *]); try rfl)
        intro hinv_624
        have hin_624 : InMainPlaced CodeOk s0 _ 0x624 := {
          inv := hinv_624
          pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
          run := by simp only [arm64_norm, *]
          sp := by (try simp only [arm64_norm]); exact hsp_sf
          fp := by (try simp only [arm64_norm]); exact hfp_sf
          vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
          spAligned := hst.spAligned
        }
        have htr_sf_eq : sf.trace = s.trace :=
          htr_sf.trans (by simp only [arm64_norm, hst_tr])
        refine SepWPp.weaken_pre ?_
          (sepWPp_of_mainOom (step_err_0x624_placed
            (P := ¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length))
            (i := i) (s := s) (n := i.argv.length) (buf := buf)
            (coinsOk := true) (inOk := false)
            (coinsCap := coinsCap) (coinsPtr := coinsPtr)
            (inCap := 0xffffffffffffffff#64) (inPtr := inPtr)
            (c := c) (w := w) (ps := ps) hc hstk hstk64 hin_624
            (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl)
            (by (try simp only [arm64_norm, hx19_f]); try rfl)
            (by (try simp only [arm64_norm, hx20_f]); try rfl)
            (by (try simp only [arm64_norm, hx21_f]); try rfl)
            (by (try simp only [arm64_norm, hx22_f]); try rfl)
            (by (try simp only [arm64_norm, hx23_f]); try rfl)
            (by (try simp only [arm64_norm, hx24_f]); try rfl)
            (by (try simp only [arm64_norm, hx25_f]); try rfl)
            (by exact ⟨by simpa only [arm64_norm] using hfiles_sf, Or.inr ⟨htag_gt1, hstdin_gt⟩,
              by simpa only [arm64_norm] using htr_sf_eq⟩)
            hexit))
        have hloc_back :
            ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
              localsCtx fsp 0
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
                0x1b8 24 [] ⊢
              locals fsp
                [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] := by
          have h24 :
              ((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
                ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ⊢
                memRegion (fsp + 0x1b8#64) 24 := by
            rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
              memRegion_split (fsp + 0x1b8#64) 8 (8 + 8) (by decide),
              memRegion_split ((fsp + 0x1b8#64) + 8#64) 8 8 (by decide)]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            exact sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
          rw [hcarve_open]
          rw [← sepConj_assoc, ← sepConj_assoc]
          exact sepConj_mono_left (by simpa only [sepConj_assoc] using h24)
        have hcoins_opt :
            ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ⊢
              optOwnedBytes A true coinsCap coinsPtr :=
          ownedBytes_entails_optOwned _ _ _ _ _
        have hin_opt : emp ⊢ optOwnedBytes A false 0xffffffffffffffff#64 inPtr := by
          rw [optOwnedBytes_false, ← sepConj_emp ⌜_⌝]
          exact entails_pure_intro_left rfl (Entails.refl emp)
        rw [stackAt_sub_split fsp hsub_le hsub64]
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 0x1b8#64) ↦₆₄ coinsCap) ∗ ((fsp + 0x1c0#64) ↦₆₄ coinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            localsCtx fsp 0
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
              0x1b8 24 []) ∗
          ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          emp ∗
          (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗
            (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗ A.pool ∗
            ((lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗
              argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
              cliStaticsPlaced ∗ mainLitsBlk617Rest)) by simp; ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hloc_back
          (sepConj_mono hcoins_opt (sepConj_mono hin_opt
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (ProofLib.entails_anyHeap _))))))))) ?_
        exact Entails.of_eq (by ac_rfl)
    | error u =>
      cases u
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (sepConj_mono_right (memRegion_16_cells (fsp + 0x1b8#64)))) ?_
      simp only [sepExists_sepConj_right, sepExists_sepConj_left]
      refine SepWPp.exists_elim fun errCoinsPtr => ?_
      refine SepWPp.exists_elim fun errCoinsLen => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x624#64) hinv_f
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv_624
      have hin_624 : InMainPlaced CodeOk s0 _ 0x624 := {
        inv := hinv_624
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hsp_sf
        fp := by (try simp only [arm64_norm]); exact hfp_sf
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
        spAligned := hst.spAligned
      }
      have htr_sf_eq : sf.trace = s.trace :=
        htr_sf.trans (by simp only [arm64_norm, hst_tr])
      have hnr_coins : ¬ CoinsReadable i := by
        rcases hcoins _ hrd_rf'.symm with hok_c | ⟨-, hnr⟩
        · cases hok_c
        · exact hnr
      refine SepWPp.weaken_pre ?_
        (sepWPp_of_mainOom (step_err_0x624_placed
          (P := ¬ CoinsReadable i ∨ (1 < c.tag ∧ stdinCapBytes < i.stdin.length))
          (i := i) (s := s) (n := i.argv.length) (buf := buf)
          (coinsOk := false) (inOk := inOk)
          (coinsCap := 0xffffffffffffffff#64) (coinsPtr := errCoinsPtr)
          (inCap := inCap) (inPtr := inPtr)
          (c := c) (w := w) (ps := ps) hc hstk hstk64 hin_624
          (by (try simp only [arm64_norm]); try rfl) (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx19_f]); try rfl)
          (by (try simp only [arm64_norm, hx20_f]); try rfl)
          (by (try simp only [arm64_norm, hx21_f]); try rfl)
          (by (try simp only [arm64_norm, hx22_f]); try rfl)
          (by (try simp only [arm64_norm, hx23_f]); try rfl)
          (by (try simp only [arm64_norm, hx24_f]); try rfl)
          (by (try simp only [arm64_norm, hx25_f]); try rfl)
          (by exact ⟨by simpa only [arm64_norm] using hfiles_sf, Or.inl hnr_coins,
            by simpa only [arm64_norm] using htr_sf_eq⟩)
          hexit))
      have hloc_back :
          ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 0x1c0#64) ↦₆₄ errCoinsPtr) ∗
            ((fsp + 0x1c8#64) ↦₆₄ errCoinsLen) ∗
            localsCtx fsp 0
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
              0x1b8 24 [] ⊢
            locals fsp
              [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1] := by
        have h24 :
            ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 0x1c0#64) ↦₆₄ errCoinsPtr) ∗
              ((fsp + 0x1c8#64) ↦₆₄ errCoinsLen) ⊢
              memRegion (fsp + 0x1b8#64) 24 := by
          rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
            memRegion_split (fsp + 0x1b8#64) 8 (8 + 8) (by decide),
            memRegion_split ((fsp + 0x1b8#64) + 8#64) 8 8 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
        rw [hcarve_open]
        rw [← sepConj_assoc, ← sepConj_assoc]
        exact sepConj_mono_left (by simpa only [sepConj_assoc] using h24)
      have hin_opt : inInvOpt inOk A i c inCap inPtr x27 ⊢ optOwnedBytes A inOk inCap inPtr := by
        cases inOk with
        | false =>
          dsimp only [inInvOpt]
          rw [optOwnedBytes_false, ← sepConj_emp ⌜_ ∧ _⌝]
          exact entails_pure_elim_left fun h => by
            rw [← sepConj_emp ⌜_⌝]
            exact entails_pure_intro_left h.1 (Entails.refl emp)
        | true =>
          dsimp only [inInvOpt, inInv]
          exact entails_pure_elim_left fun _ =>
            entails_pure_elim_left fun _ => ownedBytes_entails_optOwned _ _ _ _ _
      have hcoins_opt : emp ⊢ optOwnedBytes A false 0xffffffffffffffff#64 errCoinsPtr := by
        rw [optOwnedBytes_false, ← sepConj_emp ⌜_⌝]
        exact entails_pure_intro_left rfl (Entails.refl emp)
      rw [stackAt_sub_split fsp hsub_le hsub64]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((fsp + 0x1c0#64) ↦₆₄ errCoinsPtr) ∗
          ((fsp + 0x1c8#64) ↦₆₄ errCoinsLen) ∗
          localsCtx fsp 0
            [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr, cell fsp 0x58 w.w1]
            0x1b8 24 []) ∗
        emp ∗
        inInvOpt inOk A i c inCap inPtr x27 ∗
        (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗ A.pool ∗
          ((lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            cliStaticsPlaced ∗ mainLitsBlk617Rest)) by simp; ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hloc_back
        (sepConj_mono hcoins_opt (sepConj_mono hin_opt
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (ProofLib.entails_anyHeap _))))))))) ?_
      exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Continuation at `M+0x59c .. M+0x5ac` (`read_stdin(&fsp+0x60)` when `1 < c.tag`, spilling `inPtr`
to `[sp+0x50]`) → `step_from_0x5b0_placed`. -/
theorem step_stdin_0x59c_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {io : IoModel}
    {i : Inputs} {c : CallV} {w : CallW} {s0 s st : State} {ret : BitVec 64} {stk hookStack resStack : Nat}
    {buf p0 : BitVec 64} {ps : List (BitVec 64 × List (BitVec 8))}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hio : MainIoPlaced A H io hookStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0fs : s0.fs = initFsState (cliInputs i))
    (hstdin : io.stdin (initFsState (cliInputs i)) = some i.stdin)
    (hcoinsOk : io.pathOk (utf8 "coins"))
    (hcoins : ∀ r, io.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i))
    (htag_gt1 : 1 < c.tag)
    (hs_tr : s.trace = s0.trace)
    (hst : InMainPlaced CodeOk s0 st 0x59c)
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
  have hstdin_ok := main_readStdin_placed_ok hio
  have hsub_le : hookStack ≤ stk - mainFrameSize := by omega
  have hsub64 : stk - mainFrameSize ≤ 2 ^ 64 := by omega
  have hcarve50 := locals_carve_cell fsp
    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 [cell fsp 0x58 w.w1]
  rw [show callCellsPlaced fsp w =
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] ++ [cell fsp 0x58 w.w1] by rfl,
    hcarve50]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun old50 => ?_
  have hcarve60 := locals_carve_region fsp
    [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1]
    0x60 24 []
  rw [List.append_nil] at hcarve60
  rw [show [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] ++
        cell fsp 0x50 old50 :: [cell fsp 0x58 w.w1] =
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1] by rfl,
    hcarve60,
    locals_focus fsp
      [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1]
      0x60 24 (memRegion (fsp + 0x60#64) 24) []]
  have hal : st.spAligned = true := hst.spAligned_state
  have hsp : st.sp = fsp := hst.sp
  have hpc := hst.pc; have hrun := hst.run; have hinv := hst.inv
  rw [mPcPlaced_eq] at hpc
  rw [mProgPlaced_eq]
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := lsρ lsReadStdinSym) hinv
  wp_steps
  apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
    (by (try simp only [arm64_norm, *]); try rfl)
  intro hinv1
  refine main_call_rocl (CodeOk := CodeOk)
    (spec := readStdinSpecPlaced io A hookStack)
    ({ ret := fsp + 0x60#64, bs := i.stdin } : ReadStdinGhost)
    hstdin_ok
    hinv1 (by (try simp only [arm64_norm, *]); try rfl) (by (try simp only [arm64_norm, *]); try rfl)
    (by simp only [arm64_norm]; exact hal)
    (ret_pc := (blkPl_617).base + 0x5a4#64) (by (try simp only [arm64_norm, *]); try rfl)
    (hpanic := fun sf_p R' _ hp => by
      try dsimp only [readStdinSpecPlaced] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      apply hpanic
      have h1 := hp.1.1
      refine allocFailedIn_mono_left ?_ h1
      simp only [arm64_norm]
      rw [hst_tr, hs_tr])
    (F := callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      mainSaved s0 ∗
      localsCtx fsp 0
        [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1]
        0x60 24 [] ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - hookStack) ∗
      cliStaticsPlaced ∗ mainLitsBlk617)
    ?_ (hnext := ?_)
  · dsimp only [readStdinSpecPlaced]
    simp only [arm64_norm, hst_fs, hs0fs, hsp]
    rw [stackAt_sub_split fsp hsub_le hsub64]
    apply entails_pure_intro_left hstdin
    exact Entails.of_eq (by ac_rfl)
  · intro sf hinv_f hpc_f hrun_f hsp_f hcs_f
    dsimp only [readStdinSpecPlaced]
    have hx19_f : sf.readReg64 (.gpr 19#5) = buf := by rw [hcs_f.1]; simp only [arm64_norm, hx19]
    have hx20_f : sf.readReg64 (.gpr 20#5) = BitVec.ofNat 64 c.tag := by
      rw [hcs_f.2.1]; simp only [arm64_norm, hx20]
    have hw5_f : (sf.readReg64 (.gpr 28#5) ||| sf.readReg64 (.gpr 21#5)) = w.w5 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.1, hcs_f.2.2.1]; simp only [arm64_norm, hw5_orr]
    have hx22_f : sf.readReg64 (.gpr 22#5) = w.w2 := by
      rw [hcs_f.2.2.2.1]; simp only [arm64_norm, hx22]
    have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length := by
      rw [hcs_f.2.2.2.2.2.1]; simp only [arm64_norm, hx24]
    have hx25_f : sf.readReg64 (.gpr 25#5) = w.w0 := by
      rw [hcs_f.2.2.2.2.2.2.1]; simp only [arm64_norm, hx25]
    have hx26_f : sf.readReg64 (.gpr 26#5) = w.w6 := by
      rw [hcs_f.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hx26]
    have hsp_sf : sf.sp = fsp := by rw [hsp_f]; simp only [arm64_norm, hsp]
    have hal_sf : sf.spAligned = true := by
      simp only [State.spAligned, hsp_sf, fsp, mainFrameSize]
      exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hst.spAligned
    have hfp_sf : sf.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, hst.fp]
    have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
      rw [hcs_f.2.2.2.2.2.2.2.2.2.2.2]; simp only [calleeSavedVRegs, arm64_norm, hst.vregs]
    have hsp_pre : (_ : State).sp = fsp := hsp_f.symm.trans hsp_sf
    rw [hsp_pre]
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    refine SepWPp.exists_elim fun rIn => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hfiles_f, hok_in, htr_sf⟩ => ?_
    subst hok_in
    have hfiles_sf : sf.fs.files = (initFsState (cliInputs i)).files :=
      hfiles_f.trans (by simp only [arm64_norm, hst_fs, hs0fs])
    have htr_sf_eq : sf.trace = s.trace :=
      htr_sf.trans (by simp only [arm64_norm, hst_tr])
    have hin_of_eq : inputOf i c = i.stdin := by simp only [inputOf, htag_gt1, ↓reduceIte]
    have hctx_open :
        localsCtx fsp 0
          [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 old50, cell fsp 0x58 w.w1]
          0x60 24 [] =
        ((fsp + 0x50#64) ↦₆₄ old50) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)] := by
      simp only [localsCtx, localsFrom, emp_sepConj]
      ac_rfl
    have hloc_merge : ∀ (inPtr' c60 c70 : BitVec 64),
        ((fsp + 0x50#64) ↦₆₄ inPtr') ∗ ((fsp + 0x60#64) ↦₆₄ c60) ∗
          ((fsp + 0x68#64) ↦₆₄ inPtr') ∗ ((fsp + 0x70#64) ↦₆₄ c70) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)] ⊢
        locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr', cell fsp 0x58 w.w1] := by
      intro inPtr' c60 c70
      have h24 :
          ((fsp + 0x60#64) ↦₆₄ c60) ∗ ((fsp + 0x68#64) ↦₆₄ inPtr') ∗
            ((fsp + 0x70#64) ↦₆₄ c70) ⊢
            memRegion (fsp + 0x60#64) 24 := by
        rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
          memRegion_split (fsp + 0x60#64) 8 (8 + 8) (by decide),
          memRegion_split ((fsp + 0x60#64) + 8#64) 8 8 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
      have hctx2 :
          ((fsp + 0x50#64) ↦₆₄ inPtr') ∗ memRegion (fsp + 0x60#64) 24 ∗
            localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
              [cell fsp 0x58 w.w1, (0x60, 24, emp)] =
          locals fsp [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr', cell fsp 0x58 w.w1] := by
        have hc2 := locals_carve_region fsp
          [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4, cell fsp 0x50 inPtr', cell fsp 0x58 w.w1]
          0x60 24 []
        rw [List.append_nil] at hc2
        rw [hc2]
        simp only [locals, localsFrom, localsCtx, cell, List.cons_append, List.nil_append, emp_sepConj]
        ac_rfl
      rw [← hctx2]
      exact sepConj_mono_right (by
        rw [← sepConj_assoc, ← sepConj_assoc]
        exact sepConj_mono_left (by simpa only [sepConj_assoc] using h24))
    by_cases hcap_in : i.stdin.length ≤ stdinCapBytes
    · have hr_in : readStdinResult i.stdin = .ok i.stdin := by
        simp only [readStdinResult, hcap_in, ↓reduceIte]
      rw [hr_in]
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (vecU8_to_ownedBytes A (fsp + 0x60#64) i.stdin)) ?_
      simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd]
      refine SepWPp.exists_elim fun inCap => ?_
      refine SepWPp.exists_elim fun inPtr => ?_
      rw [hctx_open]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x5b0#64) hinv_f
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv_5b0
      have hin_5b0 : InMainPlaced CodeOk s0 _ 0x5b0 := {
        inv := hinv_5b0
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hsp_sf
        fp := by (try simp only [arm64_norm]); exact hfp_sf
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
        spAligned := hst.spAligned
      }
      refine SepWPp.weaken_pre ?_
        (step_from_0x5b0_placed (inOk := true) (buf := buf) (inCap := inCap) (inPtr := inPtr)
          (x27 := BitVec.ofNat 64 i.stdin.length)
          (c := c) (w := w) (p0 := p0) (ps := ps) hc hio hstk hstk64 hcoinsOk hcoins hs_tr hin_5b0
          (by (try simp only [arm64_norm, hx19_f]); try rfl)
          (by (try simp only [arm64_norm, hx20_f]); try rfl)
          (by (try simp only [arm64_norm, hx22_f]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx24_f]); try rfl)
          (by (try simp only [arm64_norm, hx25_f]); try rfl)
          (by (try simp only [arm64_norm, hx26_f]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hw5_f]); try rfl)
          (by (try simp only [arm64_norm, hfiles_sf]); try rfl)
          (by simpa only [arm64_norm] using htr_sf_eq)
          hpanic hexit hnext)
      have hin_inv :
          ownedBytes A inCap inPtr (BitVec.ofNat 64 i.stdin.length) i.stdin ⊢
            inInvOpt true A i c inCap inPtr (BitVec.ofNat 64 i.stdin.length) := by
        dsimp only [inInvOpt, inInv]
        rw [hin_of_eq]
        exact entails_pure_intro_left hcap_in (entails_pure_intro_left rfl (Entails.refl _))
      rw [stackAt_sub_split fsp hsub_le hsub64]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 0x50#64) ↦₆₄ inPtr) ∗ ((fsp + 0x60#64) ↦₆₄ inCap) ∗
          ((fsp + 0x68#64) ↦₆₄ inPtr) ∗ ((fsp + 0x70#64) ↦₆₄ BitVec.ofNat 64 i.stdin.length) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)]) ∗
        (ownedBytes A inCap inPtr (BitVec.ofNat 64 i.stdin.length) i.stdin ∗
          callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono (hloc_merge inPtr inCap (BitVec.ofNat 64 i.stdin.length))
        (sepConj_mono_left hin_inv)) ?_
      exact Entails.of_eq (by ac_rfl)
    · have hr_in : readStdinResult i.stdin = .error () := by
        simp only [readStdinResult, hcap_in, ↓reduceIte]
      rw [hr_in]
      dsimp only [ioVecAt]
      refine SepWPp.weaken_pre
        (sepConj_mono_left (sepConj_mono_right (memRegion_16_cells (fsp + 0x60#64)))) ?_
      simp only [sepExists_sepConj_right, sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd]
      refine SepWPp.exists_elim fun errInPtr => ?_
      refine SepWPp.exists_elim fun errInLen => ?_
      rw [hctx_open]
      apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 0x5b0#64) hinv_f
      wp_steps
      apply SepWP.done (by (try simp only [arm64_norm, *]); try rfl)
        (by (try simp only [arm64_norm, *]); try rfl)
      intro hinv_5b0
      have hin_5b0 : InMainPlaced CodeOk s0 _ 0x5b0 := {
        inv := hinv_5b0
        pc := by rw [mPcPlaced_eq]; (try simp only [arm64_norm, *]); try rfl
        run := by simp only [arm64_norm, *]
        sp := by (try simp only [arm64_norm]); exact hsp_sf
        fp := by (try simp only [arm64_norm]); exact hfp_sf
        vregs := by (try simp only [calleeSavedVRegs, arm64_norm]); exact hvregs_sf
        spAligned := hst.spAligned
      }
      refine SepWPp.weaken_pre ?_
        (step_from_0x5b0_placed (inOk := false) (buf := buf) (inCap := 0xffffffffffffffff#64)
          (inPtr := errInPtr) (x27 := errInLen)
          (c := c) (w := w) (p0 := p0) (ps := ps) hc hio hstk hstk64 hcoinsOk hcoins hs_tr hin_5b0
          (by (try simp only [arm64_norm, hx19_f]); try rfl)
          (by (try simp only [arm64_norm, hx20_f]); try rfl)
          (by (try simp only [arm64_norm, hx22_f]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hx24_f]); try rfl)
          (by (try simp only [arm64_norm, hx25_f]); try rfl)
          (by (try simp only [arm64_norm, hx26_f]); try rfl)
          (by (try simp only [arm64_norm]); try rfl)
          (by (try simp only [arm64_norm, hw5_f]); try rfl)
          (by (try simp only [arm64_norm, hfiles_sf]); try rfl)
          (by simpa only [arm64_norm] using htr_sf_eq)
          hpanic hexit hnext)
      have hin_inv : emp ⊢ inInvOpt false A i c 0xffffffffffffffff#64 errInPtr errInLen := by
        dsimp only [inInvOpt]
        rw [← sepConj_emp ⌜_⌝]
        exact entails_pure_intro_left ⟨rfl, htag_gt1, Nat.lt_of_not_ge hcap_in⟩ (Entails.refl emp)
      rw [stackAt_sub_split fsp hsub_le hsub64]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 0x50#64) ↦₆₄ errInPtr) ∗ ((fsp + 0x60#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((fsp + 0x68#64) ↦₆₄ errInPtr) ∗ ((fsp + 0x70#64) ↦₆₄ errInLen) ∗
          localsCtx fsp 0 [cell fsp 0x40 w.w3, cell fsp 0x48 w.w4] 0x50 8
            [cell fsp 0x58 w.w1, (0x60, 24, emp)]) ∗
        (emp ∗
          callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - hookStack) ∗ stackAt fsp hookStack) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617) by simp only [emp_sepConj]; ac_rfl)) ?_
      refine Entails.trans (sepConj_mono (hloc_merge errInPtr 0xffffffffffffffff#64 errInLen)
        (sepConj_mono_left hin_inv)) ?_
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.MainHops.M3Helpers
