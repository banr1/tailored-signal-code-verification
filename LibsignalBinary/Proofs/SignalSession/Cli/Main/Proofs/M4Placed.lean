/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4StepsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4ErrPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3ErrTailPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Relocatable `main` Hop M4 (`M+0x5dc → M+0x7b0 / M+0xb24 / M+0x650`, Block `617`)

Verifies `main`'s fourth hop on Block `617` under `[LibsignalPlacement]`: `coins::install`, the
1 MiB `send` payload cap (`exit 1` via `M+0x650`), `Stores::open()` and `Call` setup, the call to
`signal_session::run` (Block `579`), and post-`run` `Ok` / `Err` dispatch.
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
open CryptoVerification.SignalSession.Cli.MainHops.M4Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] ProofLib.bv_sub_add_lit
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem m4_sepWPp_exists_left_p {α : Sort _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ x : α, SepWPp prog ret s (P x) Q Qp oom) :
    SepWPp prog ret s (∃∗ x, P x) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x R hx hL

private theorem m4_allocFailedIn_of_start_trace_eq_p {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf) : allocFailedIn s0 sf := by
  unfold allocFailedIn at h ⊢
  rwa [htr] at h

private theorem m4_histOkTight_of_eq_p {i : Inputs} {sf sf' : State}
    (htr : sf'.trace = sf.trace) (hfs : sf'.fs = sf.fs) (h : HistOkTight i sf) :
    HistOkTight i sf' :=
  ⟨by rw [hfs]; exact h.1, by rw [htr]; exact h.2⟩

/-! ## 1. `M+0x5dc → M+0x650`: `IsSendOverCap` Clean Exit (`code = 1`) -/

set_option maxHeartbeats 800000 in
/-- On `c = .send peer` with `1_000_000 < i.stdin.length`, `M+0x5dc .. M+0x61c` installs `coins`,
detects `x27 > 0xf4240`, sets `w26 = 1`, and jumps to `M+0x650` to drop `input`, `Call`, and `args`
before exiting with code `1`. -/
theorem main_m4_sendOverCap_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser}
    {i : Inputs} {peer : AddrV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat}
    {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some (.send peer))
    (hover : 1_000_000 < i.stdin.length)
    (hs : AtM4Placed CodeOk i s0 s w (.send peer) i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ s'.fs.files = (initFsState (cliInputs i)).files ∧
        s'.trace = s.trace) Q Qp) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
          (inputOf i (.send peer)) ∗
        callHeap A w (.send peer) ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) := by
  let _ := hsp; let _ := hs0tr; let _ := hparse; let _ := hpanic
  set fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hin_eq : inputOf i (.send peer) = i.stdin := rfl
  refine sepWPp_weaken_pre (Entails.of_eq (show _ =
    ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
      (inputOf i (.send peer)) ∗
    callHeap A w (.send peer) ∗
    (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
      argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      mainSaved s0 ∗
      locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) ∗
      stackAt fsp (stk - mainFrameSize) ∗
      A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617) by ac_rfl)) ?_
  rw [M3Helpers.ownedBytes_pure A inCap inPtr
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
      callHeap A w (.send peer) =
        (⌜w.w0 = 0x8000000000000002#64⌝ ∗ callHeap A w (.send peer)) := by
    dsimp only [callHeap]
    apply ProofLib.sepProp_ext
    · exact M3Helpers.entails_pure_elim_left fun hp =>
        M3Helpers.entails_pure_intro_left hp (M3Helpers.entails_pure_intro_left hp (Entails.refl _))
    · exact M3Helpers.entails_pure_elim_left fun _ => Entails.refl _
  refine sepWPp_weaken_pre (Entails.of_eq (show _ =
    callHeap A w (.send peer) ∗
    (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
        (inputOf i (.send peer)) ∗
      ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
      argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      mainSaved s0 ∗
      locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) ∗
      stackAt fsp (stk - mainFrameSize) ∗
      A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617) by ac_rfl)) ?_
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
    ac_rfl
  dsimp only [cliStaticsPlaced, coinsStaticsPlaced, Coins.coinsNextPlaced, Coins.coinsLeftPlaced,
    Coins.coinsNextSym, Coins.coinsLeftSym]
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
  apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1616#64) hs.base.inv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
  intro hinv_650
  have hin_650 : InMainPlaced CodeOk s0 _ 0x650 :=
    InMainPlaced.mk_step hs.base
      (by simp only [mPcPlaced_eq, arm64_norm, *])
      (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      hinv_650
      (by simp only [calleeSavedVRegs, arm64_norm])
  refine sepWPp_weaken_pre ?_
    (M3Helpers.step_dealloc_in_0x650_placed (n := i.argv.length) (code := 1) (c := .send peer)
      (w := w) (buf := buf) (inCap := inCap) (inPtr := inPtr)
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
  refine Entails.trans (Entails.of_eq (show _ =
    ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i (.send peer)).length)
      (inputOf i (.send peer)) ∗
    callHeap A w (.send peer) ∗
    argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
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
    A.pool ∗
    (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      (lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ coinsPtr) ∗
      (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      FromRecordCallees.lsLogOff ∗
      mainLitsBlk617) by ac_rfl)) ?_
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono hloc_back
            (sepConj_mono_right
              (sepConj_mono_right (ProofLib.entails_anyHeap _)))))))

/-! ## 2. `M+0x5dc → M+0x678`: `coins::install` + `¬ IsSendOverCap` Guard -/

set_option maxHeartbeats 800000 in
private theorem m4_entry_to_setup_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc}
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
      SepWPp (mProgPlaced H) ret s_setup
        ((Coins.coinsNextPlaced ↦₆₄ coinsPtr) ∗
          (Coins.coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
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
  dsimp only [coinsStaticsPlaced, Coins.coinsNextPlaced, Coins.coinsLeftPlaced,
    Coins.coinsNextSym, Coins.coinsLeftSym]
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
      · exact M3Helpers.entails_pure_elim_left fun hp =>
          M3Helpers.entails_pure_intro_left hp.1 (M3Helpers.entails_pure_intro_left hp (Entails.refl _))
      · exact M3Helpers.entails_pure_elim_left fun _ => Entails.refl _
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      callHeap A w (.keygen me k) ∗
      ((lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ vNext) ∗
        (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ vLeft) ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗ F) by ac_rfl)) ?_
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1656#64) hs.base.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_s
    refine sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
      (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]))
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
        exact M3Helpers.entails_pure_elim_left fun hp =>
          M3Helpers.entails_pure_intro_left hp.2.2.1 (M3Helpers.entails_pure_intro_left hp (Entails.refl _))
      · exact M3Helpers.entails_pure_elim_left fun _ => Entails.refl _
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      callHeap A w (.init peer bundle) ∗
      ((lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ vNext) ∗
        (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ vLeft) ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗ F) by ac_rfl)) ?_
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
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1656#64) hs.base.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_s
    refine sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
      (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]))
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
      · exact M3Helpers.entails_pure_elim_left fun hp =>
          M3Helpers.entails_pure_intro_left hp (M3Helpers.entails_pure_intro_left hp (Entails.refl _))
      · exact M3Helpers.entails_pure_elim_left fun _ => Entails.refl _
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      callHeap A w (.send peer) ∗
      ((lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ vNext) ∗
        (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ vLeft) ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗ F) by ac_rfl)) ?_
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1656#64) hs.base.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_s
    refine sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
      (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]))
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
      · exact M3Helpers.entails_pure_elim_left fun hp =>
          M3Helpers.entails_pure_intro_left hp (M3Helpers.entails_pure_intro_left hp (Entails.refl _))
      · exact M3Helpers.entails_pure_elim_left fun _ => Entails.refl _
    refine sepWPp_weaken_pre (Entails.of_eq (show _ =
      callHeap A w (.recv peer) ∗
      ((lsρ "libsignal_cli::coins::NEXT.0" ↦₆₄ vNext) ∗
        (lsρ "libsignal_cli::coins::LEFT.0" ↦₆₄ vLeft) ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗ F) by ac_rfl)) ?_
    rw [hch_pure, sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_eq => ?_
    rw [mProgPlaced_eq]
    apply sepWPp_seq_codeOk (CodeOk := CodeOk) (mid := (blkPl_617).base + 1656#64) hs.base.inv
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hrun])
    intro hinv_s
    refine sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
      (hk _ ?_ (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]))
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

/-! ## 3. `M+0x5dc → signal_session::run` (`lsmpl.base 579`) Packaging -/

set_option maxHeartbeats 1200000 in
theorem m4_to_run_call_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State} {ret : BitVec 64}
    {stk hookStack resStack : Nat} {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
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
          ownedBytesRest A inCap inPtr (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
          anyHeap
      AtM4RunCallPlaced CodeOk s0 s3 i.argv.length buf inCap inPtr (inputOf i c).length →
      s3.sp = fsp → s3.trace = s.trace → s3.trace = s0.trace → s3.fs = s.fs →
      SepWPp (mProgPlaced H) ret s3
        ((runSpecPlaced CodeOk A uuidParse Run wrOk resStack).pre g_run s3 ∗ frameRun)
        Q Qp oom) :
    SepWPp (mProgPlaced H) ret s
      (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  have hsp0 : s.sp = fsp := hs.base.sp
  have hres_le : resStack ≤ stk - mainFrameSize := by omega
  have hstk_split := stackAt_split_ge fsp hres_le (by omega)
  refine sepWPp_weaken_pre (Entails.of_eq (show _ =
    ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
    (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
      callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
      argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
      mainSaved s0 ∗
      locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) ∗
      stackAt fsp (stk - mainFrameSize) ∗
      A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617) by ac_rfl)) ?_
  rw [M3Helpers.ownedBytes_pure A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c),
    sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, hin_le, hinCap_lt, _⟩ => ?_
  have hin_lt63 : (inputOf i c).length < 2 ^ 63 := Nat.lt_of_le_of_lt hin_le hinCap_lt
  let restKeep : SepProp :=
    (coinsPtr ↦ₛ coinsOf i) ∗
    (inPtr ↦ₛ inputOf i c) ∗
    ownedBytesRest A inCap inPtr (inputOf i c) ∗
    argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
    mainSaved s0 ∗
    m4Gaps fsp ∗
    memRegion (fsp + 0x1b8#64) 0x10 ∗
    memRegion (fsp + 0x1d0#64) 0x140 ∗
    memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
    stackAt fsp resStack ∗
    A.pool ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    FromRecordCallees.lsLogOff ∗
    mainLitsBlk617 ∗
    ownedBytesRest A coinsCap coinsPtr (coinsOf i) ∗
    argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps)
  have hpre_entry :
      ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
          callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗
          locals fsp (m4CellsPlaced fsp w inPtr (coinsOf i).length) ∗
          stackAt fsp (stk - mainFrameSize) ∗
          A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617) ⊢
      coinsStaticsPlaced ∗
        ((s.sp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        callHeap A w c ∗
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
      (sepConj_mono (ownedBytes_split A inCap inPtr (inputOf i c))
        (sepConj_mono (ownedBytes_split A coinsCap coinsPtr (coinsOf i))
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono hloc
                    (sepConj_mono (Entails.of_eq hstk_split) (Entails.refl _))))))))) ?_
    rw [hsp0]
    dsimp only [cliStaticsPlaced, restKeep]
    exact Entails.of_eq (by ac_rfl)
  refine sepWPp_weaken_pre hpre_entry ?_
  clear hpre_entry
  refine m4_entry_to_setup_placed hs hnot_over hin_lt63
    fun s_setup hs_setup hsp_setup htr_setup hfs_setup => ?_
  have hsp_s0 : s_setup.sp = fsp := hsp_setup.trans hsp0
  refine sepWPp_weaken_pre
    (P' := ((s_setup.sp + 0x40#64) ↦₆₄ w.w3) ∗
      ((s_setup.sp + 0x48#64) ↦₆₄ w.w4) ∗
      ((s_setup.sp + 0x50#64) ↦₆₄ inPtr) ∗
      ((s_setup.sp + 0x58#64) ↦₆₄ w.w1) ∗
      m4UninitP1 s_setup.sp ∗
      (m4UninitP2 fsp ∗ m4UninitP3 fsp ∗
        (Coins.coinsNextPlaced ↦₆₄ coinsPtr) ∗
        (Coins.coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        callHeap A w c ∗ restKeep))
    (by rw [hsp0, hsp_s0]; exact Entails.of_eq (by ac_rfl)) ?_
  refine m4_step_part1_placed hs_setup fun s1 hs1 htr1 hfs1 => ?_
  have hsp1 : s1.sp = fsp := hs1.base.sp
  refine sepWPp_weaken_pre
    (P' := m4UninitP2 s1.sp ∗
      (m4UninitP3 fsp ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
        ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
        m4WrittenP1Placed fsp w ∗
        (Coins.coinsNextPlaced ↦₆₄ coinsPtr) ∗
        (Coins.coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        callHeap A w c ∗ restKeep))
    (by rw [hsp_s0, hsp1]; exact Entails.of_eq (by ac_rfl)) ?_
  refine m4_step_part2_placed hs1 fun s2 hs2 htr2 hfs2 => ?_
  have hsp2 : s2.sp = fsp := hs2.base.sp
  refine sepWPp_weaken_pre
    (P' := m4UninitP3 s2.sp ∗
      (m4WrittenP2Placed fsp w ∗
        ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
        ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
        m4WrittenP1Placed fsp w ∗
        (Coins.coinsNextPlaced ↦₆₄ coinsPtr) ∗
        (Coins.coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
        callHeap A w c ∗ restKeep))
    (by rw [hsp1, hsp2]; exact Entails.of_eq (by ac_rfl)) ?_
  refine m4_step_part3_placed hs2 fun s3 hs3 _ htr3 hfs3 => ?_
  have hsp3 : s3.sp = fsp := hs3.sp
  have htr3_s : s3.trace = s.trace := htr3.trans (htr2.trans (htr1.trans htr_setup))
  have htr3_0 : s3.trace = s0.trace := htr3_s.trans hs.trace
  have hfs3_s : s3.fs = s.fs := hfs3.trans (hfs2.trans (hfs1.trans hfs_setup))
  let g_run : RunCall :=
    { i := i, c := c, a := a, res := fsp + 0x1b8#64, call := fsp + 0x78#64,
      stores := fsp + 0x310#64, inp := inPtr, coins := coinsPtr }
  let frameRun : SepProp :=
    m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ownedBytesRest A inCap inPtr (inputOf i c) ∗
      argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
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
        resStack ≤ s3.sp.toNat := by
    dsimp only [g_run]
    refine ⟨hs3.inv, hRun, hparse, ?_, ?_, ?_, hs3.x3, hs3.x4, ?_, ?_, ?_⟩
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
  have hpre_run :
      m4WrittenP3Placed s2.sp ∗
        (m4WrittenP2Placed fsp w ∗
          ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
          ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
          m4WrittenP1Placed fsp w ∗
          (Coins.coinsNextPlaced ↦₆₄ coinsPtr) ∗
          (Coins.coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
          ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
          callHeap A w c ∗ restKeep) ⊢
      (runSpecPlaced CodeOk A uuidParse Run wrOk resStack).pre g_run s3 ∗ frameRun := by
    rw [hsp2]
    let leakBundle : SepProp :=
      (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617 ∗
        ownedBytesRest A coinsCap coinsPtr (coinsOf i) ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps)
    have hrearr1 :
        m4WrittenP3Placed fsp ∗
          (m4WrittenP2Placed fsp w ∗
            ((fsp + 0x40#64) ↦₆₄ w.w3) ∗
            ((fsp + 0x48#64) ↦₆₄ w.w4) ∗
            ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            ((fsp + 0x58#64) ↦₆₄ w.w1) ∗
            m4WrittenP1Placed fsp w ∗
            (Coins.coinsNextPlaced ↦₆₄ coinsPtr) ∗
            (Coins.coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            ((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
            callHeap A w c ∗ restKeep) =
        (((fsp + 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (coinsOf i).length) ∗
          memRegion (fsp + 0x1b8#64) 0x10 ∗
          memRegion (fsp + 0x1d0#64) 0x140) ∗
        ((m4WrittenP1Placed fsp w ∗ m4WrittenP2Placed fsp w ∗ m4WrittenP3Placed fsp) ∗
          callHeap A w c ∗ mainLitsBlk617) ∗
        coinsInstalledPlaced coinsPtr (coinsOf i) ∗
        m4RestFramePlaced fsp w ∗
        (inPtr ↦ₛ inputOf i c) ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        FromRecordCallees.lsLogOff ∗
        A.pool ∗
        stackAt fsp resStack ∗
        ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        ownedBytesRest A inCap inPtr (inputOf i c) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
        (ownedBytesRest A coinsCap coinsPtr (coinsOf i) ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps)) := by
      dsimp only [restKeep, coinsInstalledPlaced, m4RestFramePlaced]
      ac_rfl
    have hpack_mid :
        (m4WrittenP1Placed fsp w ∗ m4WrittenP2Placed fsp w ∗ m4WrittenP3Placed fsp) ∗
          callHeap A w c ∗ mainLitsBlk617 ⊢
        callAt A (fsp + 0x78#64) c ∗
          storesAt A (fsp + 0x310#64) StoresGhost.opened ∗
          (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617 := by
      rw [m4_writtenPlaced_pack fsp w]
      have hmid_eq :
          (m4CallWords fsp w ∗ m4OpenStoresWordsPlaced fsp) ∗ callHeap A w c ∗ mainLitsBlk617 =
            (m4CallWords fsp w ∗ callHeap A w c) ∗
              (m4OpenStoresWordsPlaced fsp ∗ mainLitsBlk617) := by
        ac_rfl
      rw [hmid_eq]
      exact sepConj_mono (m4CallWords_pack A fsp w c) (m4OpenStoresPlaced_pack A fsp)
    rw [hrearr1]
    refine Entails.trans
      (sepConj_mono (m4_resSlot_merge fsp (BitVec.ofNat 64 (coinsOf i).length))
        (sepConj_mono hpack_mid (Entails.refl _))) ?_
    have hrearr2 :
        memRegion (fsp + 0x1b8#64) runResSize ∗
          (callAt A (fsp + 0x78#64) c ∗
            storesAt A (fsp + 0x310#64) StoresGhost.opened ∗
            (lsρ coinsLitSym ↦ᵣ utf8 "coins") ∗ mainLitsBlk617) ∗
          coinsInstalledPlaced coinsPtr (coinsOf i) ∗
          m4RestFramePlaced fsp w ∗
          (inPtr ↦ₛ inputOf i c) ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          FromRecordCallees.lsLogOff ∗
          A.pool ∗
          stackAt fsp resStack ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ownedBytesRest A inCap inPtr (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - resStack) ∗
          (ownedBytesRest A coinsCap coinsPtr (coinsOf i) ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps)) =
        (memRegion (fsp + 0x1b8#64) runResSize ∗
          callAt A (fsp + 0x78#64) c ∗
          storesAt A (fsp + 0x310#64) StoresGhost.opened ∗
          (inPtr ↦ₛ inputOf i c) ∗
          coinsInstalledPlaced coinsPtr (coinsOf i) ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          FromRecordCallees.lsLogOff ∗
          A.pool ∗
          stackAt fsp resStack) ∗
        (m4RestFramePlaced fsp w ∗
          ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ownedBytesRest A inCap inPtr (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - resStack) ∗
          leakBundle) := by
      dsimp only [leakBundle]
      ac_rfl
    rw [hrearr2]
    dsimp only [runSpecPlaced, g_run, frameRun]
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

private theorem m4_err_tail_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser}
    {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {c : CallV} {w : CallW} {s0 sf : State}
    {stk hookStack resStack : Nat} {buf inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {G : Nat → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
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
      (runResAt A wrOk (fsp + 0x1b8#64) (some none) ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap)
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
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap))
    (by rw [hsp_f]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine m4_step_check_err_placed hs_7a4 fun s_err hs_b24 hcs_err htr_err hfs_err => ?_
  have hx23_err : s_err.readReg64 (.gpr 23#5) = inCap := hcs_err.2.2.2.2.1.trans hx23_f
  have hx24_err : s_err.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
    hcs_err.2.2.2.2.2.1.trans hx24_f
  have hx19_err : s_err.readReg64 (.gpr 19#5) = buf := hcs_err.1.trans hx19_f
  have hclose_err :
      ((sf.sp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        (memRegion (fsp + 0x1c0#64) (runResSize - 8) ∗
          m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) ⊢
      ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        locals fsp [cell fsp 0x50 inPtr] ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap := by
    rw [hsp_f]
    have hord :
        ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          (memRegion (fsp + 0x1c0#64) (runResSize - 8) ∗
            m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) =
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            memRegion (fsp + 0x78#64) 56 ∗
            ((fsp + 0x1b8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            memRegion (fsp + 0x1c0#64) (runResSize - 8) ∗
            memRegion (fsp + 0x310#64) 320) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap := by
      ac_rfl
    rw [hord]
    exact sepConj_mono_right
      (sepConj_mono_left (m4_locals_close_err_cell_placed fsp w inPtr 0xffffffffffffffff#64))
  refine sepWPp_weaken_pre hclose_err ?_
  exact m4_step_err_block_placed (ps := ps) hc hext_le hstk64' hs_b24 hx23_err hx24_err hx19_err
    (fun s_exit htr_ex hfs_ex => hG s_exit (htr_ex.trans htr_err) (hfs_ex.trans hfs_err))
    hexit

private theorem m4_ok_tail_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc}
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
        (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    SepWPp (mProgPlaced H) (s0.readReg64 .lr) sf
      (runOkAt A (fsp + 0x1b8#64) g out ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap)
      Q Qp (mainOom s0) := by
  dsimp only
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  refine sepWPp_weaken_pre (sepConj_mono_left (runOkAt_open A (fsp + 0x1b8#64) g out)) ?_
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
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap))
    (by rw [hsp_f]; dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine m4_step_check_ok_placed hs_7a4 hcap_lt fun s' hs_7b0 hcs_ok htr_ok hfs_ok => ?_
  have hclose_m5 :
      ((sf.sp + 0x1b8#64) ↦₆₄ cap) ∗
        (R_ok ∗ m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
          ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) ⊢
      ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗
        locals fsp (m5CellsPlaced A fsp inPtr g out) ∗
        stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap := by
    rw [hsp_f]
    have hord1 :
        ((fsp + 0x1b8#64) ↦₆₄ cap) ∗
          (R_ok ∗ m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
            ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
            argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap) =
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            memRegion (fsp + 0x78#64) 56 ∗
            (((fsp + 0x1b8#64) ↦₆₄ cap) ∗ R_ok) ∗
            memRegion (fsp + 0x310#64) 320) ∗
          stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap := by
      ac_rfl
    rw [hord1]
    exact sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_left
            (Entails.trans
              (sepConj_mono_right
                (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_left hclose_ok))))
              (m4_locals_close_ok_placed A fsp w inPtr g out)))))
  refine sepWPp_weaken_pre hclose_m5 ?_
  exact hk s' hs_7b0
    (hcs_ok.1.trans hx19_f)
    (hcs_ok.2.2.1.trans hx21_f)
    (hcs_ok.2.2.2.1.trans hx22_f)
    (hcs_ok.2.2.2.2.1.trans hx23_f)
    (hcs_ok.2.2.2.2.2.1.trans hx24_f)
    (hcs_ok.2.2.2.2.2.2.2.2.1.trans hx27_f)
    htr_ok hfs_ok

/-! ## 5. Top-Level `main_m4` Theorems under `[LibsignalPlacement]` -/

set_option maxHeartbeats 1200000 in
/-- Post-`run` (`M+0x7a4`) continuation of `main_m4` under `[LibsignalPlacement]`, factored out so
`CliImgBridge` can supply `run`'s `Obj.Image` execution at `lsmpl.base 579` directly and resume on
Block `617` (`mProgPlaced H`) from `M+0x7a4`. -/
theorem m4_after_run_placed [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s s3 sf : State}
    {stk hookStack resStack : Nat} {buf coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0tr : s0.trace = [])
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hs3 : AtM4RunCallPlaced CodeOk s0 s3 i.argv.length buf inCap inPtr (inputOf i c).length)
    (hsp3 : s3.sp = s0.sp - BitVec.ofNat 64 mainFrameSize)
    (htr3_s : s3.trace = s.trace) (htr3_0 : s3.trace = s0.trace) (hfs3_s : s3.fs = s.fs)
    (hinv_f : CodeOk sf.mem)
    (hpcm : sf.pc = mPcPlaced 0x7a4) (hrunm : sf.status = .Running)
    (hspm : sf.sp = s3.sp) (hcsm : CalleeSavedPreserved s3 sf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧ s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)),
      a = some (some (namedWrites g.writes, out)) →
      (∀ pw ∈ g.writes, wrOk pw.1) →
      s.trace <+: s'.trace →
      AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    let g_run : RunCall :=
      { i := i, c := c, a := a, res := fsp + 0x1b8#64, call := fsp + 0x78#64,
        stores := fsp + 0x310#64, inp := inPtr, coins := coinsPtr }
    let frameRun : SepProp :=
      m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        ownedBytesRest A inCap inPtr (inputOf i c) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
        anyHeap
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) sf
      ((runSpecTightPlaced CodeOk A uuidParse Run wrOk resStack).post g_run s3 sf ∗ frameRun)
      Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  let g_run : RunCall :=
    { i := i, c := c, a := a, res := fsp + 0x1b8#64, call := fsp + 0x78#64,
      stores := fsp + 0x310#64, inp := inPtr, coins := coinsPtr }
  let frameRun : SepProp :=
    m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ownedBytesRest A inCap inPtr (inputOf i c) ∗
      argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
      anyHeap
  have hres_le : resStack ≤ stk - mainFrameSize := by omega
  have hstk_split := stackAt_split_ge fsp hres_le (by omega)
  have hsp_f : sf.sp = fsp := hspm.trans hsp3
  have hs_7a4 : InMainPlaced CodeOk s0 sf 0x7a4 :=
    { pc := hpcm, run := hrunm, sp := hsp_f,
      fp := hcsm.2.2.2.2.2.2.2.2.2.2.1.trans hs3.fp, inv := hinv_f,
      vregs := hcsm.2.2.2.2.2.2.2.2.2.2.2.trans hs3.vregs, spAligned := hs.base.spAligned }
  have hx19_f : sf.readReg64 (.gpr 19#5) = buf := hcsm.1.trans hs3.x19
  have hx21_f : sf.readReg64 (.gpr 21#5) = fsp + 0x310#64 := by rw [hcsm.2.2.1, hs3.x21, hsp3]
  have hx22_f : sf.readReg64 (.gpr 22#5) = fsp + 0x78#64 := by rw [hcsm.2.2.2.1, hs3.x22, hsp3]
  have hx23_f : sf.readReg64 (.gpr 23#5) = inCap := hcsm.2.2.2.2.1.trans hs3.x23
  have hx24_f : sf.readReg64 (.gpr 24#5) = BitVec.ofNat 64 i.argv.length :=
    hcsm.2.2.2.2.2.1.trans hs3.x24
  have hx27_f : sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (inputOf i c).length :=
    hcsm.2.2.2.2.2.2.2.2.1.trans hs3.x27
  have hpost_tidy :
      (runSpecTightPlaced CodeOk A uuidParse Run wrOk resStack).post g_run s3 sf ∗ frameRun ⊢
        ⌜s3.trace <+: sf.trace ∧
          sf.fs.files = s3.fs.files ∧
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
        (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
          runResAt A wrOk (fsp + 0x1b8#64) a') ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        mainSaved s0 ∗ stackAt fsp (stk - mainFrameSize) ∗ A.pool ∗ anyHeap := by
    dsimp only [runSpecTightPlaced, runSpecPlaced, g_run, frameRun]
    rw [hsp3]
    have hrearr_post :
        (⌜s3.trace <+: sf.trace ∧
            sf.fs.files = s3.fs.files ∧
            ProcessOutcome.traceStreamBytes .stdout sf.trace =
              ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
          memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
          (inPtr ↦ₛ inputOf i c) ∗ A.pool ∗ stackAt fsp resStack ∗
          (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
            runResAt A wrOk (fsp + 0x1b8#64) a') ∗ anyHeap) ∗
        (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
          ownedBytesRest A inCap inPtr (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
            (stk - mainFrameSize - resStack) ∗ anyHeap) =
        ⌜s3.trace <+: sf.trace ∧
          sf.fs.files = s3.fs.files ∧
          ProcessOutcome.traceStreamBytes .stdout sf.trace =
            ProcessOutcome.traceStreamBytes .stdout s3.trace⌝ ∗
        (∃∗ a' : RunAnswer, ⌜a' ≠ none ∧ a' = a⌝ ∗
          runResAt A wrOk (fsp + 0x1b8#64) a') ∗
        m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
        memRegion (fsp + 0x78#64) 56 ∗ memRegion (fsp + 0x310#64) 320 ∗
        ((inPtr ↦ₛ inputOf i c) ∗ ownedBytesRest A inCap inPtr (inputOf i c)) ∗
        argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
        (memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
          (stk - mainFrameSize - resStack) ∗ stackAt fsp resStack) ∗
        A.pool ∗ (anyHeap ∗ anyHeap) := by
      ac_rfl
    rw [hrearr_post]
    exact sepConj_mono_right
      (sepConj_mono_right
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono_right
                (sepConj_mono (ownedBytes_merge A inCap inPtr (inputOf i c))
                  (sepConj_mono_right
                    (sepConj_mono_right
                      (sepConj_mono (Entails.of_eq hstk_split.symm)
                        (sepConj_mono_right
                          (ProofLib.entails_anyHeap (anyHeap ∗ anyHeap))))))))))))
  refine sepWPp_weaken_pre hpost_tidy ?_
  clear hpost_tidy
  apply SepWPp.pure_left
  rintro ⟨htr_pref3, hfiles, hout⟩
  have htr_pref_s : s.trace <+: sf.trace := by rwa [htr3_s] at htr_pref3
  have hhist_sf : HistOkTight i sf :=
    ⟨by rw [hfiles, hfs3_s]; exact hs.fs, by rw [hout, htr3_0, hs0tr]; rfl⟩
  rw [sepExists_sepConj_left]
  apply m4_sepWPp_exists_left_p; intro a'
  rw [sepConj_assoc]
  apply SepWPp.pure_left
  rintro ⟨ha'_ne, ha'_eq⟩
  cases a' with
  | none => exact (ha'_ne rfl).elim
  | some res =>
    cases res with
    | none =>
      exact m4_err_tail_placed hc hstk hstk64 hs_7a4 hsp_f hx19_f hx23_f hx24_f
        (fun s_exit htr_tot hfs_tot =>
          ⟨rfl, ha'_eq.symm,
            m4_histOkTight_of_eq_p htr_tot hfs_tot hhist_sf,
            by rwa [htr_tot]⟩)
        hexit
    | some p =>
      rcases p with ⟨ws, out⟩
      dsimp only [runResAt]
      rw [sepExists_sepConj_left]
      apply m4_sepWPp_exists_left_p; intro g
      rw [sepConj_assoc]
      apply SepWPp.pure_left
      rintro ⟨hws, hwr⟩
      subst hws
      exact m4_ok_tail_placed hs_7a4 hsp_f hx19_f hx21_f hx22_f hx23_f hx24_f hx27_f
        fun s' hs_7b0 hx19' hx21' hx22' hx23' hx24' hx27' htr_ok hfs_ok =>
          hnext s' g out ha'_eq.symm hwr (by rwa [htr_ok])
            { base := hs_7b0, x19 := hx19', x21 := hx21', x22 := hx22', x23 := hx23',
              x24 := hx24', x27 := hx27',
              hist := m4_histOkTight_of_eq_p htr_ok hfs_ok hhist_sf }

set_option maxHeartbeats 1200000 in
/-- Proves `AtM4EndTightPlaced` and exact `a` postcondition over `runSpecTightPlaced` when
`∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000`. -/
theorem main_m4_tight_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk A uuidParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)),
      a = some (some (namedWrites g.writes, out)) →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
  refine m4_to_run_call_placed (hookStack := hookStack) (wrOk := wrOk)
    hstk hsp hs0tr hRun hnot_over hparse hs
    fun s3 hs3 hsp3 htr3_s htr3_0 hfs3_s => ?_
  let g_run : RunCall :=
    { i := i, c := c, a := a, res := fsp + 0x1b8#64, call := fsp + 0x78#64,
      stores := fsp + 0x310#64, inp := inPtr, coins := coinsPtr }
  let frameRun : SepProp :=
    m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
      ownedBytesRest A inCap inPtr (inputOf i c) ∗
      argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
      memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize)) (stk - mainFrameSize - resStack) ∗
      anyHeap
  refine main_call_plain (CodeOk := CodeOk) g_run hrun hs3.inv hs3.pc hs3.run hs3.spAligned
    hs3.lr (Entails.refl _)
    (hpanic := fun sf R' _ hp => ?_)
    (hoom := fun sf R' _ ho => ?_)
    (hnext := fun sf hinv_f hpcm hrunm hspm hcsm => ?_)
  · dsimp only [runSpecTightPlaced, runSpecPlaced, g_run] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    exact hpanic sf _ (hp.1.imp_right (m4_allocFailedIn_of_start_trace_eq_p htr3_0))
  · dsimp only [runSpecTightPlaced, runSpecPlaced] at ho
    exact (not_satisfies_false_sepConj ho).elim
  · exact m4_after_run_placed (Run := Run) (coinsPtr := coinsPtr)
      hc hstk hstk64 hs0tr hs hs3 hsp3 htr3_s htr3_0 hfs3_s hinv_f hpcm hrunm hspm hcsm hexit hnext

/-- Direct `uuidTryParse` + `¬ IsSendOverCap i` specialization matching
`MainOkComposePlaced.step4_call`. -/
theorem main_m4_call_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidTryParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecTightPlaced CodeOk A uuidTryParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a) (hnover : ¬ IsSendOverCap i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ a = some none ∧ HistOkTight i s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)),
      a = some (some (namedWrites g.writes, out)) →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndTightPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOom s0) :=
  main_m4_tight_placed_proof hc hrun hstk hstk64 hsp hs0tr hRun
    (fun peer hc_eq => Nat.le_of_not_lt fun hgt => hnover ⟨⟨peer, hc_eq ▸ hparse⟩, hgt⟩)
    hparse hs hpanic hexit hnext

/-- Legacy `mainOomLegacy` wrapper over `main_m4_tight_placed_proof`. -/
theorem main_m4_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop}
    [LsCodeInv CodeOk] {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop}
    {i : Inputs} {a : RunAnswer} {c : CallV} {w : CallW} {s0 s : State}
    {stk hookStack resStack : Nat} {buf p0 coinsCap coinsPtr inCap inPtr : BitVec 64}
    {ps : List (BitVec 64 × List (BitVec 8))} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hrun : subroutine_ok (mProgPlaced H) (lsmpl.base 579)
      (runSpecPlaced CodeOk A uuidParse Run wrOk resStack))
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hsp : stk ≤ s0.sp.toNat)
    (hs0tr : s0.trace = [])
    (hRun : Run i a)
    (hnot_over : ∀ peer, c = .send peer → i.stdin.length ≤ 1_000_000)
    (hparse : parseArgs uuidParse (i.argv.map bytesOfString) = some c)
    (hs : AtM4Placed CodeOk i s0 s w c i.argv.length buf coinsCap coinsPtr inCap)
    (hpanic : ∀ sf Pf, (a = none ∨ allocFailedIn s0 sf) → Qp sf Pf)
    (hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s' => code = 1 ∧ (a = some none ∨ allocFailedIn s0 s') ∧ HistOk i s0 s' ∧
        s.trace <+: s'.trace) Q Qp)
    (hnext : ∀ (s' : State) (g : StoresGhost) (out : List (BitVec 8)),
      (a = some (some (namedWrites g.writes, out)) ∨ allocFailedIn s0 s') →
      (∀ pw ∈ g.writes, wrOk pw.1) → s.trace <+: s'.trace →
      AtM4EndPlaced CodeOk i s0 s' c i.argv.length buf inCap →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
        (ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
          argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          mainSaved s0 ∗
          locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
            (m5CellsPlaced A (s0.sp - BitVec.ofNat 64 mainFrameSize) inPtr g out) ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ anyHeap)
        Q Qp (mainOom s0)) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A coinsCap coinsPtr (BitVec.ofNat 64 (coinsOf i).length) (coinsOf i) ∗
        ownedBytes A inCap inPtr (BitVec.ofNat 64 (inputOf i c).length) (inputOf i c) ∗
        callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
        argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
        mainSaved s0 ∗
        locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
          (m4CellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w inPtr (coinsOf i).length) ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ cliStaticsPlaced ∗ mainLitsBlk617)
      Q Qp (mainOomLegacy s0) := by
  apply sepWPp_of_mainOom
  exact main_m4_tight_placed_proof hc hrun hstk hstk64 hsp hs0tr hRun hnot_over hparse hs hpanic
    (fun s' code hs' ⟨hc1, ha, hhist, htr⟩ =>
      hexit s' code hs' ⟨hc1, Or.inl ha, Or.inl hhist, htr⟩)
    (fun s' g out ha hwr htr hAt =>
      hnext s' g out (Or.inl ha) hwr htr hAt.toAtM4EndPlaced)

end CryptoVerification.SignalSession.Cli.MainHops
