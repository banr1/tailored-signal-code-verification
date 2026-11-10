/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# Stage 3 KEM Seed Unroll Helpers

Reusable 4-byte `signal_session_coins_fill(fsp + 0x1600, 4)` draw helpers (`coinWord`,
`s3_coins_fill4`, `s3_draw_to_slot`) shared across `KemCoinsA`, `KemCoinsB`, and `KemCoinsC`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

def dhPrefix (dh1 dh2 dh3 : SignalPqxdh.Bytes) (dh4? : Option SignalPqxdh.Bytes) : SignalPqxdh.Bytes :=
  match dh4? with
  | none => F_X25519 ++ dh1 ++ dh2 ++ dh3
  | some dh4 => F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4

def dhRemAt (secretsPtr : BitVec 64) (dh4? : Option SignalPqxdh.Bytes) : SepProp :=
  match dh4? with
  | none => memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32
  | some _ => memRegion (secretsPtr + 160#64) 32

def dhLenWord (dh4? : Option SignalPqxdh.Bytes) : BitVec 64 :=
  match dh4? with
  | none => 128#64
  | some _ => 160#64

theorem sepWPp_oom_jmp {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (h : SepWP prog mid s emp
      (fun s' q => q = emp ∧ s'.pc = mid ∧ s'.status = .Running ∧ s'.trace = s.trace))
    (hoom : ∀ s' : State, s'.pc = mid → s'.status = .Running → s'.trace = s.trace →
      SepWPp prog ret s' P Q Qp Qoom) : SepWPp prog ret s P Q Qp Qoom := fun R hm hL => by
  rcases h.elim (by rwa [emp_sepConj] : s.mem ⊨ emp ∗ (P ∗ R)) hL with
    ⟨s', hst, ⟨-, -, _, hq, rfl, hpc', hrun', htr'⟩ | ⟨_, hf⟩⟩
  · rw [emp_sepConj] at hq
    obtain ⟨sf, hst', hout⟩ := hoom s' hpc' hrun' htr' R hq (hst.codeLoaded hL)
    exact ⟨sf, hst.trans hst', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem cells4_to_memRegion32 (p w0 w1 w2 w3 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ⊢
      memRegion p 32 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))) ?_
  rw [memRegion_merge_at (p + 16#64) 8 8 (p + 24#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (p + 8#64) 8 16 (p + 16#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at p 8 24 (p + 8#64) (by clear * -; bv_omega) (by decide)]
  exact Entails.refl _

theorem buildSecrets_take32_eq (dh1 dh2 dh3 : SignalPqxdh.Bytes) (dh4? : Option SignalPqxdh.Bytes)
    (kemSs : SignalPqxdh.Bytes) :
    (buildSecrets dh1 dh2 dh3 dh4? kemSs).take 32 = F_X25519 := by
  cases dh4? <;>
    simp [buildSecrets, F_X25519, List.append_assoc, List.take_append_of_le_length]

theorem tail_locals_collapse (fsp : BitVec 64) {ekASk kpk : List (BitVec 8)}
    (hek : ekASk.length = 32) (hkpk : kpk.length = 1568)
    (secretsPtr lenWord : BitVec 64) :
    memRegion (fsp + 0x994#64) 12 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
      ((fsp + 0x9c0#64) ↦ₛ kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
      ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
      ((fsp + 0x1c70#64) ↦₆₄ lenWord) ∗ memRegion (fsp + 0x1c78#64) 0x18 ⊢
      memRegion (fsp + 0x994#64) (initLocalsSize - 0x994) := by
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsToBytes_entails_memRegion_len hek)
        (sepConj_mono (pointsToBytes_entails_memRegion_len hkpk)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (Entails.refl _)))))))) ?_
  rw [memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x1c68#64) 8 0x20 (fsp + 0x1c70#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x1c60#64) 8 0x28 (fsp + 0x1c68#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0xfe0#64) 0xc80 0x30 (fsp + 0x1c60#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x9c0#64) 1568 0xcb0 (fsp + 0xfe0#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x9a0#64) 32 0x12d0 (fsp + 0x9c0#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x994#64) 12 0x12f0 (fsp + 0x9a0#64) (by clear * -; bv_omega) (by decide)]
  exact Entails.refl _

@[simp] theorem setWidth64_trunc32 (v : BitVec 32) :
    (v.setWidth 64).truncate 32 = v := by bv_omega

@[simp] theorem extract31_setWidth64 (v : BitVec 32) :
    (v.setWidth 64).extractLsb' 0 32 = v := by
  ext i hi; simp [BitVec.getElem_extractLsb', BitVec.getElem_setWidth, hi,
    Nat.lt_trans hi (by decide : 32 < 64)]

@[simp] theorem setWidth64_trunc8 (v : BitVec 32) :
    (v.setWidth 64).truncate 8 = v.truncate 8 := by bv_omega

@[simp] theorem extract7_setWidth64 (v : BitVec 32) :
    (v.setWidth 64).extractLsb' 0 8 = v.truncate 8 := by
  ext i hi; simp [BitVec.truncate_eq_setWidth, BitVec.getElem_extractLsb', BitVec.getElem_setWidth,
    hi, Nat.lt_trans hi (by decide : 8 < 64)]

def coinWord (t : List.Vector (BitVec 8) initiateTapeLen) (i : Nat) (hi : i < 32) : BitVec 32 :=
  t.get ⟨32 + 4 * i + 3, by unfold initiateTapeLen; omega⟩ ++
    t.get ⟨32 + 4 * i + 2, by unfold initiateTapeLen; omega⟩ ++
    t.get ⟨32 + 4 * i + 1, by unfold initiateTapeLen; omega⟩ ++
    t.get ⟨32 + 4 * i, by unfold initiateTapeLen; omega⟩

theorem coinDraw4_eq_pointsTo32 (a : BitVec 64)
    (t : List.Vector (BitVec 8) initiateTapeLen) (i : Nat) (hi : i < 32) :
    (a ↦ₛ (t.toList.drop (32 + 4 * i)).take 4) = (a ↦₃₂ coinWord t i hi) := by
  rw [drop_take_four_of_vec192 t i hi, ProofLib.pointsToBytes4_eq_pointsTo32, coinWord]

theorem coinWord_truncate8 (t : List.Vector (BitVec 8) initiateTapeLen) (i : Nat) (hi : i < 32) :
    (coinWord t i hi).truncate 8 = (initiateKemCoins t).get ⟨i, hi⟩ := by
  rw [coinWord, truncate8_pack4, initiateKemCoins, List.Vector.get_ofFn]

/-- Reusable 4-byte `signal_session_coins_fill(fsp + 0x1600, 4)` draw helper for step `i < 32`. -/
theorem s3_coins_fill4 {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hh : RunHooks img A (cliExterns W))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi : i < 32) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntry img W +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
    (hlr : s.readReg64 .lr = initPc img W k_out)
    (hx0 : s.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hx1 : s.readReg64 .x1 = 4#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢
      coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂ 0#32) ∗
        stackAt s.sp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm : State,
      InInitiate img W s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt s.sp cliCoinsFillStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  let g : CoinsFillGhost := ⟨fsp + 0x1600#64, 4, x.coinsP, x.coins, 32 + 4 * i⟩
  have hcall := hCoins (le_refl cliCoinsFillStack) (by decide)
  have hpc' : s.pc = (initProg img W).fnAddr cliCoinsFillName :=
    hpc.trans (coinsFill_fnAddr_eq img W)
  have hpre' : P ⊢ (coinsFillSpec img cliCoinsFillStack).pre g s ∗ F := by
    refine Entails.trans hpre ?_
    simp only [coinsFillSpec, Spec.inImage, g, sepConj_assoc]
    refine Entails.pure_right hctrl.inv
      (Entails.pure_right ⟨hx0, hx1, hcoinsLt, by unfold initiateTapeLen; omega⟩ ?_)
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion _ 0#32)))
      (Entails.of_eq (by dsimp only [fsp]; try ac_rfl))
  refine s3_call hh hcall g F hctrl htr hpc' hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp only [coinsFillSpec, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ _ h; simp only [coinsFillSpec, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ h; simp only [coinsFillSpec, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro sm _ _ _ hcsm _ hof
    simp only [coinsFillSpec, Spec.inImage, g, sepConj_assoc]
    refine sepWPp_pure_elim_oom fun ⟨htrm, _⟩ => ?_
    rw [show (32 + 4 * i) + 4 = 32 + 4 * (i + 1) from by omega,
        coinDraw4_eq_pointsTo32 (fsp + 0x1600#64) (padCoins x.coins) i hi]
    exact sepWPp_conseq_oom
      (Entails.of_eq (by dsimp only [fsp]))
      (hnext sm (hof htrm) hcsm htrm)

/-- Combined block+call step for unrolled coin draw `i ∈ [1, 24]` storing `w_{i-1}` at `slotOff`. -/
theorem s3_draw_to_slot {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hh : RunHooks img A (cliExterns W))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32)
    (k_in k_out : Nat) (slotOff : BitVec 64) (oldSlot : BitVec 32) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s k_in) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 k_in →
      s.status = .Running →
      s.readReg64 (.gpr 20#5) = s.sp + 0x348#64 →
      s.readReg64 (.gpr 21#5) = s.sp + 0x388#64 →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExterns W)))
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName +
          bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
        s
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((s.sp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt s.sp cliCoinsFillStack ∗ G)
        (fun sm Pm =>
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              ((s.sp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
              stackAt s.sp cliCoinsFillStack ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr =
            (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
            sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((fsp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiate img W s0 sm k_out → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sm
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  dsimp only at hpre hnext
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨halign, _, hfsp⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom hpre ?_
  refine' s3_block_to_call hh
    (initEntry img W +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
    k_out
    (Φ := fun sm =>
      sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
      sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc
    dsimp only [initPc, initEntry, initProg, tripleRatchetProgAtExt] at hpc ⊢
    rw [hfsp]
    exact hstep F halign hpc hctrl.run
      (by rwa [← hfsp]) (by rwa [← hfsp])
  · intro sm hctrlm hpcm hlrm htrm ⟨hx0m, hx1m, hx20m, hx21m⟩
    rw [← hfsp] at hx0m hx20m hx21m ⊢
    refine s3_coins_fill4 hh hCoins hcoinsLt i hi
      (((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
      hctrlm (htrm.trans htr) hpcm hlrm hx0m hx1m hpanic
      (by rw [hctrlm.sp]; (try dsimp only [fsp] at *); sep_frame) ?_
    intro s' hctrl' hcs' htr'
    rw [hctrlm.sp]; (try dsimp only [fsp] at *)
    exact hnext s' hctrl' (htr'.trans (htrm.trans htr))
      (hcs'.2.1.trans hx20m) (hcs'.2.2.1.trans hx21m)

theorem pack_cells4_append (a off0 off1 off2 off3 : BitVec 64)
    (pre ssBytes full : SignalPqxdh.Bytes) (w0 w1 w2 w3 : BitVec 64)
    (hfold : ((a + off0) ↦₆₄ w0) ∗ ((a + off1) ↦₆₄ w1) ∗
      ((a + off2) ↦₆₄ w2) ∗ ((a + off3) ↦₆₄ w3) =
      ((a + off0) ↦ₛ bytesToBv8 ssBytes))
    (happ : (a ↦ₛ bytesToBv8 pre) ∗ ((a + off0) ↦ₛ bytesToBv8 ssBytes) =
      (a ↦ₛ bytesToBv8 full))
    (R : SepProp) :
    (a ↦ₛ bytesToBv8 pre) ∗
      ((a + off0) ↦₆₄ w0) ∗ ((a + off1) ↦₆₄ w1) ∗
      ((a + off2) ↦₆₄ w2) ∗ ((a + off3) ↦₆₄ w3) ∗ R =
      (a ↦ₛ bytesToBv8 full) ∗ R := by
  rw [← hfold] at happ
  simp only [← happ, sepConj_assoc]

theorem repack_pqxdh_stk (pool s1 s2 s3 s4 s5 s6 m rest : SepProp)
    (h : s6 ∗ s1 = m) :
    pool ∗ s1 ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ s6 ∗ rest =
      pool ∗ m ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ rest := by
  rw [← h]; ac_rfl

theorem allOnes64_4_hex_eq_F_X25519 (a : BitVec 64) :
    (a ↦₆₄ 0xffffffffffffffff#64) ∗ ((a + 8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((a + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((a + 24#64) ↦₆₄ 0xffffffffffffffff#64) =
      (a ↦ₛ bytesToBv8 F_X25519) :=
  allOnes64_4_eq_F_X25519 a

theorem s3_step_b6c_b8c {img : Obj.Image} {W : CliHooks} {s : State}
    (pqspkPtr z70 : BitVec 64) (G : SepProp)
    (halign : (s.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 0xb6c)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 0x408#64) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExterns W)))
      ((libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
      s (((s.sp + 0x70#64) ↦₆₄ z70) ∗ ((s.sp + 0x428#64) ↦₆₄ pqspkPtr) ∗
        ((s.sp + 0x430#64) ↦₆₄ 1568#64) ∗ G)
      (fun sm Pm =>
        sm.trace = s.trace ∧
        (Pm ⊢ ((s.sp + 0x70#64) ↦₆₄ (s.sp + 0x408#64)) ∗ ((s.sp + 0x428#64) ↦₆₄ pqspkPtr) ∗
          ((s.sp + 0x430#64) ↦₆₄ 1568#64) ∗ G) ∧
        sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .lr = (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 0xb8c ∧
        (sm.readReg64 .x0 = s.sp + 0x9c0#64 ∧ sm.readReg64 .x1 = pqspkPtr ∧
          sm.readReg64 .x2 = 1568#64 ∧
          sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)) := by
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb6c 32
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
  try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22
  examples_hide_fetches; wp_steps
  exact s3_done_call (hpc := by wp_norm_goal) (by wp_norm_lhs)
    (by sep_frame)
    ⟨by wp_norm_goal, by simp only [arm64_norm, wp_norm], by wp_norm_goal,
     by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩

theorem s3_step_b8c_ba0 {img : Obj.Image} {W : CliHooks} {s : State}
    (z1600 : BitVec 32) (G : SepProp)
    (halign : (s.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 0xb8c)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0x388#64) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExterns W)))
      ((libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
      s (((s.sp + 0x1600#64) ↦₃₂ z1600) ∗ G)
      (fun sm Pm =>
        sm.trace = s.trace ∧
        (Pm ⊢ ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗ G) ∧
        sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .lr = (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName + BitVec.ofNat 64 0xba0 ∧
        (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
          sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)) := by
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExterns W))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb8c 20
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = entry
  try simp only [arm64_norm, wp_norm] at hx20 hx21
  examples_hide_fetches; wp_steps
  exact s3_done_call (hpc := by wp_norm_goal) (by wp_norm_lhs)
    (by sep_frame)
    ⟨by wp_norm_goal, by wp_norm_goal,
     by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩

/-! ## Contract-Parameterized Coin Draw & Step Helpers (`Stage3Lemmas.Ext.*`) -/

namespace Ext

theorem s3_coins_fill4 {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi : i < 32) (F : SepProp)
    {s0 s : State} {k_in k_out : Nat} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hpc : s.pc = initEntryExt img ext +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
    (hlr : s.readReg64 .lr = initPcExt img ext k_out)
    (hx0 : s.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64)
    (hx1 : s.readReg64 .x1 = 4#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hpre : P ⊢
      coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
        (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂ 0#32) ∗
        stackAt s.sp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm : State,
      InInitiateExt img ext s0 sm k_out → CalleeSavedPreserved s sm → sm.trace = s.trace →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          (((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x1600#64) ↦₃₂
            coinWord (padCoins x.coins) i hi) ∗
          stackAt s.sp cliCoinsFillStack ∗ F) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  let g : CoinsFillGhost := ⟨fsp + 0x1600#64, 4, x.coinsP, x.coins, 32 + 4 * i⟩
  have hcall := hCoins (le_refl cliCoinsFillStack) (by decide)
  have hpc' : s.pc = (initProgExt img ext).fnAddr cliCoinsFillName :=
    hpc.trans (coinsFill_fnAddr_eq img ext)
  have hpre' : P ⊢ (coinsFillSpec img cliCoinsFillStack).pre g s ∗ F := by
    refine Entails.trans hpre ?_
    simp only [coinsFillSpec, Spec.inImage, g, sepConj_assoc]
    refine Entails.pure_right hctrl.inv
      (Entails.pure_right ⟨hx0, hx1, hcoinsLt, by unfold initiateTapeLen; omega⟩ ?_)
    exact Entails.trans
      (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion _ 0#32)))
      (Entails.of_eq (by dsimp only [fsp]; try ac_rfl))
  refine s3_call hOk hcall g F hctrl htr hpc' hlr hpanic hpre' ?_ ?_ ?_ ?_
  · intro _ _ h; simp only [coinsFillSpec, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ _ h; simp only [coinsFillSpec, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro _ _ h; simp only [coinsFillSpec, Spec.inImage] at h
    exact (not_satisfies_false_sepConj h).elim
  · intro sm _ _ _ hcsm _ hof
    simp only [coinsFillSpec, Spec.inImage, g, sepConj_assoc]
    refine sepWPp_pure_elim_oom fun ⟨htrm, _⟩ => ?_
    rw [show (32 + 4 * i) + 4 = 32 + 4 * (i + 1) from by omega,
        coinDraw4_eq_pointsTo32 (fsp + 0x1600#64) (padCoins x.coins) i hi]
    exact sepWPp_conseq_oom
      (Entails.of_eq (by dsimp only [fsp]))
      (hnext sm (hof htrm) hcsm htrm)

theorem s3_draw_to_slot {img : Obj.Image} {P0 : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem}
    {x : InitGhost} {stk : Nat}
    (hOk : CliExternsOk P0 A ext)
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (i : Nat) (hi_prev : i - 1 < 32) (hi : i < 32)
    (k_in k_out : Nat) (slotOff : BitVec 64) (oldSlot : BitVec 32) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s k_in) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hstep : ∀ (G : SepProp),
      (s.sp &&& 15#64 == 0#64) = true →
      s.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 k_in →
      s.status = .Running →
      s.readReg64 (.gpr 20#5) = s.sp + 0x348#64 →
      s.readReg64 (.gpr 21#5) = s.sp + 0x388#64 →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)))
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName +
          bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
        s
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
          ((s.sp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((s.sp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt s.sp cliCoinsFillStack ∗ G)
        (fun sm Pm =>
          sm.trace = s.trace ∧
          (Pm ⊢
            coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
              ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗
              ((s.sp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
              stackAt s.sp cliCoinsFillStack ∗ G) ∧
          sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.readReg64 .lr =
            (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 k_out ∧
          (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
            sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
            sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)))
    (hpre :
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      P ⊢
        coinsCursorAt img x.coinsP x.coins (32 + 4 * i) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗
          ((fsp + slotOff) ↦₃₂ oldSlot) ∗
          stackAt fsp cliCoinsFillStack ∗ F)
    (hnext : ∀ sm : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      InInitiateExt img ext s0 sm k_out → sm.trace = s0.trace →
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sm
        (coinsCursorAt img x.coinsP x.coins (32 + 4 * (i + 1)) ∗
          ((fsp + 0x1600#64) ↦₃₂ coinWord (padCoins x.coins) i hi) ∗
          stackAt fsp cliCoinsFillStack ∗
          ((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s P Q Qp (initOom s0) := by
  dsimp only at hpre hnext
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  obtain ⟨halign, _, hfsp⟩ := hctrl.step_ctx fsp
  refine sepWPp_conseq_oom hpre ?_
  refine' s3_block_to_call hOk
    (initEntryExt img ext +
      bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
    k_out
    (Φ := fun sm =>
      sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
      sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
      sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc := hctrl.pc
    dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc ⊢
    rw [hfsp]
    exact hstep F halign hpc hctrl.run
      (by rwa [← hfsp]) (by rwa [← hfsp])
  · intro sm hctrlm hpcm hlrm htrm ⟨hx0m, hx1m, hx20m, hx21m⟩
    rw [← hfsp] at hx0m hx20m hx21m ⊢
    refine s3_coins_fill4 hOk hCoins hcoinsLt i hi
      (((fsp + slotOff) ↦₃₂ coinWord (padCoins x.coins) (i - 1) hi_prev) ∗ F)
      hctrlm (htrm.trans htr) hpcm hlrm hx0m hx1m hpanic
      (by rw [hctrlm.sp]; (try dsimp only [fsp] at *); sep_frame) ?_
    intro s' hctrl' hcs' htr'
    rw [hctrlm.sp]; (try dsimp only [fsp] at *)
    exact hnext s' hctrl' (htr'.trans (htrm.trans htr))
      (hcs'.2.1.trans hx20m) (hcs'.2.2.1.trans hx21m)

theorem s3_step_b6c_b8c {img : Obj.Image} {ext : String → Option (State → State)} {s : State}
    (pqspkPtr z70 : BitVec 64) (G : SepProp)
    (halign : (s.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 0xb6c)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 0x408#64) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)))
      ((libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
      s (((s.sp + 0x70#64) ↦₆₄ z70) ∗ ((s.sp + 0x428#64) ↦₆₄ pqspkPtr) ∗
        ((s.sp + 0x430#64) ↦₆₄ 1568#64) ∗ G)
      (fun sm Pm =>
        sm.trace = s.trace ∧
        (Pm ⊢ ((s.sp + 0x70#64) ↦₆₄ (s.sp + 0x408#64)) ∗ ((s.sp + 0x428#64) ↦₆₄ pqspkPtr) ∗
          ((s.sp + 0x430#64) ↦₆₄ 1568#64) ∗ G) ∧
        sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .lr = (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 0xb8c ∧
        (sm.readReg64 .x0 = s.sp + 0x9c0#64 ∧ sm.readReg64 .x1 = pqspkPtr ∧
          sm.readReg64 .x2 = 1568#64 ∧
          sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)) := by
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb6c 32
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
  try simp only [arm64_norm, wp_norm] at hx20 hx21 hx22
  examples_hide_fetches; wp_steps
  exact s3_done_call (hpc := by wp_norm_goal) (by wp_norm_lhs)
    (by sep_frame)
    ⟨by wp_norm_goal, by simp only [arm64_norm, wp_norm], by wp_norm_goal,
     by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩

theorem s3_step_b8c_ba0 {img : Obj.Image} {ext : String → Option (State → State)} {s : State}
    (z1600 : BitVec 32) (G : SepProp)
    (halign : (s.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 0xb8c)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 0x388#64) :
    SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)))
      ((libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName +
        bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
      s (((s.sp + 0x1600#64) ↦₃₂ z1600) ∗ G)
      (fun sm Pm =>
        sm.trace = s.trace ∧
        (Pm ⊢ ((s.sp + 0x1600#64) ↦₃₂ 0#32) ∗ G) ∧
        sm.sp = s.sp ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .lr = (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName + BitVec.ofNat 64 0xba0 ∧
        (sm.readReg64 .x0 = s.sp + 0x1600#64 ∧ sm.readReg64 .x1 = 4#64 ∧
          sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 ∧
          sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64)) := by
  code_fetches_range libsignalSessionCode initS3 img.base (Rust.withPanics (cliExternsWith ext))
    cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 0xb8c 20
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = entry
  try simp only [arm64_norm, wp_norm] at hx20 hx21
  examples_hide_fetches; wp_steps
  exact s3_done_call (hpc := by wp_norm_goal) (by wp_norm_lhs)
    (by sep_frame)
    ⟨by wp_norm_goal, by wp_norm_goal,
     by simp only [hx20, arm64_norm, wp_norm], by simp only [hx21, arm64_norm, wp_norm]⟩

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
