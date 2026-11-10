/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFrame
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpper
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Stage 3 (`one-time-pre-key` Helpers, Error Exits, and Stack Copy) of Arm `R1b` (`0x12dc → 0x24ec`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

gen_decodes CryptoVerification.libsignalSessionCode_tree r1bDecOpk
  [(ls_off% "libsignal_cli::run" + 0x12dc) → (ls_off% "libsignal_cli::run" + 0x1384),
   (ls_off% "libsignal_cli::run" + 0x1b98) → (ls_off% "libsignal_cli::run" + 0x1bdc),
   (ls_off% "libsignal_cli::run" + 0x23f4) → (ls_off% "libsignal_cli::run" + 0x23f8),
   (ls_off% "libsignal_cli::run" + 0x2420) → (ls_off% "libsignal_cli::run" + 0x2460),
   (ls_off% "libsignal_cli::run" + 0x2490) → (ls_off% "libsignal_cli::run" + 0x24ec),
   (ls_off% "libsignal_cli::run" + 0x26a8) → (ls_off% "libsignal_cli::run" + 0x26cc)]

/-! ## Scratch Stack Partition and `ownedBytes` Zero-Capacity Drop -/

theorem r1b_ownedBytes_cap0_emp (A : RustAlloc) (ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A 0#64 ptr len bs ⊢ emp := by
  rw [r1b_ownedBytes_borrow A 0#64 ptr len bs]
  apply Entails.pure_left
  rintro ⟨_, hle, _, _⟩
  have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
  subst hnil
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [pointsToBytes_nil, r1b_ownedRest, h0, ↓reduceIte, emp_sepConj]
  exact Entails.refl _

theorem r1b_memRegion7_to_head7 (d : BitVec 64) :
    memRegion d 7 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
        Wire.sevenBytesHeadAt d b0 b1 b2 b3 b4 b5 b6 := by
  rw [r1b_head7_init d]
  refine Entails.sepExists_elim fun v0 => Entails.sepExists_elim fun d4 =>
    Entails.sepExists_elim fun d5 => Entails.sepExists_elim fun d6 => ?_
  have hv0 : v0 = v0.extractLsb' 24 8 ++ v0.extractLsb' 16 8 ++
      v0.extractLsb' 8 8 ++ v0.extractLsb' 0 8 := by bv_bits
  refine Entails.sepExists_right (v0.extractLsb' 0 8)
    (Entails.sepExists_right (v0.extractLsb' 8 8)
    (Entails.sepExists_right (v0.extractLsb' 16 8)
    (Entails.sepExists_right (v0.extractLsb' 24 8)
    (Entails.sepExists_right d4 (Entails.sepExists_right d5
    (Entails.sepExists_right d6 ?_))))))
  dsimp only [Wire.sevenBytesHeadAt]
  rw [← hv0]
  exact Entails.refl _

/-- `r1b_invCore` without the scratch stack regions `[0x1d0..0x260)` and `[0x2c0..0x4d0)`. -/
def r1b_invCoreBase (A : RustAlloc) (img : Obj.Image) (g : RunCall) (d : Init1Data)
    (s0 : State) : SepProp :=
  let fsp := runFsp s0
  memRegion g.res runResSize ∗ memRegion g.call 56 ∗
    storesAt A g.stores StoresGhost.opened ∗ (g.inp ↦ₛ inputOf g.i g.c) ∗
    coinsInstalled img g.coins (MainHops.coinsOf g.i) ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    addrNameHeap A d.meG ∗ runSaved s0 ∗
    memRegion (fsp + 0x118#64) 4 ∗ memRegion (fsp + 0x160#64) 4 ∗
    ((fsp + 0x180#64) ↦₆₄ d.ikW0) ∗
    ((fsp + 0x1b8#64) ↦₆₄ d.meG.name.ptr) ∗
    ((fsp + 0x1c0#64) ↦₆₄ d.dirCap) ∗
    ((fsp + 0x1c8#64) ↦₆₄ d.dirPtr) ∗
    addrUpperAt (fsp + 0x260#64) d.meG ∗
    memRegion (fsp + 0x270#64) 0x30 ∗
    protocolAddressAt A d.peerG (fsp + 0x2a0#64) ∗
    memRegion (fsp + 0x500#64) 0x1250 ∗
    memRegion (fsp + 0x1768#64) 0x1288

theorem r1b_invCore_split_mid (A : RustAlloc) (img : Obj.Image) (g : RunCall) (d : Init1Data)
    (s0 : State) :
    r1b_invCore A img g d s0 =
      r1b_invCoreBase A img g d s0 ∗
        memRegion (runFsp s0 + 0x1d0#64) 0x90 ∗
        memRegion (runFsp s0 + 0x2c0#64) 0x210 := by
  dsimp only [r1b_invCore, r1b_invCoreBase]
  r1b_ac

/-- Stage-1 `opk` scratch layout at `0x24dc` / `0x24ec` (uniform across `opk = none` and `opk = some`; `w0e0.truncate 8 = b8`, `w0e4.truncate 8 = b7`). -/
def r1b_opkStage1At (fsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    SepProp :=
  memRegion fsp 0x0e0 ∗
    ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗
    ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
    ((fsp + 0x0e8#64) ↦₆₄ w15) ∗
    memRegion (fsp + 0x0f0#64) 0x20 ∗
    memRegion (fsp + 0x1d0#64) 0x50 ∗
    ((fsp + 0x220#64) ↦₆₄ w23) ∗
    ((fsp + 0x228#64) ↦₈ b31) ∗
    memRegion (fsp + 0x229#64) 0x37 ∗
    memRegion (fsp + 0x2c0#64) 0xf8 ∗
    Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
    memRegion (fsp + 0x3bf#64) 0x19 ∗
    ((fsp + 0x3d8#64) ↦₃₂ w9) ∗
    ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
    memRegion (fsp + 0x3de#64) 0xf2

theorem r1b_opkStage1_of_regions (fsp : BitVec 64) :
    (memRegion fsp 0x110 ∗
      memRegion (fsp + 0x1d0#64) 0x90 ∗
      memRegion (fsp + 0x2c0#64) 0x210) ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
      ∃∗ w0e0 : BitVec 32, ∃∗ w0e4 : BitVec 32,
      ∃∗ w9 : BitVec 32, ∃∗ w13 : BitVec 16,
      ∃∗ w15 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ b31 : BitVec 8,
        r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 := by
  have hlow : memRegion fsp 0x110 =
      memRegion fsp 0x0e0 ∗
        memRegion (fsp + 0x0e0#64) 4 ∗ memRegion (fsp + 0x0e4#64) 4 ∗
        memRegion (fsp + 0x0e8#64) 8 ∗ memRegion (fsp + 0x0f0#64) 0x20 := by
    rw [ProofLib.memRegion_split fsp 0x0e0 0x30 (by decide),
      r1b_split_region fsp 0x0e0 4 0x2c,
      r1b_split_region fsp 0x0e4 4 0x28,
      r1b_split_region fsp 0x0e8 8 0x20]
  have hmid : memRegion (fsp + 0x1d0#64) 0x90 =
      memRegion (fsp + 0x1d0#64) 0x50 ∗
        memRegion (fsp + 0x220#64) 8 ∗ memRegion (fsp + 0x228#64) 1 ∗
        memRegion (fsp + 0x229#64) 0x37 := by
    rw [r1b_split_region fsp 0x1d0 0x50 0x40,
      r1b_split_region fsp 0x220 8 0x38,
      r1b_split_region fsp 0x228 1 0x37]
  have hhi : memRegion (fsp + 0x2c0#64) 0x210 =
      memRegion (fsp + 0x2c0#64) 0xf8 ∗
        memRegion (fsp + 0x3b8#64) 7 ∗ memRegion (fsp + 0x3bf#64) 0x19 ∗
        memRegion (fsp + 0x3d8#64) 4 ∗ memRegion (fsp + 0x3dc#64) 2 ∗
        memRegion (fsp + 0x3de#64) 0xf2 := by
    rw [r1b_split_region fsp 0x2c0 0xf8 0x118,
      r1b_split_region fsp 0x3b8 7 0x111,
      r1b_split_region fsp 0x3bf 0x19 0xf8,
      r1b_split_region fsp 0x3d8 4 0xf4,
      r1b_split_region fsp 0x3dc 2 0xf2]
  rw [hlow, hmid, hhi,
    ProofLib.memRegion_four (fsp + 0x0e0#64),
    ProofLib.memRegion_four (fsp + 0x0e4#64),
    ProofLib.memRegion_eight (fsp + 0x0e8#64),
    ProofLib.memRegion_eight (fsp + 0x220#64),
    ProofLib.memRegion_one (fsp + 0x228#64),
    ProofLib.memRegion_four (fsp + 0x3d8#64),
    ProofLib.memRegion_two (fsp + 0x3dc#64)]
  refine Entails.trans
    (r1b_entails_frame (by r1b_ac) (r1b_memRegion7_to_head7 (fsp + 0x3b8#64)) (by r1b_ac)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun w13 =>
    Entails.sepExists_elim fun w9 =>
    Entails.sepExists_elim fun b31 =>
    Entails.sepExists_elim fun w23 =>
    Entails.sepExists_elim fun w15 =>
    Entails.sepExists_elim fun w0e4 =>
    Entails.sepExists_elim fun w0e0 =>
    Entails.sepExists_elim fun b0 =>
    Entails.sepExists_elim fun b1 =>
    Entails.sepExists_elim fun b2 =>
    Entails.sepExists_elim fun b3 =>
    Entails.sepExists_elim fun b4 =>
    Entails.sepExists_elim fun b5 =>
    Entails.sepExists_elim fun b6 => ?_
  refine Entails.sepExists_right b0 (Entails.sepExists_right b1
    (Entails.sepExists_right b2 (Entails.sepExists_right b3
    (Entails.sepExists_right b4 (Entails.sepExists_right b5
    (Entails.sepExists_right b6 (Entails.sepExists_right w0e0
    (Entails.sepExists_right w0e4 (Entails.sepExists_right w9
    (Entails.sepExists_right w13 (Entails.sepExists_right w15
    (Entails.sepExists_right w23 (Entails.sepExists_right b31 ?_)))))))))))))
  dsimp only [r1b_opkStage1At]
  exact Entails.of_eq (by r1b_ac)

theorem r1b_opkStage1_to_regions (fsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ⊢
      memRegion fsp 0x110 ∗
        memRegion (fsp + 0x1d0#64) 0x90 ∗
        memRegion (fsp + 0x2c0#64) 0x210 := by
  dsimp only [r1b_opkStage1At]
  have hlow : memRegion fsp 0x110 =
      memRegion fsp 0x0e0 ∗
        memRegion (fsp + 0x0e0#64) 4 ∗ memRegion (fsp + 0x0e4#64) 4 ∗
        memRegion (fsp + 0x0e8#64) 8 ∗ memRegion (fsp + 0x0f0#64) 0x20 := by
    rw [ProofLib.memRegion_split fsp 0x0e0 0x30 (by decide),
      r1b_split_region fsp 0x0e0 4 0x2c,
      r1b_split_region fsp 0x0e4 4 0x28,
      r1b_split_region fsp 0x0e8 8 0x20]
  have hmid : memRegion (fsp + 0x1d0#64) 0x90 =
      memRegion (fsp + 0x1d0#64) 0x50 ∗
        memRegion (fsp + 0x220#64) 8 ∗ memRegion (fsp + 0x228#64) 1 ∗
        memRegion (fsp + 0x229#64) 0x37 := by
    rw [r1b_split_region fsp 0x1d0 0x50 0x40,
      r1b_split_region fsp 0x220 8 0x38,
      r1b_split_region fsp 0x228 1 0x37]
  have hhi : memRegion (fsp + 0x2c0#64) 0x210 =
      memRegion (fsp + 0x2c0#64) 0xf8 ∗
        memRegion (fsp + 0x3b8#64) 7 ∗ memRegion (fsp + 0x3bf#64) 0x19 ∗
        memRegion (fsp + 0x3d8#64) 4 ∗ memRegion (fsp + 0x3dc#64) 2 ∗
        memRegion (fsp + 0x3de#64) 0xf2 := by
    rw [r1b_split_region fsp 0x2c0 0xf8 0x118,
      r1b_split_region fsp 0x3b8 7 0x111,
      r1b_split_region fsp 0x3bf 0x19 0xf8,
      r1b_split_region fsp 0x3d8 4 0xf4,
      r1b_split_region fsp 0x3dc 2 0xf2]
  have h1 :
      memRegion fsp 0x0e0 ∗
        ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗ ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
        ((fsp + 0x0e8#64) ↦₆₄ w15) ∗ memRegion (fsp + 0x0f0#64) 0x20 ⊢
        memRegion fsp 0x110 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _))) (by r1b_ac)) ?_
    rw [hlow]; exact Entails.of_eq (by r1b_ac)
  have h2 :
      memRegion (fsp + 0x1d0#64) 0x50 ∗
        ((fsp + 0x220#64) ↦₆₄ w23) ∗ ((fsp + 0x228#64) ↦₈ b31) ∗
        memRegion (fsp + 0x229#64) 0x37 ⊢
        memRegion (fsp + 0x1d0#64) 0x90 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (r1b_cell8_to_region _ _)) (by r1b_ac)) ?_
    rw [hmid]; exact Entails.of_eq (by r1b_ac)
  have h3 :
      memRegion (fsp + 0x2c0#64) 0xf8 ∗
        Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
        memRegion (fsp + 0x3bf#64) 0x19 ∗
        ((fsp + 0x3d8#64) ↦₃₂ w9) ∗ ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
        memRegion (fsp + 0x3de#64) 0xf2 ⊢
        memRegion (fsp + 0x2c0#64) 0x210 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (r1b_head7_to_region _ _ _ _ _ _ _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (pointsTo16_entails_memRegion _ _))) (by r1b_ac)) ?_
    rw [hhi]; exact Entails.of_eq (by r1b_ac)
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono h1 (sepConj_mono h2 h3)) (by r1b_ac)

/-! ## Error Exits (`0x1b98 → 0x2adc`, `0x2420 → 0x2aa8`) -/

theorem r1b_err_1b98 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr kpkCap kpkPtr spkCap spkPtr regCap regPtr v158 v188_in : BitVec 64}
    {eBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x1b98)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx1 : s.readReg64 .x1 = eCap)
    (hx14 : s.readReg64 (.gpr 14#5) = ePtr)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 eBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx12; let _ := hx1; let _ := hx14; let _ := hx25; let _ := hx26
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hsplit16 := r1b_region16_to_cells (fsp + 0x4f0#64)
  have h4f8 : (fsp + 0x4f0#64) + 8#64 = fsp + 0x4f8#64 := by bv_omega
  rw [h4f8] at hsplit16
  rw [hsplit16]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecOpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x1b98 0x44
  have hpc_in := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2adc#64) hst.inv
  have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2adc := hc.of_step
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hst.run]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hst.fp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
      spAligned := hst.spAligned }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  have h150 : ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ⊢
      memRegion (fsp + 0x150#64) 16 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cells2_to_region16 (fsp + 0x150#64) kpkCap v158
  have h4d0 :
      ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord 1) eCap ePtr
        (BitVec.ofNat 64 eBs.length) w4 w5
  have hpay : ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
      r1b_SpePayload A (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (BitVec.ofNat 64 eBs.length) := by
    simp only [hsm, arm64_norm]
    try rw [hx12]
    try rw [hx1]
    try rw [hx14]
    try rw [hx25]
    refine r1b_SpePayload_str A ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
  try rw [hx25]
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2adc (v188 := BitVec.ofNat 64 eBs.length)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
      hh hdrop hbnd hc_m
      (by simp [hsm, arm64_norm])
      (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx26)
      hpanic hrej)
  exact r1b_entails_frame (by r1b_ac)
    (sepConj_mono hpay (sepConj_mono h150 h4d0)) (by r1b_ac)

theorem r1b_err_2420 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr
      v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {eBs opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x2420)
    (hx8 : s.readReg64 .x8 = speWord 1)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
        ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗
        ((fsp + 0x11c#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0))
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx8
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal4 : (fsp + 0x4dc#64) &&& 3#64 = 0#64 := by bv_bits
  have hsplit16 := r1b_region16_to_cells (fsp + 0x4f0#64)
  have h4f8 : (fsp + 0x4f0#64) + 8#64 = fsp + 0x4f8#64 := by bv_omega
  rw [h4f8] at hsplit16
  rw [hsplit16]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecOpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2420 0x40
  have hpc_in := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2aa8#64) hst.inv
  have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm hsm hinv_m => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2aa8 := hc.of_step
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
      run := by simp [hsm, arm64_norm, hst.run]
      sp := by simpa [hsm, arm64_norm] using hst.sp
      fp := by simpa [hsm, arm64_norm] using hst.fp
      inv := hinv_m
      vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
      spAligned := hst.spAligned }
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
  have htr32 : ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32 = eCap.extractLsb' 0 32 := by
    bv_bits
  have h4d8 :
      ((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
        ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) =
        ((fsp + 0x4d8#64) ↦₆₄ eCap) := by
    rw [htr32]
    have hp := pointsTo64_split32 (fsp + 0x4d8#64) eCap
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hp.symm
  have h4d0 :
      ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
        ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
    have h4d0_eq :
        ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
          ((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
          ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) ∗
          ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
          ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) =
        ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
          (((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
            ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32)) ∗
          ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
          ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) := by r1b_ac
    rw [h4d0_eq, h4d8]
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord 1) eCap ePtr
        (BitVec.ofNat 64 eBs.length) w4 w5
  have hpay : ownedBytes A eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
      r1b_SpePayload A (speWord 1)
        ((((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32).zeroExtend 64)
        ((eCap.extractLsb' 32 32).zeroExtend 64)
        (sm.readReg64 (.gpr 27#5))
        (ePtr >>> 56)
        (sm.readReg64 (.gpr 24#5))
        (sm.readReg64 (.gpr 23#5))
        (sm.readReg64 (.gpr 28#5))
        (BitVec.ofNat 64 eBs.length) := by
    simp only [hsm, arm64_norm]
    refine r1b_SpePayload_str A ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
  try rw [hx8]
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_cleanup_2aa8
      (v11c := ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32)
      (v158 := speWord 1)
      (v188 := BitVec.ofNat 64 eBs.length)
      (v190 := ePtr >>> 56)
      (v1a8 := w5)
      (v1b0 := (eCap.extractLsb' 32 32).zeroExtend 64)
      (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := BitVec.ofNat 64 opkBs.length) (opkBs := opkBs)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej)
  exact r1b_entails_frame (by r1b_ac)
    (sepConj_mono hpay h4d0) (by r1b_ac)

/-! ## Shared Free Merge (`0x24dc → 0x24ec`) and Unaligned Stack Copy (`0x2490 → 0x24dc`) -/

theorem r1b_opk_free_24dc {S : RunSem} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {opkBs kpkBs kpkKey kpkSig spkBs spkKey spkSig : List (BitVec 8)}
    {kpkId spkId v11c : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtx S img ext g d s0 s 0x24dc)
    (hx1 : s.readReg64 .x1 = opkCap)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp)
    (hk : ∀ sf : State,
      r1b_OkCtx S img ext g d s0 sf 0x24ec →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
          memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
          memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
          ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (ownedBytes A opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase A img g d s0 ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
        ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
        ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
        ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
        ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  let _ := hx1; let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  by_cases hcap : opkCap = 0#64
  · subst hcap
    code_fetches_range CryptoVerification.libsignalSessionCode r1bDecOpk img.base
      (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x24dc 4
    have hpc_in := hst.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
    generalize_entry heq_fnBase :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
    examples_hide_fetches
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x24ec#64) hst.inv
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hok_m : r1b_OkCtx S img ext g d s0 sm 0x24ec := hok.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h120 : ((fsp + 0x120#64) ↦₆₄ opkPtr) ⊢ memRegion (fsp + 0x120#64) 8 :=
      pointsTo64_entails_memRegion _ _
    have hcap0 := r1b_ownedBytes_cap0_emp A opkPtr (BitVec.ofNat 64 opkBs.length) opkBs
    refine r1b_sepWPp_frame (by r1b_ac) hcap0 (by r1b_ac) ?_
    exact MainHops.sepWPp_weaken_pre
      (r1b_entails_frame (by r1b_ac) h120 (by r1b_ac))
      (hk sm hok_m
        (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx23)
        (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx24)
        (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx25)
        (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx27)
        (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx28))
  · have hbeq : (opkCap == 0#64) = false := beq_false_of_ne hcap
    code_fetches_range CryptoVerification.libsignalSessionCode r1bDecOpk img.base
      (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x24dc 0x10
    have hpc_in := hst.pc
    dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
    generalize_entry heq_fnBase :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
    examples_hide_fetches
    apply MainHops.sepWPp_seq_inImage
      (mid := fnBase + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli::run")) hst.inv
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    refine r1b_call_frame <|
      r1b_call_dealloc_ownedBytes (cap := opkCap) (ptr := opkPtr)
        (len := BitVec.ofNat 64 opkBs.length) (bs := opkBs) hh hbnd hinv_m
        (by dsimp only [mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm, hst.run])
        (by simpa [hsm, arm64_norm] using hst.sp)
        (by simpa [hsm, arm64_norm] using hst.fp)
        (by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x24ec)
        (by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm])
        (by simp [hsm, arm64_norm])
        (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx1)
        (by simp [hsm, arm64_norm])
        hcap hpanic fun sf hin_f hcs_f hfs_f htr_f => ?_
    have hok_f : r1b_OkCtx S img ext g d s0 sf 0x24ec := hok.after_call
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      hin_f hcs_f (congrArg FsState.files hfs_f) htr_f
    have h120 : ((fsp + 0x120#64) ↦₆₄ opkPtr) ⊢ memRegion (fsp + 0x120#64) 8 :=
      pointsTo64_entails_memRegion _ _
    exact MainHops.sepWPp_weaken_pre
      (r1b_entails_frame (by r1b_ac) h120 (by r1b_ac))
      (hk sf hok_f
        (hcs_f.2.2.2.2.1.trans (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx23))
        (hcs_f.2.2.2.2.2.1.trans (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx24))
        (hcs_f.2.2.2.2.2.2.1.trans (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx25))
        (hcs_f.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx27))
        (hcs_f.2.2.2.2.2.2.2.2.2.1.trans (by solve | simp [hsm, arm64_norm] | simpa [hsm, arm64_norm] using hx28)))

private theorem r1b_pk4d0_ok_to_region48 (fsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    ((fsp + 0x4d0#64) ↦₈ 0#8) ∗
      Wire.pkLayoutAt (fsp + 0x4d1#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (fsp + 0x4f1#64) 15 ⊢
      memRegion (fsp + 0x4d0#64) 48 := by
  refine Entails.trans (sepConj_mono (r1b_cell8_to_region _ _)
    (sepConj_mono_left (Wire.pkLayoutAt_entails_memRegion32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))) ?_
  rw [r1b_join_region fsp 0x4d1 32 15, r1b_join_region fsp 0x4d0 1 47]
  exact Entails.refl _

theorem r1b_opk_deser_err_1360 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {opkBs opkKey kpkBs spkBs regBs : List (BitVec 8)}
    {e : SignalProtocolError}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext) (hdrop : RunDrop.DropSpeOwnedOk img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtx img ext g d s0 s 0x1360)
    (_hd : PublicKey.deserialize opkKey = .error e)
    (hpanic : PanicK g s0 Qp) (hrej : RejectK img ext A g s0 resStack Q Qp) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (Wire.deserializeResult33At (fsp + 0x4d0#64) (.error e) ∗
        memRegion (fsp + 0x4f1#64) 15 ∗
        ownedBytes A opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon A g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp (runOom s0) := by
  intro fsp
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecOpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x1360 0x24
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecOpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x26a8 0x24
  have hpc_in := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  cases e with
  | noKeyTypeIdentifier =>
    dsimp only [Wire.deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2a88#64) hst.inv
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2a88 := hc.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
          ((fsp + 0x4d8#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x4d9#64) 24 ∗
          memRegion (fsp + 0x4f1#64) 15 ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
      have h33 := Wire.memRegion33_of_err_base (fsp + 0x4d0#64) 0#8
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h33
      refine Entails.trans (r1b_entails_frame (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_cleanup_2a88 (i := 7)
        (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := BitVec.ofNat 64 opkBs.length) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide)
        (by simp [hsm, arm64_norm, speWord]) hpanic hrej)
    exact r1b_entails_frame (by r1b_ac) h4d0 (by r1b_ac)
  | badKeyType t =>
    dsimp only [Wire.deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2a60#64) hst.inv
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2a60 := hc.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
          ((fsp + 0x4d8#64) ↦₈ 1#8) ∗ ((fsp + 0x4d9#64) ↦₈ t) ∗
          memRegion (fsp + 0x4da#64) 23 ∗ memRegion (fsp + 0x4f1#64) 15 ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
      have h33 := Wire.memRegion33_of_err_badKeyType (fsp + 0x4d0#64) t
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h33
      refine Entails.trans (r1b_entails_frame (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_cleanup_2a60
        (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := BitVec.ofNat 64 opkBs.length) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
        hh hdrop hbnd hc_m hpanic hrej)
    exact r1b_entails_frame (by r1b_ac) h4d0 (by r1b_ac)
  | badKeyLength n =>
    dsimp only [Wire.deserializeResult33At]
    rw [ProofLib.memRegion_eight (fsp + 0x158#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc,
      BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun v158 => ?_
    apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x2a8c#64) hst.inv
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine r1b_bind_state fun sm hsm hinv_m => ?_
    change SepWPp (mProg img ext) _ _ _ _ _ _
    have hc_m : r1b_ErrCtx img ext g d s0 sm 0x2a8c := hc.of_step
      { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm, arm64_norm]
        run := by simp [hsm, arm64_norm, hst.run]
        sp := by simpa [hsm, arm64_norm] using hst.sp
        fp := by simpa [hsm, arm64_norm] using hst.fp
        inv := hinv_m
        vregs := by simpa [calleeSavedVRegs, hsm, arm64_norm] using hst.vregs
        spAligned := hst.spAligned }
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
      (by simp [hsm, arm64_norm]) (by simp [hsm, arm64_norm])
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
          ((fsp + 0x4d8#64) ↦₈ 2#8) ∗ memRegion (fsp + 0x4d9#64) 7 ∗
          ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (fsp + 0x4e8#64) 9 ∗
          memRegion (fsp + 0x4f1#64) 15 ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
      have h33 := Wire.memRegion33_of_err_badKeyLength (fsp + 0x4d0#64) n
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h33
      refine Entails.trans (r1b_entails_frame (by r1b_ac) h33 (by r1b_ac)) ?_
      rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
    have h158_eq : ((fsp + 0x158#64) ↦₆₄ 0x8000000000000009#64) =
        ((fsp + 0x158#64) ↦₆₄ speWord 9) := rfl
    rw [h158_eq]
    refine MainHops.sepWPp_weaken_pre ?_
      (r1b_cleanup_2a8c (i := 9)
        (opkCap := opkCap) (opkPtr := opkPtr) (opkLen := BitVec.ofNat 64 opkBs.length) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide) hpanic hrej)
    exact r1b_entails_frame (by r1b_ac) h4d0 (by r1b_ac)
  | _ =>
    dsimp only [Wire.deserializeResult33At]
    exact SepWPp.pure_elim False.elim

set_option maxHeartbeats 400000 in
theorem r1b_opk_copy1_2490 {S : RunSem} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {opkBs kpkBs kpkKey kpkSig spkBs spkKey spkSig : List (BitVec 8)}
    {kpkId spkId opkId : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {c0 c1 c2 c3 c4 c5 c6 : BitVec 8}
    {w0e0_in w0e4_in w9_in : BitVec 32} {w13_in : BitVec 16} {w15_in w23_in : BitVec 64}
    {b31_in : BitVec 8}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A ext)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtx S img ext g d s0 s 0x2490)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp)
    (hk : ∀ sf : State,
      r1b_OkCtx S img ext g d s0 sf 0x24ec →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (mProg img ext) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase A img g d s0 ∗ logOff img ∗
          ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6
            (b8.zeroExtend 32) (b7.zeroExtend 32) w9 w13 w15 w23 b31 ∗
          memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ opkId) ∗
          memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
          ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool)
        Q Qp (runOom s0)) :
    let fsp := runFsp s0
    SepWPp (mProg img ext) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₈ 0#8) ∗
        Wire.pkLayoutAt (fsp + 0x4d1#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
        memRegion (fsp + 0x4f1#64) 15 ∗
        ownedBytes A opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        ownedBytes A kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase A img g d s0 ∗ logOff img ∗
        ownedBytes A d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1At fsp c0 c1 c2 c3 c4 c5 c6
          w0e0_in w0e4_in w9_in w13_in w15_in w23_in b31_in ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ ((fsp + 0x11c#64) ↦₃₂ opkId) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
        ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
        ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
        ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
        ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool)
      Q Qp (runOom s0) := by
  intro fsp
  change s.readReg64 (.gpr 24#5) = fsp + 0x380#64 at hx24
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hs_run : s.status = .Running := hst.run
  have hs_sp : s.sp = fsp := hst.sp
  let _ := hs_run; let _ := hs_sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal4d4 : (fsp + 0x4d4#64) &&& 3#64 = 0#64 := by bv_bits
  have hal4da : (fsp + 0x4da#64) &&& 1#64 = 0#64 := by bv_bits
  have hal4de : (fsp + 0x4de#64) &&& 1#64 = 0#64 := by bv_bits
  have hal4e8 : (fsp + 0x4e8#64) &&& 7#64 = 0#64 := by bv_bits
  have hal3b8 : (fsp + 0x3b8#64) &&& 3#64 = 0#64 := by bv_bits
  have hal3d8 : (fsp + 0x3d8#64) &&& 3#64 = 0#64 := by bv_bits
  have hal3dc : (fsp + 0x3dc#64) &&& 1#64 = 0#64 := by bv_bits
  have hal0e4 : (fsp + 0x0e4#64) &&& 3#64 = 0#64 := by bv_bits
  have hal0e8 : (fsp + 0x0e8#64) &&& 7#64 = 0#64 := by bv_bits
  code_fetches_range CryptoVerification.libsignalSessionCode r1bDecOpk img.base
    (Rust.withPanics ext) r1b_run_fnOff (num% (ls_off% "libsignal_cli::run")) 0x2490 0x4c
  have hpc_in := hst.pc
  dsimp only [runPc, mProg, tripleRatchetProgAtExt] at hpc_in ⊢
  generalize_entry heq_fnBase :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr runName = fnBase
  examples_hide_fetches
  dsimp only [Wire.pkLayoutAt, Wire.pkRestAt, r1b_opkStage1At]
  rw [Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x4d1#64)]
  dsimp only [Wire.sevenBytesTailAt, Wire.sevenBytesHeadAt]
  try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
  try rw [← BitVec.add_assoc kpkPtr 4#64]; try rw [← BitVec.add_assoc spkPtr 4#64]
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x249c#64) hst.inv
  have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm1 hsm1 hinv1 => ?_
  clear hpc hrun hsp
  have hflip4d1 :
      ((fsp + 0x4d1#64) ↦₈ b0) ∗ ((fsp + 0x4d2#64) ↦₈ b1) ∗
        ((fsp + 0x4d3#64) ↦₈ b2) ∗ ((fsp + 0x4d4#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
      ((fsp + 0x4d1#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((fsp + 0x4d5#64) ↦₈ b4) ∗ ((fsp + 0x4d6#64) ↦₈ b5) ∗
        ((fsp + 0x4d7#64) ↦₈ b6) := by
    have heq := (Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x4d1#64) b0 b1 b2 b3 b4 b5 b6).symm
    dsimp only [Wire.sevenBytesHeadAt, Wire.sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at heq
    rw [heq]; exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) hflip4d1 (by r1b_ac) ?_
  try simp only [sepConj_assoc]
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x24b8#64) hinv1
  have hpc : sm1.pc = fnBase + 0x249c#64 := by simp [hsm1, arm64_norm]
  have hrun : sm1.status = .Running := by simp [hsm1, arm64_norm, hst.run]
  have hsp : sm1.sp = fsp := by simpa [hsm1, arm64_norm] using hst.sp
  have hx10_1 : sm1.readReg64 (.gpr 10#5) = fsp + 0x4d0#64 := by
    solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using congrArg (· + 0x4d0#64) hst.sp
  have hx24_1 : sm1.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
    solve | simp [hsm1, arm64_norm] | simpa [hsm1, arm64_norm] using hx24
  let _ := hx10_1; let _ := hx24_1
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm2 hsm2 hinv2 => ?_
  clear hpc hrun hsp
  have hflip3b8_in :
      ((fsp + 0x3b8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((fsp + 0x3bc#64) ↦₈ c4) ∗ ((fsp + 0x3bd#64) ↦₈ c5) ∗
        ((fsp + 0x3be#64) ↦₈ c6) ⊢
      ((fsp + 0x3b8#64) ↦₈ b0) ∗ ((fsp + 0x3b9#64) ↦₈ b1) ∗
        ((fsp + 0x3ba#64) ↦₈ b2) ∗ ((fsp + 0x3bb#64) ↦₃₂ (c6 ++ c5 ++ c4 ++ b3)) := by
    have heq := Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x3b8#64) b0 b1 b2 b3 c4 c5 c6
    dsimp only [Wire.sevenBytesHeadAt, Wire.sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at heq
    rw [heq]; exact Entails.refl _
  refine r1b_sepWPp_frame (by r1b_ac) hflip3b8_in (by r1b_ac) ?_
  try simp only [sepConj_assoc]
  apply MainHops.sepWPp_seq_inImage (mid := fnBase + 0x24dc#64) hinv2
  have hpc : sm2.pc = fnBase + 0x24b8#64 := by simp [hsm2, arm64_norm]
  have hrun : sm2.status = .Running := by simp [hsm2, hsm1, arm64_norm, hst.run]
  have hsp : sm2.sp = fsp := by simpa [hsm2, hsm1, arm64_norm] using hst.sp
  have hx24_2 : sm2.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
    solve | simp [hsm2, hsm1, arm64_norm] | simpa [hsm2, hsm1, arm64_norm] using hx24
  have hx9_2 : sm2.readReg64 (.gpr 9#5) = (b6 ++ b5 ++ b4 ++ b3).zeroExtend 64 := by
    simp [hsm2, hsm1, arm64_norm]
  let _ := hx24_2; let _ := hx9_2
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
  refine r1b_bind_state fun sm3 hsm3 hinv3 => ?_
  change SepWPp (mProg img ext) _ _ _ _ _ _
  have hok3 : r1b_OkCtx S img ext g d s0 sm3 0x24dc := hok.of_step
    { pc := by dsimp only [runPc, mProg, tripleRatchetProgAtExt]; rw [heq_fnBase]; simp [hsm3, arm64_norm]
      run := by simp [hsm3, hsm2, hsm1, arm64_norm, hst.run]
      sp := by simpa [hsm3, hsm2, hsm1, arm64_norm] using hst.sp
      fp := by simpa [hsm3, hsm2, hsm1, arm64_norm] using hst.fp
      inv := hinv3
      vregs := by simpa [calleeSavedVRegs, hsm3, hsm2, hsm1, arm64_norm] using hst.vregs
      spAligned := hst.spAligned }
    (by simp [hsm3, hsm2, hsm1, arm64_norm]) (by simp [hsm3, hsm2, hsm1, arm64_norm])
    (by simp [hsm3, hsm2, hsm1, arm64_norm]) (by simp [hsm3, hsm2, hsm1, arm64_norm])
    (by simp [hsm3, hsm2, hsm1, arm64_norm]) (by simp [hsm3, hsm2, hsm1, arm64_norm])
  have hw3bb : ((((b6 ++ b5 ++ b4 ++ b3).zeroExtend 64).truncate 32) : BitVec 32) =
      (b6 ++ b5 ++ b4 ++ b3) := by bv_bits
  have hw3d8 : ((w9.zeroExtend 64).truncate 32 : BitVec 32) = w9 := by bv_bits
  have hw3dc : (((w13.zeroExtend 32).zeroExtend 64).truncate 16 : BitVec 16) = w13 := by bv_bits
  have hw228 : (((b31.zeroExtend 32).zeroExtend 64).truncate 8 : BitVec 8) = b31 := by bv_bits
  have hw0e0 : (((b8.zeroExtend 32).zeroExtend 64).truncate 32 : BitVec 32) =
      b8.zeroExtend 32 := by bv_bits
  have hw0e4 : (((b7.zeroExtend 32).zeroExtend 64).truncate 32 : BitVec 32) =
      b7.zeroExtend 32 := by bv_bits
  set_option linter.unusedSimpArgs false in
  simp only [hsm1, hsm2, arm64_norm, hw3bb, hw3d8, hw3dc, hw228, hw0e0, hw0e4]
  try rw [← BitVec.add_assoc kpkPtr 4#64]; try rw [← BitVec.add_assoc spkPtr 4#64]
  have hflip3b8_out :
      ((fsp + 0x3b8#64) ↦₈ b0) ∗ ((fsp + 0x3b9#64) ↦₈ b1) ∗
        ((fsp + 0x3ba#64) ↦₈ b2) ∗ ((fsp + 0x3bb#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
      Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 := by
    have heq := (Wire.sevenBytesHeadAt_eq_tailAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6).symm
    dsimp only [Wire.sevenBytesTailAt] at heq
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at heq
    rw [heq]; exact Entails.refl _
  have h4d0_48 :
      ((fsp + 0x4d0#64) ↦₈ 0#8) ∗
        ((fsp + 0x4d1#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((fsp + 0x4d5#64) ↦₈ b4) ∗ ((fsp + 0x4d6#64) ↦₈ b5) ∗
        ((fsp + 0x4d7#64) ↦₈ b6) ∗ ((fsp + 0x4d8#64) ↦₈ b7) ∗
        ((fsp + 0x4d9#64) ↦₈ b8) ∗ ((fsp + 0x4da#64) ↦₃₂ w9) ∗
        ((fsp + 0x4de#64) ↦₁₆ w13) ∗ ((fsp + 0x4e0#64) ↦₆₄ w15) ∗
        ((fsp + 0x4e8#64) ↦₆₄ w23) ∗ ((fsp + 0x4f0#64) ↦₈ b31) ∗
        memRegion (fsp + 0x4f1#64) 15 ⊢
        memRegion (fsp + 0x4d0#64) 48 := by
    have h48 := r1b_pk4d0_ok_to_region48 fsp b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
    dsimp only [Wire.pkLayoutAt, Wire.sevenBytesHeadAt, Wire.pkRestAt] at h48
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h48
  have h110 : ((fsp + 0x110#64) ↦₆₄ opkCap) ⊢ memRegion (fsp + 0x110#64) 8 :=
    pointsTo64_entails_memRegion _ _
  have hx24_run : sm3.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 := by
    change sm3.readReg64 (.gpr 24#5) = fsp + 0x380#64
    simpa [hsm3, hsm2, hsm1, arm64_norm] using hx24
  refine MainHops.sepWPp_weaken_pre ?_
    (r1b_opk_free_24dc (opkCap := opkCap) (opkPtr := opkPtr) (opkBs := opkBs)
      (kpkKey := kpkKey) (kpkSig := kpkSig) (spkKey := spkKey) (spkSig := spkSig)
      hh hbnd hok3
      (by simp [hsm3, hsm2, arm64_norm])
      (by solve | simp [hsm3, hsm2, hsm1, arm64_norm] | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx23)
      hx24_run
      (by solve | simp [hsm3, hsm2, hsm1, arm64_norm] | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx25)
      (by solve | simp [hsm3, hsm2, hsm1, arm64_norm] | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx27)
      (by solve | simp [hsm3, hsm2, hsm1, arm64_norm] | simpa [hsm3, hsm2, hsm1, arm64_norm] using hx28)
      hpanic hk)
  dsimp only [r1b_opkStage1At]
  exact r1b_entails_frame (by r1b_ac)
    (sepConj_mono hflip3b8_out (sepConj_mono h4d0_48 h110)) (by r1b_ac)


end CryptoVerification.SignalSession.Cli.RunCompose
