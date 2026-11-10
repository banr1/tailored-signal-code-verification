/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 1 Segment 1 (`0x0000 → 0x0154`): Prologue and `is_trusted_identity`

Steps through `signal_session_handshake::initiate`'s prologue, invokes `idTrustShim`, `idTrustPoll`,
`futDrop`, and `__rust_dealloc(32, 8)`, discharges the untrusted-identity `Err` exit at `0x0244`,
and establishes `stage2Mem` at `0x0154` on the `Ok(true)` branch.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open Stage1Norm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

theorem prologue_low_d0_merge_sp (sp : BitVec 64) :
    (∃∗ l0 : BitVec 64, (sp - 7408#64) ↦₆₄ l0) ∗ memRegion (sp - 7400#64) 120 ∗
      (∃∗ l80 : BitVec 64, (sp - 7280#64) ↦₆₄ l80) ∗
      (∃∗ l88 : BitVec 32, (sp - 7272#64) ↦₃₂ l88) ∗ memRegion (sp - 7268#64) 4 ∗
      (∃∗ l90 : BitVec 64, (sp - 7264#64) ↦₆₄ l90) ∗
      (∃∗ l98 : BitVec 64, (sp - 7256#64) ↦₆₄ l98) ∗
      (∃∗ la0 : BitVec 64, (sp - 7248#64) ↦₆₄ la0) ∗
      (∃∗ la8 : BitVec 64, (sp - 7240#64) ↦₆₄ la8) ∗
      (∃∗ lb0 : BitVec 64, (sp - 7232#64) ↦₆₄ lb0) ∗
      (∃∗ lb8 : BitVec 64, (sp - 7224#64) ↦₆₄ lb8) ∗
      (∃∗ lc0 : BitVec 64, (sp - 7216#64) ↦₆₄ lc0) ∗
      (∃∗ lc8 : BitVec 64, (sp - 7208#64) ↦₆₄ lc8) ⊢
      memRegion (sp - 7408#64) 208 := by
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro lc8
  apply Entails.sepExists_elim; intro lc0
  apply Entails.sepExists_elim; intro lb8
  apply Entails.sepExists_elim; intro lb0
  apply Entails.sepExists_elim; intro la8
  apply Entails.sepExists_elim; intro la0
  apply Entails.sepExists_elim; intro l98
  apply Entails.sepExists_elim; intro l90
  apply Entails.sepExists_elim; intro l88
  apply Entails.sepExists_elim; intro l80
  apply Entails.sepExists_elim; intro l0
  simpa (disch := decide) only
    [cliInitiateFrame, BitVec.add_zero, bv_sub_add_lit, Nat.reduceAdd, Nat.reduceSub,
      BitVec.ofNat_eq_ofNat] using
    prologue_low_d0_merge (sp - BitVec.ofNat 64 cliInitiateFrame)
      l0 l80 l88 l90 l98 la0 la8 lb0 lb8 lc0 lc8

theorem prologue_high_5ba_merge_sp (sp : BitVec 64) :
    memRegion (sp - 5942#64) 30 ∗
      (∃∗ wk0 : BitVec 64, (sp - 5912#64) ↦₆₄ wk0) ∗
      (∃∗ wk1 : BitVec 64, (sp - 5904#64) ↦₆₄ wk1) ∗
      (∃∗ wk2 : BitVec 64, (sp - 5896#64) ↦₆₄ wk2) ∗
      memRegion (sp - 5888#64) 1696 ∗
      (∃∗ probe : BitVec 64, (sp - 4192#64) ↦₆₄ probe) ∗
      memRegion (sp - 4184#64) 4088 ⊢
      memRegion (sp - 5942#64) 5846 := by
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro probe
  apply Entails.sepExists_elim; intro wk2
  apply Entails.sepExists_elim; intro wk1
  apply Entails.sepExists_elim; intro wk0
  simpa (disch := decide) only
    [cliInitiateFrame, initLocalsSize, BitVec.add_zero, bv_sub_add_lit, Nat.reduceAdd,
      Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
    prologue_high_5ba_merge (sp - BitVec.ofNat 64 cliInitiateFrame) wk0 wk1 wk2 probe

/-- Spatial entry footprint of `initSlotSpec` after extracting pure preconditions. -/
abbrev initEntryMem' (A : RustAlloc) (img : Obj.Image) (x : InitGhost) (stk : Nat)
    (s0 : State) : SepProp :=
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    coinsInstalled img x.coinsP x.coins ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    logOff img ∗ A.pool ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s0.sp stk

/-- Spatial state at `0x009c` after `idTrustShim` returns. -/
abbrev afterTrustShimMem (A : RustAlloc) (img : Obj.Image) (x : InitGhost) (stk : Nat)
    (s0 sAfterShim : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    A.live (sAfterShim.readReg64 .x0) 32 8 ∗
    idTrustBoxAt (sAfterShim.readReg64 .x0) x.stores x.peerA (x.bundleA + 120#64) 0#8 0#8 ∗
    A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗
    storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    coinsCursorAt img x.coinsP x.coins 0 ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    logOff img ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
    memRegion (fsp + 0x128#64) 0x490 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)

set_option maxHeartbeats 1600000 in
/-- Prologue and `is_trusted_identity` shim call (`0x0000 → 0x009c`, `initProgExt`). -/
theorem stage1_prologue_to_shim_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryExt img ext x s0)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAfterShim : State)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      InInitiateExt img ext s0 sAfterShim 0x009c →
      sAfterShim.trace = s0.trace →
      sAfterShim.readReg64 (.gpr 1#5) = img.base + idTrustFutVtOff →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sAfterShim
        (afterTrustShimMem A img x stk s0 sAfterShim) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s0
      (initEntryMem' A img x stk s0) Q Qp (initOom s0) := by
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage1Bin img.base
    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x0000 0x009c
  have hpc0 := hs0.pc; have hrun0 := hs0.run; have hal0 := hs0.spAligned
  have hx0 := hs0.x0; have hx1 := hs0.x1; have hx2 := hs0.x2; have hx3 := hs0.x3
  have hx4 := hs0.x4; have hx5 := hs0.x5; have hx6 := hs0.x6; have hx7 := hs0.x7
  have hx8 := hs0.x8; have hfs0 := hs0.files
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  dsimp only [initEntryMem']
  rw [coinsInstalled_eq_cursorZero,
    stackAt_entry_split s0 (stk_ge_frame hstk) hstk64]
  refine sepWPp_mono_pre (P' :=
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        memRegion (s0.sp - 0x60#64) 0x60 ∗
        memRegion fsp initLocalsSize ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        logOff img ∗ A.pool ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        stackAt fsp (stk - cliInitiateFrame))
    (by sep_frame) ?_
  rw [cliBundleAt_unpack]
  refine sepWPp_exists_left fun opkId => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨h1, h2, h3, hopk⟩ => ?_
  rw [memRegion_saved_split (s0.sp - 0x60#64)]
  refine sepWPp_exists_pos2 fun w11 => ?_; refine sepWPp_exists_pos2 fun w10 => ?_
  refine sepWPp_exists_pos2 fun w9 => ?_; refine sepWPp_exists_pos2 fun w8 => ?_
  refine sepWPp_exists_pos2 fun w7 => ?_; refine sepWPp_exists_pos2 fun w6 => ?_
  refine sepWPp_exists_pos2 fun w5 => ?_; refine sepWPp_exists_pos2 fun w4 => ?_
  refine sepWPp_exists_pos2 fun w3 => ?_; refine sepWPp_exists_pos2 fun w2 => ?_
  refine sepWPp_exists_pos2 fun w1 => ?_; refine sepWPp_exists_pos2 fun w0 => ?_
  refine sepWPp_mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (prologue_locals_split fsp)))) ?_
  refine sepWPp_exists_pos3 fun l0 => ?_; refine sepWPp_exists_pos3 fun l80 => ?_
  refine sepWPp_exists_pos3 fun l88 => ?_; refine sepWPp_exists_pos3 fun l90 => ?_
  refine sepWPp_exists_pos3 fun l98 => ?_; refine sepWPp_exists_pos3 fun la0 => ?_
  refine sepWPp_exists_pos3 fun la8 => ?_; refine sepWPp_exists_pos3 fun lb0 => ?_
  refine sepWPp_exists_pos3 fun lb8 => ?_; refine sepWPp_exists_pos3 fun lc0 => ?_
  refine sepWPp_exists_pos3 fun lc8 => ?_
  refine sepWPp_exists_pos3 fun a0 => ?_; refine sepWPp_exists_pos3 fun a1 => ?_
  refine sepWPp_exists_pos3 fun a2 => ?_; refine sepWPp_exists_pos3 fun a3 => ?_
  refine sepWPp_exists_pos3 fun a4 => ?_; refine sepWPp_exists_pos3 fun a5 => ?_
  refine sepWPp_exists_pos3 fun a6 => ?_; refine sepWPp_exists_pos3 fun a7 => ?_
  refine sepWPp_exists_pos3 fun a8 => ?_; refine sepWPp_exists_pos3 fun a9 => ?_
  refine sepWPp_exists_pos3 fun a10 => ?_; refine sepWPp_exists_pos3 fun flag16 => ?_
  refine sepWPp_exists_pos3 fun wk0 => ?_; refine sepWPp_exists_pos3 fun wk1 => ?_
  refine sepWPp_exists_pos3 fun wk2 => ?_; refine sepWPp_exists_pos3 fun probe => ?_
  refine sepWPp_mono_pre (P' :=
      storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        logOff img ∗ A.pool ∗
        cliBundleBody x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗
        (fsp ↦₆₄ l0) ∗ memRegion (fsp + 0x08#64) 0x78 ∗
        ((fsp + 0x80#64) ↦₆₄ l80) ∗ ((fsp + 0x88#64) ↦₃₂ l88) ∗ memRegion (fsp + 0x8c#64) 4 ∗
        ((fsp + 0x90#64) ↦₆₄ l90) ∗ ((fsp + 0x98#64) ↦₆₄ l98) ∗
        ((fsp + 0xa0#64) ↦₆₄ la0) ∗ ((fsp + 0xa8#64) ↦₆₄ la8) ∗
        ((fsp + 0xb0#64) ↦₆₄ lb0) ∗ ((fsp + 0xb8#64) ↦₆₄ lb8) ∗
        ((fsp + 0xc0#64) ↦₆₄ lc0) ∗ ((fsp + 0xc8#64) ↦₆₄ lc8) ∗
        ((fsp + 0xd0#64) ↦₆₄ a0) ∗ ((fsp + 0xd8#64) ↦₆₄ a1) ∗
        ((fsp + 0xe0#64) ↦₆₄ a2) ∗ ((fsp + 0xe8#64) ↦₆₄ a3) ∗
        ((fsp + 0xf0#64) ↦₆₄ a4) ∗ ((fsp + 0xf8#64) ↦₆₄ a5) ∗
        ((fsp + 0x100#64) ↦₆₄ a6) ∗ ((fsp + 0x108#64) ↦₆₄ a7) ∗
        ((fsp + 0x110#64) ↦₃₂ a8) ∗ memRegion (fsp + 0x114#64) 4 ∗
        ((fsp + 0x118#64) ↦₆₄ a9) ∗ ((fsp + 0x120#64) ↦₆₄ a10) ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₁₆ flag16) ∗
        memRegion (fsp + 0x5ba#64) 30 ∗
        ((fsp + 0x5d8#64) ↦₆₄ wk0) ∗ ((fsp + 0x5e0#64) ↦₆₄ wk1) ∗ ((fsp + 0x5e8#64) ↦₆₄ wk2) ∗
        memRegion (fsp + 0x5f0#64) (0xc90 - 0x5f0) ∗
        ((fsp + 0xc90#64) ↦₆₄ probe) ∗
        memRegion (fsp + 0xc98#64) (initLocalsSize - 0xc98) ∗
        (((s0.sp - 0x60#64) + 0x00#64) ↦₆₄ w0) ∗ (((s0.sp - 0x60#64) + 0x08#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x60#64) + 0x10#64) ↦₆₄ w2) ∗ (((s0.sp - 0x60#64) + 0x18#64) ↦₆₄ w3) ∗
        (((s0.sp - 0x60#64) + 0x20#64) ↦₆₄ w4) ∗ (((s0.sp - 0x60#64) + 0x28#64) ↦₆₄ w5) ∗
        (((s0.sp - 0x60#64) + 0x30#64) ↦₆₄ w6) ∗ (((s0.sp - 0x60#64) + 0x38#64) ↦₆₄ w7) ∗
        (((s0.sp - 0x60#64) + 0x40#64) ↦₆₄ w8) ∗ (((s0.sp - 0x60#64) + 0x48#64) ↦₆₄ w9) ∗
        (((s0.sp - 0x60#64) + 0x50#64) ↦₆₄ w10) ∗ (((s0.sp - 0x60#64) + 0x58#64) ↦₆₄ w11))
    (by sep_frame) ?_
  simp (disch := decide) only
    [fsp, cliInitiateFrame, BitVec.add_zero, bv_sub_add_lit, Nat.reduceSub]
  have hent : initEntryExt img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc0 ⊢
  try simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hpc0
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  examples_hide_fetches
  refine sepWPp_with_rodata (rodata_idVt_trustSlot_ext (ext := ext) himg hs0.inv.1) ?_
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to
    ((libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr idTrustShimName)
    hs0.inv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sShim hsShim hpcS hrunS hinvS
  refine sepWPp_drop_left ?_
  have hspS : sShim.sp = fsp := by
    rw [← hsShim]; simp [wp_norm, arm64_norm, fsp, cliInitiateFrame]
  have hx0S : sShim.readReg64 .x0 = x.stores := by
    rw [← hsShim]; simp [wp_norm, arm64_norm]
  have hx1S : sShim.readReg64 .x1 = x.peerA := by
    rw [← hsShim]; simp [wp_norm, arm64_norm]
  have hx2S : sShim.readReg64 .x2 = x.bundleA + 120#64 := by
    rw [← hsShim]; simp [wp_norm, arm64_norm]
  have hx3S : (sShim.readReg64 .x3).setWidth 8 = 0#8 := by
    rw [← hsShim]; simp [wp_norm, arm64_norm]; try decide
  have hlrS : sShim.readReg64 .lr = initPcExt img ext 0x009c := by
    rw [← hsShim]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm]; try bv_omega
  have hfpS : sShim.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsShim]; simp [wp_norm, arm64_norm]
  have hx19S : sShim.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsShim]; simp [wp_norm, arm64_norm, hx8]
  have hvregsS : calleeSavedVRegs sShim = calleeSavedVRegs s0 := by
    rw [← hsShim]; simp [calleeSavedVRegs, wp_norm, arm64_norm]
  have htrS : sShim.trace = s0.trace := by rw [← hsShim]; simp [wp_norm, arm64_norm]
  have hfsS : sShim.fs.files = s0.fs.files := by rw [← hsShim]; simp [wp_norm, arm64_norm]
  clear hsShim
  have halS : sShim.spAligned = true := spAligned_of_frame hal0 hspS
  simp only [pointsTo16_zero_eq]
  let shimArg : IdentityShimCall × BitVec 8 :=
    ({ self := x.stores, addrA := x.peerA, keyA := x.bundleA + 120#64 }, 0#8)
  refine sepWPp_mono_pre (P' :=
      ((idTrustShimSpec A img (stk - cliInitiateFrame)).pre shimArg sShim) ∗
      (cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        memRegion fsp 0xd0 ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8))) ?_ ?_
  · unfold idTrustShimSpec Spec.inImage initSaved initArgsAt
    dsimp only [shimArg]
    rw [hspS]
    simp (disch := decide) only
      [fsp, cliInitiateFrame, initLocalsSize, BitVec.add_zero, bv_sub_add_lit,
        Nat.reduceAdd, Nat.reduceSub]
    have hsp113 : (s0.sp - 96#64) - 17#64 = s0.sp - 113#64 := by bv_omega
    have hsp113' : (s0.sp - 96#64) + (0#64 - 17#64) = s0.sp - 113#64 := by bv_omega
    try simp only [hsp113, hsp113']
    have hpackB := cliBundleBody_pack (a := x.bundleA) (b := x.bundle)
      (spkSigPtr := x.spkSigPtr) (kpkSigPtr := x.kpkSigPtr) (kpkPtr := x.kpkPtr)
      (opkId := opkId) h1 h2 h3 hopk
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro hinvS (pure_sepConj_intro ⟨hx0S, hx1S, hx2S, hx3S⟩ ?_)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hpackB
          (sepConj_mono (prologue_low_d0_merge_sp s0.sp)
            (sepConj_mono_left (prologue_high_5ba_merge_sp s0.sp))))))
    sep_frame
  refine initCall_ext hh hpanic hStore.idTrustShim hpcS hrunS halS hinvS htrS hfsS hlrS
    (Entails.refl _) (fun _ => Entails.refl _) ?_
  intro sAfterShim hpcAS hrunAS hspAS hcsAS hinvAS hfsAS
  unfold idTrustShimSpec Spec.inImage
  dsimp only [shimArg]
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨hvtAS, _hfutNZ, _hfutAl, htrAS⟩ => ?_
  have htrAS' : sAfterShim.trace = s0.trace := htrAS.trans htrS
  have hfsAS' : sAfterShim.fs.files = s0.fs.files := hfsAS htrAS'
  have hspAS' : sAfterShim.sp = fsp := hspAS.trans hspS
  have hctrlAS : InInitiateExt img ext s0 sAfterShim 0x009c :=
    ⟨hpcAS, hrunAS, hspAS', (cs_fp hcsAS).trans hfpS, (cs_x19 hcsAS).trans hx19S,
      hfsAS', hinvAS, (cs_vregs hcsAS).trans hvregsS, hal0⟩
  rw [hspS]
  refine sepWPp_mono_pre (P' := afterTrustShimMem A img x stk s0 sAfterShim)
    (by unfold afterTrustShimMem; dsimp only [fsp]; sep_frame) ?_
  exact hnext sAfterShim h1 h2 h3 hctrlAS htrAS' hvtAS

theorem stage1_prologue_to_shim_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {B : RunBudgets} {S : RunSem} {x : InitGhost} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) (hStore : InitStoreCallees img A W B stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) (hs0 : AtInitEntry img W x s0)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAfterShim : State) (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64) (_h3 : x.bundle.kpk.length = 1568),
      InInitiate img W s0 sAfterShim 0x009c → sAfterShim.trace = s0.trace →
      sAfterShim.readReg64 (.gpr 1#5) = img.base + idTrustFutVtOff →
      SepWPp (initProg img W) (s0.readReg64 .lr) sAfterShim
        (afterTrustShimMem A img x stk s0 sAfterShim) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s0 (initEntryMem' A img x stk s0) Q Qp (initOom s0) :=
  stage1_prologue_to_shim_ext_ok (ext := cliHookExterns W) himg hh.toExt
    (initStoreCallees_toExt hStore) hstk hstk64 (atInitEntry_toExt hs0) hpanic
    fun s h1 h2 h3 hc => hnext s h1 h2 h3 (inInitiate_ofExt hc)

/-- Bundle fields outside the 32-byte `idKey` slice at `+120`. -/
def bundleRestAt (x : InitGhost) (opkId2 : BitVec 32) : SepProp :=
  (x.bundleA ↦₆₄ 64#64) ∗ ((x.bundleA + 8#64) ↦₆₄ x.spkSigPtr) ∗
    ((x.bundleA + 16#64) ↦₆₄ 64#64) ∗ (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
    ((x.bundleA + 24#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
    ((x.bundleA + 56#64) ↦₃₂ x.bundle.spkId) ∗ memRegion (x.bundleA + 60#64) 4 ∗
    ((x.bundleA + 64#64) ↦₆₄ 64#64) ∗ ((x.bundleA + 72#64) ↦₆₄ x.kpkSigPtr) ∗
    ((x.bundleA + 80#64) ↦₆₄ 64#64) ∗ (x.kpkSigPtr ↦ₛ x.bundle.kpkSig) ∗
    ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗ ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
    (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
    ((x.bundleA + 104#64) ↦₃₂ x.bundle.kpkId) ∗ memRegion (x.bundleA + 108#64) 4 ∗
    ((x.bundleA + 112#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
    ((x.bundleA + 116#64) ↦₃₂ opkId2) ∗
    ((x.bundleA + 152#64) ↦₃₂ x.bundle.regId) ∗
    ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
    (match x.bundle.opk with
     | some (_, k) => (x.bundleA + 157#64) ↦ₛ k.bytes.toList
     | none => memRegion (x.bundleA + 157#64) 32) ∗
    ((x.bundleA + 189#64) ↦₈ x.bundle.device) ∗ memRegion (x.bundleA + 190#64) 2

/-- Spatial state at `0x00b8` after `idTrustPoll` returns and its 48-byte `sret` is unpacked. -/
def afterTrustPollMem (A : RustAlloc) (img : Obj.Image) (x : InitGhost) (stk : Nat)
    (s0 : State) (futPtr : BitVec 64) (opkId2 : BitVec 32)
    (w_tb o2 o3 o4 o5 : BitVec 64) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  (((fsp + 0x1600#64) ↦₆₄ (0#64 - 2#64)) ∗
      ((fsp + 0x1608#64) ↦₆₄ w_tb) ∗
      ((fsp + 0x1610#64) ↦₆₄ o2) ∗ ((fsp + 0x1618#64) ↦₆₄ o3) ∗
      ((fsp + 0x1620#64) ↦₆₄ o4) ∗ ((fsp + 0x1628#64) ↦₆₄ o5)) ∗
    (idTrustBoxAt futPtr x.stores x.peerA (x.bundleA + 120#64) 1#8 0#8 ∗
      dirAt A (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
      protocolAddressAt A x.peer x.peerA ∗
      ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
      logOff img ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗
    (A.live futPtr 32 8 ∗
      dirAt A x.stores StoresGhost.opened.identity.own ∗
      dirAt A (x.stores + 0x50#64) StoresGhost.opened.signed ∗
      dirAt A (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
      dirAt A (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
      dirAt A (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      dirAt A (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      dirAt A (x.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A x.me x.meA ∗
      coinsCursorAt img x.coinsP x.coins 0 ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
      bundleRestAt x opkId2 ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      initSaved s0 ∗ initArgsAt img fsp x s0 ∗
      memRegion fsp 0xd0 ∗ memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) 6 ∗
      ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
      ((fsp + 0x5c8#64) ↦₆₄ (img.base + idTrustFutVtOff)) ∗
      memRegion (fsp + 0x5d0#64) (0x1600 - 0x5d0) ∗
      memRegion (fsp + 0x1630#64) (initLocalsSize - 0x1630))

set_option maxHeartbeats 1200000 in
/-- Branches on trust boolean `tb` (`0x0144 → 0x0154` on `true`, `0x0244` on `false`, `initProgExt`). -/
theorem stage1_trust_branch_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sAfterDealloc : State}
    {tb : Bool} {w_tb : BitVec 64}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryExt img ext x s0)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrlAF : InInitiateExt img ext s0 sAfterDealloc 0x0144)
    (htrAF' : sAfterDealloc.trace = s0.trace)
    (hx26AF : sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64)
    (hx27AF : sAfterDealloc.readReg64 (.gpr 27#5) = w_tb)
    (hw_tb : BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8))
    (htb2 : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok tb)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      InInitiateExt img ext s0 s1 0x0154 →
      s1.trace = s0.trace →
      s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s1
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) sAfterDealloc
      (stage2Mem A img x stk s0) Q Qp (initOom s0) := by
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage1Bin img.base
    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x0144 0x0010
  have hx8 := hs0.x8; have hfs0 := hs0.files; have hal0 := hs0.spAligned
  have hpcAF := hctrlAF.pc; have hrunAF := hctrlAF.run; have hspAF' := hctrlAF.sp
  have hfpAF := hctrlAF.fp; have hx19AF := hctrlAF.x19; have hfsAF' := hctrlAF.files0
  have hinvAF := hctrlAF.inv; have hvregsAF := hctrlAF.vregs
  have hent : initEntryExt img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpcAF ⊢
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAF
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  examples_hide_fetches
  cases tb
  · have hbit0 : w_tb.getLsbD 0 = false := getLsbD0_of_extract8_zero hw_tb
    have hbit : w_tb.extractLsb' 0 1 = 0#1 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hi0 : i = 0 := by omega
      subst hi0; simpa using hbit0
    have hb0 : w_tb[0] = false := hbit0
    refine sepWPp_step_to (fnBase + 0x0244#64) hinvAF ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro sU hsU hpcU hrunU hinvU
    have hspU : sU.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
      rw [← hsU]; simp [wp_norm, arm64_norm, hspAF']
    have hx21U : sU.readReg64 (.gpr 21#5) = sU.sp + 0xfe0#64 := by
      rw [← hsU]; simp [wp_norm, arm64_norm, hspAF', cliInitiateFrame]
    have hfpU : sU.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsU]; simp [wp_norm, arm64_norm, hfpAF]
    have hx19U : sU.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsU]; simp [wp_norm, arm64_norm, hx19AF]
    have hvregsU : calleeSavedVRegs sU = calleeSavedVRegs s0 := by
      rw [← hsU]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAF]
    have htrU : sU.trace = s0.trace := by
      rw [← hsU]; simp [wp_norm, arm64_norm, htrAF']
    have hfsU : sU.fs.files = s0.fs.files := by
      rw [← hsU]; simp [wp_norm, arm64_norm, hfsAF']
    clear hsU
    rw [← hent] at hpcU
    have hctrlU : InInitiateExt img ext s0 sU 0x0244 :=
      ⟨hpcU, hrunU, hspU, hfpU, hx19U, hfsU, hinvU, hvregsU, hal0⟩
    exact stage1_untrusted_exit_ext_ok hh hS hstk hstk64 hx8 hctrlU hx21U htrU htb2 hpost hpanic
  · have hbit0 : w_tb.getLsbD 0 = true := getLsbD0_of_extract8_one hw_tb
    have hbit : w_tb.extractLsb' 0 1 = 1#1 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hi0 : i = 0 := by omega
      subst hi0; simpa using hbit0
    have hb0 : w_tb[0] = true := hbit0
    refine sepWPp_step_to (fnBase + 0x0154#64) hinvAF ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 hpc1 hrun1 hinv1
    have hsp1 : s1.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
      rw [← hs1]; simp [wp_norm, arm64_norm, hspAF']
    have hfp1 : s1.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hs1]; simp [wp_norm, arm64_norm, hfpAF]
    have hx19_1 : s1.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hs1]; simp [wp_norm, arm64_norm, hx19AF]
    have hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      rw [← hs1]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAF]
    have htr1 : s1.trace = s0.trace := by
      rw [← hs1]; simp [wp_norm, arm64_norm, htrAF']
    have hfs1 : s1.fs.files = x.F := by
      rw [← hs1]; simp [wp_norm, arm64_norm, hfsAF', hfs0]
    have hfs10 : s1.fs.files = s1.fs.files := rfl
    clear hs1
    rw [← hent] at hpc1
    have hctrl1 : InInitiateExt img ext s0 s1 0x0154 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hx19_1, hfs1.trans hfs0.symm, hinv1, hvregs1, hal0⟩
    exact hnext s1 h1 h2 h3 hctrl1 htr1 hfs1 htb2

theorem stage1_trust_branch_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem} {x : InitGhost} {stk : Nat}
    {s0 sAfterDealloc : State} {tb : Bool} {w_tb : BitVec 64} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W)) (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) (hs0 : AtInitEntry img W x s0)
    (h1 : x.bundle.spkSig.length = 64) (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568) (hctrlAF : InInitiate img W s0 sAfterDealloc 0x0144)
    (htrAF' : sAfterDealloc.trace = s0.trace)
    (hx26AF : sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64)
    (hx27AF : sAfterDealloc.readReg64 (.gpr 27#5) = w_tb)
    (hw_tb : BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8))
    (htb2 : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok tb)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State) (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64) (_h3 : x.bundle.kpk.length = 1568),
      InInitiate img W s0 s1 0x0154 → s1.trace = s0.trace → s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProg img W) (s0.readReg64 .lr) s1 (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) sAfterDealloc
      (stage2Mem A img x stk s0) Q Qp (initOom s0) :=
  stage1_trust_branch_ext_ok (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W) hh.toExt hS hstk hstk64
    (atInitEntry_toExt hs0) h1 h2 h3 (inInitiate_toExt hctrlAF) htrAF' hx26AF hx27AF hw_tb htb2
    hpost hpanic fun s1 h1 h2 h3 hc => hnext s1 h1 h2 h3 (inInitiate_ofExt hc)

@[irreducible] def futDropAddr (img : Obj.Image) (W : CliHooks) : BitVec 64 :=
  (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr KitInst.cliIdFutDropName

theorem futDropAddr_eq (img : Obj.Image) (W : CliHooks) :
    futDropAddr img W =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr KitInst.cliIdFutDropName := by
  unfold futDropAddr; rfl

theorem futDropAddr_ne_zero {img : Obj.Image} {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage img) :
    (futDropAddr img W == 0#64) = false := by
  rw [futDropAddr_eq]; exact cliIdFutDrop_ne_zero (W := W) himg

theorem rodata_idTrustFut_drop_irr {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((img.base + idTrustFutVtOff) ↦₆₄ᵣ futDropAddr img W) ∗ R) := by
  rw [futDropAddr_eq]; exact rodata_idTrustFut_drop (W := W) himg hF

@[irreducible] def idTrustPollAddr (img : Obj.Image) (W : CliHooks) : BitVec 64 :=
  (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr idTrustPollName

theorem idTrustPollAddr_eq (img : Obj.Image) (W : CliHooks) :
    idTrustPollAddr img W =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr idTrustPollName := by
  unfold idTrustPollAddr; rfl

theorem rodata_idTrustFut_poll_irr {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + idTrustFutVtOff) + 24#64) ↦₆₄ᵣ idTrustPollAddr img W) ∗ R) := by
  rw [idTrustPollAddr_eq]; exact rodata_idTrustFut_poll (W := W) himg hF

set_option maxHeartbeats 1200000 in
/-- `futDrop`, `__rust_dealloc(32, 8)`, and `stage2Mem` packing (`0x00b8 → 0x0144`, `initProgExt`). -/
theorem stage1_trust_drop_dealloc_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sAfterPoll : State}
    {futPtr : BitVec 64} {opkId2 : BitVec 32}
    {w_tb o2 o3 o4 o5 : BitVec 64}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hopk2 : ∀ p, x.bundle.opk = some p → opkId2 = p.1)
    (hctrlAP : InInitiateExt img ext s0 sAfterPoll 0x00b8)
    (htrAP' : sAfterPoll.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sAfterDealloc : State,
      InInitiateExt img ext s0 sAfterDealloc 0x0144 →
      sAfterDealloc.trace = s0.trace →
      sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 →
      sAfterDealloc.readReg64 (.gpr 27#5) = w_tb →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sAfterDealloc
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) sAfterPoll
      (afterTrustPollMem A img x stk s0 futPtr opkId2 w_tb o2 o3 o4 o5) Q Qp (initOom s0) := by
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage1Bin img.base
    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x00b8 0x008c
  have hpcAP := hctrlAP.pc; have hrunAP := hctrlAP.run; have hspAP' := hctrlAP.sp
  have hfpAP := hctrlAP.fp; have hx19AP := hctrlAP.x19; have hfsAP' := hctrlAP.files0
  have hinvAP := hctrlAP.inv; have hvregsAP := hctrlAP.vregs; have hal0 := hctrlAP.spAligned
  have halAP := spAligned_of_frame hal0 hspAP'
  have hdz := futDropAddr_ext_ne_zero (ext := ext) himg
  unfold afterTrustPollMem; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAP' ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hspAP'] using halAP
  have hent : initEntryExt img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpcAP ⊢
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAP
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  examples_hide_fetches
  refine sepWPp_with_rodata (rodata_idTrustFut_drop_irr_ext (ext := ext) himg hinvAP.1) ?_
  refine sepWPp_step_to (futDropAddr_ext img ext) hinvAP ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sDrop hsDrop hpcD hrunD hinvD
  refine sepWPp_drop_left ?_
  have hspD : sDrop.sp = fsp := by rw [← hsDrop]; simp [wp_norm, arm64_norm, hspAP']
  have hlrD : sDrop.readReg64 .lr = initPcExt img ext 0x0130 := by
    rw [← hsDrop]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm]; try bv_omega
  have hx20D : sDrop.readReg64 (.gpr 20#5) = futPtr := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm]
  have hx22D : sDrop.readReg64 (.gpr 22#5) = img.base + idTrustFutVtOff := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm]
  have hx26D : sDrop.readReg64 (.gpr 26#5) = 0#64 - 2#64 := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm]
  have hx27D : sDrop.readReg64 (.gpr 27#5) = w_tb := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm]
  have hfpD : sDrop.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm, hfpAP]
  have hx19D : sDrop.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm, hx19AP]
  have hvregsD : calleeSavedVRegs sDrop = calleeSavedVRegs s0 := by
    rw [← hsDrop]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAP]
  have htrD : sDrop.trace = s0.trace := by rw [← hsDrop]; simp [wp_norm, arm64_norm, htrAP']
  have hfsD : sDrop.fs.files = s0.fs.files := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm, hfsAP']
  clear hsDrop
  have halD : sDrop.spAligned = true := spAligned_of_sp_eq halAP (hspD.trans hspAP'.symm)
  rw [futDropAddr_ext_eq] at hpcD
  refine initCall_ext hh hpanic hStore.futDrop (gx := ()) hpcD hrunD halD hinvD htrD hfsD hlrD
    (by unfold futDropSpec; rw [emp_sepConj]; exact Entails.refl _) (fun _ => false_entails _) ?_
  intro sAfterDrop hpcAD hrunAD hspAD hcsAD hinvAD hfsAD
  unfold futDropSpec; dsimp only
  refine sepWPp_pure_elim fun htrAD => ?_
  have htrAD' : sAfterDrop.trace = s0.trace := htrAD.trans htrD
  have hfsAD' : sAfterDrop.fs.files = s0.fs.files := hfsAD htrAD'
  have hspAD' : sAfterDrop.sp = fsp := hspAD.trans hspD
  have hx20AD : sAfterDrop.readReg64 (.gpr 20#5) = futPtr := (cs_x20 hcsAD).trans hx20D
  have hx22AD : sAfterDrop.readReg64 (.gpr 22#5) = img.base + idTrustFutVtOff :=
    (cs_x22 hcsAD).trans hx22D
  have hx26AD : sAfterDrop.readReg64 (.gpr 26#5) = 0#64 - 2#64 :=
    (cs_x26 hcsAD).trans hx26D
  have hx27AD : sAfterDrop.readReg64 (.gpr 27#5) = w_tb :=
    (cs_x27 hcsAD).trans hx27D
  refine sepWPp_with_rodata (rodata_idTrustFut_size himg hinvAD.1) ?_
  refine sepWPp_with_rodata (rodata_idTrustFut_align himg hinvAD.1) ?_
  dsimp only [initPcExt] at hpcAD
  rw [hent] at hpcAD
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAD
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to
    (fnBase + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    hinvAD ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sDealloc hsDealloc hpcF hrunF hinvF
  refine sepWPp_drop_left (sepWPp_drop_left ?_)
  have hspF : sDealloc.sp = fsp := by rw [← hsDealloc]; simp [wp_norm, arm64_norm, hspAD']
  have hx0F : sDealloc.readReg64 .x0 = futPtr := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm]
  have hx1F : (sDealloc.readReg64 .x1).toNat = 32 := by rw [← hsDealloc]; simp [wp_norm, arm64_norm]
  have hx2F : (sDealloc.readReg64 .x2).toNat = 8 := by rw [← hsDealloc]; simp [wp_norm, arm64_norm]
  have hlrF : sDealloc.readReg64 .lr = initPcExt img ext 0x0144 := by
    rw [← hsDealloc]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm]; try bv_omega
  have hx26F : sDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, hx26AD]
  have hx27F : sDealloc.readReg64 (.gpr 27#5) = w_tb := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, hx27AD]
  have hfpF : sDealloc.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, cs_fp hcsAD, hfpD]
  have hx19F : sDealloc.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, cs_x19 hcsAD, hx19D]
  have hvregsF : calleeSavedVRegs sDealloc = calleeSavedVRegs s0 := by
    rw [← hsDealloc]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAD, hvregsD]
  have htrF : sDealloc.trace = s0.trace := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, htrAD']
  have hfsF : sDealloc.fs.files = s0.fs.files := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, hfsAD']
  clear hsDealloc
  have halF : sDealloc.spAligned = true := spAligned_of_sp_eq halAP (hspF.trans hspAP'.symm)
  have hdealloc := init_dealloc_ok_at_ext (ext := ext) hh hstk hstk64
  let frameNoPool : SepProp :=
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      storesAt A x.stores StoresGhost.opened ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      coinsCursorAt img x.coinsP x.coins 0 ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      logOff img ∗ initSaved s0 ∗
      memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)
  refine sepWPp_mono_pre (P' :=
      ((rustDeallocExternSpecWithStack A (stk - cliInitiateFrame)).pre (futPtr, 32, 8) sDealloc) ∗
      frameNoPool) ?_ ?_
  · dsimp only [frameNoPool]
    unfold rustDeallocExternSpecWithStack storesAt
    dsimp only
    rw [hspF]
    have hboxMem := idTrustBoxAt_entails_memRegion futPtr x.stores x.peerA
      (x.bundleA + 120#64) 1#8 0#8
    have hpackB :
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗ bundleRestAt x opkId2 ⊢
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr := by
      refine Entails.trans ?_
        (cliBundleBody_pack (a := x.bundleA) (b := x.bundle)
          (spkSigPtr := x.spkSigPtr) (kpkSigPtr := x.kpkSigPtr) (kpkPtr := x.kpkPtr)
          (opkId := opkId2) h1 h2 h3 hopk2)
      unfold cliBundleBody bundleRestAt
      rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
    have h48 :
        ((fsp + 0x1600#64) ↦₆₄ (0#64 - 2#64)) ∗
          ((fsp + 0x1608#64) ↦₆₄ w_tb) ∗
          ((fsp + 0x1610#64) ↦₆₄ o2) ∗ ((fsp + 0x1618#64) ↦₆₄ o3) ∗
          ((fsp + 0x1620#64) ↦₆₄ o4) ∗ ((fsp + 0x1628#64) ↦₆₄ o5) ⊢
          memRegion (fsp + 0x1600#64) 48 := by
      rw [memRegion_48_words (fsp + 0x1600#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      sep_frame
    have hmergePoll48 :
        memRegion (fsp + 0x5ba#64) 6 ∗
          ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
          ((fsp + 0x5c8#64) ↦₆₄ (img.base + idTrustFutVtOff)) ∗
          memRegion (fsp + 0x5d0#64) (0x1600 - 0x5d0) ∗
          (((fsp + 0x1600#64) ↦₆₄ (0#64 - 2#64)) ∗
            ((fsp + 0x1608#64) ↦₆₄ w_tb) ∗
            ((fsp + 0x1610#64) ↦₆₄ o2) ∗ ((fsp + 0x1618#64) ↦₆₄ o3) ∗
            ((fsp + 0x1620#64) ↦₆₄ o4) ∗ ((fsp + 0x1628#64) ↦₆₄ o5)) ∗
          memRegion (fsp + 0x1630#64) (initLocalsSize - 0x1630) ⊢
          memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left h48)))))
        (poll_frame_5ba_merge fsp futPtr (img.base + idTrustFutVtOff) 48 (by decide))
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro ⟨hx0F, hx1F, hx2F, ⟨by decide, ⟨3, rfl⟩, by decide⟩⟩ ?_
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hboxMem (sepConj_mono_right (sepConj_mono hpackB (sepConj_mono_left hmergePoll48))))))
    sep_frame
  rw [← hent] at hpcF
  refine initCallInImage_ext hh hpanic hdealloc hpcF hrunF halF hinvF htrF hfsF hlrF
    (Entails.refl _) (fun _ => false_entails _) ?_
  intro sAfterDealloc hpcAF hrunAF hspAF hcsAF hinvAF hfsAF
  unfold rustDeallocExternSpecWithStack; dsimp only
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun htrAF => ?_
  have htrAF' : sAfterDealloc.trace = s0.trace := htrAF.trans htrF
  have hfsAF' : sAfterDealloc.fs.files = s0.fs.files := hfsAF htrAF'
  have hspAF' : sAfterDealloc.sp = fsp := hspAF.trans hspF
  have hx26AF : sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 :=
    (cs_x26 hcsAF).trans hx26F
  have hx27AF : sAfterDealloc.readReg64 (.gpr 27#5) = w_tb :=
    (cs_x27 hcsAF).trans hx27F
  have hfpAF : sAfterDealloc.readReg64 .fp = s0.sp - 0x60#64 :=
    (cs_fp hcsAF).trans hfpF
  have hx19AF : sAfterDealloc.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
    (cs_x19 hcsAF).trans hx19F
  have hvregsAF : calleeSavedVRegs sAfterDealloc = calleeSavedVRegs s0 :=
    (cs_vregs hcsAF).trans hvregsF
  refine sepWPp_mono_pre (P' := stage2Mem A img x stk s0) ?_ ?_
  · unfold stage2Mem
    dsimp only [frameNoPool]
    rw [hspF, ← hfsp]
    sep_frame
  have hctrlAF : InInitiateExt img ext s0 sAfterDealloc 0x0144 :=
    ⟨hpcAF, hrunAF, hspAF'.trans hfsp.symm, hfpAF, hx19AF, hfsAF', hinvAF, hvregsAF, hal0⟩
  exact hnext sAfterDealloc hctrlAF htrAF' hx26AF hx27AF

theorem stage1_trust_drop_dealloc_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {B : RunBudgets} {S : RunSem} {x : InitGhost} {stk : Nat} {s0 sAfterPoll : State}
    {futPtr : BitVec 64} {opkId2 : BitVec 32} {w_tb o2 o3 o4 o5 : BitVec 64}
    {Q Qp : State → SepProp → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) (hStore : InitStoreCallees img A W B stk)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (h1 : x.bundle.spkSig.length = 64) (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568) (hopk2 : ∀ p, x.bundle.opk = some p → opkId2 = p.1)
    (hctrlAP : InInitiate img W s0 sAfterPoll 0x00b8) (htrAP' : sAfterPoll.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sAfterDealloc : State, InInitiate img W s0 sAfterDealloc 0x0144 →
      sAfterDealloc.trace = s0.trace → sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 →
      sAfterDealloc.readReg64 (.gpr 27#5) = w_tb →
      SepWPp (initProg img W) (s0.readReg64 .lr) sAfterDealloc
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) sAfterPoll
      (afterTrustPollMem A img x stk s0 futPtr opkId2 w_tb o2 o3 o4 o5) Q Qp (initOom s0) :=
  stage1_trust_drop_dealloc_ext_ok (ext := cliHookExterns W) himg hh.toExt
    (initStoreCallees_toExt hStore) hstk hstk64 h1 h2 h3 hopk2 (inInitiate_toExt hctrlAP) htrAP'
    hpanic fun s hc => hnext s (inInitiate_ofExt hc)

set_option maxHeartbeats 1200000 in
/-- `idTrustPoll` invocation and 48-byte `sret` unpacking (`0x009c → 0x00b8`, `initProgExt`). -/
theorem stage1_trust_to_poll_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sAfterShim : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hs0 : AtInitEntryExt img ext x s0)
    (hctrlAS : InInitiateExt img ext s0 sAfterShim 0x009c)
    (htrAS' : sAfterShim.trace = s0.trace)
    (hvtAS : sAfterShim.readReg64 (.gpr 1#5) = img.base + idTrustFutVtOff)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAfterPoll : State) (futPtr : BitVec 64) (opkId2 : BitVec 32)
      (tb : Bool) (w_tb o2 o3 o4 o5 : BitVec 64),
      (∀ p, x.bundle.opk = some p → opkId2 = p.1) →
      InInitiateExt img ext s0 sAfterPoll 0x00b8 →
      sAfterPoll.trace = s0.trace →
      BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8) →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok tb →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sAfterPoll
        (afterTrustPollMem A img x stk s0 futPtr opkId2 w_tb o2 o3 o4 o5) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) sAfterShim
      (afterTrustShimMem A img x stk s0 sAfterShim) Q Qp (initOom s0) := by
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage1Bin img.base
    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x009c 0x0020
  have hfs0 := hs0.files; have hal0 := hs0.spAligned
  have hpcAS := hctrlAS.pc; have hrunAS := hctrlAS.run; have hspAS' := hctrlAS.sp
  have hfpAS := hctrlAS.fp; have hx19AS := hctrlAS.x19; have hfsAS' := hctrlAS.files0
  have hinvAS := hctrlAS.inv; have hvregsAS := hctrlAS.vregs
  have halAS := spAligned_of_frame hal0 hspAS'
  unfold afterTrustShimMem; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAS' ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hspAS'] using halAS
  rw [cliBundleAt_unpack]
  refine sepWPp_exists_left fun opkId2 => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨_, _, _, hopk2⟩ => ?_
  rw [poll_frame_5ba_split fsp 48 (by decide)]
  repeat rw [sepConj_assoc]
  refine sepWPp_exists_pos3 fun f0 => ?_
  refine sepWPp_exists_pos4 fun f1 => ?_
  let futPtr := sAfterShim.readReg64 .x0
  have hx1AS : sAfterShim.readReg64 (.gpr 1#5) = img.base + idTrustFutVtOff := hvtAS
  have hent : initEntryExt img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpcAS ⊢
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAS
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  examples_hide_fetches
  refine sepWPp_with_rodata (rodata_idTrustFut_poll_irr_ext (ext := ext) himg hinvAS.1) ?_
  refine sepWPp_step_to (idTrustPollAddr_ext img ext) hinvAS ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sPoll hsPoll hpcP hrunP hinvP
  refine sepWPp_drop_left ?_
  have hspP : sPoll.sp = fsp := by rw [← hsPoll]; simp [wp_norm, arm64_norm, hspAS']
  have hx0P : sPoll.readReg64 .x0 = futPtr := by rw [← hsPoll]; simp [futPtr, wp_norm, arm64_norm]
  have hx8P : sPoll.readReg64 .x8 = fsp + 0x1600#64 := by
    rw [← hsPoll]; simp [wp_norm, arm64_norm]; try bv_omega
  have hlrP : sPoll.readReg64 .lr = initPcExt img ext 0x00b8 := by
    rw [← hsPoll]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm]; try bv_omega
  have hfpP : sPoll.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsPoll]; simp [wp_norm, arm64_norm, hfpAS]
  have hx19P : sPoll.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsPoll]; simp [wp_norm, arm64_norm, hx19AS]
  have hvregsP : calleeSavedVRegs sPoll = calleeSavedVRegs s0 := by
    rw [← hsPoll]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAS]
  have htrP : sPoll.trace = s0.trace := by rw [← hsPoll]; simp [wp_norm, arm64_norm, htrAS']
  have hfsP : sPoll.fs.files = s0.fs.files := by
    rw [← hsPoll]; simp [wp_norm, arm64_norm, hfsAS']
  clear hsPoll
  have halP : sPoll.spAligned = true := spAligned_of_sp_eq halAS (hspP.trans hspAS'.symm)
  try rw [hspAS']
  try rw [hx1AS]
  rw [idTrustPollAddr_ext_eq] at hpcP
  let pollGhost : IdPollGhost :=
    { call := { fut := futPtr, out := fsp + 0x1600#64,
                call := { addr := x.peer, addrA := x.peerA,
                          key := x.bundle.idKey, keyA := x.bundleA + 120#64 } }
      self := x.stores
      peers := StoresGhost.opened.identity.peers }
  have hpeersGet : ∀ bs,
      StoresGhost.opened.identity.peers.get cliIo.rd sPoll.fs.files x.peer.val.name = .ok bs →
      IdFileWf bs := by
    intro bs hbs
    rw [hfsP, hfs0] at hbs
    obtain ⟨bs0, hbs0, hwf0⟩ := hinitOk.idGet
    rw [hbs0] at hbs
    cases hbs
    exact hwf0
  refine sepWPp_mono_pre (P' :=
      ((idTrustPollSpec cliIo.rd cliWrOk A img (stk - cliInitiateFrame)).pre
        (pollGhost, 0#8) sPoll) ∗
      (A.live futPtr 32 8 ∗
        dirAt A x.stores StoresGhost.opened.identity.own ∗
        dirAt A (x.stores + 0x50#64) StoresGhost.opened.signed ∗
        dirAt A (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
        dirAt A (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        dirAt A (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        bundleRestAt x opkId2 ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        initSaved s0 ∗ initArgsAt img fsp x s0 ∗
        memRegion fsp 0xd0 ∗ memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 6 ∗
        ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5c8#64) ↦₆₄ (img.base + idTrustFutVtOff)) ∗
        memRegion (fsp + 0x5d0#64) (0x1600 - 0x5d0) ∗
        memRegion (fsp + 0x1630#64) (initLocalsSize - 0x1630))) ?_ ?_
  · unfold idTrustPollSpec Spec.inImage storesAt cliBundleBody bundleRestAt
    dsimp only [pollGhost, futPtr, Reg.x0]
    rw [hspP]
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro hinvP (pure_sepConj_intro
      ⟨hx0P, hx8P, hinitOk.nameLt, by
        dsimp only [StoresGhost.opened, DirGhost.new]
        have h := hinitOk.idPathLt; unfold pathOf at h
        split at h
        · rename_i heq; rw [heq]; dsimp; omega
        · simp only [List.length_append] at h; omega,
        ⟨hinitOk.idPathOk, hinitOk.idPathLt⟩, hpeersGet⟩ ?_)
    rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
  refine initCall_ext hh hpanic hStore.idTrustPoll hpcP hrunP halP hinvP htrP hfsP hlrP
    (Entails.refl _) (fun _ => Entails.refl _) ?_
  intro sAfterPoll hpcAP hrunAP hspAP hcsAP hinvAP hfsAP
  unfold idTrustPollSpec Spec.inImage
  dsimp only [pollGhost]
  rw [sepConj_assoc]; refine sepWPp_exists_left fun gr => ?_
  refine sepWPp_exists_left fun p => ?_
  rw [sepConj_assoc]; refine sepWPp_pure_elim fun ⟨⟨hgr, htrAP⟩, hp⟩ => ?_
  have htrAP' : sAfterPoll.trace = s0.trace := htrAP.trans htrP
  have hfsAP' : sAfterPoll.fs.files = s0.fs.files := hfsAP htrAP'
  rw [hfsP, hfs0] at hgr
  obtain ⟨tb, htb1, htb2⟩ := idTrust_always_ok hinitOk hgr hp
  rw [htb1, idTrustOutAt_ok A img.base]
  have houtCells :
      trustPollOutAt img.base (fsp + 0x1600#64) (.ok tb) ⊢
        ∃∗ w_tb : BitVec 64, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
        ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64,
          ⌜BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8)⌝ ∗
          ((fsp + 0x1600#64) ↦₆₄ (0#64 - 2#64)) ∗
          ((fsp + 0x1608#64) ↦₆₄ w_tb) ∗
          ((fsp + 0x1610#64) ↦₆₄ o2) ∗ ((fsp + 0x1618#64) ↦₆₄ o3) ∗
          ((fsp + 0x1620#64) ↦₆₄ o4) ∗ ((fsp + 0x1628#64) ↦₆₄ o5) := by
    unfold trustPollOutAt
    rw [show (39 : Nat) = 7 + (8 + (8 + (8 + 8))) by decide,
      memRegion_split _ 7 _ (by decide),
      memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
      memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
      memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
      ProofLib.memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro o5
    apply Entails.sepExists_elim; intro o4
    apply Entails.sepExists_elim; intro o3
    apply Entails.sepExists_elim; intro o2
    have hpackTb :
        ((fsp + 5640#64) ↦₈ (if tb then 1#8 else 0#8)) ∗ memRegion (fsp + 5641#64) 7 ⊢
          ∃∗ w, ⌜BitVec.extractLsb' 0 8 w = (if tb then 1#8 else 0#8)⌝ ∗ ((fsp + 5640#64) ↦₆₄ w) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        byte_and_pad7_entails_word64 (fsp + 5640#64) (if tb then 1#8 else 0#8)
    refine Entails.trans (by sep_frame :
      _ ⊢ (((fsp + 5640#64) ↦₈ (if tb then 1#8 else 0#8)) ∗ memRegion (fsp + 5641#64) 7) ∗
          (((fsp + 5632#64) ↦₆₄ (0#64 - 2#64)) ∗
            ((fsp + 5648#64) ↦₆₄ o2) ∗ ((fsp + 5656#64) ↦₆₄ o3) ∗
            ((fsp + 5664#64) ↦₆₄ o4) ∗ ((fsp + 5672#64) ↦₆₄ o5))) ?_
    refine Entails.trans (sepConj_mono_left hpackTb) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w_tb
    refine Entails.sepExists_right w_tb (Entails.sepExists_right o2
      (Entails.sepExists_right o3 (Entails.sepExists_right o4 (Entails.sepExists_right o5 ?_))))
    rw [sepConj_assoc]
    exact pure_sepConj_elim fun hw => pure_sepConj_intro hw (by sep_frame)
  refine sepWPp_mono_pre (sepConj_mono_left houtCells) ?_
  refine sepWPp_exists_left fun w_tb => ?_; refine sepWPp_exists_left fun o2 => ?_
  refine sepWPp_exists_left fun o3 => ?_; refine sepWPp_exists_left fun o4 => ?_
  refine sepWPp_exists_left fun o5 => ?_
  rw [sepConj_assoc]; refine sepWPp_pure_elim fun hw_tb => ?_
  have hctrlAP : InInitiateExt img ext s0 sAfterPoll 0x00b8 :=
    ⟨hpcAP, hrunAP, (hspAP.trans hspP).trans hfsp.symm, (cs_fp hcsAP).trans hfpP,
      (cs_x19 hcsAP).trans hx19P, hfsAP', hinvAP, (cs_vregs hcsAP).trans hvregsP, hal0⟩
  refine sepWPp_mono_pre
    (P' := afterTrustPollMem A img x stk s0 futPtr opkId2 w_tb o2 o3 o4 o5)
    (by unfold afterTrustPollMem; dsimp only; rw [hspP, ← hfsp]; sep_frame) ?_
  exact hnext sAfterPoll futPtr opkId2 tb w_tb o2 o3 o4 o5 hopk2 hctrlAP htrAP' hw_tb htb2

theorem stage1_trust_to_poll_ok {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {B : RunBudgets} {S : RunSem} {x : InitGhost} {stk : Nat} {s0 sAfterShim : State}
    {Q Qp : State → SepProp → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) (hStore : InitStoreCallees img A W B stk)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val) (hs0 : AtInitEntry img W x s0)
    (hctrlAS : InInitiate img W s0 sAfterShim 0x009c) (htrAS' : sAfterShim.trace = s0.trace)
    (hvtAS : sAfterShim.readReg64 (.gpr 1#5) = img.base + idTrustFutVtOff)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAfterPoll : State) (futPtr : BitVec 64) (opkId2 : BitVec 32)
      (tb : Bool) (w_tb o2 o3 o4 o5 : BitVec 64),
      (∀ p, x.bundle.opk = some p → opkId2 = p.1) →
      InInitiate img W s0 sAfterPoll 0x00b8 → sAfterPoll.trace = s0.trace →
      BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8) →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok tb →
      SepWPp (initProg img W) (s0.readReg64 .lr) sAfterPoll
        (afterTrustPollMem A img x stk s0 futPtr opkId2 w_tb o2 o3 o4 o5) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) sAfterShim
      (afterTrustShimMem A img x stk s0 sAfterShim) Q Qp (initOom s0) :=
  stage1_trust_to_poll_ext_ok (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W) himg hh.toExt
    (initStoreCallees_toExt hStore) hinitOk (atInitEntry_toExt hs0) (inInitiate_toExt hctrlAS)
    htrAS' hvtAS hpanic fun s fp opk tb w o2 o3 o4 o5 hopk hc =>
      hnext s fp opk tb w o2 o3 o4 o5 hopk (inInitiate_ofExt hc)

/-- `idTrustPoll`, `futDrop`, `dealloc`, and trust branch (`0x009c → 0x0154`, `initProg`). -/
theorem stage1_trust_poll_drop_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sAfterShim : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hStore : InitStoreCallees img A W B stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntry img W x s0)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrlAS : InInitiate img W s0 sAfterShim 0x009c)
    (htrAS' : sAfterShim.trace = s0.trace)
    (hvtAS : sAfterShim.readReg64 (.gpr 1#5) = img.base + idTrustFutVtOff)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      InInitiate img W s0 s1 0x0154 →
      s1.trace = s0.trace →
      s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProg img W) (s0.readReg64 .lr) s1
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) sAfterShim
      (afterTrustShimMem A img x stk s0 sAfterShim) Q Qp (initOom s0) :=
  stage1_trust_to_poll_ok himg hh hStore hinitOk hs0 hctrlAS htrAS' hvtAS hpanic
    fun _ _ _ _ _ _ _ _ _ hopk2 hctrlAP htrAP' hw_tb htb2 =>
      stage1_trust_drop_dealloc_ok himg hh hStore hstk hstk64 h1 h2 h3 hopk2 hctrlAP htrAP' hpanic
        fun _ hctrlAF htrAF' hx26AF hx27AF =>
          stage1_trust_branch_ok hh hS hstk hstk64 hs0 h1 h2 h3 hctrlAF htrAF'
            hx26AF hx27AF hw_tb htb2 hpost hpanic hnext

/-- Prologue and `is_trusted_identity` (`0x0000 → 0x0154` and untrusted exit, `initProg`). -/
theorem stage1_prologue_trust_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hStore : InitStoreCallees img A W B stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntry img W x s0)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      InInitiate img W s0 s1 0x0154 →
      s1.trace = s0.trace →
      s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProg img W) (s0.readReg64 .lr) s1
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s0
      (initEntryMem' A img x stk s0) Q Qp (initOom s0) :=
  stage1_prologue_to_shim_ok himg hh hStore hstk hstk64 hs0 hpanic
    fun _ h1 h2 h3 hctrlAS htrAS' hvtAS =>
      stage1_trust_poll_drop_ok himg hh hStore hS hinitOk hstk hstk64 hs0
        h1 h2 h3 hctrlAS htrAS' hvtAS hpost hpanic hnext

/-- Prologue and `is_trusted_identity` (`0x0000 → 0x0154` and untrusted exit, `initProgExt`). -/
theorem stage1_prologue_trust_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 : State} {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hS : S.initiate = initDef X P) (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryExt img ext x s0)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State) (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64) (_h3 : x.bundle.kpk.length = 1568),
      InInitiateExt img ext s0 s1 0x0154 → s1.trace = s0.trace → s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s1
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s0
      (initEntryMem' A img x stk s0) Q Qp (initOom s0) :=
  stage1_prologue_to_shim_ext_ok himg hh hStore hstk hstk64 hs0 hpanic
    fun _ h1 h2 h3 hctrlAS htrAS' hvtAS =>
      stage1_trust_to_poll_ext_ok himg hh hStore hinitOk hs0 hctrlAS htrAS' hvtAS hpanic
        fun _ _ _ _ _ _ _ _ _ hopk2 hctrlAP htrAP' hw_tb htb2 =>
          stage1_trust_drop_dealloc_ext_ok himg hh hStore hstk hstk64 h1 h2 h3 hopk2
            hctrlAP htrAP' hpanic fun _ hctrlAF htrAF' hx26AF hx27AF =>
              stage1_trust_branch_ext_ok hh hS hstk hstk64 hs0 h1 h2 h3 hctrlAF htrAF'
                hx26AF hx27AF hw_tb htb2 hpost hpanic hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

