/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrust
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpersPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Stage 1 Segment 1 (`0x0000 → 0x0154`): Prologue and `is_trusted_identity`

Verifies `stage1_prologue_trust_placed_ok` on `initProgPlaced`: executes the prologue, invokes
`idTrustShim`, `idTrustPoll`, optional `futDrop`, and `__rust_dealloc(32, 8)`, discharges the
untrusted-identity `Err` exit at `0x0244`, and establishes `stage2MemPlaced` at `0x0154`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
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
open CryptoVerification.CliHandshake.InitiatePlaced
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

/-- Spatial entry footprint of `initSlotSpecPlaced` after extracting pure preconditions. -/
abbrev initEntryMemPlaced' [LibsignalPlacement] (A : RustAlloc) (x : InitGhost) (stk : Nat)
    (s0 : State) : SepProp :=
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    coinsInstalledPlaced x.coinsP x.coins ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    FromRecordCallees.lsLogOff ∗ A.pool ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s0.sp stk

/-- Spatial state at `0x009c` after `idTrustShim` returns. -/
abbrev afterTrustShimMemPlaced [LibsignalPlacement] (A : RustAlloc) (x : InitGhost) (stk : Nat)
    (s0 sAfterShim : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    A.live (sAfterShim.readReg64 .x0) 32 8 ∗
    idTrustBoxAt (sAfterShim.readReg64 .x0) x.stores x.peerA (x.bundleA + 120#64) 0#8 0#8 ∗
    A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗
    storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    coinsCursorAtPlaced x.coinsP x.coins 0 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
    memRegion (fsp + 0x128#64) 0x490 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)

set_option maxHeartbeats 1600000 in
/-- Prologue and `is_trusted_identity` shim call (`0x0000 → 0x009c`). -/
theorem stage1_prologue_to_shim_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryPlaced x s0)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAfterShim : State)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      InInitiatePlaced s0 sAfterShim 0x009c →
      sAfterShim.trace = s0.trace →
      sAfterShim.readReg64 (.gpr 1#5) = lsρ idTrustFutVtSym →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterShim
        (afterTrustShimMemPlaced A x stk s0 sAfterShim) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s0
      (initEntryMemPlaced' A x stk s0) Q Qp (initOom s0) := by
  have hpc0 : s0.pc = (blkPl_521).base := hs0.pc
  have hrun0 := hs0.run; have hal0 := hs0.spAligned
  have hx0 := hs0.x0; have hx1 := hs0.x1; have hx2 := hs0.x2; have hx3 := hs0.x3
  have hx4 := hs0.x4; have hx5 := hs0.x5; have hx6 := hs0.x6; have hx7 := hs0.x7
  have hx8 := hs0.x8; have hfs0 := hs0.files
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  dsimp only [initEntryMemPlaced']
  rw [coinsInstalledPlaced_eq_cursorZero,
    stackAt_entry_split s0 (stk_ge_frame hstk) hstk64]
  refine sepWPp_mono_pre (P' :=
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        memRegion (s0.sp - 0x60#64) 0x60 ∗
        memRegion fsp initLocalsSize ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        FromRecordCallees.lsLogOff ∗ A.pool ∗
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
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        FromRecordCallees.lsLogOff ∗ A.pool ∗
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
  refine sepWPp_with_rodata (rodata_idVt_trustSlot_placed hStore hs0.inv) ?_
  generalize hshimA : lsmpl.base 601 = shimAddr
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_placed shimAddr hs0.inv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sShim hsShim hpcS hrunS hinvS
  subst hshimA
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
  have hlrS : sShim.readReg64 .lr = initPcPlaced 0x009c := by
    rw [← hsShim]
    change _ = (blkPl_521).base + 156#64
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
  change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sShim _ Q Qp (initOom s0)
  refine initCallLscro hh hpanic hStore.idTrustShim (gx := shimArg)
    (F := cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      memRegion fsp 0xd0 ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      storesAt A x.stores StoresGhost.opened ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      FromRecordCallees.lsLogOff ∗ initSaved s0 ∗
      initArgsAtPlaced fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8))
    hpcS hrunS halS hinvS htrS hfsS hlrS ?_ (fun _ => Entails.refl _) ?_
  · unfold initSaved initArgsAtPlaced
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
    refine pure_sepConj_intro ⟨hx0S, hx1S, hx2S, hx3S⟩ ?_
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hpackB
          (sepConj_mono (prologue_low_d0_merge_sp s0.sp)
            (sepConj_mono_left (prologue_high_5ba_merge_sp s0.sp))))))
    sep_frame
  intro sAfterShim hpcAS hrunAS hspAS hcsAS hinvAS hfsAS
  dsimp only [shimArg]
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨hvtAS, _hfutNZ, _hfutAl, htrAS⟩ => ?_
  have htrAS' : sAfterShim.trace = s0.trace := htrAS.trans htrS
  have hfsAS' : sAfterShim.fs.files = s0.fs.files := hfsAS htrAS'
  have hspAS' : sAfterShim.sp = fsp := hspAS.trans hspS
  have hctrlAS : InInitiatePlaced s0 sAfterShim 0x009c :=
    ⟨hpcAS, hrunAS, hspAS', (cs_fp hcsAS).trans hfpS, (cs_x19 hcsAS).trans hx19S,
      hfsAS', hinvAS, (cs_vregs hcsAS).trans hvregsS, hal0⟩
  rw [hspS]
  refine sepWPp_mono_pre (P' := afterTrustShimMemPlaced A x stk s0 sAfterShim)
    (by unfold afterTrustShimMemPlaced; dsimp only [fsp]; sep_frame) ?_
  exact hnext sAfterShim h1 h2 h3 hctrlAS htrAS' hvtAS

/-- Spatial state at `0x00b8` after `idTrustPoll` returns and its 48-byte `sret` is unpacked. -/
def afterTrustPollMemPlaced [LibsignalPlacement] (A : RustAlloc) (x : InitGhost) (stk : Nat)
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
      FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗
    (A.live futPtr 32 8 ∗
      dirAt A x.stores StoresGhost.opened.identity.own ∗
      dirAt A (x.stores + 0x50#64) StoresGhost.opened.signed ∗
      dirAt A (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
      dirAt A (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
      dirAt A (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      dirAt A (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      dirAt A (x.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A x.me x.meA ∗
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      bundleRestAt x opkId2 ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      initSaved s0 ∗ initArgsAtPlaced fsp x s0 ∗
      memRegion fsp 0xd0 ∗ memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) 6 ∗
      ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
      ((fsp + 0x5c8#64) ↦₆₄ lsρ idTrustFutVtSym) ∗
      memRegion (fsp + 0x5d0#64) (0x1600 - 0x5d0) ∗
      memRegion (fsp + 0x1630#64) (initLocalsSize - 0x1630))

set_option maxHeartbeats 1200000 in
/-- Branches on trust boolean `tb` (`0x0144 → 0x0154` on `true`, `0x0244` on `false`). -/
theorem stage1_trust_branch_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sAfterDealloc : State}
    {tb : Bool} {w_tb : BitVec 64}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryPlaced x s0)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrlAF : InInitiatePlaced s0 sAfterDealloc 0x0144)
    (htrAF' : sAfterDealloc.trace = s0.trace)
    (hx26AF : sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64)
    (hx27AF : sAfterDealloc.readReg64 (.gpr 27#5) = w_tb)
    (hw_tb : BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8))
    (htb2 : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok tb)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      InInitiatePlaced s0 s1 0x0154 →
      s1.trace = s0.trace →
      s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s1
        (stage2MemPlaced A x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterDealloc
      (stage2MemPlaced A x stk s0) Q Qp (initOom s0) := by
  have hx8 := hs0.x8; have hfs0 := hs0.files; have hal0 := hs0.spAligned
  have hpcAF : sAfterDealloc.pc = (blkPl_521).base + 324#64 := hctrlAF.pc
  have hrunAF := hctrlAF.run; have hspAF' := hctrlAF.sp
  have hfpAF := hctrlAF.fp; have hx19AF := hctrlAF.x19; have hfsAF' := hctrlAF.files0
  have hinvAF := hctrlAF.inv; have hvregsAF := hctrlAF.vregs
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  cases tb
  · have hbit0 : w_tb.getLsbD 0 = false := getLsbD0_of_extract8_zero hw_tb
    have hbit : w_tb.extractLsb' 0 1 = 0#1 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hi0 : i = 0 := by omega
      subst hi0; simpa using hbit0
    have hb0 : w_tb[0] = false := hbit0
    refine sepWPp_step_to_placed ((blkPl_521).base + 580#64) hinvAF ?_
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
    have hctrlU : InInitiatePlaced s0 sU 0x0244 :=
      ⟨hpcU, hrunU, hspU, hfpU, hx19U, hfsU, hinvU, hvregsU, hal0⟩
    exact stage1_untrusted_exit_placed_ok hh hS hstk hstk64 hx8 hctrlU hx21U htrU htb2 hpost hpanic
  · have hbit0 : w_tb.getLsbD 0 = true := getLsbD0_of_extract8_one hw_tb
    have hbit : w_tb.extractLsb' 0 1 = 1#1 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have hi0 : i = 0 := by omega
      subst hi0; simpa using hbit0
    have hb0 : w_tb[0] = true := hbit0
    refine sepWPp_step_to_placed ((blkPl_521).base + 340#64) hinvAF ?_
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
    clear hs1
    have hctrl1 : InInitiatePlaced s0 s1 0x0154 :=
      ⟨hpc1, hrun1, hsp1, hfp1, hx19_1, hfs1.trans hfs0.symm, hinv1, hvregs1, hal0⟩
    exact hnext s1 h1 h2 h3 hctrl1 htr1 hfs1 htb2

set_option maxHeartbeats 1600000 in
/-- Optional `futDrop`, `__rust_dealloc(32, 8)`, and `stage2MemPlaced` packing (`0x00b8 → 0x0144`). -/
theorem stage1_trust_drop_dealloc_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sAfterPoll : State}
    {futPtr : BitVec 64} {opkId2 : BitVec 32}
    {w_tb o2 o3 o4 o5 : BitVec 64}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hopk2 : ∀ p, x.bundle.opk = some p → opkId2 = p.1)
    (hctrlAP : InInitiatePlaced s0 sAfterPoll 0x00b8)
    (htrAP' : sAfterPoll.trace = s0.trace)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sAfterDealloc : State,
      InInitiatePlaced s0 sAfterDealloc 0x0144 →
      sAfterDealloc.trace = s0.trace →
      sAfterDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 →
      sAfterDealloc.readReg64 (.gpr 27#5) = w_tb →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterDealloc
        (stage2MemPlaced A x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterPoll
      (afterTrustPollMemPlaced A x stk s0 futPtr opkId2 w_tb o2 o3 o4 o5) Q Qp (initOom s0) := by
  have hpcAP : sAfterPoll.pc = (blkPl_521).base + 184#64 := hctrlAP.pc
  have hrunAP := hctrlAP.run; have hspAP' := hctrlAP.sp
  have hfpAP := hctrlAP.fp; have hx19AP := hctrlAP.x19; have hfsAP' := hctrlAP.files0
  have hinvAP := hctrlAP.inv; have hvregsAP := hctrlAP.vregs; have hal0 := hctrlAP.spAligned
  have halAP := spAligned_of_frame hal0 hspAP'
  unfold afterTrustPollMemPlaced; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hspAP' ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hspAP'] using halAP
  let PpostPoll : SepProp :=
    (((fsp + 0x1600#64) ↦₆₄ (0#64 - 2#64)) ∗
        ((fsp + 0x1608#64) ↦₆₄ w_tb) ∗
        ((fsp + 0x1610#64) ↦₆₄ o2) ∗ ((fsp + 0x1618#64) ↦₆₄ o3) ∗
        ((fsp + 0x1620#64) ↦₆₄ o4) ∗ ((fsp + 0x1628#64) ↦₆₄ o5)) ∗
      (idTrustBoxAt futPtr x.stores x.peerA (x.bundleA + 120#64) 1#8 0#8 ∗
        dirAt A (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
        protocolAddressAt A x.peer x.peerA ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        FromRecordCallees.lsLogOff ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame)) ∗
      (A.live futPtr 32 8 ∗
        dirAt A x.stores StoresGhost.opened.identity.own ∗
        dirAt A (x.stores + 0x50#64) StoresGhost.opened.signed ∗
        dirAt A (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
        dirAt A (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
        dirAt A (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A x.me x.meA ∗
        coinsCursorAtPlaced x.coinsP x.coins 0 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        bundleRestAt x opkId2 ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        initSaved s0 ∗ initArgsAtPlaced fsp x s0 ∗
        memRegion fsp 0xd0 ∗ memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 6 ∗
        ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ idTrustFutVtSym) ∗
        memRegion (fsp + 0x5d0#64) (0x1600 - 0x5d0) ∗
        memRegion (fsp + 0x1630#64) (initLocalsSize - 0x1630))
  suffices h0130 : ∀ sAfterDrop : State,
      sAfterDrop.pc = (blkPl_521).base + 304#64 →
      sAfterDrop.status = .Running →
      sAfterDrop.sp = fsp →
      sAfterDrop.readReg64 (.gpr 20#5) = futPtr →
      sAfterDrop.readReg64 (.gpr 22#5) = lsρ idTrustFutVtSym →
      sAfterDrop.readReg64 (.gpr 26#5) = 0#64 - 2#64 →
      sAfterDrop.readReg64 (.gpr 27#5) = w_tb →
      sAfterDrop.readReg64 .fp = s0.sp - 0x60#64 →
      sAfterDrop.readReg64 (.gpr 19#5) = s0.readReg64 .x8 →
      calleeSavedVRegs sAfterDrop = calleeSavedVRegs s0 →
      sAfterDrop.trace = s0.trace →
      sAfterDrop.fs.files = s0.fs.files →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sAfterDrop.mem →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterDrop PpostPoll Q Qp (initOom s0) by
    refine sepWPp_with_rodata (rodata_idTrustFut_drop_placed' hinvAP) ?_
    by_cases hdz0 : lsmpl.base 547 = 0#64
    · rw [hdz0]
      dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
      refine sepWPp_step_to_placed ((blkPl_521).base + 304#64) hinvAP ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro sAD hsAD hpcAD hrunAD hinvAD
      refine sepWPp_drop_left ?_
      have hspAD : sAD.sp = fsp := by rw [← hsAD]; simp [wp_norm, arm64_norm, hspAP']
      have hx20AD : sAD.readReg64 (.gpr 20#5) = futPtr := by rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hx22AD : sAD.readReg64 (.gpr 22#5) = lsρ idTrustFutVtSym := by
        rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hx26AD : sAD.readReg64 (.gpr 26#5) = 0#64 - 2#64 := by
        rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hx27AD : sAD.readReg64 (.gpr 27#5) = w_tb := by
        rw [← hsAD]; simp [wp_norm, arm64_norm]
      have hfpAD : sAD.readReg64 .fp = s0.sp - 0x60#64 := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hfpAP]
      have hx19AD : sAD.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hx19AP]
      have hvregsAD : calleeSavedVRegs sAD = calleeSavedVRegs s0 := by
        rw [← hsAD]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAP]
      have htrAD : sAD.trace = s0.trace := by rw [← hsAD]; simp [wp_norm, arm64_norm, htrAP']
      have hfsAD : sAD.fs.files = s0.fs.files := by
        rw [← hsAD]; simp [wp_norm, arm64_norm, hfsAP']
      clear hsAD
      exact h0130 sAD hpcAD hrunAD hspAD hx20AD hx22AD hx26AD hx27AD hfpAD hx19AD hvregsAD htrAD
        hfsAD hinvAD
    · have hdz : (lsmpl.base 547 == 0#64) = false := beq_eq_false_iff_ne.2 hdz0
      generalize hdropA : lsmpl.base 547 = dropAddr at hdz ⊢
      dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
      refine sepWPp_step_to_placed dropAddr hinvAP ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro sDrop hsDrop hpcD hrunD hinvD
      subst hdropA
      refine sepWPp_drop_left ?_
      have hspD : sDrop.sp = fsp := by rw [← hsDrop]; simp [wp_norm, arm64_norm, hspAP']
      have hlrD : sDrop.readReg64 .lr = initPcPlaced 0x0130 := by
        rw [← hsDrop]
        change _ = (blkPl_521).base + 304#64
        simp [wp_norm, arm64_norm]; try bv_omega
      have hx20D : sDrop.readReg64 (.gpr 20#5) = futPtr := by
        rw [← hsDrop]; simp [wp_norm, arm64_norm]
      have hx22D : sDrop.readReg64 (.gpr 22#5) = lsρ idTrustFutVtSym := by
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
      change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sDrop PpostPoll Q Qp (initOom s0)
      refine initCallLscro hh hpanic hStore.futDrop (gx := ()) (F := PpostPoll)
        hpcD hrunD halD hinvD htrD hfsD hlrD
        (by unfold futDropSpec; rw [emp_sepConj]; exact Entails.refl _) (fun _ => false_entails _) ?_
      intro sAfterDrop hpcAD hrunAD hspAD hcsAD hinvAD hfsAD
      unfold futDropSpec; dsimp only
      refine sepWPp_pure_elim fun htrAD => ?_
      have htrAD' : sAfterDrop.trace = s0.trace := htrAD.trans htrD
      exact h0130 sAfterDrop hpcAD hrunAD (hspAD.trans hspD)
        ((cs_x20 hcsAD).trans hx20D) ((cs_x22 hcsAD).trans hx22D)
        ((cs_x26 hcsAD).trans hx26D) ((cs_x27 hcsAD).trans hx27D)
        ((cs_fp hcsAD).trans hfpD) ((cs_x19 hcsAD).trans hx19D)
        ((cs_vregs hcsAD).trans hvregsD) htrAD' (hfsAD htrAD') hinvAD
  intro sAfterDrop hpcAD hrunAD hspAD' hx20AD hx22AD hx26AD hx27AD hfpAD hx19AD hvregsAD htrAD' hfsAD' hinvAD
  dsimp only [PpostPoll]
  refine sepWPp_with_rodata (rodata_idTrustFut_size_placed' hinvAD) ?_
  refine sepWPp_with_rodata (rodata_idTrustFut_align_placed' hinvAD) ?_
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_placed (lsρ lsRustDeallocSymCli) hinvAD ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sDealloc hsDealloc hpcF hrunF hinvF
  refine sepWPp_drop_left (sepWPp_drop_left ?_)
  have hspF : sDealloc.sp = fsp := by rw [← hsDealloc]; simp [wp_norm, arm64_norm, hspAD']
  have hx0F : sDealloc.readReg64 .x0 = futPtr := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, hx20AD]
  have hx1F : (sDealloc.readReg64 .x1).toNat = 32 := by rw [← hsDealloc]; simp [wp_norm, arm64_norm]
  have hx2F : (sDealloc.readReg64 .x2).toNat = 8 := by rw [← hsDealloc]; simp [wp_norm, arm64_norm]
  have hlrF : sDealloc.readReg64 .lr = initPcPlaced 0x0144 := by
    rw [← hsDealloc]
    change _ = (blkPl_521).base + 324#64
    simp [wp_norm, arm64_norm]; try bv_omega
  have hx26F : sDealloc.readReg64 (.gpr 26#5) = 0#64 - 2#64 := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, hx26AD]
  have hx27F : sDealloc.readReg64 (.gpr 27#5) = w_tb := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, hx27AD]
  have hfpF : sDealloc.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, hfpAD]
  have hx19F : sDealloc.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, hx19AD]
  have hvregsF : calleeSavedVRegs sDealloc = calleeSavedVRegs s0 := by
    rw [← hsDealloc]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregsAD]
  have htrF : sDealloc.trace = s0.trace := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, htrAD']
  have hfsF : sDealloc.fs.files = s0.fs.files := by
    rw [← hsDealloc]; simp [wp_norm, arm64_norm, hfsAD']
  clear hsDealloc
  have halF : sDealloc.spAligned = true := spAligned_of_sp_eq halAP (hspF.trans hspAP'.symm)
  have hdealloc := init_dealloc_placed_ok_at (mmpl := mmpl) (gh := gh) (W := W) (B := B) hh hstk hstk64
  have hpcF' : sDealloc.pc = lsρ lsRustDeallocSymCli := hpcF
  let frameNoPool : SepProp :=
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      storesAt A x.stores StoresGhost.opened ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      FromRecordCallees.lsLogOff ∗ initSaved s0 ∗
      memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)
  change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sDealloc _ Q Qp (initOom s0)
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
          ((fsp + 0x5c8#64) ↦₆₄ lsρ idTrustFutVtSym) ∗
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
        (poll_frame_5ba_merge fsp futPtr (lsρ idTrustFutVtSym) 48 (by decide))
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro ⟨hx0F, hx1F, hx2F, ⟨by decide, ⟨3, rfl⟩, by decide⟩⟩ ?_
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hboxMem (sepConj_mono_right (sepConj_mono hpackB (sepConj_mono_left hmergePoll48))))))
    sep_frame
  refine initCallLscro hh hpanic hdealloc hpcF' hrunF halF hinvF htrF hfsF hlrF
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
  refine sepWPp_mono_pre (P' := stage2MemPlaced A x stk s0) ?_ ?_
  · unfold stage2MemPlaced
    dsimp only [frameNoPool]
    rw [hspF, ← hfsp]
    sep_frame
  have hctrlAF : InInitiatePlaced s0 sAfterDealloc 0x0144 :=
    ⟨hpcAF, hrunAF, hspAF'.trans hfsp.symm, hfpAF, hx19AF, hfsAF', hinvAF, hvregsAF, hal0⟩
  exact hnext sAfterDealloc hctrlAF htrAF' hx26AF hx27AF

set_option maxHeartbeats 1200000 in
/-- `idTrustPoll` invocation and 48-byte `sret` unpacking (`0x009c → 0x00b8`). -/
theorem stage1_trust_to_poll_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sAfterShim : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hs0 : AtInitEntryPlaced x s0)
    (hctrlAS : InInitiatePlaced s0 sAfterShim 0x009c)
    (htrAS' : sAfterShim.trace = s0.trace)
    (hvtAS : sAfterShim.readReg64 (.gpr 1#5) = lsρ idTrustFutVtSym)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sAfterPoll : State) (futPtr : BitVec 64) (opkId2 : BitVec 32)
      (tb : Bool) (w_tb o2 o3 o4 o5 : BitVec 64),
      (∀ p, x.bundle.opk = some p → opkId2 = p.1) →
      InInitiatePlaced s0 sAfterPoll 0x00b8 →
      sAfterPoll.trace = s0.trace →
      BitVec.extractLsb' 0 8 w_tb = (if tb then 1#8 else 0#8) →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok tb →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterPoll
        (afterTrustPollMemPlaced A x stk s0 futPtr opkId2 w_tb o2 o3 o4 o5) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterShim
      (afterTrustShimMemPlaced A x stk s0 sAfterShim) Q Qp (initOom s0) := by
  have hfs0 := hs0.files; have hal0 := hs0.spAligned
  have hpcAS : sAfterShim.pc = (blkPl_521).base + 156#64 := hctrlAS.pc
  have hrunAS := hctrlAS.run; have hspAS' := hctrlAS.sp
  have hfpAS := hctrlAS.fp; have hx19AS := hctrlAS.x19; have hfsAS' := hctrlAS.files0
  have hinvAS := hctrlAS.inv; have hvregsAS := hctrlAS.vregs
  have halAS := spAligned_of_frame hal0 hspAS'
  unfold afterTrustShimMemPlaced; dsimp only
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
  have hx1AS : sAfterShim.readReg64 (.gpr 1#5) = lsρ idTrustFutVtSym := hvtAS
  refine sepWPp_with_rodata (rodata_idTrustFut_poll_placed' hinvAS) ?_
  generalize hpollA : lsmpl.base 566 = pollAddr
  dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521]
  refine sepWPp_step_to_placed pollAddr hinvAS ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sPoll hsPoll hpcP hrunP hinvP
  subst hpollA
  refine sepWPp_drop_left ?_
  have hspP : sPoll.sp = fsp := by rw [← hsPoll]; simp [wp_norm, arm64_norm, hspAS']
  have hx0P : sPoll.readReg64 .x0 = futPtr := by rw [← hsPoll]; simp [futPtr, wp_norm, arm64_norm]
  have hx8P : sPoll.readReg64 .x8 = fsp + 0x1600#64 := by
    rw [← hsPoll]; simp [wp_norm, arm64_norm]; try bv_omega
  have hlrP : sPoll.readReg64 .lr = initPcPlaced 0x00b8 := by
    rw [← hsPoll]
    change _ = (blkPl_521).base + 184#64
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
  change SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sPoll _ Q Qp (initOom s0)
  refine initCallLscro hh hpanic hStore.idTrustPoll (gx := (pollGhost, 0#8))
    (F := A.live futPtr 32 8 ∗
      dirAt A x.stores StoresGhost.opened.identity.own ∗
      dirAt A (x.stores + 0x50#64) StoresGhost.opened.signed ∗
      dirAt A (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
      dirAt A (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
      dirAt A (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
      dirAt A (x.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      dirAt A (x.stores + 0x118#64) StoresGhost.opened.pub ∗
      protocolAddressAt A x.me x.meA ∗
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      bundleRestAt x opkId2 ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      initSaved s0 ∗ initArgsAtPlaced fsp x s0 ∗
      memRegion fsp 0xd0 ∗ memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) 6 ∗
      ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
      ((fsp + 0x5c8#64) ↦₆₄ lsρ idTrustFutVtSym) ∗
      memRegion (fsp + 0x5d0#64) (0x1600 - 0x5d0) ∗
      memRegion (fsp + 0x1630#64) (initLocalsSize - 0x1630))
    hpcP hrunP halP hinvP htrP hfsP hlrP ?_ (fun _ => Entails.refl _) ?_
  · unfold storesAt cliBundleBody bundleRestAt
    dsimp only [pollGhost, futPtr, Reg.x0]
    rw [hspP]
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro
      ⟨hx0P, hx8P, hinitOk.nameLt, by
        dsimp only [StoresGhost.opened, DirGhost.new]
        have h := hinitOk.idPathLt; unfold pathOf at h
        split at h
        · rename_i heq; rw [heq]; dsimp; omega
        · simp only [List.length_append] at h; omega,
        ⟨hinitOk.idPathOk, hinitOk.idPathLt⟩, hpeersGet⟩ ?_
    rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
  intro sAfterPoll hpcAP hrunAP hspAP hcsAP hinvAP hfsAP
  dsimp only [pollGhost]
  rw [sepConj_assoc]; refine sepWPp_exists_left fun gr => ?_
  refine sepWPp_exists_left fun p => ?_
  rw [sepConj_assoc]; refine sepWPp_pure_elim fun ⟨⟨hgr, htrAP⟩, hp⟩ => ?_
  have htrAP' : sAfterPoll.trace = s0.trace := htrAP.trans htrP
  have hfsAP' : sAfterPoll.fs.files = s0.fs.files := hfsAP htrAP'
  rw [hfsP, hfs0] at hgr
  obtain ⟨tb, htb1, htb2⟩ := idTrust_always_ok hinitOk hgr hp
  rw [htb1, idTrustOutAt_ok A 0#64]
  have houtCells :
      trustPollOutAt 0#64 (fsp + 0x1600#64) (.ok tb) ⊢
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
  have hctrlAP : InInitiatePlaced s0 sAfterPoll 0x00b8 :=
    ⟨hpcAP, hrunAP, (hspAP.trans hspP).trans hfsp.symm, (cs_fp hcsAP).trans hfpP,
      (cs_x19 hcsAP).trans hx19P, hfsAP', hinvAP, (cs_vregs hcsAP).trans hvregsP, hal0⟩
  refine sepWPp_mono_pre
    (P' := afterTrustPollMemPlaced A x stk s0 futPtr opkId2 w_tb o2 o3 o4 o5)
    (by unfold afterTrustPollMemPlaced; dsimp only; rw [hspP, ← hfsp]; sep_frame) ?_
  exact hnext sAfterPoll futPtr opkId2 tb w_tb o2 o3 o4 o5 hopk2 hctrlAP htrAP' hw_tb htb2

/-- `idTrustPoll`, `futDrop`, `dealloc`, and trust branch (`0x009c → 0x0154`). -/
theorem stage1_trust_poll_drop_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 sAfterShim : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryPlaced x s0)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrlAS : InInitiatePlaced s0 sAfterShim 0x009c)
    (htrAS' : sAfterShim.trace = s0.trace)
    (hvtAS : sAfterShim.readReg64 (.gpr 1#5) = lsρ idTrustFutVtSym)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      InInitiatePlaced s0 s1 0x0154 →
      s1.trace = s0.trace →
      s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s1
        (stage2MemPlaced A x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sAfterShim
      (afterTrustShimMemPlaced A x stk s0 sAfterShim) Q Qp (initOom s0) :=
  stage1_trust_to_poll_placed_ok hh hStore hinitOk hs0 hctrlAS htrAS' hvtAS hpanic
    fun _ _ _ _ _ _ _ _ _ hopk2 hctrlAP htrAP' hw_tb htb2 =>
      stage1_trust_drop_dealloc_placed_ok hh hStore hstk hstk64 h1 h2 h3 hopk2 hctrlAP htrAP' hpanic
        fun _ hctrlAF htrAF' hx26AF hx27AF =>
          stage1_trust_branch_placed_ok hh hS hstk hstk64 hs0 h1 h2 h3 hctrlAF htrAF'
            hx26AF hx27AF hw_tb htb2 hpost hpanic hnext

/-- Prologue and `is_trusted_identity` (`0x0000 → 0x0154` and untrusted exit). -/
theorem stage1_prologue_trust_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtInitEntryPlaced x s0)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s1 : State)
      (_h1 : x.bundle.spkSig.length = 64)
      (_h2 : x.bundle.kpkSig.length = 64)
      (_h3 : x.bundle.kpk.length = 1568),
      InInitiatePlaced s0 s1 0x0154 →
      s1.trace = s0.trace →
      s1.fs.files = x.F →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s1
        (stage2MemPlaced A x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s0
      (initEntryMemPlaced' A x stk s0) Q Qp (initOom s0) :=
  stage1_prologue_to_shim_placed_ok hh hStore hstk hstk64 hs0 hpanic
    fun _ h1 h2 h3 hctrlAS htrAS' hvtAS =>
      stage1_trust_poll_drop_placed_ok hh hStore hS hinitOk hstk hstk64 hs0
        h1 h2 h3 hctrlAS htrAS' hvtAS hpost hpanic hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
