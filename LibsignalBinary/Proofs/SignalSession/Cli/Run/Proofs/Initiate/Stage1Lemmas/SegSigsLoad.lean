/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrust
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 1 Segment 4 (`0x01fc → 0x0390`): `load_session(peer)` and Stage 2 Handoff

Verifies `stage1_load_session_ok` and `stage1_load_session_ext_ok`: invokes `sessLoadShim`,
`sessLoadPoll`, `memcpy(312)`, `futDrop`, and `__rust_dealloc(24, 8)`, resolves `InitOk₀.noSession`
to `ans = .ok none` (`x22 = -1`), and establishes `AtStage2` and `stage2Mem` at `0x0390`.
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

/-- Splits `[sp + 0x5ba, sp + initLocalsSize)` into future slots (`+0x5c0`, `+0x5c8`), 312-byte record slot (`+0x5f8`), and 368-byte `sret` (`+0x1600`). -/
theorem load_frame_5ba_split (sp : BitVec 64) :
    memRegion (sp + 0x5ba#64) (initLocalsSize - 0x5ba) =
      memRegion (sp + 0x5ba#64) 6 ∗
        (∃∗ f0 : BitVec 64, (sp + 0x5c0#64) ↦₆₄ f0) ∗
        (∃∗ f1 : BitVec 64, (sp + 0x5c8#64) ↦₆₄ f1) ∗
        memRegion (sp + 0x5d0#64) 40 ∗
        memRegion (sp + 0x5f8#64) 312 ∗
        memRegion (sp + 0x730#64) (0x1600 - 0x730) ∗
        memRegion (sp + 0x1600#64) 368 ∗
        memRegion (sp + 0x1770#64) (initLocalsSize - 0x1770) := by
  rw [show initLocalsSize - 0x5ba =
        6 + (8 + (8 + (40 + (312 + ((0x1600 - 0x730) + (368 + (initLocalsSize - 0x1770))))))) by decide,
      memRegion_split (sp + 0x5ba#64) 6 _ (by decide),
      memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
      memRegion_split _ 8 _ (by decide), ProofLib.memRegion_eight,
      memRegion_split _ 40 _ (by decide),
      memRegion_split _ 312 _ (by decide),
      memRegion_split _ (0x1600 - 0x730) _ (by decide),
      memRegion_split _ 368 _ (by decide)]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]

/-- Merges `[sp + 0x5ba, sp + initLocalsSize)` back after `sessLoadPoll` and `memcpy(312)`. -/
theorem load_frame_5ba_merge (sp : BitVec 64) (f0 f1 : BitVec 64) :
    memRegion (sp + 0x5ba#64) 6 ∗
      ((sp + 0x5c0#64) ↦₆₄ f0) ∗
      ((sp + 0x5c8#64) ↦₆₄ f1) ∗
      memRegion (sp + 0x5d0#64) 40 ∗
      memRegion (sp + 0x5f8#64) 312 ∗
      memRegion (sp + 0x730#64) (0x1600 - 0x730) ∗
      memRegion (sp + 0x1600#64) 368 ∗
      memRegion (sp + 0x1770#64) (initLocalsSize - 0x1770) ⊢
      memRegion (sp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
  rw [load_frame_5ba_split sp]
  sep_frame

@[irreducible] def sessLoadShimAddr_ext (img : Obj.Image)
    (ext : String → Option (State → State)) : BitVec 64 :=
  (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr sessLoadShimName

theorem sessLoadShimAddr_ext_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    sessLoadShimAddr_ext img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr sessLoadShimName := by
  unfold sessLoadShimAddr_ext; rfl

theorem rodata_sessVt_loadSlot_irr_ext {img : Obj.Image}
    {ext : String → Option (State → State)} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((sessVt img + 24#64) ↦₆₄ᵣ sessLoadShimAddr_ext img ext) ∗ R) := by
  rw [sessLoadShimAddr_ext_eq]; exact rodata_sessVt_loadSlot_ext (ext := ext) himg hF

@[irreducible] def sessLoadShimAddr (img : Obj.Image) (W : CliHooks) : BitVec 64 :=
  (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr sessLoadShimName

theorem sessLoadShimAddr_eq (img : Obj.Image) (W : CliHooks) :
    sessLoadShimAddr img W =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr sessLoadShimName := by
  unfold sessLoadShimAddr; rfl

theorem rodata_sessVt_loadSlot_irr {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((sessVt img + 24#64) ↦₆₄ᵣ sessLoadShimAddr img W) ∗ R) := by
  rw [sessLoadShimAddr_eq]; exact rodata_sessVt_loadSlot (W := W) himg hF

@[irreducible] def sessLoadPollAddr_ext (img : Obj.Image)
    (ext : String → Option (State → State)) : BitVec 64 :=
  (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr sessLoadPollName

theorem sessLoadPollAddr_ext_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    sessLoadPollAddr_ext img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr sessLoadPollName := by
  unfold sessLoadPollAddr_ext; rfl

theorem rodata_sessLoadFut_poll_irr_ext {img : Obj.Image}
    {ext : String → Option (State → State)} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + sessLoadFutVtOff) + 24#64) ↦₆₄ᵣ sessLoadPollAddr_ext img ext) ∗ R) := by
  rw [sessLoadPollAddr_ext_eq]; exact rodata_sessLoadFut_poll_ext (ext := ext) himg hF

theorem rodata_sessLoadFut_drop_irr_ext {img : Obj.Image}
    {ext : String → Option (State → State)} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((img.base + sessLoadFutVtOff) ↦₆₄ᵣ futDropAddr_ext img ext) ∗ R) := by
  rw [futDropAddr_ext_eq]; exact rodata_sessLoadFut_drop_ext (ext := ext) himg hF

@[irreducible] def sessLoadPollAddr (img : Obj.Image) (W : CliHooks) : BitVec 64 :=
  (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExterns W))).fnAddr sessLoadPollName

theorem sessLoadPollAddr_eq (img : Obj.Image) (W : CliHooks) :
    sessLoadPollAddr img W =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr sessLoadPollName := by
  unfold sessLoadPollAddr; rfl

theorem rodata_sessLoadFut_poll_irr {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ (((img.base + sessLoadFutVtOff) + 24#64) ↦₆₄ᵣ sessLoadPollAddr img W) ∗ R) := by
  rw [sessLoadPollAddr_eq]; exact rodata_sessLoadFut_poll (W := W) himg hF

theorem rodata_sessLoadFut_drop_irr {img : Obj.Image} {W : CliHooks} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    ∀ R, (s.mem ⊨ R) →
      (s.mem ⊨ ((img.base + sessLoadFutVtOff) ↦₆₄ᵣ futDropAddr img W) ∗ R) := by
  rw [futDropAddr_eq]; exact rodata_sessLoadFut_drop (W := W) himg hF

set_option maxHeartbeats 3200000 in
/-- `load_session(peer)` to `AtStage2Ext` (`0x01fc → 0x0390`, `initProgExt`). -/
theorem stage1_load_session_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hbe : bundleEOf? x.bundle = some be)
    (hctrl : InInitiateExt img ext s0 s3 0x01fc)
    (htr : s3.trace = s0.trace)
    (hfs : s3.fs.files = x.F)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hsigs : PreKeyBundleFields.signaturesVerify X P be = true)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (be' : PreKeyBundleFields),
      AtStage2Ext img P ext X x be' s0 s4 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s4
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
      (stage2Mem A img x stk s0) Q Qp (initOom s0) := by
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage1Bin img.base
    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 0x01fc 0x0194
  have hpc3 := hctrl.pc; have hrun3 := hctrl.run; have hsp3 := hctrl.sp
  have hfp3 := hctrl.fp; have hx19_3 := hctrl.x19; have hfs30 := hctrl.files0
  have hvregs3 := hctrl.vregs; have hal0 := hctrl.spAligned
  have hal3 := inInitiateExt_spAligned_cur hctrl
  unfold stage2Mem; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hsp3 ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp3] using hal3
  unfold initArgsAt
  have hent : initEntryExt img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc3 ⊢
  try simp only [BitVec.ofNat_eq_ofNat] at hpc3
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  examples_hide_fetches
  have hdz := futDropAddr_ext_ne_zero (ext := ext) himg
  refine sepWPp_with_rodata (rodata_sessVt_loadSlot_irr_ext (ext := ext) himg hctrl.inv.1) ?_
  refine sepWPp_step_to (sessLoadShimAddr_ext img ext) hctrl.inv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sShim hsShim hpcS hrunS hinvS
  rw [sessLoadShimAddr_ext_eq] at hpcS
  refine sepWPp_drop_left ?_
  have hspS : sShim.sp = fsp := by rw [← hsShim]; simp [wp_norm, arm64_norm, hsp3]
  have hx0S : sShim.readReg64 .x0 = x.stores + 0xf0#64 := by
    rw [← hsShim]; simp [wp_norm, arm64_norm, hsp3]
  have hx1S : sShim.readReg64 .x1 = x.peerA := by
    rw [← hsShim]; simp [wp_norm, arm64_norm, hsp3]
  have hlrS : sShim.readReg64 .lr = initPcExt img ext 0x020c := by
    rw [← hsShim]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm, hpc3]; try bv_omega
  have hfpS : sShim.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsShim]; simp [wp_norm, arm64_norm, hfp3]
  have hx19S : sShim.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsShim]; simp [wp_norm, arm64_norm, hx19_3]
  have hvregsS : calleeSavedVRegs sShim = calleeSavedVRegs s0 := by
    rw [← hsShim]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs3]
  have htrS : sShim.trace = s0.trace := by rw [← hsShim]; simp [wp_norm, arm64_norm, htr]
  have hfsS : sShim.fs.files = s0.fs.files := by rw [← hsShim]; simp [wp_norm, arm64_norm, hfs30]
  clear hsShim
  have halS : sShim.spAligned = true := spAligned_of_sp_eq hal3 (hspS.trans hsp3.symm)
  let loadShimArg : LoadShimCall := { self := x.stores + 0xf0#64, addrA := x.peerA }
  refine sepWPp_mono_pre (P' :=
      ((sessLoadShimSpec A img (stk - cliInitiateFrame)).pre loadShimArg sShim) ∗
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba))) ?_ ?_
  · unfold sessLoadShimSpec Spec.inImage initArgsAt
    dsimp only [loadShimArg]
    rw [hspS]
    repeat rw [sepConj_assoc]
    exact pure_sepConj_intro hinvS (pure_sepConj_intro ⟨hx0S, hx1S⟩ (by sep_frame))
  refine initCall_ext hh hpanic hStore.sessLoadShim hpcS hrunS halS hinvS htrS hfsS hlrS
    (Entails.refl _) (fun _ => Entails.refl _) ?_
  intro sAS hpcAS hrunAS hspAS hcsAS hinvAS hfsAS
  unfold sessLoadShimSpec Spec.inImage
  dsimp only [loadShimArg]
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨hvtAS, hfutNZ, hfutAl, htrAS⟩ => ?_
  have htrAS' : sAS.trace = s0.trace := htrAS.trans htrS
  have hfsAS' : sAS.fs.files = s0.fs.files := hfsAS htrAS'
  have hspAS' : sAS.sp = fsp := hspAS.trans hspS
  rw [hspS]
  refine sepWPp_mono_pre (P' :=
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        A.live (sAS.readReg64 .x0) 24 8 ∗
        sessLoadBoxAt (sAS.readReg64 .x0) (x.stores + 0xf0#64) x.peerA 0#8 ∗
        A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8))
    (by sep_frame) ?_
  rw [load_frame_5ba_split fsp]
  repeat rw [sepConj_assoc]
  refine sepWPp_exists_pos2 fun f0 => ?_
  refine sepWPp_exists_pos3 fun f1 => ?_
  let futPtr := sAS.readReg64 .x0
  have hx1AS : sAS.readReg64 (.gpr 1#5) = img.base + sessLoadFutVtOff := hvtAS
  refine sepWPp_with_rodata (rodata_sessLoadFut_poll_irr_ext (ext := ext) himg hinvAS.1) ?_
  dsimp only [initPcExt] at hpcAS
  rw [hent] at hpcAS
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAS
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to (sessLoadPollAddr_ext img ext) hinvAS ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sPoll hsPoll hpcP hrunP hinvP
  rw [sessLoadPollAddr_ext_eq] at hpcP
  refine sepWPp_drop_left ?_
  have hspP : sPoll.sp = fsp := by rw [← hsPoll]; simp [wp_norm, arm64_norm, hspAS']
  have hx0P : sPoll.readReg64 .x0 = futPtr := by rw [← hsPoll]; simp [futPtr, wp_norm, arm64_norm]
  have hx8P : sPoll.readReg64 .x8 = fsp + 0x1600#64 := by
    rw [← hsPoll]; simp [wp_norm, arm64_norm, hspAS']; try bv_omega
  have hx20P : sPoll.readReg64 (.gpr 20#5) = fsp + 0x1600#64 := by
    rw [← hsPoll]; simp [wp_norm, arm64_norm, hspAS']; try bv_omega
  have hlrP : sPoll.readReg64 .lr = initPcExt img ext 0x0230 := by
    rw [← hsPoll]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm, hpcAS]; try bv_omega
  have hfpP : sPoll.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsPoll]; simp [wp_norm, arm64_norm, cs_fp hcsAS, hfpS]
  have hx19P : sPoll.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsPoll]; simp [wp_norm, arm64_norm, cs_x19 hcsAS, hx19S]
  have hvregsP : calleeSavedVRegs sPoll = calleeSavedVRegs s0 := by
    rw [← hsPoll]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAS, hvregsS]
  have htrP : sPoll.trace = s0.trace := by rw [← hsPoll]; simp [wp_norm, arm64_norm, htrAS']
  have hfsP : sPoll.fs.files = s0.fs.files := by rw [← hsPoll]; simp [wp_norm, arm64_norm, hfsAS']
  clear hsPoll
  have halP : sPoll.spAligned = true := spAligned_of_sp_eq hal3 (hspP.trans hsp3.symm)
  try rw [hspAS']
  try rw [hx1AS]
  let pollGhost : SessLoadPollGhost :=
    { call := { fut := futPtr, out := fsp + 0x1600#64, addr := x.peer, addrA := x.peerA }
      self := x.stores + 0xf0#64
      dir := StoresGhost.opened.sessions }
  have hsessGet : ∀ bs,
      StoresGhost.opened.sessions.get cliIo.rd sPoll.fs.files (addressText x.peer.val) = .ok bs →
      SessFileWf (fun _ => False) bs := by
    intro bs hbs
    rw [hfsP, ← hfs30, hfs, hinitOk.noSession] at hbs
    cases hbs
    exact sessFileWf_false_of_nil
  refine sepWPp_mono_pre (P' :=
      ((sessLoadPollSpec cliIo.rd cliWrOk (fun _ => False) A img (stk - cliInitiateFrame)).pre
        pollGhost sPoll) ∗
      (A.live futPtr 24 8 ∗
        dirAt A x.stores StoresGhost.opened.identity.own ∗
        dirAt A (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
        dirAt A (x.stores + 0x50#64) StoresGhost.opened.signed ∗
        dirAt A (x.stores + 0x78#64) StoresGhost.opened.kyber.oneTime ∗
        dirAt A (x.stores + 0xa0#64) StoresGhost.opened.kyber.lastResort ∗
        dirAt A (x.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
        dirAt A (x.stores + 0x118#64) StoresGhost.opened.pub ∗
        protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 6 ∗
        ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5c8#64) ↦₆₄ (img.base + sessLoadFutVtOff)) ∗
        memRegion (fsp + 0x5d0#64) 40 ∗
        memRegion (fsp + 0x5f8#64) 312 ∗
        memRegion (fsp + 0x730#64) (0x1600 - 0x730) ∗
        memRegion (fsp + 0x1770#64) (initLocalsSize - 0x1770))) ?_ ?_
  · unfold sessLoadPollSpec Spec.inImage storesAt
    dsimp only [pollGhost, futPtr, Reg.x0]
    rw [hspP]
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro hinvP (pure_sepConj_intro
      ⟨hx0P, hx8P, hinitOk.nameLt, hinitOk.textLt, by
        dsimp only [StoresGhost.opened, DirGhost.new]
        have h := hinitOk.sessPathLt; unfold pathOf at h
        split at h
        · rename_i heq; rw [heq]; dsimp; omega
        · simp only [List.length_append] at h; omega,
        ⟨hinitOk.sessPathOk, hinitOk.sessPathLt⟩, hsessGet⟩ ?_)
    sep_frame
  refine initCall_ext hh hpanic hStore.sessLoadPoll hpcP hrunP halP hinvP htrP hfsP hlrP
    (Entails.refl _) (fun _ => Entails.refl _) ?_
  intro sAP hpcAP hrunAP hspAP hcsAP hinvAP hfsAP
  unfold sessLoadPollSpec Spec.inImage
  dsimp only [pollGhost]
  rw [sepConj_assoc]; refine sepWPp_exists_left fun gr => ?_
  refine sepWPp_exists_left fun ans => ?_
  rw [sepConj_assoc]; refine sepWPp_pure_elim fun ⟨⟨hgr, htrAP⟩, hans⟩ => ?_
  have htrAP' : sAP.trace = s0.trace := htrAP.trans htrP
  have hfsAP' : sAP.fs.files = s0.fs.files := hfsAP htrAP'
  have hspAP' : sAP.sp = fsp := hspAP.trans hspP
  have hx20AP : sAP.readReg64 (.gpr 20#5) = fsp + 0x1600#64 := (cs_x20 hcsAP).trans hx20P
  have hansNone : ans = .ok none := by
    rw [hfsP, ← hfs30, hfs, hinitOk.noSession] at hgr
    subst hgr
    exact hans
  rw [hansNone]
  dsimp only [sessLoadOutAt]
  have h360 : memRegion (fsp + 0x1600#64 + 8#64) 360 =
      memRegion (fsp + 0x1608#64) 48 ∗ memRegion (fsp + 0x1638#64) 312 := by
    rw [show (360 : Nat) = 48 + 312 by decide, memRegion_split _ 48 312 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h360, sepConj_assoc, sepConj_assoc, memRegion_48_words (fsp + 0x1608#64)]
  refine sepWPp_exists_pos2 fun m5 => ?_; refine sepWPp_exists_pos2 fun m4 => ?_
  refine sepWPp_exists_pos2 fun m3 => ?_; refine sepWPp_exists_pos2 fun m2 => ?_
  refine sepWPp_exists_pos2 fun m1 => ?_; refine sepWPp_exists_pos2 fun m0 => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [initPcExt] at hpcAP
  rw [hent] at hpcAP
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAP
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to
    (fnBase + bv% (ls_rel% "libsignal_cli_handshake::initiate" "memcpy"))
    hinvAP ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sMc hsMc hpcM hrunM hinvM
  have hspM : sMc.sp = fsp := by rw [← hsMc]; simp [wp_norm, arm64_norm, hspAP']
  have hx0M : sMc.readReg64 .x0 = fsp + 0x5f8#64 := by
    rw [← hsMc]; simp [wp_norm, arm64_norm, hspAP']; try bv_omega
  have hx1M : sMc.readReg64 .x1 = fsp + 0x1638#64 := by
    rw [← hsMc]; simp [wp_norm, arm64_norm, hx20AP]; try bv_omega
  have hx2M : (sMc.readReg64 .x2).toNat = 312 := by
    rw [← hsMc]; simp [wp_norm, arm64_norm]
  have hx22M : sMc.readReg64 (.gpr 22#5) = 0#64 - 1#64 := by
    rw [← hsMc]; simp [wp_norm, arm64_norm]
  have hlrM : sMc.readReg64 .lr = initPcExt img ext 0x02f0 := by
    rw [← hsMc]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm, hpcAP]; try bv_omega
  have hfpM : sMc.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsMc]; simp [wp_norm, arm64_norm, cs_fp hcsAP, hfpP]
  have hx19M : sMc.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsMc]; simp [wp_norm, arm64_norm, cs_x19 hcsAP, hx19P]
  have hvregsM : calleeSavedVRegs sMc = calleeSavedVRegs s0 := by
    rw [← hsMc]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAP, hvregsP]
  have htrM : sMc.trace = s0.trace := by rw [← hsMc]; simp [wp_norm, arm64_norm, htrAP']
  have hfsM : sMc.fs.files = s0.fs.files := by rw [← hsMc]; simp [wp_norm, arm64_norm, hfsAP']
  clear hsMc
  have halM : sMc.spAligned = true := spAligned_of_sp_eq hal3 (hspM.trans hsp3.symm)
  try rw [hspAP']
  have hmcCall := init_memcpyScratch_ok_at_ext (ext := ext) (B := B) (n := 312) hh hstk hstk64
  have h56 :
      ((fsp + 5632#64) ↦₆₄ (0#64 - 1#64)) ∗
        ((fsp + 5640#64) ↦₆₄ m0) ∗ ((fsp + 5648#64) ↦₆₄ m1) ∗
        ((fsp + 5656#64) ↦₆₄ m2) ∗ ((fsp + 5664#64) ↦₆₄ m3) ∗
        ((fsp + 5672#64) ↦₆₄ m4) ∗ ((fsp + 5680#64) ↦₆₄ m5) ⊢
        memRegion (fsp + 0x1600#64) 56 := by
    have hm0 := pointsTo64_entails_memRegion (fsp + 0x1600#64) (0#64 - 1#64)
    have hm48 :
        ((fsp + 5640#64) ↦₆₄ m0) ∗ ((fsp + 5648#64) ↦₆₄ m1) ∗
          ((fsp + 5656#64) ↦₆₄ m2) ∗ ((fsp + 5664#64) ↦₆₄ m3) ∗
          ((fsp + 5672#64) ↦₆₄ m4) ∗ ((fsp + 5680#64) ↦₆₄ m5) ⊢
          memRegion (fsp + 0x1608#64) 48 := by
      rw [memRegion_48_words (fsp + 0x1608#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      sep_frame
    rw [show memRegion (fsp + 0x1600#64) 56 =
          memRegion (fsp + 0x1600#64) 8 ∗ memRegion (fsp + 0x1608#64) 48 from by
        rw [show (56 : Nat) = 8 + 48 by decide, memRegion_split _ 8 48 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]]
    exact sepConj_mono hm0 hm48
  refine sepWPp_mono_pre (P' :=
      ((memcpyScratchSpec 312 (stk - cliInitiateFrame)).pre
        (fsp + 0x5f8#64, fsp + 0x1638#64) sMc) ∗
      (memRegion (fsp + 0x1600#64) 56 ∗
        A.live futPtr 24 8 ∗
        sessLoadBoxAt futPtr (x.stores + 0xf0#64) x.peerA 1#8 ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) 6 ∗
        ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5c8#64) ↦₆₄ (img.base + sessLoadFutVtOff)) ∗
        memRegion (fsp + 0x5d0#64) 40 ∗
        memRegion (fsp + 0x730#64) (0x1600 - 0x730) ∗
        memRegion (fsp + 0x1770#64) (initLocalsSize - 0x1770))) ?_ ?_
  · unfold memcpyScratchSpec storesAt
    try dsimp only [futPtr, Reg.x0]
    try dsimp only
    try rw [hspP]
    rw [hspM]
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro ⟨hx0M, hx1M, hx2M⟩ ?_
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56))))
    sep_frame
  rw [← hent] at hpcM
  refine initCallInImage_ext hh hpanic hmcCall hpcM hrunM halM hinvM htrM hfsM hlrM
    (Entails.refl _) (fun _ => false_entails _) ?_
  intro sAM hpcAM hrunAM hspAM hcsAM hinvAM hfsAM
  unfold memcpyScratchSpec; dsimp only
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun htrAM => ?_
  have htrAM' : sAM.trace = s0.trace := htrAM.trans htrM
  have hfsAM' : sAM.fs.files = s0.fs.files := hfsAM htrAM'
  have hspAM' : sAM.sp = fsp := hspAM.trans hspM
  have hx22AM : sAM.readReg64 (.gpr 22#5) = 0#64 - 1#64 := (cs_x22 hcsAM).trans hx22M
  refine sepWPp_with_rodata (rodata_sessLoadFut_drop_irr_ext (ext := ext) himg hinvAM.1) ?_
  dsimp only [initPcExt] at hpcAM
  rw [hent] at hpcAM
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAM
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to (futDropAddr_ext img ext) hinvAM ?_
  wp_steps
  apply SepWP.done
    (by first | wp_norm_goal | simp only [arm64_norm, wp_norm, hpcAM, hrunAM, hdz])
    (by first | wp_norm_lhs | simp only [arm64_norm, wp_norm, hpcAM, hrunAM, hdz])
  intro sDrop hsDrop hpcD hrunD hinvD
  rw [futDropAddr_ext_eq] at hpcD
  refine sepWPp_drop_left ?_
  have hspD : sDrop.sp = fsp := by rw [← hsDrop]; simp [wp_norm, arm64_norm, hspAM']
  have hx20D : sDrop.readReg64 (.gpr 20#5) = futPtr := by rw [← hsDrop]; simp [futPtr, wp_norm, arm64_norm]
  have hx22D : sDrop.readReg64 (.gpr 22#5) = 0#64 - 1#64 := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm, hx22AM]
  have hx23D : sDrop.readReg64 (.gpr 23#5) = img.base + sessLoadFutVtOff := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm]
  have hlrD : sDrop.readReg64 .lr = initPcExt img ext 0x0308 := by
    rw [← hsDrop]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm, hpcAM]; try bv_omega
  have hfpD : sDrop.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm, cs_fp hcsAM, hfpM]
  have hx19D : sDrop.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsDrop]; simp [wp_norm, arm64_norm, cs_x19 hcsAM, hx19M]
  have hvregsD : calleeSavedVRegs sDrop = calleeSavedVRegs s0 := by
    rw [← hsDrop]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAM, hvregsM]
  have htrD : sDrop.trace = s0.trace := by rw [← hsDrop]; simp [wp_norm, arm64_norm, htrAM']
  have hfsD : sDrop.fs.files = s0.fs.files := by rw [← hsDrop]; simp [wp_norm, arm64_norm, hfsAM']
  clear hsDrop
  have halD : sDrop.spAligned = true := spAligned_of_sp_eq hal3 (hspD.trans hsp3.symm)
  try rw [hspAM']
  refine initCall_ext hh hpanic hStore.futDrop (gx := ()) hpcD hrunD halD hinvD htrD hfsD hlrD
    (by unfold futDropSpec; rw [emp_sepConj]; exact Entails.refl _) (fun _ => false_entails _) ?_
  intro sAD hpcAD hrunAD hspAD hcsAD hinvAD hfsAD
  unfold futDropSpec; dsimp only
  refine sepWPp_pure_elim fun htrAD => ?_
  have htrAD' : sAD.trace = s0.trace := htrAD.trans htrD
  have hfsAD' : sAD.fs.files = s0.fs.files := hfsAD htrAD'
  have hspAD' : sAD.sp = fsp := hspAD.trans hspD
  have hx20AD : sAD.readReg64 (.gpr 20#5) = futPtr := (cs_x20 hcsAD).trans hx20D
  have hx22AD : sAD.readReg64 (.gpr 22#5) = 0#64 - 1#64 := (cs_x22 hcsAD).trans hx22D
  have hx23AD : sAD.readReg64 (.gpr 23#5) = img.base + sessLoadFutVtOff := (cs_x23 hcsAD).trans hx23D
  refine sepWPp_with_rodata (rodata_sessLoadFut_size himg hinvAD.1) ?_
  refine sepWPp_with_rodata (rodata_sessLoadFut_align himg hinvAD.1) ?_
  dsimp only [initPcExt] at hpcAD
  rw [hent] at hpcAD
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAD
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to
    (fnBase + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
    hinvAD ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sF hsF hpcF hrunF hinvF
  refine sepWPp_drop_left (sepWPp_drop_left ?_)
  have hspF : sF.sp = fsp := by rw [← hsF]; simp [wp_norm, arm64_norm, hspAD']
  have hx0F : sF.readReg64 .x0 = futPtr := by rw [← hsF]; simp [wp_norm, arm64_norm, hx20AD]
  have hx1F : (sF.readReg64 .x1).toNat = 24 := by rw [← hsF]; simp [wp_norm, arm64_norm]
  have hx2F : (sF.readReg64 .x2).toNat = 8 := by rw [← hsF]; simp [wp_norm, arm64_norm]
  have hx22F : sF.readReg64 (.gpr 22#5) = 0#64 - 1#64 := by
    rw [← hsF]; simp [wp_norm, arm64_norm, hx22AD]
  have hlrF : sF.readReg64 .lr = initPcExt img ext 0x031c := by
    rw [← hsF]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm, hpcAD]; try bv_omega
  have hfpF : sF.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsF]; simp [wp_norm, arm64_norm, cs_fp hcsAD, hfpD]
  have hx19F : sF.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsF]; simp [wp_norm, arm64_norm, cs_x19 hcsAD, hx19D]
  have hvregsF : calleeSavedVRegs sF = calleeSavedVRegs s0 := by
    rw [← hsF]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAD, hvregsD]
  have htrF : sF.trace = s0.trace := by rw [← hsF]; simp [wp_norm, arm64_norm, htrAD']
  have hfsF : sF.fs.files = s0.fs.files := by rw [← hsF]; simp [wp_norm, arm64_norm, hfsAD']
  clear hsF
  have halF : sF.spAligned = true := spAligned_of_sp_eq hal3 (hspF.trans hsp3.symm)
  have hdealloc := init_dealloc_ok_at_ext (ext := ext) hh hstk hstk64
  let frameNoPool : SepProp :=
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      storesAt A x.stores StoresGhost.opened ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      coinsCursorAt img x.coinsP x.coins 0 ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      logOff img ∗ initSaved s0 ∗
      memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8)
  refine sepWPp_mono_pre (P' :=
      ((rustDeallocExternSpecWithStack A (stk - cliInitiateFrame)).pre (futPtr, 24, 8) sF) ∗
      frameNoPool) ?_ ?_
  · dsimp only [frameNoPool]
    unfold rustDeallocExternSpecWithStack
    try dsimp only [futPtr, Reg.x0]
    try dsimp only
    try rw [hspM]
    rw [hspF]
    have hboxMem := sessLoadBoxAt_entails_memRegion futPtr (x.stores + 0xf0#64) x.peerA 1#8
    have h368 : memRegion (fsp + 0x1600#64) 56 ∗ memRegion (fsp + 0x1638#64) 312 =
        memRegion (fsp + 0x1600#64) 368 :=
      memRegion_merge (fsp + 0x1600#64) (fsp + 0x1638#64) 56 312 368
        (by bv_omega) (by decide) (by decide)
    have hmergeLoad368 :
        memRegion (fsp + 0x5ba#64) 6 ∗
          ((fsp + 0x5c0#64) ↦₆₄ futPtr) ∗
          ((fsp + 0x5c8#64) ↦₆₄ (img.base + sessLoadFutVtOff)) ∗
          memRegion (fsp + 0x5d0#64) 40 ∗
          memRegion (fsp + 0x5f8#64) 312 ∗
          memRegion (fsp + 0x730#64) (0x1600 - 0x730) ∗
          (memRegion (fsp + 0x1600#64) 56 ∗ memRegion (fsp + 0x1638#64) 312) ∗
          memRegion (fsp + 0x1770#64) (initLocalsSize - 0x1770) ⊢
          memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
      rw [h368]
      exact load_frame_5ba_merge fsp futPtr (img.base + sessLoadFutVtOff)
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro ⟨hx0F, hx1F, hx2F, ⟨by decide, ⟨3, rfl⟩, by decide⟩⟩ ?_
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hboxMem (sepConj_mono_right (sepConj_mono_left hmergeLoad368)))))
    sep_frame
  rw [← hent] at hpcF
  refine initCallInImage_ext hh hpanic hdealloc hpcF hrunF halF hinvF htrF hfsF hlrF
    (Entails.refl _) (fun _ => false_entails _) ?_
  intro sAF hpcAF hrunAF hspAF hcsAF hinvAF hfsAF
  unfold rustDeallocExternSpecWithStack; dsimp only
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun htrAF => ?_
  have htrAF' : sAF.trace = s0.trace := htrAF.trans htrF
  have hfsAF' : sAF.fs.files = s0.fs.files := hfsAF htrAF'
  have hspAF' : sAF.sp = fsp := hspAF.trans hspF
  have hx22AF : sAF.readReg64 (.gpr 22#5) = 0#64 - 1#64 := (cs_x22 hcsAF).trans hx22F
  refine sepWPp_mono_pre (P' := stage2Mem A img x stk s0)
    (by unfold stage2Mem; dsimp only [frameNoPool]; rw [hspF, ← hfsp]; sep_frame) ?_
  dsimp only [initPcExt] at hpcAF
  rw [hent] at hpcAF
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAF
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to
    (fnBase + 0x0390#64)
    hinvAF ?_
  wp_steps
  apply SepWP.done
    (by first | wp_norm_goal | simp only [arm64_norm, wp_norm, hpcAF, hrunAF, hx22AF])
    (by first | wp_norm_lhs | simp only [arm64_norm, wp_norm, hpcAF, hrunAF, hx22AF])
  intro s4 hs4 hpc4 hrun4 hinv4
  have hsp4 : s4.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
    rw [hfsp, ← hs4]; simp [wp_norm, arm64_norm, hspAF']
  have hfp4 : s4.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hs4]; simp [wp_norm, arm64_norm, cs_fp hcsAF, hfpF]
  have hx19_4 : s4.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hs4]; simp [wp_norm, arm64_norm, cs_x19 hcsAF, hx19F]
  have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
    rw [← hs4]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAF, hvregsF]
  have htr4 : s4.trace = s0.trace := by rw [← hs4]; simp [wp_norm, arm64_norm, htrAF']
  have hfs40 : s4.fs.files = s0.fs.files := by rw [← hs4]; simp [wp_norm, arm64_norm, hfsAF']
  have hfs4F : s4.fs.files = x.F := by rw [hfs40, ← hfs30, hfs]
  have hx22_4 : s4.readReg64 (.gpr 22#5) = 0#64 := by rw [← hs4]; simp [wp_norm, arm64_norm]
  have hx23_4 : s4.readReg64 (.gpr 23#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x80#64 := by
    rw [hfsp, ← hs4]; simp [wp_norm, arm64_norm, hspAF']
  have hx25_4 : s4.readReg64 (.gpr 25#5) = 0#64 - 1#64 := by
    rw [← hs4]; simp [wp_norm, arm64_norm]
  have hx26_4 : s4.readReg64 (.gpr 26#5) = 8#64 := by rw [← hs4]; simp [wp_norm, arm64_norm]
  have hx27_4 : s4.readReg64 (.gpr 27#5) = 0#64 := by rw [← hs4]; simp [wp_norm, arm64_norm]
  clear hs4
  rw [← hent] at hpc4
  have hctrl4 : InInitiateExt img ext s0 s4 0x0390 :=
    ⟨hpc4, hrun4, hsp4, hfp4, hx19_4, hfs40, hinv4, hvregs4, hal0⟩
  exact hnext s4 be
    ⟨hctrl4, htr4, hfs4F, hx8, hbe, htrust, hsigs, hx22_4, hx23_4, hx25_4, hx26_4, hx27_4⟩

/-- `load_session(peer)` to `AtStage2` (`0x01fc → 0x0390`, `initProg`). -/
theorem stage1_load_session_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hStore : InitStoreCallees img A W B stk)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hbe : bundleEOf? x.bundle = some be)
    (hctrl : InInitiate img W s0 s3 0x01fc)
    (htr : s3.trace = s0.trace)
    (hfs : s3.fs.files = x.F)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hsigs : PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ be = true)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (be' : PreKeyBundleFields),
      AtStage2 img W X x be' s0 s4 →
      SepWPp (initProg img W) (s0.readReg64 .lr) s4
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s3
      (stage2Mem A img x stk s0) Q Qp (initOom s0) :=
  stage1_load_session_ext_ok (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W)
    himg hh.toExt (initStoreCallees_toExt hStore) hinitOk hstk hstk64 hx8 hbe
    (inInitiate_toExt hctrl) htr hfs htrust hsigs hpanic
    (fun s4 be' hs4 => hnext s4 be' (atStage2_ofExt hs4))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
