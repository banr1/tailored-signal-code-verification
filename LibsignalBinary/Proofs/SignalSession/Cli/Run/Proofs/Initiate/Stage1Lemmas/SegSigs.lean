/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.ModelAndLayout
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.KemPubSerializeVal
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 1 Segments 2 and 3 (`0x0154 → 0x01fc`): Bundle XEdDSA Signature Checks

Verifies signed pre-key (`stage1_spk_sig_ok`, `0x0154 → 0x01b4` and `0x0280 → 0x0350`) and Kyber
pre-key (`stage1_kpk_sig_ok`, `0x01b4 → 0x01fc` and `0x02a4 → 0x0350`) XEdDSA signature checks on
`initProg` and `initProgExt`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
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

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  cliInitiateFrame initLocalsSize
  bv_sub_add_lit sp_sub_96_sub_4096 sp_sub_4192_sub_3216 sp_sub_96_add_96 BitVec.toNat_zero

set_option maxHeartbeats 1200000 in
/-- Signed pre-key XEdDSA signature check (`0x0154 → 0x01b4` and `0x0280 → 0x0350`, `initProgExt`). -/
theorem stage1_spk_sig_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {calStk stk : Nat} {s0 s1 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hcal : calStk ≤ stk - cliInitiateFrame)
    (hVerify : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliVerifySignatureName)
      ((verifySigAtStkSpec (modelPrims X P) calStk).inImage img))
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrl : InInitiateExt img ext s0 s1 0x0154)
    (htr : s1.trace = s0.trace)
    (hfs : s1.fs.files = x.F)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s2 : State),
      InInitiateExt img ext s0 s2 0x01b4 →
      s2.trace = s0.trace →
      s2.fs.files = x.F →
      (modelPrims X P).sigVerify
        (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
        (SignalPqxdh.encodeEC (vecU8 (mkBundleE x.bundle h1 h2 h3).spkPub))
        (vecU8 (mkBundleE x.bundle h1 h2 h3).spkSig) = true →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s2
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s1
      (stage2Mem A img x stk s0) Q Qp (initOom s0) := by
  let _ := htrust
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage1Bin img.base
    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    0x0154 0x0150
  have hpc1 := hctrl.pc; have hrun1 := hctrl.run; have hsp1 := hctrl.sp
  have hfp1 := hctrl.fp; have hx19_1 := hctrl.x19; have hfs10 := hctrl.files0
  have hvregs1 := hctrl.vregs; have hal0 := hctrl.spAligned
  have hal1 := inInitiateExt_spAligned_cur hctrl
  let be := mkBundleE x.bundle h1 h2 h3
  unfold stage2Mem; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hsp1 ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp1] using hal1
  have hsplit5ba :
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) =
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
          memRegion (fsp + 0x1600#64) 32 ∗
          memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620) := by
    rw [show initLocalsSize - 0x5ba = (0x1600 - 0x5ba) + (32 + (initLocalsSize - 0x1620)) by decide,
      memRegion_split (fsp + 0x5ba#64) (0x1600 - 0x5ba) _ (by decide),
      memRegion_split _ 32 _ (by decide)]
    simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsplit5ba]
  refine sepWPp_mono_pre (P' :=
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        memRegion (fsp + 0x1600#64) 32 ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt fsp (stk - cliInitiateFrame))
    (by sep_frame) ?_
  rw [cliBundleAt_unpack]
  refine sepWPp_exists_left fun opkId => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨_, _, _, hopk⟩ => ?_
  rw [memRegion_32_words (fsp + 0x1600#64)]
  refine sepWPp_exists_pos2 fun d3 => ?_; refine sepWPp_exists_pos2 fun d2 => ?_
  refine sepWPp_exists_pos2 fun d1 => ?_; refine sepWPp_exists_pos2 fun d0 => ?_
  refine sepWPp_mono_pre (P' :=
      ((x.bundleA + 24#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        (x.bundleA ↦₆₄ 64#64) ∗ ((x.bundleA + 8#64) ↦₆₄ x.spkSigPtr) ∗
        ((x.bundleA + 16#64) ↦₆₄ 64#64) ∗ (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
        ((x.bundleA + 56#64) ↦₃₂ x.bundle.spkId) ∗ memRegion (x.bundleA + 60#64) 4 ∗
        ((x.bundleA + 64#64) ↦₆₄ 64#64) ∗ ((x.bundleA + 72#64) ↦₆₄ x.kpkSigPtr) ∗
        ((x.bundleA + 80#64) ↦₆₄ 64#64) ∗ (x.kpkSigPtr ↦ₛ x.bundle.kpkSig) ∗
        ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗ ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
        (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
        ((x.bundleA + 104#64) ↦₃₂ x.bundle.kpkId) ∗ memRegion (x.bundleA + 108#64) 4 ∗
        ((x.bundleA + 112#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((x.bundleA + 116#64) ↦₃₂ opkId) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 152#64) ↦₃₂ x.bundle.regId) ∗
        ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
        (match x.bundle.opk with
         | some (_, k) => (x.bundleA + 157#64) ↦ₛ k.bytes.toList
         | none => memRegion (x.bundleA + 157#64) 32) ∗
        ((x.bundleA + 189#64) ↦₈ x.bundle.device) ∗ memRegion (x.bundleA + 190#64) 2 ∗
        ((fsp + 0x1600#64) ↦₆₄ d0) ∗ ((fsp + 0x1608#64) ↦₆₄ d1) ∗
        ((fsp + 0x1610#64) ↦₆₄ d2) ∗ ((fsp + 0x1618#64) ↦₆₄ d3) ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620) ∗
        stackAt fsp (stk - cliInitiateFrame))
    (by unfold cliBundleBody; rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)) ?_
  refine sepWPp_mono_pre
    (sepConj_mono_left (bytes32_eq_exists_words4 (x.bundleA + 24#64) (by simp))) ?_
  refine sepWPp_exists_left fun w0 => ?_; refine sepWPp_exists_left fun w1 => ?_
  refine sepWPp_exists_left fun w2 => ?_; refine sepWPp_exists_left fun w3 => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepConj_assoc]; refine sepWPp_pure_elim fun hbs => ?_
  unfold initArgsAt
  have hent : initEntryExt img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc1 ⊢
  try simp only [BitVec.ofNat_eq_ofNat] at hpc1
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  examples_hide_fetches
  refine sepWPp_step_to
    (fnBase + bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
        ls_off% "libsignal_cli_handshake::initiate"))
    hctrl.inv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sSer hsSer hpcS hrunS hinvS
  have hspS : sSer.sp = fsp := by rw [← hsSer]; simp [wp_norm, arm64_norm, hsp1]
  have hx0S : sSer.readReg64 .x0 = fsp + 0x1600#64 := by
    rw [← hsSer]; simp [wp_norm, arm64_norm, hsp1]; try bv_omega
  have hx22S : sSer.readReg64 (.gpr 22#5) = x.bundleA + 120#64 := by
    rw [← hsSer]; simp [wp_norm, arm64_norm, hsp1]
  have hlrS : sSer.readReg64 .lr = initPcExt img ext 0x017c := by
    rw [← hsSer]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm, hpc1]; try bv_omega
  have hfpS : sSer.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsSer]; simp [wp_norm, arm64_norm, hfp1]
  have hx19S : sSer.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsSer]; simp [wp_norm, arm64_norm, hx19_1]
  have hvregsS : calleeSavedVRegs sSer = calleeSavedVRegs s0 := by
    rw [← hsSer]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs1]
  have htrS : sSer.trace = s0.trace := by rw [← hsSer]; simp [wp_norm, arm64_norm, htr]
  have hfsS : sSer.fs.files = s0.fs.files := by rw [← hsSer]; simp [wp_norm, arm64_norm, hfs10]
  clear hsSer
  have halS : sSer.spAligned = true := spAligned_of_sp_eq hal1 (hspS.trans hsp1.symm)
  try rw [hsp1]
  have hser := init_pubKeySerialize_ok_at_ext (ext := ext) hh hstk hstk64
  let serCall : PublicKeySerializeCall := { self := fsp + 0x1600#64, pk := x.bundle.spk }
  let bundleRestSpk : SepProp :=
    ((x.bundleA + 24#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      (x.bundleA ↦₆₄ 64#64) ∗ ((x.bundleA + 8#64) ↦₆₄ x.spkSigPtr) ∗
      ((x.bundleA + 16#64) ↦₆₄ 64#64) ∗
      ((x.bundleA + 56#64) ↦₃₂ x.bundle.spkId) ∗ memRegion (x.bundleA + 60#64) 4 ∗
      ((x.bundleA + 64#64) ↦₆₄ 64#64) ∗ ((x.bundleA + 72#64) ↦₆₄ x.kpkSigPtr) ∗
      ((x.bundleA + 80#64) ↦₆₄ 64#64) ∗ (x.kpkSigPtr ↦ₛ x.bundle.kpkSig) ∗
      ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗ ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
      (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
      ((x.bundleA + 104#64) ↦₃₂ x.bundle.kpkId) ∗ memRegion (x.bundleA + 108#64) 4 ∗
      ((x.bundleA + 112#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
      ((x.bundleA + 116#64) ↦₃₂ opkId) ∗
      ((x.bundleA + 152#64) ↦₃₂ x.bundle.regId) ∗
      ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
      (match x.bundle.opk with
       | some (_, k) => (x.bundleA + 157#64) ↦ₛ k.bytes.toList
       | none => memRegion (x.bundleA + 157#64) 32) ∗
      ((x.bundleA + 189#64) ↦₈ x.bundle.device) ∗ memRegion (x.bundleA + 190#64) 2
  refine sepWPp_mono_pre (P' :=
      ((pubKeySerializeAtStkSpec A (stk - cliInitiateFrame)).pre serCall sSer) ∗
      (bundleRestSpk ∗
        (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620))) ?_ ?_
  · unfold pubKeySerializeAtStkSpec initArgsAt
    dsimp only [serCall, bundleRestSpk]
    rw [hspS]
    have hwSrc :
        ((x.bundleA + 24#64) ↦₆₄ w0) ∗ ((x.bundleA + 32#64) ↦₆₄ w1) ∗
          ((x.bundleA + 40#64) ↦₆₄ w2) ∗ ((x.bundleA + 48#64) ↦₆₄ w3) ⊢
          ((x.bundleA + 24#64) ↦ₛ x.bundle.spk.bytes.toList) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using words4_to_bytes32 (x.bundleA + 24#64) hbs
    have hwDst :
        ((fsp + 0x1600#64) ↦₆₄ w0) ∗
          ((fsp + 0x1608#64) ↦₆₄ w1) ∗
          ((fsp + 0x1610#64) ↦₆₄ w2) ∗
          ((fsp + 0x1618#64) ↦₆₄ w3) ⊢
          ((fsp + 0x1600#64) ↦ₛ x.bundle.spk.bytes.toList) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        words4_to_bytes32 (fsp + 0x1600#64) hbs
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro hx0S ?_
    refine Entails.trans ?_
      (sepConj_mono hwDst (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hwSrc))))
    sep_frame
  rw [← hent] at hpcS
  refine initCallInImage_ext hh hpanic hser hpcS hrunS halS hinvS htrS hfsS hlrS
    (Entails.refl _) (fun _ => Entails.refl _) ?_
  intro sAS hpcAS hrunAS hspAS hcsAS hinvAS hfsAS
  unfold pubKeySerializeAtStkSpec; dsimp only [serCall]
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨hx1AS, htrAS⟩ => ?_
  have htrAS' : sAS.trace = s0.trace := htrAS.trans htrS
  have hfsAS' : sAS.fs.files = s0.fs.files := hfsAS htrAS'
  have hspAS' : sAS.sp = fsp := hspAS.trans hspS
  have hx22AS : sAS.readReg64 (.gpr 22#5) = x.bundleA + 120#64 := (cs_x22 hcsAS).trans hx22S
  let bufPtr := sAS.readReg64 .x0
  have hmerge5ba :
      ((fsp + 0x1600#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 0x5ba#64) (0x1600 - 0x5ba) ∗
        memRegion (fsp + 0x1620#64) (initLocalsSize - 0x1620) ⊢
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
    have hm32 : ((fsp + 0x1600#64) ↦ₛ x.bundle.spk.bytes.toList) ⊢ memRegion (fsp + 0x1600#64) 32 := by
      simpa using pointsToBytes_entails_memRegion (fsp + 0x1600#64) x.bundle.spk.bytes.toList
    rw [hsplit5ba]
    refine Entails.trans (sepConj_mono_left hm32) ?_
    sep_frame
  refine sepWPp_mono_pre (P' :=
      (⌜bufPtr ≠ 0#64⌝ ∗ A.live bufPtr 33 1 ∗ (bufPtr ↦ₛ x.bundle.spk.serialize)) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      ((x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        bundleRestSpk ∗
        A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8))) ?_ ?_
  · rw [hspS]
    refine Entails.trans ?_
      (sepConj_mono (boxU8Buf_serialize_unpack A bufPtr x.bundle.spk)
        (sepConj_mono_left hmerge5ba))
    sep_frame
  repeat rw [sepConj_assoc]
  refine sepWPp_pure_elim fun hbufNZ => ?_
  unfold initArgsAt; try dsimp only [bundleRestSpk]
  dsimp only [initPcExt] at hpcAS
  rw [hent] at hpcAS
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAS
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to
    (fnBase + bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::verify_signature" -
        ls_off% "libsignal_cli_handshake::initiate"))
    hinvAS ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sVer hsVer hpcV hrunV hinvV
  have hspV : sVer.sp = fsp := by rw [← hsVer]; simp [wp_norm, arm64_norm, hspAS']
  have hx0V : sVer.readReg64 .x0 = x.bundleA + 120#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, hx22AS]
  have hx1V : sVer.readReg64 .x1 = bufPtr := by
    rw [← hsVer]; simp [bufPtr, wp_norm, arm64_norm]
  have hx2V : sVer.readReg64 .x2 = 33#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, hx1AS]
  have hx3V : sVer.readReg64 .x3 = x.spkSigPtr := by
    rw [← hsVer]; simp [wp_norm, arm64_norm]
  have hx4V : sVer.readReg64 .x4 = 64#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm]
  have hx20V : sVer.readReg64 (.gpr 20#5) = bufPtr := by
    rw [← hsVer]; simp [bufPtr, wp_norm, arm64_norm]
  have hx21V : sVer.readReg64 (.gpr 21#5) = 33#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, hx1AS]
  have hlrV : sVer.readReg64 .lr = initPcExt img ext 0x019c := by
    rw [← hsVer]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm, hpcAS]; try bv_omega
  have hfpV : sVer.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, cs_fp hcsAS, hfpS]
  have hx19V : sVer.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, cs_x19 hcsAS, hx19S]
  have hvregsV : calleeSavedVRegs sVer = calleeSavedVRegs s0 := by
    rw [← hsVer]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAS, hvregsS]
  have htrV : sVer.trace = s0.trace := by rw [← hsVer]; simp [wp_norm, arm64_norm, htrAS']
  have hfsV : sVer.fs.files = s0.fs.files := by rw [← hsVer]; simp [wp_norm, arm64_norm, hfsAS']
  clear hsVer
  have halV : sVer.spAligned = true := spAligned_of_sp_eq hal1 (hspV.trans hsp1.symm)
  have hvCall := init_verifySig_ok_at_ext (P := P) (ext := ext) (X := X) hcal hstk64 hVerify
  let vg : VerifySignatureGhost :=
    { pkPtr := x.bundleA + 120#64
      msgPtr := bufPtr
      sigPtr := x.spkSigPtr
      pk := vecU8 be.idPub
      m := SignalPqxdh.encodeEC (vecU8 be.spkPub)
      sig := vecU8 be.spkSig }
  have hmlen : vg.m.length = 33 := by simp [vg, SignalPqxdh.encodeEC, E2E.vecU8]
  have hpkEq : Pqxdh.Shared.bytesToBv8 vg.pk = x.bundle.idKey.publicKey.bytes.toList :=
    bytesToBv8_vecU8 be.idPub
  have hmEq : Pqxdh.Shared.bytesToBv8 vg.m = x.bundle.spk.serialize :=
    (spkSerialize_eq_encodeEC x.bundle h1 h2 h3).symm
  have hsigEq : Pqxdh.Shared.bytesToBv8 vg.sig = x.bundle.spkSig :=
    bytesToBv8_vecU8 be.spkSig
  refine sepWPp_mono_pre (P' :=
      ((verifySigAtStkSpec (modelPrims X P) (stk - cliInitiateFrame)).pre vg sVer) ∗
      (A.live bufPtr 33 1 ∗ A.pool ∗
        bundleRestSpk ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba))) ?_ ?_
  · unfold verifySigAtStkSpec initArgsAt
    try dsimp only [vg, bundleRestSpk, bufPtr, Reg.x0]
    try dsimp only [Reg.x0]
    rw [hspV, hpkEq, hmEq, hsigEq, hmlen]
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro
      ⟨hx0V, hx1V, hx2V, hx3V, hx4V, by simp [be, mkBundleE, E2E.vecU8], Or.inl rfl,
        by simp [be, mkBundleE, E2E.vecU8, h1]⟩ ?_
    rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
  rw [← hent] at hpcV
  refine initCallInImage_ext hh hpanic hvCall hpcV hrunV halV hinvV htrV hfsV hlrV
    (Entails.refl _) (fun _ => false_entails _) ?_
  intro sAV hpcAV hrunAV hspAV hcsAV hinvAV hfsAV
  unfold verifySigAtStkSpec; dsimp only
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨hx0AV, htrAV⟩ => ?_
  have htrAV' : sAV.trace = s0.trace := htrAV.trans htrV
  have hfsAV' : sAV.fs.files = s0.fs.files := hfsAV htrAV'
  have hspAV' : sAV.sp = fsp := hspAV.trans hspV
  have hx20AV : sAV.readReg64 (.gpr 20#5) = bufPtr := (cs_x20 hcsAV).trans hx20V
  have hx21AV : sAV.readReg64 (.gpr 21#5) = 33#64 := (cs_x21 hcsAV).trans hx21V
  let frameNoPool : SepProp :=
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      storesAt A x.stores StoresGhost.opened ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      coinsCursorAt img x.coinsP x.coins 0 ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      logOff img ∗ initSaved s0 ∗
      memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)
  refine sepWPp_mono_pre (P' :=
      A.pool ∗ A.live bufPtr 33 1 ∗ memRegion bufPtr 33 ∗
      stackAt fsp (stk - cliInitiateFrame) ∗ frameNoPool) ?_ ?_
  · rw [hspV, hpkEq, hmEq, hsigEq]
    dsimp only [vg, frameNoPool]
    have hbufMem : (bufPtr ↦ₛ x.bundle.spk.serialize) ⊢ memRegion bufPtr 33 := by
      have hm := pointsToBytes_entails_memRegion bufPtr x.bundle.spk.serialize
      have hl : x.bundle.spk.serialize.length = 33 := by simp [PublicKey.serialize]
      rwa [hl] at hm
    have hpackB :
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗ bundleRestSpk ⊢
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr := by
      refine Entails.trans ?_
        (cliBundleBody_pack (a := x.bundleA) (b := x.bundle)
          (spkSigPtr := x.spkSigPtr) (kpkSigPtr := x.kpkSigPtr) (kpkPtr := x.kpkPtr)
          (opkId := opkId) h1 h2 h3 hopk)
      unfold cliBundleBody; dsimp only [bundleRestSpk]
      rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbufMem (sepConj_mono_right (sepConj_mono_left hpackB)))))
    sep_frame
  have hdealloc := init_dealloc_ok_at_ext (ext := ext) hh hstk hstk64
  dsimp only [initPcExt] at hpcAV
  rw [hent] at hpcAV
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAV
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  cases hv : (modelPrims X P).sigVerify vg.pk vg.m vg.sig
  · -- Invalid SPK signature (`hv = false`)
    rw [hv] at hx0AV
    simp only [Bool.false_eq_true, ↓reduceIte, Reg.x0] at hx0AV
    refine sepWPp_step_to
      (fnBase + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      hinvAV ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro sD hsD hpcD hrunD hinvD
    have hspD : sD.sp = fsp := by rw [← hsD]; simp [wp_norm, arm64_norm, hspAV']
    have hx0D : sD.readReg64 .x0 = bufPtr := by rw [← hsD]; simp [wp_norm, arm64_norm, hx20AV]
    have hx1D : (sD.readReg64 .x1).toNat = 33 := by rw [← hsD]; simp [wp_norm, arm64_norm, hx21AV]
    have hx2D : (sD.readReg64 .x2).toNat = 1 := by rw [← hsD]; simp [wp_norm, arm64_norm]
    have hlrD : sD.readReg64 .lr = initPcExt img ext 0x0294 := by
      rw [← hsD]; dsimp [initPcExt]; rw [hent]
      simp [wp_norm, arm64_norm, hpcAV]; try bv_omega
    have hfpD : sD.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsD]; simp [wp_norm, arm64_norm, cs_fp hcsAV, hfpV]
    have hx19D : sD.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsD]; simp [wp_norm, arm64_norm, cs_x19 hcsAV, hx19V]
    have hvregsD : calleeSavedVRegs sD = calleeSavedVRegs s0 := by
      rw [← hsD]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAV, hvregsV]
    have htrD : sD.trace = s0.trace := by rw [← hsD]; simp [wp_norm, arm64_norm, htrAV']
    have hfsD : sD.fs.files = s0.fs.files := by rw [← hsD]; simp [wp_norm, arm64_norm, hfsAV']
    clear hsD
    have halD : sD.spAligned = true := spAligned_of_sp_eq hal1 (hspD.trans hsp1.symm)
    rw [← hent] at hpcD
    refine initCallInImage_ext hh hpanic hdealloc (gx := (bufPtr, 33, 1))
      hpcD hrunD halD hinvD htrD hfsD hlrD
      (by
        unfold rustDeallocExternSpecWithStack; dsimp only; rw [hspD]
        repeat rw [sepConj_assoc]; exact pure_sepConj_intro ⟨hx0D, hx1D, hx2D, ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩ (by sep_frame))
      (fun _ => false_entails _) ?_
    intro sAD hpcAD hrunAD hspAD hcsAD hinvAD hfsAD
    unfold rustDeallocExternSpecWithStack; dsimp only
    rw [sepConj_assoc]; refine sepWPp_pure_elim fun htrAD => ?_
    have htrAD' : sAD.trace = s0.trace := htrAD.trans htrD
    have hfsAD' : sAD.fs.files = s0.fs.files := hfsAD htrAD'
    have hspAD' : sAD.sp = fsp := hspAD.trans hspD
    refine sepWPp_mono_pre (P' := stage2Mem A img x stk s0)
      (by unfold stage2Mem; dsimp only [frameNoPool]; rw [hspD, ← hfsp]; sep_frame) ?_
    dsimp only [initPcExt] at hpcAD
    rw [hent] at hpcAD
    try simp only [BitVec.ofNat_eq_ofNat] at hpcAD
    dsimp only [initProgExt, tripleRatchetProgAtExt]
    refine sepWPp_step_to
      (fnBase + 0x0350#64)
      hinvAD ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro sErr hsErr hpcErr hrunErr hinvErr
    have hspErr : sErr.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
      rw [hfsp, ← hsErr]; simp [wp_norm, arm64_norm, hspAD']
    have hfpErr : sErr.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, cs_fp hcsAD, hfpD]
    have hx19Err : sErr.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, cs_x19 hcsAD, hx19D]
    have hvregsErr : calleeSavedVRegs sErr = calleeSavedVRegs s0 := by
      rw [← hsErr]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAD, hvregsD]
    have htrErr : sErr.trace = s0.trace := by rw [← hsErr]; simp [wp_norm, arm64_norm, htrAD']
    have hfsErr : sErr.fs.files = s0.fs.files := by rw [← hsErr]; simp [wp_norm, arm64_norm, hfsAD']
    have hx26Err : sErr.readReg64 (.gpr 26#5) = speWord 11 := by
      rw [← hsErr]; simp [wp_norm, arm64_norm]; rfl
    clear hsErr
    rw [← hent] at hpcErr
    have hctrlErr : InInitiateExt img ext s0 sErr 0x0350 :=
      ⟨hpcErr, hrunErr, hspErr, hfpErr, hx19Err, hfsErr, hinvErr, hvregsErr, hal0⟩
    have hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none := by
      rw [hS]
      exact initDef_eq_some_none_of_sigsOk_false X P x.F x.peer.val x.me.val
        x.bundle be x.coins (bundleEOf_eq_some_mkBundleE x.bundle h1 h2 h3)
        (sigsOk_false_of_spk_false X P be hv)
    exact stage1_plain11_exit_ext_ok hstk hstk64 hx8 hctrlErr htrErr hans hpost hx26Err
  · -- Valid SPK signature (`hv = true`)
    rw [hv] at hx0AV
    simp only [↓reduceIte, Reg.x0] at hx0AV
    refine sepWPp_step_to
      (fnBase + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      hinvAV ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro sD hsD hpcD hrunD hinvD
    have hspD : sD.sp = fsp := by rw [← hsD]; simp [wp_norm, arm64_norm, hspAV']
    have hx0D : sD.readReg64 .x0 = bufPtr := by rw [← hsD]; simp [wp_norm, arm64_norm, hx20AV]
    have hx1D : (sD.readReg64 .x1).toNat = 33 := by rw [← hsD]; simp [wp_norm, arm64_norm, hx21AV]
    have hx2D : (sD.readReg64 .x2).toNat = 1 := by rw [← hsD]; simp [wp_norm, arm64_norm]
    have hlrD : sD.readReg64 .lr = initPcExt img ext 0x01b4 := by
      rw [← hsD]; dsimp [initPcExt]; rw [hent]
      simp [wp_norm, arm64_norm, hpcAV]; try bv_omega
    have hfpD : sD.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsD]; simp [wp_norm, arm64_norm, cs_fp hcsAV, hfpV]
    have hx19D : sD.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsD]; simp [wp_norm, arm64_norm, cs_x19 hcsAV, hx19V]
    have hvregsD : calleeSavedVRegs sD = calleeSavedVRegs s0 := by
      rw [← hsD]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAV, hvregsV]
    have htrD : sD.trace = s0.trace := by rw [← hsD]; simp [wp_norm, arm64_norm, htrAV']
    have hfsD : sD.fs.files = s0.fs.files := by rw [← hsD]; simp [wp_norm, arm64_norm, hfsAV']
    clear hsD
    have halD : sD.spAligned = true := spAligned_of_sp_eq hal1 (hspD.trans hsp1.symm)
    rw [← hent] at hpcD
    refine initCallInImage_ext hh hpanic hdealloc (gx := (bufPtr, 33, 1))
      hpcD hrunD halD hinvD htrD hfsD hlrD
      (by
        unfold rustDeallocExternSpecWithStack; dsimp only; rw [hspD]
        repeat rw [sepConj_assoc]; exact pure_sepConj_intro ⟨hx0D, hx1D, hx2D, ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩ (by sep_frame))
      (fun _ => false_entails _) ?_
    intro s2 hpc2 hrun2 hsp2 hcs2 hinv2 hfs2
    unfold rustDeallocExternSpecWithStack; dsimp only
    rw [sepConj_assoc]; refine sepWPp_pure_elim fun htr2 => ?_
    have htr2' : s2.trace = s0.trace := htr2.trans htrD
    have hfs20 : s2.fs.files = s0.fs.files := hfs2 htr2'
    have hfs2F : s2.fs.files = x.F := by rw [hfs20, ← hfs10, hfs]
    have hctrl2 : InInitiateExt img ext s0 s2 0x01b4 :=
      ⟨hpc2, hrun2, (hsp2.trans hspD).trans hfsp.symm, (cs_fp hcs2).trans hfpD, (cs_x19 hcs2).trans hx19D,
        hfs20, hinv2, (cs_vregs hcs2).trans hvregsD, hal0⟩
    refine sepWPp_mono_pre (P' := stage2Mem A img x stk s0)
      (by unfold stage2Mem; dsimp only [frameNoPool]; rw [hspD, ← hfsp]; sep_frame) ?_
    exact hnext s2 hctrl2 htr2' hfs2F hv

/-- Signed pre-key XEdDSA signature check (`0x0154 → 0x01b4` and `0x0280 → 0x0350`, `initProg`). -/
theorem stage1_spk_sig_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s1 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrl : InInitiate img W s0 s1 0x0154)
    (htr : s1.trace = s0.trace)
    (hfs : s1.fs.files = x.F)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s2 : State),
      InInitiate img W s0 s2 0x01b4 →
      s2.trace = s0.trace →
      s2.fs.files = x.F →
      (modelPrims X ⟨W.C, W.Q⟩).sigVerify
        (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
        (SignalPqxdh.encodeEC (vecU8 (mkBundleE x.bundle h1 h2 h3).spkPub))
        (vecU8 (mkBundleE x.bundle h1 h2 h3).spkSig) = true →
      SepWPp (initProg img W) (s0.readReg64 .lr) s2
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s1
      (stage2Mem A img x stk s0) Q Qp (initOom s0) := by
  have hbase := hLocal.verifySignature X
  have hspecEq : verifySignatureSpec (modelPrims X ⟨W.C, W.Q⟩) img =
      (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩)
        (Pqxdh.Shared.pqxdhHookStack + 1280)).inImage img := rfl
  rw [hspecEq] at hbase
  have hcal : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ stk - cliInitiateFrame := by
    have hb := stk_sub_ge_base hstk
    have hp : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ 516880 := by decide
    omega
  exact stage1_spk_sig_ext_ok (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W)
    hh.toExt hcal hbase hS hstk hstk64 hx8 h1 h2 h3 (inInitiate_toExt hctrl) htr hfs htrust
    hpost hpanic (fun s2 hc2 htr2 hfs2 hv => hnext s2 (inInitiate_ofExt hc2) htr2 hfs2 hv)

set_option maxHeartbeats 1200000 in
/-- Kyber pre-key XEdDSA signature check (`0x01b4 → 0x01fc` and `0x02a4 → 0x0350`, `initProgExt`). -/
theorem stage1_kpk_sig_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {calStk stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hcal : calStk ≤ stk - cliInitiateFrame)
    (hVerify : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliVerifySignatureName)
      ((verifySigAtStkSpec (modelPrims X P) calStk).inImage img))
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrl : InInitiateExt img ext s0 s2 0x01b4)
    (htr : s2.trace = s0.trace)
    (hfs : s2.fs.files = x.F)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hspk : (modelPrims X P).sigVerify
      (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
      (SignalPqxdh.encodeEC (vecU8 (mkBundleE x.bundle h1 h2 h3).spkPub))
      (vecU8 (mkBundleE x.bundle h1 h2 h3).spkSig) = true)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s3 : State),
      InInitiateExt img ext s0 s3 0x01fc →
      s3.trace = s0.trace →
      s3.fs.files = x.F →
      PreKeyBundleFields.signaturesVerify X P (mkBundleE x.bundle h1 h2 h3) = true →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s2
      (stage2Mem A img x stk s0) Q Qp (initOom s0) := by
  let _ := htrust
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage1Bin img.base
    (Rust.withPanics (cliExternsWith ext)) cliInitiate_fnOff
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    0x01b4 0x0114
  have hpc2 := hctrl.pc; have hrun2 := hctrl.run; have hsp2 := hctrl.sp
  have hfp2 := hctrl.fp; have hx19_2 := hctrl.x19; have hfs20 := hctrl.files0
  have hvregs2 := hctrl.vregs; have hal0 := hctrl.spAligned
  have hal2 := inInitiateExt_spAligned_cur hctrl
  let be := mkBundleE x.bundle h1 h2 h3
  unfold stage2Mem; dsimp only
  generalize hfsp : s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp at hsp2 ⊢
  have hfspAl : (fsp &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp2] using hal2
  refine sepWPp_mono_pre (P' :=
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        stackAt fsp (stk - cliInitiateFrame)) (by sep_frame) ?_
  rw [cliBundleAt_unpack]
  refine sepWPp_exists_left fun opkId => ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨_, _, _, hopk⟩ => ?_
  let bundleRestKpk : SepProp :=
    (x.bundleA ↦₆₄ 64#64) ∗ ((x.bundleA + 8#64) ↦₆₄ x.spkSigPtr) ∗
      ((x.bundleA + 16#64) ↦₆₄ 64#64) ∗ (x.spkSigPtr ↦ₛ x.bundle.spkSig) ∗
      ((x.bundleA + 24#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      ((x.bundleA + 56#64) ↦₃₂ x.bundle.spkId) ∗ memRegion (x.bundleA + 60#64) 4 ∗
      ((x.bundleA + 64#64) ↦₆₄ 64#64) ∗ ((x.bundleA + 72#64) ↦₆₄ x.kpkSigPtr) ∗
      ((x.bundleA + 80#64) ↦₆₄ 64#64) ∗
      ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗ ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
      ((x.bundleA + 104#64) ↦₃₂ x.bundle.kpkId) ∗ memRegion (x.bundleA + 108#64) 4 ∗
      ((x.bundleA + 112#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
      ((x.bundleA + 116#64) ↦₃₂ opkId) ∗
      ((x.bundleA + 152#64) ↦₃₂ x.bundle.regId) ∗
      ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
      (match x.bundle.opk with
       | some (_, k) => (x.bundleA + 157#64) ↦ₛ k.bytes.toList
       | none => memRegion (x.bundleA + 157#64) 32) ∗
      ((x.bundleA + 189#64) ↦₈ x.bundle.device) ∗ memRegion (x.bundleA + 190#64) 2
  refine sepWPp_mono_pre (P' :=
      (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
        (x.kpkSigPtr ↦ₛ x.bundle.kpkSig) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        bundleRestKpk ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        stackAt fsp (stk - cliInitiateFrame))
    (by unfold cliBundleBody; dsimp only [bundleRestKpk]; rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)) ?_
  unfold initArgsAt; dsimp only [bundleRestKpk]
  have hent : initEntryExt img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
  dsimp only [initPcExt, initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc2 ⊢
  try simp only [BitVec.ofNat_eq_ofNat] at hpc2
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
  examples_hide_fetches
  refine sepWPp_step_to
    (fnBase + bv% (ls_rel% "libsignal_cli_handshake::initiate"
        "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"))
    hctrl.inv ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sSer hsSer hpcS hrunS hinvS
  have hspS : sSer.sp = fsp := by rw [← hsSer]; simp [wp_norm, arm64_norm, hsp2]
  have hx0S : sSer.readReg64 .x0 = x.kpkPtr := by rw [← hsSer]; simp [wp_norm, arm64_norm, hsp2]
  have hx1S : sSer.readReg64 .x1 = 1568#64 := by rw [← hsSer]; simp [wp_norm, arm64_norm, hsp2]
  have hx22S : sSer.readReg64 (.gpr 22#5) = x.bundleA + 120#64 := by
    rw [← hsSer]; simp [wp_norm, arm64_norm, hsp2]
  have hlrS : sSer.readReg64 .lr = initPcExt img ext 0x01c4 := by
    rw [← hsSer]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm, hpc2]; try bv_omega
  have hfpS : sSer.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsSer]; simp [wp_norm, arm64_norm, hfp2]
  have hx19S : sSer.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsSer]; simp [wp_norm, arm64_norm, hx19_2]
  have hvregsS : calleeSavedVRegs sSer = calleeSavedVRegs s0 := by
    rw [← hsSer]; simp [calleeSavedVRegs, wp_norm, arm64_norm, hvregs2]
  have htrS : sSer.trace = s0.trace := by rw [← hsSer]; simp [wp_norm, arm64_norm, htr]
  have hfsS : sSer.fs.files = s0.fs.files := by rw [← hsSer]; simp [wp_norm, arm64_norm, hfs20]
  clear hsSer
  have halS : sSer.spAligned = true := spAligned_of_sp_eq hal2 (hspS.trans hsp2.symm)
  try rw [hsp2]
  have hkser := init_kemPubSerializeVal_ok_at_ext (ext := ext) hh hstk hstk64
  refine sepWPp_mono_pre (P' :=
      ((kemPubSerializeValAtStkSpec A (stk - cliInitiateFrame)).pre (x.kpkPtr, x.bundle.kpk) sSer) ∗
      ((x.kpkSigPtr ↦ₛ x.bundle.kpkSig) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        bundleRestKpk ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba))) ?_ ?_
  · unfold kemPubSerializeValAtStkSpec initArgsAt
    try dsimp only [bundleRestKpk]
    try dsimp only
    rw [hspS]
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro ⟨hx0S, hx1S, h3⟩ ?_
    rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
  rw [← hent] at hpcS
  refine initCallInImage_ext hh hpanic hkser hpcS hrunS halS hinvS htrS hfsS hlrS
    (Entails.refl _) (fun _ => Entails.refl _) ?_
  intro sAS hpcAS hrunAS hspAS hcsAS hinvAS hfsAS
  unfold kemPubSerializeValAtStkSpec; dsimp only
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨hbufNZ, hx1AS, htrAS⟩ => ?_
  have htrAS' : sAS.trace = s0.trace := htrAS.trans htrS
  have hfsAS' : sAS.fs.files = s0.fs.files := hfsAS htrAS'
  have hspAS' : sAS.sp = fsp := hspAS.trans hspS
  have hx22AS : sAS.readReg64 (.gpr 22#5) = x.bundleA + 120#64 := (cs_x22 hcsAS).trans hx22S
  let bufPtr := sAS.readReg64 .x0
  unfold initArgsAt; try dsimp only [bundleRestKpk]
  dsimp only [initPcExt] at hpcAS
  rw [hent] at hpcAS
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAS
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  refine sepWPp_step_to
    (fnBase + bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::verify_signature" -
        ls_off% "libsignal_cli_handshake::initiate"))
    hinvAS ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro sVer hsVer hpcV hrunV hinvV
  have hspV : sVer.sp = fsp := by rw [← hsVer]; simp [wp_norm, arm64_norm, hspAS']
  have hx0V : sVer.readReg64 .x0 = x.bundleA + 120#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, hx22AS]
  have hx1V : sVer.readReg64 .x1 = bufPtr := by
    rw [← hsVer]; simp [bufPtr, wp_norm, arm64_norm]
  have hx2V : sVer.readReg64 .x2 = 1569#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, hx1AS]
  have hx3V : sVer.readReg64 .x3 = x.kpkSigPtr := by
    rw [← hsVer]; simp [wp_norm, arm64_norm]
  have hx4V : sVer.readReg64 .x4 = 64#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm]
  have hx20V : sVer.readReg64 (.gpr 20#5) = bufPtr := by
    rw [← hsVer]; simp [bufPtr, wp_norm, arm64_norm]
  have hx21V : sVer.readReg64 (.gpr 21#5) = 1569#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, hx1AS]
  have hlrV : sVer.readReg64 .lr = initPcExt img ext 0x01e4 := by
    rw [← hsVer]; dsimp [initPcExt]; rw [hent]
    simp [wp_norm, arm64_norm, hpcAS]; try bv_omega
  have hfpV : sVer.readReg64 .fp = s0.sp - 0x60#64 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, cs_fp hcsAS, hfpS]
  have hx19V : sVer.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
    rw [← hsVer]; simp [wp_norm, arm64_norm, cs_x19 hcsAS, hx19S]
  have hvregsV : calleeSavedVRegs sVer = calleeSavedVRegs s0 := by
    rw [← hsVer]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAS, hvregsS]
  have htrV : sVer.trace = s0.trace := by rw [← hsVer]; simp [wp_norm, arm64_norm, htrAS']
  have hfsV : sVer.fs.files = s0.fs.files := by rw [← hsVer]; simp [wp_norm, arm64_norm, hfsAS']
  clear hsVer
  have halV : sVer.spAligned = true := spAligned_of_sp_eq hal2 (hspV.trans hsp2.symm)
  have hvCall := init_verifySig_ok_at_ext (P := P) (ext := ext) (X := X) hcal hstk64 hVerify
  let vg : VerifySignatureGhost :=
    { pkPtr := x.bundleA + 120#64
      msgPtr := bufPtr
      sigPtr := x.kpkSigPtr
      pk := vecU8 be.idPub
      m := SignalPqxdh.encodeKEM (vecU8 be.kpkPub)
      sig := vecU8 be.kpkSig }
  have hmlen : vg.m.length = 1569 := by simp [vg, SignalPqxdh.encodeKEM, E2E.vecU8]
  have hpkEq : Pqxdh.Shared.bytesToBv8 vg.pk = x.bundle.idKey.publicKey.bytes.toList :=
    bytesToBv8_vecU8 be.idPub
  have hmEq : Pqxdh.Shared.bytesToBv8 vg.m = (8#8 :: x.bundle.kpk) :=
    (kpkSerialize_eq_encodeKEM x.bundle h1 h2 h3).symm
  have hsigEq : Pqxdh.Shared.bytesToBv8 vg.sig = x.bundle.kpkSig :=
    bytesToBv8_vecU8 be.kpkSig
  refine sepWPp_mono_pre (P' :=
      ((verifySigAtStkSpec (modelPrims X P) (stk - cliInitiateFrame)).pre vg sVer) ∗
      (A.live bufPtr 1569 1 ∗ A.pool ∗
        (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
        bundleRestKpk ∗
        storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        coinsCursorAt img x.coinsP x.coins 0 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
        memRegion (fsp + 0x128#64) 0x490 ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba))) ?_ ?_
  · unfold verifySigAtStkSpec initArgsAt
    try dsimp only [vg, bundleRestKpk, bufPtr, Reg.x0]
    try dsimp only [Reg.x0]
    rw [hspS, hspV, hpkEq, hmEq, hsigEq, hmlen]
    repeat rw [sepConj_assoc]
    refine pure_sepConj_intro
      ⟨hx0V, hx1V, hx2V, hx3V, hx4V, by simp [be, mkBundleE, E2E.vecU8], Or.inr rfl,
        by simp [be, mkBundleE, E2E.vecU8, h2]⟩ ?_
    rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
  rw [← hent] at hpcV
  refine initCallInImage_ext hh hpanic hvCall hpcV hrunV halV hinvV htrV hfsV hlrV
    (Entails.refl _) (fun _ => false_entails _) ?_
  intro sAV hpcAV hrunAV hspAV hcsAV hinvAV hfsAV
  unfold verifySigAtStkSpec; dsimp only
  rw [sepConj_assoc]
  refine sepWPp_pure_elim fun ⟨hx0AV, htrAV⟩ => ?_
  have htrAV' : sAV.trace = s0.trace := htrAV.trans htrV
  have hfsAV' : sAV.fs.files = s0.fs.files := hfsAV htrAV'
  have hspAV' : sAV.sp = fsp := hspAV.trans hspV
  have hx20AV : sAV.readReg64 (.gpr 20#5) = bufPtr := (cs_x20 hcsAV).trans hx20V
  have hx21AV : sAV.readReg64 (.gpr 21#5) = 1569#64 := (cs_x21 hcsAV).trans hx21V
  let frameNoPool : SepProp :=
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      storesAt A x.stores StoresGhost.opened ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      coinsCursorAt img x.coinsP x.coins 0 ∗
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      logOff img ∗ initSaved s0 ∗
      memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
      memRegion (fsp + 0x128#64) 0x490 ∗
      ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)
  refine sepWPp_mono_pre (P' :=
      A.pool ∗ A.live bufPtr 1569 1 ∗ memRegion bufPtr 1569 ∗
      stackAt fsp (stk - cliInitiateFrame) ∗ frameNoPool) ?_ ?_
  · rw [hspV, hpkEq, hmEq, hsigEq]
    dsimp only [vg, frameNoPool]
    have hbufMem : (bufPtr ↦ₛ (8#8 :: x.bundle.kpk)) ⊢ memRegion bufPtr 1569 := by
      have hm := pointsToBytes_entails_memRegion bufPtr (8#8 :: x.bundle.kpk)
      have hl : (8#8 :: x.bundle.kpk).length = 1569 := by simp [h3]
      rwa [hl] at hm
    have hpackB :
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          (x.kpkSigPtr ↦ₛ x.bundle.kpkSig) ∗
          (x.kpkPtr ↦ₛ x.bundle.kpk) ∗ bundleRestKpk ⊢
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr := by
      refine Entails.trans ?_
        (cliBundleBody_pack (a := x.bundleA) (b := x.bundle)
          (spkSigPtr := x.spkSigPtr) (kpkSigPtr := x.kpkSigPtr) (kpkPtr := x.kpkPtr)
          (opkId := opkId) h1 h2 h3 hopk)
      unfold cliBundleBody; dsimp only [bundleRestKpk]
      rcases x.bundle.opk with _ | ⟨_, _⟩ <;> (dsimp only; sep_frame)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbufMem (sepConj_mono_right (sepConj_mono_left hpackB)))))
    sep_frame
  have hdealloc := init_dealloc_ok_at_ext (ext := ext) hh hstk hstk64
  dsimp only [initPcExt] at hpcAV
  rw [hent] at hpcAV
  try simp only [BitVec.ofNat_eq_ofNat] at hpcAV
  dsimp only [initProgExt, tripleRatchetProgAtExt]
  cases hv : (modelPrims X P).sigVerify vg.pk vg.m vg.sig
  · -- Invalid KPK signature (`hv = false`)
    rw [hv] at hx0AV
    simp only [Bool.false_eq_true, ↓reduceIte, Reg.x0] at hx0AV
    refine sepWPp_step_to
      (fnBase + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      hinvAV ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro sD hsD hpcD hrunD hinvD
    have hspD : sD.sp = fsp := by rw [← hsD]; simp [wp_norm, arm64_norm, hspAV']
    have hx0D : sD.readReg64 .x0 = bufPtr := by rw [← hsD]; simp [wp_norm, arm64_norm, hx20AV]
    have hx1D : (sD.readReg64 .x1).toNat = 1569 := by rw [← hsD]; simp [wp_norm, arm64_norm, hx21AV]
    have hx2D : (sD.readReg64 .x2).toNat = 1 := by rw [← hsD]; simp [wp_norm, arm64_norm]
    have hx22D : sD.readReg64 (.gpr 22#5) = speWord 8 := by
      rw [← hsD]; simp [wp_norm, arm64_norm]; rfl
    have hlrD : sD.readReg64 .lr = initPcExt img ext 0x02c0 := by
      rw [← hsD]; dsimp [initPcExt]; rw [hent]
      simp [wp_norm, arm64_norm, hpcAV]; try bv_omega
    have hfpD : sD.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsD]; simp [wp_norm, arm64_norm, cs_fp hcsAV, hfpV]
    have hx19D : sD.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsD]; simp [wp_norm, arm64_norm, cs_x19 hcsAV, hx19V]
    have hvregsD : calleeSavedVRegs sD = calleeSavedVRegs s0 := by
      rw [← hsD]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAV, hvregsV]
    have htrD : sD.trace = s0.trace := by rw [← hsD]; simp [wp_norm, arm64_norm, htrAV']
    have hfsD : sD.fs.files = s0.fs.files := by rw [← hsD]; simp [wp_norm, arm64_norm, hfsAV']
    clear hsD
    have halD : sD.spAligned = true := spAligned_of_sp_eq hal2 (hspD.trans hsp2.symm)
    rw [← hent] at hpcD
    refine initCallInImage_ext hh hpanic hdealloc (gx := (bufPtr, 1569, 1))
      hpcD hrunD halD hinvD htrD hfsD hlrD
      (by
        unfold rustDeallocExternSpecWithStack; dsimp only; rw [hspD]
        repeat rw [sepConj_assoc]; exact pure_sepConj_intro ⟨hx0D, hx1D, hx2D, ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩ (by sep_frame))
      (fun _ => false_entails _) ?_
    intro sAD hpcAD hrunAD hspAD hcsAD hinvAD hfsAD
    unfold rustDeallocExternSpecWithStack; dsimp only
    rw [sepConj_assoc]; refine sepWPp_pure_elim fun htrAD => ?_
    have htrAD' : sAD.trace = s0.trace := htrAD.trans htrD
    have hfsAD' : sAD.fs.files = s0.fs.files := hfsAD htrAD'
    have hspAD' : sAD.sp = fsp := hspAD.trans hspD
    have hx22AD : sAD.readReg64 (.gpr 22#5) = speWord 8 := (cs_x22 hcsAD).trans hx22D
    refine sepWPp_mono_pre (P' := stage2Mem A img x stk s0)
      (by unfold stage2Mem; dsimp only [frameNoPool]; rw [hspD, ← hfsp]; sep_frame) ?_
    dsimp only [initPcExt] at hpcAD
    rw [hent] at hpcAD
    try simp only [BitVec.ofNat_eq_ofNat] at hpcAD
    dsimp only [initProgExt, tripleRatchetProgAtExt]
    refine sepWPp_step_to
      (fnBase + 0x0350#64)
      hinvAD ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro sErr hsErr hpcErr hrunErr hinvErr
    have hspErr : sErr.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := by
      rw [hfsp, ← hsErr]; simp [wp_norm, arm64_norm, hspAD']
    have hfpErr : sErr.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, cs_fp hcsAD, hfpD]
    have hx19Err : sErr.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, cs_x19 hcsAD, hx19D]
    have hvregsErr : calleeSavedVRegs sErr = calleeSavedVRegs s0 := by
      rw [← hsErr]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAD, hvregsD]
    have htrErr : sErr.trace = s0.trace := by rw [← hsErr]; simp [wp_norm, arm64_norm, htrAD']
    have hfsErr : sErr.fs.files = s0.fs.files := by rw [← hsErr]; simp [wp_norm, arm64_norm, hfsAD']
    have hx26Err : sErr.readReg64 (.gpr 26#5) = speWord 11 := by
      rw [← hsErr]; simp [wp_norm, arm64_norm, hx22AD]; rfl
    clear hsErr
    rw [← hent] at hpcErr
    have hctrlErr : InInitiateExt img ext s0 sErr 0x0350 :=
      ⟨hpcErr, hrunErr, hspErr, hfpErr, hx19Err, hfsErr, hinvErr, hvregsErr, hal0⟩
    have hans : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none := by
      rw [hS]
      exact initDef_eq_some_none_of_sigsOk_false X P x.F x.peer.val x.me.val
        x.bundle be x.coins (bundleEOf_eq_some_mkBundleE x.bundle h1 h2 h3)
        (sigsOk_false_of_kpk_false X P be hv)
    exact stage1_plain11_exit_ext_ok hstk hstk64 hx8 hctrlErr htrErr hans hpost hx26Err
  · -- Valid KPK signature (`hv = true`)
    rw [hv] at hx0AV
    simp only [↓reduceIte, Reg.x0] at hx0AV
    refine sepWPp_step_to
      (fnBase + bv% (ls_rel% "libsignal_cli_handshake::initiate" "__rustc::__rust_dealloc"))
      hinvAV ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro sD hsD hpcD hrunD hinvD
    have hspD : sD.sp = fsp := by rw [← hsD]; simp [wp_norm, arm64_norm, hspAV']
    have hx0D : sD.readReg64 .x0 = bufPtr := by rw [← hsD]; simp [wp_norm, arm64_norm, hx20AV]
    have hx1D : (sD.readReg64 .x1).toNat = 1569 := by rw [← hsD]; simp [wp_norm, arm64_norm, hx21AV]
    have hx2D : (sD.readReg64 .x2).toNat = 1 := by rw [← hsD]; simp [wp_norm, arm64_norm]
    have hlrD : sD.readReg64 .lr = initPcExt img ext 0x01fc := by
      rw [← hsD]; dsimp [initPcExt]; rw [hent]
      simp [wp_norm, arm64_norm, hpcAV]; try bv_omega
    have hfpD : sD.readReg64 .fp = s0.sp - 0x60#64 := by
      rw [← hsD]; simp [wp_norm, arm64_norm, cs_fp hcsAV, hfpV]
    have hx19D : sD.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := by
      rw [← hsD]; simp [wp_norm, arm64_norm, cs_x19 hcsAV, hx19V]
    have hvregsD : calleeSavedVRegs sD = calleeSavedVRegs s0 := by
      rw [← hsD]; simp [calleeSavedVRegs, wp_norm, arm64_norm, cs_vregs hcsAV, hvregsV]
    have htrD : sD.trace = s0.trace := by rw [← hsD]; simp [wp_norm, arm64_norm, htrAV']
    have hfsD : sD.fs.files = s0.fs.files := by rw [← hsD]; simp [wp_norm, arm64_norm, hfsAV']
    clear hsD
    have halD : sD.spAligned = true := spAligned_of_sp_eq hal2 (hspD.trans hsp2.symm)
    rw [← hent] at hpcD
    refine initCallInImage_ext hh hpanic hdealloc (gx := (bufPtr, 1569, 1))
      hpcD hrunD halD hinvD htrD hfsD hlrD
      (by
        unfold rustDeallocExternSpecWithStack; dsimp only; rw [hspD]
        repeat rw [sepConj_assoc]; exact pure_sepConj_intro ⟨hx0D, hx1D, hx2D, ⟨by decide, ⟨0, rfl⟩, by decide⟩⟩ (by sep_frame))
      (fun _ => false_entails _) ?_
    intro s3 hpc3 hrun3 hsp3 hcs3 hinv3 hfs3
    unfold rustDeallocExternSpecWithStack; dsimp only
    rw [sepConj_assoc]; refine sepWPp_pure_elim fun htr3 => ?_
    have htr3' : s3.trace = s0.trace := htr3.trans htrD
    have hfs30 : s3.fs.files = s0.fs.files := hfs3 htr3'
    have hfs3F : s3.fs.files = x.F := by rw [hfs30, ← hfs20, hfs]
    have hctrl3 : InInitiateExt img ext s0 s3 0x01fc :=
      ⟨hpc3, hrun3, (hsp3.trans hspD).trans hfsp.symm, (cs_fp hcs3).trans hfpD, (cs_x19 hcs3).trans hx19D,
        hfs30, hinv3, (cs_vregs hcs3).trans hvregsD, hal0⟩
    have hsigs : PreKeyBundleFields.signaturesVerify X P be = true := by
      unfold PreKeyBundleFields.signaturesVerify
      dsimp only [initiateInput]
      rw [hspk, hv, Bool.and_self]
    refine sepWPp_mono_pre (P' := stage2Mem A img x stk s0)
      (by unfold stage2Mem; dsimp only [frameNoPool]; rw [hspD, ← hfsp]; sep_frame) ?_
    exact hnext s3 hctrl3 htr3' hfs3F hsigs

/-- Kyber pre-key XEdDSA signature check (`0x01b4 → 0x01fc` and `0x02a4 → 0x0350`, `initProg`). -/
theorem stage1_kpk_sig_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (h1 : x.bundle.spkSig.length = 64)
    (h2 : x.bundle.kpkSig.length = 64)
    (h3 : x.bundle.kpk.length = 1568)
    (hctrl : InInitiate img W s0 s2 0x01b4)
    (htr : s2.trace = s0.trace)
    (hfs : s2.fs.files = x.F)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true)
    (hspk : (modelPrims X ⟨W.C, W.Q⟩).sigVerify
      (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
      (SignalPqxdh.encodeEC (vecU8 (mkBundleE x.bundle h1 h2 h3).spkPub))
      (vecU8 (mkBundleE x.bundle h1 h2 h3).spkSig) = true)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s3 : State),
      InInitiate img W s0 s3 0x01fc →
      s3.trace = s0.trace →
      s3.fs.files = x.F →
      PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ (mkBundleE x.bundle h1 h2 h3) = true →
      SepWPp (initProg img W) (s0.readReg64 .lr) s3
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s2
      (stage2Mem A img x stk s0) Q Qp (initOom s0) := by
  have hbase := hLocal.verifySignature X
  have hspecEq : verifySignatureSpec (modelPrims X ⟨W.C, W.Q⟩) img =
      (verifySigAtStkSpec (modelPrims X ⟨W.C, W.Q⟩)
        (Pqxdh.Shared.pqxdhHookStack + 1280)).inImage img := rfl
  rw [hspecEq] at hbase
  have hcal : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ stk - cliInitiateFrame := by
    have hb := stk_sub_ge_base hstk
    have hp : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ 516880 := by decide
    omega
  exact stage1_kpk_sig_ext_ok (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W)
    hh.toExt hcal hbase hS hstk hstk64 hx8 h1 h2 h3 (inInitiate_toExt hctrl) htr hfs htrust hspk
    hpost hpanic (fun s3 hc3 htr3 hfs3 hsigs => hnext s3 (inInitiate_ofExt hc3) htr3 hfs3 hsigs)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
