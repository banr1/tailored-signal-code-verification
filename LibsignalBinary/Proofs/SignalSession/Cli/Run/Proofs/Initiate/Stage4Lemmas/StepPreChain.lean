/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Cells
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Decode
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExit
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 4 Segment 1: `ephA` Draw/Clamp and `<RootKey>::create_chain` (`+4260 → +4576 / +4508`)

Executes `+4260 → +4496` (`hkSlotBytes` unpack, `coins_fill` `160..192`, X25519 scalar clamp,
`derive_public_key_bytes`, `StaticSecret::drop`, and `<RootKey>::create_chain`), then dispatches
`+4496 → +4576` on `.ok (rk1, ck1)` and `+4496 → +4508` on `.error .invalidKeyAgreement`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local arm64_norm, local wp_norm] cliInitiateFrame_eq BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for attrName in [`arm64_norm, `wp_norm] do
    let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
      | throwError "unknown simproc extension `{attrName}`"
    for declName in [``BitVec.reduceSub, ``BitVec.reduceNeg] do
      Lean.Meta.Simp.addSimprocAttrCore ext declName .local (post := true)

s4_clean_sp_attrs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  Keys.clamp_byte0_norm Keys.clamp_byte0_norm32
  Keys.clamp_byte31_bfxil_norm Keys.clamp_byte31_bfxil_norm'

/-- Total outcome dichotomy for `<RootKey>::create_chain`: every X25519 agreement output produces
either `.ok (rk1, ck1)` or `.error .invalidKeyAgreement`. -/
theorem rootCreateChain_ok_or_err (C : Crypto) (rk : RootKey)
    (their : PublicKey) (our : PrivateKey) :
    (∃ rk1 ck1, rootCreateChain C rk their our = .ok (rk1, ck1)) ∨
      rootCreateChain C rk their our = .error .invalidKeyAgreement := by
  rcases hdh : calculateAgreement C.X their our with _ | ss
  · right
    exact Keys.rootCreateChain_of_calculateAgreement_none C rk their our hdh
  · left
    exact ⟨_, _, Keys.rootCreateChain_of_calculateAgreement_some C rk their our ss hdh⟩

theorem stage4EphVec_len (coins : List (BitVec 8)) :
    (((padCoins coins).toList.drop 160).take 32).length = 32 := by
  simp; decide

/-- 32-byte coin slice at offset `160..192` drawn for `ephA`. -/
abbrev stage4EphVec (coins : List (BitVec 8)) : List.Vector (BitVec 8) 32 :=
  ⟨((padCoins coins).toList.drop 160).take 32, stage4EphVec_len coins⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
private theorem stage4_step_prechain_from_4448
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    (rk0Key ck0Key pq0Key : RootKey)
    (ephClamped : List.Vector (BitVec 8) 32)
    {Frame : SepProp}
    {Qp : State → SepProp → Prop}
    (hStaticDrop : subroutine_ok (s4ProgExt img ext)
      (s4PcExt img ext (ls_rel% "libsignal_cli_handshake::initiate"
        "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop"))
      CliExt.zeroizeSpec)
    (hLocal : Stage4CalleesExtX img P A ext)
    (hTrace : CryptoVerification.LibsignalPublicApi.StoreKit.TraceFsSound (s4ProgExt img ext))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    {s4 : State} (hctrl4 : S4InInitiate img ext s0 s4 4448) (htr4 : s4.trace = s0.trace)
    (hx20_4 : s4.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21_4 : s4.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22_4 : s4.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64)
    (hx23_4 : s4.readReg64 (.gpr 23#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2496#64)
    (hx25_4 : s4.readReg64 (.gpr 25#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (s4ProgExt img ext) (s4PcExt img ext 4496) s4
      (coinsCursorAt img x.coinsP x.coins 192 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗ memRegion (fsp + 2192#64) 24 ∗
        ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗ ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) ∗
        ((fsp + 2288#64) ↦₃₂ 0#32) ∗ ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) ∗
        memRegion (fsp + 2352#64) 100 ∗ ((fsp + 2496#64) ↦ₛ (P.C.pubKey ephClamped).toList) ∗
        memRegion (fsp + 2528#64) 32 ∗ ((fsp + 4064#64) ↦ₛ ephClamped.toList) ∗
        memRegion (fsp + 5632#64) 32 ∗ memRegion (fsp + 5664#64) 40 ∗
        A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame)
      (fun sf Pf => sf.trace = s0.trace ∧ S4InInitiate img ext s0 sf 4496 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧ sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢ coinsCursorAt img x.coinsP x.coins 192 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗ memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗ ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗ ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) ∗
          memRegion (fsp + 2352#64) 100 ∗ ((fsp + 2496#64) ↦ₛ (P.C.pubKey ephClamped).toList) ∗
          ((fsp + 2528#64) ↦ₛ ephClamped.toList) ∗ memRegion (fsp + 4064#64) 32 ∗
          createChainResultAt (fsp + 5632#64) (rootCreateChain P.C rk0Key x.bundle.spk ⟨ephClamped⟩) ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame))
      Qp (initOom s0) := by
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hfp_fsp : Hide (s0.sp - 0x60#64 = fsp + 7312#64) :=
    ⟨by dsimp only [fsp, cliInitiateFrame]; bv_omega⟩
  have hfsp_align : ∀ (st : State), st.sp = fsp → st.spAligned = true :=
    fun st hst => fsp_aligned_of_s0 hstk hspk hst hctrl4.spAligned
  have hrk_ne : fsp + 2224#64 ≠ 0#64 := fsp_add_ne_zero hstk hspk 2224 (by decide)
  have hs4_sp' : s4.sp = fsp := hctrl4.sp
  have hs4_fp : s4.readReg64 .fp = fsp + 7312#64 := hctrl4.fp.trans hfp_fsp.val
  have hs4_x19 : s4.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := hctrl4.x19
  have hs4_x20 : s4.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20_4
  have hs4_x21 : s4.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21_4
  have hs4_x22 : s4.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22_4
  have hs4_x23 : s4.readReg64 (.gpr 23#5) = fsp + 2496#64 := hx23_4
  have hs4_x25 : s4.readReg64 (.gpr 25#5) = fsp + 5632#64 := hx25_4
  have hs4_vr : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hctrl4.vregs
  have hs4_tr : s4.trace = s0.trace := htr4
  have hs4_files : s4.fs.files = s0.fs.files := hctrl4.files0
  have hs4_run : s4.status = .Running := hctrl4.run
  have hs4_align : s4.spAligned = true := hfsp_align s4 hs4_sp'
  clear hx20_4 hx21_4 hx22_4 hx23_4 hx25_4
  clear_value fsp
  stage4_pre_fetches img.base (cliExternsWith ext)
  stage4_bind_entry img.base (cliExternsWith ext)
  examples_hide_fetches
  have hfn_entry : s4EntryExt img ext = fnStart := fnStart_def
  have hs4_pc' : s4.pc = fnStart + bv% (4448) := by
    rw [hctrl4.pc, s4PcExt, hfn_entry]
  have hstdrop := hStaticDrop
  have hcc := sub_ok_at_s4PcExt hLocal.rootKeyCreateChain
    (2 ^ 64 - ls_rel% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"
      "libsignal_cli_handshake::initiate")
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    (num% (ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"))
    cliInitiate_fnOff cliRootKeyCreateChain_fnOff (by decide)
  obtain ⟨sk0, sk1, sk2, sk3, _, hsk_cells⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ephClamped)
  have hsk_4064 : ((fsp + 4064#64) ↦ₛ ephClamped.toList) =
      ((fsp + 4064#64) ↦₆₄ sk0) ∗ ((fsp + 4072#64) ↦₆₄ sk1) ∗
      ((fsp + 4080#64) ↦₆₄ sk2) ∗ ((fsp + 4088#64) ↦₆₄ sk3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hsk_cells (fsp + 4064#64)
  have hsk_2528 : ((fsp + 2528#64) ↦ₛ ephClamped.toList) =
      ((fsp + 2528#64) ↦₆₄ sk0) ∗ ((fsp + 2536#64) ↦₆₄ sk1) ∗
      ((fsp + 2544#64) ↦₆₄ sk2) ∗ ((fsp + 2552#64) ↦₆₄ sk3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hsk_cells (fsp + 2528#64)
  have hm72_split :
      memRegion (fsp + 5632#64) 72 =
        memRegion (fsp + 5632#64) 32 ∗ memRegion (fsp + 5664#64) 40 :=
    ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 32) (k := 40)
      (b' := fsp + 5664#64) rfl (by bv_omega) (by decide)
  apply sepWPp_steps_post (post := fun sf Pf =>
    sf.pc = s4PcExt img ext 4496 ∧ sf.status = .Running ∧
    sf.sp = fsp ∧ sf.readReg64 .fp = s0.sp - 0x60#64 ∧
    sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
    sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
    sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
    sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
    sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
    ImgCallInv img sf ∧ sf.trace = s0.trace ∧
    (Pf ⊢
      coinsCursorAt img x.coinsP x.coins 192 ∗
      ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
      ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      memRegion (fsp + 2192#64) 24 ∗
      ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗
      ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) ∗
      ((fsp + 2288#64) ↦₃₂ 0#32) ∗
      ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) ∗
      memRegion (fsp + 2352#64) 100 ∗
      ((fsp + 2496#64) ↦ₛ (P.C.pubKey ephClamped).toList) ∗
      ((fsp + 2528#64) ↦ₛ ephClamped.toList) ∗
      memRegion (fsp + 4064#64) 32 ∗
      createChainResultAt (fsp + 5632#64)
        (rootCreateChain P.C rk0Key
          x.bundle.spk ⟨ephClamped⟩) ∗
      A.pool ∗
      stackAt fsp (stk - cliInitiateFrame) ∗
      Frame))
  ·
    conv => arg 4; rw [hsk_4064, cells4_eq_memRegion32 (fsp + 2528#64)]
    s4_elim_exists u2528_0; s4_elim_exists u2528_1; s4_elim_exists u2528_2; s4_elim_exists u2528_3
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply sepWPp_step_to_frozen hctrl4.inv
      (mid := fnStart + bv% (ls_rel% "libsignal_cli_handshake::initiate"
        "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs5_F hs5_sym
    have h4064_sk := cells4_entails_memRegion32' (fsp + 4064#64) sk0 sk1 sk2 sk3
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4064_sk
    s4_fold_pre h4064_sk
    s4_rw_pre hsk_2528.symm
    conv => arg 4; rw [stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)]
    conv => arg 4; simp only [sepConj_assoc]
    refine sepWPp_call_wpp_split hstdrop (fsp + 4064#64)
      (T := memRegion (fsp + 4064#64) 32 ∗ stackAt fsp extHookStack)
      (F := ?_)
      hs5_F hs5_sym
      (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [CliExt.zeroizeSpec, CliExt.withStack]
      have hs5_sp_eq := frozen_sp_eq hs5_F fsp (by wp_norm_goal)
      rw [hs5_sp_eq, sepConj_assoc]
      exact Entails.pure_right (by wp_norm_goal) (Entails.of_eq (by s4_ac_rfl))
    intro s6 hs6_pc hs6_run hs6_sp hs6_cs hs6_F hs6_sym
    dsimp only [CliExt.zeroizeSpec, CliExt.withStack]
    have hs5_sp_eq := frozen_sp_eq hs5_F fsp (by wp_norm_goal)
    conv => arg 4; rw [hs5_sp_eq]
    s4_pure_elim
    intro hs6_tr_eq
    have hs6_sp' : s6.sp = fsp := hs6_sp.trans hs5_sp_eq
    have hs6_align : s6.spAligned = true := hfsp_align s6 hs6_sp'
    have hs6_fp : s6.readReg64 .fp = fsp + 7312#64 :=
      (hs6_cs.gpr ⟨29, by decide⟩).trans (by wp_norm_goal)
    have hs6_x19 : s6.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs6_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs6_x20 : s6.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs6_cs.gpr ⟨20, by decide⟩).trans (by wp_norm_goal)
    have hs6_x21 : s6.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs6_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs6_x22 : s6.readReg64 (.gpr 22#5) = fsp + 2304#64 :=
      (hs6_cs.gpr ⟨22, by decide⟩).trans (by wp_norm_goal)
    have hs6_x23 : s6.readReg64 (.gpr 23#5) = fsp + 2496#64 :=
      (hs6_cs.gpr ⟨23, by decide⟩).trans (by wp_norm_goal)
    have hs6_x25 : s6.readReg64 (.gpr 25#5) = fsp + 5632#64 :=
      (hs6_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs6_vr : calleeSavedVRegs s6 = calleeSavedVRegs s0 :=
      hs6_cs.vregs.trans (by simp only [calleeSavedVRegs, arm64_norm]; exact hs4_vr)
    have hs6_tr : s6.trace = s0.trace := hs6_tr_eq.trans (by wp_norm_goal)
    have hs6_pc' : s6.pc = fnStart + bv% (4472) := by
      rw [hs6_pc]; wp_norm_goal
    have hz32 : ((fsp + 4064#64) ↦ₛ List.replicate 32 0#8) ⊢ memRegion (fsp + 4064#64) 32 := by
      have hlen32 : (List.replicate 32 0#8).length = 32 := by decide
      exact hlen32 ▸ pointsToBytes_entails_memRegion (fsp + 4064#64) (List.replicate 32 0#8)
    s4_fold_pre hz32
    s4_rw_pre hm72_split.symm
    s4_rw_pre (stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)).symm
    conv => arg 4; rw [stackAt_fsp_split hstk hstk64 fsp (576 + extractStackExt) (by decide)]
    conv => arg 4; simp only [sepConj_assoc]
    apply sepWPp_step_to_frozen ⟨hs6_F, hs6_sym⟩
      (mid := fnStart + bv% (2 ^ 64 - ls_rel% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"
        "libsignal_cli_handshake::initiate"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs7_F hs7_sym
    refine sepWPp_call_wpp_split hcc
      ⟨fsp + 2224#64, rk0Key,
       fsp + 0x408#64, x.bundle.spk,
       fsp + 2528#64, ⟨ephClamped⟩,
       fsp + 5632#64⟩
      (T := ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 2528#64) ↦ₛ ephClamped.toList) ∗
        memRegion (fsp + 5632#64) 72 ∗
        A.pool ∗
        stackAt fsp (576 + extractStackExt))
      (F := ?_)
      hs7_F hs7_sym
      (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun sm _ _ =>
        hpanic sm _ (by
          dsimp only [Keys.createChainSpecAt, Spec.inImage, rustPanicOnOom]
          exact panic_oom_entails_initOnPanic A img S x stk s0 _ sm _ _
            (by simp only [wp_norm, arm64_norm]; exact hs6_tr)))
      ?_
    · dsimp only [Keys.createChainSpecAt, Spec.inImage]
      have hs7_sp_eq := frozen_sp_eq hs7_F fsp (by wp_norm_goal)
      rw [hs7_sp_eq]
      exact Entails.pure_right ⟨hs7_F, hs7_sym⟩
        (Entails.pure_right ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, hrk_ne⟩
          (Entails.of_eq (by s4_ac_rfl)))
    intro s8 hs8_pc hs8_run hs8_sp hs8_cs hs8_F hs8_sym
    dsimp only [Keys.createChainSpecAt, Spec.inImage]
    have hs7_sp_eq := frozen_sp_eq hs7_F fsp (by wp_norm_goal)
    conv => arg 4; rw [hs7_sp_eq]
    s4_pure_elim
    intro hs8_tr_eq
    have hs8_sp' : s8.sp = fsp := hs8_sp.trans hs7_sp_eq
    have hs8_fp : s8.readReg64 .fp = s0.sp - 0x60#64 :=
      (hs8_cs.gpr ⟨29, by decide⟩).trans (by rw [hfp_fsp.val]; wp_norm_goal)
    have hs8_x19 : s8.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs8_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs8_x20 : s8.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs8_cs.gpr ⟨20, by decide⟩).trans (by wp_norm_goal)
    have hs8_x21 : s8.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs8_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs8_x22 : s8.readReg64 (.gpr 22#5) = fsp + 2304#64 :=
      (hs8_cs.gpr ⟨22, by decide⟩).trans (by wp_norm_goal)
    have hs8_x25 : s8.readReg64 (.gpr 25#5) = fsp + 5632#64 :=
      (hs8_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs8_vr : calleeSavedVRegs s8 = calleeSavedVRegs s0 :=
      hs8_cs.vregs.trans (by simp only [calleeSavedVRegs, arm64_norm]; exact hs6_vr)
    have hs8_tr : s8.trace = s0.trace := hs8_tr_eq.trans (by wp_norm_goal)
    have hs8_pc_init : s8.pc = s4PcExt img ext 4496 := by
      rw [s4PcExt, hfn_entry, hs8_pc]; try wp_norm_goal
    apply SepWPp.of_sepWP_ret
    apply SepWP.done hs8_pc_init hs8_run
    refine ⟨hs8_pc_init, hs8_run, hs8_sp', hs8_fp, hs8_x19, hs8_x20, hs8_x21, hs8_x22, hs8_x25,
      hs8_vr, ⟨hs8_F, hs8_sym⟩, hs8_tr, ?_⟩
    have hstk_back := (stackAt_fsp_split hstk hstk64 fsp (576 + extractStackExt) (by decide)).symm
    s4_rw_ent hstk_back
    exact Entails.of_eq (by s4_ac_rfl)
  · intro sf Pf hsteps
      ⟨hpcf, hrunf, hspf, hfpf, hx19f, hx20f, hx21f, hx22f, hx25f, hvrf, hinvf, htrf, hentf⟩
    have hfilesf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq hTrace hsteps
        (htrf.trans hs4_tr.symm)).trans hs4_files
    exact ⟨htrf, ⟨hpcf, hrunf, hfsp_def.val ▸ hspf, hfpf, hx19f, hfilesf, hinvf, hvrf, hctrl4.spAligned⟩,
      hx20f, hx21f, hx22f, hx25f, hentf⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 800000 in
private theorem stage4_step_prechain_4376_to_4448
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey}
    {Frame : SepProp}
    {Qp : State → SepProp → Prop}
    (hLocal : Stage4CalleesExtX img P A ext)
    (hTrace : CryptoVerification.LibsignalPublicApi.StoreKit.TraceFsSound (s4ProgExt img ext))
    {s2 : State} (hctrl2 : S4InInitiate img ext s0 s2 4376) (htr2 : s2.trace = s0.trace)
    (hx20 : s2.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s2.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s2.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let ephVec := stage4EphVec x.coins
    SepWPp (s4ProgExt img ext) (s4PcExt img ext 4448) s2
      (coinsCursorAt img x.coinsP x.coins 192 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗ memRegion (fsp + 2192#64) 24 ∗
        ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
        ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
        ((fsp + 2288#64) ↦₃₂ 0#32) ∗
        ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
        memRegion (fsp + 2352#64) 100 ∗ memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
        ((fsp + 5632#64) ↦ₛ ((padCoins x.coins).toList.drop 160).take 32) ∗
        memRegion (fsp + 5664#64) 40 ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame)
      (fun sf Pf => sf.trace = s0.trace ∧ S4InInitiate img ext s0 sf 4448 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧ sf.readReg64 (.gpr 23#5) = fsp + 2496#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢ coinsCursorAt img x.coinsP x.coins 192 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗ memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
          memRegion (fsp + 2352#64) 100 ∗
          ((fsp + 2496#64) ↦ₛ (P.C.pubKey (Ratchet.clampScalar ephVec)).toList) ∗
          memRegion (fsp + 2528#64) 32 ∗ ((fsp + 4064#64) ↦ₛ (Ratchet.clampScalar ephVec).toList) ∗
          memRegion (fsp + 5632#64) 32 ∗ memRegion (fsp + 5664#64) 40 ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame))
      Qp (initOom s0) := by
  intro fsp ephVec
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hfp_fsp : Hide (s0.sp - 0x60#64 = fsp + 7312#64) :=
    ⟨by dsimp only [fsp, cliInitiateFrame]; bv_omega⟩
  have hfsp_align : ∀ (st : State), st.sp = fsp → st.spAligned = true :=
    fun st hst => fsp_aligned_of_s0 hstk hspk hst hctrl2.spAligned
  have hs2_sp' : s2.sp = fsp := hctrl2.sp
  have hs2_fp : s2.readReg64 .fp = fsp + 7312#64 := hctrl2.fp.trans hfp_fsp.val
  have hs2_x19 : s2.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := hctrl2.x19
  have hs2_x20 : s2.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20
  have hs2_x21 : s2.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21
  have hs2_x22 : s2.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22
  have hs2_vr : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hctrl2.vregs
  have hs2_files : s2.fs.files = s0.fs.files := hctrl2.files0
  have heph_eq : Hide (((padCoins x.coins).toList.drop 160).take 32 = ephVec.toList) :=
    ⟨rfl⟩
  set ephClamped : List.Vector (BitVec 8) 32 := Ratchet.clampScalar ephVec
  set rk0Key : RootKey := bytesToKey32 (ofU8 dk.rootKey)
  set ck0Key : RootKey := bytesToKey32 (ofU8 dk.chainKey)
  set pq0Key : RootKey := bytesToKey32 (ofU8 dk.pqrKey)
  have hephClamped_def : Hide (ephClamped = Ratchet.clampScalar ephVec) := ⟨rfl⟩
  have hrk0Key_def : Hide (rk0Key = bytesToKey32 (ofU8 dk.rootKey)) := ⟨rfl⟩
  have hck0Key_def : Hide (ck0Key = bytesToKey32 (ofU8 dk.chainKey)) := ⟨rfl⟩
  have hpq0Key_def : Hide (pq0Key = bytesToKey32 (ofU8 dk.pqrKey)) := ⟨rfl⟩
  clear hx20 hx21 hx22
  clear_value fsp ephVec ephClamped rk0Key ck0Key pq0Key
  stage4_pre_fetches img.base (cliExternsWith ext)
  stage4_bind_entry img.base (cliExternsWith ext)
  examples_hide_fetches
  have hfn_entry : s4EntryExt img ext = fnStart := fnStart_def
  have hdpk := sub_ok_at_s4PcExt hLocal.derivePubKeyBytes
    (2 ^ 64 - ls_rel% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"
      "libsignal_cli_handshake::initiate")
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    (num% (ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"))
    cliInitiate_fnOff cliDerivePubKeyBytes_fnOff (by decide)
  obtain ⟨sk0, sk1, sk2, sk3, _, hsk_cells⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ephClamped)
  have hs2_pc' : s2.pc = fnStart + bv% (4376) := by
    rw [hctrl2.pc, s4PcExt, hfn_entry]
  have hs2_run : s2.status = .Running := hctrl2.run
  have hs2_align : s2.spAligned = true := hfsp_align s2 hs2_sp'
  apply sepWPp_steps_post (post := fun sf Pf =>
    sf.pc = s4PcExt img ext 4448 ∧ sf.status = .Running ∧
    sf.sp = fsp ∧ sf.readReg64 .fp = s0.sp - 0x60#64 ∧
    sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
    sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
    sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
    sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
    sf.readReg64 (.gpr 23#5) = fsp + 2496#64 ∧
    sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
    ImgCallInv img sf ∧ sf.trace = s0.trace ∧
    (Pf ⊢
      coinsCursorAt img x.coinsP x.coins 192 ∗
      ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
      ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      memRegion (fsp + 2192#64) 24 ∗
      ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗
      ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) ∗
      ((fsp + 2288#64) ↦₃₂ 0#32) ∗
      ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) ∗
      memRegion (fsp + 2352#64) 100 ∗
      ((fsp + 2496#64) ↦ₛ (P.C.pubKey ephClamped).toList) ∗
      memRegion (fsp + 2528#64) 32 ∗
      ((fsp + 4064#64) ↦ₛ ephClamped.toList) ∗
      memRegion (fsp + 5632#64) 32 ∗
      memRegion (fsp + 5664#64) 40 ∗
      A.pool ∗
      stackAt fsp (stk - cliInitiateFrame) ∗
      Frame))
  ·
    conv => arg 4; rw [heph_eq.val, pointsTo_vec32_split_ends (fsp + 5632#64) ephVec]
    conv => arg 4; simp only [Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply sepWPp_step_to_frozen hctrl2.inv (mid := fnStart + bv% (4428))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs2a_F hs2a_sym
    have hclamp_fold :
        ((fsp + 5632#64) ↦₈ (ephVec.get ⟨0, by decide⟩ &&& 0xf8#8)) ∗
        ((fsp + 5633#64) ↦ₛ (ephVec.toList.drop 1).take 30) ∗
        ((fsp + 5663#64) ↦₈ ((ephVec.get ⟨31, by decide⟩ &&& 0x7f#8) ||| 0x40#8)) =
          ((fsp + 5632#64) ↦ₛ ephClamped.toList) := by
      rw [hephClamped_def.val]
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        pointsTo_vec32_clamp_fold (fsp + 5632#64) ephVec
    have hsk_5632 : ((fsp + 5632#64) ↦ₛ ephClamped.toList) =
        ((fsp + 5632#64) ↦₆₄ sk0) ∗ ((fsp + 5640#64) ↦₆₄ sk1) ∗
        ((fsp + 5648#64) ↦₆₄ sk2) ∗ ((fsp + 5656#64) ↦₆₄ sk3) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hsk_cells (fsp + 5632#64)
    have hsk_4064 : ((fsp + 4064#64) ↦ₛ ephClamped.toList) =
        ((fsp + 4064#64) ↦₆₄ sk0) ∗ ((fsp + 4072#64) ↦₆₄ sk1) ∗
        ((fsp + 4080#64) ↦₆₄ sk2) ∗ ((fsp + 4088#64) ↦₆₄ sk3) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hsk_cells (fsp + 4064#64)
    s4_rw_pre hclamp_fold
    conv => arg 4; rw [hsk_5632, cells4_eq_memRegion32 (fsp + 4064#64)]
    s4_elim_exists u4064_0; s4_elim_exists u4064_1; s4_elim_exists u4064_2; s4_elim_exists u4064_3
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    apply sepWPp_step_to_frozen ⟨hs2a_F, hs2a_sym⟩
      (mid := fnStart + bv% (2 ^ 64 - ls_rel%
        "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"
        "libsignal_cli_handshake::initiate"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs3_F hs3_sym
    have h5632_sk := cells4_entails_memRegion32' (fsp + 5632#64) sk0 sk1 sk2 sk3
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h5632_sk
    s4_fold_pre h5632_sk
    s4_rw_pre hsk_4064.symm
    conv => arg 4; rw [stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)]
    conv => arg 4; simp only [sepConj_assoc]
    refine sepWPp_call_wpp_split hdpk
      ⟨fsp + 4064#64, ephClamped, fsp + 2496#64⟩
      (T := ((fsp + 4064#64) ↦ₛ ephClamped.toList) ∗
        memRegion (fsp + 2496#64) 32 ∗ stackAt fsp extHookStack)
      (F := ?_)
      hs3_F hs3_sym
      (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs) (hfsp_align _ (by wp_norm_goal)) rfl
      (by s4_split_frame)
      ?_
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
    · dsimp only [derivePublicKeyBytesStackSpec]
      have hs3_sp_eq := frozen_sp_eq hs3_F fsp (by wp_norm_goal)
      rw [hs3_sp_eq]
      exact Entails.pure_right ⟨by wp_norm_goal, by wp_norm_goal⟩ (Entails.of_eq (by s4_ac_rfl))
    intro s4 hs4_pc hs4_run hs4_sp hs4_cs hs4_F hs4_sym
    dsimp only [derivePublicKeyBytesStackSpec]
    have hs3_sp_eq := frozen_sp_eq hs3_F fsp (by wp_norm_goal)
    conv => arg 4; rw [hs3_sp_eq]
    s4_pure_elim
    intro hs4_tr_eq
    have hs4_sp' : s4.sp = fsp := hs4_sp.trans hs3_sp_eq
    have hs4_fp : s4.readReg64 .fp = s0.sp - 0x60#64 :=
      (hs4_cs.gpr ⟨29, by decide⟩).trans (by rw [hfp_fsp.val]; wp_norm_goal)
    have hs4_x19 : s4.readReg64 (.gpr 19#5) = s0.readReg64 .x8 :=
      (hs4_cs.gpr ⟨19, by decide⟩).trans (by wp_norm_goal)
    have hs4_x20 : s4.readReg64 (.gpr 20#5) = fsp + 0x348#64 :=
      (hs4_cs.gpr ⟨20, by decide⟩).trans (by wp_norm_goal)
    have hs4_x21 : s4.readReg64 (.gpr 21#5) = fsp + 0x388#64 :=
      (hs4_cs.gpr ⟨21, by decide⟩).trans (by wp_norm_goal)
    have hs4_x22 : s4.readReg64 (.gpr 22#5) = fsp + 2304#64 :=
      (hs4_cs.gpr ⟨22, by decide⟩).trans (by wp_norm_goal)
    have hs4_x23 : s4.readReg64 (.gpr 23#5) = fsp + 2496#64 :=
      (hs4_cs.gpr ⟨23, by decide⟩).trans (by wp_norm_goal)
    have hs4_x25 : s4.readReg64 (.gpr 25#5) = fsp + 5632#64 :=
      (hs4_cs.gpr ⟨25, by decide⟩).trans (by wp_norm_goal)
    have hs4_vr : calleeSavedVRegs s4 = calleeSavedVRegs s0 :=
      hs4_cs.vregs.trans (by simp only [calleeSavedVRegs, arm64_norm]; exact hs2_vr)
    have hs4_tr : s4.trace = s0.trace := hs4_tr_eq.trans (by wp_norm_goal)
    have hs4_pc_init : s4.pc = s4PcExt img ext 4448 := by
      rw [s4PcExt, hfn_entry, hs4_pc]; try wp_norm_goal
    apply SepWPp.of_sepWP_ret
    apply SepWP.done hs4_pc_init hs4_run
    refine ⟨hs4_pc_init, hs4_run, hs4_sp', hs4_fp, hs4_x19, hs4_x20, hs4_x21, hs4_x22,
      hs4_x23, hs4_x25, hs4_vr, ⟨hs4_F, hs4_sym⟩, hs4_tr, ?_⟩
    have hstk_back := (stackAt_fsp_split hstk hstk64 fsp extHookStack (by decide)).symm
    s4_rw_ent hstk_back
    exact Entails.of_eq (by s4_ac_rfl)
  · intro sf Pf hsteps
      ⟨hpcf, hrunf, hspf, hfpf, hx19f, hx20f, hx21f, hx22f, hx23f, hx25f, hvrf, hinvf, htrf, hentf⟩
    have hfilesf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq hTrace hsteps
        (htrf.trans htr2.symm)).trans hs2_files
    exact ⟨htrf, ⟨hpcf, hrunf, hfsp_def.val ▸ hspf, hfpf, hx19f, hfilesf, hinvf, hvrf, hctrl2.spAligned⟩,
      hx20f, hx21f, hx22f, hx23f, hx25f, hentf⟩

private theorem prechain_4260_mem_unpack (fsp : BitVec 64) (Rest : SepProp) :
    memRegion (fsp + 2192#64) 24 ∗ memRegion (fsp + 2224#64) 32 ∗
    memRegion (fsp + 2256#64) 36 ∗ memRegion (fsp + 2304#64) 32 ∗
    memRegion (fsp + 5632#64) 32 ∗ Rest =
    ∃∗ u2192_0 : BitVec 64, ∃∗ u2192_1 : BitVec 64, ∃∗ u2192_2 : BitVec 64,
    ∃∗ u2224_0 : BitVec 64, ∃∗ u2224_1 : BitVec 64, ∃∗ u2224_2 : BitVec 64, ∃∗ u2224_3 : BitVec 64,
    ∃∗ u2256_0 : BitVec 64, ∃∗ u2256_1 : BitVec 64, ∃∗ u2256_2 : BitVec 64, ∃∗ u2256_3 : BitVec 64,
    ∃∗ u2288 : BitVec 32,
    ∃∗ u2304_0 : BitVec 64, ∃∗ u2304_1 : BitVec 64, ∃∗ u2304_2 : BitVec 64, ∃∗ u2304_3 : BitVec 64,
    ∃∗ u5632_0 : BitVec 64, ∃∗ u5632_1 : BitVec 64, ∃∗ u5632_2 : BitVec 64, ∃∗ u5632_3 : BitVec 64,
      ((fsp + 2192#64) ↦₆₄ u2192_0) ∗ ((fsp + 2200#64) ↦₆₄ u2192_1) ∗ ((fsp + 2208#64) ↦₆₄ u2192_2) ∗
      ((fsp + 2224#64) ↦₆₄ u2224_0) ∗ ((fsp + 2232#64) ↦₆₄ u2224_1) ∗
      ((fsp + 2240#64) ↦₆₄ u2224_2) ∗ ((fsp + 2248#64) ↦₆₄ u2224_3) ∗
      ((fsp + 2256#64) ↦₆₄ u2256_0) ∗ ((fsp + 2264#64) ↦₆₄ u2256_1) ∗
      ((fsp + 2272#64) ↦₆₄ u2256_2) ∗ ((fsp + 2280#64) ↦₆₄ u2256_3) ∗ ((fsp + 2288#64) ↦₃₂ u2288) ∗
      ((fsp + 2304#64) ↦₆₄ u2304_0) ∗ ((fsp + 2312#64) ↦₆₄ u2304_1) ∗
      ((fsp + 2320#64) ↦₆₄ u2304_2) ∗ ((fsp + 2328#64) ↦₆₄ u2304_3) ∗
      ((fsp + 5632#64) ↦₆₄ u5632_0) ∗ ((fsp + 5640#64) ↦₆₄ u5632_1) ∗
      ((fsp + 5648#64) ↦₆₄ u5632_2) ∗ ((fsp + 5656#64) ↦₆₄ u5632_3) ∗ Rest := by
  rw [cells3_eq_memRegion24 (fsp + 2192#64), cells4_eq_memRegion32 (fsp + 2224#64),
      cells4_4_eq_memRegion36 (fsp + 2256#64), cells4_eq_memRegion32 (fsp + 2304#64),
      cells4_eq_memRegion32 (fsp + 5632#64)]
  s4_exists_eq

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 800000 in
private theorem stage4_step_prechain_4260_to_cf
    {img : Obj.Image} {ext : String → Option (State → State)} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey} {hkSlotBytes : List (BitVec 8)}
    {Frame : SepProp} {Qp : State → SepProp → Prop}
    (hTrace : CryptoVerification.LibsignalPublicApi.StoreKit.TraceFsSound (s4ProgExt img ext)) {s : State}
    (hctrl : S4InInitiate img ext s0 s 4260) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64)
    (hrk_bv : (ofU8 dk.rootKey).length = 32) (hpq_bv : (ofU8 dk.pqrKey).length = 32)
    (hck_bv : (ofU8 dk.chainKey).length = 32)
    (hhk : hkSlotBytes = ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (s4ProgExt img ext)
      (s4PcExt img ext (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill")) s
      (memRegion (fsp + 2192#64) 24 ∗ memRegion (fsp + 2224#64) 32 ∗
        memRegion (fsp + 2256#64) 36 ∗ memRegion (fsp + 2304#64) 32 ∗
        memRegion (fsp + 5632#64) 32 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧
        sf.pc = s4PcExt img ext (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill") ∧
        sf.status = .Running ∧ sf.sp = fsp ∧ sf.readReg64 .lr = s4PcExt img ext 4376 ∧
        sf.readReg64 .x0 = fsp + 5632#64 ∧ sf.readReg64 .x1 = 32#64 ∧
        sf.readReg64 .fp = s0.sp - 0x60#64 ∧ sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧ sf.fs.files = s0.fs.files ∧
        ImgCallInv img sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        (Pf ⊢ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
          memRegion (fsp + 2352#64) 100 ∗ memRegion (fsp + 5632#64) 32 ∗ Frame))
      Qp (initOom s0) := by
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hfp_fsp : Hide (s0.sp - 0x60#64 = fsp + 7312#64) :=
    ⟨by dsimp only [fsp, cliInitiateFrame]; bv_omega⟩
  have hsp0 : s.sp = fsp := hctrl.sp
  have hfp0 : s.readReg64 .fp = fsp + 7312#64 := hctrl.fp.trans hfp_fsp.val
  have hx20 : s.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20
  have hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21
  have hx22_0 : s.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22
  have halign0 : s.spAligned = true := fsp_aligned_of_s0 hstk hspk hsp0 hctrl.spAligned
  have hrun0 : s.status = .Running := hctrl.run
  have hx19_0 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := hctrl.x19
  have hvr0 : calleeSavedVRegs s = calleeSavedVRegs s0 := hctrl.vregs
  set rk0Key : RootKey := bytesToKey32 (ofU8 dk.rootKey)
  set ck0Key : RootKey := bytesToKey32 (ofU8 dk.chainKey)
  set pq0Key : RootKey := bytesToKey32 (ofU8 dk.pqrKey)
  have hrk_key_eq : keyToBytes32 rk0Key = ofU8 dk.rootKey :=
    Keys.keyToBytes32_bytesToKey32 (ofU8 dk.rootKey) hrk_bv
  have hpq_key_eq : keyToBytes32 pq0Key = ofU8 dk.pqrKey :=
    Keys.keyToBytes32_bytesToKey32 (ofU8 dk.pqrKey) hpq_bv
  have hck_key_eq : keyToBytes32 ck0Key = ofU8 dk.chainKey :=
    Keys.keyToBytes32_bytesToKey32 (ofU8 dk.chainKey) hck_bv
  clear hx22 hfsp_def
  clear_value fsp rk0Key ck0Key pq0Key
  obtain ⟨rk0, rk1w, rk2, rk3, _, hrk_cells⟩ := exists_unpack64_of_length_32 hrk_bv
  obtain ⟨pq0, pq1, pq2, pq3, _, hpq_cells⟩ := exists_unpack64_of_length_32 hpq_bv
  obtain ⟨ck0w, ck1w, ck2w, ck3w, _, hck_cells⟩ := exists_unpack64_of_length_32 hck_bv
  apply sepWPp_steps_post (post := fun sf Pf =>
    sf.trace = s0.trace ∧
    sf.pc = s4PcExt img ext (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill") ∧
    sf.status = .Running ∧ sf.sp = fsp ∧ sf.readReg64 .lr = s4PcExt img ext 4376 ∧
    sf.readReg64 .x0 = fsp + 5632#64 ∧ sf.readReg64 .x1 = 32#64 ∧
    sf.readReg64 .fp = s0.sp - 0x60#64 ∧ sf.readReg64 (.gpr 19#5) = s0.readReg64 .x8 ∧
    sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
    sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧ ImgCallInv img sf ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
    (Pf ⊢ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ memRegion (fsp + 2192#64) 24 ∗
      ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) ∗ ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) ∗
      ((fsp + 2288#64) ↦₃₂ 0#32) ∗ ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) ∗
      memRegion (fsp + 2352#64) 100 ∗ memRegion (fsp + 5632#64) 32 ∗ Frame))
  · refine sepWPp_mono_pre
      (Entails.of_eq (prechain_4260_mem_unpack fsp
        (((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗ Frame))) ?_
    refine SepWPp.exists_elim fun u2192_0 => SepWPp.exists_elim fun u2192_1 =>
      SepWPp.exists_elim fun u2192_2 =>
      SepWPp.exists_elim fun u2224_0 => SepWPp.exists_elim fun u2224_1 =>
      SepWPp.exists_elim fun u2224_2 => SepWPp.exists_elim fun u2224_3 =>
      SepWPp.exists_elim fun u2256_0 => SepWPp.exists_elim fun u2256_1 =>
      SepWPp.exists_elim fun u2256_2 => SepWPp.exists_elim fun u2256_3 =>
      SepWPp.exists_elim fun u2288 =>
      SepWPp.exists_elim fun u2304_0 => SepWPp.exists_elim fun u2304_1 =>
      SepWPp.exists_elim fun u2304_2 => SepWPp.exists_elim fun u2304_3 =>
      SepWPp.exists_elim fun u5632_0 => SepWPp.exists_elim fun u5632_1 =>
      SepWPp.exists_elim fun u5632_2 => SepWPp.exists_elim fun u5632_3 => ?_
    conv => arg 4; rw [hhk,
      hkSlot100_unpack (fsp + 2352#64) (ofU8 dk.rootKey) (ofU8 dk.pqrKey) (ofU8 dk.chainKey)
        hrk_cells hpq_cells hck_cells hrk_bv hpq_bv hck_bv]
    conv => arg 4; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    stage4_pre_fetches img.base (cliExternsWith ext)
    stage4_bind_entry img.base (cliExternsWith ext)
    examples_hide_fetches
    have hfn_entry : s4EntryExt img ext = fnStart := fnStart_def
    have hpc0 : s.pc = fnStart + bv% (4260) := by rw [hctrl.pc, s4PcExt, hfn_entry]
    apply sepWPp_step_to_frozen hctrl.inv
      (mid := fnStart + bv% (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hs1_F hs1_sym
    apply SepWPp.of_sepWP_ret
    apply SepWP.done (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs)
    have h2192_f := cells3_entails_memRegion24 (fsp + 2192#64) pq1 pq2 pq3
    have h2352_f := hkSlot100_cells_entails_memRegion100 (fsp + 2352#64)
      rk0 rk1w rk2 rk3 pq0 pq1 pq2 pq3 ck0w ck1w ck2w ck3w
    have h5632_f := cells4_entails_memRegion32' (fsp + 5632#64) 0#64 0#64 0#64 0#64
    have hrk_2224 : ((fsp + 2224#64) ↦ₛ keyToBytes32 rk0Key) =
        ((fsp + 2224#64) ↦₆₄ rk0) ∗ ((fsp + 2232#64) ↦₆₄ rk1w) ∗
        ((fsp + 2240#64) ↦₆₄ rk2) ∗ ((fsp + 2248#64) ↦₆₄ rk3) := by
      rw [hrk_key_eq, hrk_cells (fsp + 2224#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hck_2256 : ((fsp + 2256#64) ↦ₛ keyToBytes32 ck0Key) =
        ((fsp + 2256#64) ↦₆₄ ck0w) ∗ ((fsp + 2264#64) ↦₆₄ ck1w) ∗
        ((fsp + 2272#64) ↦₆₄ ck2w) ∗ ((fsp + 2280#64) ↦₆₄ ck3w) := by
      rw [hck_key_eq, hck_cells (fsp + 2256#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hpq_2304 : ((fsp + 2304#64) ↦ₛ keyToBytes32 pq0Key) =
        ((fsp + 2304#64) ↦₆₄ pq0) ∗ ((fsp + 2312#64) ↦₆₄ pq1) ∗
        ((fsp + 2320#64) ↦₆₄ pq2) ∗ ((fsp + 2328#64) ↦₆₄ pq3) := by
      rw [hpq_key_eq, hpq_cells (fsp + 2304#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h2192_f h2352_f h5632_f
    refine ⟨by wp_norm_goal, by rw [s4PcExt, hfn_entry]; try wp_norm_goal, by wp_norm_lhs,
      by wp_norm_goal, by rw [s4PcExt, hfn_entry]; try wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by rw [hfp_fsp.val]; wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, ⟨hs1_F, hs1_sym⟩,
      by simp only [calleeSavedVRegs, arm64_norm]; exact hvr0, ?_⟩
    rw [hrk_2224, hck_2256, hpq_2304]
    s4_fold_ent h2192_f; s4_fold_ent h2352_f; s4_fold_ent h5632_f
    exact Entails.of_eq (by s4_ac_rfl)
  · intro sf Pf hsteps
      ⟨htrf, hpcf, hrunf, hspf, hlrf, hx0f, hx1f, hfpf, hx19f, hx20f, hx21f, hx22f, hinvf, hvrf, hentf⟩
    have hfilesf : sf.fs.files = s0.fs.files :=
      (files_eq_of_steps_trace_eq hTrace hsteps
        (htrf.trans htr.symm)).trans hctrl.files0
    exact ⟨htrf, hpcf, hrunf, hspf, hlrf, hx0f, hx1f, hfpf, hx19f, hx20f, hx21f, hx22f,
      hfilesf, hinvf, hvrf, hentf⟩

private theorem stage4_call_coins_fill_to_4376
    {img : Obj.Image} {ext : String → Option (State → State)} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 s1 : State} (hspk : stk ≤ s0.sp.toNat)
    {Frame : SepProp} {Qp : State → SepProp → Prop}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (s4ProgExt img ext) ((s4ProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpc1 : s1.pc = s4PcExt img ext (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill"))
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hlr1 : s1.readReg64 .lr = s4PcExt img ext 4376)
    (hx0_1 : s1.readReg64 .x0 = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64)
    (hx1_1 : s1.readReg64 .x1 = 32#64) (hfp1 : s1.readReg64 .fp = s0.sp - 0x60#64)
    (hx19_1 : s1.readReg64 (.gpr 19#5) = s0.readReg64 .x8)
    (hx20_1 : s1.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21_1 : s1.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22_1 : s1.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64)
    (hfiles1 : s1.fs.files = s0.fs.files) (hinv1 : ImgCallInv img s1)
    (hvr1 : calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hspAligned0 : s0.spAligned = true) (htr1 : s1.trace = s0.trace) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (s4ProgExt img ext) (s4PcExt img ext 4376) s1
      (coinsCursorAt img x.coinsP x.coins 160 ∗ memRegion (fsp + 5632#64) 32 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ S4InInitiate img ext s0 sf 4376 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        (Pf ⊢ coinsCursorAt img x.coinsP x.coins 192 ∗
          ((fsp + 5632#64) ↦ₛ ((padCoins x.coins).toList.drop 160).take 32) ∗
          stackAt fsp (stk - cliInitiateFrame) ∗ Frame))
      Qp (initOom s0) := by
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hsp1' : s1.sp = fsp := hsp1
  have hx0_1' : s1.readReg64 .x0 = fsp + 5632#64 := hx0_1
  have hx20_1' : s1.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20_1
  have hx21_1' : s1.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21_1
  have hx22_1' : s1.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22_1
  have halign1 : s1.spAligned = true := fsp_aligned_of_s0 hstk hspk hsp1' hspAligned0
  clear hx0_1 hx20_1 hx21_1 hx22_1 hsp1
  clear_value fsp
  have hcf := sub_ok_at_s4PcExt (hCoins (coinsFill_stk_le hstk) (stk_sub_le_63 hstk64))
    (ls_rel% "libsignal_cli_handshake::initiate" "signal_session_coins_fill")
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    (num% (ls_off% "signal_session_coins_fill"))
    cliInitiate_fnOff cliCoinsFill_fnOff (by decide)
  refine sepWPp_call_wpp_split hcf ⟨fsp + 5632#64, 32, x.coinsP, x.coins, 160⟩
    (T := coinsCursorAt img x.coinsP x.coins 160 ∗
      memRegion (fsp + 5632#64) 32 ∗ stackAt fsp (stk - cliInitiateFrame))
    (F := Frame) hinv1.1 hinv1.2 hpc1 hrun1 halign1 hlr1 (by simp only [sepConj_assoc]) ?_
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim) ?_
  · dsimp only [coinsFillSpec, Spec.inImage]
    rw [hsp1']
    exact Entails.pure_right ⟨hinv1.1, hinv1.2⟩
      (Entails.pure_right ⟨hx0_1', hx1_1, hcoinsLt, by decide⟩
        (Entails.of_eq (by simp only [])))
  intro s2 hs2_pc hs2_run hs2_sp hs2_cs hs2_F hs2_sym
  dsimp only [coinsFillSpec, Spec.inImage]
  conv => arg 4; rw [hsp1', show (160 : Nat) + 32 = 192 from rfl]
  s4_pure_elim
  rintro ⟨hs2_tr_eq, hs2_fs_eq⟩
  have hs2_sp' : s2.sp = fsp := hs2_sp.trans hsp1'
  have hs2_fp : s2.readReg64 .fp = s0.sp - 0x60#64 := (hs2_cs.gpr ⟨29, by decide⟩).trans hfp1
  have hs2_x19 : s2.readReg64 (.gpr 19#5) = s0.readReg64 .x8 := (hs2_cs.gpr ⟨19, by decide⟩).trans hx19_1
  have hs2_x20 : s2.readReg64 (.gpr 20#5) = fsp + 0x348#64 := (hs2_cs.gpr ⟨20, by decide⟩).trans hx20_1'
  have hs2_x21 : s2.readReg64 (.gpr 21#5) = fsp + 0x388#64 := (hs2_cs.gpr ⟨21, by decide⟩).trans hx21_1'
  have hs2_x22 : s2.readReg64 (.gpr 22#5) = fsp + 2304#64 := (hs2_cs.gpr ⟨22, by decide⟩).trans hx22_1'
  have hs2_vr : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hs2_cs.vregs.trans hvr1
  have hs2_tr : s2.trace = s0.trace := hs2_tr_eq.trans htr1
  have hs2_files : s2.fs.files = s0.fs.files := by rw [hs2_fs_eq]; exact hfiles1
  have hctrl2 : S4InInitiate img ext s0 s2 4376 :=
    ⟨hs2_pc, hs2_run, hfsp_def.val ▸ hs2_sp', hs2_fp, hs2_x19, hs2_files,
      ⟨hs2_F, hs2_sym⟩, hs2_vr, hspAligned0⟩
  apply SepWPp.of_sepWP_ret
  apply SepWP.done hs2_pc hs2_run
  exact ⟨hs2_tr, hctrl2, hs2_x20, hs2_x21, hs2_x22, Entails.of_eq (by simp only [])⟩

private theorem stage4_step_prechain_to_4376
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} {S : RunSem} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey} {hkSlotBytes : List (BitVec 8)}
    {Frame : SepProp} {Qp : State → SepProp → Prop}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (s4ProgExt img ext) ((s4ProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hTrace : CryptoVerification.LibsignalPublicApi.StoreKit.TraceFsSound (s4ProgExt img ext))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (_hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) {s : State}
    (hctrl : S4InInitiate img ext s0 s 4260) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64)
    (hrk_bv : (ofU8 dk.rootKey).length = 32) (hpq_bv : (ofU8 dk.pqrKey).length = 32)
    (hck_bv : (ofU8 dk.chainKey).length = 32)
    (hhk : hkSlotBytes = ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (s4ProgExt img ext) (s4PcExt img ext 4376) s
      (coinsCursorAt img x.coinsP x.coins 160 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 2192#64) 24 ∗ memRegion (fsp + 2224#64) 32 ∗
        memRegion (fsp + 2256#64) 36 ∗ memRegion (fsp + 2304#64) 32 ∗
        ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗ memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
        memRegion (fsp + 5632#64) 72 ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ S4InInitiate img ext s0 sf 4376 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        (Pf ⊢ coinsCursorAt img x.coinsP x.coins 192 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗ memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
          memRegion (fsp + 2352#64) 100 ∗ memRegion (fsp + 2496#64) 32 ∗
          memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
          ((fsp + 5632#64) ↦ₛ ((padCoins x.coins).toList.drop 160).take 32) ∗
          memRegion (fsp + 5664#64) 40 ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame))
      Qp (initOom s0) := by
  intro fsp
  have hfsp_eq : Hide (s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp) := ⟨rfl⟩
  clear_value fsp
  have hm72_split : memRegion (fsp + 5632#64) 72 =
      memRegion (fsp + 5632#64) 32 ∗ memRegion (fsp + 5664#64) 40 :=
    ProofLib.memRegion_split' (b := fsp + 5632#64) (n := 32) (k := 40)
      (b' := fsp + 5664#64) rfl (by bv_omega) (by decide)
  let RestCf : SepProp :=
    coinsCursorAt img x.coinsP x.coins 160 ∗ ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      memRegion (fsp + 2496#64) 32 ∗ memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
      memRegion (fsp + 5664#64) 40 ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame
  refine sepWPp_seq_files hTrace
    (sepWPp_mono_pre
      (by dsimp only [RestCf]; rw [hm72_split, hfsp_eq.val]; exact Entails.of_eq (by s4_ac_rfl))
      (stage4_step_prechain_4260_to_cf (Frame := RestCf)
        hstk hspk hTrace hctrl htr hx20 hx21 hx22 hrk_bv hpq_bv hck_bv hhk)) ?_
  rintro s1 P1 _ _ _
    ⟨htr1, hpc1, hrun1, hsp1, hlr1, hx0_1, hx1_1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1,
      hfiles1, hinv1, hvr1, hent1⟩
  let FrameCf : SepProp :=
    ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
      memRegion (fsp + 2192#64) 24 ∗
      ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
      ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
      ((fsp + 2288#64) ↦₃₂ 0#32) ∗
      ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
      memRegion (fsp + 2352#64) 100 ∗ memRegion (fsp + 2496#64) 32 ∗
      memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
      memRegion (fsp + 5664#64) 40 ∗ A.pool ∗ Frame
  have hent1_cf :
      P1 ⊢ coinsCursorAt img x.coinsP x.coins 160 ∗
        memRegion ((s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64) 32 ∗
        stackAt (s0.sp - BitVec.ofNat 64 cliInitiateFrame) (stk - cliInitiateFrame) ∗
        FrameCf := by
    refine Entails.trans hent1 ?_
    dsimp only [RestCf, FrameCf]
    rw [hfsp_eq.val]
    exact Entails.of_eq (by s4_ac_rfl)
  apply sepWPp_steps_post
    (sepWPp_mono_pre hent1_cf
      (stage4_call_coins_fill_to_4376 (Frame := FrameCf)
        hstk hstk64 hspk hCoins hcoinsLt hpc1 hrun1 hsp1 hlr1 hx0_1 hx1_1 hfp1 hx19_1
        hx20_1 hx21_1 hx22_1 hfiles1 hinv1 hvr1 hctrl.spAligned htr1))
  intro sf Pf _ ⟨htrf, hctrlf, hx20f, hx21f, hx22f, hentf⟩
  rw [hfsp_eq.val] at hx20f hx21f hx22f hentf
  refine ⟨htrf, hctrlf, hx20f, hx21f, hx22f, Entails.trans hentf ?_⟩
  dsimp only [FrameCf]
  exact Entails.of_eq (by s4_ac_rfl)

theorem stage4_step_prechain_to_4496_ext
    {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey} {hkSlotBytes : List (BitVec 8)}
    {Frame : SepProp} {Qp : State → SepProp → Prop}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (s4ProgExt img ext) ((s4ProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hStaticDrop : subroutine_ok (s4ProgExt img ext)
      (s4PcExt img ext (ls_rel% "libsignal_cli_handshake::initiate"
        "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop"))
      CliExt.zeroizeSpec)
    (hLocal : Stage4CalleesExtX img P A ext)
    (hTrace : CryptoVerification.LibsignalPublicApi.StoreKit.TraceFsSound (s4ProgExt img ext))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) {s : State}
    (hctrl : S4InInitiate img ext s0 s 4260) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64)
    (hrk_bv : (ofU8 dk.rootKey).length = 32) (hpq_bv : (ofU8 dk.pqrKey).length = 32)
    (hck_bv : (ofU8 dk.chainKey).length = 32)
    (hhk : hkSlotBytes = ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let ephVec := stage4EphVec x.coins
    SepWPp (s4ProgExt img ext) (s4PcExt img ext 4496) s
      (coinsCursorAt img x.coinsP x.coins 160 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 2192#64) 24 ∗ memRegion (fsp + 2224#64) 32 ∗
        memRegion (fsp + 2256#64) 36 ∗ memRegion (fsp + 2304#64) 32 ∗
        ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗ memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
        memRegion (fsp + 5632#64) 72 ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ S4InInitiate img ext s0 sf 4496 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢ coinsCursorAt img x.coinsP x.coins 192 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗ memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
          memRegion (fsp + 2352#64) 100 ∗
          ((fsp + 2496#64) ↦ₛ (P.C.pubKey (Ratchet.clampScalar ephVec)).toList) ∗
          ((fsp + 2528#64) ↦ₛ (Ratchet.clampScalar ephVec).toList) ∗
          memRegion (fsp + 4064#64) 32 ∗
          createChainResultAt (fsp + 5632#64)
            (rootCreateChain P.C (bytesToKey32 (ofU8 dk.rootKey))
              x.bundle.spk ⟨Ratchet.clampScalar ephVec⟩) ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame))
      Qp (initOom s0) := by
  intro fsp ephVec
  refine sepWPp_seq_files hTrace
    (stage4_step_prechain_to_4376 hstk hstk64 hspk hCoins hTrace hcoinsLt hpanic
      hctrl htr hx20 hx21 hx22 hrk_bv hpq_bv hck_bv hhk) ?_
  rintro s2 P2 _ _ _ ⟨htr2, hctrl2, hx20_2, hx21_2, hx22_2, hent2⟩
  refine sepWPp_seq_files hTrace
    (sepWPp_mono_pre hent2
      (stage4_step_prechain_4376_to_4448 hstk hstk64 hspk hLocal hTrace hctrl2 htr2
        hx20_2 hx21_2 hx22_2)) ?_
  rintro s4 P4 _ _ _ ⟨htr4, hctrl4, hx20_4, hx21_4, hx22_4, hx23_4, hx25_4, hent4⟩
  exact sepWPp_mono_pre hent4
    (stage4_step_prechain_from_4448 hstk hstk64 hspk
      (bytesToKey32 (ofU8 dk.rootKey))
      (bytesToKey32 (ofU8 dk.chainKey))
      (bytesToKey32 (ofU8 dk.pqrKey))
      (Ratchet.clampScalar ephVec)
      hStaticDrop hLocal hTrace hpanic hctrl4 htr4 hx20_4 hx21_4 hx22_4 hx23_4 hx25_4)

theorem stage4_step_prechain_to_4496
    {img : Obj.Image} {A : RustAlloc} {W : CliHooks} {S : RunSem} {B : RunBudgets}
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} (hspk : stk ≤ s0.sp.toNat)
    {dk : SignalPqxdh.DRKey} {hkSlotBytes : List (BitVec 8)}
    {Frame : SepProp} {Qp : State → SepProp → Prop}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hLocal : InitLocalCallees img A W stk) (hcoinsLt : x.coins.length < 2 ^ 63)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) {s : State}
    (hctrl : InInitiate img W s0 s 4260) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64)
    (hrk_bv : (ofU8 dk.rootKey).length = 32) (hpq_bv : (ofU8 dk.pqrKey).length = 32)
    (hck_bv : (ofU8 dk.chainKey).length = 32)
    (hhk : hkSlotBytes = ofU8 dk.rootKey ++ ofU8 dk.pqrKey ++ ofU8 dk.chainKey ++ unpack32 0#32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let ephVec := stage4EphVec x.coins
    SepWPp (initProg img W) (initPc img W 4496) s
      (coinsCursorAt img x.coinsP x.coins 160 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        memRegion (fsp + 2192#64) 24 ∗ memRegion (fsp + 2224#64) 32 ∗
        memRegion (fsp + 2256#64) 36 ∗ memRegion (fsp + 2304#64) 32 ∗
        ((fsp + 2352#64) ↦ₛ hkSlotBytes) ∗ memRegion (fsp + 2496#64) 32 ∗
        memRegion (fsp + 2528#64) 32 ∗ memRegion (fsp + 4064#64) 32 ∗
        memRegion (fsp + 5632#64) 72 ∗ A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ InInitiate img W s0 sf 4496 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢ coinsCursorAt img x.coinsP x.coins 192 ∗ ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
          ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗ memRegion (fsp + 2192#64) 24 ∗
          ((fsp + 2224#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.rootKey))) ∗
          ((fsp + 2256#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.chainKey))) ∗
          ((fsp + 2288#64) ↦₃₂ 0#32) ∗
          ((fsp + 2304#64) ↦ₛ keyToBytes32 (bytesToKey32 (ofU8 dk.pqrKey))) ∗
          memRegion (fsp + 2352#64) 100 ∗
          ((fsp + 2496#64) ↦ₛ (W.C.pubKey (Ratchet.clampScalar ephVec)).toList) ∗
          ((fsp + 2528#64) ↦ₛ (Ratchet.clampScalar ephVec).toList) ∗
          memRegion (fsp + 4064#64) 32 ∗
          createChainResultAt (fsp + 5632#64)
            (rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey))
              x.bundle.spk ⟨Ratchet.clampScalar ephVec⟩) ∗
          A.pool ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Frame))
      Qp (initOom s0) := by
  intro fsp ephVec
  apply sepWPp_steps_post
    (stage4_step_prechain_to_4496_ext (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W)
      hstk hstk64 hspk hCoins (zeroizeSecretSpec_to_cliExt (staticDrop_ok_at_init img W))
      (Stage4CalleesExt.of_initLocalCallees hLocal).to_extX (initProg_traceFsSound img W)
      hcoinsLt hpanic ⟨hctrl.pc, hctrl.run, hctrl.sp, hctrl.fp, hctrl.x19, hctrl.files0,
        hctrl.inv, hctrl.vregs, hctrl.spAligned⟩
      htr hx20 hx21 hx22 hrk_bv hpq_bv hck_bv hhk)
  rintro sf Pf _ ⟨htrf, hc, hx20f, hx21f, hx22f, hx25f, hentf⟩
  exact ⟨htrf, ⟨hc.pc, hc.run, hc.sp, hc.fp, hc.x19, hc.files0, hc.inv, hc.vregs, hc.spAligned⟩,
    hx20f, hx21f, hx22f, hx25f, hentf⟩

theorem stage4_branch_4496_ok_ext
    {img : Obj.Image} {ext : String → Option (State → State)} {B : RunBudgets} {stk : Nat}
    {s0 s : State} {rk1 : RootKey} {ck1 : ChainKey} {Frame : SepProp}
    {Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk) (hspk : stk ≤ s0.sp.toNat)
    (hctrl : S4InInitiate img ext s0 s 4496) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64)
    (hx25 : s.readReg64 (.gpr 25#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (s4ProgExt img ext) (s4PcExt img ext 4576) s
      (((fsp + 5632#64) ↦₃₂ 0#32) ∗ ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
        ((fsp + 5668#64) ↦ₛ chainKeyBytes ck1) ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ S4InInitiate img ext s0 sf 4576 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢ ((fsp + 5632#64) ↦₃₂ 0#32) ∗ ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
          ((fsp + 5668#64) ↦ₛ chainKeyBytes ck1) ∗ Frame))
      Qp (initOom s0) := by
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hsp0 : s.sp = fsp := hctrl.sp
  have halign0 : s.spAligned = true := fsp_aligned_of_s0 hstk hspk hsp0 hctrl.spAligned
  have hx20 : s.readReg64 (.gpr 20#5) = fsp + 0x348#64 := hx20
  have hx21 : s.readReg64 (.gpr 21#5) = fsp + 0x388#64 := hx21
  have hx22 : s.readReg64 (.gpr 22#5) = fsp + 2304#64 := hx22
  have hx25 : s.readReg64 (.gpr 25#5) = fsp + 5632#64 := hx25
  clear_value fsp
  stage4_pre_fetches img.base (cliExternsWith ext)
  stage4_bind_entry img.base (cliExternsWith ext)
  examples_hide_fetches
  have hfn_entry : s4EntryExt img ext = fnStart := fnStart_def
  have hpc0 : s.pc = fnStart + bv% (4496) := by rw [hctrl.pc, s4PcExt, hfn_entry]
  have hrun0 : s.status = .Running := hctrl.run
  apply sepWPp_step_to_frozen hctrl.inv (mid := fnStart + bv% (4576))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF' hsym'
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs)
  refine ⟨by simp only [arm64_norm]; exact htr,
    ⟨by rw [s4PcExt, hfn_entry]; try wp_norm_goal, by wp_norm_lhs,
     by simp only [arm64_norm]; exact hfsp_def.val ▸ hsp0,
     by simp only [arm64_norm]; exact hctrl.fp,
     by simp only [arm64_norm]; exact hctrl.x19,
     by simp only [arm64_norm]; exact hctrl.files0, ⟨hF', hsym'⟩,
     by simp only [calleeSavedVRegs, arm64_norm]; exact hctrl.vregs, hctrl.spAligned⟩,
    by simp only [arm64_norm]; exact hx20, by simp only [arm64_norm]; exact hx21,
    by simp only [arm64_norm]; exact hx22, by simp only [arm64_norm]; exact hx25,
    Entails.of_eq (by s4_ac_rfl)⟩

theorem stage4_branch_4496_ok
    {img : Obj.Image} {W : CliHooks} {B : RunBudgets} {stk : Nat}
    {s0 s : State} {rk1 : RootKey} {ck1 : ChainKey} {Frame : SepProp}
    {Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk) (hspk : stk ≤ s0.sp.toNat)
    (hctrl : InInitiate img W s0 s 4496) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 2304#64)
    (hx25 : s.readReg64 (.gpr 25#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 5632#64) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProg img W) (initPc img W 4576) s
      (((fsp + 5632#64) ↦₃₂ 0#32) ∗ ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
        ((fsp + 5668#64) ↦ₛ chainKeyBytes ck1) ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ InInitiate img W s0 sf 4576 ∧
        sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧
        sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 ∧
        sf.readReg64 (.gpr 22#5) = fsp + 2304#64 ∧
        sf.readReg64 (.gpr 25#5) = fsp + 5632#64 ∧
        (Pf ⊢ ((fsp + 5632#64) ↦₃₂ 0#32) ∗ ((fsp + 5636#64) ↦ₛ keyToBytes32 rk1) ∗
          ((fsp + 5668#64) ↦ₛ chainKeyBytes ck1) ∗ Frame))
      Qp (initOom s0) := by
  intro fsp
  apply sepWPp_steps_post
    (stage4_branch_4496_ok_ext (ext := cliHookExterns W) (rk1 := rk1) (ck1 := ck1) (Frame := Frame)
      hstk hspk ⟨hctrl.pc, hctrl.run, hctrl.sp, hctrl.fp, hctrl.x19, hctrl.files0, hctrl.inv,
        hctrl.vregs, hctrl.spAligned⟩ htr hx20 hx21 hx22 hx25)
  rintro sf Pf _ ⟨htrf, hc, hx20f, hx21f, hx22f, hx25f, hentf⟩
  exact ⟨htrf, ⟨hc.pc, hc.run, hc.sp, hc.fp, hc.x19, hc.files0, hc.inv, hc.vregs, hc.spAligned⟩,
    hx20f, hx21f, hx22f, hx25f, hentf⟩

theorem stage4_branch_4496_err_ext
    {img : Obj.Image} {ext : String → Option (State → State)} {B : RunBudgets} {stk : Nat}
    {s0 s : State} {Frame : SepProp} {Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk) (hspk : stk ≤ s0.sp.toNat)
    (hctrl : S4InInitiate img ext s0 s 4496) (htr : s.trace = s0.trace) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (s4ProgExt img ext) (s4PcExt img ext 4508) s
      (((fsp + 5632#64) ↦₃₂ 1#32) ∗ memRegion (fsp + 5636#64) 4 ∗
        ((fsp + 5640#64) ↦₆₄ speWord 10) ∗ memRegion (fsp + 5648#64) 56 ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ S4InInitiate img ext s0 sf 4508 ∧
        (Pf ⊢ ((fsp + 5632#64) ↦₃₂ 1#32) ∗ memRegion (fsp + 5636#64) 4 ∗
          ((fsp + 5640#64) ↦₆₄ speWord 10) ∗ memRegion (fsp + 5648#64) 40 ∗
          memRegion (fsp + 5688#64) 16 ∗ Frame))
      Qp (initOom s0) := by
  intro fsp
  have hfsp_def : Hide (fsp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) := ⟨rfl⟩
  have hsp0 : s.sp = fsp := hctrl.sp
  have halign0 : s.spAligned = true := fsp_aligned_of_s0 hstk hspk hsp0 hctrl.spAligned
  clear_value fsp
  stage4_pre_fetches img.base (cliExternsWith ext)
  stage4_bind_entry img.base (cliExternsWith ext)
  examples_hide_fetches
  have hfn_entry : s4EntryExt img ext = fnStart := fnStart_def
  have hpc0 : s.pc = fnStart + bv% (4496) := by rw [hctrl.pc, s4PcExt, hfn_entry]
  have hrun0 : s.status = .Running := hctrl.run
  apply sepWPp_step_to_frozen hctrl.inv (mid := fnStart + bv% (4508))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF' hsym'
  apply SepWPp.of_sepWP_ret
  apply SepWP.done (by rw [s4PcExt, hfn_entry]; try wp_norm_goal) (by wp_norm_lhs)
  have hm56 : memRegion (fsp + 5648#64) 56 =
      memRegion (fsp + 5648#64) 40 ∗ memRegion (fsp + 5688#64) 16 :=
    ProofLib.memRegion_split' (b := fsp + 5648#64) (n := 40) (k := 16)
      (b' := fsp + 5688#64) rfl (by bv_omega) (by decide)
  refine ⟨by simp only [arm64_norm]; exact htr,
    ⟨by rw [s4PcExt, hfn_entry]; try wp_norm_goal, by wp_norm_lhs,
     by simp only [arm64_norm]; exact hfsp_def.val ▸ hsp0,
     by simp only [arm64_norm]; exact hctrl.fp,
     by simp only [arm64_norm]; exact hctrl.x19,
     by simp only [arm64_norm]; exact hctrl.files0, ⟨hF', hsym'⟩,
     by simp only [calleeSavedVRegs, arm64_norm]; exact hctrl.vregs, hctrl.spAligned⟩, ?_⟩
  rw [hm56]
  exact Entails.of_eq (by s4_ac_rfl)

theorem stage4_branch_4496_err
    {img : Obj.Image} {W : CliHooks} {B : RunBudgets} {stk : Nat}
    {s0 s : State} {Frame : SepProp} {Qp : State → SepProp → Prop}
    (hstk : cliInitiateNeed B ≤ stk) (hspk : stk ≤ s0.sp.toNat)
    (hctrl : InInitiate img W s0 s 4496) (htr : s.trace = s0.trace) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProg img W) (initPc img W 4508) s
      (((fsp + 5632#64) ↦₃₂ 1#32) ∗ memRegion (fsp + 5636#64) 4 ∗
        ((fsp + 5640#64) ↦₆₄ speWord 10) ∗ memRegion (fsp + 5648#64) 56 ∗ Frame)
      (fun sf Pf =>
        sf.trace = s0.trace ∧ InInitiate img W s0 sf 4508 ∧
        (Pf ⊢ ((fsp + 5632#64) ↦₃₂ 1#32) ∗ memRegion (fsp + 5636#64) 4 ∗
          ((fsp + 5640#64) ↦₆₄ speWord 10) ∗ memRegion (fsp + 5648#64) 40 ∗
          memRegion (fsp + 5688#64) 16 ∗ Frame))
      Qp (initOom s0) := by
  intro fsp
  apply sepWPp_steps_post
    (stage4_branch_4496_err_ext (ext := cliHookExterns W) (Frame := Frame)
      hstk hspk ⟨hctrl.pc, hctrl.run, hctrl.sp, hctrl.fp, hctrl.x19, hctrl.files0, hctrl.inv,
        hctrl.vregs, hctrl.spAligned⟩ htr)
  rintro sf Pf _ ⟨htrf, hc, hentf⟩
  exact ⟨htrf, ⟨hc.pc, hc.run, hc.sp, hc.fp, hc.x19, hc.files0, hc.inv, hc.vregs, hc.spAligned⟩, hentf⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
