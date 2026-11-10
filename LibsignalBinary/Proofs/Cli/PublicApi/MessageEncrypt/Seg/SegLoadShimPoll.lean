/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDecodes
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadShimPoll
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.SymWP

/-!
# `segLoad` Prologue, Load Shim, and Poll (`+0x000..+0x160`)

Proves `segLoad_to_dispatch` for the CLI encryption entry, stepping through prologue and spill
setup `E0` (`+0x000..+0x08c`), `kit.loadShim`, pre-poll setup (`+0x090..+0x0a8`), `kit.loadPoll`,
and ready-path future cleanup `E1` (`+0x0ac..+0x160`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove

open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_poll_wp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp box self remA waker0 waker1 v830 v838 v840 : BitVec 64}
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))} {F : SepProp}
    (hsub : encSubStackV kit ikit ≤ 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xac#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x580#64) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64) s
      (loadPollOutAtS Scope A img.base (sp + 0x580#64) ans ∗
        memRegion (sp + 0x46a#64) 6 ∗
        ((sp + 0x470#64) ↦₆₄ box) ∗ ((sp + 0x478#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
        ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
        ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8 ∗
        memRegion (sp + 0x6f8#64) 312 ∗
        ((sp + 0x830#64) ↦₆₄ v830) ∗ ((sp + 0x838#64) ↦₆₄ v838) ∗ ((sp + 0x840#64) ↦₆₄ v840) ∗
        A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box self remA 1#8 ∗
        A.pool ∗
        memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
        stackAt sp kit.loadPollStack ∗
        loadVtablesAt kit ∗ F)
      (fun sf P_f =>
        ∃ w0 w1 w2 w3 w4 w5 w6 : BitVec 64, ∃ tail : List (BitVec 8),
          w0 ≠ 0xFFFFFFFFFFFFFFFD#64 ∧ tail.length = 312 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧
          sf.trace = s.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          sf.readReg64 .x24 = w0 ∧ sf.readReg64 .x27 = w1 ∧
          sf.readReg64 .x21 = w2 ∧ sf.readReg64 .x23 = w3 ∧
          sf.readReg64 .x25 = sp + 0x580#64 ∧
          sf.readReg64 .x26 = sp + 0x9d0#64 ∧
          sf.readReg64 .x28 = sp + 0x4a0#64 ∧
          sf.pstate = addsPState64 w0 2#64 ∧
          P_f = (memRegion (sp + 0x46a#64) 0x116 ∗
            memRegion (sp + 0x580#64) 368 ∗
            ((sp + 0x6f8#64) ↦ₛ tail) ∗
            ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
            ((sp + 0x840#64) ↦₆₄ w6) ∗
            LoadOutRes Scope A img.base ans w0 w1 w2 w3 w4 w5 w6 tail ∗
            A.pool ∗ stackAt sp (encSubStackV kit ikit) ∗ loadVtablesAt kit ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  have hmemcpy := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.memcpy_ok_at_enc env
  have hdrop := env.kitOk.loadFutDrop
  have hdealloc := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dealloc_ok_at_enc env
  have hb := ProofLib.ObjectLoad.base_aligned_of_loads env.loads
  have hdz := kit.loadFutDrop_ne_zero hb
  have hdz' : (img.base + kit.loadFutDropOff == 0#64) = false := beq_false_of_ne hdz
  have hsz' : (BitVec.ofNat 64 kit.loadBoxSize == 0#64) = false :=
    beq_false_of_ne kit.loadBoxSize_ne_zero
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0xac 0xb8
  dsimp only [tripleRatchetProgAt] at hpc hmemcpy hdrop hdealloc ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx20
  have hbox_toNat : (BitVec.ofNat 64 kit.loadBoxSize).toNat = kit.loadBoxSize :=
    Nat.mod_eq_of_lt kit.loadBoxSize_lt
  apply SepWP.fold (loadPollOutAtS_decompose_sp Scope A img.base s.sp ans) (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4
  apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro tail
  apply SepWP.pure_elim; rintro ⟨hw0_ne, htail_len⟩
  have hw0_b : (w0 + 3#64 == 0#64) = false := ne_neg3_add3_ne_zero hw0_ne
  wp_conv_pre => unfold loadVtablesAt
  wp_simp_pre [sepConj_assoc]
  wp_steps
  wp_call hmemcpy (s.sp + 0x6f8#64, s.sp + 0x5b8#64, tail)
  apply SepWP.fold (out368_fold s.sp w0 w1 w2 w3 w4 w5 w6 tail htail_len) (by sep_focus)
  wp_steps
  apply SepWP.fold (fold_46a_498 s.sp box (img.base + kit.loadFutVtOff) waker0 waker1 0#64) (by sep_focus)
  wp_call hdrop ()
  rw [hsp_sf] at h_12
  wp_steps
  apply SepWP.fold (kit.loadBoxAt_memRegion box self remA 1#8) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (stack_encSub_poll_to_dealloc_eq kit ikit hsub h_12)) (by sep_focus)
  wp_call hdealloc (box, kit.loadBoxSize, 8)
  apply SepWP.fold (Entails.of_eq (stack_encSub_dealloc_back_eq kit ikit hsub h_12)) (by sep_focus)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨w0, w1, w2, w3, w4, w5, w6, tail, hw0_ne, htail_len, ?_⟩
  simp only [wp_norm, arm64_norm]
  refine ⟨by rw [hsp_sf_1, h_12],
          by rw [hsp_sf_1, h_12]; exact hal_norm,
          by rw [hpost_1, h_11, hpost],
          by rw [h_23, h_13, h],
          by rw [hcs_sf_1, hpost_sf, hcs_sf],
          by rw [hvregs_2, hvregs_1, hvregs],
          by rw [h_28, h_18, h_5],
          by rw [h_31, h_21, h_8],
          by rw [h_25, h_15, h_2],
          by rw [h_27, h_17, h_4],
          by rw [h_29, h_19, h_6],
          by rw [h_32, h_22, h_9],
          ?_⟩
  unfold loadVtablesAt
  ac_rfl

/-! ## 1. Pre-Poll (`+0x090..+0x0a8`) -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_pre_poll_wp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (_env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State}
    {sp box v470 v478 : BitVec 64} {F : SepProp}
    (hsub : encSubStackV kit ikit ≤ 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x90#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = box)
    (hx1 : s.readReg64 .x1 = img.base + kit.loadFutVtOff)
    (_hbox_ne : box ≠ 0#64) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      (img.base + kit.loadPollOff) s
      (((sp + 0x470#64) ↦₆₄ v470) ∗ ((sp + 0x478#64) ↦₆₄ v478) ∗
        stackAt s.sp kit.loadShimStack ∗
        memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
        loadVtablesAt kit ∗ F)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.fs = s.fs ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧
        sf.readReg64 .x8 = sp + 0x580#64 ∧
        sf.readReg64 .x20 = sp + 0x580#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xac#64 ∧
        P_f = (((sp + 0x470#64) ↦₆₄ box) ∗ ((sp + 0x478#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
          memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
          stackAt sp kit.loadPollStack ∗
          loadVtablesAt kit ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x90 0x1c
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize h_entry : (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx0 hx1
  apply SepWP.fold (Entails.of_eq (stack_encSub_shim_to_poll_eq kit ikit hsub rfl)) (by sep_focus)
  wp_conv_pre => unfold loadVtablesAt
  wp_simp_pre [sepConj_assoc]
  wp_steps
  have hvt :
      ((kit.ss_vt + 24#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
      ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
      ((img.base + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((img.base + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
      ((img.base + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ⊢
        loadVtablesAt kit :=
    Entails.refl _
  apply SepWP.fold hvt (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm, hx0, hal_norm, true_and]
  ac_rfl

/-! ## 2. Prologue + Spill Table `E0` (`+0x000..+0x08c`) -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_shim_wp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (_env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (s0 : State) {sp : BitVec 64} (F : SepProp)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hsp0 : sp = s0.sp - 0xbe0#64)
    (hpc : s0.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName)
    (hrun : s0.status = .Running)
    (hal : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ptA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length)
    (hx2 : s0.readReg64 .x2 = x.remA)
    (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.ssA)
    (hx5 : s0.readReg64 .x5 = kit.ss_vt)
    (hx6 : s0.readReg64 .x6 = x.idA)
    (hx7 : s0.readReg64 .x7 = ikit.id_vt)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      (img.base + kit.loadShimOff) s0
      (nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ loadVtablesAt kit ∗ F)
      (fun sm P_m =>
        ∃ v50 v470 v478 waker0 waker1 v830 v838 v840 : BitVec 64,
          sm.sp = sp ∧ sm.spAligned = true ∧
          sm.fs = s0.fs ∧
          sm.trace = s0.trace ∧
          sm.readReg64 .x0 = x.ssA ∧
          sm.readReg64 .x1 = x.remA ∧
          sm.readReg64 .x19 = x.ret ∧
          sm.readReg64 .x29 = s0.sp - 0x60#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x30 = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x90#64 ∧
          P_m = (nowAt s0.sp x.now ∗
            encSavedRegs s0.sp s0 ∗
            stackAt sm.sp kit.loadShimStack ∗
            memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
            memRegion sp 0x50 ∗
            ((sp + 0x50#64) ↦₆₄ v50) ∗
            encSpillsInit kit.ss_vt ikit.id_vt sp x ∗
            ((sp + 0x108#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 0x110#64) 0x358 ∗
            ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
            memRegion (sp + 0x46a#64) 6 ∗
            ((sp + 0x470#64) ↦₆₄ v470) ∗ ((sp + 0x478#64) ↦₆₄ v478) ∗
            ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
            ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8 ∗
            memRegion (sp + 0x580#64) 368 ∗
            memRegion (sp + 0x6f0#64) 8 ∗
            memRegion (sp + 0x6f8#64) 312 ∗
            ((sp + 0x830#64) ↦₆₄ v830) ∗ ((sp + 0x838#64) ↦₆₄ v838) ∗
            ((sp + 0x840#64) ↦₆₄ v840) ∗
            memRegion (sp + 0x848#64) 0x338 ∗
            loadVtablesAt kit ∗ F)) := by
  subst hsp0
  have hsub := encSubStackV_le_two_pow_64 kit ikit hsp_le
  have hal_norm : (s0.sp &&& 15#64 == 0#64) = true := hal
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x0 0x90
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize h_entry : (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8
  wp_conv_pre =>
    unfold nowAt loadVtablesAt
    rw [stackAt_withStoresEncStack_split kit ikit s0.sp hsp_le]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    bv_sub_add_lit, sepConj_assoc]
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.fold (encSavedRegs_fold s0.sp s0) (by sep_focus)
  wp_conv_pre =>
    rw [memRegion_0xb80_split (s0.sp - 3040#64),
        exists_pointsTo128_eq_two_pointsTo64 (s0.sp - 3040#64 + 0x830#64)]
    simp (config := { maxSteps := 400000 }) only [cells_succ, cells_zero, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      bv_sub_add_lit, sepConj_assoc]
  repeat (apply SepWP.exists_elim; intro v_tmp)
  wp_steps
  wp_clear_temps
  rename_i v1 v2 v3 v4 v5 v6
  apply SepWP.fold (nowAt_fold s0.sp x.now) (by sep_focus)
  apply SepWP.fold (fold_sp50_sub s0.sp) (by sep_focus)
  apply SepWP.fold (encSpillsInit_sub_fold kit.ss_vt ikit.id_vt s0.sp x) (by sep_focus)
  apply SepWP.fold (pointsTo16_zero_sub s0.sp) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (stack_encSub_shim kit ikit (s0.sp - 3040#64) hsub)) (by sep_focus)
  have hvt :
      ((kit.ss_vt + 24#64) ↦₆₄ᵣ (img.base + kit.loadShimOff)) ∗
      ((img.base + kit.loadFutVtOff) ↦₆₄ᵣ (img.base + kit.loadFutDropOff)) ∗
      ((img.base + (kit.loadFutVtOff + 8#64)) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((img.base + (kit.loadFutVtOff + 16#64)) ↦₆₄ᵣ 8#64) ∗
      ((img.base + (kit.loadFutVtOff + 24#64)) ↦₆₄ᵣ (img.base + kit.loadPollOff)) ⊢
        loadVtablesAt kit := by
    unfold loadVtablesAt
    simp only [BitVec.add_assoc]
    exact Entails.refl _
  apply SepWP.fold hvt (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨v_tmp, v5, v6,
    (entry + 40#64 &&& 18446744073709547520#64) + bv% (ls_reloc% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]")) - (page% (ls_off% "libsignal_cli_ratchet::encrypt" + 40))),
    (entry + 40#64 &&& 18446744073709547520#64) + bv% (ls_reloc% (ls_reloc% (ls_off% "<<core::task::wake::RawWaker>::NOOP::VTABLE::{closure#0} as core::ops::function::FnOnce<(*const (),)>>::call_once [local#2]")) - (page% (ls_off% "libsignal_cli_ratchet::encrypt" + 40))),
    v4, v3, v2, ?_⟩
  simp only [wp_norm, arm64_norm, bv_sub_add_lit, hal_norm, true_and]
  ac_rfl

/-! ## 3. Combined `E0` + `loadShim` + `loadPoll` + `E1` to `+0x160` (`segLoad_to_dispatch`) -/

set_option linter.unusedVariables false in
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  nowAt s0.sp x.now ∗
  encSavedRegs s0.sp s0 ∗
  memRegion sp 0x50 ∗
  ((sp + 0x50#64) ↦₆₄ v50) ∗
  encSpillsInit kit.ss_vt ikit.id_vt sp x ∗
  ((sp + 0x108#64) ↦₆₄ x.remA) ∗
  memRegion (sp + 0x110#64) 0x358 ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
  memRegion (sp + 0x6f0#64) 8 ∗
  memRegion (sp + 0x848#64) 0x338 ∗
  (x.ptA ↦ₛ x.ptext) ∗
  protocolAddressAt A x.loc x.locA ∗
  memRegion x.ret 248 ∗
  CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
  logOff img ∗
  ikit.identityAt x.idA ist0

set_option linter.unusedVariables false in
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame {A : RustAlloc} {img : Obj.Image} (kit : SessionStoreSpec A img.base)
    (st0 : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  nowAt s0.sp x.now ∗
  encSavedRegs s0.sp s0 ∗
  memRegion sp 0x50 ∗
  ((sp + 0x50#64) ↦₆₄ v50) ∗
  encSpillsInit kit.ss_vt ikit.id_vt sp x ∗
  ((sp + 0x108#64) ↦₆₄ x.remA) ∗
  memRegion (sp + 0x110#64) 0x358 ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
  memRegion (sp + 0x6f0#64) 8 ∗
  memRegion (sp + 0x848#64) 0x338 ∗
  (x.ptA ↦ₛ x.ptext) ∗
  protocolAddressAt A x.loc x.locA ∗
  memRegion x.ret 248 ∗
  CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
  logOff img ∗
  encStoreExtra kit st0 ikit ist0 x s0

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.tapeAt_eq_pure_sep_tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt ctl cur rest = ⌜rest.length < 2 ^ 63⌝ ∗ CryptoVerification.SignalSession.Coins.coinsAfter ctl cur rest 0 := by
  simp [CryptoVerification.SignalSession.Coins.coinsAt, CryptoVerification.SignalSession.Coins.tapeAt2, CryptoVerification.SignalSession.Coins.coinsAfter, CryptoVerification.SignalSession.Coins.tapeAfter2]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_to_dispatch {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 : State)
    (hfs : EncFsCtx kit ikit C ctl abs s0 s0)
    (hpc0 : s0.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img) (hrun0 : s0.status = .Running) (hal0 : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ R)
    (hcont : ∀ (s : State) (sp : BitVec 64)
      (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
      (w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8)),
      sp = s0.sp - 0xbe0#64 →
      s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64 →
      encMidMeta img x s0 s →
      x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStackV kit ikit ≤ s0.sp.toNat →
      w0 ≠ 0xFFFFFFFFFFFFFFFD#64 → tail.length = 312 →
      kit.loadRel st0 x.rem.val ans →
      s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans →
      s.readReg64 .x24 = w0 → s.readReg64 .x27 = w1 →
      s.readReg64 .x21 = w2 → s.readReg64 .x23 = w3 →
      s.readReg64 .x25 = sp + 0x580#64 →
      s.readReg64 .x26 = sp + 0x9d0#64 →
      s.readReg64 .x28 = sp + 0x4a0#64 →
      s.pstate = addsPState64 w0 2#64 →
      (s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutRes Scope A img.base ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        protocolAddressAt A x.rem x.remA ∗
        A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
        (fun s' => ∃ r g sess,
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s')) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s0
      (fun s' => ∃ r g sess,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage] at hm0
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.tapeAt_eq_pure_sep_tapeAfter_zero] at hm0
  have hpull0 :
      (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
          s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
        (⌜x.rest.length < 2 ^ 63⌝ ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0) ∗
        logOff img ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ A.pool)) ∗ R =
      ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
        x.locA ≠ 0#64 ∧
        s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
        s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
        withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
        kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
      (⌜x.rest.length < 2 ^ 63⌝ ∗
      ((nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
        (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))) ∗ R))) := by ac_rfl
  rw [hpull0] at hm0
  obtain ⟨hF0, hm0⟩ := (satisfies_pure_sepConj _ _ _).mp hm0
  obtain ⟨⟨hx0, hx1_nat, hpt_lt, hx2, hx3, hloc_ne, hx4, hx5, hx6, hx7, hnsec, hx8, hsp_le, haddr_ss, _haddr_id⟩, hm0⟩ :=
    (satisfies_pure_sepConj _ _ _).mp hm0
  obtain ⟨hrest_lt, hm0⟩ := (satisfies_pure_sepConj _ _ _).mp hm0
  have hsub := encSubStackV_le_two_pow_64 kit ikit hsp_le
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm_vt := loadVtablesAt_intro env.vtables hF0.1 hm0
  have hpull_vt :
      loadVtablesAt kit ∗
        ((nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
          (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
            ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))) ∗ R) =
      (nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ loadVtablesAt kit ∗
        (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))) ∗ R := by ac_rfl
  rw [hpull_vt] at hm_vt
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_fnAddr env] at hpc0
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (tripleRatchetProgAt img.base C ctl abs) s0 :=
    (hfs.fsAt (evs := []) (List.append_nil _).symm (fun _ => NoFsEv.nil)).mono (fun _ h => h.1) id
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_sepWPp (target := (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64) hm_vt ?_
  have he0 := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_shim_wp env x s0
    (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
      ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))
    hsp_le rfl hpc0 hrun0 hal0 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8
  refine messageEncrypt_of_sepWP_frozen ⟨hF0.1, hF0.2⟩ (SepWP.mono he0 ?_)
  intro sm P_m hpcm hrunm hpostm hFm
  rcases hpostm with ⟨v50, v470, v478, waker0, waker1, v830, v838, v840,
    hspm, halm, hfsm, htrm, hx0m, hx1m, hx19m, hx29m, hvregsm, hx30m, rfl⟩
  refine messageEncrypt_call_panic_then_sepWPp_frozen
    (subroutine_ok_withStepsPost_inImage env.kitOk.loadShim)
    (x := ⟨x.ssA, x.remA⟩)
    (F := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
      ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
      ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
      ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
      ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
      ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
      protocolAddressAt A x.rem x.remA ∗
      kit.storeAt x.ssA st0 ∗
      loadVtablesAt kit)
    hFm hpcm hrunm halm hx30m ?_ ?_ (fun _ _ => rfl) ?_
  · intro R' hm'
    refine inImage_pre_intro hFm.1 hFm.2 ?_
    dsimp only [kitLoadShimSpec, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame] at hm' ⊢
    refine Satisfies.mono ?_ hm'
    have hpre_eq :
        (nowAt s0.sp x.now ∗
          encSavedRegs s0.sp s0 ∗
          stackAt sm.sp kit.loadShimStack ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
          ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
          ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          loadVtablesAt kit ∗
          (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
            ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗ logOff img ∗ ikit.identityAt x.idA ist0))) ∗ R' =
        (A.pool ∗ stackAt sm.sp kit.loadShimStack) ∗
        (((nowAt s0.sp x.now ∗
          encSavedRegs s0.sp s0 ∗
          memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.loc x.locA ∗
          memRegion x.ret 248 ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
          logOff img ∗
          ikit.identityAt x.idA ist0) ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
          ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
          ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
          protocolAddressAt A x.rem x.remA ∗
          kit.storeAt x.ssA st0 ∗
          loadVtablesAt kit) ∗ R') := by ac_rfl
    rw [hpre_eq]
    apply sepConj_mono_left
    exact Entails.pure_right (And.intro hx0m hx1m) (Entails.refl _)
  · intro sf
    dsimp only [kitLoadShimSpec]
    exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.alloc_onPanic_entails (by rw [htrm])
  · intro sf1 hpc1 hrun1 hsp1 hcs1 hF1
    rcases hcs1 with ⟨hcs19, _, _, _, _, _, _, _, _, _, hcs29, hcsv1⟩
    dsimp only [Spec.inImage, withStepsPost, kitLoadShimSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hsteps1 => ?_
    refine SepWPp.pure_elim fun ⟨hx1_1, hbox_ne, _hbox_align, htr1⟩ => ?_
    have henv1 : kit.envOk sf1.fs.files :=
      (hfsAt.of_call hsteps1 (congrArg FsState.files hfsm) htr1).envOk_here
    set box := sf1.readReg64 .x0
    have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
    have hal1 : sf1.spAligned = true := by rw [State.spAligned, hsp1, ← State.spAligned]; exact halm
    have hpre_poll := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_pre_poll_wp env
      (s := sf1) (sp := s0.sp - 0xbe0#64) (box := box)
      (v470 := v470) (v478 := v478)
      (F := A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
        A.pool ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
        ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
        ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
        protocolAddressAt A x.rem x.remA ∗
        kit.storeAt x.ssA st0)
      hsub hpc1 hrun1 hsp1' hal1 rfl hx1_1 hbox_ne
    have hpre_poll_eq :
        A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
          A.pool ∗ stackAt sm.sp kit.loadShimStack ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
          ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
          ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
          protocolAddressAt A x.rem x.remA ∗
          kit.storeAt x.ssA st0 ∗
          loadVtablesAt kit =
        ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          stackAt sf1.sp kit.loadShimStack ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          loadVtablesAt kit ∗
          (A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
            A.pool ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
            ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
            ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
            protocolAddressAt A x.rem x.remA ∗
            kit.storeAt x.ssA st0) := by
      rw [hsp1]
      ac_rfl
    rw [hpre_poll_eq]
    refine messageEncrypt_of_sepWP_frozen hF1 (SepWP.mono hpre_poll ?_)
    intro sm2 P_m2 hpcm2 hrunm2 hpostm2 hFm2
    rcases hpostm2 with ⟨hspm2, halm2, hfsm2, htrm2, hx0m2, hx8m2, hx20m2, hx19m2, hx29m2, hvregsm2, hx30m2, rfl⟩
    refine messageEncrypt_call_panic_then_wp_frozen env.kitOk.loadPoll
      (x := (⟨box, s0.sp - 0xbe0#64 + 0x580#64, x.remA, x.rem⟩, x.ssA, st0))
      (F := ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
        ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
        memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
        loadVtablesAt kit ∗
        A.live box kit.loadBoxSize 8 ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
        ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
        ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840))
      hFm2 hpcm2 hrunm2 halm2 hx30m2 ?_ ?_ (fun _ _ => rfl) ?_
    · intro R' hm'
      refine withEnvPre_pre_intro (hfsm2 ▸ henv1) ?_
      dsimp only [kitLoadPollSpecS] at hm' ⊢
      refine Satisfies.mono ?_ hm'
      rw [hspm2]
      have hperm_p :
          (((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
            ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
            stackAt (s0.sp - 0xbe0#64) kit.loadPollStack ∗
            loadVtablesAt kit ∗
            (A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
              A.pool ∗
              CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
              ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
              ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
              protocolAddressAt A x.rem x.remA ∗
              kit.storeAt x.ssA st0)) ∗ R' =
          (kit.loadBoxAt box x.ssA x.remA 0#8 ∗ kit.storeAt x.ssA st0 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            protocolAddressAt A x.rem x.remA ∗ A.pool ∗
            stackAt (s0.sp - 0xbe0#64) kit.loadPollStack) ∗
          ((((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
            ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
            loadVtablesAt kit ∗
            A.live box kit.loadBoxSize 8 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
            ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
            ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840)) ∗ R') := by ac_rfl
      rw [hperm_p]
      apply sepConj_mono_left
      exact Entails.pure_right ⟨hFm2.1, hFm2.2, hx0m2, hx8m2, haddr_ss⟩ (Entails.refl _)
    · intro sf
      dsimp only [withEnvPre, kitLoadPollSpecSE, kitLoadPollSpecS]
      exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.alloc_onPanic_entails (by rw [htrm2, htr1, htrm])
    · intro sf2 hpc2 hrun2 hsp2 hcs2
      rcases hcs2 with ⟨hcs2_19, hcs2_20, _, _, _, _, _, _, _, _, hcs2_29, hcs2_v⟩
      dsimp only [withEnvPre, kitLoadPollSpecSE, kitLoadPollSpecS]
      wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_elim; intro ans
      apply SepWP.pure_elim; rintro ⟨hl, htr2⟩
      have hsp2' : sf2.sp = s0.sp - 0xbe0#64 := by rw [hsp2, hspm2]
      have hal2 : sf2.spAligned = true := by rw [State.spAligned, hsp2, ← State.spAligned]; exact halm2
      have hx20_2 : sf2.readReg64 .x20 = s0.sp - 0xbe0#64 + 0x580#64 := by rw [hcs2_20, hx20m2]
      have he1 := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_poll_wp env
        (s := sf2) (sp := s0.sp - 0xbe0#64) (box := box) (self := x.ssA) (remA := x.remA)
        (waker0 := waker0) (waker1 := waker1) (v830 := v830) (v838 := v838) (v840 := v840)
        (ans := ans)
        (F := protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame kit ikit ist0 ctl x s0 v50)
        hsub hpc2 hrun2 hsp2' hal2 hx20_2
      refine sepWP_conseq_pc_run (by rw [hspm2]; ac_rfl) he1 ?_
      intro sf P_f hpcf hrunf hpostf hFf hm_f
      rcases hpostf with ⟨w0, w1, w2, w3, w4, w5, w6, tail,
        hw0_ne, htail, hspf, half, htrf, hx19f, hx29f, hvregsf,
        hx24f, hx27f, hx21f, hx23f, hx25f, hx26f, hx28f, hpsf, rfl⟩
      have hm_f' : sf.mem ⊨ (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          LoadOutRes Scope A img.base ans w0 w1 w2 w3 w4 w5 w6 tail ∗
          protocolAddressAt A x.rem x.remA ∗
          A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗ loadVtablesAt kit ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R := by
        refine Satisfies.mono ?_ hm_f
        refine sepConj_mono_left ?_
        have hsp_split := encSubStack_split_extra kit st0 ikit ist0 x s0 hsp_le
        dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.shimFrame, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame]
        have hperm :
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              LoadOutRes Scope A img.base ans w0 w1 w2 w3 w4 w5 w6 tail ∗
              A.pool ∗ stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) ∗ loadVtablesAt kit ∗
              (protocolAddressAt A x.rem x.remA ∗
                kit.storeAt x.ssA st0 ∗
                (nowAt s0.sp x.now ∗
                  encSavedRegs s0.sp s0 ∗
                  memRegion (s0.sp - 0xbe0#64) 0x50 ∗
                  ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
                  encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
                  ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
                  ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
                  (x.ptA ↦ₛ x.ptext) ∗
                  protocolAddressAt A x.loc x.locA ∗
                  memRegion x.ret 248 ∗
                  CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
                  logOff img ∗
                  ikit.identityAt x.idA ist0)) =
            (kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
              stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit)) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              LoadOutRes Scope A img.base ans w0 w1 w2 w3 w4 w5 w6 tail ∗
              protocolAddressAt A x.rem x.remA ∗
              A.pool ∗ loadVtablesAt kit ∗
              nowAt s0.sp x.now ∗
              encSavedRegs s0.sp s0 ∗
              memRegion (s0.sp - 0xbe0#64) 0x50 ∗
              ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
              encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
              ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
              ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
              (x.ptA ↦ₛ x.ptext) ∗
              protocolAddressAt A x.loc x.locA ∗
              memRegion x.ret 248 ∗
              CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
              logOff img) := by ac_rfl
        rw [hperm]
        refine Entails.trans (sepConj_mono_left hsp_split) ?_
        exact Entails.of_eq (by ac_rfl)
      refine hcont sf (s0.sp - 0xbe0#64) ans w0 w1 w2 w3 w4 w5 w6 v50 tail rfl
        hpcf ⟨hrunf, hspf, hal0, half, ?_, ?_, hFf.1, hFf.2, ?_⟩
        ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
        hw0_ne htail hl ?_ hx24f hx27f hx21f hx23f hx25f hx26f hx28f hpsf hm_f'
      · rw [hx29f, hcs2_29, hx29m2, hcs29, hx29m]
      · rw [hx19f, hcs2_19, hx19m2, hcs19, hx19m]
      · rw [hvregsf, hcs2_v, hvregsm2, hcsv1, hvregsm]
      · rw [htrf, htr2, htrm2, htr1, htrm]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
