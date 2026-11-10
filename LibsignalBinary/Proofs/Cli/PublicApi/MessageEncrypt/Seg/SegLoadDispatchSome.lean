/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPoll
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDecodes
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDispatch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSome
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# CLI `SegLoad` Dispatch: `.ok (some r)` Branch & `segLoad_ok`

Proves `segLoad_dispatch_some` (`r.currentSession = some sess` → `Cur` at `+0x20c`;
`r.currentSession = none` → `+0x564`) and assembles `segLoad_ok` on the CLI image.
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

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Arithmetic & Frame Helpers for `ans = .ok (some r)` -/

set_option linter.unusedVariables false in
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (s0 : State) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  nowAt s0.sp x.now ∗
  encSavedRegs s0.sp s0 ∗
  memRegion sp 0x50 ∗
  encSpillsInit kit.ss_vt ikit.id_vt sp x ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
  memRegion (sp + 0x6f0#64) 8 ∗
  (x.ptA ↦ₛ x.ptext) ∗
  protocolAddressAt A x.loc x.locA ∗
  memRegion x.ret 248 ∗
  CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
  logOff img ∗
  encStoreExtra kit st0 ikit ist0 x s0

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame_eq_rec_sep {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50 =
      ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
      ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0 := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec]
  ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_some_cur_wp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp remA v50 w0 w1 w2 w3 w4 w5 w6 : BitVec 64}
    {tail : List (BitVec 8)} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hw0_ne1 : w0 ≠ 0xFFFFFFFFFFFFFFFF#64)
    (hw0_ne2 : w0 ≠ 0xFFFFFFFFFFFFFFFE#64)
    (hw3_ne : w3 ≠ 0xFFFFFFFFFFFFFFFF#64)
    (htail_len : tail.length = 312)
    (hx24 : s.readReg64 .x24 = w0)
    (hx27 : s.readReg64 .x27 = w1)
    (hx21 : s.readReg64 .x21 = w2)
    (hx23 : s.readReg64 .x23 = w3)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x20c#64) s
      (((sp + 0x50#64) ↦₆₄ v50) ∗
        ((sp + 0x108#64) ↦₆₄ remA) ∗
        memRegion (sp + 0x110#64) 0x358 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗ F)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x20 = sp + 0x58#64 ∧
        sf.readReg64 .x21 = sp + 0x128#64 ∧
        sf.readReg64 .x25 = sp + 0x580#64 ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x28 = sp + 0x4a0#64 ∧
        P_f = (recordWords56At (sp + 0x110#64) w0 w1 w2 w3 w4 w5 w6 ∗
          ((sp + 0x148#64) ↦ₛ tail) ∗
          memRegion (sp + 0x280#64) 0x1e8 ∗
          ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
          ((sp + 0x108#64) ↦₆₄ remA) ∗
          ((sp + 0x6f8#64) ↦ₛ tail) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
          ((sp + 0x840#64) ↦₆₄ w6) ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hw0_b2 : (w0 + 2#64 == 0#64) = false := ne_neg2_add2_ne_zero hw0_ne2
  have hw0_b1 : (w0 + 1#64 == 0#64) = false := ne_neg1_add1_ne_zero hw0_ne1
  have hw3_b1 : (w3 + 1#64 != 0#64) = true := ne_neg1_add1_bne_zero hw3_ne
  have hmemcpy := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.memcpy_ok_at_enc env
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x160 0x68
  dsimp only [tripleRatchetProgAt] at hpc hmemcpy ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx24 hx27 hx21 hx23 hx25 hx26 hx28
  wp_conv_pre => rw [memRegion_0x110_split_record s.sp]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  repeat (apply SepWP.exists_elim; intro _)
  wp_steps
  wp_call hmemcpy (s.sp + 0x148#64, s.sp + 0x6f8#64, tail)
  wp_steps
  apply SepWP.fold (recordWords56At_fold_sp110 s.sp w0 w1 w2 w3 w4 w5 w6) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm, hsp_sf, hpost, h, h_1, h_6, h_7, h_9,
    hcs_sf, hvregs, hx25, hx26, hx28, hal_norm, true_and]
  ac_rfl

/-! ## 2. `SepWP`s for `r.currentSession = none` (`+0x160..+0x208`, `+0x660..+0x67c` → `+0x564`) -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_some_nocur_pre_wp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp remA v50 w0 w1 w2 w4 w5 w6 : BitVec 64}
    {tail : List (BitVec 8)} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hw0_ne1 : w0 ≠ 0xFFFFFFFFFFFFFFFF#64)
    (hw0_ne2 : w0 ≠ 0xFFFFFFFFFFFFFFFE#64)
    (htail_len : tail.length = 312)
    (hx24 : s.readReg64 .x24 = w0)
    (hx27 : s.readReg64 .x27 = w1)
    (hx21 : s.readReg64 .x21 = w2)
    (hx23 : s.readReg64 .x23 = 0xFFFFFFFFFFFFFFFF#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) s
      (((sp + 0x50#64) ↦₆₄ v50) ∗
        ((sp + 0x108#64) ↦₆₄ remA) ∗
        memRegion (sp + 0x110#64) 0x358 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗ F)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = remA ∧
        sf.readReg64 .x8 = sp + 0x580#64 ∧
        sf.readReg64 .x22 = remA ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x1d4#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x28 = sp + 0x4a0#64 ∧
        P_f = (((sp + 0x110#64) ↦₆₄ w0) ∗ ((sp + 0x118#64) ↦₆₄ w1) ∗
          ((sp + 0x120#64) ↦₆₄ w2) ∗ ((sp + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
          ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
          ((sp + 0x140#64) ↦₆₄ w6) ∗
          ((sp + 0x148#64) ↦ₛ tail) ∗
          memRegion (sp + 0x280#64) 0x1e8 ∗
          ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
          ((sp + 0x108#64) ↦₆₄ remA) ∗
          ((sp + 0x6f8#64) ↦ₛ tail) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
          ((sp + 0x840#64) ↦₆₄ w6) ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hw0_b2 : (w0 + 2#64 == 0#64) = false := ne_neg2_add2_ne_zero hw0_ne2
  have hw0_b1 : (w0 + 1#64 == 0#64) = false := ne_neg1_add1_ne_zero hw0_ne1
  have hmemcpy := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.memcpy_ok_at_enc env
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x160 0x74
  dsimp only [tripleRatchetProgAt] at hpc hmemcpy ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx24 hx27 hx21 hx23 hx25 hx26 hx28
  wp_conv_pre => rw [memRegion_0x110_split_record s.sp]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  repeat (apply SepWP.exists_elim; intro _)
  wp_steps
  wp_call hmemcpy (s.sp + 0x148#64, s.sp + 0x6f8#64, tail)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm, hsp_sf, hpost, h, h_3, h_7, h_9,
    hcs_sf, hvregs, hx26, hx28, hal_norm, true_and]
  ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_some_nocur_post_wp {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp remA cap ptr len w0 w1 w2 w4 w5 w6 : BitVec 64}
    {dev : BitVec 8} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x1d4#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hcap_ne2 : cap ≠ 0xFFFFFFFFFFFFFFFE#64)
    (hx22 : s.readReg64 .x22 = remA)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64) s
      (((remA + 0x18#64) ↦₈ dev) ∗
        ((sp + 0x110#64) ↦₆₄ w0) ∗ ((sp + 0x118#64) ↦₆₄ w1) ∗
        ((sp + 0x120#64) ↦₆₄ w2) ∗ ((sp + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
        ((sp + 0x140#64) ↦₆₄ w6) ∗
        ((sp + 0x580#64) ↦₆₄ cap) ∗ ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ len) ∗
        memRegion (sp + 0x598#64) 344 ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        ∃ w3 : BitVec 64, DevWord dev w3 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x29 = sp + 0xb80#64 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          sf.readReg64 .x26 = sp + 0x9d0#64 ∧
          sf.readReg64 .x28 = sp + 0x4a0#64 ∧
          sf.readReg64 .x27 = cap ∧
          sf.readReg64 .x21 = ptr ∧
          sf.readReg64 .x23 = len ∧
          P_f = (((remA + 0x18#64) ↦₈ dev) ∗
            recordWords56At (sp + 0x110#64) w0 w1 w2 0xFFFFFFFFFFFFFFFF#64 w4 w5 w6 ∗
            memRegion (sp + 0x580#64) 368 ∗
            memRegion (sp + 0x848#64) 0x188 ∗
            ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)))) ∗
            ((sp + 0x9e0#64) ↦₆₄ 15#64) ∗
            memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hcap_b2 : (cap + 2#64 == 0#64) = false := ne_neg2_add2_ne_zero hcap_ne2
  have hadrp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.enc_adrp_0x4d6a0 (H := Rust.withPanics (tripleRatchetExterns C ctl abs))
    env.loads 0x1d8#64 (Or.inl rfl)
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x1d4 0x38
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x660 0x20
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx22 hx26 hx28 hx29 hadrp
  wp_conv_pre =>
    rw [memRegion_0x598_split s.sp, memRegion_0x848_split_0x9d0_0xb00 s.sp]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  repeat (apply SepWP.exists_elim; intro _)
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.fold (devWord_of_pointsTo8_memRegion7_1432 s.sp dev) (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro w3
  apply SepWP.pure_elim; intro hdev
  wp_steps
  apply SepWP.fold (recordWords56At_fold_sp110 s.sp w0 w1 w2 0xFFFFFFFFFFFFFFFF#64 w4 w5 w6) (by sep_focus)
  apply SepWP.fold (memRegion_0x580_368_fold s.sp cap ptr len w3 _) (by sep_focus)
  apply SepWP.fold (memRegion_0x9e8_0x198_fold s.sp w3 _ 15#64) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨w3, hdev, ?_⟩
  simp only [wp_norm, arm64_norm, hx26, hx28, hx29, hal_norm, true_and]
  ac_rfl

/-! ## 3. `segLoad_dispatch_some` and `segLoad_ok` -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_some {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (r : SessionRecord (List (BitVec 8)))
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64)
    (hmeta : encMidMeta img x s0 s)
    (hbnds : x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
      x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.ok (some r)))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hx24 : s.readReg64 .x24 = w0) (hx27 : s.readReg64 .x27 = w1)
    (hx21 : s.readReg64 .x21 = w2) (hx23 : s.readReg64 .x23 = w3)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutRes Scope A img.base (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A x.rem x.remA ∗
      A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun s' => ∃ r g sess,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hF, hsym, hvregs⟩
  rcases hbnds with ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
  have hm_drop : s.mem ⊨
      LoadOutRes Scope A img.base (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        protocolAddressAt A x.rem x.remA ∗
        A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    refine Satisfies.mono ?_ hm
    exact Entails.of_eq (by ac_rfl)
  clear hm
  rw [loadOutRes_some_eq] at hm_drop
  obtain ⟨g, hm_drop1⟩ := satisfies_sepExists_left hm_drop
  clear hm_drop
  rw [sepConj_assoc] at hm_drop1
  obtain ⟨⟨hscope, hcap_lt, hw0_eq, hw1_eq, hw2_eq, hw3_eq_init, htail_inl⟩, hm_drop2⟩ :=
    satisfies_pure_left hm_drop1
  clear hm_drop1
  subst hw0_eq hw1_eq hw2_eq hw3_eq_init
  obtain ⟨hw0_ne1, hw0_ne2, _⟩ := ne_neg_tags_of_lt_two_pow_63 hcap_lt
  cases hcur : r.currentSession with
  | some sess =>
    have hm_cur : s.mem ⊨
        ⌜recordCurCap g ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
        ((((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          (recordHeap A g r ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            protocolAddressAt A x.rem x.remA ∗
            A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0)) ∗ R) := by
      refine Satisfies.mono ?_ hm_drop2
      refine Entails.trans (sepConj_mono_left (curSession_some_of_recordTailInline htail_inl hcur)) ?_
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame_eq_rec_sep kit st0 ikit ist0 ctl x s0 v50]
      exact Entails.of_eq (by ac_rfl)
    clear hm_drop2
    obtain ⟨hw3_ne, hm_cur'⟩ := satisfies_pure_left hm_cur
    clear hm_cur
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_sepWP_frozen ⟨hF, hsym⟩ hm_cur'
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_some_cur_wp env hpc hrun hsp hal hw0_ne1 hw0_ne2 hw3_ne htail
        hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps) ?_
    intro sf P_f hpcf hrunf hpostf hFf hm_f
    rcases hpostf with ⟨hspf, half, htrf, hx19f, hx29f, hvregsf, hx20f, hx21f, hx25f, hx26f, hx28f, rfl⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_done ⟨r, g, sess, hcur, ⟨hscope, hl⟩, ?_⟩
    refine ⟨?_, ⟨hrunf, hspf, hal0, half, by rw [hx29f, hx29], by rw [hx19f, hx19], hFf.1, hFf.2, by rw [hvregsf, hvregs]⟩,
      by rw [htrf, htr],
      ⟨hx20f, hx21f, hx25f, hx26f, hx28f⟩,
      hpt_lt, hrest_lt, hloc_ne, hnsec, enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩
    · rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.curPC, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_fnAddr env, hpcf]
    · dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeam, curScratch]
      refine Satisfies.mono ?_ hm_f
      have hrec := sessionRecordAt_of_words56_sep_tail A (s0.sp - 0xbe0#64 + 0x110#64) g r htail_inl
      have h38 : (s0.sp - 0xbe0#64 + 0x110#64) + 0x38#64 = s0.sp - 0xbe0#64 + 0x148#64 := by bv_arith
      rw [h38] at hrec
      have h46a := memRegion_0x46a_0x716_fold (s0.sp - 0xbe0#64) w4 w5 w6 tail htail
      have hspills := encSpillsAt_fold kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x
      have hperm_cur :
          (recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
            ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            (recordHeap A g r ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              protocolAddressAt A x.rem x.remA ∗
              A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
              CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0)) ∗ R =
          (recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
            ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗ recordHeap A g r) ∗
          (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
            ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
            memRegion (s0.sp - 0xbe0#64) 0x50 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
            memRegion x.ret 248 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)) := by
        dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon]
        ac_rfl
      rw [hperm_cur]
      refine Entails.trans (sepConj_mono hrec (sepConj_mono hspills (sepConj_mono_left h46a))) ?_
      exact Entails.of_eq (by ac_rfl)
  | none =>
    obtain ⟨_, hw3_eq⟩ := curSession_none_of_recordTailInline htail_inl hcur
    rw [hw3_eq] at hx23
    have hm_nocur : s.mem ⊨
        (((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          (vecGhostAt A x.rem.name x.remA ∗
            ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
            A.pool ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
            stackAt (s0.sp - 0xbe0#64) extHookStack ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
            (recordHeap A g r ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0))) ∗ R := by
      refine Satisfies.mono ?_ hm_drop2
      rw [protocolAddressAt, memRegion_0x580_split_24 (s0.sp - 0xbe0#64),
          stack_encSub_extHook (s0.sp - 0xbe0#64), CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame_eq_rec_sep kit st0 ikit ist0 ctl x s0 v50]
      exact Entails.of_eq (by ac_rfl)
    clear hm_drop2
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_sepWPp
      (target := (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64) hm_nocur ?_
    have hpre_wp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_some_nocur_pre_wp env
      (remA := x.remA) (v50 := v50)
      (w0 := g.prevCap) (w1 := g.prevPtr) (w2 := 0#64) (w4 := w4) (w5 := w5) (w6 := w6)
      (tail := tail)
      (F := vecGhostAt A x.rem.name x.remA ∗
        ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
        memRegion (x.remA + 0x19#64) 7 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
        A.pool ∗
        memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt (s0.sp - 0xbe0#64) extHookStack ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
        (recordHeap A g r ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0))
      hpc hrun hsp hal hw0_ne1 hw0_ne2 htail hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps
    refine messageEncrypt_of_sepWP_frozen ⟨hF, hsym⟩ (SepWP.mono hpre_wp ?_)
    intro sm P_m hpcm hrunm hpostm hFm
    rcases hpostm with ⟨hspm, halm, htrm, hx0m, hx8m, hx22m, hx30m, hx19m, hx29m, hvregsm, hx26m, hx28m, rfl⟩
    refine messageEncrypt_call_panic_then_wp_frozen (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.stringClone_ok_at_enc env)
      (x := (x.remA, s0.sp - 0xbe0#64 + 0x580#64, x.rem.name))
      (F := ((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
        ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
        ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
        ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6) ∗
        ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
        ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
        ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
        memRegion (x.remA + 0x19#64) 7 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
        memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
        (recordHeap A g r ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0))
      hFm hpcm hrunm halm hx30m ?_ ?_ (fun _ _ => rfl) ?_
    · intro R' hm'
      dsimp only [stringCloneSpec]
      refine Satisfies.mono ?_ hm'
      rw [hspm]
      have hperm_c :
          (((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
            ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
            ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6) ∗
            ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            (vecGhostAt A x.rem.name x.remA ∗
              ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
              memRegion (x.remA + 0x19#64) 7 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
              A.pool ∗
              memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
              stackAt (s0.sp - 0xbe0#64) extHookStack ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
              (recordHeap A g r ∗
                memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
                CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0))) ∗ R' =
          (vecGhostAt A x.rem.name x.remA ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
            A.pool ∗
            stackAt (s0.sp - 0xbe0#64) extHookStack) ∗
          ((((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
            ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
            ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6) ∗
            ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
            (recordHeap A g r ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0)) ∗ R') := by ac_rfl
      rw [hperm_c]
      apply sepConj_mono_left
      exact Entails.pure_right (And.intro hx0m hx8m) (Entails.refl _)
    · intro sf_p
      dsimp only [stringCloneSpec]
      exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.alloc_onPanic_entails
        ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), by rw [htrm, htr]⟩
    · intro sf1 hpc1 hrun1 hsp1 hcs1
      rcases hcs1 with ⟨hcs19, _, _, hcs22, _, _, _, hcs26, _, hcs28, hcs29, hcsv1⟩
      dsimp only [stringCloneSpec]
      wp_simp_pre [sepConj_assoc]
      apply SepWP.pure_elim; intro htr1
      wp_conv_pre => rw [vecU8_eq_words3_sep_buf_lt]
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
      apply SepWP.exists_elim; intro cap
      apply SepWP.exists_elim; intro ptr
      wp_simp_pre [sepConj_pure_left_comm, sepConj_assoc]
      apply SepWP.pure_elim; intro hcap_lt_c
      have hcap_ne2 : cap ≠ 0xFFFFFFFFFFFFFFFE#64 := (ne_neg_tags_of_lt_two_pow_63 hcap_lt_c).2.1
      have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
      have hal1 : sf1.spAligned = true := by rw [State.spAligned, hsp1, ← State.spAligned]; exact halm
      have hx22_1 : sf1.readReg64 .x22 = x.remA := by rw [hcs22, hx22m]
      have hx26_1 : sf1.readReg64 .x26 = s0.sp - 0xbe0#64 + 0x9d0#64 := by rw [hcs26, hx26m]
      have hx28_1 : sf1.readReg64 .x28 = s0.sp - 0xbe0#64 + 0x4a0#64 := by rw [hcs28, hx28m]
      have hx29_1 : sf1.readReg64 .x29 = s0.sp - 0xbe0#64 + 0xb80#64 := by
        rw [hcs29, hx29m, hx29, sp_sub_0x60_eq_sub_0xbe0_add_0xb80]
      have hpost_wp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_some_nocur_post_wp env
        (s := sf1) (sp := s0.sp - 0xbe0#64) (remA := x.remA)
        (cap := cap) (ptr := ptr) (len := BitVec.ofNat 64 x.rem.name.bytes.length)
        (w0 := g.prevCap) (w1 := g.prevPtr) (w2 := 0#64) (w4 := w4) (w5 := w5) (w6 := w6)
        (dev := x.rem.device)
        (F := ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          vecGhostAt A x.rem.name x.remA ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          vecU8Buf A cap ptr x.rem.name.bytes ∗
          A.pool ∗
          stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          (recordHeap A g r ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0))
        hpc1 hrun1 hsp1' hal1 hcap_ne2 hx22_1 hx26_1 hx28_1 hx29_1
      have hpre_post_eq :
          vecGhostAt A x.rem.name x.remA ∗
            ((s0.sp - 0xbe0#64 + 0x580#64) ↦₆₄ cap) ∗
            ((s0.sp - 0xbe0#64 + 1416#64) ↦₆₄ ptr) ∗
            ((s0.sp - 0xbe0#64 + 1424#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
            vecU8Buf A cap ptr x.rem.name.bytes ∗
            A.pool ∗
            stackAt sm.sp extHookStack ∗
            ((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
            ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
            ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6) ∗
            ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
            recordHeap A g r ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0 =
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
            ((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
            ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
            ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6) ∗
            ((s0.sp - 0xbe0#64 + 0x580#64) ↦₆₄ cap) ∗
            ((s0.sp - 0xbe0#64 + 0x588#64) ↦₆₄ ptr) ∗
            ((s0.sp - 0xbe0#64 + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
            (((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
              ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
              ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
              ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              vecGhostAt A x.rem.name x.remA ∗
              memRegion (x.remA + 0x19#64) 7 ∗
              vecU8Buf A cap ptr x.rem.name.bytes ∗
              A.pool ∗
              stackAt (s0.sp - 0xbe0#64) encSubStack ∗
              (recordHeap A g r ∗
                memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
                CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0)) := by
        rw [hspm, ← stack_encSub_extHook_back (s0.sp - 0xbe0#64)]
        ac_rfl
      refine sepWP_conseq_pc_run hpre_post_eq hpost_wp ?_
      intro sf P_f hpcf hrunf hpostf hFf hm_f
      rcases hpostf with ⟨w3', hdev, hspf, half, htrf, hx19f, _hx29f, hvregsf, hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
      have hm_rod := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.rodata_message_encrypt_intro env.loads hFf.1.roData hm_f
      have hm_eq : x.model C S uuidTryParse (answersOfLoad (.ok (some r))) =
          (.error (.sessionNotFound x.rem.val "message_encrypt"), [.loadSession x.rem.val]) := by
        unfold EncryptGhost.model messageEncrypt Api.run storeCall answersOfLoad
        simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
          ExceptT.lift, StateT.bind, pure, ExceptT.pure, StateT.pure, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift,
          MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe, MonadExceptOf.throw, hcur]
        rfl
      have hfinal :
          kit.storeFinal st0 (answersOfLoad (.ok (some r)))
            (x.model C S uuidTryParse (answersOfLoad (.ok (some r)))).2 = st0 := by
        rw [congrArg Prod.snd hm_eq]
        rfl
      have hifinal :
          ikit.idFinal ist0 (answersOfLoad (.ok (some r)))
            (x.model C S uuidTryParse (answersOfLoad (.ok (some r)))).2 = ist0 := by
        rw [congrArg Prod.snd hm_eq]
        rfl
      refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_false (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.tailFreePrevSessions_ok env x R s0 sf (answersOfLoad (.ok (some r)))
        (.sessionNotFound x.rem.val "message_encrypt")
        cap ptr (BitVec.ofNat 64 x.rem.val.name.length) w3' (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) 15#64
        (vecU8Buf A cap ptr x.rem.val.name ∗ ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt"))
        g.prevCap g.prevPtr
        (tailModel_load_some_none hl hcur (by rw [htrf, htr1, htrm, htr]))
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.speStaged_sessionNotFound_devWord A img.base x.ret cap ptr w3' x.rem.val hdev)
        ⟨?_, ⟨hrunf, hspf, hal0, half,
          by rw [_hx29f, ← sp_sub_0x60_eq_sub_0xbe0_add_0xb80],
          by rw [hx19f, hcs19, hx19m, hx19], hFf.1, hFf.2,
          by rw [hvregsf, hcsv1, hvregsm, hvregs]⟩,
          ⟨hx26f, hx28f, hx27f, hx21f, hx23f⟩,
          enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
      · rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_fnAddr env, hpcf]
      · dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.EncTailV]
        rw [draws_answersOfLoad_some_none S x r hcur, hfinal, hifinal]
        refine Satisfies.mono ?_ hm_rod
        have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
          w3' (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) 15#64 w4 w5 w6 tail htail
        have hrec_noCur := recordNoCur_fold_sp110 A (s0.sp - 0xbe0#64) g r htail_inl hcur
        have h280 := memRegion_0x280_0x1ea_fold (s0.sp - 0xbe0#64)
        have hperm_end :
            ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt") ∗
            ((((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
              recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64
                0xFFFFFFFFFFFFFFFF#64 w4 w5 w6 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
              ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
              ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)))) ∗
              ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
              (((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
                memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
                ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
                ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
                ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
                ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
                ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
                ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
                vecGhostAt A x.rem.name x.remA ∗
                memRegion (x.remA + 0x19#64) 7 ∗
                vecU8Buf A cap ptr x.rem.name.bytes ∗
                A.pool ∗
                stackAt (s0.sp - 0xbe0#64) encSubStack ∗
                (recordHeap A g r ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
                  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec kit st0 ikit ist0 ctl x s0))) ∗ R) =
            (memRegion (s0.sp - 0xbe0#64) 0x50 ∗
              ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64))) ∗
            (recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64
              0xFFFFFFFFFFFFFFFF#64 w4 w5 w6 ∗
              ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗ recordHeap A g r) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
              ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8)) ∗
            ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
              ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188) ∗
            (((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
              ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)))) ∗
              ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64)) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198) ∗
            (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
            ((vecU8Buf A cap ptr x.rem.val.name ∗ ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt")) ∗
              memRegion x.ret 248 ∗
              CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)) := by
          dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNoRec, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, protocolAddressAt, AddrGhost.val]
          ac_rfl
        rw [hperm_end]
        refine Entails.trans (sepConj_mono (fold_sp58 _ _)
          (sepConj_mono hrec_noCur
            (sepConj_mono h280
              (sepConj_mono hpoll
                (sepConj_mono_left (encSpillsAt_fold _ _ _ _)))))) ?_
        exact Entails.of_eq (by ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_okV {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x R s0 hfs hpc0 hrun0 hal0 hm0
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_to_dispatch env x R s0 hfs hpc0 hrun0 hal0 hm0 ?_
  intro s sp ans w0 w1 w2 w3 w4 w5 w6 v50 tail hsp_eq hpc hmeta hbnds _hw0_ne3 htail
    hl htr hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps hm
  rcases ans with ⟨⟩ | (_ | r)
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_err env x R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx27 hx21 hx23 hx25 hx26 hx28 hps hm
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_none env x R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx24 hx26 hx28 hps hm
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_some env x R s0 s r sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hsp_eq hpc hmeta hbnds htail hl htr hx24 hx27 hx21 hx23
      hx25 hx26 hx28 hps hm

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_ok {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_okV

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
