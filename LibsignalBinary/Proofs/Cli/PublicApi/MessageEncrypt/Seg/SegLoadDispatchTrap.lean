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
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

@[expose] public section

set_option autoImplicit false

/-!
# Trap-Mode `segLoad` Dispatch for `Err` and `Ok none`

Proves the trap-mode `segLoad` exit branches when the session-store load returns `.error ()`
(`+0x160..+0x174` → T2) or `.ok none` (`+0x178..+0x180`, `+0x41c..+0x458` → T2).
-/

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

/-! ## 1. Frame & `.rodata` Helpers for `E2` Exits -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_err_wp_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (_env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp w4 w5 w6 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hps : s.pstate = addsPState64 0xFFFFFFFFFFFFFFFE#64 2#64) :
    SepWP (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x5b4#64) s
      (((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        P_f = (((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x848#64) 0x188 ∗
          ((sp + 0x9d0#64) ↦₆₄ w4) ∗ ((sp + 0x9d8#64) ↦₆₄ w5) ∗ ((sp + 0x9e0#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x160 0x18
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx25 hx26
  wp_conv_pre => rw [memRegion_0x848_split_0x9d0 s.sp]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm, hx26, hal_norm, true_and]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_sepWP_frozen_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {post : State → SepProp → Prop} {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (trTrapProgAt img.base C abs) target s P post)
    (hcont : ∀ sf P_f, sf.pc = target → sf.status = .Running → post sf P_f →
      FrozenInv img sf → (sf.mem ⊨ P_f ∗ R) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 sf Out) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_f, hmf, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout'⟩ :=
    hcont sm P_f hpcm hrunm hpost (hF.of_steps hsteps) hmf (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_err_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64)
    (hmeta : encMidMeta img x s0 s)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.error ()))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.error ()))
    (hx27 : s.readReg64 .x27 = w1) (hx21 : s.readReg64 .x21 = w2) (hx23 : s.readReg64 .x23 = w3)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutRes Scope A img.base (.error ()) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A x.rem x.remA ∗
      A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun s' => ∃ r g sess,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hF, hsym, hvregs⟩
  have hm_drop : s.mem ⊨
      LoadOutRes Scope A img.base (.error ()) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        protocolAddressAt A x.rem x.remA ∗
        A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  clear hm
  rw [loadOutRes_err_eq, sepConj_assoc] at hm_drop
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hm_drop'⟩ := satisfies_pure_left hm_drop
  rw [← sepConj_assoc] at hm_drop'
  have hm_tail : s.mem ⊨
      (((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
        (((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          memRegion (s0.sp - 0xbe0#64) 0x58 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
          encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗
          encStoreExtra kit st0 ikit ist0 x s0)) ∗ R := by
    refine Satisfies.mono ?_ hm_drop'
    refine sepConj_mono_left ?_
    have hfr := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame_tail_entails kit st0 ikit ist0 ctl x s0 v50
    have hperm1 :
        ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          protocolAddressAt A x.rem x.remA ∗
          A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) =
        (protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗
        (((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6)) := by ac_rfl
    rw [hperm1]
    refine Entails.trans (sepConj_mono_left hfr) ?_
    exact Entails.of_eq (by ac_rfl)
  have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_err_wp_trap env
    (w4 := 1#64) (w5 := img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) (w6 := w6)
    (F := ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
      ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
      memRegion (s0.sp - 0xbe0#64) 0x58 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗
      encStoreExtra kit st0 ikit ist0 x s0)
    hpc hrun hsp hal hx25 hx26 hps
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_sepWP_frozen_trap ⟨hF, hsym⟩ hm_tail hwp ?_
  intro sf P_f hpcf hrunf hpostf hFf hm_f
  rcases hpostf with ⟨hspf, half, htrf, hx19f, hx29f, hvregsf, hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_false_trap (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.tailWriteErr_ok_trap env x R s0 sf (answersOfLoad (.error ())) (.store ())
    0x800000000000001A#64 (img.base + bv% (ls_reloc% 0x77cc)) 10#64 1#64 (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w6
    ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)
    (tailModel_load_err hl (htrf.trans htr))
    (speStaged_storeErr A img.base x.ret w6)
    ⟨?_, ⟨hrunf, hspf, hal0, half, hx29f.trans hx29, hx19f.trans hx19, hFf.1, hFf.2, hvregsf.trans hvregs⟩,
      ⟨hx26f, hx28f.trans hx28, hx27f.trans hx27, hx21f.trans hx21, hx23f.trans hx23⟩,
      enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
  · rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_fnAddr_trap env, hpcf]
  · dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.EncTailV]
    rw [draws_answersOfLoad_err]
    change sf.mem ⊨ _ ∗ _ ∗ _ ∗ _ ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)
    refine Satisfies.mono ?_ hm_f
    have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
      1#64 (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w6
      1#64 (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w6 tail htail
    have hperm2 :
        ((((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
          ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
          (((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            memRegion (s0.sp - 0xbe0#64) 0x58 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
            encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
            memRegion x.ret 248 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗
            encStoreExtra kit st0 ikit ist0 x s0)) ∗ R) =
        ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188) ∗
        (((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
          ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ w6)) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198) ∗
        (memRegion (s0.sp - 0xbe0#64) 0x58 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
          ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ∗
          encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗
          (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)) := by ac_rfl
    rw [hperm2]
    refine Entails.trans (sepConj_mono_left hpoll) ?_
    exact Entails.of_eq (by ac_rfl)

/-! ## 2. Branch 2: `ans = .ok none` (`+0x160`, `+0x178..+0x180`, `+0x41c..+0x458` → `+0x5b4`) -/

set_option linter.unusedVariables false in

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_none_pre_wp_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (_env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp remA : BitVec 64} {F : SepProp}
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = 0xFFFFFFFFFFFFFFFF#64)
    (hps : s.pstate = addsPState64 0xFFFFFFFFFFFFFFFF#64 2#64) :
    SepWP (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) s
      (((sp + 0x108#64) ↦₆₄ remA) ∗ F)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = remA ∧
        sf.readReg64 .x8 = sp + 0x580#64 ∧
        sf.readReg64 .x22 = remA ∧
        sf.readReg64 .x30 = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x428#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        P_f = (((sp + 0x108#64) ↦₆₄ remA) ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x160 0x24
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x41c 0x0c
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx24
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm, hal_norm, true_and]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_none_post_wp_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {s : State} {sp remA cap ptr len : BitVec 64} {dev : BitVec 8} {F : SepProp}
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = remA)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x5b4#64) s
      (((remA + 0x18#64) ↦₈ dev) ∗
        ((sp + 0x580#64) ↦₆₄ cap) ∗ ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ len) ∗
        memRegion (sp + 0x598#64) 344 ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        ∃ w3 : BitVec 64, DevWord dev w3 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          sf.readReg64 .x26 = sp + 0x9d0#64 ∧
          sf.readReg64 .x28 = sp + 0x4a0#64 ∧
          sf.readReg64 .x27 = cap ∧
          sf.readReg64 .x21 = ptr ∧
          sf.readReg64 .x23 = len ∧
          P_f = (((remA + 0x18#64) ↦₈ dev) ∗
            memRegion (sp + 0x580#64) 368 ∗
            memRegion (sp + 0x848#64) 0x188 ∗
            ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)))) ∗
            ((sp + 0x9e0#64) ↦₆₄ 15#64) ∗
            memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hadrp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.enc_adrp_0x4d6a0 (H := Rust.withPanics (trTrapExterns C abs))
    env.loads 0x43c#64 (Or.inr rfl)
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = (ls_off% "libsignal_cli_ratchet::encrypt") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")
  code_fetches_range CryptoVerification.libsignalSessionCode messageEncryptLoadBinCli img.base
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "libsignal_cli_ratchet::encrypt") 0x428 0x34
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  simp only [wp_norm, arm64_norm] at hx22 hx26 hx28 hadrp
  wp_conv_pre =>
    rw [memRegion_0x598_split s.sp, memRegion_0x848_split_0x9d0 s.sp]
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
  apply SepWP.fold (memRegion_0x580_368_fold s.sp cap ptr len w3 _) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨w3, hdev, ?_⟩
  simp only [wp_norm, arm64_norm, hx26, hx28, hal_norm, true_and]
  ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_none_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x160#64)
    (hmeta : encMidMeta img x s0 s)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.ok none))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok none))
    (hx24 : s.readReg64 .x24 = w0)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutRes Scope A img.base (.ok none) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A x.rem x.remA ∗
      A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun s' => ∃ r g sess,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hF, hsym, hvregs⟩
  have hm_drop : s.mem ⊨
      LoadOutRes Scope A img.base (.ok none) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
        (vecGhostAt A x.rem.name x.remA ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          A.pool ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          stackAt (s0.sp - 0xbe0#64) extHookStack ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    refine Satisfies.mono ?_ hm
    rw [protocolAddressAt, memRegion_0x580_split_24 (s0.sp - 0xbe0#64),
        stack_encSub_extHook (s0.sp - 0xbe0#64), CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrame_eq_108_848_sep kit st0 ikit ist0 ctl x s0 v50]
    exact Entails.of_eq (by ac_rfl)
  clear hm
  rw [loadOutRes_none_eq] at hm_drop
  obtain ⟨rfl, hm_drop'⟩ := satisfies_pure_left hm_drop
  clear hm_drop
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_sepWPp_trap
    (target := (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x5b4#64) hm_drop' ?_
  have hpre_wp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_none_pre_wp_trap env
    (remA := x.remA)
    (F := vecGhostAt A x.rem.name x.remA ∗
      ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      memRegion (x.remA + 0x19#64) 7 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
      A.pool ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
      stackAt (s0.sp - 0xbe0#64) extHookStack ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))
    hpc hrun hsp hal hx24 hps
  refine messageEncrypt_of_sepWP_frozen ⟨hF, hsym⟩ (SepWP.mono hpre_wp ?_)
  intro sm P_m hpcm hrunm hpostm hFm
  rcases hpostm with ⟨hspm, halm, htrm, hx0m, hx8m, hx22m, hx30m, hx19m, hx29m, hvregsm, hx26m, hx28m, rfl⟩
  refine messageEncrypt_call_panic_then_wp_frozen (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.stringClone_ok_at_enc_trap env)
    (x := (x.remA, s0.sp - 0xbe0#64 + 0x580#64, x.rem.name))
    (F := ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
      ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      memRegion (x.remA + 0x19#64) 7 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))
    hFm hpcm hrunm halm hx30m ?_ ?_ (fun _ _ => rfl) ?_
  · intro R' hm'
    dsimp only [stringCloneSpec]
    refine Satisfies.mono ?_ hm'
    rw [hspm]
    have hperm_c :
        (((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          (vecGhostAt A x.rem.name x.remA ∗
            ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
            A.pool ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
            stackAt (s0.sp - 0xbe0#64) extHookStack ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))) ∗ R' =
        (vecGhostAt A x.rem.name x.remA ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
          A.pool ∗
          stackAt (s0.sp - 0xbe0#64) extHookStack) ∗
        ((((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50)) ∗ R') := by ac_rfl
    rw [hperm_c]
    apply sepConj_mono_left
    exact Entails.pure_right (And.intro hx0m hx8m) (Entails.refl _)
  · intro sf_p
    dsimp only [stringCloneSpec]
    exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.alloc_onPanic_entails (by rw [htrm, htr]; exact ⟨kit.loadEvs encRecord x.rem.val (.ok none), rfl⟩)
  · intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨hcs19, _, _, hcs22, _, _, _, hcs26, _, hcs28, hcs29, hcsv1⟩
    dsimp only [stringCloneSpec]
    wp_conv_pre => rw [vecU8_eq_words3_sep_buf]
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    apply SepWP.exists_elim; intro cap
    apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; intro htr1
    have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
    have hal1 : sf1.spAligned = true := by rw [State.spAligned, hsp1, ← State.spAligned]; exact halm
    have hx22_1 : sf1.readReg64 .x22 = x.remA := by rw [hcs22, hx22m]
    have hx26_1 : sf1.readReg64 .x26 = s0.sp - 0xbe0#64 + 0x9d0#64 := by rw [hcs26, hx26m, hx26]
    have hx28_1 : sf1.readReg64 .x28 = s0.sp - 0xbe0#64 + 0x4a0#64 := by rw [hcs28, hx28m, hx28]
    have hpost_wp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_dispatch_none_post_wp_trap env
      (s := sf1) (sp := s0.sp - 0xbe0#64) (remA := x.remA)
      (cap := cap) (ptr := ptr) (len := BitVec.ofNat 64 x.rem.name.bytes.length)
      (dev := x.rem.device)
      (F := vecGhostAt A x.rem.name x.remA ∗
        memRegion (x.remA + 0x19#64) 7 ∗
        vecU8Buf A cap ptr x.rem.name.bytes ∗
        A.pool ∗
        stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
        (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))
      hpc1 hrun1 hsp1' hal1 hx22_1 hx26_1 hx28_1
    have hpre_post_eq :
        vecGhostAt A x.rem.name x.remA ∗
          ((s0.sp - 0xbe0#64 + 0x580#64) ↦₆₄ cap) ∗
          ((s0.sp - 0xbe0#64 + 1416#64) ↦₆₄ ptr) ∗
          ((s0.sp - 0xbe0#64 + 1424#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          vecU8Buf A cap ptr x.rem.name.bytes ∗
          A.pool ∗
          stackAt sm.sp extHookStack ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50 =
        ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          ((s0.sp - 0xbe0#64 + 0x580#64) ↦₆₄ cap) ∗
          ((s0.sp - 0xbe0#64 + 0x588#64) ↦₆₄ ptr) ∗
          ((s0.sp - 0xbe0#64 + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (vecGhostAt A x.rem.name x.remA ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            vecU8Buf A cap ptr x.rem.name.bytes ∗
            A.pool ∗
            stackAt (s0.sp - 0xbe0#64) encSubStack ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50)) := by
      rw [hspm, ← stack_encSub_extHook_back (s0.sp - 0xbe0#64)]
      ac_rfl
    refine sepWP_conseq_pc_run hpre_post_eq hpost_wp ?_
    intro sf P_f hpcf hrunf hpostf hFf hm_f
    rcases hpostf with ⟨w3', hdev, hspf, half, htrf, hx19f, hx29f, hvregsf, hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
    have hm_rod := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.rodata_message_encrypt_intro env.loads hFf.1.roData hm_f
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_false_trap (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.tailWriteErr_ok_trap env x R s0 sf (answersOfLoad (.ok none))
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.val.name.length) w3' (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) 15#64
      (vecU8Buf A cap ptr x.rem.val.name ∗ ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt"))
      (tailModel_load_none hl (by rw [htrf, htr1, htrm, htr]))
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.speStaged_sessionNotFound_devWord A img.base x.ret cap ptr w3' x.rem.val hdev)
      ⟨?_, ⟨hrunf, hspf, hal0, half,
        by rw [hx29f, hcs29, hx29m, hx29],
        by rw [hx19f, hcs19, hx19m, hx19], hFf.1, hFf.2,
        by rw [hvregsf, hcsv1, hvregsm, hvregs]⟩,
        ⟨hx26f, hx28f, hx27f, hx21f, hx23f⟩,
        enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
    · rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_fnAddr_trap env, hpcf]
    · dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.EncTailV]
      rw [draws_answersOfLoad_none]
      change sf.mem ⊨ _ ∗ _ ∗ _ ∗ _ ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)
      refine Satisfies.mono ?_ hm_rod
      have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
        w3' (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) 15#64 w4 w5 w6 tail htail
      have hperm_end :
          ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt") ∗
          ((((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
            ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
            ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)))) ∗
            ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
            (vecGhostAt A x.rem.name x.remA ∗
              memRegion (x.remA + 0x19#64) 7 ∗
              vecU8Buf A cap ptr x.rem.name.bytes ∗
              A.pool ∗
              stackAt (s0.sp - 0xbe0#64) encSubStack ∗
              ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
              (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
                ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
                ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
                ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
                ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
                CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848 kit st0 ikit ist0 ctl x s0 v50))) ∗ R) =
          (memRegion (s0.sp - 0xbe0#64) 0x50 ∗ ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50)) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
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
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗
            (encStoreExtra kit st0 ikit ist0 x s0 ∗ R)) := by
        dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dispatchFrameNo108848, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, protocolAddressAt, AddrGhost.val]
        ac_rfl
      rw [hperm_end]
      refine Entails.trans (sepConj_mono (fold_sp58 _ _)
        (sepConj_mono (memRegion_0x110_0x35a_fold _ _ _)
          (sepConj_mono hpoll
            (sepConj_mono_left (encSpillsAt_fold _ _ _ _))))) ?_
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
