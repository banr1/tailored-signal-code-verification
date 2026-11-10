/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegPostSomeHelpers
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.RecordJoin
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegPostSomeHelpers
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Ext-Generic `SegPostSome` (`+0x1f50 → +0x1fcc / +0x22a8 / panic`)

Proves ext-generic post-decrypt dispatch and remote identity key lookup `segPostSomeVX_ok_ext`
over `tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome
open ProofLib.ProgramReflection

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem segPostSome_err_act_sat {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {x : DecryptGhost} {s0 : State} {sp prevCap prevPtr : BitVec 64}
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {e : SignalProtocolError} {w21 w2 : BitVec 32} {w0 w1 w3 w4 : BitVec 64}
    {H R' : SepProp} {draws : Nat} {m : Memory}
    (hsp_def : sp = s0.sp - 0xee0#64)
    (hmem2 : m ⊨
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (sp + 0x138#64) G st) ∗
      ((((sp + 0x4b0#64) ↦₆₄ recordResultTag (.error e)) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗ H) ∗
       (memRegion (sp + 0x4e0#64) 0x920 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ R'))) :
    m ⊨
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ recordResultTag (.error e)) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24) ∗
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (sp + 0x138#64) G st ∗
        H ∗
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        wsFixedV kit ikit x s0 sp ∗
        ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
        memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
        memRegion x.ret 48 ∗ R') := by
  subst hsp_def
  let sp := s0.sp - 0xee0#64
  have h300_split :
      memRegion (sp + 0x300#64) 0x1b0 =
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4a4#64) 0xc := by
    rw [memRegion_split (sp + 0x300#64) 0x190 0x20 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xc (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h4e0_split :
      memRegion (sp + 0x4e0#64) 0x920 =
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x580#64) 0x24 ∗
          memRegion (sp + 0x5a4#64) 0x85c := by
    rw [memRegion_split (sp + 0x4e0#64) 0xa0 0x880 (by decide),
        memRegion_split (sp + 0x4e0#64 + 0xa0#64) 0x24 0x85c (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hws_eq :
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr =
        wsFixedV kit ikit x s0 sp ∗
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x1b0 ∗
          memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
          memRegion x.ret 48 := by
    unfold wsRegionFrameV wsFixedV
    dsimp only [sp]
    ac_rfl
  rw [hws_eq, h300_split, h4e0_split] at hmem2
  dsimp only [sp] at hmem2 ⊢
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2

set_option maxHeartbeats 400000 in
private theorem segPostSome_err_wp {img : Obj.Image} {ext : String → Option (State → State)}
    {x : DecryptGhost} {s0 s : State} {sp : BitVec 64} {e : SignalProtocolError}
    {w21 w2 : BitVec 32} {w0 w1 w3 w4 : BitVec 64} {bs : List (BitVec 8)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hsp_def : sp = s0.sp - 0xee0#64)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xee0#64)
    (hal : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = x.ret)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.sp - 3648#64)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = recordResultTag (.error e))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hne : e ≠ .panic)
    (hbs_eq : bs = unpack64 w0 ++ unpack64 w1 ++ unpack32 w2 ++ unpack64 w3 ++ unpack64 w4) :
    SepWP (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.errJoinPC img false) s
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ recordResultTag (.error e)) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24)
      (fun sf Pf =>
        (Pf ⊢ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4b0#64) 0x30 ∗
          ((sp + 0x580#64) ↦ₛ bs)) ∧
        sf.sp = s.sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x27 = x.ret ∧
        sf.readReg64 .x26 = sp + 0xa0#64 ∧ sf.readReg64 .x28 = recordResultTag (.error e) ∧
        resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = w21 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0) := by
  subst hsp_def
  let sp := s0.sp - 0xee0#64
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext himg
    CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit at hpc
  rw [hentry] at hpc
  code_fetches_range CryptoVerification.libsignalSessionCode messageDecryptPostSomeBinCli img.base
    (Rust.withPanics ext) hfn (ls_off% "libsignal_cli_ratchet::decrypt_signal") 0x1f50 0x20
  code_fetches_range CryptoVerification.libsignalSessionCode messageDecryptPostSomeBinCli img.base
    (Rust.withPanics ext) hfn (ls_off% "libsignal_cli_ratchet::decrypt_signal") 0x20b4 0x20
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.errJoinPC
  rw [ite_eq_right_iff.mpr nofun, hentry]
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry at *
  examples_hide_fetches
  wp_conv_pre => rw [scratch20_split sp, dst36_split sp]
  dsimp only [sp]
  wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWP.exists_elim; intro _)
  have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
  have hx28_ne : recordResultTag (.error e) + 2#64 ≠ 0#64 :=
    recordResultTag_err_add_two_ne_zero e hne
  wp_steps
  apply SepWP.fold (scratch20_fold (s0.sp - 0xee0#64) w0 w1 w2) (by sep_focus)
  apply SepWP.fold (slot48_fold_memRegion (s0.sp - 0xee0#64) (recordResultTag (.error e)) w21 w0 w1 w2 w3 w4) (by sep_focus)
  apply SepWP.fold (dst36_fold (s0.sp - 0xee0#64) w0 w1 w2 w3 w4 hbs_eq) (by sep_focus)
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine ⟨?_, rfl, hal, rfl, ?_, ?_, ?_, ?_, ?_, hvregs⟩
  · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
    exact Entails.of_eq (by ac_rfl)
  · wp_norm_lhs
  · wp_norm_lhs
  · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
    wp_norm_lhs
  · wp_norm_lhs
  · simp only [wp_norm, arm64_norm]
    exact resWord1_ubfm_eq w21

private theorem segPostSome_err_comb {C : Crypto} {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {x : DecryptGhost} {ans : StoreAnswers (List (BitVec 8)) Unit}
    {s0 : State} {sp prevCap prevPtr x28 x20 x21 : BitVec 64}
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {bs : List (BitVec 8)} {H R' : SepProp} {draws : Nat}
    {res1 : Except (ApiError AddrVal Unit) (List (BitVec 8))}
    (hdraws : x.draws C ans = draws)
    (hstaged : ((sp + 0x580#64) ↦ₛ bs) ∗ H ⊢ StagedRes A x28 x20 x21 (sp + 0x580#64) res1) :
    (memRegion (sp + 0x490#64) 0x14 ∗
      memRegion (sp + 0x4b0#64) 0x30 ∗
      ((sp + 0x580#64) ↦ₛ bs)) ∗
    (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
      ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
      sessionStateAt A (sp + 0x138#64) G st ∗
      H ∗
      memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗ logOff img ∗
      stackAt sp rootStack ∗ A.pool ∗
      wsFixedV kit ikit x s0 sp ∗
      ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
      memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
      memRegion x.ret 48 ∗ R') ⊢
    wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, st)) ∗
      memRegion (sp + 0x290#64) 24 ∗
      StagedRes A x28 x20 x21 (sp + 0x580#64) res1 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R' := by
  have h290_split :
      memRegion (sp + 0x290#64) 0x38 =
        memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20 := by
    rw [memRegion_split (sp + 0x290#64) 24 0x20 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h300_join :
      memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
        memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
        memRegion (sp + 0x4e0#64) 0xa0 =
      memRegion (sp + 0x300#64) 0x280 := by
    rw [memRegion_split (sp + 0x300#64) 0x190 0xf0 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xdc (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64) 0xc 0xd0 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64) 0x30 0xa0 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hwsEnv_eq :
      signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ logOff img ∗
        (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
        A.pool =
      wsEnv A img x sp := by
    unfold wsEnv
    rw [stackAt_root_join_wsCallee sp]
  rw [hdraws, h290_split]
  have hreord_lhs :
      (memRegion (sp + 0x490#64) 0x14 ∗
        memRegion (sp + 0x4b0#64) 0x30 ∗
        ((sp + 0x580#64) ↦ₛ bs)) ∗
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (sp + 0x138#64) G st ∗
        H ∗
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        wsFixedV kit ikit x s0 sp ∗
        ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
        (memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20) ∗
        memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
        memRegion x.ret 48 ∗ R') =
      ((((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          sessionStateAt A (sp + 0x138#64) G st) ∗
        (((sp + 0x580#64) ↦ₛ bs) ∗ H) ∗
        (wsFixedV kit ikit x s0 sp ∗
          (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗ logOff img ∗
            (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
            A.pool) ∗
          wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗
          memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          (memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
            memRegion (sp + 0x4e0#64) 0xa0) ∗
          memRegion (sp + 0x5a4#64) 0x85c ∗ memRegion x.ret 48 ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗ R')) := by
    ac_rfl
  rw [hreord_lhs, hwsEnv_eq, h300_join]
  refine Entails.trans
    (sepConj_mono (record_some_entails_droppable A sp prevCap prevPtr G st)
      (sepConj_mono_left hstaged)) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem segPostSome_ok_act_sat {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {x : DecryptGhost} {s0 : State} {sp prevCap prevPtr cap ptr : BitVec 64}
    {G' : SessionGhost} {st' : SessionState (List (BitVec 8))}
    {pt : List (BitVec 8)} {w21 w2 : BitVec 32} {w0 w1 : BitVec 64}
    {R' : SepProp} {draws : Nat} {m : Memory}
    (hsp_def : sp = s0.sp - 0xee0#64)
    (hmem_ss : m ⊨
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64)) ∗
      (sessionStateAt A (sp + 0x138#64) G' st' ∗
        (((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
          ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗
          ((sp + 0x4cc#64) ↦₃₂ w2) ∗ memRegion (sp + 0x4d0#64) 16 ∗
          CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.vecU8Buf A cap ptr pt ∗
          memRegion (sp + 0x4e0#64) 0x920 ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗ logOff img ∗
          stackAt sp rootStack ∗ A.pool ∗
          wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ R'))) :
    m ⊨
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        memRegion (sp + 0x4d0#64) 16 ∗
        memRegion (sp + 0x290#64) 24 ∗
        ((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
        vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64) ∗
        memRegion (sp + 0x5f0#64) 34 ∗
        memRegion (sp + 0xca0#64) 32 ∗
        logOff img ∗
        stackAt sp Getters.remoteIdentityKeyStack) ∗
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateRemExposedAt A (sp + 0x138#64) G' st' ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.vecU8Buf A cap ptr pt ∗
        memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x612#64) 0x68e ∗
        memRegion (sp + 0xcc0#64) 0x140 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
        memRegion (sp - 262144#64) 262000 ∗ A.pool ∗
        wsFixedV kit ikit x s0 sp ∗
        ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
        memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
        memRegion x.ret 48 ∗ R') := by
  subst hsp_def
  let sp := s0.sp - 0xee0#64
  have h300_split :
      memRegion (sp + 0x300#64) 0x1b0 =
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4a4#64) 0xc := by
    rw [memRegion_split (sp + 0x300#64) 0x190 0x20 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xc (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h290_split :
      memRegion (sp + 0x290#64) 0x38 =
        memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20 := by
    rw [memRegion_split (sp + 0x290#64) 24 0x20 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h4e0_split :
      memRegion (sp + 0x4e0#64) 0x920 =
        memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x5f0#64) 34 ∗
          memRegion (sp + 0x612#64) 0x68e ∗ memRegion (sp + 0xca0#64) 32 ∗
          memRegion (sp + 0xcc0#64) 0x140 := by
    rw [memRegion_split (sp + 0x4e0#64) 0x110 0x810 (by decide),
        memRegion_split (sp + 0x4e0#64 + 0x110#64) 34 0x7ee (by decide),
        memRegion_split (sp + 0x4e0#64 + 0x110#64 + 34#64) 0x68e 0x160 (by decide),
        memRegion_split (sp + 0x4e0#64 + 0x110#64 + 34#64 + 0x68e#64) 32 0x140 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hstk_split :
      stackAt sp rootStack =
        memRegion (sp - 262144#64) 262000 ∗ stackAt sp Getters.remoteIdentityKeyStack := by
    simp only [stackAt, rootStack, Getters.remoteIdentityKeyStack, Nat.reducePow]
    have hsplit := memRegion_split (sp - 262144#64) 262000 144 (by decide)
    have hadd : sp - 262144#64 + 262000#64 = sp - 144#64 := by bv_omega
    rw [hsplit, hadd]
  have hws_eq :
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr =
        wsFixedV kit ikit x s0 sp ∗
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x1b0 ∗
          memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
          memRegion x.ret 48 := by
    unfold wsRegionFrameV wsFixedV
    dsimp only [sp]
    ac_rfl
  rw [sessionStateAt_expose_rem A (sp + 0x138#64) G' st',
      hws_eq, h300_split, h290_split, h4e0_split, hstk_split] at hmem_ss
  dsimp only [sp] at hmem_ss ⊢
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem_ss

set_option maxHeartbeats 400000 in
private theorem segPostSome_ok_wp_pre {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : DecryptGhost} {s0 s : State} {sp : BitVec 64}
    {G' : SessionGhost} {st' : SessionState (List (BitVec 8))}
    {w21 w2 : BitVec 32} {w0 w1 : BitVec 64}
    (himg : Obj.Loads libsignalSessionImage img)
    (hRemIk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.remoteIdentityKeyName)
      (Getters.remoteIdentityKeySpec A img))
    (hsp_def : sp = s0.sp - 0xee0#64)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xee0#64)
    (hal0 : s0.spAligned = true)
    (hal : s.spAligned = true)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64)
    (hx27 : s.readReg64 (Reg.gpr 27#5) = x.ret)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.sp - 3648#64)
    (hx28 : s.readReg64 (Reg.gpr 28#5) = okTagVec)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_inv : match st'.remoteIdentity with
      | none => G'.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G'.remoteIk.bytes = .ok ik.publicKey)
    (hcap_ne : (G'.localIk.cap + 1#64 == 0#64) = false) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1fc8#64) s
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        memRegion (sp + 0x4d0#64) 16 ∗
        memRegion (sp + 0x290#64) 24 ∗
        ((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
        vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64) ∗
        memRegion (sp + 0x5f0#64) 34 ∗
        memRegion (sp + 0xca0#64) 32 ∗
        logOff img ∗
        stackAt sp Getters.remoteIdentityKeyStack)
      (fun sm Pm =>
        (∃ remBs : List (BitVec 8),
          remBs.length = 32 ∧
          (∀ ik, st'.remoteIdentity = some ik → remBs = ik.publicKey.bytes.toList) ∧
          (Pm ⊢ memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4b0#64) 0x30 ∗
            memRegion (sp + 0x5f0#64) 34 ∗
            (((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
              ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2)) ∗
            (((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
              vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64)) ∗
            ((sp + 0xca0#64) ↦ₛ remBs) ∗
            logOff img ∗
            stackAt sp Getters.remoteIdentityKeyStack)) ∧
        sm.sp = s.sp ∧ sm.spAligned = true ∧ sm.trace = s.trace ∧
        sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x27 = x.ret ∧
        sm.readReg64 .x26 = sp + 0xa0#64 ∧ sm.readReg64 .x22 = sp + 0x294#64 ∧
        sm.readReg64 .x8 = (remoteIdentityTag st'.remoteIdentity).zeroExtend 64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  subst hsp_def
  let sp := s0.sp - 0xee0#64
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext himg
    CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit at hpc
  rw [hentry] at hpc
  have hrem_call := remoteIdentityKey_ok_at_msgDecrypt_ext hRemIk
  code_fetches_range CryptoVerification.libsignalSessionCode messageDecryptPostSomeBinCli img.base
    (Rust.withPanics ext) hfn (ls_off% "libsignal_cli_ratchet::decrypt_signal") 0x1f50 0x78
  dsimp only [tripleRatchetProgAtExt] at hpc hrem_call ⊢
  generalize (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry at *
  examples_hide_fetches
  wp_conv_pre => rw [scratch20_split sp, slot290_split sp, slotca0_split sp]
  dsimp only [sp]
  wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWP.exists_elim; intro _)
  have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
  dsimp only [okTagVec] at hx28
  wp_steps
  wp_call hrem_call
    (Getters.RemoteIdentityKeyGhost.mk (s0.sp - 0xee0#64 + 0x138#64)
      G'.remoteIk st'.remoteIdentity (s0.sp - 0xee0#64 + 0x5f0#64))
  have hfold_rem := remoteIdentityOkAt_unified (s0.sp - 0xee0#64 + 0x5f0#64) st'.remoteIdentity
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hfold_rem
  refine SepWP.fold hfold_rem (by sep_focus) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun remBs => ?_
  refine SepWP.pure_elim fun ⟨hrem_len, hrem_eq⟩ => ?_
  obtain ⟨k0, k1, k2, k3, _hk_bs, hk_pts⟩ := exists_unpack64_of_length_32 hrem_len
  wp_conv_pre => rw [hk_pts (s0.sp - 2286#64)]
  wp_simp_pre [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  wp_steps
  have hf1 := scratch20_fold (s0.sp - 0xee0#64) w0 w1 w2
  have hf2 := slot4b0_ok_fold_memRegion (s0.sp - 0xee0#64) w21 w0 w1 w2
  have hf3 := slot5f0_fold_memRegion (s0.sp - 0xee0#64) 0#8 (remoteIdentityTag st'.remoteIdentity) k0 k1 k2 k3
  have hf4 :
      (((s0.sp - 0xee0#64 + 0xca0#64) ↦₆₄ k0) ∗
        ((s0.sp - 0xee0#64 + 0xca8#64) ↦₆₄ k1) ∗
        ((s0.sp - 0xee0#64 + 0xcb0#64) ↦₆₄ k2) ∗
        ((s0.sp - 0xee0#64 + 0xcb8#64) ↦₆₄ k3)) ⊢
      ((s0.sp - 0xee0#64 + 0xca0#64) ↦ₛ remBs) := by
    rw [hk_pts (s0.sp - 0xee0#64 + 0xca0#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hf1 hf2 hf3 hf4
  apply SepWP.fold hf1 (by sep_focus)
  apply SepWP.fold hf2 (by sep_focus)
  apply SepWP.fold hf3 (by sep_focus)
  apply SepWP.fold hf4 (by sep_focus)
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine ⟨⟨remBs, hrem_len, hrem_eq, ?_⟩,
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *]; exact hal0,
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, hcs_sf, hx29],
    by simp only [wp_norm, arm64_norm, h_8, hx27],
    by simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, wp_norm, arm64_norm, *],
    by simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *]⟩
  rw [hsp]
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
  exact Entails.of_eq (by ac_rfl)

private theorem segPostSome_ok_some_comb {C : Crypto} {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {x : DecryptGhost} {ans : StoreAnswers (List (BitVec 8)) Unit}
    {s0 : State} {sp prevCap prevPtr cap ptr : BitVec 64}
    {G' : SessionGhost} {st' : SessionState (List (BitVec 8))}
    {rec' : SessionRecord (List (BitVec 8))} {pt remBs : List (BitVec 8)}
    {k : IdentityKey} {w21 w2 : BitVec 32} {w0 w1 : BitVec 64}
    {R' : SepProp} {draws : Nat}
    (hdraws : x.draws C ans = draws)
    (hremBs_eq : remBs = k.publicKey.bytes.toList)
    (hbrec :
      ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (sp + 0x138#64) G' st' ⊢
      ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec')
    (hvec_pt : ∀ a : BitVec 64,
      ((a ↦₃₂ w21) ∗ ((a + 4#64) ↦₆₄ w0) ∗ ((a + 12#64) ↦₆₄ w1) ∗
        ((a + 20#64) ↦₃₂ w2) ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.vecU8Buf A cap ptr pt) ⊢
      vecU8 A a pt) :
    (memRegion (sp + 0x490#64) 0x14 ∗
      memRegion (sp + 0x4b0#64) 0x30 ∗
      memRegion (sp + 0x5f0#64) 34 ∗
      (((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
        ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2)) ∗
      (((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
        vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64)) ∗
      ((sp + 0xca0#64) ↦ₛ remBs) ∗
      logOff img ∗
      stackAt sp Getters.remoteIdentityKeyStack) ∗
    (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
      ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
      sessionStateRemExposedAt A (sp + 0x138#64) G' st' ∗
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.vecU8Buf A cap ptr pt ∗
      memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x612#64) 0x68e ∗
      memRegion (sp + 0xcc0#64) 0x140 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
      memRegion (sp - 262144#64) 262000 ∗ A.pool ∗
      wsFixedV kit ikit x s0 sp ∗
      ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
      memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
      memRegion x.ret 48 ∗ R') ⊢
    wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗ R' := by
  have hstk_split :
      stackAt sp rootStack =
        memRegion (sp - 262144#64) 262000 ∗ stackAt sp Getters.remoteIdentityKeyStack := by
    simp only [stackAt, rootStack, Getters.remoteIdentityKeyStack, Nat.reducePow]
    have hsplit := memRegion_split (sp - 262144#64) 262000 144 (by decide)
    have hadd : sp - 262144#64 + 262000#64 = sp - 144#64 := by bv_omega
    rw [hsplit, hadd]
  have h300_join :
      memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
        memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
        memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x5f0#64) 34 ∗
        memRegion (sp + 0x612#64) 0x68e =
      memRegion (sp + 0x300#64) 0x9a0 := by
    rw [memRegion_split (sp + 0x300#64) 0x190 0x810 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0x7fc (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64) 0xc 0x7f0 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64) 0x30 0x7c0 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64 + 0x30#64) 0x110 0x6b0 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64 + 0x30#64 + 0x110#64) 34 0x68e (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hwsEnv_eq :
      signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ logOff img ∗
        ((memRegion (sp - 262144#64) 262000 ∗ stackAt sp Getters.remoteIdentityKeyStack) ∗
          memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
        A.pool =
      wsEnv A img x sp := by
    unfold wsEnv
    rw [← hstk_split, stackAt_root_join_wsCallee sp]
  rw [hdraws, hremBs_eq]
  have hreord_lhs :
      (memRegion (sp + 0x490#64) 0x14 ∗
        memRegion (sp + 0x4b0#64) 0x30 ∗
        memRegion (sp + 0x5f0#64) 34 ∗
        (((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
          ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2)) ∗
        (((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
          vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64)) ∗
        ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
        logOff img ∗
        stackAt sp Getters.remoteIdentityKeyStack) ∗
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateRemExposedAt A (sp + 0x138#64) G' st' ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.vecU8Buf A cap ptr pt ∗
        memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x612#64) 0x68e ∗
        memRegion (sp + 0xcc0#64) 0x140 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗
        memRegion (sp - 262144#64) 262000 ∗ A.pool ∗
        wsFixedV kit ikit x s0 sp ∗
        ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
        memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
        memRegion x.ret 48 ∗ R') =
      ((((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          (((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
            vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64) ∗
            sessionStateRemExposedAt A (sp + 0x138#64) G' st')) ∗
        (((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
          ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2) ∗
          CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.vecU8Buf A cap ptr pt) ∗
        (wsFixedV kit ikit x s0 sp ∗
          (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗ logOff img ∗
            ((memRegion (sp - 262144#64) 262000 ∗ stackAt sp Getters.remoteIdentityKeyStack) ∗
              memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
            A.pool) ∗
          wsMsgCells x sp ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
          memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          (memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
            memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x5f0#64) 34 ∗
            memRegion (sp + 0x612#64) 0x68e) ∗
          memRegion (sp + 0xcc0#64) 0x140 ∗ memRegion x.ret 48 ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗ R')) := by
    ac_rfl
  rw [hreord_lhs, ← sessionStateAt_expose_rem A (sp + 0x138#64) G' st',
      hwsEnv_eq, h300_join]
  have hvec290 :
      ((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
        ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2) ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.vecU8Buf A cap ptr pt ⊢
      vecU8 A (sp + 0x290#64) pt := by
    have hv := hvec_pt (sp + 0x290#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
    exact hv
  refine Entails.trans
    (sepConj_mono hbrec (sepConj_mono_left hvec290)) ?_
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem segPostSomeVX_ok_of_loads_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hRemIk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.remoteIdentityKeyName)
      (Getters.remoteIdentityKeySpec A img))
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hPre : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x false R s0 s') := by
  intro hL
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext himg
    CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
  rcases hPre with ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, hfrozen, hsym, hvregs⟩,
    s1, rec_, ses, G, prevCap, prevPtr, hs1_sp, hs1_tr, hload, hscope, hcur, hw0, hmem⟩
  let sp := s0.sp - 0xee0#64
  let R' : SepProp := decStoreExtra kit ikit st0 ist0 s0 ∗ R
  change s1.sp = sp at hs1_sp
  let x_rg := recGhostOf x prevPtr G ses.state
  change s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).post x_rg s1 s ∗
    wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ R' at hmem
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨⟨hno_pan, htr_s1, hs_sp1, _, _, hx26, hx28⟩, hmem⟩
  rw [hs1_sp] at hx26 hmem
  dsimp only [sp] at hx26
  simp only [wp_norm, arm64_norm] at hx29 hx27 hx26 hx28
  have htrace : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession :=
    htr_s1.trans hs1_tr
  have hdraws : x.draws C ans = x_rg.draws C :=
    draws_eq_region_draws C x prevPtr G ses ans rec_ hload hcur
  have hpc_raw := hpc
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit at hpc
  rw [hentry] at hpc
  rcases hmod_rg : x_rg.model C S uuidTryParse with ⟨res_rg, st'⟩
  cases res_rg with
  | error e =>
    have hmod1 : (x_rg.model C S uuidTryParse).1 = .error e := by rw [hmod_rg]
    have hne : e ≠ .panic := fun hp => hno_pan (hmod1.trans (congrArg Except.error hp))
    have hmod : x.model C S uuidTryParse ans = (.error (.protocol e), [.loadSession x.rem.val]) :=
      model_of_region_err C S x prevPtr G ses ans rec_ e hload hcur hmod1 hne
    rw [hmod1] at hx28 hmem
    dsimp only [x_rg, recGhostOf] at hmem
    have hmem1 : s.mem ⊨
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          sessionStateAt A (sp + 0x138#64) G ses.state) ∗
        (recordResultAt A (sp + 0x4b0#64) (.error e) ∗
          (memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x_rg.draws C) ∗ logOff img ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ R')) := by
      unfold wsMsgCells
      dsimp only [sp] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    clear hmem
    obtain ⟨w21, w0, w1, w2, w3, w4, bs, H, hbs_len, hbs_eq, hreassemble, hmem2⟩ :=
      recordResultAt_err_sat hne hmem1
    clear hmem1
    have hmem_act := segPostSome_err_act_sat (sp := sp) rfl hmem2
    clear hmem2
    have hwp := segPostSome_err_wp (ext := ext) (sp := sp) (w21 := w21)
      himg rfl hpc_raw hrun hsp hal hx29 hx27 hx26 hx28 hvregs hne hbs_eq
    obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_pf, hsp_sf, hal_sf, htr_sf,
      hx29_sf, hx27_sf, hx26_sf, hx28_sf, hres_w1, hvregs_sf⟩ | ⟨_, _hoom⟩⟩ :=
      hwp.elim hmem_act hL
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    clear hmem_act hwp
    have hfrozen_sf : img.FrozenLoaded sf := hfrozen.of_keepsFrozen hsteps.keepsFrozen
    have hsym_sf : sf.symtab = img.symtab := hsteps.symtab_eq.trans hsym
    refine ⟨sf, hsteps, Or.inl (Or.inr ?_)⟩
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_pf) hmf
    clear hmf hent_pf
    refine ⟨hpc_sf, ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf, hx27_sf, hfrozen_sf, hsym_sf, hvregs_sf⟩,
      hx26_sf, ?_, ans, some (G, ses.state), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx28_sf]
      exact recordResultTag_err_ne_pendingTag e hne
    · intro h; rw [hmod] at h; cases h
    · intro p h; rw [hmod] at h; cases h
    · intro r hr; rw [hload] at hr; cases hr; exact hscope
    · rw [hmod]; exact ⟨hload ▸ hscope.2, trivial⟩
    · rw [hmod]; trivial
    · rw [htr_sf, htrace, hmod]; simp
    · have hstaged :
          ((sp + 0x580#64) ↦ₛ bs) ∗ H ⊢
            StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
              (x.model C S uuidTryParse ans).1 := by
        unfold StagedRes
        refine Entails.sepExists_right bs (Entails.sepExists_right H ?_)
        refine Entails.pure_right ⟨hbs_len, fun r => ?_⟩ (Entails.refl _)
        rw [hmod, hx28_sf, hres_w1]
        exact hreassemble r
      have hcomb := segPostSome_err_comb (img := img) (kit := kit) (ikit := ikit) (s0 := s0)
        (prevCap := prevCap) (prevPtr := prevPtr) (G := G) (st := ses.state) (R' := R')
        hdraws hstaged
      have hmf_res := Satisfies.mono hcomb hmf1
      have hsf_eq : kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2 = st0 := by rw [hmod]; rfl
      have hif_eq : ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2 = ist0 := by rw [hmod]; rfl
      rw [hsf_eq, hif_eq]
      simpa only [R', sepConj_assoc, Bool.false_eq_true, ↓reduceIte] using hmf_res
  | ok pt =>
    have hmod1 : (x_rg.model C S uuidTryParse).1 = .ok pt := by rw [hmod_rg]
    have hmod2 : (x_rg.model C S uuidTryParse).2 = st' := by rw [hmod_rg]
    rw [hmod1] at hx28
    dsimp only [recordResultTag] at hx28
    simp only [hmod1, hmod2, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hmem
    dsimp only [x_rg, recGhostOf] at hmem
    obtain ⟨G', hmem⟩ := hmem
    have hmem_rel : s.mem ⊨ ⌜G.AfterRecordDecrypt G'⌝ ∗
        ((memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          sessionStateAt A (sp + 0x138#64) G' st') ∗
         (recordResultAt A (sp + 0x4b0#64) (.ok pt) ∗
          (memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x_rg.draws C) ∗ logOff img ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ R'))) := by
      unfold wsMsgCells
      dsimp only [sp] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    clear hmem
    rw [satisfies_pure_sepConj] at hmem_rel
    obtain ⟨hrel, hmem1⟩ := hmem_rel
    obtain ⟨cap, ptr, w21, w0, w1, w2, hvec_pt, hmem2⟩ := recordResultAt_ok_sat hmem1
    clear hmem1
    have hmem_ss : s.mem ⊨
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64)) ∗
        (sessionStateAt A (sp + 0x138#64) G' st' ∗
          (((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
            ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗
            ((sp + 0x4cc#64) ↦₃₂ w2) ∗ memRegion (sp + 0x4d0#64) 16 ∗
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.vecU8Buf A cap ptr pt ∗ memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x_rg.draws C) ∗ logOff img ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ R')) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
    clear hmem2
    have hrem_inv := sessionStateAt_rem_inv hmem_ss
    have hcap_lt := sessionStateAt_localIk_cap_lt hmem_ss
    have hcap_ne : (G'.localIk.cap + 1#64 == 0#64) = false :=
      beq_eq_false_iff_ne.mpr (cap_add_one_ne_zero hcap_lt)
    have hmem_act := segPostSome_ok_act_sat (sp := sp) rfl hmem_ss
    clear hmem_ss
    have hwp_pre := segPostSome_ok_wp_pre (sp := sp) (w21 := w21) (w2 := w2) (w0 := w0) (w1 := w1)
      himg hRemIk rfl hpc_raw hrun hsp hal0 hal hx29 hx27 hx26 hx28 hvregs hrem_inv hcap_ne
    obtain ⟨sm, hsteps1, ⟨hpc_sm, hrun_sm, Pm, hmf,
      ⟨remBs, _hrem_len, hrem_eq, hent_pm⟩,
      hsp_sm, hal_sm, htr_sm, hx29_sm, hx27_sm, hx26_sm, hx22_sm, hx8_sm, hvregs_sm⟩ | ⟨_, _hoom⟩⟩ :=
      hwp_pre.elim hmem_act hL
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    clear hmem_act hwp_pre
    have hL_sm := hsteps1.codeLoaded hL
    have hfrozen_sm : img.FrozenLoaded sm := hfrozen.of_keepsFrozen hsteps1.keepsFrozen
    have hsym_sm : sm.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
    have hmf1 := Satisfies.mono (Entails.trans (sepConj_mono_left hent_pm)
      (Entails.of_eq (emp_sepConj _).symm)) hmf
    clear hmf hent_pm
    cases hrem_opt : st'.remoteIdentity with
    | some k =>
      rw [hrem_opt] at hx8_sm
      dsimp only [remoteIdentityTag] at hx8_sm
      simp only [wp_norm, arm64_norm] at hx29_sm hx27_sm hx26_sm hx22_sm hx8_sm
      have hwp_some : SepWP (tripleRatchetProgAtExt img.base ext) (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.keyReadyPC img) sm emp
          (fun sf Pf =>
            (Pf ⊢ emp) ∧
            sf.sp = sm.sp ∧ sf.spAligned = true ∧ sf.trace = sm.trace ∧
            sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x27 = x.ret ∧
            sf.readReg64 .x26 = sp + 0xa0#64 ∧ sf.readReg64 .x22 = sp + 0x294#64 ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0) := by
        have := libsignalSessionCode_fetch_fnAddr (b := img.base)
          (H := Rust.withPanics ext)
          (k := 0x1fc8) hfn (by decide) (ls_decode% messageDecryptPostSomeBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8136))
        unfold CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.keyReadyPC
        rw [hentry]
        dsimp only [tripleRatchetProgAtExt] at hpc_sm ⊢
        generalize (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry at *
        examples_hide_fetches
        wp_steps
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        exact ⟨Entails.refl _, rfl, hal_sm, rfl,
          by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hvregs_sm⟩
      obtain ⟨sf, hsteps2, ⟨hpc_sf, hrun_sf, Pf, hmf2, hent_pf,
        hsp_sf, hal_sf, htr_sf, hx29_sf, hx27_sf, hx26_sf, hx22_sf, hvregs_sf⟩ | ⟨_, _hoom⟩⟩ :=
        hwp_some.elim hmf1 hL_sm
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      clear hmf1 hwp_some
      have hfrozen_sf : img.FrozenLoaded sf := hfrozen_sm.of_keepsFrozen hsteps2.keepsFrozen
      have hsym_sf : sf.symtab = img.symtab := hsteps2.symtab_eq.trans hsym_sm
      have hmf3 := Satisfies.mono (sepConj_mono_left hent_pf) hmf2
      clear hmf2 hent_pf
      rw [emp_sepConj] at hmf3
      refine ⟨sf, hsteps1.trans hsteps2, Or.inl (Or.inl ?_)⟩
      let ses' : Session (List (BitVec 8)) :=
        { ses with state := st', pendingPreKey := none, pendingKyberPreKey := none }
      let rec' : SessionRecord (List (BitVec 8)) := { currentSession := some ses' }
      have hdec_rec : decryptRecord C S uuidTryParse x rec_ = .ok (pt, rec') :=
        decryptRecord_of_region_ok C S x prevPtr G ses rec_ pt st' hcur hmod_rg
      have hremBs_eq : remBs = k.publicKey.bytes.toList := hrem_eq k hrem_opt
      refine ⟨hpc_sf,
        ⟨hrun_sf, hsp_sf.trans (hsp_sm.trans hsp), hal0, hal_sf, hx29_sf, hx27_sf, hfrozen_sf, hsym_sf, hvregs_sf⟩,
        hx26_sf, hx22_sf, rec_, rec', pt, ses', k,
        hload, hscope, hdec_rec, rfl, hrem_opt,
        htr_sf.trans (htr_sm.trans htrace), ?_⟩
      have hbrec :
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
            sessionStateAt A (sp + 0x138#64) G' st' ⊢
          ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec' := by
        have hb := MessageDecrypt.Pf.RecordJoin.recordJoin_ok A (sp + 0x120#64) prevCap prevPtr G G' ses st' hw0 hrel
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hb
        exact hb
      have hcomb := segPostSome_ok_some_comb (img := img) (kit := kit) (ikit := ikit) (s0 := s0)
        (cap := cap) (ptr := ptr) (R' := R') hdraws hremBs_eq hbrec hvec_pt
      simpa only [R', sepConj_assoc] using Satisfies.mono hcomb hmf3
    | none =>
      rw [hrem_opt] at hx8_sm
      dsimp only [remoteIdentityTag] at hx8_sm
      simp only [wp_norm, arm64_norm] at hx8_sm
      have hwp_none : SepWP (tripleRatchetProgAtExt img.base ext)
          ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + bv% ((2^64 + ls_off% "core::option::expect_failed" - (ls_off% "libsignal_cli_ratchet::decrypt_signal")) % 2^64)) sm emp
          (fun sc Pc => (Pc ⊢ emp) ∧ sc.trace = sm.trace) := by
        have := libsignalSessionCode_fetch_fnAddr (b := img.base)
          (H := Rust.withPanics ext)
          (k := 0x1fc8) hfn (by decide) (ls_decode% messageDecryptPostSomeBinCli (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 8136))
        code_fetches_range CryptoVerification.libsignalSessionCode messageDecryptPostSomeBinCli img.base
          (Rust.withPanics ext) hfn (ls_off% "libsignal_cli_ratchet::decrypt_signal") 0x2560 0x18
        dsimp only [tripleRatchetProgAtExt] at hpc_sm ⊢
        generalize (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry at *
        examples_hide_fetches
        wp_steps
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        exact ⟨Entails.refl _, rfl⟩
      obtain ⟨sc, hsteps2, ⟨hpc_sc, hrun_sc, Pc, hmf2, hent_pc, htr_sc⟩ | ⟨_, _hoom⟩⟩ :=
        hwp_none.elim hmf1 hL_sm
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      clear hmf1 hwp_none
      have hmf3 := Satisfies.mono (sepConj_mono_left hent_pc) hmf2
      clear hmf2 hent_pc
      rw [emp_sepConj] at hmf3
      have hext : (tripleRatchetProgAtExt img.base ext).externAt? sc.pc = some Rust.panicked := by
        rw [hpc_sc]
        exact panic_at_expect_failed_msgDecrypt_ext img.base ext
      have hstep_pan : Step (tripleRatchetProgAtExt img.base ext) sc (Rust.panicked sc) :=
        Step.extern hrun_sc hext (Memory.KeepsFrozen.refl _) rfl
      refine ⟨Rust.panicked sc, hsteps1.trans (hsteps2.trans (Steps.step hstep_pan (Steps.refl _))),
        Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))⟩
      dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX, Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      have htr_pan : (Rust.panicked sc).trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession := by
        change sc.trace = _
        exact htr_sc.trans (htr_sm.trans htrace)
      have hload_pref :
          s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: (Rust.panicked sc).trace := by
        rw [htr_pan]
      have hs0_pref : s0.trace <+: (Rust.panicked sc).trace :=
        (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
      have hmod_pan : (x.model C S uuidTryParse ans).1 = .error .panic :=
        model_panic_of_remoteIdentity_none C S x prevPtr G ses ans rec_ pt st'
          hload hcur hmod_rg hrem_opt
      refine ⟨⟨hs0_pref, Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl hmod_pan⟩⟩, ?_⟩
      change sc.mem ⊨ anyHeap ∗ R
      dsimp only [R'] at hmf3
      simp only [← sepConj_assoc] at hmf3
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmf3

theorem segPostSomeVX_ok_ext4K {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hhyps : DecHypsExt4K img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hRemIk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.remoteIdentityKeyName)
      (Getters.remoteIdentityKeySpec A img))
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hPre : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x false R s0 s') :=
  segPostSomeVX_ok_of_loads_ext hhyps.loads hRemIk x ans R s0 s hPre

theorem segPostSomeVX_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hhyps : DecHypsExt img C A uuidTryParse S encRecord ext kit ikit st0 Scope)
    (hRemIk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.remoteIdentityKeyName)
      (Getters.remoteIdentityKeySpec A img))
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hPre : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x false R s0 s') :=
  segPostSomeVX_ok_of_loads_ext hhyps.loads hRemIk x ans R s0 s hPre

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
