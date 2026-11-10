/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegDispatchAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.SessionOnlyKitEPlaced
public import LibsignalBinary.Proofs.Common.StringClonePlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BridgeReloc
import all Init.Data.String.Defs

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoGames
open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch hiding apiDecResultAt_store_placed_of_words stagedRes_store_err_placed apiDecResultAt_sessionNotFound_placed_of_words stagedRes_sessionNotFound_placed messageDecrypt_of_sepWP_lscro messageDecrypt_of_sepWP_done_lscro messageDecrypt_call_panic_then_wp_lscro decSeg_of_sepWP_mid_placed decSeg_of_sepWP_done_placed decSeg_of_sepWPp_placed msgDecryptStrSym satisfies_rodata_msgDecryptStr_placed ls_hook_ok_197 stringClone_placed_ok msgDecrypt_memcpy_placed_ok msgDecrypt_dealloc_placed_ok stringClone_onPanic_entails_placed loadPollPlacedOutAt_err_entails loadPollPlacedOutAt_none_entails loadPollPlacedOutAt_some_entails loadPollBranchRestPlaced loadPollPlacedOutAt_entails_common

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


open CryptoVerification

theorem apiDecResultAt_store_placed_of_words (A : RustAlloc) (strPtr vt w6 r : BitVec 64) :
    ((r ↦₆₄ 0x800000000000001A#64) ∗ ((r + 8#64) ↦₆₄ strPtr) ∗
      ((r + 0x10#64) ↦₆₄ 10#64) ∗ ((r + 0x18#64) ↦₆₄ 1#64) ∗
      ((r + 0x20#64) ↦₆₄ vt) ∗ ((r + 0x28#64) ↦₆₄ w6) ∗
      (strPtr ↦ᵣ storeHookStr)) ⊢
      apiDecResultAt A r (.error (.store ())) := by
  dsimp only [apiDecResultAt, apiErrAt]
  have hspe : speWord speApplicationCallback = 0x800000000000001A#64 := rfl
  have hstr : (((r + 8#64) ↦₆₄ strPtr) ∗
      ((r + 0x10#64) ↦₆₄ 10#64) ∗ (strPtr ↦ᵣ storeHookStr)) ⊢
      strRefAt (r + 8#64) storeHookStr := by
    have hlen : BitVec.ofNat 64 storeHookStr.length = 10#64 := by rfl_kernel
    have h10 : r + 8#64 + 8#64 = r + 0x10#64 := by bv_arith
    have h := strRefAt_intro (r + 8#64) strPtr storeHookStr
    rwa [hlen, h10] at h
  have hd : ((r + 0x18#64) ↦₆₄ 1#64) ⊢ ∃∗ d : BitVec 64, ⌜d ≠ 0⌝ ∗ ((r + 0x18#64) ↦₆₄ d) :=
    Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))
  have hvt : ((r + 0x20#64) ↦₆₄ vt) ⊢ ∃∗ vt' : BitVec 64, ((r + 0x20#64) ↦₆₄ vt') :=
    Entails.sepExists_right vt (Entails.refl _)
  have hm8 : ((r + 0x28#64) ↦₆₄ w6) ⊢ memRegion (r + 0x28#64) 8 := by
    rw [ProofLib.memRegion_eight]
    exact Entails.sepExists_right w6 (Entails.refl _)
  rw [hspe]
  have hreord :
      ((r ↦₆₄ 0x800000000000001A#64) ∗ ((r + 8#64) ↦₆₄ strPtr) ∗
        ((r + 0x10#64) ↦₆₄ 10#64) ∗ ((r + 0x18#64) ↦₆₄ 1#64) ∗
        ((r + 0x20#64) ↦₆₄ vt) ∗ ((r + 0x28#64) ↦₆₄ w6) ∗
        (strPtr ↦ᵣ storeHookStr)) =
      ((r ↦₆₄ 0x800000000000001A#64) ∗
        (((r + 8#64) ↦₆₄ strPtr) ∗ ((r + 0x10#64) ↦₆₄ 10#64) ∗ (strPtr ↦ᵣ storeHookStr)) ∗
        ((r + 0x18#64) ↦₆₄ 1#64) ∗ ((r + 0x20#64) ↦₆₄ vt) ∗
        ((r + 0x28#64) ↦₆₄ w6)) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono hstr (sepConj_mono hd (sepConj_mono hvt hm8)))

theorem stagedRes_store_err_placed (A : RustAlloc) (src strPtr vt w6 : BitVec 64) :
    (((src ↦₁₂₈ q0OfWords strPtr 10#64 1#64) ∗
      ((src + 0x10#64) ↦₁₂₈ q1OfWords 1#64 vt w6) ∗
      ((src + 0x20#64) ↦₃₂ w6.extractLsb' 32 32)) ∗
      (strPtr ↦ᵣ storeHookStr)) ⊢
      StagedRes A 0x800000000000001A#64
        (BitVec.zeroExtend 64
          (BitVec.truncate 32 (BitVec.zeroExtend 64 (strPtr.extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 (strPtr.extractLsb' 0 32))
        src (.error (.store ())) :=
  stagedRes_of_words5 A src 0x800000000000001A#64 strPtr 10#64 1#64
    vt w6 (strPtr ↦ᵣ storeHookStr) (.error (.store ()))
    (apiDecResultAt_store_placed_of_words A strPtr vt w6)

theorem apiDecResultAt_sessionNotFound_placed_of_words (A : RustAlloc) (a : AddrVal)
    (cap ptr strPtr w4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : a.device :: pad = unpack64 w4) (r : BitVec 64) :
    ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
      ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
      ((r + 0x18#64) ↦₆₄ w4) ∗
      ((r + 0x20#64) ↦₆₄ strPtr) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
      (vecU8Buf A cap ptr a.name ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal"))) ⊢
      apiDecResultAt A r (.error (.sessionNotFound a "message_decrypt_signal")) := by
  dsimp only [apiDecResultAt, apiErrAt, addrCloneAt]
  have hvec := vecU8_intro A r cap ptr a.name
  have hw4_ent := pointsTo64_entails_byte_memRegion7 (r + 0x18#64) a.device pad w4 hpad hw4
  have h19 : r + 0x18#64 + 1#64 = r + 0x19#64 := by bv_arith
  rw [h19] at hw4_ent
  have hstr : (((r + 0x20#64) ↦₆₄ strPtr) ∗
      ((r + 0x28#64) ↦₆₄ 22#64) ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal")) ⊢
      strRefAt (r + 0x20#64) (utf8 "message_decrypt_signal") := by
    have hlen : BitVec.ofNat 64 (utf8 "message_decrypt_signal").length = 22#64 := by rfl_kernel
    have h28 : r + 0x20#64 + 8#64 = r + 0x28#64 := by bv_arith
    have h := strRefAt_intro (r + 0x20#64) strPtr (utf8 "message_decrypt_signal")
    rwa [hlen, h28] at h
  have hreord :
      ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
        ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
        ((r + 0x18#64) ↦₆₄ w4) ∗
        ((r + 0x20#64) ↦₆₄ strPtr) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
        (vecU8Buf A cap ptr a.name ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal"))) =
      ((((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
          ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
          vecU8Buf A cap ptr a.name) ∗
        ((r + 0x18#64) ↦₆₄ w4)) ∗
        (((r + 0x20#64) ↦₆₄ strPtr) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
          (strPtr ↦ᵣ utf8 "message_decrypt_signal"))) := by ac_rfl
  rw [hreord]
  exact sepConj_mono (sepConj_mono hvec hw4_ent) hstr

theorem stagedRes_sessionNotFound_placed (A : RustAlloc) (src : BitVec 64) (a : AddrVal)
    (cap ptr strPtr w4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : a.device :: pad = unpack64 w4) :
    (((src ↦₁₂₈ q0OfWords ptr (BitVec.ofNat 64 a.name.length) w4) ∗
      ((src + 0x10#64) ↦₁₂₈ q1OfWords w4 strPtr 22#64) ∗
      ((src + 0x20#64) ↦₃₂ 0#32)) ∗
      (vecU8Buf A cap ptr a.name ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal"))) ⊢
      StagedRes A cap
        (BitVec.zeroExtend 64
          (BitVec.truncate 32 (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32))
        src (.error (.sessionNotFound a "message_decrypt_signal")) := by
  have h22 : (22#64 : BitVec 64).extractLsb' 32 32 = 0#32 := rfl
  rw [← h22]
  exact stagedRes_of_words5 A src cap ptr (BitVec.ofNat 64 a.name.length) w4
    strPtr 22#64
    (vecU8Buf A cap ptr a.name ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal"))
    (.error (.sessionNotFound a "message_decrypt_signal"))
    (apiDecResultAt_sessionNotFound_placed_of_words A a cap ptr strPtr w4 pad hpad hw4)

theorem messageDecrypt_of_sepWP_lscro [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem messageDecrypt_of_sepWP_done_lscro [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog ret s P (fun sf P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem → Q sf P_f)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hq (hcrl.of_keepsFrozen hsteps.keepsFrozen)⟩⟩

theorem messageDecrypt_call_panic_then_wp_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F)
        (fun sf' P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf'.mem → post sf' P_f))
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun (hpre R' hm) hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hcrl_m := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpc', hrun', P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ :=
      (hnext sm hpcm hrunm hspm hcsm).elim hpost (hsteps.codeLoaded hL)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc', hrun', P_f, hmf, hq (hcrl_m.of_keepsFrozen hsteps'.keepsFrozen)⟩⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (hoom sm (F ∗ R') _hoom_st _hoom_post).elim

theorem decSeg_of_sepWP_mid_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : String → Option (State → State)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {mid : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_463 H) mid s P
      (fun sm Pm => StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → (sm.mem ⊨ Pm ∗ R) →
        DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 sm Out)) :
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem decSeg_of_sepWP_done_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : String → Option (State → State)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_463 H) target s P
      (fun sf P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem → (sf.mem ⊨ P_f ∗ R) → Out sf)) :
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_, _, P_f, hmf, hOut⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl (hOut (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmf)⟩

theorem decSeg_of_sepWPp_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : String → Option (State → State)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (lsProg_463 H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresDecPlacedSpecV C A ctl parse S encRecord kit ikit st0 ist0 Scope).onPanic x s0 sf ∗ R))) :
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

abbrev msgDecryptStrSym : String :=
  "libsignal_cli_ratchet:.rodata..Lanon.125"

theorem satisfies_rodata_msgDecryptStr_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : CryptoVerification.LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ msgDecryptStrSym) ↦ᵣ utf8 "message_decrypt_signal") ∗ P :=
  CryptoVerification.lsro_slice_intro hro (off := 0) (BitVec.add_zero _).symm (by rfl_kernel) hP

theorem ls_hook_ok_463 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hmem : sym ∈ libsignalSessionExterns := by decide) (h : HookSat H sym spec) :
    subroutine_ok (lsProg_463 H) (lsmpl.ρ sym) spec := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact CryptoVerification.ls_hook_ok (prog := lsProg_463 H) (i := 463) (k := k)
    (by rw [List.getElem?_eq_getElem hlt, hk]) h

theorem stringClone_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : PublicApiDecHooksPlaced A H) :
    subroutine_ok (lsProg_463 H) (lsmpl.base 623)
      (CryptoVerification.withLsCodeLoaded lsmpl (stringCloneSpec A)) :=
  LibsignalBinary.Proofs.Common.StringClonePlaced.stringClone_placed_codeLoaded_ok
    (callerProg := lsProg_463 H) (i := 463)
    hH.shim hH.alloc hH.memcpy hH.handleError

theorem msgDecrypt_memcpy_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hM : HookSat H "memcpy" sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_463 H) (lsmpl.ρ "memcpy") framelessMemcpySpec :=
  ls_hook_ok_463 (by decide) hM

theorem msgDecrypt_dealloc_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hD : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_463 H) (lsmpl.ρ lsRustDeallocSym) (rustDeallocSpec A) :=
  ls_hook_ok_463 (by decide) hD

theorem stringClone_onPanic_entails_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {s0 s sf : State} {F : SepProp}
    (h0s : s0.trace <+: s.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).onPanic x s0 sf := by
  dsimp only [withStoresDecPlacedSpecV]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  exact Entails.pure_right ⟨h0s.trans hpref, Or.inl (allocFailedIn_trans' h0s halloc)⟩
    (entails_anyHeap _)

theorem loadPollPlacedOutAt_err_entails {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (sp : BitVec 64) :
    StoreKit.loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) (.error ()) ⊢
      ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜tail.length = 312⌝ ∗
        recordWords56At (sp + 0x5f0#64) 0xFFFFFFFFFFFFFFFE#64 0x800000000000001A#64
          strPtr 10#64 1#64 vt w6 ∗
        (strPtr ↦ᵣ storeHookStr) ∗
        ((sp + 0x628#64) ↦ₛ tail) := by
  dsimp only [StoreKit.loadPollPlacedOutAtS]
  apply Entails.sepExists_elim; intro strPtr
  apply Entails.sepExists_elim; intro vt
  rw [memRegion_split (sp + 0x5f0#64 + 0x30#64) 8 312 (by decide),
      ProofLib.memRegion_eight,
      memRegion_eq_exists_bytes (sp + 0x5f0#64 + 0x30#64 + 8#64) 312 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tail
  apply Entails.sepExists_elim; intro w6
  refine Entails.sepExists_right strPtr (Entails.sepExists_right vt
    (Entails.sepExists_right w6 (Entails.sepExists_right tail ?_)))
  unfold recordWords56At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem loadPollPlacedOutAt_none_entails {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (sp : BitVec 64) :
    StoreKit.loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) (.ok none) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜tail.length = 312⌝ ∗
        recordWords56At (sp + 0x5f0#64) 0xFFFFFFFFFFFFFFFF#64 w1 w2 w3 w4 w5 w6 ∗
        ((sp + 0x628#64) ↦ₛ tail) :=
  loadPollOutAt_none_entails (Scope := Scope) A 0#64 sp

theorem loadPollPlacedOutAt_some_entails (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (sp : BitVec 64) (rec : SessionRecord (List (BitVec 8))) :
    StoreKit.loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) (.ok (some rec)) ⊢
      ∃∗ g : RecordGhost, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜Scope rec ∧ RecordTailInline g rec w4 w5 w6 tail ∧ g.prevCap.toNat < 2 ^ 63⌝ ∗
        recordWords56At (sp + 0x5f0#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
        ((sp + 0x628#64) ↦ₛ tail) ∗ recordHeap A g rec :=
  loadPollOutAt_some_entails Scope A 0#64 sp rec

def loadPollBranchRestPlaced (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    Except Unit (Option (SessionRecord (List (BitVec 8)))) → SepProp
  | .error () =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1 = 0x800000000000001A#64 ∧
      w3 = 10#64 ∧ w4 = 1#64⌝ ∗
      (w2 ↦ᵣ storeHookStr)
  | .ok none =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝
  | .ok (some rec) =>
    ∃∗ g : RecordGhost,
      ⌜Scope rec ∧ RecordTailInline g rec w4 w5 w6 tail ∧
        g.prevCap.toNat < 2 ^ 63 ∧
        w0 = g.prevCap ∧ w1 = g.prevPtr ∧ w2 = 0#64 ∧ w3 = recordCurCap g⌝ ∗
      recordHeap A g rec

theorem loadPollPlacedOutAt_entails_common (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (sp : BitVec 64)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8))))) :
    StoreKit.loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) ans ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFD#64 ∧ tail.length = 312⌝ ∗
        ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x604#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) ∗
        loadPollBranchRestPlaced Scope A w0 w1 w2 w3 w4 w5 w6 tail ans ∗
        ((sp + 0x628#64) ↦ₛ tail) := by
  have hrep : ∀ w0 w1 w2 w3 w4 w5 w6 : BitVec 64,
      recordWords56At (sp + 0x5f0#64) w0 w1 w2 w3 w4 w5 w6 =
        ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x604#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) := by
    intro w0 w1 w2 w3 w4 w5 w6
    rw [recordWords56At_repack]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rcases ans with ⟨⟨⟩⟩ | (_ | rec)
  · refine Entails.trans (loadPollPlacedOutAt_err_entails A sp) ?_
    apply Entails.sepExists_elim; intro strPtr
    apply Entails.sepExists_elim; intro vt
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; intro htail
    rw [hrep]
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64
      (Entails.sepExists_right 0x800000000000001A#64
        (Entails.sepExists_right strPtr
          (Entails.sepExists_right 10#64
            (Entails.sepExists_right 1#64
              (Entails.sepExists_right vt
                (Entails.sepExists_right w6
                  (Entails.sepExists_right tail ?_)))))))
    dsimp only [loadPollBranchRestPlaced]
    apply Entails.pure_right ⟨by decide, htail⟩
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
    exact Entails.pure_right (by trivial) (Entails.refl _)
  · refine Entails.trans (loadPollPlacedOutAt_none_entails A sp) ?_
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; intro htail
    rw [hrep]
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFF#64
      (Entails.sepExists_right w1
        (Entails.sepExists_right w2
          (Entails.sepExists_right w3
             (Entails.sepExists_right w4
              (Entails.sepExists_right w5
                (Entails.sepExists_right w6
                  (Entails.sepExists_right tail ?_)))))))
    change _ ⊢ ⌜_⌝ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ ⌜_⌝ ∗ _
    apply Entails.pure_right ⟨by decide, htail⟩
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
    exact Entails.pure_right (by trivial) (Entails.refl _)
  · refine Entails.trans (loadPollPlacedOutAt_some_entails Scope A sp rec) ?_
    apply Entails.sepExists_elim; intro g
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; rintro ⟨hscope, htail_inl, hlt⟩
    have hne := (ne_neg_tags_of_lt_two_pow_63 hlt).2.2
    rw [hrep]
    refine Entails.sepExists_right g.prevCap
      (Entails.sepExists_right g.prevPtr
        (Entails.sepExists_right 0#64
          (Entails.sepExists_right (recordCurCap g)
            (Entails.sepExists_right w4
              (Entails.sepExists_right w5
                (Entails.sepExists_right w6
                  (Entails.sepExists_right tail ?_)))))))
    change _ ⊢ ⌜_⌝ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ (∃∗ g', ⌜_⌝ ∗ _) ∗ _
    apply Entails.pure_right ⟨hne, htail_inl.1⟩
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
    rw [sepConj_comm ((sp + 0x628#64) ↦ₛ tail) (recordHeap A g rec)]
    refine sepConj_mono_left (Entails.sepExists_right g ?_)
    exact Entails.pure_right ⟨hscope, htail_inl, hlt, by trivial⟩ (Entails.refl _)


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch
