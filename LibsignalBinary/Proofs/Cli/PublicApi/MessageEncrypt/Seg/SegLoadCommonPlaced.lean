/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadCommon
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Common.StringClonePlaced
public import ProofLib.SepLogic.WPp
public import ProofLib.SepLogic.WP.Apply
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import all Init.Data.String.Defs

/-!
# Relocatable CLI `SegLoad` Shared Infrastructure

Relocatable (`[LibsignalPlacement]`) `LibsignalCodeRoLoaded` / `SegExitPlaced` bridges, external
hook `subroutine_ok` lemmas on `lsProg_464 Hk`, `.rodata` vtable and `"message_encrypt"`
materialization, `SpeStaged` lemmas, and `loadPollPlacedOutAtS` decomposition.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  LibsignalCodeRoLoaded withLsCodeRoLoaded sepWP_seq_lscro sepWPp_seq_lscro
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. `LibsignalCodeRoLoaded` & `SepWPp` / `SegExitPlaced` Bridges -/

theorem messageEncrypt_of_sepWP_placed [LibsignalPlacement] {prog : Program}
    {ret mid : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_seq_lscro hcrl h

theorem messageEncrypt_call_panic_then_wp_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F)
        (fun sf' P_f => LibsignalCodeRoLoaded lsmpl sf'.mem → post sf' P_f))
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
    have hcrlm := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpc', hrun', P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ :=
      (hnext sm hpcm hrunm hspm hcsm).elim hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc', hrun', P_f, hmf, hq (hcrlm.of_keepsFrozen hsteps'.keepsFrozen)⟩⟩
    · exact (not_satisfies_false_sepConj _hoom).elim
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (hoom sm (F ∗ R') _hoom_st _hoom_post).elim

theorem messageEncrypt_call_panic_then_sepWPp_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R)))
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
    have hcrlm := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hcrlm R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (hoom sm (F ∗ R') _hoom_st _hoom_post).elim

theorem alloc_onPanic_placed_entails [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 s sf : State} {F : SepProp}
    (hpref0 : s0.trace <+: s.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf := by
  dsimp only [withStoresEncPlacedSpecV, withLsCodeRoLoaded]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  have halloc0 : allocFailedIn s0 sf := by
    unfold allocFailedIn at halloc ⊢
    rcases hpref0 with ⟨t1, ht1⟩
    have hlen : s.trace.length = s0.trace.length + t1.length := by
      rw [← ht1, List.length_append]
    rw [hlen, ← List.drop_drop] at halloc
    exact List.mem_of_mem_drop halloc
  exact Entails.pure_right ⟨hpref0.trans hpref, Or.inl halloc0⟩ (entails_anyHeap _)

theorem segExit_placed_of_sepWPp [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (lsProg_464 Hk) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 sf Out)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R))) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hcont⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · obtain ⟨sf, hsteps', hout'⟩ := hcont hmf (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem segExit_placed_done [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (h : Out s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s Out :=
  fun _ => ⟨s, .refl s, Or.inl h⟩

theorem segExit_placed_of_false [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (h : SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False)) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s Out :=
  Pf.SegFrom.SegExitPlaced.of_false h

theorem segExit_placed_of_sepWP_frozen [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {post : State → SepProp → Prop} {Out : State → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_464 Hk) target s P post)
    (hcont : ∀ sf P_f, sf.pc = target → sf.status = .Running → post sf P_f →
      LibsignalCodeRoLoaded lsmpl sf.mem → (sf.mem ⊨ P_f ∗ R) →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 sf Out) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_f, hmf, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout'⟩ :=
    hcont sm P_f hpcm hrunm hpost (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmf (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

/-! ## 2. External Hook & `futDrop` Address Lemmas on `lsProg_464 Hk` -/

theorem memcpy_placed_ok [LibsignalPlacement] {Scope Q C A}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl S encRecord Hk}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) (lsmpl.ρ "memcpy") framelessMemcpySpec :=
  ls_hook_ok_of_mem env.hooks.memcpy

theorem dealloc_placed_ok [LibsignalPlacement] {Scope Q C A}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl S encRecord Hk}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) (lsmpl.ρ lsRustDeallocSym) (rustDeallocSpec A) :=
  ls_hook_ok_of_mem env.hooks.dealloc

theorem stringClone_placed_ok [LibsignalPlacement] {Scope Q C A}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl S encRecord Hk}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) (lsmpl.base 623)
      (CryptoVerification.withLsCodeLoaded lsmpl (stringCloneSpec A)) :=
  LibsignalBinary.Proofs.Common.StringClonePlaced.stringClone_placed_codeLoaded_ok
    (callerProg := lsProg_464 Hk) (i := 464)
    env.hooks.shim env.hooks.alloc env.hooks.memcpy env.hooks.handleError

theorem loadFutDrop_placed_ne_zero {A : RustAlloc} (kit : SessionStoreSpec A 0#64) :
    (0#64 + kit.loadFutDropOff == 0#64) = false :=
  beq_false_of_ne (kit.loadFutDrop_ne_zero rfl)

/-! ## 3. `.rodata` Vtable & `"message_encrypt"` String Literal Lemmas -/

theorem loadVtablesPlaced_intro [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} (vt : SessionOnlyVtablesPlacedOk kit)
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ loadVtablesAt kit ∗ P := by
  unfold loadVtablesAt
  simp only [sepConj_assoc]
  exact vt.loadSlot hro (vt.loadFutDrop hro
    (vt.loadFutSize hro (vt.loadFutAlign hro
      (vt.loadFutPoll hro hP))))

theorem rodata_message_encrypt_placed_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.122") ↦ᵣ utf8 "message_encrypt") ∗ P :=
  CryptoVerification.lsro_slice_intro hro (off := 0) (BitVec.add_zero _).symm (by rfl_kernel) hP

/-! ## 4. Parametric `SpeStaged` Lemmas for `store ()` and `sessionNotFound` -/

theorem speStaged_storeErr_placed (A : RustAlloc) (ret strPtr vt w6 : BitVec 64) :
    SpeStaged A ret (.store ())
      [0x800000000000001A#64, strPtr, 10#64, 1#64, vt, w6]
      (strPtr ↦ᵣ storeHookStr) := by
  refine ⟨by decide, rfl, ?_⟩
  dsimp only [words64At, encErrAt, apiErrAt, strRefAt]
  have h10 : BitVec.ofNat 64 storeHookStr.length = 10#64 := by decide +kernel
  have hword : speWord speApplicationCallback = 0x800000000000001A#64 := rfl
  have ha1 : ret + 8#64 + 8#64 + 8#64 = ret + 8#64 + 0x10#64 := by bv_arith
  have ha2 : ret + 8#64 + 0x10#64 + 8#64 = ret + 8#64 + 0x18#64 := by bv_arith
  have ha3 : ret + 8#64 + 0x18#64 + 8#64 = ret + 8#64 + 0x20#64 := by bv_arith
  have ha4 : ret + 8#64 + 0x20#64 + 8#64 = ret + 8#64 + 0x28#64 := by bv_arith
  rw [ha1, ha2, ha3, ha4, sepConj_emp, hword]
  have hpull :
      (((ret + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
        ((ret + 8#64 + 8#64) ↦₆₄ strPtr) ∗
        ((ret + 8#64 + 0x10#64) ↦₆₄ 10#64) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ 1#64) ∗
        ((ret + 8#64 + 0x20#64) ↦₆₄ vt) ∗
        ((ret + 8#64 + 0x28#64) ↦₆₄ w6)) ∗
        (strPtr ↦ᵣ storeHookStr) =
      ((ret + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
        (((ret + 8#64 + 8#64) ↦₆₄ strPtr) ∗
          ((ret + 8#64 + 8#64 + 8#64) ↦₆₄ 10#64) ∗
          (strPtr ↦ᵣ storeHookStr)) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ 1#64) ∗
        ((ret + 8#64 + 0x20#64) ↦₆₄ vt) ∗
        ((ret + 8#64 + 0x28#64) ↦₆₄ w6) := by
    rw [ha1]
    sep_ac_rfl
  rw [hpull]
  refine sepConj_mono_right ?_
  refine sepConj_mono ?_ ?_
  · refine Entails.sepExists_right strPtr ?_
    rw [h10]
    exact Entails.of_eq (by sep_ac_rfl)
  refine sepConj_mono (Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))) ?_
  refine sepConj_mono (Entails.sepExists_right vt (Entails.refl _)) ?_
  exact pointsTo64_entails_memRegion _ _

theorem speStaged_sessionNotFound_devWord_placed (A : RustAlloc)
    (ret cap ptr w3 msgPtr : BitVec 64)
    (a : AddrVal) (hdev : DevWord a.device w3) :
    SpeStaged A ret (.sessionNotFound a "message_encrypt")
      [cap, ptr, BitVec.ofNat 64 a.name.length, w3, msgPtr, 15#64]
      (vecU8Buf A cap ptr a.name ∗ (msgPtr ↦ᵣ utf8 "message_encrypt")) := by
  refine ⟨by nofun, rfl, ?_⟩
  dsimp only [words64At, encErrAt, apiErrAt, addrCloneAt, strRefAt]
  have h15 : BitVec.ofNat 64 (utf8 "message_encrypt").length = 15#64 := by decide +kernel
  have ha1 : ret + 8#64 + 8#64 + 8#64 = ret + 8#64 + 0x10#64 := by bv_arith
  have ha2 : ret + 8#64 + 0x10#64 + 8#64 = ret + 8#64 + 0x18#64 := by bv_arith
  have ha3 : ret + 8#64 + 0x18#64 + 8#64 = ret + 8#64 + 0x20#64 := by bv_arith
  have ha4 : ret + 8#64 + 0x20#64 + 8#64 = ret + 8#64 + 0x28#64 := by bv_arith
  rw [ha1, ha2, ha3, ha4, sepConj_emp]
  have hvec :
      (((ret + 8#64) ↦₆₄ cap) ∗ ((ret + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((ret + 8#64 + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
        vecU8Buf A cap ptr a.name) ⊢ vecU8 A (ret + 8#64) a.name := by
    unfold vecU8
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h16 : ret + 8#64 + 16#64 = ret + 8#64 + 0x10#64 := rfl
    rw [h16]
    exact Entails.of_eq (by sep_ac_rfl)
  have hpull :
      (((ret + 8#64) ↦₆₄ cap) ∗
        ((ret + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((ret + 8#64 + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ w3) ∗
        ((ret + 8#64 + 0x20#64) ↦₆₄ msgPtr) ∗
        ((ret + 8#64 + 0x28#64) ↦₆₄ 15#64)) ∗
        (vecU8Buf A cap ptr a.name ∗ (msgPtr ↦ᵣ utf8 "message_encrypt")) =
      ((((ret + 8#64) ↦₆₄ cap) ∗ ((ret + 8#64 + 8#64) ↦₆₄ ptr) ∗
          ((ret + 8#64 + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
          vecU8Buf A cap ptr a.name) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ w3)) ∗
        (((ret + 8#64 + 0x20#64) ↦₆₄ msgPtr) ∗
          ((ret + 8#64 + 0x20#64 + 8#64) ↦₆₄ 15#64) ∗
          (msgPtr ↦ᵣ utf8 "message_encrypt")) := by
    rw [ha4]
    sep_ac_rfl
  rw [hpull]
  refine sepConj_mono ?_ ?_
  · refine Entails.trans (sepConj_mono hvec (pointsTo64_entails_dev_of_devWord _ hdev)) ?_
    have h19 : ret + 8#64 + 0x18#64 + 1#64 = ret + 8#64 + 0x19#64 := by bv_arith
    rw [h19]
    exact Entails.of_eq (by sep_ac_rfl)
  · refine Entails.sepExists_right msgPtr ?_
    rw [h15]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 5. Parametric Decomposition of `loadPollPlacedOutAtS` -/

/-- Residual fact after extracting the 7 header words and 312-B tail from `loadPollPlacedOutAtS`. -/
def LoadOutResPlaced (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) : SepProp :=
  match ans with
  | .error () =>
    ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
      ⌜w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1 = 0x800000000000001A#64 ∧
        w2 = strPtr ∧ w3 = 10#64 ∧ w4 = 1#64 ∧ w5 = vt⌝ ∗
        (strPtr ↦ᵣ storeHookStr)
  | .ok none =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝
  | .ok (some r) =>
    ∃∗ g : RecordGhost,
      ⌜Scope r ∧ g.prevCap.toNat < 2 ^ 63 ∧
        w0 = g.prevCap ∧ w1 = g.prevPtr ∧ w2 = 0#64 ∧ w3 = recordCurCap g ∧
        RecordTailInline g r w4 w5 w6 tail⌝ ∗
        recordHeap A g r

theorem loadPollPlacedOutAtS_decompose (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (out : BitVec 64)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8))))) :
    loadPollPlacedOutAtS Scope A out ans ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFD#64 ∧ tail.length = 312⌝ ∗
        (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
        ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₁₂₈ (w5 ++ w4)) ∗
        ((out + 0x30#64) ↦₆₄ w6) ∗ ((out + 0x38#64) ↦ₛ tail) ∗
        LoadOutResPlaced Scope A ans w0 w1 w2 w3 w4 w5 w6 tail := by
  rcases ans with ⟨⟩ | _ | r
  · dsimp only [loadPollPlacedOutAtS, LoadOutResPlaced]
    apply Entails.sepExists_elim; intro strPtr
    apply Entails.sepExists_elim; intro vt
    rw [memRegion_split (out + 0x30#64) 8 312 (by decide),
        ProofLib.memRegion_eight (out + 0x30#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [memRegion_eq_exists_bytes (out + 0x38#64) 312 (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro tail
    apply Entails.sepExists_elim; intro w6
    have hpull_err :
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
          ((out + 0x10#64) ↦₆₄ strPtr) ∗
          ((out + 0x18#64) ↦₆₄ 10#64) ∗
          ((out + 0x20#64) ↦₆₄ 1#64) ∗
          ((out + 0x28#64) ↦₆₄ vt) ∗
          (strPtr ↦ᵣ storeHookStr) ∗
          (((out + 0x30#64) ↦₆₄ w6) ∗ (⌜tail.length = 312⌝ ∗ ((out + 0x38#64) ↦ₛ tail))) =
        ⌜tail.length = 312⌝ ∗
          ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
            ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
            ((out + 0x10#64) ↦₆₄ strPtr) ∗
            ((out + 0x18#64) ↦₆₄ 10#64) ∗
            (((out + 0x20#64) ↦₆₄ 1#64) ∗
              ((out + 0x28#64) ↦₆₄ vt) ∗
              ((out + 0x30#64) ↦₆₄ w6)) ∗
            ((out + 0x38#64) ↦ₛ tail) ∗
            (strPtr ↦ᵣ storeHookStr)) := by sep_ac_rfl
    rw [hpull_err]
    apply Entails.pure_left; intro htail
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64
      (Entails.sepExists_right 0x800000000000001A#64
      (Entails.sepExists_right strPtr
      (Entails.sepExists_right 10#64
      (Entails.sepExists_right 1#64
      (Entails.sepExists_right vt
      (Entails.sepExists_right w6
      (Entails.sepExists_right tail ?_)))))))
    rw [words3_repack_q128_w64 out 1#64 vt w6]
    refine Entails.sepExists_right strPtr (Entails.sepExists_right vt ?_)
    apply Entails.pure_right ⟨by decide, htail⟩
    have hpull_err2 :
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
          ((out + 0x10#64) ↦₆₄ strPtr) ∗
          ((out + 0x18#64) ↦₆₄ 10#64) ∗
          (((out + 0x20#64) ↦₁₂₈ (vt ++ 1#64)) ∗
            ((out + 0x30#64) ↦₆₄ w6)) ∗
          ((out + 0x38#64) ↦ₛ tail) ∗
          (strPtr ↦ᵣ storeHookStr) =
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
          ((out + 0x10#64) ↦₆₄ strPtr) ∗
          ((out + 0x18#64) ↦₆₄ 10#64) ∗
          ((out + 0x20#64) ↦₁₂₈ (vt ++ 1#64)) ∗
          ((out + 0x30#64) ↦₆₄ w6) ∗
          ((out + 0x38#64) ↦ₛ tail) ∗
          (strPtr ↦ᵣ storeHookStr) := by sep_ac_rfl
    rw [hpull_err2]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))))))
    exact Entails.pure_right ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (Entails.refl _)
  · exact loadPollOutAtS_decompose Scope A 0#64 out (.ok none)
  · exact loadPollOutAtS_decompose Scope A 0#64 out (.ok (some r))

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
