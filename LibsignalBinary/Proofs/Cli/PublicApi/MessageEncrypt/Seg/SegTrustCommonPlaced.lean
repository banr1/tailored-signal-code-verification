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
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommon
public import LibsignalBinary.Proofs.Common.StringClonePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import all Init.Data.String.Defs

/-!
# Relocatable Shared Helpers for `segTrust`, `segSave`, and `segApplyStore`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. `SegExitPlaced` Combinators & Allocation Panic Bridge -/

export CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
  (SegExitPlaced.next SegExitPlaced.of_false SegExitPlaced.of_sepWP SegExitPlaced.call)

theorem SegExitPlaced.step_left [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s sm : State} {next : State → Prop}
    (hsteps : Steps (lsProg_464 Hk) s sm)
    (h : SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 sm next) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps', hout⟩ := h (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem alloc_onPanic_entails_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 s sf : State} {F R R0 : SepProp}
    (hpref0 : s0.trace <+: s.trace)
    (hR : R ⊢ anyHeap ∗ R0) :
    ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R ⊢
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0 := by
  refine Entails.trans (sepConj_mono_right hR) ?_
  dsimp only [withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded]
  have hreord :
      ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ (anyHeap ∗ R0) =
      ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ ((anyHeap ∗ F ∗ anyHeap) ∗ R0) := by ac_rfl
  rw [hreord]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  have halloc0 := allocFailedIn_trans hpref0 halloc
  exact sepConj_mono_left (Entails.pure_right ⟨hpref0.trans hpref, Or.inl halloc0⟩ (entails_anyHeap _))

/-! ## 2. External Hook Lemmas on `lsProg_464 Hk` -/

theorem dealloc_placed_ok_at_enc [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) (lsρ lsRustDeallocSym) (rustDeallocSpec A) := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem (by decide : lsRustDeallocSym ∈ libsignalSessionExterns)
  exact ls_hook_ok (k := k) (by simp [hk, hget]) env.hooks.dealloc

theorem stringClone_placed_ok_at_enc [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) (lsmpl.base 623)
      (StoreKit.withLsRoCl lsmpl (stringCloneSpec A)) :=
  StoreKit.ls_subroutine_ok_rocl_of_plain
    (LibsignalBinary.Proofs.Common.StringClonePlaced.stringClone_blk623_ok
      env.hooks.shim env.hooks.alloc env.hooks.memcpy env.hooks.handleError)

/-! ## 3. Placed `.rodata` Vtable & Store-Hook Error Lemmas -/

theorem trustVtablesAt_placed_intro [LibsignalPlacement] {A : RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} (hvt : IdentityVtablesPlacedOk ikit)
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ trustVtablesAt ikit ∗ P := by
  unfold trustVtablesAt
  simp only [sepConj_assoc]
  exact hvt.trustSlot hro (hvt.trustFutDrop hro
    (hvt.trustFutSize hro (hvt.trustFutAlign hro
      (hvt.trustFutPoll hro hP))))

theorem saveVtablesAt_placed_intro [LibsignalPlacement] {A : RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} (hvt : IdentityVtablesPlacedOk ikit)
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ saveVtablesAt ikit ∗ P := by
  unfold saveVtablesAt
  simp only [sepConj_assoc]
  exact hvt.saveSlot hro (hvt.saveFutDrop hro
    (hvt.saveFutSize hro (hvt.saveFutAlign hro
      (hvt.saveFutPoll hro hP))))

theorem storeVtablesAt_placed_intro [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} (hvt : SessionOnlyVtablesPlacedOk kit)
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ storeVtablesAt kit ∗ P := by
  unfold storeVtablesAt
  simp only [sepConj_assoc]
  exact hvt.storeSlot hro (hvt.storeFutDrop hro
    (hvt.storeFutSize hro (hvt.storeFutAlign hro
      (hvt.storeFutPoll hro hP))))

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
    ac_rfl
  rw [hpull]
  refine sepConj_mono_right ?_
  refine sepConj_mono ?_ ?_
  · refine Entails.sepExists_right strPtr ?_
    rw [h10]
    exact Entails.of_eq (by ac_rfl)
  refine sepConj_mono (Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))) ?_
  refine sepConj_mono (Entails.sepExists_right vt (Entails.refl _)) ?_
  exact pointsTo64_entails_memRegion _ _

/-! ## 4. Placed Call Wrappers (`call_nopanic_placed`, `call_alloc_placed`, `call_rocl_alloc_placed`) -/

theorem call_nopanic_placed {α : Type} [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_464 Hk) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (lsProg_464 Hk) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 sm next)
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  refine SegExitPlaced.call hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by
      rw [hpanic, sepConj_assoc] at h
      exact (not_satisfies_false_sepConj h).elim)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp hspm) hcsm hpost

theorem call_alloc_placed {α : Type} [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_464 Hk) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpref0 : s0.trace <+: s.trace)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (lsProg_464 Hk) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 sm next)
    (hR : R ⊢ anyHeap ∗ R0 := by exact sepConj_mono_left (entails_anyHeap _))
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  refine SegExitPlaced.call hcall xc hpc hrun hsp hlr hm
    (fun sf code R' _ h => by rw [hexit] at h; exact not_satisfies_false_sepConj h)
    (fun sf _ _ h => by
      rw [hpanic] at h
      exact Satisfies.mono (alloc_onPanic_entails_placed hpref0 hR) h)
    (fun sm _ hsteps hpcm hrunm hspm hcsm hpost => ?_)
    (fun sf R' _ h => by rw [hoom] at h; exact not_satisfies_false_sepConj h)
  rw [sepConj_assoc] at hpost
  exact hnext sm hsteps hpcm hrunm hspm (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp hspm) hcsm hpost

theorem call_rocl_alloc_placed {α : Type} [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_464 Hk) entry (StoreKit.withLsRoCl lsmpl spec))
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpref0 : s0.trace <+: s.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (lsProg_464 Hk) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 sm next)
    (hR : R ⊢ anyHeap ∗ R0 := by exact sepConj_mono_left (entails_anyHeap _))
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  have hm_rocl : s.mem ⊨ (StoreKit.withLsRoCl lsmpl spec).pre xc s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hm⟩
  refine call_alloc_placed hcall xc hpc hrun hsp hlr hpref0 hm_rocl
    (fun sm hsteps hpcm hrunm hspm hsp_alm hcsm hpost => ?_)
    (hR := hR) (hexit := hexit) (hpanic := hpanic) (hoom := hoom)
  dsimp only [StoreKit.withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hpost.1 hpost.2

theorem call_rocl_nopanic_placed {α : Type} [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_464 Hk) entry (StoreKit.withLsRoCl lsmpl spec))
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hnext : ∀ sm : State,
      Steps (lsProg_464 Hk) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      (sm.mem ⊨ spec.post xc s sm ∗ (F ∗ R)) →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 sm next)
    (hexit : ∀ code sf, spec.onExit xc code s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic xc s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom xc s sf = ⌜False⌝ := by intros; rfl) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  have hm_rocl : s.mem ⊨ (StoreKit.withLsRoCl lsmpl spec).pre xc s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hm⟩
  refine call_nopanic_placed (R0 := R0) hcall xc hpc hrun hsp hlr hm_rocl
    (fun sm hsteps hpcm hrunm hspm hsp_alm hcsm hpost => ?_)
    (hexit := hexit) (hpanic := hpanic) (hoom := hoom)
  dsimp only [StoreKit.withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hpost.2

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
