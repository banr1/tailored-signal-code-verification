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
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
public import LibsignalBinary.Proofs.Common.StringClonePlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BridgeReloc
import all Init.Data.String.Defs

/-!
# Relocatable Shared Helpers for `segPreKey`

Provides external hook `subroutine_ok` lemmas on Block `464` (`lsProg_464 Hk`), `.rodata` framing
for `"message_encrypt"`, `SegExitPlaced` combinators, and panic/model bridges under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
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
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. External Hook `subroutine_ok` Lemmas on Block `464` (`lsProg_464 Hk`) -/

theorem timeAdd_placed_ok_at_enc [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) (lsρ lsTimeAddSym)
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet timeAddSpec) :=
  ls_hook_ok_of_mem env.hooks.timeAdd

theorem durationSince_placed_ok_at_enc [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) (lsρ lsDurationSinceSym)
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet
        durationSinceBoundedSpec) :=
  ls_hook_ok_of_mem env.hooks.durationSince

theorem stringClone_placed_ok_at_enc [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk) :
    subroutine_ok (lsProg_464 Hk) (lsmpl.base 623)
      (StoreKit.withLsRoCl lsmpl (stringCloneSpec A)) :=
  StoreKit.ls_subroutine_ok_rocl_of_plain
    (LibsignalBinary.Proofs.Common.StringClonePlaced.stringClone_blk623_ok
      env.hooks.shim env.hooks.alloc env.hooks.memcpy env.hooks.handleError)

/-! ## 2. `.rodata` Literal `"message_encrypt"` (`"signal_session_ratchet:.rodata..Lanon.122"`, 15 bytes) -/

abbrev lsMessageEncryptRodataSym : String := "libsignal_cli_ratchet:.rodata..Lanon.122"

theorem blkPl_198_ρ_lanon122 [LibsignalPlacement] :
    (blkPl_464).ρ lsMessageEncryptRodataSym = lsmpl.ρ lsMessageEncryptRodataSym := by
  dsimp only [blkPl_464, Obj.MultiPlacedLib.blockPlacement]
  exact ls_resolve_data (by decide +kernel)

theorem rodata_message_encrypt_placed_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt") ∗ P :=
  CryptoVerification.lsro_slice_intro hro (off := 0) (BitVec.add_zero _).symm (by rfl_kernel) hP

theorem rodata_message_encrypt_placed_sepWPp [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s
      (((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt") ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact rodata_message_encrypt_placed_intro hro hm

/-! ## 3. `SepWPp` Call Helper for `StoreKit.withLsRoCl` & `SegExitPlaced` Combinators -/

theorem SepWPp.call_frame_rocl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (StoreKit.withLsRoCl lsmpl spec))
    {x : α} {s : State} {φ : Prop} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpre_eq : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hf : P = T ∗ F)
    (hexit : ∀ code sf R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ (F ∗ R')) → False)
    (hpan : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  intro R' hm hL
  have hpre : s.mem ⊨ (StoreKit.withLsRoCl lsmpl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj]
    rw [hf, sepConj_assoc] at hm
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun hpre hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, hex_st, hpost⟩ | ⟨hoom_st, hpost⟩
  · dsimp only [StoreKit.withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hcrl_sm, hpost⟩
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hcrl_sm R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [StoreKit.withLsRoCl] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, hpan sm hpan_st⟩)⟩
  · exact (hexit code sm R' hex_st hpost).elim
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom_st, hoom sm R' hoom_st hpost⟩)⟩

theorem segExitPlaced_trans [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s mid)
    (h2 : ∀ sm, mid sm → SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 sm next) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem onPanicPlaced_absorb_extra [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 sf : State} {R0 : SepProp}
    (h : sf.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗
      (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0)) :
    sf.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0 := by
  dsimp only [withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [← sepConj_assoc] at h
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) h.2

theorem segExitPlaced_of_sepWPp_lscro [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {next : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hm : s.mem ⊨ P ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0))
    (hwp : SepWPp (lsProg_464 Hk) target s P
      (fun sf P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        (sf.mem ⊨ P_f ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0)) → next sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0)) →
        (sf.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗
          (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0)))) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, onPanicPlaced_absorb_extra (hqp hmf)⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

/-! ## 4. Relocatable Panic & Model Bridges (`withStoresEncPlacedSpecV`) -/

theorem onPanic_of_alloc_placed [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 s sf : State} {F R : SepProp}
    (hpref0 : s0.trace <+: s.trace)
    (hm : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨ha, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  refine ⟨⟨hpref0.trans hpref, Or.inl (allocFailedIn_of_prefix hpref0 ha)⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm

theorem onPanic_of_unack_placed [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hm : sf.mem ⊨ (⌜(∃ items', ({ sess with state := taken } : Session (List (BitVec 8))).pendingPreKey = some items' ∧
        SystemTime.unixEpoch.checkedAddSecs items'.timestamp.toNat = none) ∧
      s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨⟨items', hpk', hts⟩, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  simp only [hpk, Option.some.injEq] at hpk'
  subst hpk'
  have hpref0 : s0.trace <+: sf.trace := by
    refine List.IsPrefix.trans ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩ ?_
    rwa [← htr]
  refine ⟨⟨hpref0, Or.inr ⟨preKeyErrAnswers r, hsc.2, ?_, ?_⟩⟩, ?_⟩
  · rw [show (preKeyErrAnswers r).loadSession = .ok (some r) from rfl, ← htr]
    exact hpref
  · exact Or.inl (model_of_unack_panic hcur hfrom hrem hpk hts)
  · exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm

theorem onPanic_of_timeAdd_placed [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts : SystemTime} {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hm : sf.mem ⊨ (⌜ts.checkedAddSecs maxUnacknowledgedSessionAge = none ∧
      s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨hexp, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  have hpref0 : s0.trace <+: sf.trace := by
    refine List.IsPrefix.trans ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩ ?_
    rwa [← htr]
  refine ⟨⟨hpref0, Or.inr ⟨preKeyErrAnswers r, hsc.2, ?_, ?_⟩⟩, ?_⟩
  · rw [show (preKeyErrAnswers r).loadSession = .ok (some r) from rfl, ← htr]
    exact hpref
  · exact Or.inl (model_of_timeAdd_panic hcur hfrom hrem hpk hts hexp)
  · exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm

theorem onPanic_of_otrEnc_placed [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime} {sp pqCap pqPtr : BitVec 64} {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false)
    (hm : sf.mem ⊨ (⌜(((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error .panic ∨
        S.sendPanics otr.pqrState x.rest ∨ allocFailedIn s sf) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨hp, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  have hpref0 : s0.trace <+: sf.trace := by
    refine List.IsPrefix.trans ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩ ?_
    rwa [← htr]
  have htr' : s0.trace ++ kit.loadEvs encRecord x.rem.val (preKeyErrAnswers r).loadSession <+: sf.trace := by
    rw [show (preKeyErrAnswers r).loadSession = .ok (some r) from rfl, ← htr]
    exact hpref
  refine ⟨⟨hpref0, ?_⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩
  rcases hp with hotr | hsp | halloc
  · exact Or.inr ⟨preKeyErrAnswers r, hsc.2, htr',
      Or.inl (model_of_otr_panic hcur hfrom hrem hpk hts hexp hlt hotr)⟩
  · refine Or.inr ⟨preKeyErrAnswers r, hsc.2, htr', Or.inr ?_⟩
    unfold EncryptGhost.sendPanics
    rw [sendState_of_not_stale hcur hfrom hrem hpk hts hexp hlt]
    exact ⟨otr.pqrState, rfl, hsp⟩
  · refine Or.inl (allocFailedIn_of_prefix ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), ?_⟩ halloc)
    exact htr.symm

theorem tailModel_of_otr_err_placed {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime} {sp pqCap pqPtr : BitVec 64} {e : SignalProtocolError}
    {s0 s : State}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false)
    (herr : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error e) :
    TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r) (.error (ApiError.ofProtocol e)) s0 s := by
  have hexec := execOk_of_preKeyOtrGhost_error herr
  have hm : x.model C S uuidTryParse (preKeyErrAnswers r) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    rw [EncryptGhost.model, messageEncrypt_eq_flat]
    simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
      hexp, hlt, ↓reduceIte, Bool.false_eq_true, hexec]
  refine ⟨⟨congrArg Prod.fst hm, by rw [congrArg Prod.snd hm]; exact ⟨hsc.2, trivial⟩,
    by rw [congrArg Prod.snd hm]; exact trivial⟩, ?_⟩
  rw [congrArg Prod.snd hm, htr, ikit.traceOfWith_load]
  rfl

theorem stepsThroughEncrypt_of_preKey_ok_placed {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel}
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime} {sp pqCap pqPtr : BitVec 64} {sm : SignalMessage}
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false)
    (hok : ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .ok sm) :
    let otr' := ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).2
    let psm := PreKeySignalMessage.new otr'.sessionVersion sess.localRegistrationId
      items.preKeyId items.signedPreKeyId
      (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))
      items.baseKey otr'.localIdentityKey sm
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k
      (.preKeySignalMessage psm) otr' := by
  intro otr' psm
  refine ⟨hcur, hscope, hfrom, hrem, ?_⟩
  unfold EncEncryptStep
  rw [hpk]
  exact ⟨ts, expiry, sm, hts, hexp, hlt, execOk_of_preKeyOtrGhost_ok hok, rfl⟩

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
