/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadCommon
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Rodata

/-!
# CLI `SegLoad` Shared Infrastructure

Provides `SepWPp` / `SegExit` bridges, callee/hook address lemmas, `.rodata` string and vtable
helpers, `SpeStaged` lemmas for `sessionNotFound`, and `loadPollOutAtS` decomposition for `SegLoad`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalTripleRatchet.Encrypt

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove

open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `FrozenInv` & `SepWPp` / `SegExit` Bridges -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.alloc_onPanic_entails {C : Crypto} {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 s sf : State} {F : SepProp}
    (hpref0 : s0.trace <+: s.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage]
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

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_sepWPp_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (trTrapProgAt img.base C abs) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 sf Out)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R))) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hcont⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · obtain ⟨sf, hsteps', hout'⟩ := hcont hmf (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_sepWPp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 sf Out)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R))) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hcont⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · obtain ⟨sf, hsteps', hout'⟩ := hcont hmf (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_done_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (h : Out s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out :=
  fun _ => ⟨s, .refl s, Or.inl h⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_done {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (h : Out s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out :=
  fun _ => ⟨s, .refl s, Or.inl h⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_false_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := h hL
  exact ⟨sf, hsteps, hout.elim False.elim Or.inr⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segExit_of_false {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := h hL
  exact ⟨sf, hsteps, hout.elim False.elim Or.inr⟩

/-! ## 2. Entry & Callee/Hook Address Lemmas -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_fnAddr_trap {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
  entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_fnAddr {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
  entryOf_eq_tripleRatchetProgAt env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_base_add_trap {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = img.base + (bv% (ls_off% "libsignal_cli_ratchet::encrypt")) := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_fnAddr_trap env, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_base_add {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = img.base + (bv% (ls_off% "libsignal_cli_ratchet::encrypt")) := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.encEntry_eq_fnAddr env, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.memcpy_ok_at_enc_trap {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (_env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "memcpy" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
      framelessMemcpySpec :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cliFramelessMemcpy_ok_at_trap
    (b := img.base) (C := C) (abs := abs)
    (name := CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName)
    (k := num% (ls_off% "memcpy" - (ls_off% "libsignal_cli_ratchet::encrypt")))
    (by simp only [(ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"), arm64_norm])

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.memcpy_ok_at_enc {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (_env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "memcpy" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
      framelessMemcpySpec := by
  exact framelessMemcpy_ok_at (b := img.base) (C := C) (ctl := ctl) (abs := abs)
    (name := CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName) (k := num% (ls_off% "memcpy" - (ls_off% "libsignal_cli_ratchet::encrypt")))
    (by simp only [(ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"), arm64_norm])

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dealloc_ok_at_enc_trap {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
      (rustDeallocSpec A) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cliDealloc_ok_at_norm_trap
    (b := img.base) (C := C) env.hooks.alloc_abs
    (name := CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_cli_ratchet::encrypt")))
    (by simp only [(ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"), arm64_norm])

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.dealloc_ok_at_enc {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
      (rustDeallocSpec A) := by
  exact dealloc_ok_at_norm (b := img.base) (C := C) (ctl := ctl)
    (name := CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName) (k := num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_cli_ratchet::encrypt"))) env.hooks.alloc
    (by simp only [(ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"), arm64_norm])

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.stringClone_ok_at_enc_trap {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
      (stringCloneSpec A) := by
  have heq :
      (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName +
        bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64) =
      (trTrapProgAt img.base C abs).fnAddr stringCloneHookName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"),
      LibsignalBinary.Proofs.Common.StringCloneFlat.stringCloneName_fnOff]
    bv_omega
  rw [heq]
  exact LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_trTrapProgAt_ok
    img.base C A abs env.hooks.alloc_abs

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.stringClone_ok_at_enc {Scope Q} {img : Obj.Image} {C A} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
      (stringCloneSpec A) := by
  have heq :
      (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName +
        bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr stringCloneHookName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"),
      LibsignalBinary.Proofs.Common.StringCloneFlat.stringCloneName_fnOff]
    bv_omega
  rw [heq]
  exact LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_tripleRatchetProgAt_ok
    img.base C A ctl abs env.hooks.alloc

/-! ## 3. `.rodata` Vtable & String Literal Lemmas -/

private theorem rodata_0x4a6a0_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)) - num% (ls_xref% 0x2440 0x2444))).take 15 = utf8 "message_encrypt" := by
  rfl_kernel

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.rodata_message_encrypt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt") ∗ P :=
  EncryptCoreFacts.of_rodata_loads_eq himg
    (secOff := num% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) (secLen := 15) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) rodata_0x4a6a0_eq hro hP

/-! ## 4. Session-API Model `TailModel` Helpers for `segLoad` Error Exits -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.speStaged_sessionNotFound_devWord (A : RustAlloc) (b ret cap ptr w3 : BitVec 64)
    (a : AddrVal) (hdev : DevWord a.device w3) :
    SpeStaged A ret (.sessionNotFound a "message_encrypt")
      [cap, ptr, BitVec.ofNat 64 a.name.length, w3, b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)), 15#64]
      (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt")) := by
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
    exact Entails.of_eq (by ac_rfl)
  have hpull :
      (((ret + 8#64) ↦₆₄ cap) ∗
        ((ret + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((ret + 8#64 + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ w3) ∗
        ((ret + 8#64 + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)))) ∗
        ((ret + 8#64 + 0x28#64) ↦₆₄ 15#64)) ∗
        (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt")) =
      ((((ret + 8#64) ↦₆₄ cap) ∗ ((ret + 8#64 + 8#64) ↦₆₄ ptr) ∗
          ((ret + 8#64 + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
          vecU8Buf A cap ptr a.name) ∗
        ((ret + 8#64 + 0x18#64) ↦₆₄ w3)) ∗
        (((ret + 8#64 + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)))) ∗
          ((ret + 8#64 + 0x20#64 + 8#64) ↦₆₄ 15#64) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt")) := by
    rw [ha4]
    ac_rfl
  rw [hpull]
  refine sepConj_mono ?_ ?_
  · refine Entails.trans (sepConj_mono hvec (pointsTo64_entails_dev_of_devWord _ hdev)) ?_
    have h19 : ret + 8#64 + 0x18#64 + 1#64 = ret + 8#64 + 0x19#64 := by bv_arith
    rw [h19]
    exact Entails.of_eq (by ac_rfl)
  · refine Entails.sepExists_right (b + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ?_
    rw [h15]
    exact Entails.of_eq (by ac_rfl)

/-! ## 5. Parametric Decomposition of `loadPollOutAtS` -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.enc_adrp_0x4d6a0 {img : Obj.Image} {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (k : BitVec 64)
    (hk : k = 0x1d8#64 ∨ k = 0x43c#64) :
    (((libsignalSessionCode.rebase img.base H).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + k) &&&
      0xfffffffffffff000#64) + bv% (page% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)) - (page% (ls_off% "libsignal_cli_ratchet::encrypt" + 472))) +
      bv% ((ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)) % 4096) = img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)) := by
  have hb := ProofLib.ObjectLoad.base_aligned_of_loads himg
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"), BitVec.add_assoc img.base,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rcases hk with rfl | rfl <;> bv_arith

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
