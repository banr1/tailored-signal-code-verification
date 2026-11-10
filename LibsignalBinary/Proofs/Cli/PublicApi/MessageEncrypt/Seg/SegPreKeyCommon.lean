/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Rodata

/-!
# Shared Helpers for `segPreKey`

Provides `SystemTime` arithmetic helpers, external hook `subroutine_ok` lemmas, `.rodata` string
literal `"message_encrypt"` framing, and `SegExit` / panic bridges shared across `segPreKey`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Encrypt

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Pure model and `SystemTime` lemmas -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
  entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
  entryOf_eq_tripleRatchetProgAt env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = img.base + (bv% (ls_off% "libsignal_cli_ratchet::encrypt")) := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr_trap env, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = img.base + (bv% (ls_off% "libsignal_cli_ratchet::encrypt")) := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr env, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.unack_ok_at_enc_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) (unackItemsSpec A img) := by
  have h := env.callees.unack
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.UnackItemsOk_trap at h
  have haddr : img.base + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items") =
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add_trap env]; bv_omega
  rwa [← haddr]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.unack_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) (unackItemsSpec A img) := by
  have h := env.callees.unack
  unfold UnackItemsOk at h
  have haddr : img.base + 0x1245c#64 = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add env]; bv_omega
  rwa [← haddr]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.kyber_ok_at_enc_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) (kyberMapSpec A) := by
  have h := env.callees.kyber
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk_trap at h
  have haddr : img.base + (bv% (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")) = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add_trap env]; bv_omega
  rwa [← haddr]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.kyber_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) (kyberMapSpec A) := by
  have h := env.callees.kyber
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk at h
  have haddr : img.base + (bv% (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>")) = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add env]; bv_omega
  rwa [← haddr]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.otrEnc_ok_at_enc_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl uuidTryParse S img) := by
  have h := env.callees.otrEnc
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ_trap at h
  have haddr : (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName =
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>"), CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add_trap env]
    bv_omega
  rwa [← haddr]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.otrEnc_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ Q C A ctl uuidTryParse S img) := by
  have h := env.callees.otrEnc
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ at h
  have haddr : (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName =
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>"), CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add env]
    bv_omega
  rwa [← haddr]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.preKeyMsgNew_ok_at_enc_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) (preKeyMsgNewSpec A) := by
  have h := env.callees.psmNew
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.PreKeyMsgNewOk_trap at h
  have haddr : img.base + bv% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new") =
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add_trap env]; bv_omega
  rwa [← haddr]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.preKeyMsgNew_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) (preKeyMsgNewSpec A) := by
  have h := env.callees.psmNew
  unfold PreKeyMsgNewOk at h
  have haddr : img.base + 0x15130#64 = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_base_add env]; bv_omega
  rwa [← haddr]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.timeAdd_ok_at_enc_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) timeAddSpec := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr_trap env]
  exact hook_ok_at (hname := timeAddHookName) (stub := num% (ls_off% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add"))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (by decide) (by decide)
    (ls_hook% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add")
    (by simp [Rust.isPanicSymbol, timeAddHookName]) env.hooks.timeAdd

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.timeAdd_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) timeAddSpec := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr env]
  have habs := tripleRatchetExterns_stores_abs C ctl abs
  have h4 : Rust.withPanics (tripleRatchetExterns C ctl abs) timeAddHookName =
      abs timeAddHookName := Option.some.inj (congrArg (·[4]?) habs)
  refine hook_ok_at_raw (hname := timeAddHookName) (stub := num% (ls_off% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add"))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (by decide) (by decide)
    (ls_hook% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add") ?_
  simpa [HookSat, h4] using env.hooks.timeAdd

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.durationSince_ok_at_enc_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<std::time::SystemTime>::duration_since" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
      CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr_trap env]
  exact hook_ok_at (hname := durationSinceHookName) (stub := num% (ls_off% "<std::time::SystemTime>::duration_since"))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (by decide) (by decide)
    (ls_hook% "<std::time::SystemTime>::duration_since")
    (by simp [Rust.isPanicSymbol, durationSinceHookName]) env.hooks.durationSince

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.durationSince_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<std::time::SystemTime>::duration_since" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) durationSinceSpec := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr env]
  have habs := tripleRatchetExterns_stores_abs C ctl abs
  have h5 : Rust.withPanics (tripleRatchetExterns C ctl abs) durationSinceHookName =
      abs durationSinceHookName := Option.some.inj (congrArg (·[5]?) habs)
  refine hook_ok_at_raw (hname := durationSinceHookName) (stub := num% (ls_off% "<std::time::SystemTime>::duration_since"))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (by decide) (by decide)
    (ls_hook% "<std::time::SystemTime>::duration_since") ?_
  simpa [HookSat, h5] using env.hooks.durationSince

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.stringClone_ok_at_enc_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) (stringCloneSpec A) := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr_trap env]
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

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.stringClone_ok_at_enc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope Q C ctl S encRecord abs}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) (stringCloneSpec A) := by
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr env]
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

/-! ## `.rodata` Literal `"message_encrypt"` (15 bytes) -/

open ProofLib.ProgramReflection in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.rodata_0x4a6a0_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)) - num% (ls_xref% 0x2440 0x2444))).take 15 = utf8 "message_encrypt" := by
  rfl_kernel

open ProofLib.ProgramReflection in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.rodata_message_encrypt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt") ∗ P :=
  EncryptCoreFacts.of_rodata_loads_eq himg
    (secOff := num% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) (secLen := 15) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.rodata_0x4a6a0_eq hro hP

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.rodata_message_encrypt_sepWPp {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWPp prog ret s (((img.base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476))) ↦ᵣ utf8 "message_encrypt") ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.rodata_message_encrypt_intro himg hro hm

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s mid)
    (h2 : ∀ sm, mid sm → CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s mid)
    (h2 : ∀ sm, mid sm → CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_false_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {next : State → Prop}
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sf, hst, hfalse | hout⟩ := h hL
  · exact hfalse.elim
  · exact ⟨sf, hst, Or.inr hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_false {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {next : State → Prop}
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sf, hst, hfalse | hout⟩ := h hL
  · exact hfalse.elim
  · exact ⟨sf, hst, Or.inr hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_absorb_extra {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 sf : State} {R0 : SepProp}
    (h : sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗
      (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0 := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [← sepConj_assoc] at h
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) h.2

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_alloc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {s0 s sf : State} {F R : SepProp}
    (hpref0 : s0.trace <+: s.trace)
    (hm : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨ha, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  refine ⟨⟨hpref0.trans hpref, Or.inl (allocFailedIn_of_prefix hpref0 ha)⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_unack {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
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
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage]
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

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_timeAdd {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
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
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage]
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

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_otrEnc {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
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
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage]
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

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.adrp_0x4a6a0_eq (base entry : BitVec 64)
    (halign : base &&& 0xfff#64 = 0#64) (hentry : base + bv% (ls_off% "libsignal_cli_ratchet::encrypt") = entry) :
    ((entry + 1968#64 &&& 18446744073709547520#64) + bv% ((ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)) - page% (ls_off% "libsignal_cli_ratchet::encrypt" + 1968))) = base + bv% (ls_xref% (ls_off% "libsignal_cli_ratchet::encrypt" + 472) (ls_off% "libsignal_cli_ratchet::encrypt" + 476)) := by
  subst hentry
  rw [BitVec.add_assoc, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.adrp_0x4b000_eq (base entry : BitVec 64)
    (halign : base &&& 0xfff#64 = 0#64) (hentry : base + bv% (ls_off% "libsignal_cli_ratchet::encrypt") = entry) :
    ((entry + 1816#64 &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "libsignal_cli_ratchet::encrypt" + 1816))) = base + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  subst hentry
  rw [BitVec.add_assoc, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl
end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
