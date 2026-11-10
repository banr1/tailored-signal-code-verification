/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVX
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegDispatchAux
public import LibsignalBinary.Proofs.E2E.RecordX.ScopeP
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.Common.StringCloneFlatX

/-!
# Ext-Generic `MessageDecrypt` Foundations (`ExtDefs`)

Defines ext-generic filesystem carriers, stacked allocator/callee contracts (`AllocContracts4K` and
`AllocContractsX`), and segment step relations over `tripleRatchetProgAtExt img.base ext` shared by
`_trap` and `WithStoresVT`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- Filesystem invariant carrier for `decrypt_signal` at `tripleRatchetProgAtExt img.base ext`. -/
abbrev DecFsCtxExt {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (ext : String → Option (State → State)) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (tripleRatchetProgAtExt img.base ext) s0 s

/-- Hypothesis bundle for `MessageDecrypt` segments over `tripleRatchetProgAtExt img.base ext` under `RecordInScopeP`. -/
structure DecHypsExt (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State))
    (ss : SessionStoreSpec A img.base)
    (id : IdentityStoreSpec A img.base)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  alloc : AllocContracts img.base A ext
  kit : SessionOnlyKitOkSE ss Scope encRecord ext
  ikit : StoreKit.Identity.IdentityStoreKitOkIE img id ext
  scopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r
  recOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
    ss.addrOk x.rem.val →
    ss.ScopeAt Scope st0 x.rem.val rec →
    decryptRecord C S parse x rec = .ok (pt, rec') →
    ss.RecOk rec'

/-- Specializes `DecHypsExt` from `DecHypsV_trap` at `ext := trTrapExterns C abs`. -/
theorem DecHypsExt.of_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {ss : SessionStoreSpec A img.base}
    {id : IdentityStoreSpec A img.base}
    {st0 : ss.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap
      img C A parse S encRecord abs ss id st0 Scope) :
    DecHypsExt img C A parse S encRecord (trTrapExterns C abs) ss id st0 Scope where
  loads := h.loads
  alloc := by
    have hA := AllocContracts.of_tripleRatchetProgAt_trap img.base C A (trTrapExterns C abs) h.hooks.alloc
    rwa [trTrapExterns_idem C abs] at hA
  kit := h.kit
  ikit := h.ikit
  scopeInP r hr := CryptoVerification.E2E.RecordX.recordInScopeP_of_recordInScope (h.scopeIn r hr)
  recOk := h.recOk

/-- Segment step relation `DecSegVX` generalized to `tripleRatchetProgAtExt img.base ext`. -/
def DecSegVXExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
  ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
    (Out s' ∨
      SubroutineOutcome
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
          C A ctl parse S encRecord img kit ikit st0 ist0 Scope Extra)
        x R s0 s')

theorem decSegVXExt_of_sepWPp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecVX
          C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope Extra).onPanic x s0 sf ∗ R))) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem decSegVXExt_of_sepWP_mid {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {mid : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (tripleRatchetProgAtExt img.base ext) mid s P
      (fun sm Pm => FrozenInv img sm → (sm.mem ⊨ Pm ∗ R) →
        DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 sm Out)) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hnext (hF.of_steps hsteps) hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem decSegVXExt_of_sepWP_done {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (tripleRatchetProgAtExt img.base ext) target s P
      (fun sf P_f => FrozenInv img sf → (sf.mem ⊨ P_f ∗ R) → Out sf)) :
    DecSegVXExt img C A ctl uuidTryParse S encRecord ext kit ikit st0 ist0 Scope Extra x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_, _, P_f, hmf, hOut⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl (hOut (hF.of_steps hsteps) hmf)⟩

/-! ## Ext-generic callee and panic helpers -/

theorem msgDecrypt_memcpy_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      framelessMemcpySpec :=
  memcpy_ok_at2_ext hA (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
    (k := num% (ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8, (ls_stub% "memcpy")])

theorem msgDecrypt_alloc_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (rustAllocSpec A) :=
  alloc_ok_at_norm_ext hA (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8, (ls_stub% "__rustc::__rust_alloc")])

theorem msgDecrypt_dealloc_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (rustDeallocSpec A) :=
  dealloc_ok_at_norm_ext hA (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8, (ls_stub% "__rustc::__rust_dealloc")])

theorem msgDecrypt_shim_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      sessionShimSpec :=
  hA.shim_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])

theorem panic_at_handle_error_msgDecrypt_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64)) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
    (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8, (ls_stub% "alloc::raw_vec::handle_error")])

theorem panic_at_expect_failed_msgDecrypt_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "core::option::expect_failed" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64)) =
      some Rust.panicked :=
  panic_at_sym_ext b ext CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName "core::option::expect_failed"
    (num% (ls_off% "core::option::expect_failed" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8, (ls_stub% "core::option::expect_failed")])
    (by rw [(ls_stub% "core::option::expect_failed")]; decide)
    (fun H => by
      rw [(ls_stub% "core::option::expect_failed")]
      exact (ls_hook% "core::option::expect_failed") H)
    (hp := by simp [Rust.isPanicSymbol])

theorem remoteIdentityKey_ok_at_msgDecrypt_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.remoteIdentityKeyName)
      (Getters.remoteIdentityKeySpec A img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        0x1fa0#64 + bv% (((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "libsignal_cli_ratchet::decrypt_signal" - 8096) % 2^64)))
      (Getters.remoteIdentityKeySpec A img) := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName) + 0x1fa0#64 +
      bv% (((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "libsignal_cli_ratchet::decrypt_signal" - 8096) % 2^64)) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff Getters.remoteIdentityKeyName) := by
    rw [CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8,
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::remote_identity_key")]
    decide
  have haddr :
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1fa0#64 +
        bv% (((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "libsignal_cli_ratchet::decrypt_signal" - 8096) % 2^64)) =
      (tripleRatchetProgAtExt img.base ext).fnAddr Getters.remoteIdentityKeyName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc (BitVec.ofNat 64 _), hk]
  rwa [haddr]

/-! ## Stacked `AllocContractsX` and `AllocContracts4K` -/

/-- Stack budget for `<PublicKey as PartialEq>::eq` (`64 + extHookStack = 16448` bytes). -/
abbrev publicKeyEqStackX : Nat := Getters.publicKeyEqStackExt

theorem publicKeyEqStackX_eq : publicKeyEqStackX = 64 + extHookStack := rfl

theorem publicKeyEqStackX_val : publicKeyEqStackX = 16448 := rfl

/-- Specification for `<PublicKey as PartialEq>::eq` with `64 + extHookStack` stack bytes. -/
abbrev publicKeyEqSpecX : Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) :=
  Getters.publicKeyEqSpecExt

/-- `subroutine_ok` hypothesis for `<PublicKey as PartialEq>::eq` on `tripleRatchetProgAtExt b ext`. -/
abbrev PublicKeyEqOkExtX (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  Getters.PublicKeyEqOkExt32 b ext

theorem allocHookStack_le_extHookStack : allocHookStack ≤ extHookStack := by decide

theorem decNeedAux_extHookStack_eq : 2 ^ 20 + extHookStack = 2 ^ 20 + 16384 := rfl

/-- Checks that `trustPollNeed` / `savePollNeed` at `extHookStack` covers the `192`-byte poll frame plus `64 + extHookStack`. -/
theorem idPollStack_covers_publicKeyEq_with_extHookStack :
    192 + (64 + extHookStack) ≤
      192 + max (max (640 + (320 + (2384 + extHookStack))) 96) (max 64 extHookStack) := by
  decide

/-- `DecHypsExt` with `AllocContractsX` (`extHookStack = 16384` bytes). -/
structure DecHypsExtX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State))
    (ss : SessionStoreSpec A img.base)
    (id : IdentityStoreSpec A img.base)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  alloc : AllocContractsX img A ext
  kit : SessionOnlyKitOkSE ss Scope encRecord ext
  ikit : StoreKit.Identity.IdentityStoreKitOkIE img id ext
  scopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r
  recOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
    ss.addrOk x.rem.val →
    ss.ScopeAt Scope st0 x.rem.val rec →
    decryptRecord C S parse x rec = .ok (pt, rec') →
    ss.RecOk rec'

theorem msgDecrypt_memcpy_ok_extX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hA (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
    (k := num% (ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [(ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"), (ls_stub% "memcpy")])

theorem msgDecrypt_alloc_ok_extX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  alloc_ok_at_norm_ext_x hA (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [(ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"), (ls_stub% "__rustc::__rust_alloc")])

theorem msgDecrypt_dealloc_ok_extX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hA (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [(ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"), (ls_stub% "__rustc::__rust_dealloc")])

theorem msgDecrypt_realloc_ok_extX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_realloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      ((rustReallocExternSpecWithStack A extHookStack).inImage img) :=
  realloc_ok_at_norm_ext_x hA (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
    (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [(ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"), (ls_stub% "__rustc::__rust_realloc")])

theorem msgDecrypt_shim_ok_extX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hA (name := CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
    (by rw [(ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"), (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])

/-- `memcpy` specification requiring `allocHookStack` (`4096` bytes) of stack slack. -/
def msgDecryptMemcpySpec4K : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      stackAt s0.sp allocHookStack

/-- Allocator, shim, and `4096`-byte `memcpy` contract bundle on `tripleRatchetProgAtExt b ext`. -/
structure AllocContracts4K (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A)
  dealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A)
  realloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustReallocSpec A)
  shim : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec
  memcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) msgDecryptMemcpySpec4K

theorem _root_.CryptoVerification.LibsignalTripleRatchet.AllocContracts.toAllocContracts4K
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) : AllocContracts4K b A ext := by
  refine ⟨hA.alloc, hA.dealloc, hA.realloc, hA.shim, ?_⟩
  have hm := memcpy_ok_at2_ext hA (name := memcpyName) (k := 0) (Nat.add_zero _)
  change subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr memcpyName + 0#64) framelessMemcpySpec at hm
  rw [BitVec.add_zero] at hm
  refine subroutine_ok_outcome_intro fun (dst, src, bs) R s0 hpc hrun hpre hsp => ?_
  let R' : SepProp := stackAt s0.sp allocHookStack ∗ R
  have hpre' : s0.mem ⊨ framelessMemcpySpec.pre (dst, src, bs) s0 ∗ R' := by
    dsimp only [msgDecryptMemcpySpec4K, framelessMemcpySpec, R'] at hpre ⊢
    ac_nf at hpre ⊢
  refine hm.mono_outcome (dst, src, bs) R' s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [msgDecryptMemcpySpec4K, framelessMemcpySpec, R'] at hpost ⊢
    ac_nf at hpost ⊢
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem msgDecrypt_memcpy_ok_ext4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      msgDecryptMemcpySpec4K := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr memcpyName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, memcpyName,
      (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"),
      (ls_stub% "memcpy"), BitVec.add_assoc]
    rfl
  rw [haddr]
  exact hA.memcpy

theorem msgDecrypt_alloc_ok_ext4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (rustAllocSpec A) := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr allocName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, allocName,
      (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"),
      (ls_stub% "__rustc::__rust_alloc"), BitVec.add_assoc]
    rfl
  rw [haddr]
  exact hA.alloc

theorem msgDecrypt_dealloc_ok_ext4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (rustDeallocSpec A) := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr deallocName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, deallocName,
      (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"),
      (ls_stub% "__rustc::__rust_dealloc"), BitVec.add_assoc]
    rfl
  rw [haddr]
  exact hA.dealloc

theorem msgDecrypt_shim_ok_ext4K {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      sessionShimSpec := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr shimName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, shimName,
      (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"),
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2"), BitVec.add_assoc]
    rfl
  rw [haddr]
  exact hA.shim

theorem stringClone_ok_at_dec_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (stringCloneSpec A) := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr stringCloneHookName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase,
      CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName,
      (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal"),
      LibsignalBinary.Proofs.Common.StringCloneFlat.stringCloneName_fnOff, BitVec.add_assoc]
    bv_omega
  have hmc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack framelessMemcpySpec allocHookStack) := by
    refine subroutine_ok_outcome_intro fun (dst, src, bs) R s0 hpc hrun hpre hsp => ?_
    have hpre' : s0.mem ⊨ msgDecryptMemcpySpec4K.pre (dst, src, bs) s0 ∗ R := by
      dsimp only [withStack, framelessMemcpySpec, msgDecryptMemcpySpec4K] at hpre ⊢
      ac_nf at hpre ⊢
    refine hA.memcpy.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hp⟩ | ⟨c, hc, hex⟩ | ⟨hoom, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withStack, framelessMemcpySpec, msgDecryptMemcpySpec4K] at hpost ⊢
      ac_nf at hpost ⊢
    · exact Or.inr (Or.inl ⟨hpan, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hoom, hp⟩))
  rw [haddr]
  exact LibsignalBinary.Proofs.Common.StringCloneFlatX.stringClone_4k_ok A hA.shim hA.alloc hmc

/-- `DecHypsExt` with `AllocContracts4K` (`allocHookStack = 4096` bytes). -/
structure DecHypsExt4K (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State))
    (ss : SessionStoreSpec A img.base)
    (id : IdentityStoreSpec A img.base)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  alloc : AllocContracts4K img.base A ext
  kit : SessionOnlyKitOkSE ss Scope encRecord ext
  ikit : StoreKit.Identity.IdentityStoreKitOkIE img id ext
  scopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r
  recOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
    ss.addrOk x.rem.val →
    ss.ScopeAt Scope st0 x.rem.val rec →
    decryptRecord C S parse x rec = .ok (pt, rec') →
    ss.RecOk rec'

theorem DecHypsExt.toDecHypsExt4K {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {ss : SessionStoreSpec A img.base} {id : IdentityStoreSpec A img.base}
    {st0 : ss.StoreState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (h : DecHypsExt img C A parse S encRecord ext ss id st0 Scope) :
    DecHypsExt4K img C A parse S encRecord ext ss id st0 Scope where
  loads := h.loads
  alloc := h.alloc.toAllocContracts4K
  kit := h.kit
  ikit := h.ikit
  scopeInP := h.scopeInP
  recOk := h.recOk

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
