/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seams
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitE
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq

/-!
# Ext-Generic `WithStoresVT` Specifications and Environments

Defines `OtrEncryptOkT_ext`, `EncCalleesT_ext`, `EncEnv_ext`, `EncEnvT_ext` (carrying
`scopeTsZero`), `withStoresEncSpecVT_ext`, `EncFsCtx_ext`, `SegExit_ext`, and `h45_SegExitVT_ext`
on `tripleRatchetProgAtExt` without importing `signalSessionCliCode`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (SessionOnlyKitOkSE SessionOnlyVtablesOk)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreKitOkIE)
open CryptoVerification.LibsignalSpqrV1 (TokenInit)
open CryptoVerification.Cli.LibsignalPublicApi (encryptWithStoresName)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

namespace WithStoresVT

abbrev UnackItemsOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items"))
    (unackItemsSpec A img)

abbrev KyberMapOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + bv% (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_cli_ratchet::Coins>::{closure#0}::{closure#2}>"))
    (kyberMapSpec A)

abbrev PreKeyMsgNewOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + bv% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new"))
    (preKeyMsgNewSpec A)

abbrev CmDropOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    (img.base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]"))
    (cmDropSpec A)

abbrev otrEncryptSpecQExt (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) : Spec OtrEncryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl parse S img with
    pre := fun x s => ⌜Q x.ot.pqrState⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl parse S img).pre x s }

abbrev OtrEncryptOkQExt (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (otrEncryptSpecQExt Q C A ctl parse S img)

abbrev shimSpecExt : Spec Unit :=
  { pre := fun _ _ => emp
    post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ }

abbrev memcpySpecExt : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  { pre := (libcMemcpySpec allocHookStack).pre
    post := fun (dst, src, bs) s0 sf =>
      ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
        (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack }

abbrev memcpyROSpecExt : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withStack
    { pre := fun (dst, src, bs) s0 =>
        ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
          bs.length ≤ 2 ^ 64⌝ ∗ memRegion dst bs.length ∗ (src ↦ᵣ bs)
      post := fun (dst, src, bs) s0 sf =>
        ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) }
    allocHookStack

abbrev durationSinceEpochSpecExt : Spec (BitVec 64 × BitVec 64) :=
  { pre := fun (p, ret) s =>
      ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧
        s.readReg64 .x1 = 0#64 ∧ (s.readReg64 .x2).setWidth 32 = 0#32⌝ ∗
        (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₃₂ 0#32) ∗ memRegion (p + 12#64) 4 ∗
        memRegion ret 24 ∗ stackAt s.sp 16384
    post := fun (p, ret) s0 sf =>
      ⌜sf.trace = s0.trace⌝ ∗
        memRegion p 16 ∗
        ((∃∗ w2 : BitVec 64, ∃∗ w0 : BitVec 64,
          (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2))) ∗
        stackAt s0.sp 16384 }

/-- Contract-backed hook bundle for CLI `MessageEncrypt` on `tripleRatchetProgAtExt img.base ext`. -/
structure EncHooksExt (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S ext where
  shim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" shimSpecExt
  memcpy : HookSat ext "memcpy" memcpySpecExt
  memcpyRO : HookSat ext "memcpy" memcpyROSpecExt
  timeAdd : HookSat ext timeAddHookName timeAddSpec
  durationSinceEpoch : HookSat ext durationSinceHookName durationSinceEpochSpecExt

/-- `4096`B (`allocHookStack = memHookStack`) allocator + `shim` + `memcpy` contract bundle on
`tripleRatchetProgAtExt b ext`. -/
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
    ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
    (withStack framelessMemcpySpec allocHookStack)

/-- `__rustc::__rust_no_alloc_shim_is_unstable_v2` at call distance `k` from `name` on `tripleRatchetProgAtExt`. -/
theorem noAllocShim_ok_at_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hshim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" shimSpecExt)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      sessionShimSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl hk
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol]) hshim

/-- `memcpy` (`memcpySpecExt`, 4096 B stack) at call distance `k` from `name` on `tripleRatchetProgAtExt`. -/
theorem memcpy_ok_at_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : HookSat ext "memcpy" memcpySpecExt)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      memcpySpecExt :=
  hook_ok_at (hname := "memcpy") rfl hk (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol]) hmemcpy

/-- `memcpy` (`withStack framelessMemcpySpec allocHookStack`, 4096 B stack) at call distance `k` from `name`. -/
theorem stackedMemcpy_ok_at_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : HookSat ext "memcpy" memcpySpecExt)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack framelessMemcpySpec allocHookStack) := by
  have h := memcpy_ok_at_ext (b := b) hmemcpy (name := name) (k := k) hk
  refine subroutine_ok.of_codeLoaded fun (dst, src, bs) R s0 hpc hrun hpre hal _hL => ?_
  have hpre' : s0.mem ⊨ memcpySpecExt.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [withStack, framelessMemcpySpec, memcpySpecExt, libcMemcpySpec, allocHookStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine (h.to_outcome (dst, src, bs) R s0 hpc hrun hpre' hal).mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [memcpySpecExt, withStack, framelessMemcpySpec, allocHookStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- `__rust_alloc` at call distance `k` from `name` on `tripleRatchetProgAtExt`, taking `AllocHooks A ext`. -/
theorem alloc_ok_at_norm_ext' {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc") :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  alloc_ok_at_ext b A ext hA name k hk

/-- `__rust_dealloc` at call distance `k` from `name` on `tripleRatchetProgAtExt`, taking `AllocHooks A ext`. -/
theorem dealloc_ok_at_norm_ext' {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc") :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  dealloc_ok_at_ext b A ext hA name k hk

/-- `__rust_realloc` at call distance `k` from `name` on `tripleRatchetProgAtExt`, taking `AllocHooks A ext`. -/
theorem realloc_ok_at_norm_ext' {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc") :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  realloc_ok_at_ext b A ext hA name k hk

theorem allocContracts4K_of_encHooksExt {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hH : EncHooksExt C A S ext) : AllocContracts4K b A ext where
  alloc := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      alloc_ok_at_norm_ext' (b := b) hH.alloc (name := allocName) (k := 0) (Nat.add_zero _)
  dealloc := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      dealloc_ok_at_norm_ext' (b := b) hH.alloc (name := deallocName) (k := 0) (Nat.add_zero _)
  realloc := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      realloc_ok_at_norm_ext' (b := b) hH.alloc (name := reallocName) (k := 0) (Nat.add_zero _)
  shim := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      noAllocShim_ok_at_ext (b := b) hH.shim (name := shimName) (k := 0) (Nat.add_zero _)
  memcpy := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      stackedMemcpy_ok_at_ext (b := b) hH.memcpy (name := memcpyName) (k := 0) (Nat.add_zero _)

/-- `entryOf img name` equals `(tripleRatchetProgAtExt img.base ext).fnAddr name`. -/
theorem entryOf_eq_trExtProgAt {img : Obj.Image} (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (name : String) :
    entryOf img name = (tripleRatchetProgAtExt img.base ext).fnAddr name :=
  entryOf_eq_tripleRatchetProgAtExt (ext := ext) himg name

structure EncCalleesQExt (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop where
  otrFrom : OutgoingRatchet.OtrFromExtOk img A ext
  otrApply : OutgoingRatchet.OtrApplyExtOk img A ext
  remoteIk : OutgoingRatchet.RemoteIdentityKeyExtOk img A ext
  otrEnc : OtrEncryptOkQExt Q img C A ctl parse S ext
  unack : UnackItemsOkExt img A ext
  kyber : KyberMapOkExt img A ext
  psmNew : PreKeyMsgNewOkExt img A ext
  cmDrop : CmDropOkExt img A ext
  dropSs : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
    img.base A ext

end WithStoresVT

/-- `OTR::encrypt` on `tripleRatchetProgAtExt` meets `Cli.LibsignalSpqrV1.otrEncryptSpecT`. -/
def OtrEncryptOkT_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl parse S img)

/-- `OtrEncryptOkT_ext` from an `entryOf`-addressed `subroutine_ok` on `tripleRatchetProgAtExt`. -/
theorem otrEncryptOkT_of_run_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img)) :
    OtrEncryptOkT_ext img C A ctl uuidTryParse S ext := by
  unfold OtrEncryptOkT_ext
  rwa [WithStoresVT.entryOf_eq_trExtProgAt ext himg] at h

/-- Shared non-OTR-encrypt callee contracts on `tripleRatchetProgAtExt img.base ext`. -/
structure EncBaseCallees_ext (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  otrFrom : OutgoingRatchet.OtrFromExtOk img A ext
  otrApply : OutgoingRatchet.OtrApplyExtOk img A ext
  remoteIk : OutgoingRatchet.RemoteIdentityKeyExtOk img A ext
  unack : WithStoresVT.UnackItemsOkExt img A ext
  kyber : WithStoresVT.KyberMapOkExt img A ext
  psmNew : WithStoresVT.PreKeyMsgNewOkExt img A ext
  cmDrop : WithStoresVT.CmDropOkExt img A ext
  dropSs : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
    img.base A ext

/-- `EncCallees_ext` with `OTR::encrypt` specialized to `OtrEncryptOkT_ext`. -/
structure EncCalleesT_ext (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop where
  otrFrom : OutgoingRatchet.OtrFromExtOk img A ext
  otrApply : OutgoingRatchet.OtrApplyExtOk img A ext
  remoteIk : OutgoingRatchet.RemoteIdentityKeyExtOk img A ext
  otrEnc : OtrEncryptOkT_ext img C A ctl parse S ext
  unack : WithStoresVT.UnackItemsOkExt img A ext
  kyber : WithStoresVT.KyberMapOkExt img A ext
  psmNew : WithStoresVT.PreKeyMsgNewOkExt img A ext
  cmDrop : WithStoresVT.CmDropOkExt img A ext
  dropSs : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
    img.base A ext

theorem EncCalleesT_ext.toBase {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (h : EncCalleesT_ext img C A ctl parse S ext) : EncBaseCallees_ext img A ext :=
  ⟨h.otrFrom, h.otrApply, h.remoteIk, h.unack, h.kyber, h.psmNew, h.cmDrop, h.dropSs⟩

theorem WithStoresVT.EncCalleesQExt.toBase {Q : List (BitVec 8) → Prop} {img : Obj.Image}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (h : WithStoresVT.EncCalleesQExt Q img C A ctl parse S ext) : EncBaseCallees_ext img A ext :=
  ⟨h.otrFrom, h.otrApply, h.remoteIk, h.unack, h.kyber, h.psmNew, h.cmDrop, h.dropSs⟩

/-- Shared base environment on `tripleRatchetProgAtExt img.base ext` for all non-OTR-encrypt
segments and tails. -/
structure EncBaseEnv_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : WithStoresVT.EncHooksExt C A S ext
  kitOk : SessionOnlyKitOkSE kit Scope encRecord ext
  ikitOk : IdentityStoreKitOkIE img ikit ext
  callees : EncBaseCallees_ext img A ext
  vtables : SessionOnlyVtablesOk img kit
  idVtables : IdentityVtablesOk img ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    kit.addrOk x.rem.val →
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

/-- Ext-generic twin of `EncEnv_trap` on `tripleRatchetProgAtExt img.base ext` (Arm 2 `RecordPqEmpty`),
carrying `scopeTsZero` for the `UNIX_EPOCH` `duration_since` contract on `SegPreKey`. -/
structure EncEnv_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : WithStoresVT.EncHooksExt C A S ext
  kitOk : SessionOnlyKitOkSE kit Scope encRecord ext
  ikitOk : IdentityStoreKitOkIE img ikit ext
  callees : WithStoresVT.EncCalleesQExt Q img C A ctl parse S ext
  vtables : SessionOnlyVtablesOk img kit
  idVtables : IdentityVtablesOk img ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  scopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s → Q s.state.pqRatchetState
  scopeTsZero : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8)))
    (s : Session (List (BitVec 8))) (p : PendingPreKey),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s → s.pendingPreKey = some p →
      p.timestamp = 0
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    kit.addrOk x.rem.val →
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

theorem EncEnv_ext.toBase {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    (env : EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext) :
    EncBaseEnv_ext kit st0 ikit ist0 Scope C parse S encRecord ext where
  loads := env.loads
  hooks := env.hooks
  kitOk := env.kitOk
  ikitOk := env.ikitOk
  callees := env.callees.toBase
  vtables := env.vtables
  idVtables := env.idVtables
  scopeIn := env.scopeIn
  recOk := env.recOk

theorem EncEnv_ext.q_otr {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    (env : EncEnv_ext kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord ext)
    {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 rem r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    Q otr.pqrState :=
  fromSessionState_pqrState hfrom ▸ env.scopeQ r sess hsc hcur

/-- `EncEnv_ext` at `Q := (·.length < 2^32)` with `callees : EncCalleesT_ext` and `scopeTsZero`. -/
structure EncEnvT_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : WithStoresVT.EncHooksExt C A S ext
  kitOk : SessionOnlyKitOkSE kit Scope encRecord ext
  ikitOk : IdentityStoreKitOkIE img ikit ext
  callees : EncCalleesT_ext img C A ctl parse S ext
  vtables : SessionOnlyVtablesOk img kit
  idVtables : IdentityVtablesOk img ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  scopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s → s.state.pqRatchetState.length < 2 ^ 32
  scopeTsZero : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8)))
    (s : Session (List (BitVec 8))) (p : PendingPreKey),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s → s.pendingPreKey = some p →
      p.timestamp = 0
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    kit.addrOk x.rem.val →
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

theorem EncEnvT_ext.toBase {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    (env : EncEnvT_ext kit st0 ikit ist0 Scope C ctl parse S encRecord ext) :
    EncBaseEnv_ext kit st0 ikit ist0 Scope C parse S encRecord ext where
  loads := env.loads
  hooks := env.hooks
  kitOk := env.kitOk
  ikitOk := env.ikitOk
  callees := env.callees.toBase
  vtables := env.vtables
  idVtables := env.idVtables
  scopeIn := env.scopeIn
  recOk := env.recOk

theorem EncEnvT_ext.q_otr {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    (env : EncEnvT_ext kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord ext)
    {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 rem r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    otr.pqrState.length < 2 ^ 32 :=
  fromSessionState_pqrState hfrom ▸ env.scopeQ r sess hsc hcur

/-- CLI `withStoresEncSpecV` with `64 ≤ x.rest.length` in `pre` and `TokenInit img` framed. -/
def withStoresEncSpecVT_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec WithStoresEncGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
      kit st0 ikit ist0 C ctl uuidParse S encRecord with
    pre := fun x s =>
      ⌜64 ≤ x.rest.length⌝ ∗ TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).pre x s
    post := fun x s0 sf =>
      TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf }

/-- Ext-generic twin of `EncFsCtx_trap` on `tripleRatchetProgAtExt img.base ext`. -/
abbrev EncFsCtx_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (ext : String → Option (State → State)) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (tripleRatchetProgAtExt img.base ext) s0 s

/-- Ext-generic twin of `SegExit_trap` on `tripleRatchetProgAtExt img.base ext`. -/
def SegExit_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    ∃ sf, Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
      (next sf ∨ SubroutineOutcome
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
          kit st0 ikit ist0 C ctl parse S encRecord) x R s0 sf)

theorem SegExit_ext.next {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop} (h : next s) :
    SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s next :=
  fun _ => ⟨s, Steps.refl s, Or.inl h⟩

theorem SegExit_ext.of_false {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h : SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s (fun _ => False)) :
    SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hfalse | hout⟩ := h hL
  · exact False.elim hfalse
  · exact ⟨sf, hsteps, Or.inr hout⟩

theorem SegExit_ext.trans {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {mid next : State → Prop}
    (h1 : SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s mid)
    (h2 : ∀ sm, mid sm → SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 sm next) :
    SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem SegExit_ext.of_sepWP {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {mid : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R))
    (hwp : SepWP (tripleRatchetProgAtExt img.base ext) mid s P post)
    (hcont : ∀ sm Pm, (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      Steps (tripleRatchetProgAtExt img.base ext) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) →
      post sm Pm → SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R0 s0 sm next) :
    SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem SegExit_ext.call {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (tripleRatchetProgAtExt img.base ext) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (tripleRatchetProgAtExt img.base ext) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
        kit st0 ikit ist0 C ctl parse S encRecord).onPanic x s0 sf ∗ R0))
    (hnext : ∀ sm : State, (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      Steps (tripleRatchetProgAtExt img.base ext) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome xc (F ∗ R) s hpc hrun hm hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (hoom sm _ _hoom_st _hoom_post).elim

theorem h45_subroutineOutcome_vt_of_v_ext {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
        kit st0 ikit ist0 C ctl uuidParse S encRecord)
      x (TokenInit img ∗ R) s0 sf) :
    SubroutineOutcome (withStoresEncSpecVT_ext kit st0 ikit ist0 C ctl uuidParse S encRecord)
      x R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only [withStoresEncSpecVT_ext]
    refine Satisfies.mono ?_ hpost
    exact Entails.of_eq (by ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresEncSpecVT_ext,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage] at honp ⊢
    refine Satisfies.mono ?_ honp
    rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap (TokenInit img)]
    refine sepConj_mono_left (sepConj_mono_right ?_)
    exact entails_anyHeap (anyHeap ∗ TokenInit img)
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (TokenInit img ∗ R) at honex
    rw [satisfies_pure_sepConj] at honex
    exact False.elim honex.1
  · change sf.mem ⊨ ⌜False⌝ ∗ (TokenInit img ∗ R) at honoom
    rw [satisfies_pure_sepConj] at honoom
    exact False.elim honoom.1

/-- Segment continuation wrapper for `withStoresEncSpecVT_ext` on `tripleRatchetProgAtExt`. -/
def h45_SegExitVT_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State))
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
  ∃ sf, Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
    (next sf ∨
      SubroutineOutcome (withStoresEncSpecVT_ext kit st0 ikit ist0 C ctl parse S encRecord)
        x R s0 sf)

theorem h45_segExitVT_of_segExit_ext {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {next : State → Prop}
    (h : SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x (TokenInit img ∗ R) s0 s next) :
    h45_SegExitVT_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s next := by
  intro hL
  obtain ⟨sf, hst, hnext | hout⟩ := h hL
  · exact ⟨sf, hst, Or.inl hnext⟩
  · exact ⟨sf, hst, Or.inr (h45_subroutineOutcome_vt_of_v_ext hout)⟩

theorem h45_segExitVT_trans_ext {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : h45_SegExitVT_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s mid)
    (h2 : ∀ sm, mid sm → h45_SegExitVT_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 sm next) :
    h45_SegExitVT_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem h45_segExitVT_of_false_ext {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h : h45_SegExitVT_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s (fun _ => False)) :
    h45_SegExitVT_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s next := by
  intro hL
  obtain ⟨sf, hst, hfalse | hout⟩ := h hL
  · exact False.elim hfalse
  · exact ⟨sf, hst, Or.inr hout⟩

theorem h45_segExitVT_call_ext {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    {α : Type} {entry : BitVec 64} {spec : Spec α} {F : SepProp}
    (hcal : subroutine_ok (tripleRatchetProgAtExt img.base ext) entry spec)
    (g : α)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hal : s.spAligned = true)
    (_hlr : s.readReg64 .x30 ≠ 0#64)
    (hpre : s.mem ⊨ spec.pre g s ∗ (F ∗ R))
    (hexit : ∀ sf code, sf.status = .Exited code → Steps (tripleRatchetProgAtExt img.base ext) s sf →
      (sf.mem ⊨ spec.onExit g code s sf ∗ (F ∗ R)) → False)
    (hpan : ∀ sf, sf.status = .Panicked → Steps (tripleRatchetProgAtExt img.base ext) s sf →
      (sf.mem ⊨ (spec.onPanic g s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl parse S encRecord).onPanic x s0 sf ∗ R))
    (hok : ∀ sf, (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      sf.pc = s.readReg64 .x30 → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      (sf.mem ⊨ (spec.post g s sf ∗ F) ∗ R) →
      h45_SegExitVT_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 sf next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom g s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    h45_SegExitVT_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hout, _⟩ := hcal.no_fault_before_outcome g (F ∗ R) s hpc hrun hpre hal hL
  rcases hout with ⟨⟨hsf_pc, _, hsf_run⟩, ⟨hsf_sp, hcs⟩, hpost⟩ | ⟨hpan_st, honp⟩ | ⟨code, hex_st, honex⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    obtain ⟨sf', hsteps', hfin⟩ := hok sf hL hsteps hsf_pc hsf_run hsf_sp hcs hpost (hsteps.codeLoaded hL)
    exact ⟨sf', hsteps.trans hsteps', hfin⟩
  · rw [← sepConj_assoc] at honp
    exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_st, hpan sf hpan_st hsteps honp⟩))⟩
  · exact False.elim (hexit sf code hex_st hsteps honex)
  · exact False.elim (hoom sf _ _hoom_st _hoom_post)

/-! ## Ext-generic `Seg*SpecV_ext` and `EncSegsV_ext` (for Arm 2 `RecordPqEmpty`) -/

def SegLoadSpecV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext →
    ∀ (x : WithStoresEncGhost) (R : SepProp) (s0 : State),
      EncFsCtx_ext kit ikit ext s0 s0 →
      s0.pc = encEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl parse S encRecord).pre x s0 ∗ R) →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s0
        (fun s => ∃ r g sess, CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s)

def SegFromSpecV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
      (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s
        (fun s' => ∃ otr taken pqCap pqPtr,
          OtrStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s')

def SegIdentitySpecV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R : SepProp)
      (s0 s : State),
      OtrStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s
        (fun s' => ∃ k,
          KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s')

def SegSignalSpecV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey = none →
      KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

def SegPreKeySpecV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey.isSome →
      KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

def SegTrustSpecV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtx_ext kit ikit ext s0 s →
      CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s
        (fun s' => SaveStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k
          m otr' pqCap' pqPtr' R s0 s')

def SegSaveSpecV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtx_ext kit ikit ext s0 s →
      SaveStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s
        (fun s' => ∃ c, ApplyStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr
          taken k m otr' pqCap' pqPtr' c R s0 s')

def SegApplyStoreSpecV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
      (c : IdentityChange) (R : SepProp) (s0 s : State),
      kit.addrOk x.rem.val →
      EncFsCtx_ext kit ikit ext s0 s →
      ApplyStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
        pqCap' pqPtr' c R s0 s →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s
        (fun s' => StoredStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken
          k m otr' c R s0 s')

def SegFinishSpecV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop :=
  EncEnv_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
      (s0 s : State),
      StoredStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' c R
        s0 s →
      SegExit_ext kit st0 ikit ist0 C ctl parse S encRecord ext x R s0 s (fun _ => False)

structure EncSegsV_ext {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ext : String → Option (State → State)) : Prop where
  load : SegLoadSpecV_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext
  fromS : SegFromSpecV_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext
  identity : SegIdentitySpecV_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext
  signal : SegSignalSpecV_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext
  preKey : SegPreKeySpecV_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext
  trust : SegTrustSpecV_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext
  save : SegSaveSpecV_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext
  applyStore : SegApplyStoreSpecV_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext
  finish : SegFinishSpecV_ext kit st0 ikit ist0 Scope Q C ctl parse S encRecord ext

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
